#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include "fat32.h"

void *map_disk(const char *fname);

/* ================================================================
 * Filesystem geometry
 * ================================================================ */

static uint32_t g_bps;           /* bytes per sector        */
static uint32_t g_spc;           /* sectors per cluster     */
static uint32_t g_cluster_size;  /* bytes per cluster       */
static uint32_t g_data_offset;   /* byte offset of cluster 2 */
static uint32_t g_total_clusters;
static uint8_t *g_img;           /* mmap'd image base       */
static size_t   g_image_size;

/* ================================================================
 * Recovered file list
 * ================================================================ */

#define MAX_RECOVERED 4096

struct recovered_file {
    char     filename[512];
    uint32_t start_cluster;
    uint32_t file_size;
    char     sha1[64];
};

static struct recovered_file g_files[MAX_RECOVERED];
static int g_nfiles = 0;

/* ================================================================
 * Helpers
 * ================================================================ */

static inline uint32_t rd16le(const uint8_t *p)
{
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8);
}

static inline uint32_t rd32le(const uint8_t *p)
{
    return (uint32_t)p[0]        | ((uint32_t)p[1] << 8)
         | ((uint32_t)p[2] << 16)| ((uint32_t)p[3] << 24);
}

static uint32_t cluster_offset(uint32_t cl)
{
    return g_data_offset + (uint32_t)(cl - 2) * g_cluster_size;
}

static int cluster_recovered(uint32_t cl)
{
    for (int i = 0; i < g_nfiles; i++) {
        uint32_t s = g_files[i].start_cluster;
        uint32_t n = (g_files[i].file_size + g_cluster_size - 1) / g_cluster_size;
        if (cl >= s && cl < s + n)
            return 1;
    }
    return 0;
}

/* ================================================================
 * BMP header validation (24-bit, created by PIL)
 * ================================================================ */

static int is_valid_bmp(const uint8_t *p, uint32_t avail)
{
    if (avail < 54) return 0;
    if (p[0] != 'B' || p[1] != 'M') return 0;

    uint32_t fsz  = rd32le(p + 2);
    uint32_t doff = rd32le(p + 10);
    uint32_t hsz  = rd32le(p + 14);
    uint32_t pln  = rd16le(p + 26);
    uint32_t bpp  = rd16le(p + 28);
    int32_t  w    = (int32_t)rd32le(p + 18);
    int32_t  h    = (int32_t)rd32le(p + 22);

    if (fsz < 54 || fsz > 256u * 1024 * 1024) return 0;
    if (doff < 14 || doff > fsz)               return 0;
    if (pln != 1)                               return 0;
    if (bpp != 24)                              return 0;
    if (w <= 0 || w > 16384)                    return 0;
    if (h <= 0 || h > 16384)                    return 0;
    if (hsz != 40 && hsz != 52 && hsz != 56
        && hsz != 108 && hsz != 124)            return 0;
    return 1;
}

/* ================================================================
 * 8.3 short name → human-readable filename
 * ================================================================ */

static void parse_short_name(const struct fat32dent *e, char *out, size_t sz)
{
    char base[9] = {0}, ext[4] = {0};
    memcpy(base, e->DIR_Name, 8);
    memcpy(ext,  e->DIR_Name + 8, 3);

    int bi = 7;
    while (bi >= 0 && base[bi] == ' ') bi--;
    base[bi + 1] = '\0';

    int ei = 2;
    while (ei >= 0 && ext[ei] == ' ') ei--;
    ext[ei + 1] = '\0';

    if (ext[0])
        snprintf(out, sz, "%s.%s", base, ext);
    else
        snprintf(out, sz, "%s", base);
}

/* ================================================================
 * LFN checksum (FAT spec) — with optional byte-0 override
 * ================================================================ */

static uint8_t lfn_checksum(const uint8_t *name)
{
    uint8_t sum = 0;
    for (int i = 0; i < 11; i++)
        sum = ((sum & 1) ? 0x80 : 0) + (sum >> 1) + name[i];
    return sum;
}

/* ================================================================
 * Extract LFN by walking backwards from the short entry.
 *
 * For DELETED entries the original seq byte is destroyed (Linux
 * replaces it with 0xE5), so we CANNOT rely on it.  Instead we:
 *   1. Read characters from the nearest LFN entry to determine the
 *      name length, then compute total_entries = ceil(len / 13).
 *   2. Collect exactly total_entries consecutive LFN entries
 *      (matching checksum) before the short entry.
 *   3. Read characters in seq order (farthest → nearest).
 *
 * For LIVE entries we still use the standard 0x40 + seq approach.
 * ================================================================ */

static void get_lfn(const struct fat32dent *se,
                    const uint8_t *cbuf, uint32_t csize,
                    char *out, size_t osz)
{
    parse_short_name(se, out, osz);

    const uint8_t *sp  = (const uint8_t *)se;
    uint32_t       sptr = (uint32_t)(sp - cbuf);
    if (sptr < 32) return;

    const uint8_t *prev = sp - 32;
    if ((prev[11] & 0x0F) != 0x0F) return;     /* no LFN at all */

    int is_del = (sp[0] == 0xE5);

    /* --- determine expected checksum --- */
    uint8_t chk;
    if (!is_del) {
        chk = lfn_checksum(se->DIR_Name);
    } else {
        uint8_t trial[11];
        memcpy(trial, se->DIR_Name, 11);
        int found = 0;
        uint8_t target = prev[13];
        for (int b = 0; b < 256; b++) {
            trial[0] = (uint8_t)b;
            if (lfn_checksum(trial) == target) { chk = target; found = 1; break; }
        }
        if (!found) return;
    }
    if (prev[13] != chk) return;                /* checksum must match */

    /* --- helper: count chars in a single LFN entry --- */
    #define COUNT_CHARS(ep) ({                                  \
        int _n = 0;                                             \
        for (int _k = 0; _k < 5; _k++)                          \
            if (rd16le((ep)+1+_k*2)==0) goto _c; else _n++;     \
        for (int _k = 0; _k < 6; _k++)                          \
            if (rd16le((ep)+14+_k*2)==0) goto _c; else _n++;    \
        for (int _k = 0; _k < 2; _k++)                          \
            if (rd16le((ep)+28+_k*2)==0) goto _c; else _n++;    \
        _c: _n;                                                 \
    })

    /* --- determine total LFN entry count --- */
    int total;
    if (!is_del) {
        total = prev[0] & 0x1F;               /* seq of last physical entry */
    } else {
        int nc = COUNT_CHARS(prev);
        total = (nc + 12) / 13;                /* ceil(nc / 13) */
    }
    #undef COUNT_CHARS

    if (total < 1 || total > 20) return;
    if (sptr < (uint32_t)total * 32) return;

    /* --- verify all total entries are valid LFN with correct chk --- */
    for (int i = 1; i <= total; i++) {
        uint32_t off = sptr - (uint32_t)i * 32;
        const uint8_t *ep = cbuf + off;
        if ((ep[11] & 0x0F) != 0x0F) return;
        if (ep[13] != chk) return;
    }

    /* --- read characters in physical order (farthest → nearest) ---
     *     Physical order = seq order: entry at offset (sptr - total*32)
     *     has seq 1, entry at (sptr - 32) has seq total.              */
    size_t pos = 0;
    for (int i = total; i >= 1 && pos < osz - 1; i--) {
        uint32_t off = sptr - (uint32_t)i * 32;
        const uint8_t *ep = cbuf + off;

        for (int k = 0; k < 5 && pos < osz - 1; k++) {
            uint16_t c = rd16le(ep + 1 + k * 2);
            if (c == 0) goto done;
            out[pos++] = (c < 128) ? (char)c : '_';
        }
        for (int k = 0; k < 6 && pos < osz - 1; k++) {
            uint16_t c = rd16le(ep + 14 + k * 2);
            if (c == 0) goto done;
            out[pos++] = (c < 128) ? (char)c : '_';
        }
        for (int k = 0; k < 2 && pos < osz - 1; k++) {
            uint16_t c = rd16le(ep + 28 + k * 2);
            if (c == 0) goto done;
            out[pos++] = (c < 128) ? (char)c : '_';
        }
    }
done:
    out[pos] = '\0';
    if (pos == 0) parse_short_name(se, out, osz);
}

/* ================================================================
 * SHA1 via external sha1sum(1)
 * ================================================================ */

static int compute_sha1(const char *path, char *out, size_t osz)
{
    char cmd[1024];
    snprintf(cmd, sizeof(cmd), "sha1sum '%s' 2>/dev/null", path);

    FILE *fp = popen(cmd, "r");
    if (!fp) return -1;

    char buf[256] = {0};
    if (!fgets(buf, sizeof(buf), fp)) { pclose(fp); return -1; }
    pclose(fp);

    if (strlen(buf) < 40) return -1;
    memcpy(out, buf, 40);
    out[40] = '\0';
    return 0;
}

/* ================================================================
 * Recover one file: extract data, write to /tmp, hash, print
 * ================================================================ */

static int do_recover(uint32_t start_cl, uint32_t file_size,
                      const uint8_t *data, const char *name)
{
    /* Dedup by start cluster */
    for (int i = 0; i < g_nfiles; i++)
        if (g_files[i].start_cluster == start_cl)
            return 0;

    char tmp[512];
    snprintf(tmp, sizeof(tmp), "/tmp/fsrecov_%u_%u.bmp",
             start_cl, file_size);

    FILE *fp = fopen(tmp, "wb");
    if (!fp) return 0;
    fwrite(data, 1, file_size, fp);
    fclose(fp);

    char sha1[64] = {0};
    if (compute_sha1(tmp, sha1, sizeof(sha1)) != 0) {
        unlink(tmp);
        return 0;
    }

    if (g_nfiles < MAX_RECOVERED) {
        g_files[g_nfiles].start_cluster = start_cl;
        g_files[g_nfiles].file_size     = file_size;
        strncpy(g_files[g_nfiles].filename, name,
                sizeof(g_files[0].filename) - 1);
        strncpy(g_files[g_nfiles].sha1, sha1,
                sizeof(g_files[0].sha1) - 1);
        g_nfiles++;
    }

    printf("%s  %s\n", sha1, name);
    unlink(tmp);
    return 1;
}

static int try_recover(uint32_t start_cl, uint32_t file_size,
                       const char *name)
{
    if (file_size == 0 || start_cl < 2 || start_cl >= g_total_clusters)
        return 0;

    uint32_t n_need = (file_size + g_cluster_size - 1) / g_cluster_size;
    if (start_cl + n_need - 1 >= g_total_clusters)
        return 0;

    uint32_t off = cluster_offset(start_cl);
    if (off + file_size > g_image_size)
        return 0;

    const uint8_t *data = g_img + off;
    if (!is_valid_bmp(data, file_size))
        return 0;

    return do_recover(start_cl, file_size, data, name);
}

/* ================================================================
 * Pass 1 — scan old directory entries
 *
 * Process both live and deleted short entries.  Deleted entries
 * (0xE5) often retain valid cluster / size (depending on the OS
 * that performed the deletion).
 * ================================================================ */

static void process_dir_cluster(uint32_t cl)
{
    uint32_t off = cluster_offset(cl);
    if (off + g_cluster_size > g_image_size)
        return;
    const uint8_t *cbuf = g_img + off;
    int dents = g_cluster_size / 32;

    for (int i = 0; i < dents; i++) {
        const struct fat32dent *e =
            (const struct fat32dent *)(cbuf + i * 32);
        const uint8_t *raw = cbuf + i * 32;

        if (raw[0] == 0x00) break;                /* end-of-directory */
        if ((e->DIR_Attr & 0x0F) == 0x0F) continue;  /* LFN — skip  */
        if (!(e->DIR_Attr & ATTR_ARCHIVE)) continue; /* not a file   */

        /* Extension must be BMP (case-insensitive) */
        char ext[4] = {0};
        memcpy(ext, e->DIR_Name + 8, 3);
        for (int j = 0; j < 3; j++)
            if (ext[j] >= 'a' && ext[j] <= 'z')
                ext[j] -= 32;
        if (strcmp(ext, "BMP") != 0)
            continue;

        uint32_t start_cl =
            ((uint32_t)e->DIR_FstClusHI << 16) | e->DIR_FstClusLO;
        uint32_t file_size = e->DIR_FileSize;

        if (start_cl < 2 || start_cl >= g_total_clusters) continue;
        if (file_size == 0 || file_size > g_image_size)   continue;

        uint32_t doff = cluster_offset(start_cl);
        if (doff + 2 > g_image_size) continue;
        if (g_img[doff] != 'B' || g_img[doff + 1] != 'M') continue;

        char filename[512] = {0};
        get_lfn(e, cbuf, g_cluster_size, filename, sizeof(filename));

        try_recover(start_cl, file_size, filename);
    }
}

/* ================================================================
 * Pass 2 — BMP signature scan
 *
 * For files whose directory entry has cluster=0 / size=0 (zeroed
 * by some OS drivers on delete), we scan every cluster in the data
 * area for a valid BMP header.  We read contiguous clusters until
 * we've accumulated file_size bytes or the next cluster starts with
 * "BM" (belonging to a different file).
 * ================================================================ */

static void signature_scan(void)
{
    for (uint32_t cl = 2; cl < g_total_clusters; cl++) {
        if (cluster_recovered(cl))
            continue;

        uint32_t off = cluster_offset(cl);
        if (off + 54 > g_image_size)
            break;

        const uint8_t *p = g_img + off;
        if (p[0] != 'B' || p[1] != 'M')
            continue;
        if (!is_valid_bmp(p, g_cluster_size))
            continue;

        uint32_t file_size = rd32le(p + 2);
        if (file_size > g_image_size - off)
            continue;

        uint32_t n_need = (file_size + g_cluster_size - 1) / g_cluster_size;

        /* Read contiguous clusters; stop if next cluster looks like
         * the start of another file (BM signature at offset 0).     */
        uint32_t actual = 1;
        for (uint32_t j = 1; j < n_need; j++) {
            uint32_t nc = cl + j;
            if (nc >= g_total_clusters) break;
            uint32_t noff = cluster_offset(nc);
            if (noff + 2 > g_image_size) break;
            if (g_img[noff] == 'B' && g_img[noff + 1] == 'M') break;
            if (cluster_recovered(nc)) break;
            actual++;
        }

        uint32_t avail = actual * g_cluster_size;
        uint32_t sz = (file_size <= avail) ? file_size : avail;

        char name[64];
        snprintf(name, sizeof(name), "recovered_%u.bmp", cl);

        do_recover(cl, sz, p, name);
    }
}

/* ================================================================
 * Top-level scan
 * ================================================================ */

static void scan_data_area(void)
{
    /* Pass 1: directory entries (gives us real filenames) */
    for (uint32_t cl = 3; cl < g_total_clusters; cl++)
        process_dir_cluster(cl);

    /* Pass 2: signature scan for files without valid dir entries */
    signature_scan();
}

/* ================================================================
 * Entry point
 * ================================================================ */

int main(int argc, char *argv[])
{
    if (argc < 2) {
        fprintf(stderr, "Usage: %s fs-image\n", argv[0]);
        exit(1);
    }

    setbuf(stdout, NULL);
    assert(sizeof(struct fat32hdr) == 512);

    struct fat32hdr *hdr = map_disk(argv[1]);
    g_img        = (uint8_t *)hdr;
    g_image_size = (size_t)hdr->BPB_TotSec32 * hdr->BPB_BytsPerSec;

    g_bps          = hdr->BPB_BytsPerSec;
    g_spc          = hdr->BPB_SecPerClus;
    g_cluster_size = g_bps * g_spc;
    g_data_offset  = (hdr->BPB_RsvdSecCnt +
                      hdr->BPB_NumFATs * hdr->BPB_FATSz32) * g_bps;
    g_total_clusters =
        (hdr->BPB_TotSec32 * g_bps - g_data_offset) / g_cluster_size;

    scan_data_area();

    munmap(hdr, g_image_size);
    return 0;
}

/* ================================================================
 * map_disk (unchanged)
 * ================================================================ */

void *map_disk(const char *fname)
{
    int fd = open(fname, O_RDONLY);

    if (fd < 0) {
        perror(fname);
        goto release;
    }

    off_t size = lseek(fd, 0, SEEK_END);
    if (size == -1) {
        perror(fname);
        goto release;
    }

    struct fat32hdr *hdr = mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
    if (hdr == (void *)-1) {
        goto release;
    }

    if (hdr->Signature_word != 0xaa55 ||
            hdr->BPB_TotSec32 * hdr->BPB_BytsPerSec != size) {
        fprintf(stderr, "%s: Not a FAT file image\n", fname);
        munmap(hdr, size);
        goto release;
    }
    close(fd);
    return hdr;

release:
    if (fd >= 0) {
        close(fd);
    }
    exit(1);
}
