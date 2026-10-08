// An independent, unverified C implementation of Tree-RSSA with the same arithmetic as the
// Lean specification: heap sum tree, population brackets, xoshiro256++ seeded through
// SplitMix64, exponentials -log V. It serves two purposes in the benchmark:
//   * a cross-check: its final populations must equal those of every Lean generation for the
//     same seed (bench/generations.py compares the digests);
//   * a calibration of the Lean code against straightforward C.
// build: cc -O3 -march=native -o treerssa bench/c/treerssa.c -lm
// usage: treerssa <model.rn> <T> [seed]
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef struct { int nr; int *rs; int *rn; int nc; int *cs; long *cd; double rate; } Rx;

static uint64_t s0, s1, s2, s3;
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t next(void) {
  uint64_t result = rotl(s0 + s3, 23) + s0, t = s1 << 17;
  s2 ^= s0; s3 ^= s1; s1 ^= s2; s0 ^= s3; s2 ^= t; s3 = rotl(s3, 45);
  return result;
}
static uint64_t splitmix(uint64_t *x) {
  uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}
static const double P53 = 1.1102230246251565e-16, P52 = 2.220446049250313e-16;

static int S, M, depth, leaves;
static long *pop, *lo, *hi, *ms;
static Rx *rx;
static int **deps, *ndeps;
static double *lower, *tree;

static inline unsigned long ff(unsigned long n, int nu) {
  unsigned long r = 1;
  for (int k = 0; k < nu; k++) { if (n < (unsigned long)(k + 1)) return 0; r *= (n - k); }
  return r;
}
static inline double prop(const Rx *r, const long *arr) {
  unsigned long c = 1;
  for (int i = 0; i < r->nr; i++) c *= ff((unsigned long)arr[r->rs[i]], r->rn[i]);
  return r->rate * (double)c;
}
static void bracket(long m, long n, long *l, long *h) {
  if (n == 0) { *l = 0; *h = 0; }
  else if (n < m) { *l = n; *h = n; }
  else if (n < 25) { *l = n >= 4 ? n - 4 : 0; *h = n + 4; }
  else { *l = 9 * n / 10; *h = 11 * n / 10; }
}
static inline int stale(long m, long n, long l, long h) { return n < l || h < n || (n < m && h != n); }

int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r");
  double T = atof(argv[2]);
  uint64_t seed = argc > 3 ? strtoull(argv[3], 0, 10) : 1;
  char tag[64];
  if (fscanf(f, "%63s %*d", tag) != 1) return 1;
  if (fscanf(f, "%63s %d", tag, &S) != 2) return 1;
  pop = calloc(S, sizeof(long)); lo = calloc(S, sizeof(long)); hi = calloc(S, sizeof(long));
  ms = calloc(S, sizeof(long));
  for (int s = 0; s < S; s++) if (fscanf(f, "%ld", &pop[s]) != 1) return 1;
  if (fscanf(f, "%63s %d", tag, &M) != 2) return 1;
  rx = calloc(M, sizeof(Rx));
  for (int j = 0; j < M; j++) {
    char hex[32]; uint64_t bits;
    if (fscanf(f, "%31s", hex) != 1) return 1;
    bits = strtoull(hex, 0, 16); memcpy(&rx[j].rate, &bits, 8);
    if (fscanf(f, "%d", &rx[j].nr) != 1) return 1;
    rx[j].rs = calloc(rx[j].nr + 1, sizeof(int)); rx[j].rn = calloc(rx[j].nr + 1, sizeof(int));
    for (int i = 0; i < rx[j].nr; i++) if (fscanf(f, "%d %d", &rx[j].rs[i], &rx[j].rn[i]) != 2) return 1;
    if (fscanf(f, "%d", &rx[j].nc) != 1) return 1;
    rx[j].cs = calloc(rx[j].nc + 1, sizeof(int)); rx[j].cd = calloc(rx[j].nc + 1, sizeof(long));
    for (int i = 0; i < rx[j].nc; i++) if (fscanf(f, "%d %ld", &rx[j].cs[i], &rx[j].cd[i]) != 2) return 1;
    for (int i = 0; i < rx[j].nr; i++) if (rx[j].rn[i] > ms[rx[j].rs[i]]) ms[rx[j].rs[i]] = rx[j].rn[i];
  }
  deps = calloc(S, sizeof(int *)); ndeps = calloc(S, sizeof(int));
  for (int j = 0; j < M; j++) for (int i = 0; i < rx[j].nr; i++) ndeps[rx[j].rs[i]]++;
  for (int s = 0; s < S; s++) { deps[s] = calloc(ndeps[s] + 1, sizeof(int)); ndeps[s] = 0; }
  for (int j = 0; j < M; j++) for (int i = 0; i < rx[j].nr; i++) { int s = rx[j].rs[i]; deps[s][ndeps[s]++] = j; }
  depth = 0; { unsigned m = M - 1; int lg = 0; while (m >>= 1) lg++; depth = lg + 1; }
  if (M <= 1) depth = 1;
  leaves = 1 << depth;
  for (int s = 0; s < S; s++) bracket(ms[s], pop[s], &lo[s], &hi[s]);
  lower = calloc(M, sizeof(double)); tree = calloc(2 * leaves, sizeof(double));
  uint64_t x = seed; s0 = splitmix(&x); s1 = splitmix(&x); s2 = splitmix(&x); s3 = splitmix(&x);
  struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
  for (int j = 0; j < M; j++) { lower[j] = prop(&rx[j], lo); tree[leaves + j] = prop(&rx[j], hi); }
  for (int k = leaves - 1; k >= 1; k--) tree[k] = tree[2 * k] + tree[2 * k + 1];
  double now = 0; long events = 0;
  for (;;) {
    double total = tree[1];
    if (!(total > 0)) break;
    double elapsed = 0; int j;
    for (;;) {
      double u = (double)(next() >> 11) * P53;
      double xx = u * total; int k = 1;
      for (int d = 0; d < depth; d++) { double l = tree[2 * k]; if (xx < l) k = 2 * k; else { k = 2 * k + 1; xx -= l; } }
      j = k - leaves;
      double e = -log(((double)(next() >> 12) + 0.5) * P52);
      elapsed += e;
      double v = (double)(next() >> 11) * P53;
      if (j < M) {
        double th = v * tree[leaves + j], l = lower[j];
        if ((0 < l && th <= l)) break;
        double a = prop(&rx[j], pop);
        if (0 < a && th <= a) break;
      }
    }
    double t = now + elapsed / total;
    if (t > T) break;
    now = t; events++;
    for (int i = 0; i < rx[j].nc; i++) { long *p = &pop[rx[j].cs[i]]; *p = *p + rx[j].cd[i]; if (*p < 0) *p = 0; }
    for (int i = 0; i < rx[j].nc; i++) {
      int s = rx[j].cs[i];
      if (stale(ms[s], pop[s], lo[s], hi[s])) {
        bracket(ms[s], pop[s], &lo[s], &hi[s]);
        for (int q = 0; q < ndeps[s]; q++) {
          int kk = deps[s][q];
          lower[kk] = prop(&rx[kk], lo);
          double up = prop(&rx[kk], hi);
          int leaf = leaves + kk;
          if (up != tree[leaf] || signbit(up) != signbit(tree[leaf])) {
            tree[leaf] = up;
            for (int n = leaf / 2; n >= 1; n /= 2) tree[n] = tree[2 * n] + tree[2 * n + 1];
          }
        }
      }
    }
  }
  clock_gettime(CLOCK_MONOTONIC, &t1);
  double secs = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
  uint64_t h = 0xcbf29ce484222325ULL;
  for (int s = 0; s < S; s++) h = (h ^ (uint64_t)pop[s]) * 0x100000001b3ULL;
  printf("{\"events\": %ld, \"seconds\": %.6f, \"rate\": %.4g, \"digest\": \"%llu\"}\n", events, secs,
         events / secs, (unsigned long long)h);
  return 0;
}
