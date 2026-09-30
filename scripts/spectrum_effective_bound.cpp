// Positive construction closure for the E677/E1083/E1286 bound certificates.
// This program is a reproducible finite computation, not a Lean proof.
// Input: checked seed orders and idempotence flags. Output: a packed bitmap.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

using Word = std::uint64_t;
using Order = std::int64_t;

class Orders {
 public:
  explicit Orders(int bound) : words_((Order(bound) + 128) / 64), bound_(bound) {}
  bool has(int n) const { return (words_[n / 64] >> (n % 64)) & 1; }
  void add(int n) { words_[n / 64] |= Word(1) << (n % 64); }

  // Add offset + r for the already certified r <= end. The two accessed
  // regions are disjoint in every use below. A common point excludes r = 0.
  void translate(int offset, int end, bool common_point = false) {
    end = std::min(end, bound_ - offset);
    if (end < 0) return;
    const Word* __restrict source = words_.data();
    Word* __restrict target = words_.data() + offset / 64;
    const int bits = offset % 64;
    const int last_word = end / 64;
    Word first = source[0] & ~Word(common_point);
    if (!last_word) {
      if (end % 64 < 63) first &= (Word(1) << (end % 64 + 1)) - 1;
      target[0] |= first << bits;
      if (bits) target[1] |= first >> (64 - bits);
      return;
    }
    target[0] |= first << bits;
    if (!bits) {
      for (int i = 1; i < last_word; ++i) target[i] |= source[i];
    } else {
      if (last_word > 1)
        target[1] |= (source[1] << bits) | (first >> (64 - bits));
      for (int i = 2; i < last_word; ++i)
        target[i] |= (source[i] << bits) | (source[i - 1] >> (64 - bits));
    }
    Word last = source[last_word];
    if (end % 64 < 63) last &= (Word(1) << (end % 64 + 1)) - 1;
    const Word previous = last_word == 1 ? first : source[last_word - 1];
    target[last_word] |= (last << bits) | (bits ? previous >> (64 - bits) : 0);
    if (bits) target[last_word + 1] |= last >> (64 - bits);
  }

  bool save(const char* path) const {
    auto* file = std::fopen(path, "wb");
    if (!file) return false;
    const auto bytes = (Order(bound_) + 8) / 8;
    const bool success = std::fwrite(words_.data(), 1, bytes, file) == std::size_t(bytes);
    return std::fclose(file) == 0 && success;
  }

 private:
  std::vector<Word> words_;
  int bound_;
};

int main(int argc, char** argv) {
  if (argc < 4 || argc > 6) {
    std::fprintf(stderr, "usage: %s SEEDS.tsv BOUND OUTPUT.bin [LAW [IDEMPOTENT.bin]]\n", argv[0]);
    return 2;
  }
  const int bound = std::atoi(argv[2]);
  const int law = argc >= 5 ? std::atoi(argv[4]) : 677;
  if (law != 677 && law != 1083 && law != 1286) return 2;
  const int minimum = law == 1083 ? 3 : law == 1286 ? 7 : 5;
  if (bound < 16 || bound > 1000000000) return 2;
  Orders known(bound), idempotent(bound);
  known.add(0); known.add(1); idempotent.add(0); idempotent.add(1);
  auto* seeds = std::fopen(argv[1], "r");
  if (!seeds) { std::perror("seeds"); return 1; }
  int order, idem;
  while (std::fscanf(seeds, "%d %d", &order, &idem) == 2) {
    if (order < minimum || order > bound || (idem != 0 && idem != 1)) return 2;
    known.add(order);
    if (idem) idempotent.add(order);
  }
  std::fclose(seeds);
  for (Order n = 2; n*n*n*n <= bound; ++n) {
    known.add(n*n*n*n);
    idempotent.add(n*n*n*n);
  }
  if (law == 677)
    known.add(9);  // The pointed model checked by the E677 Python driver.
  if (law == 1083)
    for (Order n = 2; n*n <= bound; ++n) known.add(n*n);

  // No product or design can introduce a new order beyond this input limit.
  const int limit = (bound + minimum - 1) / minimum;
  std::vector<int> smallest(limit + 1), least_power(limit + 1, limit + 1);
  for (int p = 2; p <= limit; ++p)
    if (!smallest[p])
      for (int n = p; n <= limit; n += p)
        if (!smallest[n]) smallest[n] = p;
  for (int n = 2; n <= limit; ++n) {
    const int p = smallest[n];
    int factor = 1, rest = n;
    while (rest % p == 0) { factor *= p; rest /= p; }
    least_power[n] = std::min(factor, least_power[rest]);
  }

  const int root = int(std::sqrt(bound));
  std::vector<int> small_models, blocks;
  for (int n = 2; n <= limit; ++n) {
    if (idempotent.has(n) && n <= root + 2) blocks.push_back(n);
    if (!known.has(n)) continue;
    if (n <= root) small_models.push_back(n);

    // Cartesian products, including idempotent products.
    for (int factor : small_models) {
      if (Order(factor) * n > bound) break;
      known.add(factor * n);
      if (idempotent.has(n) && idempotent.has(factor)) idempotent.add(factor * n);
    }

    // Identify a fixed point in all groups of a TD(k,n-1).
    const int q0 = n - 1;
    for (int k : blocks) {
      if (k > least_power[q0] + 1 || Order(k) * q0 + 1 > bound) break;
      known.add(k * q0 + 1);
      if (idempotent.has(n)) idempotent.add(k * q0 + 1);
    }

    // One truncated group, with or without a shared fixed point.
    for (int common = 0; common <= 1; ++common) {
      const int q = n - common;
      for (int k : blocks) {
        if (k > least_power[q] || Order(k) * q > bound) break;
        if (!idempotent.has(k + 1)) continue;
        known.translate(k * q, q + common, common);
        if (idempotent.has(n)) idempotent.translate(k * q, q + common, common);
      }
    }
  }
  if (!known.save(argv[3])) { std::perror("bitmap"); return 1; }
  if (argc == 6 && !idempotent.save(argv[5])) { std::perror("idempotent bitmap"); return 1; }
  return 0;
}
