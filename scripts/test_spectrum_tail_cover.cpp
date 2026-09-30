// Low-level checks for the compressed finite-spectrum certificate replay.
// c++ -O2 -fsanitize=address,undefined scripts/test_spectrum_tail_cover.cpp -o /tmp/test-spectrum-cover
// /tmp/test-spectrum-cover
#define main spectrum_cover_checker_main
#include "spectrum_tail_cover_check.cpp"
#undef main
#include <random>

int main() {
  std::mt19937_64 random(12345);
  for (int test = 0; test < 100000; ++test) {
    std::vector<Word> source(16);
    for (auto& word : source) word = random();
    const Order offset = random()%4000, lo = random()%4500;
    const Order hi = lo+random()%700, end = random()%1024;
    const bool common = random()%2;
    std::vector<Word> actual((hi-lo+64)/64), expected(actual.size());
    translate(source, actual, lo, hi, offset, end, common);
    // Independent, pointwise specification; exercise unaligned endpoints,
    // clipping, empty intersections, and exclusion of the common point.
    for (Order n = lo; n <= hi; ++n) {
      const Order r = n-offset;
      if (r >= common && r <= end && r < 1024 && ((source[r/64] >> (r%64)) & 1))
        expected[(n-lo)/64] |= Word(1) << ((n-lo)%64);
    }
    require(actual == expected, "Translation differs from its pointwise specification");
  }

  for (int test = 0; test < 1000; ++test) {
    std::vector<Word> source((100000+63)/64);
    for (auto& word : source) word = random() | random() | random();
    const Order lo = random()%3000, hi = lo+50000+random()%40000;
    std::vector<Word> reference((hi-lo+64)/64), cached(reference.size());
    std::vector<unsigned char> full((cached.size()+511)/512);
    for (int step = 0; step < 100; ++step) {
      const Order offset = random()%40000, end = random()%100000;
      const bool common = random()%2;
      translate(source, reference, lo, hi, offset, end, common);
      translate_cached(source, cached, full, lo, hi, offset, end, common);
      require(reference == cached, "Skipping completed blocks changed the union");
    }
  }
  std::puts("100000 pointwise comparisons and 100000 cached-union comparisons passed.");
}
