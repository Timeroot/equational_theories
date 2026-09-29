// Exhaustive verification of the E677 TD(81,81) constructions.
// Input supplies finite-field arithmetic and block/group tables. No search.
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

int main() {
  int q, k, r;
  if (!(std::cin >> q >> k >> r) || q != 81 || k != 80 || r < 1 || r > q)
    throw std::runtime_error("bad construction parameters");
  auto read = [](int n) {
    std::vector<int> v(n);
    for (int &x : v) if (!(std::cin >> x)) throw std::runtime_error("short input");
    return v;
  };
  auto add = read(q*q), mult = read(q*q), neg = read(q), inv = read(q);
  auto small = read(k*k), large = read((k+1)*(k+1)), hole = read(r*r);
  const int n = k*q+r;
  std::vector<std::uint16_t> table(std::size_t(n)*n);
  std::uint64_t digest = 14695981039346656037ULL;
  for (int x = 0; x < n; ++x) {
    const int gx = x/q, ux = x%q;
    for (int y = 0; y < n; ++y) {
      const int gy = y/q, uy = y%q;
      int output;
      if (gx == gy) {
        output = gx*q + (gx == k ? hole[ux*r+uy] : large[ux*q+uy]);
      } else {
        const int difference = add[gy*q+neg[gx]];
        const int slope = mult[add[uy*q+neg[ux]]*q+inv[difference]];
        const int intercept = add[ux*q+neg[mult[gx*q+slope]]];
        const int extra = add[intercept*q+mult[k*q+slope]];
        const bool retained = extra < r;
        if (!retained && (gx == k || gy == k))
          throw std::runtime_error("missing input from transversal block");
        const int go = retained ? large[gx*(k+1)+gy] : small[gx*k+gy];
        if (go < 0 || go > k)
          throw std::runtime_error("invalid transversal block");
        const int uo = add[intercept*q+mult[go*q+slope]];
        if (go == k && uo >= r) throw std::runtime_error("output outside truncated group");
        output = go*q+uo;
      }
      if (output < 0 || output >= n) throw std::runtime_error("output outside carrier");
      table[std::size_t(x)*n+y] = output;
      digest = (digest ^ std::uint64_t(output))*1099511628211ULL;
    }
  }
  auto op = [&](int x, int y) { return int(table[std::size_t(x)*n+y]); };
  int idempotents = 0;
  for (int x = 0; x < n; ++x) {
    idempotents += op(x, x) == x;
    if (op(op(op(x, x), x), x) != x) throw std::runtime_error("E255 failed");
    for (int y = 0; y < n; ++y)
      if (op(y, op(x, op(op(y, x), y))) != x)
        throw std::runtime_error("E677 failed");
  }
  std::cout << "{\"law\":677,\"order\":" << n
            << ",\"pairs_checked\":" << std::uint64_t(n)*n
            << ",\"idempotents\":" << idempotents
            << ",\"e255\":true,\"table_fnv1a_values\":\"" << digest << "\"}\n";
}
