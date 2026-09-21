// Exhaust all triples of distinct operation-table positions, allowing mixed factors.
// Input: three blocks, each containing order, factor ID, source table, target table.
// Repeated factor IDs must describe the same pair of tables.
// A pass asserts three-position interpolation, not full term definability.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>

int main(int argc, char **argv) {
    if (argc != 3) {
        std::cerr << "usage: interpolation3 INPUT OUTPUT\n";
        return 2;
    }
    std::ifstream in(argv[1]);
    int n[3], id[3];
    std::vector<int> source[3], target[3];
    for (int k = 0; k < 3; ++k) {
        if (!(in >> n[k] >> id[k]) || n[k] < 1 || n[k] > 40) return 2;
        source[k].resize(n[k] * n[k]);
        target[k].resize(n[k] * n[k]);
        for (auto *table : {&source[k], &target[k]})
            for (int &x : *table)
                if (!(in >> x) || x < 0 || x >= n[k]) return 2;
        for (int j = 0; j < k; ++j)
            if (id[j] == id[k] &&
                (n[j] != n[k] || source[j] != source[k] || target[j] != target[k]))
                return 2;
    }
    const int stride = n[1] * n[2], size = n[0] * stride;
    std::vector<uint16_t> product(static_cast<size_t>(size) * size);
    for (int a = 0; a < size; ++a)
        for (int b = 0; b < size; ++b)
            product[static_cast<size_t>(a) * size + b] =
                stride * source[0][(a / stride) * n[0] + b / stride] +
                n[2] * source[1][(a / n[2] % n[1]) * n[1] + b / n[2] % n[1]] +
                source[2][(a % n[2]) * n[2] + b % n[2]];

    std::vector<uint32_t> seen(size);
    uint32_t stamp = 0;
    std::vector<int> members;
    members.reserve(size);
    uint64_t cases = 0;
    for (int c = 0; c < n[0] * n[0]; ++c)
        for (int d = 0; d < n[1] * n[1]; ++d)
            for (int e = 0; e < n[2] * n[2]; ++e) {
                // Permuting coordinates from the same factor repeats the same test.
                if ((id[0] == id[1] && c >= d) || (id[1] == id[2] && d >= e) ||
                    (id[0] == id[2] && c >= e)) continue;
                const int u = stride * (c / n[0]) + n[2] * (d / n[1]) + e / n[2];
                const int v = stride * (c % n[0]) + n[2] * (d % n[1]) + e % n[2];
                const int w = stride * target[0][c] + n[2] * target[1][d] + target[2][e];
                ++stamp;
                members.clear();
                seen[u] = stamp;
                members.push_back(u);
                if (v != u) {
                    seen[v] = stamp;
                    members.push_back(v);
                }
                // Close the two projection tuples under the coordinatewise operation.
                for (size_t i = 0; i < members.size() && seen[w] != stamp; ++i) {
                    const int a = members[i];
                    for (size_t j = 0; j <= i && seen[w] != stamp; ++j) {
                        const int b = members[j];
                        for (int r : {product[static_cast<size_t>(a) * size + b], product[static_cast<size_t>(b) * size + a]})
                            if (seen[r] != stamp) {
                                seen[r] = stamp;
                                members.push_back(r);
                            }
                    }
                }
                ++cases;
                if (seen[w] != stamp) {
                    std::ofstream out(argv[2]);
                    out << "{\"order\":" << size << ",\"passed\":false,\"positions\":["
                        << c << ',' << d << ',' << e << "],\"missing\":" << w
                        << ",\"members\":[";
                    for (size_t i = 0; i < members.size(); ++i)
                        out << (i ? "," : "") << members[i];
                    out << "],\"tested\":" << cases << "}\n";
                    return 0;
                }
            }
    std::ofstream out(argv[2]);
    out << "{\"order\":" << size << ",\"passed\":true,\"tested\":" << cases << "}\n";
}
