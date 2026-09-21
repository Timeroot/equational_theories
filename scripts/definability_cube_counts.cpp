// Exploratory exact model counts for E3342 and E3545, at orders two through five.
// Build: g++ -O3 scripts/definability_cube_counts.cpp -o /tmp/cube_counts
// Run: /tmp/cube_counts 5
// These computations are not Lean certificates and seed no definability facts.
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <map>
#include <numeric>
#include <vector>

using namespace std;

long long power(int n, int exponent) {
    long long value = 1;
    while (exponent-- > 0) value *= n;
    return value;
}

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    int n = atoi(argv[1]);
    if (n < 2 || n > 5) return 2;
    auto start = chrono::steady_clock::now();
    long long count_a = 0, count_b = 0, identity = 0;
    vector<int> f(n), parent(n * n), component(n * n), values(n * n), table(n * n);
    function<int(int)> root = [&](int i) {
        return parent[i] == i ? i : parent[i] = root(parent[i]);
    };
    for (int code = 0; code < power(n, n); code++) {
        int remaining = code, moved = 0;
        bool two_cycle = false;
        for (int x = 0; x < n; x++) {
            f[x] = remaining % n;
            remaining /= n;
            moved += f[x] != x;
        }
        // The identity-twist contribution is the same for both laws:
        // tables are symmetric, and their diagonal q has no two-cycles.
        // Each nonfixed diagonal value q(x) forces the entry {x,q(x)} to x.
        // All remaining unordered off-diagonal entries can be chosen freely.
        for (int x = 0; x < n; x++)
            two_cycle |= f[x] != x && f[f[x]] == x;
        if (!two_cycle) identity += power(n, n * (n - 1) / 2 - moved);
        if (moved == 0) continue;

        // For a prescribed cube map f, either law says
        // table[x,y] = table[y,f(x)]. Union-find identifies these cells.
        // Each operation is counted once because its actual cube map is unique.
        iota(parent.begin(), parent.end(), 0);
        for (int x = 0; x < n; x++)
            for (int y = 0; y < n; y++)
                parent[root(x * n + y)] = root(y * n + f[x]);
        int components = 0;
        map<int, int> ids;
        for (int i = 0; i < n * n; i++) {
            int r = root(i);
            if (!ids.count(r)) ids[r] = components++;
            component[i] = ids[r];
        }
        function<void(int)> enumerate = [&](int k) {
            if (k < components) {
                for (int value = 0; value < n; value++) {
                    values[k] = value;
                    enumerate(k + 1);
                }
                return;
            }
            for (int i = 0; i < n * n; i++) table[i] = values[component[i]];
            bool a = true, b = true;
            for (int x = 0; x < n && (a || b); x++) {
                int q = table[x * n + x];
                a &= table[x * n + q] == f[x];
                b &= table[q * n + x] == f[x];
            }
            count_a += a;
            count_b += b;
        };
        enumerate(0);
    }
    cout << "{\"order\":" << n << ",\"E3342\":" << count_a + identity
         << ",\"E3545\":" << count_b + identity
         << ",\"identity_twist_contribution\":" << identity
         << ",\"seconds\":" << chrono::duration<double>(chrono::steady_clock::now() - start).count()
         << "}\n";
}
