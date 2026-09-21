// Complete necessary-incidence reduction for A12 with all beta=eta=1.
// The historical filename is retained; no thin-line premise is used.
// Standard C++17, no SAT solver or external certificate.

#ifdef NDEBUG
#error "This exhaustive checker requires active assertions."
#endif

#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>

constexpr int N = 8;
using Rows = std::array<int, N>;
using Four = std::array<int, 4>;
constexpr Rows SHARP = {2, 2, 2, 2, 1, 1, 1, 1};
constexpr Rows DEGREE = {2, 2, 2, 2, 3, 3, 3, 3};

int size(int mask) {
    int result = 0;
    while (mask) { mask &= mask - 1; ++result; }
    return result;
}
bool has(int mask, int vertex) { return (mask >> vertex) & 1; }

Rows transpose(const Rows& rows) {
    Rows columns{};
    for (int i = 0; i < N; ++i)
        for (int j = 0; j < N; ++j)
            if (has(rows[i], j)) columns[j] |= 1 << i;
    return columns;
}

bool partial_conditions(const Rows& D, const Rows& C, int depth) {
    for (int a = 0; a < depth; ++a) {
        int seen = 0;
        for (int middle = 0; middle < depth; ++middle) {
            if (!has(D[a], middle)) continue;
            if (size(C[a] & D[middle]) != 1) return false; // beta=1
            if (seen & D[middle] & ~C[a]) return false;
            seen |= D[middle];
        }
    }
    return true;
}

bool balanced(const Rows& D, const Rows& C) {
    const auto Dt = transpose(D), Ct = transpose(C);
    for (int b = 0; b < N; ++b)
        for (int d = 0; d < N; ++d)
            if (has(D[b], d) && size(Dt[b] & Ct[d]) != 1) return false;
    return true;
}

bool one_A_closure(const Rows& D, const Rows& C) {
    for (int a = 0; a < N; ++a)
        for (int b = 0; b < N; ++b) if (has(D[a], b))
            for (int c = 0; c < N; ++c) if (has(D[b], c))
                for (int d = 0; d < N; ++d)
                    if (has(D[c], d) && has(C[d], a) &&
                        has(C[a], c) != has(C[b], d)) return false;
    return true;
}

bool return_capacities(const Rows& D, const Rows& C) {
    const auto Dt = transpose(D), Ct = transpose(C);
    for (int b = 0; b < N; ++b) {
        for (int d = 0; d < N; ++d) {
            const bool A_return = has(C[b], d);
            const bool B_return = !A_return && (D[b] & Dt[d]);
            const int fiber = A_return ? 8 : B_return ? 5 : 4;
            int good = 0;
            for (int x = 0; x < N; ++x) if (has(D[d], x))
                for (int y = 0; y < N; ++y)
                    if (has(D[x], y) && has(D[y], b) &&
                        !has(C[d], y) && !has(C[x], b)) ++good;
            if (good > fiber - SHARP[b] - SHARP[d]) return false;
            const int mixed = good + size(C[d] & Dt[b]) + size(D[d] & Ct[b]);
            if (mixed > 4) return false;
            // Both boundary bad-extension counts equal one for B returns.
            if (B_return && (mixed < 1 || mixed > 3)) return false;
        }
    }
    return true;
}

// Four two-element neighbor sets are the edges of a connected four-cycle
// on the four low vertices. No isomorphism or visual recognition is used.
bool low_cycle(const Rows& rows) {
    std::array<int, 4> degree{}, adjacency{};
    for (int i = 0; i < 4; ++i) {
        const int endpoints = rows[i] >> 4;
        if ((rows[i] & 15) || size(endpoints) != 2) return false;
        for (int a = 0; a < 4; ++a) if (has(endpoints, a)) {
            ++degree[a];
            adjacency[a] |= endpoints & ~(1 << a);
        }
    }
    if (degree != Four{2, 2, 2, 2}) return false;
    int reached = 1;
    for (int pass = 0; pass < 4; ++pass)
        for (int a = 0; a < 4; ++a)
            if (has(reached, a)) reached |= adjacency[a];
    return reached == 15;
}

std::set<Rows> sharp_classes() {
    std::set<Four> medium, low;
    std::vector<int> options;
    for (int row = 0; row < 16; ++row) if (size(row) == 2) options.push_back(row);
    for (int a : options) for (int b : options)
        for (int c : options) for (int d : options) {
            const Four rows = {a, b, c, d};
            Four columns{};
            for (int row : rows)
                for (int j = 0; j < 4; ++j) columns[j] += has(row, j);
            if (columns != Four{2, 2, 2, 2}) continue;
            Four best = rows, labels = {0, 1, 2, 3};
            do {
                Four transformed{};
                for (int i = 0; i < 4; ++i)
                    for (int j = 0; j < 4; ++j)
                        if (has(rows[i], j)) transformed[labels[i]] |= 1 << labels[j];
                best = std::min(best, transformed);
            } while (std::next_permutation(labels.begin(), labels.end()));
            medium.insert(best);
        }
    Four permutation = {0, 1, 2, 3};
    do {
        Four best = permutation, labels = {0, 1, 2, 3};
        do {
            Four transformed{};
            for (int i = 0; i < 4; ++i) transformed[labels[i]] = labels[permutation[i]];
            best = std::min(best, transformed);
        } while (std::next_permutation(labels.begin(), labels.end()));
        low.insert(best);
    } while (std::next_permutation(permutation.begin(), permutation.end()));
    assert(medium.size() == 8 && low.size() == 5);
    std::set<Rows> result;
    for (const auto& m : medium) for (const auto& l : low) {
        Rows rows{};
        for (int i = 0; i < 4; ++i) {
            rows[i] = m[i];
            rows[i + 4] = 1 << (l[i] + 4);
        }
        result.insert(rows);
    }
    return result;
}

struct Counts {
    std::uint64_t nodes = 0, full = 0, balance = 0, closure = 0, returns = 0;
};

struct Search {
    const Rows& C;
    const std::array<std::vector<int>, N>& choices;
    Counts& counts;
    Rows D{}, capacity = DEGREE;

    void extend(int depth) {
        ++counts.nodes;
        if (depth == N) {
            assert(capacity == Rows{});
            ++counts.full;
            if (!balanced(D, C)) return;
            ++counts.balance;
            if (!one_A_closure(D, C)) return;
            ++counts.closure;
            if (!return_capacities(D, C)) return;
            ++counts.returns;
            assert(low_cycle(D));
            assert(low_cycle(transpose(D)));
            return;
        }
        for (int row : choices[depth]) {
            bool fits = true;
            for (int j = 0; j < N; ++j)
                if (has(row, j) && capacity[j] == 0) fits = false;
            if (!fits) continue;
            for (int j = 0; j < N; ++j) capacity[j] -= has(row, j);
            D[depth] = row;
            if (*std::max_element(capacity.begin(), capacity.end()) <= N - 1 - depth
                && partial_conditions(D, C, depth + 1)) extend(depth + 1);
            for (int j = 0; j < N; ++j) capacity[j] += has(row, j);
        }
    }
};

void positive_controls() {
    const Rows C = {3, 3, 12, 12, 16, 32, 64, 128};
    const Rows D = {48, 192, 80, 160, 133, 73, 38, 26};
    const auto Dt = transpose(D), Ct = transpose(C);
    for (int i = 0; i < N; ++i) {
        assert(size(D[i]) == DEGREE[i] && size(Dt[i]) == DEGREE[i]);
        assert(size(C[i]) == SHARP[i] && size(Ct[i]) == SHARP[i]);
    }
    assert(partial_conditions(D, C, N));
    assert(balanced(D, C));
    assert(one_A_closure(D, C));
    assert(return_capacities(D, C));
    assert(low_cycle(D) && low_cycle(transpose(D)));
    // A disconnected pair of doubled edges is not a four-cycle.
    const Rows disconnected = {48, 48, 192, 192, 0, 0, 0, 0};
    assert(!low_cycle(disconnected));
}

int main() {
    const auto started = std::chrono::steady_clock::now();
    positive_controls();
    const auto classes = sharp_classes();
    assert(classes.size() == 40);
    std::array<std::vector<int>, N> choices;
    for (int i = 0; i < N; ++i)
        for (int row = 0; row < (1 << N); ++row)
            if (size(row) == DEGREE[i]) choices[i].push_back(row);
    Counts counts;
    for (const auto& C : classes) Search{C, choices, counts}.extend(0);
    assert(counts.nodes == 3984137);
    assert(counts.full == 21272 && counts.balance == 21025);
    assert(counts.closure == 316 && counts.returns == 56);
    std::cout << "PROVED REDUCTION: both medium/low incidence graphs are four-cycles\n"
              << "C classes: " << classes.size() << "; partial nodes: " << counts.nodes
              << "; full D: " << counts.full << "; balanced: " << counts.balance
              << "; one-A closure: " << counts.closure
              << "; return capacities: " << counts.returns << '\n'
              << "Every survivor has D_MM=0 and both checked four-cycles.\nElapsed: "
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count()
              << "s\n";
}
