// Exact necessary-incidence exclusion, not a search for 40-point magmas.
// Build with c++ -O3 -std=c++17.
// Run: /tmp/1485_n40_twelve_one_high_loop_check

#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>

constexpr int N = 7;
using Array = std::array<int, N>;
constexpr Array DEGREE = {2, 2, 3, 3, 3, 3, 3};

int cardinality(int mask) {
    int result = 0;
    while (mask) {
        mask &= mask - 1;
        ++result;
    }
    return result;
}

bool contains(int mask, int vertex) { return (mask >> vertex) & 1; }

// Only rows below depth have been assigned. Every counted two-step path
// already has both its edges fixed, so a violation cannot be repaired later.
bool no_repeated_good_middle(const Array& rows, const Array& target,
                             int depth = N) {
    for (int a = 0; a < depth; ++a) {
        int seen = 0;
        for (int middle = 0; middle < depth; ++middle) {
            if (!contains(rows[a], middle)) continue;
            if (seen & rows[middle] & ~(1 << target[a])) return false;
            seen |= rows[middle];
        }
    }
    return true;
}

bool edge_balance(const Array& rows, const Array& target) {
    Array inverse{};
    for (int i = 0; i < N; ++i) inverse[target[i]] = i;
    for (int b = 0; b < N; ++b) {
        for (int d = 0; d < N; ++d) {
            if (contains(rows[b], d) &&
                contains(rows[d], target[b]) != contains(rows[inverse[d]], b))
                return false;
        }
    }
    return true;
}

bool one_A_closure(const Array& rows, const Array& target) {
    for (int a = 0; a < N; ++a)
        for (int b = 0; b < N; ++b) {
            if (!contains(rows[a], b)) continue;
            for (int c = 0; c < N; ++c) {
                if (!contains(rows[b], c)) continue;
                for (int d = 0; d < N; ++d)
                    if (contains(rows[c], d) && target[d] == a &&
                        (target[a] == c) != (target[b] == d))
                        return false;
            }
        }
    return true;
}

bool correct_degrees(const Array& rows) {
    Array columns{};
    for (int i = 0; i < N; ++i) {
        if (cardinality(rows[i]) != DEGREE[i]) return false;
        for (int j = 0; j < N; ++j) columns[j] += contains(rows[i], j);
    }
    return columns == DEGREE;
}

std::set<Array> sharp_permutation_classes() {
    Array permutation{};
    std::iota(permutation.begin(), permutation.end(), 0);
    std::set<Array> classes;
    do {
        Array best = permutation;
        std::array<int, 5> low = {2, 3, 4, 5, 6};
        do {
            for (int swap = 0; swap < 2; ++swap) {
                Array labels = {swap, 1 - swap, low[0], low[1], low[2],
                                low[3], low[4]};
                Array transformed{};
                for (int i = 0; i < N; ++i)
                    transformed[labels[i]] = labels[permutation[i]];
                best = std::min(best, transformed);
            }
        } while (std::next_permutation(low.begin(), low.end()));
        classes.insert(best);
    } while (std::next_permutation(permutation.begin(), permutation.end()));
    return classes;
}

struct Counts {
    std::uint64_t partial_nodes = 0;
    std::uint64_t full_matrices = 0;
    std::uint64_t balanced_matrices = 0;
    std::uint64_t surviving_matrices = 0;
};

struct Search {
    const Array& target;
    const std::array<std::vector<int>, N>& choices;
    Counts& counts;
    Array rows{};
    Array capacity = DEGREE;

    void extend(int depth) {
        ++counts.partial_nodes;
        if (depth == N) {
            assert(correct_degrees(rows));
            assert(no_repeated_good_middle(rows, target));
            ++counts.full_matrices;
            if (!edge_balance(rows, target)) return;
            ++counts.balanced_matrices;
            if (one_A_closure(rows, target)) ++counts.surviving_matrices;
            return;
        }
        for (int row : choices[depth]) {
            bool fits = true;
            for (int j = 0; j < N; ++j)
                if (contains(row, j) && capacity[j] == 0) fits = false;
            if (!fits) continue;
            for (int j = 0; j < N; ++j) capacity[j] -= contains(row, j);
            rows[depth] = row;
            if (*std::max_element(capacity.begin(), capacity.end()) <= N - 1 - depth
                && no_repeated_good_middle(rows, target, depth + 1))
                extend(depth + 1);
            for (int j = 0; j < N; ++j) capacity[j] += contains(row, j);
        }
    }
};

void positive_controls() {
    const Array identity = {0, 1, 2, 3, 4, 5, 6};
    // A genuine partial-incidence survivor through every test except closure.
    const Array near_candidate = {5, 24, 97, 42, 82, 76, 52};
    assert(correct_degrees(near_candidate));
    assert(no_repeated_good_middle(near_candidate, identity));
    assert(edge_balance(near_candidate, identity));
    assert(!one_A_closure(near_candidate, identity));
    // The closure test itself is not identically false: isolated loops pass.
    Array loops{};
    for (int i = 0; i < N; ++i) loops[i] = 1 << i;
    assert(no_repeated_good_middle(loops, identity));
    assert(edge_balance(loops, identity));
    assert(one_A_closure(loops, identity));
    assert(!correct_degrees(loops));
}

int main() {
    const auto started = std::chrono::steady_clock::now();
    positive_controls();
    const auto classes = sharp_permutation_classes();
    assert(classes.size() == 56);
    std::array<std::vector<int>, N> choices;
    for (int i = 0; i < N; ++i)
        for (int row = 0; row < (1 << N); ++row)
            if (cardinality(row) == DEGREE[i]) choices[i].push_back(row);
    Counts counts;
    for (const auto& target : classes) Search{target, choices, counts}.extend(0);
    assert(counts.full_matrices == 738);
    assert(counts.balanced_matrices == 720);
    assert(counts.surviving_matrices == 0);
    std::cout << "EXCLUDED: order 40, A12/B8, one sharp-degree-three vertex with a D loop\n"
              << "Sharp-permutation classes: " << classes.size() << '\n'
              << "Partial nodes: " << counts.partial_nodes << '\n'
              << "Complete D matrices: " << counts.full_matrices << '\n'
              << "After edge balance: " << counts.balanced_matrices << '\n'
              << "After one-A closure: " << counts.surviving_matrices << '\n'
              << "Elapsed: "
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count()
              << "s\n";
}
