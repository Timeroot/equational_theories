// Pack a trimmed binary LRAT proof as compact RUP.
//
// Only a generator: the output is untrusted data. Lean reconstructs the omitted
// hints and checks the resulting proof with Std's verified LRAT checker.
// RUP clauses may be sorted; RAT additions are deliberately rejected.
// --input-mask inserts an optional 'm' header followed by one byte per input
// clause ID (including unused ID zero). Only input clauses appearing in LRAT
// hints are selected. Replay may ignore the others when searching for hints;
// the final LRAT checker still receives the entire original CNF.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

using Words = std::vector<uint32_t>;
static FILE *output;

static uint32_t read_word() {
  uint32_t value = 0;
  for (unsigned shift = 0; shift < 35; shift += 7) {
    int byte = std::getchar();
    if (byte == EOF) std::exit(3);
    value |= uint32_t(byte & 127) << shift;
    if (byte < 128) return value;
  }
  std::exit(3);
}

static void write_word(uint64_t value) {
  while (value > 127) {
    std::fputc((value & 127) | 128, output);
    value >>= 7;
  }
  std::fputc(value, output);
}

int main(int argc, char **argv) {
  bool with_mask = argc == 3 && std::string(argv[1]) == "--input-mask";
  if (argc != 2 && !with_mask) {
    std::fprintf(stderr, "usage: compact-rup [--input-mask] OUTPUT < proof.binary.lrat\n");
    return 1;
  }
  const char *output_path = argv[with_mask ? 2 : 1];
  output = std::fopen(output_path, "wb");
  if (!output) { std::perror(output_path); return 1; }
  std::vector<uint8_t> selected;
  long mask_position = 0;
  uint32_t count = 0, initial = 0;
  bool ends_in_contradiction = false;
  std::vector<Words> history(256);
  int tag;
  while ((tag = std::getchar()) != EOF) {
    if (tag == 'a') {
      uint32_t id = read_word();
      if (count == 0) {
        initial = id;
        write_word(initial); // Binary LRAT encodes positive IDs as twice the ID.
        if (with_mask) {
          selected.resize(initial / 2);
          std::fputc('m', output);
          mask_position = std::ftell(output);
          if (mask_position < 0) return 1;
          if (std::fwrite(selected.data(), 1, selected.size(), output) != selected.size())
            return 1;
        }
      }
      Words literals;
      for (uint32_t word; (word = read_word());) literals.push_back(word);
      for (uint32_t word; (word = read_word());) {
        if (word & 1) {
          std::fprintf(stderr, "RAT additions are not supported\n");
          return 5;
        }
        if (with_mask && word / 2 < selected.size()) selected[word / 2] = 1;
      }
      if (id != initial + 2 * count) {
        std::fprintf(stderr, "input must have consecutive, trimmed clause IDs\n");
        return 6;
      }
      std::sort(literals.begin(), literals.end());
      ends_in_contradiction = literals.empty();
      unsigned best = 0;
      int score = 0;
      // Reuse a recent clause when a keep-mask and its added literals are
      // expected to be smaller than spelling out this clause from scratch.
      for (unsigned distance = 1; distance <= std::min(count, 256u); ++distance) {
        const auto &old = history[(count - distance) % 256];
        if (old.size() > 63) continue;
        int common = 0;
        auto a = literals.begin();
        auto b = old.begin();
        while (a != literals.end() && b != old.end()) {
          if (*a < *b) ++a;
          else if (*b < *a) ++b;
          else { ++common; ++a; ++b; }
        }
        int saving = 2 * common - int((old.size() + 6) / 7) - 1;
        if (saving > score) { score = saving; best = distance; }
      }
      uint64_t mask = 0;
      Words added = literals;
      if (best) {
        const auto &old = history[(count - best) % 256];
        added.clear();
        std::set_difference(literals.begin(), literals.end(), old.begin(), old.end(),
                            std::back_inserter(added));
        for (size_t k = 0; k < old.size(); ++k)
          if (std::binary_search(literals.begin(), literals.end(), old[k]))
            mask |= uint64_t(1) << k;
      }
      std::fputc('a', output);
      write_word(best);
      if (best) write_word(mask);
      uint32_t previous = 0;
      for (auto literal : added) {
        write_word(literal - previous + 1);
        previous = literal;
      }
      write_word(0);
      history[count % 256] = std::move(literals);
      ++count;
    } else if (tag == 'd') {
      if (count == 0) return 4;
      Words ids;
      for (uint32_t word; (word = read_word());) {
        uint32_t id = word / 2;
        // Trimmed traces can request deletion of an absent clause. Such a
        // request is a no-op, and is not part of the compact clause database.
        if (id < initial / 2 + count) ids.push_back(id);
      }
      std::sort(ids.begin(), ids.end());
      std::fputc('d', output);
      uint32_t previous = 0;
      for (auto id : ids) { write_word(id - previous + 1); previous = id; }
      write_word(0);
    } else {
      return 4;
    }
  }
  if (with_mask && count) {
    if (std::fseek(output, mask_position, SEEK_SET) != 0 ||
        std::fwrite(selected.data(), 1, selected.size(), output) != selected.size()) return 1;
    std::fprintf(stderr, "Selected %zu of %zu input clauses\n",
      size_t(std::count(selected.begin(), selected.end(), uint8_t(1))), selected.size()-1);
  }
  // A failed buffered write must never yield a successfully saved, truncated
  // certificate, even if a later flush succeeds after space becomes available.
  if (std::ferror(stdin) || std::ferror(output)) {
    std::fprintf(stderr, "I/O error while packing the certificate\n");
    std::fclose(output);
    return 1;
  }
  if (std::fclose(output) != 0) return 1;
  if (!count || !ends_in_contradiction) {
    std::fprintf(stderr, "input does not end in an empty learned clause\n");
    return 7;
  }
  std::fprintf(stderr, "Packed %u RUP additions\n", count);
}
