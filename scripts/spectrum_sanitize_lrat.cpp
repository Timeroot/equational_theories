// Renumber a binary LRAT trace after deleting tautological input clauses.
// This is an untrusted data transformation. Lean checks the resulting proof
// against its own sanitized CNF. No non-tautological input is removed.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

static FILE *output;
static uint32_t old_count, new_count;
static std::vector<uint32_t> ids(1,0);

static uint32_t read_word() {
  uint32_t n=0;
  for (unsigned s=0;s<35;s+=7) {
    int b=std::getchar(); if (b==EOF) std::exit(3);
    n|=uint32_t(b&127)<<s; if (b<128) return n;
  }
  std::exit(3);
}
static void write_word(uint32_t n) {
  while (n>127) { std::fputc((n&127)|128,output); n>>=7; }
  std::fputc(n,output);
}
static uint32_t remap(uint32_t id) {
  return id<=old_count ? ids[id] : id-old_count+new_count;
}

int main(int argc,char **argv) {
  if (argc!=3) {
    std::fprintf(stderr,"usage: sanitize-lrat ORIGINAL.cnf OUTPUT.binary < INPUT.binary\n");
    return 1;
  }
  std::ifstream cnf(argv[1]); std::string line; std::vector<int> clause;
  if (!cnf) return 1;
  while (std::getline(cnf,line)) {
    if (line.empty() || line[0]=='c') continue;
    std::istringstream in(line);
    if (line[0]=='p') { std::string p,format; uint32_t vars; in>>p>>format>>vars>>old_count; continue; }
    int literal;
    while (in>>literal) {
      if (literal) { clause.push_back(literal); continue; }
      std::sort(clause.begin(),clause.end());
      bool taut=false;
      for (int v:clause) if (std::binary_search(clause.begin(),clause.end(),-v)) { taut=true; break; }
      ids.push_back(taut ? 0 : ++new_count); clause.clear();
    }
  }
  if (!clause.empty() || ids.size()!=old_count+1) return 2;
  output=std::fopen(argv[2],"wb"); if (!output) return 1;
  int tag;
  while ((tag=std::getchar())!=EOF) {
    std::fputc(tag,output);
    if (tag=='a') {
      uint32_t id=read_word();
      if ((id&1) || id/2<=old_count) return 4;
      write_word(2*remap(id/2));
      for (uint32_t v;(v=read_word());) write_word(v);
      write_word(0);
      for (uint32_t hint;(hint=read_word());) {
        uint32_t mapped=remap(hint/2);
        if (!mapped) {
          std::fprintf(stderr,"trace references a tautological input clause\n"); return 5;
        }
        write_word(2*mapped+(hint&1));
      }
      write_word(0);
    } else if (tag=='d') {
      for (uint32_t word;(word=read_word());) {
        if (word&1) return 4;
        uint32_t mapped=remap(word/2); if (mapped) write_word(2*mapped);
      }
      write_word(0);
    } else return 4;
  }
  if (std::ferror(stdin) || std::ferror(output)) return 1;
  if (std::fclose(output)!=0) return 1;
  std::fprintf(stderr,"Removed %u tautological clauses; %u input clauses remain\n",old_count-new_count,new_count);
}
