// Bounded exact replacement of three blocks in a near cyclic difference family.
// Input: v, number of blocks, then each block's size and entries.
// Usage: seconds [subgroup-hole-size]. The subgroup cosets supply the hole blocks.
// FOUND certifies a design; spectrum transfer also needs models of its block sizes.
// Failure concerns only the supplied frozen blocks.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <map>
#include <unordered_map>
#include <vector>
using namespace std;
using Mask = unsigned __int128;
struct Hash { size_t operator()(Mask x) const {
  uint64_t a=x, b=x>>64;
  return a ^ (b+0x9e3779b97f4a7c15ULL+(a<<6)+(a>>2));
}};
struct Block { vector<int> xs; Mask ds; };
int n;
chrono::steady_clock::time_point deadline;
long long visits=0;
void tick() {
  if ((++visits & 4095)==0 && chrono::steady_clock::now()>deadline) throw 1;
}
int dist(int a,int b) { int d=abs(a-b);return min(d,n-d); }
Mask bit(int d) { return Mask(1)<<(d-1); }
Mask mask(const vector<int>& xs) {
  Mask m=0;
  for (int i=0;i<int(xs.size());i++) for(int j=0;j<i;j++) {
    Mask b=bit(dist(xs[i],xs[j])); if(m&b) return 0; m|=b;
  }
  return m;
}
struct Catalogue {
  vector<Block> rows;
  unordered_map<Mask,int,Hash> index;
  vector<vector<int>> at;
  Catalogue():at((n+1)/2){}
  void add(const vector<int>& xs, Mask ds) {
    if(index.count(ds)) return;
    int i=rows.size();index[ds]=i;rows.push_back({xs,ds});
    for(int d=1;d<=(n-1)/2;d++) if(ds&bit(d))at[d].push_back(i);
  }
};
void enumerate(Catalogue& cat, int k, Mask allowed, vector<int>& xs,
               const vector<int>& candidates, Mask seen) {
  tick();
  if(int(xs.size())==k) { cat.add(xs,seen);return; }
  if(xs.size()+candidates.size()<size_t(k))return;
  for(int i=0;i<int(candidates.size());i++) {
    int a=candidates[i];Mask extra=0;bool ok=true;
    for(int x:xs) { Mask b=bit(dist(a,x));if(!(allowed&b)||((extra|seen)&b)){ok=false;break;}extra|=b; }
    if(!ok)continue;
    xs.push_back(a);
    vector<int> next;
    for(int j=i+1;j<int(candidates.size());j++) {
      int b=candidates[j];
      if(b-a<xs[1] || n-b<xs[1])continue;
      Mask db=bit(dist(a,b));if((allowed&db)&&!((seen|extra)&db))next.push_back(b);
    }
    enumerate(cat,k,allowed,xs,next,seen|extra);
    xs.pop_back();
  }
}
bool cover(map<int,Catalogue>& cats, map<int,int>& needed, Mask remain,
           vector<Block>& answer, int depth) {
  tick();
  if(depth==0)return remain==0;
  if(depth==1) {
    for(auto [k,count]:needed)if(count) {
      auto it=cats.at(k).index.find(remain);
      if(it==cats.at(k).index.end())return false;
      answer.push_back(cats.at(k).rows[it->second]);return true;
    }
  }
  if(depth==2) {
    vector<int> kinds;
    for(auto [k,num]:needed)for(int j=0;j<num;j++)kinds.push_back(k);
    if(cats.at(kinds[0]).rows.size()>cats.at(kinds[1]).rows.size())swap(kinds[0],kinds[1]);
    auto& first=cats.at(kinds[0]);auto& second=cats.at(kinds[1]);
    for(auto& row:first.rows) {
      tick();if((row.ds&remain)!=row.ds)continue;
      auto it=second.index.find(remain^row.ds);
      if(it!=second.index.end()) {
        answer.push_back(row);answer.push_back(second.rows[it->second]);return true;
      }
    }
    return false;
  }
  int bestd=0;size_t best=SIZE_MAX;
  for(int d=1;d<=(n-1)/2;d++)if(remain&bit(d)) {
    size_t count=0;
    for(auto [k,num]:needed)if(num)for(int i:cats.at(k).at[d]) {
      Mask ds=cats.at(k).rows[i].ds;if((ds&remain)==ds)count++;
    }
    if(count<best){best=count;bestd=d;}if(!best)return false;
  }
  for(auto& [k,num]:needed)if(num) {
    for(int i:cats.at(k).at[bestd]) {
      auto& row=cats.at(k).rows[i];if((row.ds&remain)!=row.ds)continue;
      --num;answer.push_back(row);
      if(cover(cats,needed,remain^row.ds,answer,depth-1))return true;
      answer.pop_back();++num;
    }
  }
  return false;
}
int main(int argc,char**argv) {
  int seconds=argc>1?atoi(argv[1]):300, hole=argc>2?atoi(argv[2]):1, count;
  cin>>n>>count;if(n%2==0 || n>255 || n<9)return 2;
  if(hole<1||hole%2==0||n%hole)return 2;
  vector<vector<int>> rows(count);
  for(auto& r:rows){int k;cin>>k;r.resize(k);for(int& x:r)cin>>x;}
  deadline=chrono::steady_clock::now()+chrono::seconds(seconds);
  Mask all=(Mask(1)<<((n-1)/2))-1;
  try {
    for(int a=0;a<count;a++)for(int b=a+1;b<count;b++)for(int c=b+1;c<count;c++) {
      Mask fixed=0;bool ok=true;
      for(int j=1;j<=(hole-1)/2;j++)fixed|=bit(j*(n/hole));
      for(int i=0;i<count;i++)if(i!=a&&i!=b&&i!=c){Mask ds=mask(rows[i]);if(!ds||(ds&fixed)){ok=false;break;}fixed|=ds;}
      if(!ok)continue;
      Mask allowed=all^fixed;
      map<int,int> needed;for(int i:{a,b,c})needed[rows[i].size()]++;
      map<int,Catalogue> cats;
      cerr<<"free "<<a<<' '<<b<<' '<<c<<'\n';
      for(auto [k,num]:needed) {
        auto& cat=cats[k];vector<int> xs{0};vector<int> candidates;
        for(int x=1;x<n;x++)if(allowed&bit(dist(0,x)))candidates.push_back(x);
        enumerate(cat,k,allowed,xs,candidates,0);
        cerr<<"  size "<<k<<": "<<cat.rows.size()<<" distance sets\n";
      }
      vector<Block> answer;
      if(cover(cats,needed,allowed,answer,3)) {
        for(int i=0,j=0;i<count;i++)if(i==a||i==b||i==c)rows[i]=answer[j++].xs;
        cout<<"{\"status\":\"FOUND\",\"order\":"<<n<<",\"hole\":"<<hole<<",\"blocks\":[";
        for(int i=0;i<count;i++){if(i)cout<<',';cout<<'[';for(int j=0;j<int(rows[i].size());j++){if(j)cout<<',';cout<<rows[i][j];}cout<<']';}
        cout<<"]}\n";return 0;
      }
      cerr<<"  no three-block repair\n";
    }
    cout<<"{\"status\":\"NO_THREE_BLOCK_REPAIR\"}\n";
  }catch(int){cout<<"{\"status\":\"UNKNOWN\",\"reason\":\"time limit\"}\n";}
}
