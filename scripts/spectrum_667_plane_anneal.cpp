// Fixed-cardinality restrictions of a supplied pairwise balanced design.
// Input: v, target size, line count, allowed-size count; allowed sizes;
// then each line's size followed by its points. Arguments: seconds, seed.
// Only FOUND is a construction; other output is explicitly a near-design.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using namespace std;
int main(int argc, char** argv) {
  int seconds = argc > 1 ? atoi(argv[1]) : 120;
  unsigned seed = argc > 2 ? stoul(argv[2]) : 1;
  int v, n, m, nk;
  if (!(cin >> v >> n >> m >> nk) || n < 1 || n > v) return 2;
  vector<int> allowed(nk);
  for (int& k : allowed) cin >> k;
  vector<vector<int>> lines(m), at(v);
  int maxk = 0;
  for (int l=0; l<m; ++l) {
    int k; cin >> k; maxk=max(maxk,k); lines[l].resize(k);
    for (int& x : lines[l]) { cin >> x; at[x].push_back(l); }
  }
  vector<int> penalty(maxk+1,100000);
  for (int k=0; k<=maxk; ++k)
    for (int a : allowed) penalty[k]=min(penalty[k],(k-a)*(k-a));
  mt19937 rng(seed);
  uniform_real_distribution<double> uni(0,1);
  vector<int> order(v), selected(v), counts(m), bestset;
  iota(order.begin(),order.end(),0);
  int best=100000, cost=0;
  long long moves=0;
  auto start=chrono::steady_clock::now();
  auto deadline=start+chrono::seconds(seconds);
  while (chrono::steady_clock::now()<deadline && best>0) {
    shuffle(order.begin(),order.end(),rng);
    fill(selected.begin(),selected.end(),0);
    fill(counts.begin(),counts.end(),0);
    for (int i=0;i<n;++i) { selected[order[i]]=1; for(int l:at[order[i]])++counts[l]; }
    cost=0; for(int c:counts)cost+=penalty[c];
    for (int step=0;step<300000 && best>0;++step) {
      if (cost<best) { best=cost; bestset=selected; cerr<<"best "<<best<<'\n'; }
      if (!best || n==v) break;
      int i=rng()%n, j=n+rng()%(v-n), x=order[i], y=order[j];
      int delta=0;
      for(int l:at[x]) { delta-=penalty[counts[l]]; --counts[l]; delta+=penalty[counts[l]]; }
      for(int l:at[y]) { delta-=penalty[counts[l]]; ++counts[l]; delta+=penalty[counts[l]]; }
      double t=.08+1.25*pow(1.-double(step%30000)/30000,2);
      if(delta<=0 || uni(rng)<exp(-delta/t)) {
        cost+=delta; swap(order[i],order[j]); selected[x]=0; selected[y]=1;
      } else {
        for(int l:at[x])++counts[l]; for(int l:at[y])--counts[l];
      }
      ++moves;
      if ((moves&16383)==0 && chrono::steady_clock::now()>=deadline)break;
    }
  }
  cout<<"{\"status\":\""<<(best==0?"FOUND":"UNKNOWN")<<"\",\"order\":"<<n
      <<",\"seed\":"<<seed<<",\"best_penalty\":"<<best<<",\"moves\":"<<moves
      <<",\"selected\":[";
  bool first=true;
  for(int x=0;x<v;++x)if(!bestset.empty() && bestset[x]){ if(!first)cout<<',';cout<<x;first=false; }
  cout<<"]}\n";
}
