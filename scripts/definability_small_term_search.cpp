// Bounded binary-term enumeration for the seven targets in the marked-case sweep.
// Compile: g++ -O3 -std=c++17 scripts/definability_small_term_search.cpp -o /tmp/term_search
// Standard input: order, number of targets, operation limit, seconds,
// target law numbers, then the source table in row-major order.
// Output: a shared term DAG for each successful target. A stopped search is
// inconclusive. All witnesses are independently replayed against equations.txt.
// __uint128_t packs all 25 cells of a five-element operation in 75 bits.
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using U=__uint128_t;
struct H {size_t operator()(U x)const{return uint64_t(x)^uint64_t(x>>64)*0x9e3779b97f4a7c15ULL;}};
int n,w,src[25];
inline int get(U op,int i){return (op>>(w*i))&((1<<w)-1);}
inline U compose(U a,U b){U v=0;for(int i=0;i<n*n;i++){v|=U(src[get(a,i)*n+get(b,i)])<<(w*i);}return v;}
bool holds(U op,int law){
 int tab[25];for(int i=0;i<n*n;i++)tab[i]=get(op,i);
 auto f=[&](int x,int y){return tab[x*n+y];};
 for(int x=0;x<n;x++)for(int y=0;y<n;y++){
  int l=0,r=0;
  switch(law){
   case 3272:l=f(x,x);r=f(y,f(x,f(y,y)));break;
   case 3472:l=f(x,x);r=f(y,f(f(x,x),y));break;
   case 1482:l=x;r=f(f(y,x),f(x,f(y,y)));break;
   case 3548:l=f(x,y);r=f(y,f(f(x,y),x));break;
   case 3558:l=f(x,y);r=f(y,f(f(y,y),x));break;
   case 4290:l=f(x,f(x,y));r=f(y,f(x,x));break;
   case 313:l=f(x,x);r=f(y,f(x,y));break;
   default:throw 1;
  }
  if(l!=r)return false;
 }
 return true;
}
int main(){
 int nt,limit;double seconds;std::cin>>n>>nt>>limit>>seconds;w=n<=4?2:3;
 if(!std::cin || n<2 || n>5 || nt<1 || limit<2 || seconds<=0)return 2;
 std::vector<int>targets(nt);for(auto&t:targets)std::cin>>t;for(int i=0;i<n*n;i++)std::cin>>src[i];
 U x=0,y=0;for(int i=0;i<n*n;i++){x|=U(i/n)<<(w*i);y|=U(i%n)<<(w*i);}
 std::vector<U>ops={x,y};std::vector<std::array<int,2>>nodes={{-1,-1},{-2,-2}};std::unordered_set<U,H>seen={x,y};seen.reserve(limit);
 std::unordered_map<int,int>found;for(int i=0;i<2;i++)for(int t:targets)if(holds(ops[i],t))found[t]=i;
 auto start=std::chrono::steady_clock::now();bool complete=false;uint64_t products=0;int i=0;
 for(;i<int(ops.size()) && found.size()<targets.size();i++){
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>seconds)break;
  for(int j=0;j<=i;j++)for(int dir=0;dir<2;dir++){
   int a=dir?j:i,b=dir?i:j;U v=compose(ops[a],ops[b]);products++;
   if(!seen.insert(v).second)continue;
   int k=ops.size();ops.push_back(v);nodes.push_back({a,b});
   for(int t:targets)if(!found.count(t)&&holds(v,t))found[t]=k;
   if(found.size()==targets.size()||int(ops.size())>=limit)goto done;
  }
 }
 complete=i==int(ops.size());
 done:
 std::vector<int>renum(ops.size(),-1);renum[0]=0;renum[1]=1;for(auto [t,k]:found)if(k>=2)renum[k]=-2;
 for(int k=int(ops.size())-1;k>=2;k--)if(renum[k]==-2){for(int c:nodes[k])if(c>=2)renum[c]=-2;}
 std::cout<<"{\"term_nodes\":[\"x\",\"y\"";int count=2;
 for(int k=2;k<int(ops.size());k++)if(renum[k]==-2){renum[k]=count++;std::cout<<",["<<renum[nodes[k][0]]<<","<<renum[nodes[k][1]]<<"]";}
 std::cout<<"],\"term_roots\":{";bool first=true;for(auto [t,k]:found){if(!first)std::cout<<",";first=false;std::cout<<"\""<<t<<"\":"<<renum[k];}
 std::cout<<"},\"clone_exhausted\":"<<(complete?"true":"false")<<",\"operations\":"<<ops.size()<<",\"products\":"<<products<<",\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"}\n";
}
