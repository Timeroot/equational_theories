// Bounded subpower membership with a term certificate for a found vector.
// Compile: g++ -O3 -std=c++17 scripts/definability_subpower_search.cpp -o /tmp/subpower_search
// Standard input: order, number of seeds, vector length, operation limit, seconds,
// the seed vectors, the goal vector, then the source table in row-major order.
// Output: a DAG (integer variable nodes index the seeds); root -1 means that
// no witness was found. It is not a nonmembership claim unless closure exhausted.
// Packed vectors use 2 bits per coordinate at orders 2--4 and 3 at order 5;
// the total packed length must be at most 128 bits.
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using U=__uint128_t;
struct H {size_t operator()(U x)const{return uint64_t(x)^uint64_t(x>>64)*0x9e3779b97f4a7c15ULL;}};
int n,w,src[25],width;
inline int get(U op,int i){return (op>>(w*i))&((1<<w)-1);}
inline U compose(U a,U b){U v=0;for(int i=0;i<width;i++){v|=U(src[get(a,i)*n+get(b,i)])<<(w*i);}return v;}
int main(){
 int nt=1,limit,k;double seconds;std::cin>>n>>k>>width>>limit>>seconds;w=n<=4?2:3;
 if(!std::cin || n<2 || n>5 || k<1 || width<1 || w*width>128 || limit<k || seconds<=0)return 2;
 std::vector<U>ops;std::vector<std::array<int,2>>nodes;std::unordered_set<U,H>seen;seen.reserve(limit);
 for(int j=0;j<k;j++){U v=0;for(int i=0;i<width;i++){int x;std::cin>>x;v|=U(x)<<(w*i);}ops.push_back(v);nodes.push_back({-j-1,-j-1});seen.insert(v);}
 U goal=0;for(int i=0;i<width;i++){int x;std::cin>>x;goal|=U(x)<<(w*i);}for(int i=0;i<n*n;i++)std::cin>>src[i];
 std::unordered_map<int,int>found;for(int i=0;i<k;i++)if(ops[i]==goal)found[0]=i;
 auto start=std::chrono::steady_clock::now();bool complete=false;uint64_t products=0;int i=0;
 for(;i<int(ops.size()) && found.size()<size_t(nt);i++){
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>seconds)break;
  for(int j=0;j<=i;j++)for(int dir=0;dir<2;dir++){
   int a=dir?j:i,b=dir?i:j;U v=compose(ops[a],ops[b]);products++;
   if(!seen.insert(v).second)continue;
   int k=ops.size();ops.push_back(v);nodes.push_back({a,b});
   if(v==goal)found[0]=k;
   if(found.size()==size_t(nt)||int(ops.size())>=limit)goto done;
  }
 }
 complete=i==int(ops.size());
 done:
 std::vector<int>renum(ops.size(),-1);for(int j=0;j<k;j++)renum[j]=j;for(auto [t,j]:found)if(j>=k)renum[j]=-2;
 for(int j=int(ops.size())-1;j>=k;j--)if(renum[j]==-2){for(int c:nodes[j])if(c>=k)renum[c]=-2;}
 std::cout<<"{\"nodes\":[";for(int j=0;j<k;j++){if(j)std::cout<<",";std::cout<<j;}int count=k;
 for(int j=k;j<int(ops.size());j++)if(renum[j]==-2){renum[j]=count++;std::cout<<",["<<renum[nodes[j][0]]<<","<<renum[nodes[j][1]]<<"]";}
 std::cout<<"],\"root\":"<<(found.count(0)?renum[found[0]]:-1)<<",\"operations\":"<<ops.size()<<",\"complete\":"<<(complete?"true":"false")<<"}\n";
}
