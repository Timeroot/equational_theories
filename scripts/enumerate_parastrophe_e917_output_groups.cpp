// External research enumeration, not a Lean certificate.
// For each allowable uniform b, enumerate every permutation a. Outputs of
// left autotopies act freely, so equality of generated words at zero must
// mean equality everywhere. Reject violations, then relabel each regular
// orbit by the same generator-first breadth-first traversal.
// Usage: g++ -O3 ... -o /tmp/e917-groups; /tmp/e917-groups 9 > cases.json
#include <vector>
#include <set>
#include <algorithm>
#include <iostream>
#include <numeric>
#include <string>
using P=std::vector<int>;
P mul(const P&a,const P&b){P c(a.size());for(unsigned x=0;x<a.size();x++)c[x]=a[b[x]];return c;}
void print(const P&p){std::cout<<'[';for(unsigned i=0;i<p.size();i++){if(i)std::cout<<',';std::cout<<p[i];}std::cout<<']';}
int main(int argc,char**argv){
 if(argc!=2)return 2;
 int n=std::stoi(argv[1]);if(n<2||n>10)return 2;
 P id(n);std::iota(id.begin(),id.end(),0);
 std::set<std::pair<P,P>> forms;
 unsigned long long checked=0,passed=0;
 for(int period=2;period<=n;period++){
  if(n%period||((n/period)*(period-1))%2)continue;
  P b(n);for(int x=0;x<n;x++)b[x]=period*(x/period)+(x+1)%period;
  P a=id;
  do{
   checked++;
   bool bad=false;for(int x=0;x<n;x++)if(a[x]==x||a[x]==b[x]){bad=true;break;}
   if(bad)continue;
   std::vector<bool>seen(n);std::vector<P>value(n);
   std::vector<P>group{id};seen[0]=true;value[0]=id;
   for(unsigned i=0;i<group.size()&&!bad;i++)for(const P &g:{a,b}){
    P t=mul(g,group[i]);int j=t[0];
    if(seen[j]){if(t!=value[j]){bad=true;break;}}
    else{
     for(int x=0;x<n;x++)if(t[x]==x){bad=true;break;}
     if(bad)break;
     seen[j]=true;value[j]=t;group.push_back(t);
    }
   }
   if(bad)continue;
   passed++;
   int m=group.size();if(n%m)return 3;
   P index(n,-1);for(int i=0;i<m;i++)index[group[i][0]]=i;
   P aa(n),bb(n);
   for(int x=0;x<n;x++){
    aa[x]=m*(x/m)+index[a[group[x%m][0]]];
    bb[x]=m*(x/m)+index[b[group[x%m][0]]];
   }
   forms.insert({aa,bb});
  }while(std::next_permutation(a.begin(),a.end()));
 }
 std::cout<<"[\n";int i=0;
 for(const auto& [a,b]:forms){
  if(i)std::cout<<",\n";
  std::cout<<"{\"case\":"<<i++<<",\"a\":";print(a);std::cout<<",\"b\":";print(b);std::cout<<'}';
 }
 std::cout<<"\n]\n";
 std::cerr<<checked<<" permutations examined; "<<passed<<" free pairs; "<<forms.size()<<" normal forms.\n";
}
