// Enumerate transversals and test standard one-point quasigroup prolongations.
// Input: n, time limit in seconds, then n*n table entries.
// UNKNOWN means the enumeration stopped early, never a nonexistence theorem.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using Clock=chrono::steady_clock;
int n; double seconds; vector<int> tab,pi,sigma,ext; uint64_t leaves=0,nodes=0,mixed=0;
bool stopped=false,found=false; Clock::time_point started;
int mul(int x,int y){return ext[x*(n+1)+y];}
bool law(int x,int y){return x==mul(y,mul(mul(y,x),mul(x,y)));}
void enumerate_transversals(int row,uint64_t columns,uint64_t symbols){
  if(stopped||found)return;
  if((++nodes&4095)==0 && chrono::duration<double>(Clock::now()-started).count()>=seconds){stopped=true;return;}
  if(row==n){
    ++leaves;
    for(int x=0;x<n;++x)for(int y=0;y<n;++y)ext[x*(n+1)+y]=tab[x*n+y];
    for(int x=0;x<n;++x){ext[x*(n+1)+pi[x]]=n;ext[x*(n+1)+n]=sigma[x];ext[n*(n+1)+pi[x]]=sigma[x];}
    ext[n*(n+1)+n]=n;
    for(int x=0;x<=n;++x)if(!law(x,n)||!law(n,x))return;
    ++mixed;
    for(int x=0;x<=n;++x)for(int y=0;y<=n;++y)if(!law(x,y))return;
    found=true;return;
  }
  for(int y=0;y<n;++y){int z=tab[row*n+y];if((columns>>y&1)||(symbols>>z&1))continue;
    pi[row]=y;sigma[row]=z;enumerate_transversals(row+1,columns|(1ULL<<y),symbols|(1ULL<<z));
    if(stopped||found)return;
  }
}
int main(){
  if(!(cin>>n>>seconds)||n<1||n>30||seconds<=0)return 2;
  tab.resize(n*n);for(int&x:tab)if(!(cin>>x)||x<0||x>=n)return 2;
  for(int x=0;x<n;++x){vector<int>r,c;for(int y=0;y<n;++y){r.push_back(tab[x*n+y]);c.push_back(tab[y*n+x]);}
    sort(r.begin(),r.end());sort(c.begin(),c.end());for(int y=0;y<n;++y)if(r[y]!=y||c[y]!=y)return 2;}
  for(int x=0;x<n;++x)for(int y=0;y<n;++y)if(x!=tab[y*n+tab[tab[y*n+x]*n+tab[x*n+y]]])return 2;
  pi.resize(n);sigma.resize(n);ext.resize((n+1)*(n+1));started=Clock::now();enumerate_transversals(0,0,0);
  cout<<"{\"base_order\":"<<n<<",\"order\":"<<n+1<<",\"status\":\""<<(found?"MODEL":stopped?"UNKNOWN":"EXHAUSTED")
      <<"\",\"transversals_checked\":"<<leaves<<",\"mixed_law_passes\":"<<mixed<<",\"nodes\":"<<nodes
      <<",\"seconds\":"<<chrono::duration<double>(Clock::now()-started).count()<<",\"limit_seconds\":"<<seconds;
  if(found){cout<<",\"table\":[";for(size_t i=0;i<ext.size();++i)cout<<(i?",":"")<<ext[i];cout<<"]";}
  cout<<"}\n";
}
