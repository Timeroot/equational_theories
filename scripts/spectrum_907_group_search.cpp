// Exhaustive, time-bounded search of op(x,y)=f(x)^epsilon*g(y)^delta*c.
// epsilon,delta in {+1,-1}, with at least one inverse. Input: group order,
// seconds, multiplication table, automorphism count, automorphism tables.
#include <chrono>
#include <iostream>
#include <vector>
#include <algorithm>
using namespace std; using Clock=chrono::steady_clock;
int main(){
 int n;double limit;if(!(cin>>n>>limit)||n<2||limit<=0)return 2;
 vector<int>p(n*n),inv(n);for(int&x:p)if(!(cin>>x)||x<0||x>=n)return 2;
 for(int x=0;x<n;++x){if(p[x]!=x||p[x*n]!=x)return 2;inv[x]=-1;for(int y=0;y<n;++y)if(p[x*n+y]==0&&p[y*n+x]==0)inv[x]=y;if(inv[x]<0)return 2;}
 int k;if(!(cin>>k)||k<1)return 2;vector<vector<int>>aut(k,vector<int>(n));
 for(auto&a:aut){for(int&v:a)if(!(cin>>v)||v<0||v>=n)return 2;auto b=a;sort(b.begin(),b.end());for(int x=0;x<n;++x)if(b[x]!=x)return 2;
  for(int x=0;x<n;++x)for(int y=0;y<n;++y)if(a[p[x*n+y]]!=p[a[x]*n+a[y]])return 2;}
 auto start=Clock::now();uint64_t checked=0,axis=0;bool stopped=false,found=false;vector<int>table;int fa=-1,ga=-1,maskFound=-1,cf=-1;
 for(int mask=1;mask<=3&&!stopped&&!found;++mask)for(int i=0;i<k&&!stopped&&!found;++i)for(int j=0;j<k&&!stopped&&!found;++j)for(int c=0;c<n;++c){
  if((++checked&4095)==0&&chrono::duration<double>(Clock::now()-start).count()>=limit){stopped=true;break;}
  auto op=[&](int x,int y){int a=aut[i][x],b=aut[j][y];if(mask&1)a=inv[a];if(mask&2)b=inv[b];return p[p[a*n+b]*n+c];};
  auto law=[&](int x,int y){return x==op(y,op(op(y,x),op(x,y)));};
  bool ok=true;for(int x=0;x<n&&ok;++x)if(!law(x,0)||!law(0,x))ok=false;if(!ok)continue;++axis;
  for(int x=0;x<n&&ok;++x)for(int y=0;y<n&&ok;++y)if(!law(x,y))ok=false;
  if(ok){found=true;fa=i;ga=j;maskFound=mask;cf=c;for(int x=0;x<n;++x)for(int y=0;y<n;++y)table.push_back(op(x,y));break;}
 }
 cout<<"{\"order\":"<<n<<",\"automorphisms\":"<<k<<",\"status\":\""<<(found?"MODEL":stopped?"UNKNOWN":"EXHAUSTED")<<"\",\"candidates_checked\":"<<checked
 <<",\"axis_tests_passed\":"<<axis<<",\"seconds\":"<<chrono::duration<double>(Clock::now()-start).count()<<",\"limit_seconds\":"<<limit;
 if(found){cout<<",\"f\":"<<fa<<",\"g\":"<<ga<<",\"inversion_mask\":"<<maskFound<<",\"constant\":"<<cf<<",\"table\":[";for(size_t i=0;i<table.size();++i)cout<<(i?",":"")<<table[i];cout<<"]";}
 cout<<"}\n";
}
