// Exploratory cyclic PBD(v,{5,7,8}) search. A failure or timeout proves nothing.
// Usage: binary seconds seed type order. The default order is339.
// Type selects one of the possible block-count distributions. A success is an independently checkable
// list of base blocks whose unordered cyclic distances partition1..(v-1)/2.
// Optional arguments: comma-separated sizes, subgroup-hole size, group mode.
// The mode "frobenius" uses (C13 : C3) x C5 at 195 or C73 : C3 at 219.
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):60;unsigned long long seed=argc>2?strtoull(argv[2],0,10):1;
 int typ=argc>3?atoi(argv[3]):0;
 int n=argc>4?atoi(argv[4]):339;if(n%2==0||n<9)return 2;
 // Optional explicit sizes and a subgroup hole: e.g. 195 7,7,11 or
 // 195 11,5,5,5,5 5. In the latter, cosets of the subgroup supply 5-blocks.
 int hole=argc>6?atoi(argv[6]):1;
 if(hole<1||n%hole||hole%2==0)return 2;
 vector<vector<int>> shapes;
 if(argc>5){vector<int>s;string token;istringstream in(argv[5]);while(getline(in,token,','))s.push_back(stoi(token));int pairs=(hole-1)/2;for(int k:s){if(k<2||k>n)return 2;pairs+=k*(k-1)/2;}if(pairs!=(n-1)/2)return 2;shapes.push_back(s);}
 else for(int a=0;a<=(n-1)/20;a++)for(int b=0;b<=(n-1)/42;b++)for(int c=0;c<=(n-1)/56;c++)if(10*a+21*b+28*c==(n-1)/2){vector<int>s;s.insert(s.end(),a,5);s.insert(s.end(),b,7);s.insert(s.end(),c,8);shapes.push_back(s);}
 if(shapes.empty())return 2;
 mt19937_64 rng(seed);vector<int> sizes=shapes[typ%shapes.size()];
 vector<vector<int>> b,best;vector<int>cnt((n+1)/2);int E=0,globalbest=10000;long long total=0;
 bool nonabelian=argc>7&&string(argv[7])=="frobenius";
 vector<vector<int>> difference;
 if(nonabelian){
  if((n!=195&&n!=219)||(hole!=1&&!(n==195&&hole==5)))return 2;
  int prime=n==219?73:13,root=n==219?8:3,extra=n/(3*prime);
  // Coordinates (a,b,c); multiplication twists a' by root^b modulo prime.
  auto mult=[&](int x,int y){int a=x%prime,b=(x/prime)%3,c=x/(3*prime);int aa=y%prime,bb=(y/prime)%3,cc=y/(3*prime);int rr=b==0?1:b==1?root:root*root%prime;return (a+rr*aa)%prime+prime*((b+bb)%3)+3*prime*((c+cc)%extra);};
  vector<int> inv(n),cls(n);
  for(int x=0;x<n;x++)for(int y=0;y<n;y++)if(mult(x,y)==0)inv[x]=y;
  int classes=0;for(int x=1;x<n;x++)if(!cls[x])cls[x]=cls[inv[x]]=++classes;
  difference.assign(n,vector<int>(n));
  for(int x=0;x<n;x++)for(int y=0;y<n;y++)difference[x][y]=cls[mult(inv[x],y)];
 }
 auto dist=[&](int x,int y){if(nonabelian)return difference[x][y];int d=abs(x-y);return min(d,n-d);};
 auto add=[&](int d){E+=cnt[d]++;};auto rem=[&](int d){E-=--cnt[d];};
 auto start=chrono::steady_clock::now();
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  b.clear();fill(cnt.begin(),cnt.end(),0);E=0;
  for(int j=1;j<=(hole-1)/2;j++)cnt[dist(0,j*(n/hole))]=1;
  for(int k:sizes){vector<int>r{0};while(int(r.size())<k){int a=1+rng()%(n-1);if(find(r.begin(),r.end(),a)==r.end())r.push_back(a);}for(int i=0;i<k;i++)for(int j=0;j<i;j++)add(dist(r[i],r[j]));b.push_back(r);}
  for(int iter=0;iter<600000;iter++){
   total++;int ri=rng()%b.size();auto&r=b[ri];int at=1+rng()%(r.size()-1);int old=r[at],neu=1+rng()%(n-1);
   if(find(r.begin(),r.end(),neu)!=r.end())continue;
   int before=E;for(int j=0;j<int(r.size());j++)if(j!=at)rem(dist(old,r[j]));
   for(int j=0;j<int(r.size());j++)if(j!=at)add(dist(neu,r[j]));
   double phase=(iter%100000)/100000.;double temp=0.06+1.7*pow(1.-phase,3);
   if(E<=before || (rng()/(double)rng.max())<exp((before-E)/temp))r[at]=neu;
   else{for(int j=0;j<int(r.size());j++)if(j!=at)rem(dist(neu,r[j]));for(int j=0;j<int(r.size());j++)if(j!=at)add(dist(old,r[j]));}
   if(E<globalbest){globalbest=E;best=b;cerr<<"best "<<E<<" steps "<<total<<"\n";}
   if(E==0){cout<<"{\"group\":\""<<(nonabelian?"frobenius":"cyclic")<<"\",\"order\":"<<n<<",\"hole\":"<<hole<<",\"type\":"<<typ<<",\"seed\":"<<seed<<",\"blocks\":[";for(int i=0;i<int(b.size());i++){if(i)cout<<',';cout<<'[';for(int j=0;j<int(b[i].size());j++){if(j)cout<<',';cout<<b[i][j];}cout<<']';}cout<<"]}\n";return 0;}
   if((iter&16383)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;
  }
 }
 cout<<"{\"group\":\""<<(nonabelian?"frobenius":"cyclic")<<"\",\"order\":"<<n<<",\"hole\":"<<hole<<",\"type\":"<<typ<<",\"seed\":"<<seed<<",\"status\":\"unknown\",\"best_collisions\":"<<globalbest<<",\"steps\":"<<total<<",\"best_blocks\":[";for(int i=0;i<int(best.size());i++){if(i)cout<<',';cout<<'[';for(int j=0;j<int(best[i].size());j++){if(j)cout<<',';cout<<best[i][j];}cout<<']';}cout<<"]}\n";
}
