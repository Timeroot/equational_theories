// Exploratory E667 annealing over row, column, and symbol cycle trades of a Latin square.
// Input: path to n followed by n*n integer table entries; seconds; random seed; optional peak heat.
// The output is a near-model unless violated_equation_instances is exactly zero.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
int main(int argc,char**argv){
 if(argc!=4 && argc!=5)return 2;std::ifstream in(argv[1]);int n;in>>n;std::vector<int> t(n*n),bestT;for(int&x:t)in>>x;
 std::mt19937_64 rng(std::stoull(argv[3]));int seconds=std::stoi(argv[2]);double heat=argc==5?std::stod(argv[4]):2.5;auto start=std::chrono::steady_clock::now();
 auto score=[&](){int v=0;for(int x=0;x<n;x++){int s=t[x*n+x];for(int y=0;y<n;y++)v+=t[y*n+t[x*n+t[s*n+y]]]!=x;}return v;};
 int energy=score(),best=energy;bestT=t;long long iter=0;std::cerr<<"initial "<<energy<<"\n";
 while(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<seconds && best){
  int r=rng()%n,s=rng()%(n-1);if(s>=r)s++;int mode=rng()%3,c=rng()%n;std::vector<std::pair<int,int>> swaps;
  if(mode<2){
   std::vector<int> perm(n);for(int x=0;x<n;x++)for(int y=0;y<n;y++)if((mode? t[y*n+r]:t[r*n+y])==(mode?t[x*n+s]:t[s*n+x])){perm[x]=y;break;}
   int x=c;do{swaps.emplace_back(mode?x*n+r:r*n+x,mode?x*n+s:s*n+x);x=perm[x];}while(x!=c);
  }else{
   std::vector<int> ca(n),cb(n),perm(n);for(int x=0;x<n;x++)for(int y=0;y<n;y++){if(t[x*n+y]==r)ca[x]=y;if(t[x*n+y]==s)cb[x]=y;}
   for(int x=0;x<n;x++)for(int y=0;y<n;y++)if(cb[y]==ca[x]){perm[x]=y;break;}
   int x=c;do{swaps.emplace_back(x*n+ca[x],x*n+cb[x]);x=perm[x];}while(x!=c);
  }
  for(auto [x,y]:swaps)std::swap(t[x],t[y]);int next=score();
  double temp=0.1+heat*std::exp(-double(iter%150000)/20000);
  if(next<=energy || std::generate_canonical<double,53>(rng)<std::exp((energy-next)/temp))energy=next;
  else for(auto [x,y]:swaps)std::swap(t[x],t[y]);
  if(energy<best){best=energy;bestT=t;std::cerr<<"best "<<best<<" at "<<iter<<"\n";}
  iter++;if(iter%150000==0){t=bestT;energy=best;}
 }
 std::cout<<"{\"order\":"<<n<<",\"violated_equation_instances\":"<<best<<",\"iterations\":"<<iter<<",\"table\":[";
 for(int i=0;i<n*n;i++)std::cout<<(i?",":"")<<bestT[i];std::cout<<"]}\n";
}
