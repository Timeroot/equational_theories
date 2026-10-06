// Exploratory E667 annealing over two input permutations of a fixed quasigroup.
// Input: path to n followed by n*n integer table entries; seconds; random seed.
// The output is a near-model unless violated_equation_instances is exactly zero.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
int main(int argc,char**argv){
 if(argc!=4){std::cerr<<"usage: isotope_anneal table.txt seconds seed\n";return 2;}
 std::ifstream in(argv[1]);int n;in>>n;std::vector<int> q(n*n),t(n*n),a(n),b(n),bestA,bestB;for(int&z:q)in>>z;
 std::mt19937_64 rng(std::stoull(argv[3]));int sec=std::stoi(argv[2]);int best=n*n+1,energy=0;long long iter=0;
 auto now=[](){return std::chrono::steady_clock::now();};auto start=now();
 auto rebuild=[&](){for(int x=0;x<n;x++)for(int y=0;y<n;y++)t[x*n+y]=q[a[x]*n+b[y]];};
 auto score=[&](){int v=0;for(int x=0;x<n;x++){int sx=t[x*n+x];for(int y=0;y<n;y++)v+=t[y*n+t[x*n+t[sx*n+y]]]!=x;}return v;};
 auto randomize=[&](){std::iota(a.begin(),a.end(),0);std::iota(b.begin(),b.end(),0);std::shuffle(a.begin(),a.end(),rng);std::shuffle(b.begin(),b.end(),rng);rebuild();energy=score();};
 randomize();
 while(std::chrono::duration<double>(now()-start).count()<sec){
  int x=rng()%n,y=rng()%(n-1);if(y>=x)y++;int mode=rng()%3;
  if(mode!=1)std::swap(a[x],a[y]);if(mode!=0)std::swap(b[x],b[y]);rebuild();int next=score();
  double temp=0.25+3.0*std::exp(-double(iter%200000)/30000);
  bool accept=next<=energy || std::generate_canonical<double,53>(rng)<std::exp((energy-next)/temp);
  if(accept)energy=next;else{if(mode!=1)std::swap(a[x],a[y]);if(mode!=0)std::swap(b[x],b[y]);}
  if(energy<best){best=energy;bestA=a;bestB=b;std::cerr<<"best "<<best<<" iteration "<<iter<<"\n";}
  if(!best)break;
  iter++;if(iter%200000==0)randomize();
 }
 std::cout<<"{\"order\":"<<n<<",\"violated_equation_instances\":"<<best<<",\"iterations\":"<<iter<<",\"A\":[";
 for(int i=0;i<n;i++)std::cout<<(i?",":"")<<bestA[i];std::cout<<"],\"B\":[";
 for(int i=0;i<n;i++)std::cout<<(i?",":"")<<bestB[i];std::cout<<"]}\n";
}
