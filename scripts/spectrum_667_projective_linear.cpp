// Research-only exhaustive check of Q(Ax,By) on the 15 nonzero vectors of F2^4.
// Q(x,x)=x and Q(x,y)=x XOR y otherwise; A,B range over GL(4,2).
// This excludes this restricted construction family only, not arbitrary E667 models.
// Build: c++ -O3 scripts/spectrum_667_projective_linear.cpp -o /tmp/e667-pg
#include <array>
#include <vector>
#include <iostream>
#include <fstream>
using P=std::array<unsigned char,16>;
int main(){
 std::vector<P> gl;for(int a=1;a<16;a++)for(int b=1;b<16;b++)for(int c=1;c<16;c++)for(int d=1;d<16;d++){
 P p{};bool seen[16]={};bool ok=true;int e[]={a,b,c,d};for(int x=0;x<16;x++){int y=0;for(int i=0;i<4;i++)if(x>>i&1)y^=e[i];p[x]=y;if(seen[y]){ok=false;break;}seen[y]=true;}if(ok)gl.push_back(p);
 }
 std::cerr<<"GL4(2) maps "<<gl.size()<<"\n";unsigned long count=0,diag=0;
 for(auto&a:gl)for(auto&b:gl){
 auto op=[&](int x,int y)->int{int u=a[x],v=b[y];return u==v?u:u^v;};
 bool ok=true;for(int x=1;x<16;x++)if(op(x,op(x,op(op(x,x),x)))!=x){ok=false;break;}
 if(!ok)continue;diag++;
 for(int x=1;x<16&&ok;x++)for(int y=1;y<16;y++)if(op(y,op(x,op(op(x,x),y)))!=x){ok=false;break;}
 if(ok){count++;std::cout<<"SAT A:";for(int x=1;x<16;x++)std::cout<<int(a[x])<<",";std::cout<<" B:";for(int x=1;x<16;x++)std::cout<<int(b[x])<<",";std::cout<<"\n";return 0;}
 }
 std::cout<<"UNSAT restricted GL4(2) isotopes; pairs="<<gl.size()*gl.size()<<" diagonal_survivors="<<diag<<"\n";
}
