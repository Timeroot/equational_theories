// Search for translated-prefix cover certificates. Outputs must be replayed
// by spectrum_tail_cover_check.cpp; this optimizer is not trusted.
// Usage: HAVE CUTOFF END CHUNK OUTPUT (HAVE filename must contain "have").
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <fstream>
#include <map>
#include <array>
#include <string>
#include <set>
using I=int64_t;using U=uint64_t;
const I SOURCE=1000000000;std::vector<U>h;std::vector<int>ps,ks={1008,2223,2511,3087,3951,5328,5871,6288,7008,7056};
std::vector<int> least; std::set<I> gaps; I C,covered;std::map<I,std::array<I,3>> recipes;
bool has(I n){return n>=0&&n<=SOURCE&&(h[n/64]>>(n%64)&1);}
bool td(int k,I q){if(q<k)return false;if(q<(I)least.size())return least[q]>=k;for(int p:ps){if(p>=k)break;if(q%p==0){I v=1;do{q/=p;v*=p;}while(q%p==0);if(v<k)return false;}}return true;}
bool model(I n);
bool find(I n,int& k,I& q,int& e){for(int K:ks){I top=n/K,bot=(n+K)/(K+1);bot=std::max(bot,(n-SOURCE+K-1)/K);I mid=(n-std::min(top,SOURCE)/2)/K;mid=std::max(bot,std::min(top,mid));for(I delta=0;delta<=top-bot;delta++){I Q=mid+delta;if(Q>top)Q=bot+(Q-top-1);if(!td(K,Q))continue;I r=n-K*Q;for(int E=0;E<2;E++)if((!E||r>0)&&r<=Q+E&&has(r)&&model(Q+E)){k=K;q=Q;e=E;return true;}}}return false;}
bool model(I n){if(n<=SOURCE)return has(n);if(n>=C&&n<=covered&&!gaps.count(n))return true;if(recipes.count(n))return true;int k,e;I q;if(find(n,k,q,e)){recipes[n]={k,q,e};return true;}return false;}
// Translate the source interval into a target chunk; clip both endpoints.
void paint0(const std::vector<U>& source, std::vector<U>& target,
               I lo, I hi, I offset, I end, bool common) {
  const I a = std::max<I>(common, lo - offset);
  const I b = std::min({end, SOURCE, hi - offset});
  if (a > b) return;
  const I first = a + offset - lo, last = b + offset - lo;
  const I fw = first/64, lw = last/64;
  const I bit_offset = lo+64*fw-offset;
  const I word = bit_offset >= 0 ? bit_offset/64 : (bit_offset-63)/64;
  const int bits = bit_offset-64*word;
  auto boundary = [&](I index) {
    U value = 0;
    if (index >= 0 && index < I(source.size())) value = source[index] >> bits;
    if (bits && index+1 >= 0 && index+1 < I(source.size()))
      value |= source[index+1] << (64-bits);
    return value;
  };
  const U first_mask = ~U(0) << (first%64);
  const U last_mask = last%64 == 63 ? ~U(0) : (U(1) << (last%64+1))-1;
  if (fw == lw) {
    target[fw] |= boundary(word) & first_mask & last_mask;
    return;
  }
  target[fw] |= boundary(word) & first_mask;
  // Interior words lie wholly within the certified source interval. Separate
  // boundary handling lets the compiler vectorize these contiguous shifts.
  const U* __restrict input = source.data()+word+1;
  U* __restrict output = target.data()+fw+1;
  if (bits) {
    for (I j = 0; j < lw-fw-1; ++j)
      output[j] |= (input[j] >> bits) | (input[j+1] << (64-bits));
  } else {
    for (I j = 0; j < lw-fw-1; ++j) output[j] |= input[j];
  }
  target[lw] |= boundary(word+lw-fw) & last_mask;
}

void paint(std::vector<U>&dst,I lo,I hi,I offset,I end,bool common){paint0(h,dst,lo,hi,offset,end,common);}

int main(int argc,char**argv){if(argc!=6)return 2;std::ifstream f(argv[1],std::ios::binary);h.resize((SOURCE+128)/64);f.read((char*)h.data(),h.size()*8);{std::string ip=argv[1];ip.replace(ip.find("have"),4,"idem");std::ifstream ff(ip,std::ios::binary);std::vector<U>d(200000/64+2);ff.read((char*)d.data(),d.size()*8);ks.clear();for(int k=2;k<200000;k++)if((d[k/64]>>(k%64)&1)&&(d[(k+1)/64]>>((k+1)%64)&1))ks.push_back(k);}C=atoll(argv[2]);I end=atoll(argv[3]),chunk=atoll(argv[4]);std::string path=argv[5];I resume=getenv("TAIL_RESUME")?atoll(getenv("TAIL_RESUME")):0;FILE*out=fopen(path.c_str(),resume?"a":"w");for(int p=2;p<=200000;p++){bool prime=true;for(int d=2;d*d<=p;d++)if(p%d==0)prime=false;if(prime)ps.push_back(p);}{const int L=100000000;std::vector<int> sp(L+1);least.resize(L+1,L+1);for(int p=2;p<=L;p++)if(!sp[p])for(int n=p;n<=L;n+=p)if(!sp[n])sp[n]=p;for(int n=2;n<=L;n++){int p=sp[n],m=n,v=1;while(m%p==0){m/=p;v*=p;}least[n]=std::min(v,least[m]);}}covered=resume?resume:C-1;I total=0;for(I lo=resume?resume+1:C;lo<=end;lo+=chunk){I hi=std::min(lo+chunk-1,end);std::vector<U>dst((hi-lo+64)/64);paint(dst,lo,hi,0,SOURCE,false);I checks=0;for(I j=0;j<(I)dst.size();j++){U mask=~dst[j];if(j==(I)dst.size()-1&&(hi-lo+1)%64)mask&=(U(1)<<((hi-lo+1)%64))-1;while(mask){I n=lo+64*j+__builtin_ctzll(mask);int k,e;I q;if(!find(n,k,q,e)){fprintf(stderr,"GAP n=%lld\n",(long long)n);gaps.insert(n);dst[j]|=U(1)<<(n-lo-64*j);mask&=mask-1;continue;}fprintf(out,"%lld %lld %d %lld %d\n",(long long)lo,(long long)hi,k,(long long)q,e);paint(dst,lo,hi,k*q,q+e,e);checks++;mask=~dst[j];if(j==(I)dst.size()-1&&(hi-lo+1)%64)mask&=(U(1)<<((hi-lo+1)%64))-1;}}covered=hi;total+=checks;if((lo-C)/chunk%10==0){fprintf(stderr,"covered=%lld checks=%lld total=%lld recipes=%zu\n",(long long)hi,(long long)checks,(long long)total,recipes.size());fflush(out);}}
fclose(out);FILE*gf=fopen((path+".gaps").c_str(),"w");for(I n:gaps)fprintf(gf,"%lld\n",(long long)n);fclose(gf);FILE*r=fopen((path+".recipes").c_str(),"w");for(auto [n,v]:recipes)fprintf(r,"%lld %lld %lld %lld\n",(long long)n,(long long)v[0],(long long)v[1],(long long)v[2]);fclose(r);printf("lastGap=%lld\n",gaps.empty()?0LL:(long long)*gaps.rbegin());printf("complete C=%lld end=%lld covers=%lld recipes=%zu\n",(long long)C,(long long)end,(long long)total,recipes.size());}
