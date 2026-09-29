#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <vector>
// Research search for a constructive replacement of the E677 Wilson tail.
// Each marked order follows from a finite-field seed, product, one-hole TD,
// or common-point TD. Unmarked orders are NOT nonexistence results.
// This executable is not a Lean proof or a catalogue evidence source.
// Usage: executable [bound (default 3000000)] [optional output bitmap]
int main(int argc,char**argv) {
  int B=argc>1?atoi(argv[1]):3000000;
  if(B<2 || B>300000000) {fprintf(stderr,"bound must be in [2,300000000]\n");return 2;}
  std::vector<int> sp(B+1), least(B+1,B+1);
  for(int p=2;p<=B;p++) if(!sp[p]) for(int n=p;n<=B;n+=p) if(!sp[n]) sp[n]=p;
  std::vector<unsigned char> have(B+1,0);
  have[0]=have[1]=1;
  long aff=0,prod=0,glue=0,common=0;
  for(int n=2;n<=B;n++) {
    int m=n,p=sp[n],q=1,e=0;
    while(m%p==0) {m/=p;q*=p;e++;}
    least[n]=std::min(q,least[m]);
    int d=p==5?1:p%5==1?1:p%5==4?2:4;
    if(have[m] && e%d==0) {have[n]=1;aff++;}
  }
  std::vector<int> small;
  for(int n=2;n<=B;n++) {
    if(!have[n]) continue;
    small.push_back(n);
    for(int a:small) {
      if(1LL*a*n>B)break;
      if(!have[a*n]) {have[a*n]=1;prod++;}
    }
    for(int e=0;e<=1;e++) {
      int q=n-e;
      if(q>=80 && least[q]>=80 && 80LL*q<=B) {
        for(int r=0;r<=q && 80LL*q+r+e<=B;r++)
          if(have[r+e] && !have[80*q+r+e]) {have[80*q+r+e]=1;glue++;}
      }
      if(e==1 && q>=2) for(int k:small) {
        if(k>least[q]+1 || 1LL*k*q+1>B)break;
        if(!have[k*q+1]) {have[k*q+1]=1;common++;}
      }
    }
  }
  printf("B=%d affine=%ld products=%ld glue=%ld common=%ld\n",B,aff,prod,glue,common);
  for(int a=10000;a<=B;a*=10) {
    int total=0,miss=0,last=0,b=std::min(B,a*10-1);
    for(int n=a;n<=b;n++)if(n%5<=1) {total++;if(!have[n]) {miss++;last=n;}}
    printf("[%d,%d] missing %d/%d last %d\n",a,b,miss,total,last);
  }
  int run=0,best=0,end=0;
  for(int n=1;n<=B;n++)if(n%5<=1) {
    if(have[n]) {run++;if(run>best){best=run;end=n;}}else run=0;
  }
  printf("Longest admissible run %d ending %d\n",best,end);
  int last_odd=0;
  for(int n=1;n<=B;n+=10) if(!have[n])last_odd=n;
  printf("Last missing order congruent to 1 mod 10: %d\n",last_odd);
  if(argc>2) {
    FILE*f=fopen(argv[2],"wb");
    if(!f) {perror(argv[2]);return 2;}
    bool ok=fwrite(have.data(),1,have.size(),f)==have.size();
    fclose(f);
    if(!ok) {fprintf(stderr,"incomplete bitmap write\n");return 2;}
  }
}
