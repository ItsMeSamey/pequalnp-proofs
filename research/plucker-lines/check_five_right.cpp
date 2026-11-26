#include <cstdio>
#include <vector>
#include <set>
#include <array>
using namespace std;
int parity(int x) { return __builtin_parity((unsigned)x); }
struct Basis {
 array<int,10> piv{};
 int reduce(int x) const { for(int i=9;i>=0;--i) if((x>>i)&1) x^=piv[i];return x; }
 void add(int x) {x=reduce(x); if(x) piv[31-__builtin_clz((unsigned)x)]=x;}
};
int main() {
 int tests=0;
 for(int m=1;m<=5;m+=2) for(int u=1;u<=m;u+=2) {
  int all=(1<<m)-1, q0=(1<<u)-1;
  vector<int> neutral;
  for(int z=1;z<=all;z++) if(!parity(z)) neutral.push_back(z);
  for(int S=0;S<(1<<(int)neutral.size());++S) {
   ++tests;
   int E=0;
   for(int j=0;j<(int)neutral.size();++j) if(S>>j&1) E^=neutral[j];
   Basis projected[32];
   for(int y=1;y<=all;y++) for(int j=0;j<(int)neutral.size();++j) {
    int z=neutral[j];
    if((S>>j&1) && !parity(z&y)) projected[y].add(z&y);
   }
   Basis bad;
   for(int r=0;r<2;++r) {
    int own=r ? all^q0:q0;
    for(int a=0;a<=all;a++) if((a&own)==own && !parity(a)) {
     bool singleton=false;
     for(int y=1;y<=all;++y) if(parity(y&own) && !parity(y&(all^own)) &&
                                       !projected[y].reduce(a&y)) singleton=true;
     if(!singleton) bad.add(a|(1<<(m+r)));
    }
   }
   if(!bad.reduce(E|(1<<m))) {printf("exception %d %d %d\n",m,u,S);return 1;}
  }
 }
 printf("%d neutral systems certified\n",tests);
}
