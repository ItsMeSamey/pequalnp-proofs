#include "hereditary.hpp"
#include <cstdio>
using namespace hereditary;
int main(){setup();Mask f{};f[10]=1;int hist[40]{};while(scanf("%d",&f[0])==1){
 for(int i=1;i<10;i++)scanf("%d",&f[i]);int b=bound<true>(f,f);hist[b]++;
 if(b<=15){for(int i=0;i<10;i++)printf("%d ",f[i]);printf("%d\n",b);}
 }for(int i=0;i<40;i++)if(hist[i])fprintf(stderr,"%d %d\n",i,hist[i]);}
