#include <algorithm>
#include <array>
#include <cstdio>
#include <fstream>
#include <set>
using namespace std;
int perm[24][8192];
int main(int argc,char**argv){
 ifstream in(argv[1]);for(auto &p:perm)for(int &v:p)in>>v;
 using F=array<int,11>;F f;set<F> reps;
 size_t n=0;
 while(scanf("%d",&f[0])==1){for(int i=1;i<11;i++)scanf("%d",&f[i]);F best=f;
  for(auto &p:perm){F x;for(int i=0;i<11;i++)x[i]=p[f[i]];sort(x.begin(),x.end());if(x<best)best=x;}
  reps.insert(best);n++;
 }for(auto&row:reps){for(int v:row)printf("%d ",v);puts("");}fprintf(stderr,"%zu cases %zu reps\n",n,reps.size());}
