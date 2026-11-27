#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <vector>
using namespace std;
using V=vector<int>;
int p[12],tab[81][12],num,lo,hi,eligible,best;
bool bad[81];
V orbits(int w){
 V parts;int left=4095;
 while(left){int i=__builtin_ctz(left),j=i,b=0;do{b|=1<<j;j=p[tab[w][j]];}while(j!=i);parts.push_back(b);left^=b;}
 return parts;
}
bool joins(V const&parts,V const&h,int r,int s){
 int x=1<<r,y;do{y=x;for(int k:parts)if(k&x)x|=k;for(int k:h)if(k&x)x|=k;}while(x!=y);return (x>>s)&1;
}
void test(int r,int s){
 ++num;if(num<=lo||num>hi)return;
 vector<V> choices;array<V,81> parts;
 for(int w=0;w<81;w++)if(bad[w]){
  parts[w]=orbits(w);int first=0;V options{0};
  for(int k:parts[w]){
   if(k&(1<<r)){if(k&(1<<s))return;first=k;}
   else if(!(k&(1<<s))){int n=options.size();for(int i=0;i<n;i++)options.push_back(options[i]|k);}
  }
  for(int &k:options)k|=first;
  if(!w)options={first};
  choices.push_back(options);
 }
 ++eligible;set<V> hs{V{4095}};
 for(auto &options:choices){set<V> next;
  for(auto &h:hs)for(int x:options){V v;for(int k:h){if(k&x)v.push_back(k&x);if(k&~x)v.push_back(k&~x);}
   sort(v.begin(),v.end());next.insert(v);}
  hs.swap(next);
 }
 for(int w=0;w<81;w++)if(!bad[w])parts[w]=orbits(w);
 for(auto &h:hs){int n=0;for(int w=0;w<81;w++)if(!bad[w])n+=joins(parts[w],h,r,s);
 if(n>best){best=n;printf("best %d at %d roots %d %d p",n,num,r,s);for(int i:p)printf(" %d",i);printf(" blocks");for(int k:h)printf(" %d",k);puts("");fflush(stdout);}}
}
void finish(V const&a,V const&b,int used){
 V u;for(int i=0;i<12;i++)if(!(used>>i&1))u.push_back(i);V v=u;
 for(auto z:{a,b})for(int j=0;j<(int)z.size();j++)p[z[j]]=z[(j+1)%z.size()];
 do{for(int i=0;i<(int)u.size();i++)p[u[i]]=v[i];test(a[0],b[0]);}while(next_permutation(v.begin(),v.end()));
}
void second(V&a,V&b,int used,int mask,bool sign){
 if(mask==15)finish(a,b,used);
 for(int i=0;i<12;i++)if(!(used>>i&1)&&(sign||i%3==1)){
 b.push_back(i);second(a,b,used|(1<<i),mask|(1<<(i/3)),true);b.pop_back();}
}
void first(V&a,int used,int n,bool sign){
 if(n==4){V b;second(a,b,used,0,sign);}
 for(int g=0;g<4;g++){
 int prev=(used>>(3*g))&7;if((!prev&&g!=n)||__builtin_popcount((unsigned)prev)>=2)continue;
 for(int j=0;j<3;j++)if(!(prev>>j&1)&&((!prev&&j==0)||(prev&&(sign||j==1)))){
 int i=3*g+j;a.push_back(i);first(a,used|(1<<i),max(n,g+1),sign||j!=0);a.pop_back();}
 }
}
int main(int argc,char**argv){
 lo=atoi(argv[1]);hi=atoi(argv[2]);
 for(int w=0;w<81;w++){int k=w;array<int,4> z;for(int g=3;g>=0;g--){z[g]=k%3;k/=3;}
 auto [a,b,c,d]=z;bad[w]=(a+c+d)%3==0&&(b+c-d+3)%3==0;
 for(int i=0;i<12;i++)tab[w][i]=3*(i/3)+(i%3+z[i/3])%3;}
 if(argc>3){
 int baseline[]={6,8,7,9,11,10,3,1,5,0,4,2};
 copy(baseline,baseline+12,p);for(int w=0;w<81;w++)bad[w]=w%40==0;
 test(3,5);return best==78?0:1;}
 V a;first(a,0,0,false);printf("interval (%d,%d] total %d eligible %d best %d\n",lo,hi,num,eligible,best);
}
