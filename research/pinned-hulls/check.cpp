#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <numeric>
#include <random>
#include <vector>
using namespace std;
using W=unsigned __int128;
int hi(W x){uint64_t h=x>>64;return h?127-__builtin_clzll(h):63-__builtin_clzll((uint64_t)x);}
int bitcount(unsigned u){return __builtin_popcount(u);}
struct Ring{
 int variables,low,limit; vector<int>pos,mons; vector<vector<W>> products;
 Ring(int free,int degree):variables(free),pos(1<<free){
  low=0;
  for(int d=0;d<=degree;d++)for(int x=0;x<1<<free;x++)if(bitcount(x)==d){
   pos[x]=mons.size();mons.push_back(x);if(d<degree)low++;}
  limit=mons.size();if(limit>128)abort();products.assign(free,vector<W>(low));
  for(int i=0;i<free;i++)for(int j=0;j<low;j++)products[i][j]=W(1)<<pos[mons[j]|(1<<i)];
 }
 vector<int> linears(const vector<int>&adj)const{
  vector<W> eq;
  for(int i=0;i<int(adj.size());i++){
   int left=i<2?0:(1<<(i-2));W p=0;
   for(int j=0;j<int(adj.size());j++)if(adj[i]>>j&1){
    int right=j<2?0:(1<<(j-2));p^=W(1)<<pos[left|right];
   }
   eq.push_back(p);
  }
  W basis[128]={};
  for(size_t f=0;f<eq.size();f++){
   W x=eq[f];while(x&&basis[hi(x)])x^=basis[hi(x)];
   if(!x)continue;
   if(x==1){vector<int>all;for(int j=0;j<=variables;j++)all.push_back(1<<j);return all;}
   int k=hi(x);basis[k]=x;
   if(k<low)for(int j=0;j<variables;j++){
    W y=0,v=x;while(v){int u=__builtin_ctzll((uint64_t)v);v&=v-1;y^=products[j][u];}eq.push_back(y);}
  }
  vector<int>lin;
  for(int j=0;j<=variables;j++)if(basis[j])lin.push_back((int)basis[j]);
  return lin;
 }
};
int ranki(vector<int>v){
 int piv[32]={},rank=0;
 for(int x:v){while(x&&piv[hi(x)])x^=piv[hi(x)];if(x){piv[hi(x)]=x;rank++;}}
 return rank;
}
struct Search{
 int n; Ring r2,r3; long long tested=0,nonempty=0,gap2=0,gap3=0,empty2=0,empty3=0;
 Search(int size):n(size),r2(size-2,2),r3(size-2,3){}
 void test(const vector<int>&a){
  tested++;vector<int>points;
  for(int x=3;x<1<<n;x+=4){
   bool ok=true;for(int i=0;i<n;i++)if((x>>i&1)&&(__builtin_parity(a[i]&x)))ok=false;
   if(ok)points.push_back(((x>>2)<<1)|1);
  }
  if(points.size())nonempty++;
  int exact=n-1-ranki(points);
  auto lin=r2.linears(a);if((int)lin.size()==exact)return;
  long long &c=points.empty()?empty2:gap2;c++;
  auto cub=r3.linears(a);if((int)cub.size()!=exact){(points.empty()?empty3:gap3)++;}
  if(c!=1 && (int)cub.size()==exact)return;
  // Return an explicit affine form absent from the computed consequence space.
  auto deficient=(int)cub.size()==exact?lin:cub;
  int missing=0;
  for(int h=1;h<1<<(n-1);h++){
   bool vanishes=true;for(int p:points)if(__builtin_parity(p&h))vanishes=false;
   if(!vanishes)continue;
   auto ext=deficient;ext.push_back(h);if(ranki(ext)>(int)deficient.size()){missing=h;break;}
  }
  printf("gap n%d roots0,1 adj",n);for(int v:a)printf(" %d",v);
  printf(" points%zu exact%d degree2-%zu degree3-%zu missing%d\n",points.size(),exact,lin.size(),cub.size(),missing);
  fflush(stdout);
  if((int)cub.size()!=exact && !points.empty())exit(3);
 }
 void summary(){printf("DONE n%d graphs%lld nonempty%lld gap2%lld gap3%lld emptygap2%lld emptygap3%lld\n",n,tested,nonempty,gap2,gap3,empty2,empty3);fflush(stdout);}
};
int main(int argc,char**argv){
 int n=atoi(argv[1]), draws=atoi(argv[2]);Search s(n);
 vector<pair<int,int>>edges;int num[12][12]={};
 for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)if(i||j!=1){
  num[i][j]=num[j][i]=edges.size();edges.push_back({i,j});
 }
 auto adj=[&](uint64_t mask){vector<int>a(n);a[0]=2;a[1]=1;for(size_t k=0;k<edges.size();k++)if(mask>>k&1){
  auto [i,j]=edges[k];a[i]|=1<<j;a[j]|=1<<i;}return a;};
 if(draws>0){
  mt19937_64 rng(argc>3?atoi(argv[3]):852);
  for(int c=0;c<draws;c++){uint64_t b=0;double prob=(1+(rng()%19))/20.;
   for(size_t j=0;j<edges.size();j++)if(generate_canonical<double,32>(rng)<prob)b|=1ull<<j;
   s.test(adj(b));}s.summary();return 0;
 }
 size_t end=1ull<<edges.size();vector<bool>seen(end);
 vector<vector<int>> perm;
 for(int flip=0;flip<2;flip++){vector<int>p(n);iota(p.begin(),p.end(),0);if(flip)swap(p[0],p[1]);do{
  vector<int>row;for(auto [i,j]:edges)row.push_back(num[p[i]][p[j]]);perm.push_back(row);
 }while(next_permutation(p.begin()+2,p.end()));}
 for(size_t g=0;g<end;g++){
  if(seen[g])continue;s.test(adj(g));
  for(auto &p:perm){size_t h=0;for(int j=0;j<(int)edges.size();j++)if(g>>j&1)h|=size_t(1)<<p[j];seen[h]=true;}
 }s.summary();
}
