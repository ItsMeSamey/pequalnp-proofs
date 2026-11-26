#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <random>
using namespace std;
using W=unsigned __int128;
int par(unsigned v){return __builtin_parity(v);}
int high(W v){return (uint64_t)(v>>64)?127-__builtin_clzll((uint64_t)(v>>64)):63-__builtin_clzll((uint64_t)v);}
struct Fixed{
 int n,k,m,nd,low,monpos[512],forms[12]={},lmask[4]={};
 vector<int>L,R; vector<vector<W>> images; W edge[10][10]={};
 Fixed(vector<int>ls,vector<int>rs):n(ls.size()+rs.size()),k(ls.size()),m(rs.size()),L(ls),R(rs){
  vector<int> label=L;label.insert(label.end(),R.begin(),R.end());int piv[12]={};nd=0;
  for(int t=0;t<3;t++){
   int x=(3>>t)&1;
   for(int i=0;i<n;i++)if(label[i]>>t&1)x|=2<<i;
   while(x>1&&piv[high(x)])x^=piv[high(x)];
   if(x>1)piv[high(x)]=x;
  }
  for(int i=0;i<n;i++){
   if(!piv[i+1])forms[i]=2<<nd++;
   else{int x=piv[i+1];forms[i]=x&1;for(int j=0;j<i;j++)if(x>>(j+1)&1)forms[i]^=forms[j];}
  }
  vector<int> mons;
  for(int deg=0;deg<=3;deg++)for(int v=0;v<1<<nd;v++)if(__builtin_popcount((unsigned)v)==deg){
   monpos[v]=mons.size();mons.push_back(v);}
  if(mons.size()>128)abort();
  low=1+nd+nd*(nd-1)/2;
  images.assign(nd,vector<W>(low));
  for(int j=0;j<nd;j++)for(int a=0;a<low;a++)images[j][a]=W(1)<<monpos[mons[a]|(1<<j)];
  for(int i=0;i<k;i++)for(int j=0;j<m;j++){
   int f=forms[i],g=forms[k+j]; W e=0;
   for(int a=0;a<=nd;a++)if(f>>a&1)for(int b=0;b<=nd;b++)if(g>>b&1)
    e^=W(1)<<monpos[((1<<a)>>1)|((1<<b)>>1)];
   edge[i][j]=e;
  }
 }
 int degree(const vector<int>&a)const{
  vector<W> guards(n);for(int i=0;i<k;i++)for(int j=0;j<m;j++)if(a[i]>>j&1){
   guards[i]^=edge[i][j];guards[k+j]^=edge[i][j];
  }
  for(int d=2;d<=3;d++){
   W piv[128]={};vector<W> todo=guards;int limit=d==2?1+nd:low;
   for(size_t it=0;it<todo.size();it++){
    W u=todo[it];while(u&&piv[high(u)])u^=piv[high(u)];
    if(u==1)goto success;
    if(!u)continue;
    piv[high(u)]=u;
    if(high(u)<limit)for(int j=0;j<nd;j++){
     W v=0,p=u;
     while(p){v^=images[j][__builtin_ctzll((uint64_t)p)];p&=p-1;}todo.push_back(v);
    }
   }
   continue;
  success:return d;
  }
  return 4;
 }
};

#include <set>
#include <numeric>
#ifndef PC_VERTICES
#define PC_VERTICES 9
#endif
const int N=PC_VERTICES;
static_assert(N==9 || N==10);
struct RawRing {
 int mon[N][N];
 unsigned long long table[N][1<<(N+1)]={};
 RawRing(){
  int p=N+1;
  for(int i=0;i<N;i++)for(int j=i;j<N;j++)mon[i][j]=mon[j][i]=i==j?i+1:p++;
  for(int j=0;j<N;j++)for(int x=1;x<(1<<(N+1));x++){
   int bit=__builtin_ctz((unsigned)x);
   table[j][x]=table[j][x&(x-1)]^(1ull<<(bit?mon[j][bit-1]:j+1));
  }
 }
 bool pc2(const array<unsigned long long,N>&g,int a,int b,int h)const{
  unsigned long long piv[64]={}, q[256];int tail=0;
  for(auto x:g)q[tail++]=x;
  q[tail++]=2*a+1;q[tail++]=2*b+1;q[tail++]=2*h;
  for(int f=0;f<tail;f++){
   auto x=q[f];int k=0;
   while(x){k=63-__builtin_clzll(x);if(!piv[k])break;x^=piv[k];}
   if(x==1)return true;
   if(!x)continue;
   piv[k]=x;
   if(k<=N)for(int j=0;j<N;j++)q[tail++]=table[j][x];
  }
  return false;
 }
};
void orbit(int bits, int k, int m, vector<bool>&seen){
 vector<int>a(k),p(m);iota(p.begin(),p.end(),0);
 for(int i=0;i<k;i++)a[i]=(bits>>(m*i))&((1<<m)-1);
 do{
  vector<int>b(k);for(int i=0;i<k;i++)for(int j=0;j<m;j++)b[i]|=((a[i]>>j)&1)<<p[j];
  sort(b.begin(),b.end());
  do{int y=0;for(int i=0;i<k;i++)y|=b[i]<<(m*i);seen[y]=true;}while(next_permutation(b.begin(),b.end()));
 }while(next_permutation(p.begin(),p.end()));
}
int main(int argc,char**argv){
 if(argc!=2)return 2;
 RawRing ring;int k=atoi(argv[1]),m=N-k;
 if(k<1||k>N/2)return 2;
 vector<bool> seen(1ull<<(k*m));long long graphs=0,empty=0,reps=0,d3=0;
 for(int bits=0;bits<1<<(m*k);bits++){
  if(seen[bits])continue;
  graphs++;orbit(bits,k,m,seen);
  vector<int> row(k);array<unsigned long long,N>guard{};int adj[N]={};
  for(int i=0;i<k;i++){
   row[i]=(bits>>(i*m))&((1<<m)-1);
   for(int j=0;j<m;j++)if(row[i]>>j&1){
    adj[i]|=1<<(k+j);adj[k+j]|=1<<i;
    guard[i]^=1ull<<ring.mon[i][k+j];guard[k+j]^=1ull<<ring.mon[i][k+j];
   }
  }
  vector<int>feasible;
  for(int x=0;x<1<<N;x++){
   bool works=true;for(int i=0;i<N;i++)if((x>>i&1)&&par(x&adj[i]))works=false;
   if(works)feasible.push_back(x);
  }
  for(int alpha=1;alpha<1<<k;alpha++)for(int u=1;u<1<<m;u++){
   int beta=u<<k,base=-1,rank=0;int piv[N]={};
   for(int x:feasible)if(par(x&alpha)&&par(x&beta)){
    if(base<0){base=x;continue;}
    int v=x^base;
    while(v){int j=31-__builtin_clz(v);if(piv[j])v^=piv[j];else{piv[j]=v;rank++;break;}}
    if(rank==N-2)break;
   }
   if(base<0){empty++;continue;}
   if(rank==N-2)continue;
   for(int h=1;h<1<<N;h++){
    if(h==alpha||h==beta||h>(h^alpha^beta)||!par(h&base))continue;
    bool ok=true;for(int p:piv)if(par(h&p)){ok=false;break;}if(!ok)continue;
    reps++;if(ring.pc2(guard,alpha,beta,h))continue;
    vector<int>ls(k),rs(m);
    for(int i=0;i<k;i++)ls[i]=((alpha>>i)&1)+4*((h>>i)&1);
    for(int j=0;j<m;j++)rs[j]=2*((u>>j)&1)+4*((h>>(k+j))&1);
    Fixed f(ls,rs);
    int d=f.degree(row);
    if(d==2){puts("ERROR degree disagreement");return 1;}
    if(d==4){printf("DEGREE4 split %d bits %d alpha %d beta %d h %d\n",k,bits,alpha,beta,h);return 0;}
    d3++;
   }
  }
  if(graphs%200==0){printf("partial %lld %lld %lld\n",graphs,reps,d3);fflush(stdout);}
 }
 printf("COMPLETE split %d graphs %lld empty %lld reps %lld d3 %lld\n",k,graphs,empty,reps,d3);
}
