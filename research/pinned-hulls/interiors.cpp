#include <algorithm>
#include <array>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <numeric>
#include <vector>
using namespace std;
using W=unsigned __int128;
int high(W x){uint64_t v=x>>64;return v?127-__builtin_clzll(v):63-__builtin_clzll((uint64_t)x);}
struct Reduced{
 int s, digits[2], pos[256];
 vector<vector<W>> images;
 Reduced(int free):s(free){
  vector<int>mon;
  for(int d=0;d<=3;d++)for(int h=0;h<(1<<s);h++)if(__builtin_popcount((unsigned)h)==d){
   pos[h]=mon.size();mon.push_back(h);
  }
  assert(mon.size()<=128);
  digits[0]=s+1;digits[1]=1+s+s*(s-1)/2;
  images.assign(s,vector<W>(digits[1]));
  for(int j=0;j<s;j++)for(int i=0;i<digits[1];i++)images[j][i]=W(1)<<pos[mon[i]|(1<<j)];
 }
 W product(int a,int b)const{
  W out=0;
  for(int x=a;x;x&=x-1)for(int y=b;y;y&=y-1)
   out^=W(1)<<pos[((x&-x)|(y&-y))>>1];
  return out;
 }
 int consequenceRank(const vector<W>&g,int degree)const{
  W piv[128]={};vector<W>q=g;int rank=0;
  for(size_t it=0;it<q.size();it++){
   W x=q[it];int p=0;
   while(x){p=high(x);if(!piv[p])break;x^=piv[p];}
   if(x==1)return s+1;
   if(!x)continue;
   piv[p]=x;rank+=(p<=s);
   if(p<digits[degree-2]){
    for(const auto&imgs:images){
     W out=0;uint64_t rem=x;
     while(rem){int j=__builtin_ctzll(rem);rem&=rem-1;out^=imgs[j];}
     q.push_back(out);
    }
   }
  }
  return rank;
 }
};
struct Count{
 int k,m,n; Reduced calc; long long cases=0,nonempty=0,miss2=0,miss3=0;
 Count(int left,int right):k(left),m(right),n(left+right+2),calc(max(0,left+right-2)){}
 void test(uint32_t inside, int attach){
  cases++;
  int la=attach&((1<<k)-1),ra=attach>>k;
  if(!la||!ra)return;
  int dl=high(la),dr=high(ra)+k,s=n-4, forms[12]={},free=0;
  for(int i=0;i<k+m;i++)if(i!=dl&&i!=dr)forms[i]=2<<free++;
  forms[dl]=forms[dr]=1;
  for(int i=0;i<k;i++)if(i!=dl&&(la>>i&1))forms[dl]^=forms[i];
  for(int j=0;j<m;j++)if(k+j!=dr&&(ra>>j&1))forms[dr]^=forms[k+j];
  vector<W>guards;int ng[12]={};
  for(int i=0;i<k+m;i++)ng[i]=(attach>>i)&1;
  for(int i=0;i<k;i++)for(int j=0;j<m;j++)if(inside>>(i*m+j)&1){
   ng[i]^=forms[k+j];ng[k+j]^=forms[i];
  }
  for(int i=0;i<k+m;i++)guards.push_back(calc.product(forms[i],ng[i]));
  int basis[16]={};int rank=0;
  for(int h=1;h<1<<(s+1);h+=2){
   int i=0;for(;i<k+m;i++)if(__builtin_parity(h&forms[i])&&__builtin_parity(h&ng[i]))break;
   if(i!=k+m)continue;
   int v=h;while(v&&basis[high(v)])v^=basis[high(v)];if(v){basis[high(v)]=v;rank++;}
   if(rank==s+1)break;
  }
  if(!rank)return; // bridge case proved by a quadratic cut
  nonempty++;
  int target=s+1-rank;
  if(target==0)return;
  if(calc.consequenceRank(guards,2)==target)return;
  miss2++;
  if(calc.consequenceRank(guards,3)!=target){
   miss3++;printf("CUBIC GAP left%d right%d inside%u attach%d\n",k,m,inside,attach);fflush(stdout);exit(3);
  }
 }
};
int main(int argc,char**argv){
 int n=atoi(argv[1]),k=atoi(argv[2])-1,m=n-k-2;
 Count total(k,m);
 vector<vector<int>> edgePerm, vertexPerm;
 vector<int> a(k),b(m);iota(a.begin(),a.end(),0);
 do{
  iota(b.begin(),b.end(),0);
  do{
   vector<int> e(k*m),v(k+m);
   for(int i=0;i<k;i++)v[i]=a[i];
   for(int j=0;j<m;j++)v[k+j]=k+b[j];
   for(int i=0;i<k;i++)for(int j=0;j<m;j++)e[i*m+j]=a[i]*m+b[j];
   edgePerm.push_back(e);vertexPerm.push_back(v);
  }while(next_permutation(b.begin(),b.end()));
 }while(next_permutation(a.begin(),a.end()));
 auto move=[](unsigned bits,const vector<int>&p){
  unsigned out=0;while(bits){int j=__builtin_ctz(bits);bits&=bits-1;out|=1u<<p[j];}return out;
 };
 vector<bool>seen(1u<<(k*m));int reps=0;
 for(unsigned g=0;g<seen.size();g++){
  if(seen[g])continue;reps++;
  vector<int>autom;
  for(int p=0;p<(int)edgePerm.size();p++){
   unsigned h=move(g,edgePerm[p]);seen[h]=true;if(h==g)autom.push_back(p);
  }
  vector<bool>hit(1<<(k+m));
  for(unsigned lab=0;lab<hit.size();lab++){
   if(hit[lab])continue;
   total.test(g,lab);
   for(int p:autom)hit[move(lab,vertexPerm[p])]=true;
  }
 }
 printf("COMPLETE n%d split%d interiors%d graphs%lld nonempty%lld gap2 %lld gap3 %lld\n",n,k+1,reps,total.cases,total.nonempty,total.miss2,total.miss3);
}
