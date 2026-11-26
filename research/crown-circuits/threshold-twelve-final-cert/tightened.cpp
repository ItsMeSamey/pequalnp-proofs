#include <algorithm>
#include <array>
#include <bit>
#include <cstdio>
#include <numeric>
#include <unordered_set>
using namespace std;
struct X{
 int p,k[8]{},d[8]{},a[8]{},r[8]{};unordered_set<unsigned> seen;
 long long cnt[4]{};
 void deg(int i,int n,bool dbl){if(i==p){inside(0,n,0);return;}for(int x=i?k[i-1]:2;x<=8&&n+(p-i)*x<=24;x++){if((dbl&&x==2)||x+2>p+1)continue;k[i]=x;deg(i+1,n+x,dbl||x==2);}}
 void inside(int i,int n,int m){if(i==p){if(m%2||n-m/2>12)return;copy(d,d+p,r);fill(a,a+p,0);seen.clear();edge(0);return;}
 for(int x=i&&k[i]==k[i-1]?d[i-1]:0;x<=min(p-1,k[i]);x++){if(k[i]+max(x,2)>p+1)continue;d[i]=x;inside(i+1,n,m+x);}}
 void edge(int i){while(i<p&&!r[i])i++;if(i==p){check();return;}unsigned possible=0;for(int j=i+1;j<p;j++)if(r[j])possible|=1<<j;
 int n=r[i];if(popcount(possible)<n)return;r[i]=0;for(unsigned v=possible;v;v=(v-1)&possible)if(popcount(v)==n){a[i]|=v;for(int j=i+1;j<p;j++)if(v>>j&1){r[j]--;a[j]|=1<<i;}edge(i+1);for(int j=i+1;j<p;j++)if(v>>j&1){r[j]++;a[j]^=1<<i;}a[i]^=v;}r[i]=n;}
 unsigned code(int*perm){unsigned res=0,bit=0;for(int i=0;i<p;i++)for(int j=i+1;j<p;j++,bit++)if(a[perm[i]]>>perm[j]&1)res|=1u<<bit;return res;}
 void images(int i,int*perm){if(i==p){seen.insert(code(perm));return;}int j=i+1;while(j<p&&k[i]==k[j]&&d[i]==d[j])j++;do{images(j,perm);}while(next_permutation(perm+i,perm+j));}
 void check(){
  int h[8]{},far[8]{},component[8]{};unsigned treated=0;int outside=0,ncomponents=0;
  for(int i=0;i<p;i++)if(!(treated>>i&1)){unsigned set=1u<<i,prev=0;while(prev!=set){prev=set;for(int j=0;j<p;j++)if(set>>j&1)set|=a[j];}
   ncomponents++;int z=popcount(set);for(int j=0;j<p;j++)if(set>>j&1)component[j]=z;outside+=max(0,z-2);treated|=set;}
  for(int i=0;i<p;i++){unsigned z=0;for(int j=0;j<p;j++)if(a[i]>>j&1)z|=a[j];h[i]=popcount(z&~(unsigned(a[i])|(1u<<i)));
   far[i]=component[i]-1-d[i]+outside-max(0,component[i]-2);if(k[i]>ncomponents+1||k[i]>4||k[i]+d[i]+h[i]>p+1)return;}
  int perm[8];iota(perm,perm+p,0);unsigned rep=code(perm);if(seen.count(rep))return;images(0,perm);cnt[0]++;
  for(int i=0;i<p;i++)if(k[i]+d[i]+far[i]>p+1)return;cnt[1]++;
  unsigned small=0,two=0,all=(1u<<p)-1;for(int i=0;i<p;i++){if(k[i]<=4)small|=1<<i;if(k[i]<=3)two|=1<<i;}
  int typed=0;for(unsigned s=small;;s=(s-1)&small){int ns=popcount(s),b=p-ns;bool ok=!(two&~s)&&ns<=7&&(small!=all||b>0)&&popcount(small&~s)<=5;
   for(int i=0;i<p&&ok;i++){int ds=popcount((unsigned)a[i]&s),db=d[i]-ds;if(2*k[i]+db+max(far[i],2-d[i])>b+9||7-ns+ds<(int)bit_width((unsigned)k[i]-1))ok=false;}
   int coldEdges=0; for(int i=0;i<p;i++)if(s>>i&1)coldEdges+=popcount(unsigned(a[i])&s); if(coldEdges>2)ok=false; if(ok){typed++;printf("graph %d %u %u",p,rep,s);for(int i=0;i<p;i++)printf(" %d/%d/%d",k[i],d[i],far[i]);puts("");}
   if(!s)break;}
  if(typed){cnt[2]++;cnt[3]+=typed;}}
};
int main(){for(int p=3;p<=8;p++){X c;c.p=p;c.deg(0,0,false);printf("total %d %lld %lld %lld %lld\n",p,c.cnt[0],c.cnt[1],c.cnt[2],c.cnt[3]);fflush(stdout);}}
