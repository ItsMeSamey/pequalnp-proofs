#include <array>
#include <cstdio>
using namespace std;
int par(int x){return __builtin_parity((unsigned)x);}
struct basis{
 int p[16]={};
 int reduce(int x) const{while(x&&p[31-__builtin_clz(x)])x^=p[31-__builtin_clz(x)];return x;}
 void add(int x){x=reduce(x);if(x)p[31-__builtin_clz(x)]=x;}
};
bool singleton(int c,const int k[2][4],int code){
 // state 0 all zeros, 1 all ones, 2 mixed odd, 3 mixed even.
 for(int z=0;z<4;z++){
  basis b;
  for(int d=0;d<2;d++)for(int u=0;u<4;u++)if(k[d][u]){
   int st=d==c?1:((code>>(2*u))&3);
   int bit=par(u&z);
   if(st==bit || st>=2)b.add((u&z)|(1<<(2+d)));
  }
  if(!b.reduce(1<<(2+c)))return true;
 }return false;
}
bool attainable(int c,const int k[2][4]){
 bool mixed[4]={},bad[256]={};
 for(int code=0;code<256;code++){
  bool works=true; int ones=0;
  for(int u=0;u<4;u++){
   int n=k[1-c][u], st=(code>>(2*u))&3;
   if((st==1&&!n)||(st==2&&n<2)||(st==3&&n<3))works=false;
   ones+=k[c][u]+(st==1?n:st==2?1:0);
  }
  if(!works || ones%2 || singleton(c,k,code))continue;
  bad[code]=true;
  for(int u=0;u<4;u++)if(((code>>(2*u))&3)>=2)mixed[u]=true;
 }
 basis b;
 for(int code=0;code<256;code++)if(bad[code]){
  int row=16;
  for(int u=0;u<4;u++){
   int st=(code>>(2*u))&3;
   if(st==2||(st==1&&(!mixed[u]||(k[1-c][u]&1))))row|=1<<u;
  }
  b.add(row);
 }
 int goal=c?0:16;
 for(int u=0;u<4;u++)if(k[1-c][u]&&(par(u)^c)&&(!mixed[u]||(k[1-c][u]&1)))goal|=1<<u;
 return !b.reduce(goal);
}
int main(){
 int checked=0;
 for(int idx=0;idx<390625;idx++){
  int k[2][4],sum[2]={},zsum[2]={},v=idx;
  for(int d=0;d<2;d++)for(int u=0;u<4;u++){
   k[d][u]=v%5;v/=5;sum[d]+=k[d][u];if(k[d][u]%2)zsum[d]^=u;
  }
  if(!(sum[0]%2)||sum[1]%2 || zsum[0]!=zsum[1] || !par(zsum[0]))continue;
  checked++;
  if(attainable(0,k)&&attainable(1,k)){printf("counter %d\n",idx);return 1;}
 }
 printf("all %d admissible multiplicity profiles passed\n",checked);
}
