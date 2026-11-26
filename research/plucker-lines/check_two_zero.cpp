#include <array>
#include <cstdio>
#include <vector>
using namespace std;
int par(int x) {return __builtin_parity((unsigned)x);}
struct Basis {
 array<int,25> piv{};
 int reduce(int x) const {while(x){int p=31-__builtin_clz((unsigned)x); if(!piv[p])break;x^=piv[p];}return x;}
 void add(int x){x=reduce(x);if(x)piv[31-__builtin_clz((unsigned)x)]=x;}
};
struct Side {array<int,4> c{};int present=0,b=0,syn=0;};
bool has_single(int own,int zero,int one){
 for(int sel=0;sel<4;sel++){
  Basis cols;
  for(int z=0;z<4;z++){
   int t=1<<z, tag=(z&sel)<<2;
   if(par(z&sel)){
    if(own&t) cols.add(tag|1);
    if(one&t) cols.add(tag|2);
   }else if(zero&t) cols.add(tag|2);
  }
  if(!cols.reduce(1))return true;
 }return false;
}
bool obstruction(int own,int b,const Side& opp){
 static int good[16][16][16];static bool init=false;
 if(!init){for(int i=0;i<16;i++)for(int j=0;j<16;j++)for(int k=0;k<16;k++)good[i][j][k]=has_single(i,j,k);init=true;}
 int ofs[4],n=0,target=0;
 for(int z=0;z<4;z++){ofs[z]=n;int m=(1<<opp.c[z])-1;if(par(z)^(1-b))target|=m<<n;n+=opp.c[z];}
 target|=b<<n;Basis bad;int mixed=0;
 for(int i=0;i<=opp.c[0];i++)for(int j=0;j<=opp.c[1];j++)for(int k=0;k<=opp.c[2];k++)for(int l=0;l<=opp.c[3];l++){
  if(((i+j+k+l)&1)!=b)continue;
  int cnt[]={i,j,k,l},zero=0,one=0,row=1<<n;
  for(int z=0;z<4;z++){if(cnt[z])one|=1<<z;if(cnt[z]<opp.c[z])zero|=1<<z;row|=((1<<cnt[z])-1)<<ofs[z];}
  if(good[own][zero][one])continue;
  bad.add(row);
  int insert=zero&one&~mixed; mixed|=insert;
  for(int z=0;z<4;z++)if(insert>>z&1)for(int h=1;h<opp.c[z];h++)bad.add(((1<<h)|1)<<ofs[z]);
 }return !bad.reduce(target);
}
int main(){
 vector<Side> side;
 for(int a=0;a<5;a++)for(int b=0;b<5;b++)for(int c=0;c<5;c++)for(int d=0;d<5;d++){
  Side x;x.c={a,b,c,d};for(int z=0;z<4;z++){if(x.c[z])x.present|=1<<z;if(x.c[z]&1){x.syn^=z;x.b^=1;}}
  side.push_back(x);
 }
 static bool adm[16][2][625];
 for(int h=0;h<16;h++)for(int b=0;b<2;b++)for(int j=0;j<625;j++)adm[h][b][j]=obstruction(h,b,side[j]);
 int checked=0;for(int i=0;i<625;i++)for(int j=0;j<625;j++)if(side[i].b && !side[j].b && side[i].syn==side[j].syn){
  checked++;
  if(adm[side[i].present][1][j] && adm[side[j].present][0][i]){
   printf("counterexample counts Q0 %d %d %d %d Q1 %d %d %d %d\n",side[i].c[0],side[i].c[1],side[i].c[2],side[i].c[3],side[j].c[0],side[j].c[1],side[j].c[2],side[j].c[3]);return 1;
  }
 }
 printf("%d multiplicity profiles certified\n",checked);
}
