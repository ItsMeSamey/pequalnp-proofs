#include <algorithm>
#include <array>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
struct Arm{int mask;array<int,13> yes,no,charge;};
bool debit(int need,int first,int d,int limit,int mass[],int compatible[],int weight[]){
 if(!need)return true;
 for(int i=first;i<13;i++){
  if(weight[i]>=limit)continue;
  int w=weight[i],f=compatible[i];bool valid=true;
  for(int z=f;z;z&=z-1)if(mass[countr_zero((unsigned)z)]+w>limit){valid=false;break;}
  if(!valid)continue;
  for(int z=f;z;z&=z-1)mass[countr_zero((unsigned)z)]+=w;
  weight[i]*=2;
  if(debit(need-1,i,d,limit,mass,compatible,weight))return true;
  weight[i]=w;for(int z=f;z;z&=z-1)mass[countr_zero((unsigned)z)]-=w;
 }
 return false;
}
int main(int argc,char**argv){
 int s=atoi(argv[1]),dirty=atoi(argv[2]),common=atoi(argv[3]),D=7-s,arms=common?1:s;
 array<int,13> row;int id=0;
 while(cin>>row[0]){
  for(int i=1;i<13;i++)cin>>row[i];int U[2]={};
  for(int j=0;j<s;j++)for(int i=0;i<13;i++)if(row[i]>>(2+j)&1)U[j]|=1<<i;
  vector<Arm> options[2];
  for(int a=0;a<arms;a++)for(int m=1;m<8192;m++){
   bool good=true;int first=common?0:a,last=common?s-1:a;
   for(int j=first;j<=last;j++)
    if(popcount(unsigned(U[j]&m))!=int(j<dirty)||popcount(unsigned(m&~U[j]))<3)good=false;
   if(!good)continue; Arm z{};z.mask=m;
   for(int i=0;i<13;i++){
    int on=m>>i&1;z.charge[i]=-on;
    for(int j=first;j<=last;j++){int u=U[j]>>i&1;
     if(u&&!on)z.yes[i]|=1<<j;if(on&&!u)z.no[i]|=1<<j;z.charge[i]+=on|u;}
   }options[a].push_back(z);
  }
  if(arms==1)options[1].push_back(Arm{});
  int pure=0;
  for(int i=0;i<13;i++)pure+=(row[i]&3)+popcount(unsigned(row[i]>>2));
  int required=max(0,2+(max(0,2*(6-s)+dirty-(26-pure))+1)/2-dirty);
  long long total=0,hits=0;
  for(auto const&a:options[0])for(auto const&b:options[1]){
   total++;int mass[4]={},len=0,compatible[13]={},weight[13]={};bool fine=true;
   for(int i=0;i<13&&fine;i++){
    int cap=2+(row[i]&3)+common-a.charge[i]-b.charge[i];
    if(cap<0){fine=false;break;}
    int yes=a.yes[i]|b.yes[i],no=a.no[i]|b.no[i],free=((1<<s)-1)^(yes|no);
    len+=cap+popcount(unsigned(yes|no));
    int vol=1<<(D-min(D,cap));weight[i]=vol;
    for(int f=free;;f=(f-1)&free){compatible[i]|=1<<(yes|f);if((mass[yes|f]+=vol)>(1<<D)){fine=false;break;}if(!f)break;}
   }
   if(fine&&len-required>=49&&debit(required,0,D,1<<D,mass,compatible,weight)){
    hits++;if(argc>4)cerr<<id<<" "<<a.mask<<" "<<b.mask<<"\n";
   }
  }cout<<id++<<" "<<total<<" "<<hits<<endl;
 }
}
