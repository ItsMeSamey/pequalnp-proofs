#include <cstdio>
#include <vector>
#include <array>
#include <algorithm>
#include <bit>
#include <cstdint>
using namespace std;
int L[7],C[7],E[7][2],V,lo[16],hi[16]; bool F[8192],G[8192]; vector<int> freeList,helpers;
bool sub(int a,int b){return !(a&~b);}
bool reach(int g,int h){
 int mn[40]={g,h},mx[40]={g,h},cnt=2,done=0,outputs=0;
 while(true){
  int old=done;
  for(int i=0;i<V;i++)if(!(done>>i&1)){
   int a=lo[i],b=hi[i];bool ok=false;
   for(int j=0;j<cnt&&!ok;j++){
    if(sub(mn[j],b)&&F[a&~mx[j]]){ok=true;break;}
    for(int k=j+1;k<cnt;k++){
      if(sub(mn[j]|mn[k],b)&&sub(a,mx[j]|mx[k])){ok=true;break;}
      if(sub(a,mx[j]&mx[k])&&sub(mn[j]&mn[k],b)){ok=true;break;}
    }
   }
   if(ok){
    done|=1<<i;mn[cnt]=a;mx[cnt++]=b;
    for(int t=0;t<7;t++)if(!(outputs>>t&1)&&(done>>E[t][0]&1)&&(done>>E[t][1]&1)){
     outputs|=1<<t;mn[cnt]=mx[cnt]=L[t];cnt++;
     if(C[t]!=L[t]){mn[cnt]=mx[cnt]=C[t];cnt++;}
    }
   }
  }
  if(done==(1<<V)-1)return true;
  if(old==done)return false;
 }
}
int main(){
 for(int&t:L)if(scanf("%d",&t)!=1)return 1;
 for(int z=0;z<8192;z++){
  F[z]=true;for(int t:L)if(popcount((unsigned)(t&z))>=2)F[z]=false;
  if(F[z])freeList.push_back(z);
 }
 for(int a:freeList)for(int b:freeList)if(!F[a|b])G[a|b]=true;
 for(int g=0;g<8192;g++)if(G[g])helpers.push_back(g);
 int id,di;
 while(scanf("%d%d%d",&id,&di,&V)==3){
  for(int i=0;i<V;i++)scanf("%d",lo+i);
  for(int i=0;i<V;i++)scanf("%d",hi+i);
  for(int&t:C)scanf("%d",&t);
  for(auto&p:E)scanf("%d%d",p,p+1);
  vector<pair<int,int>> eligible;
  for(int g:helpers){
   int mask=0;
   for(int i=0;i<V;i++)if(sub(g,hi[i])&&F[lo[i]&~g])mask|=1<<i;
   if(mask)eligible.push_back({g,mask});
  }
  int count=0;
  for(int i=0;i<(int)eligible.size();i++)for(int j=0;j<i;j++){
   auto[g,u]=eligible[i];auto[h,v]=eligible[j];
   if(g&h)continue;
   bool viable=false;
   for(int a=u;a&&!viable;a&=a-1){int ai=countr_zero((unsigned)a);
    if(sub(h,g|lo[ai]))continue;
    for(int b=v;b;b&=b-1){int bi=countr_zero((unsigned)b);
      if(ai!=bi&&!sub(g,h|lo[bi])){viable=true;break;}
    }
   }
   if(viable&&reach(g,h)){printf("%d %d %d %d\n",id,di,g,h);count++;}
  }
  printf("%d %d -1 %d\n",id,di,count);
 }
}
