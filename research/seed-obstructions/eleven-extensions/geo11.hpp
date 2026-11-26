int owner[8192],part[8192],prim[8192]{},ext[8192],lines[13]{},localCost[2048],tag[16]{};
vector<int> operands[8192];
void geometry(){
 fill(owner,owner+8192,-1);
 for(int l=0;l<13;l++){
   auto pt=[&](int d){return 1<<((l+d)%13);};
   lines[l]=pt(0)|pt(1)|pt(3)|pt(9);
   if(l<6)prim[pt(0)|pt(1)]=prim[pt(3)|pt(9)]=prim[lines[l]]=1;
   prim[1<<l]=1;
 }
 int k=0;
 for(int m=1;m<16;m++)if(popcount(unsigned(m))>=2)tag[m]=1<<(k++);
 for(int s=0;s<8192;s++){
   ext[s]=none_of(lines,lines+13,[&](int l){return !(s&~l);});
   if(popcount(unsigned(s))<2)continue;
   for(int j=0;j<7;j++)if(!(s&~lines[j+6])){
      owner[s]=j;int n=0,sm=0;
      for(unsigned bits=lines[j+6];bits;bits&=bits-1,n++)if(s&(bits&-bits))sm|=1<<n;
      part[s]=tag[sm];
   }
 }
 fill(localCost,localCost+2048,40);localCost[0]=0;
 for(int s=0;s<2048;s++){
   for(int a=1;a<16;a++)if(!tag[a]||(s&tag[a])){
     for(int b=a;b;b=(b-1)&a)localCost[s|tag[b]]=min(localCost[s|tag[b]],localCost[s]+1);
     for(int b=1;b<a;b++)if(!tag[b]||(s&tag[b]))localCost[s|tag[a|b]]=min(localCost[s|tag[a|b]],localCost[s]+1);
   }
 }
 for(int s=2047;s>=0;s--)for(int i=0;i<11;i++)localCost[s]=min(localCost[s],localCost[s|1<<i]);
 for(int a=1;a<8192;a++)if(!ext[a])for(int b=1;b<=a;b++)if(!ext[b]&&ext[a|b]){
    operands[a|b].push_back(a);operands[a|b].push_back(b);
 }
}
bool possible(const array<int,11>& f,int bound,const array<int,7>& floor,int budget){
 int need[7]{},unc=0,reqExt=0,em=0;
 auto insert=[&](int m){if(prim[m])return;if(owner[m]>=0)need[owner[m]]|=part[m];else if(ext[m]){++reqExt;em=m;}else ++unc;};
 for(int i=0;i<11;i++)if(f[i]&&(!i||f[i-1]!=f[i]))insert(f[i]);
 auto special=[&](int a){return !prim[a]&&owner[a]<0&&find(f.begin(),f.end(),a)==f.end();};
 int slack=budget-bound;
 for(int h=reqExt;h<=slack;h++){
   if(h+unc>slack)continue;
   int base=h+unc,save[7]{};
   for(int t=0;t<7;t++){
     int c=max(floor[t],localCost[need[t]]);
     base+=c;
     save[t]=c-max(floor[t],popcount(unsigned(need[t])));
   }
   sort(save,save+7,greater<int>());
   for(int i=0;i<min(7,h*(h-1)/2);i++)base-=save[i];
   if(base>budget)continue;
   if(h!=1||reqExt!=1)return true;
   for(int i=0;i<int(operands[em].size());i+=2){
      int a=operands[em][i],b=operands[em][i+1];
      int u=unc+special(a)+special(b);
      if(u+h>slack)continue;
      int v=h+u;
      for(int t=0;t<7;t++){
         int ns=need[t]|(owner[a]==t?part[a]:0)|(owner[b]==t?part[b]:0);
         v+=max(floor[t],localCost[ns]);
      }
      if(v<=budget)return true;
   }
 }
 return false;
}
