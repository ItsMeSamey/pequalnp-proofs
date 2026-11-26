#define main scan_main
#include "one_dirty.cpp"
#undef main
using Top=pair<int,int>;
vector<Top> tops(){
 set<Top> result;
 auto canon=[](int a,int b){vector<pair<int,int>> c;
  for(int j=2;j<7;j++){int x=a>>(2*j)&3,y=b>>(2*j)&3;
   if(x==2||(!x&&y==2)){x=(x>>1)|((x&1)<<1);y=(y>>1)|((y&1)<<1);}c.push_back({x,y});}
  sort(c.begin(),c.end());int x=a&15,y=0;for(int j=0;j<5;j++){x|=c[j].first<<(4+2*j);y|=c[j].second<<(4+2*j);}return Top{x,y};};
 vector<int> masks;for(int a=0;a<16384;a+=16)if(!(a&(a>>1)&0x1555))masks.push_back(a);
 for(int dep:{0,4,12})for(int a:masks)for(int b:masks){
  if(!b||(!a&&!dep))continue;if(dep==12&&((a|b)&((a|b)>>1)&0x1555))continue;
  Top t=canon(a|dep,b);if(!dep)t=min(t,canon(b,a));result.insert(t);}
 return {result.begin(),result.end()};
}
struct Double:Search{
 Top top;
 Double(Top t,int h,const char*path):Search(0,h,path,false),top(t){
  z[0]=~U(0);
  for(int j=0;j<14;j++){int bit=1<<j;
   for(int s=0;s<128;s++){int x=bit;if(x&(1<<(s&1)))x|=t.first;if(x&(1<<(2+(s>>1&1))))x|=t.second;
    bool on=false;for(int a=2;a<7;a++)if(x&(1<<(2*a+(s>>a&1)))){on=true;break;}if(!on)z[bit]|=U(1)<<s;}}
  for(int m=1;m<16384;m++)if(wt(m)>1)z[m]=z[m&-m]&z[m&(m-1)];
 }
 Key doubleKey(){
  int n=chain.size();vector<int> order(n);iota(order.begin(),order.end(),0);Key best;best.fill(65535);
  do{
   bool ordered=true;for(int i=1;i<n;i++)if(wt(chain[order[i-1]])>wt(chain[order[i]])){ordered=false;break;}if(!ordered)continue;
   Key k{};for(int j=0;j<7;j++){int x=0,y=0;int f[2]={top.first,top.second};
    for(int r=0;r<2;r++){if(f[r]>>(2*j)&1)x|=1<<r;if(f[r]>>(2*j+1)&1)y|=1<<r;}
    for(int r=0;r<n;r++){auto m=chain[order[r]];if(m>>(2*j)&1)x|=1<<(r+2);if(m>>(2*j+1)&1)y|=1<<(r+2);}
    if(x>y)swap(x,y);k[j]=(x<<(n+2))|y;}
   sort(k.begin()+2,k.end());best=min(best,k);
  }while(next_permutation(order.begin(),order.end()));return best;
 }
 void walk(){
  int k=chain.size();if(!seen[k].insert(doubleKey()).second)return;auto c=choices();
  if(possible(c)){++hits[k];if(hits[k]<100){log<<top.first<<" "<<top.second<<" "<<k;for(int m:chain)log<<" "<<m;log<<endl;}}
  if(k==H)return;for(int m:c)if(wt(m)>1&&find(bank.begin(),bank.end(),m)==bank.end()){
   bank.push_back(m);chain.push_back(m);walk();chain.pop_back();bank.pop_back();}
 }
};
#ifndef DOUBLE_NO_MAIN
int main(int argc,char**argv){
 if(argc<5)return 2;auto ts=tops();int h=atoi(argv[1]),start=atoi(argv[2]),end=min<int>(ts.size(),atoi(argv[3]));
 for(int i=start;i<end;i++){string l=string(argv[4])+to_string(i);Double s(ts[i],h,l.c_str());s.walk();
  cout<<i<<" "<<ts[i].first<<" "<<ts[i].second;for(int j=0;j<=h;j++)cout<<" "<<s.seen[j].size()<<" "<<s.volume[j]<<" "<<s.hits[j];cout<<endl;}
}

#endif
