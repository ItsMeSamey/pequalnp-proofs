#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
using U=__uint128_t;
int wt(int m){return popcount(static_cast<unsigned>(m));}
bool cut(vector<int> req,int budget){
 sort(req.begin(),req.end());req.erase(unique(req.begin(),req.end()),req.end());
 int d=req.size(),n=0,k=0;array<bool,256> avail{};
 for(int j=0;j<d;j++)avail[1<<j]=true;
 for(int j=0;j<14;j++){int p=0;for(int i=0;i<d;i++)if(req[i]>>j&1)p|=1<<i;
  if(p){++n;if(!avail[p]){avail[p]=true;++k;}}}
 int spare=budget+d-n-k;if(spare!=0)return spare>0;
 for(int x=1;x<(1<<d);x++)if(avail[x]&&wt(x)>1){
  bool ok=false;for(int a=(x-1)&x;a&&!ok;a=(a-1)&x)if(avail[a])
   for(int b=(x-1)&x;b;b=(b-1)&x)if(avail[b]&&(a|b)==x){ok=true;break;}
  if(!ok)return false;
 }return true;
}
int main(int argc,char**argv){
 if(argc<3)return 2;int d=atoi(argv[1]);ifstream in(argv[2]);int id,c,cap;
 while(in>>id>>c>>cap){vector<int> t(d);for(auto&x:t)in>>x;
  if(cap<12){cout<<id<<" "<<c<<" "<<cap<<" 0 0\n";continue;}
  array<U,16384> z{};z[0]=~U(0);
  for(int s=0;s<128;s++){int m=0;for(int j=6;j>=0;j--)if(j>=d||(m&t[j]))m|=1<<(2*j+(s>>j&1));
   for(int b=0;b<14;b++)if(!(m>>b&1))z[1<<b]|=U(1)<<s;}
  for(int m=1;m<16384;m++)if(wt(m)>1)z[m]=z[m&(m-1)]&z[m&-m];
  vector<vector<U>> repl(d);for(int j=0;j<d;j++){
   repl[j].push_back(z[t[j]]);
   for(int b=0;b<14;b++)if(z[t[j]|1<<b])repl[j].push_back(z[t[j]|1<<b]);
  }
  vector<vector<int>> hard(d);int raw=0;
  for(int m=1;m<16384;m++)if(z[m]&&wt(m)>1&&wt(m)<=7){
   if(any_of(t.begin(),t.end(),[&](int a){return !(m&~a);}))continue;
   vector<int> req=t;req.push_back(m);if(!cut(req,6))continue;++raw;
   int hot=0,x=m;for(int j=0;j<d;j++)if(((x>>(2*j))&3)==3){x|=t[j];hot|=1<<j;}
   for(int j=0;j<d;j++)if(hot>>j&1){
    if(none_of(repl[j].begin(),repl[j].end(),[&](U a){return !(a&~z[m]);}))hard[j].push_back(m);
   }
  }
  int nonempty=0;for(auto&v:hard)nonempty+=!v.empty();
  cout<<id<<" "<<c<<" "<<cap<<" "<<raw<<" "<<nonempty;
  for(auto&v:hard)cout<<" "<<v.size();cout<<endl;
 }
}
