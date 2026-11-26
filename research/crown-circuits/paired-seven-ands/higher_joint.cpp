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
 int d=req.size(),n=0;vector<int> base;for(int i=0;i<d;i++)base.push_back(1<<i);
 for(int j=0;j<14;j++){int m=0;for(int i=0;i<d;i++)if(req[i]>>j&1)m|=1<<i;
  if(!m)continue;++n;if(find(base.begin(),base.end(),m)==base.end())base.push_back(m);}
 int spare=budget+d-n-(int(base.size())-d);if(spare!=0)return spare>0;
 for(int m:base)if(wt(m)>1){bool ok=false;
  for(int a:base)if(a!=m&&!(a&~m))for(int b:base)if(b!=m&&(a|b)==m){ok=true;break;}
  if(!ok)return false;
 }return true;
}
int main(int argc,char**argv){
 if(argc<3)return 2;int d=atoi(argv[1]);ifstream in(argv[2]);int id,c,cap;
 while(in>>id>>c>>cap){vector<int> t(d);for(auto&x:t)in>>x;
  if(cap<12)continue;
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
  if(any_of(hard.begin(),hard.end(),[](const auto&v){return v.empty();}))continue;
  vector<int> order(d);for(int j=0;j<d;j++)order[j]=j;
  sort(order.begin(),order.end(),[&](int a,int b){return pair(hard[a].size(),a)<pair(hard[b].size(),b);});
  long long roots=0,leaves=0;vector<int> chosen;int lead=order[0];
  auto complete=[&](auto&& self,int step)->bool{
   if(step==d){++leaves;return true;}
   for(int m:hard[order[step]]){
    if(find(chosen.begin(),chosen.end(),m)!=chosen.end()){if(self(self,step+1))return true;continue;}
    if(any_of(chosen.begin(),chosen.end(),[&](int n){return (z[m]&z[n])!=0;}))continue;
    chosen.push_back(m);vector<int> req=t;req.insert(req.end(),chosen.begin(),chosen.end());
    bool ok=cut(req,5+chosen.size())&&self(self,step+1);chosen.pop_back();if(ok)return true;
   }return false;
  };
  for(int m:hard[lead]){chosen={m};if(complete(complete,1)){++roots;}}
  cout<<id<<" "<<c<<" "<<cap<<" "<<lead<<" "<<hard[lead].size()<<" "<<roots<<" "<<leaves<<endl;
 }
}
