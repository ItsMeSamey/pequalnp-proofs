#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <set>
#include <vector>
using namespace std;
int main(){
  array<int,4> perm={0,1,2,3};vector<array<int,16>> maps;
  do{for(int d=0;d<16;d++){array<int,16> m{};for(int p=0;p<16;p++){int q=d;for(int j=0;j<4;j++)q^=((p>>j)&1)<<perm[j];m[p]=q;}maps.push_back(m);}}while(next_permutation(perm.begin(),perm.end()));
  array<bool,65536> done{};vector<unsigned> sets;
  for(unsigned H=0;H<65536;H++)if(popcount(H)==5&&!done[H]){
    sets.push_back(65535^H);for(auto const& m:maps){unsigned h=0;for(int p=0;p<16;p++)if(H>>p&1)h|=1<<m[p];done[h]=true;}
  }
  array<int,256> env{};for(int e=0;e<256;e++)for(int p=0;p<16;p++)for(int j=0;j<4;j++)if(e>>(2*j+(p>>j&1))&1)env[e]|=1<<p;
  vector<int> f;for(int k=0;k<9;k++)f.push_back(1<<k); // bit 8 represents negative direct feature
  set<array<int,3>> unique;
  auto rec=[&](auto&& self)->void{
    if(f.size()<12){
      int sz=f.size();for(int a=0;a<sz;a++)for(int b=a+1;b<sz;b++){
        int u=f[a]|f[b];if(find(f.begin(),f.end(),u)!=f.end())continue;
        f.push_back(u);self(self);f.pop_back();
      }return;
    }
    array<int,3> key={f[9],f[10],f[11]};sort(key.begin(),key.end());if(!unique.insert(key).second)return;
    set<int> expressions;
    for(int i=9;i<12;i++)for(int j=0;j<i;j++){
      int x=f[i]|f[j];
      if((x&256)||env[x&255]==65535)expressions.insert(x&255);
    }
    for(unsigned S:sets){
      vector<int> opt[16];int usable=0;for(int e:expressions){
        unsigned omitted=S & ~env[e];
        if(popcount(omitted)>1)continue;
        for(int p=0;p<16;p++)if((S>>p&1)&&(!omitted||(omitted>>p&1)))opt[p].push_back(e);
        usable++;
      }
      if(usable<11)continue;
      array<int,256> owner;owner.fill(-1);bool good=true;
      for(int p=0;p<16&&good;p++)if(S>>p&1){
        array<bool,256> vis{};
        auto aug=[&](auto&& aug,int label)->bool{
          for(int e:opt[label])if(!vis[e]){vis[e]=true;if(owner[e]<0||aug(aug,owner[e])){owner[e]=label;return true;}}return false;
        };good=aug(aug,p);
      }
      if(good){
        array<int,16> local{};
        for(int p=0;p<16;p++)for(int j=0;j<4;j++)local[p]|=1<<(2*j+(p>>j&1));
        array<vector<int>,16> choices;for(int p=0;p<16;p++)choices[p]=opt[p];
        auto assign=[&](auto&& self,unsigned rem,array<vector<int>,16> const& alts)->bool{
          if(!rem)return true;
          int p=countr_zero(rem);
          for(int i=0;i<16;i++)if((rem>>i&1)&&alts[i].size()<alts[p].size())p=i;
          unsigned tail=rem^(1u<<p);
          for(int e:alts[p]){
            auto next=alts;bool ok=true;
            for(int q=0;q<16;q++)if(tail>>q&1){
              next[q].clear();
              for(auto f:alts[q])if((f&local[p]&~e)&&(e&local[q]&~f))next[q].push_back(f);
              if(next[q].empty()){ok=false;break;}
            }
            if(ok&&self(self,tail,next))return true;
          }
          return false;
        };if(assign(assign,S,choices))printf("%u %d %d %d\n",S,key[0],key[1],key[2]);
      }
    }
  };rec(rec);fprintf(stderr,"%zu relative cube shapes and %zu distinct ordered-realizable auxiliary families\n",sets.size(),unique.size());
}
