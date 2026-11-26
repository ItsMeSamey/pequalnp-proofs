#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
using Word=uint64_t;
using Cover=bitset<128>;
using Profile=array<int,5>;
struct Relation{int point,mask,out;};
int b,n,ex,m,r,stars[3];
vector<Cover> cover;
vector<vector<int>> hits;
Profile chosen{};
set<Profile> saved;
void generate(Cover need,int level){
 if(level==b){
    if(need.none()){auto x=chosen;sort(x.begin(),x.begin()+b);saved.insert(x);}
    return;
 }
 if(need.none()){
    for(int f=0;f<(1<<n);f++){chosen[level]=f;generate(need,level+1);}
    return;
 }
 int next=-1;
 for(int i=0;i<m;i++)if(need[i]&&(next<0||hits[i].size()<hits[next].size()))next=i;
 for(int f:hits[next]){
    Cover after=need&~cover[f];
    if(level+1==b&&after.any())continue;
    chosen[level]=f;generate(after,level+1);
 }
}
constexpr int WORDS=8;
using Bits=array<Word,WORDS>;
int main(int argc,char**argv){
 if(argc!=4)return 1;
 b=stoi(argv[2]);if(b!=4&&b!=5)return 1;
 ifstream input(argv[1]);ofstream failures(argv[3]);
 if(!(input>>n>>ex>>m>>r)||r>WORDS*64||m>128)return 2;
 for(int& t:stars)input>>t;
 cover.resize(1<<n);hits.resize(m);Cover need;
 for(int j=0;j<m;j++){
   int p,nmask;input>>p>>nmask;need.set(j);
   for(int f=0;f<1<<n;f++)if((f>>p&1)&&!(f&nmask)){hits[j].push_back(f);cover[f].set(j);}
 }
 vector<Bits> full(1<<n);vector<Bits> outside(ex);
 for(int j=0;j<r;j++){
    int p,nmask,ext;input>>p>>nmask>>ext;int word=j/64;Word bit=Word(1)<<(j%64);
    for(int f=0;f<1<<n;f++)if((f>>p&1)&&!(f&nmask))full[f][word]|=bit;
    for(int k=0;k<ex;k++)if(ext>>k&1)outside[k][word]|=bit;
 }
 generate(need,0);
 int hist[10]{};
 for(auto fs:saved){
    int unusable=0;
    Bits repeated{},once{};
    for(int i=0;i<b;i++)for(int j=0;j<(r+63)/64;j++){
      auto v=full[fs[i]][j];repeated[j]|=once[j]&v;once[j]|=v;
    }
    for(int i=0;i<b;i++)for(int k=0;k<ex;k++){
      bool absent=false;
      for(int j=0;j<(r+63)/64;j++)if(full[fs[i]][j]&~repeated[j]&outside[k][j]){absent=true;break;}
      if(!absent){unusable|=1<<i;break;}
    }
    int cost=0;
    for(int t:stars){
      int best=3;
      for(int i=0;i<b;i++)if(!(unusable>>i&1)&&!(fs[i]&~t))
         best=min(best,__builtin_popcount(t&~fs[i]));
      cost+=best;
    }
    hist[cost]++;
    if(cost>b){for(int i=0;i<b;i++)failures<<fs[i]<<' ';failures<<cost<<'\n';}
 }
 cout<<argv[1]<<' '<<b<<' '<<saved.size();
 for(int i=0;i<10;i++)cout<<' '<<hist[i];
 cout<<'\n';
}
