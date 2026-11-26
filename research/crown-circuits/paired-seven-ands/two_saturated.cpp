#define DOUBLE_NO_MAIN
#include "two_dirty.cpp"
#include <map>
using Trees=vector<vector<int>>;
map<int,Trees> memo;
const Trees& trees(int m){
 if(auto it=memo.find(m);it!=memo.end())return it->second;
 auto&r=memo[m];if(wt(m)==1){r.push_back({});return r;}
 for(int a=(m-1)&m;a;a=(a-1)&m){int b=m^a;if(a>b)continue;
  for(const auto&x:trees(a))for(const auto&y:trees(b)){auto v=x;v.insert(v.end(),y.begin(),y.end());v.push_back(m);r.push_back(v);}}
 return r;
}
int main(int argc,char**argv){
 if(argc<4)return 2;int t=atoi(argv[1]),start=atoi(argv[2]),end=atoi(argv[3]);auto ts=tops();end=min(end,(int)ts.size());int residual=6-t;
 for(int i=start;i<end;i++){int T=ts[i].first;if(wt(T)!=t)continue;
  Double s(ts[i],0,"/dev/null");long long roots=0,sets=0,eligible=0,hits=0;
  for(int e=4;e<16384;e+=4){if(wt(e)!=residual||(e&T))continue;int K=e|3;if(!s.z[K])continue;++roots;
   for(auto a:trees(T))for(auto b:trees(K)){++sets;s.bank.resize(14);
    s.bank.insert(s.bank.end(),a.begin(),a.end());b.pop_back();s.bank.insert(s.bank.end(),b.begin(),b.end());
    auto c=s.choices();vector<U> q;for(int m:c)if(wt(m)>1&&!(s.z[m]&s.z[K]))q.push_back(s.z[m]);
    sort(q.begin(),q.end(),[](U a,U b){return pc(a)!=pc(b)?pc(a)<pc(b):a<b;});
    vector<U> v;for(auto z:q){bool skip=false;for(auto w:v)if((z&w)==w){skip=true;break;}if(!skip)v.push_back(z);}
    if(v.size()<11)continue;int space=pc(s.z[K]);for(int j=0;j<11;j++)space+=pc(v[j]);if(space>128)continue;++eligible;
    if(s.pack(v,0,11,s.z[K])){++hits;cout<<"POSITIVE "<<i<<" "<<K<<endl;}
   }
  }cout<<i<<" "<<T<<" "<<ts[i].second<<" "<<roots<<" "<<sets<<" "<<eligible<<" "<<hits<<endl;
 }}
