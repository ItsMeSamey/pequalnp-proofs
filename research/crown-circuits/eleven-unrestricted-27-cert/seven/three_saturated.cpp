#define main old_scan_main
#include "one_dirty.cpp"
#undef main
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
struct Triple:Search{
 Triple(const array<int,3>&t):Search(0,5,"/dev/null",false){z[0]=~U(0);for(int i=0;i<14;i++)for(int s=0;s<128;s++){
  int x=1<<i;for(int j=0;j<3;j++)if(x&(1<<(2*j+(s>>j&1))))x|=t[j];
  bool val=false;for(int j=3;j<7;j++)if(x&(1<<(2*j+(s>>j&1)))){val=true;break;}
  if(!val)z[1<<i]|=U(1)<<s;
 }for(int m=1;m<16384;m++)if(wt(m)>1)z[m]=z[m&(m-1)]&z[m&-m];}
};
#ifndef TRIPLE_NO_MAIN
int main(int argc,char**argv){
 if(argc<3)return 2;int t=atoi(argv[1]),residual=6-t;ifstream in(argv[2]);int id;array<int,3> a;
 while(in>>id>>a[0]>>a[1]>>a[2]){int T=a[0];if(wt(T)!=t)continue;
  long long roots=0,sets=0,eligible=0,hits=0;Triple s(a);
  for(int e=4;e<16384;e+=4){if(wt(e)!=residual||(e&T))continue;int K=e|3;if(!s.z[K])continue;
   bool fit=true;for(int j=1;j<=2;j++)if(wt(a[j])>1&&(a[j]&~T)&&(a[j]&~K))fit=false;
   if(!fit)continue;++roots;
   for(auto A:trees(T))for(auto B:trees(K)){s.bank.resize(14);s.bank.insert(s.bank.end(),A.begin(),A.end());
    B.pop_back();s.bank.insert(s.bank.end(),B.begin(),B.end());
    if(find(s.bank.begin(),s.bank.end(),a[1])==s.bank.end()||find(s.bank.begin(),s.bank.end(),a[2])==s.bank.end())continue;
    ++sets;auto c=s.choices();vector<U> q;for(int m:c)if(wt(m)>1&&!(s.z[m]&s.z[K]))q.push_back(s.z[m]);
    sort(q.begin(),q.end(),[](U a,U b){return pc(a)!=pc(b)?pc(a)<pc(b):a<b;});
    vector<U> v;for(auto z:q){bool skip=false;for(auto y:v)if((y&z)==y){skip=true;break;}if(!skip)v.push_back(z);}
    if(v.size()<11)continue;int vol=pc(s.z[K]);for(int j=0;j<11;j++)vol+=pc(v[j]);if(vol>128)continue;++eligible;
    if(s.pack(v,0,11,s.z[K])){++hits;cout<<"POSITIVE "<<id<<" "<<K<<endl;}
   }
  }cout<<id<<" "<<T<<" "<<a[1]<<" "<<a[2]<<" "<<roots<<" "<<sets<<" "<<eligible<<" "<<hits<<endl;
 }}

#endif
