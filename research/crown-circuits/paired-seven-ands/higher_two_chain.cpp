#define TRIPLE_NO_MAIN
#include "three_saturated.cpp"
vector<vector<int>> pureLibraries(const vector<int>&t){
 set<int> required,possible;for(int m:t)if(wt(m)>1){required.insert(m);for(int p=m;p;p=(p-1)&m)if(wt(p)>1)possible.insert(p);}
 vector<int> optional;for(int p:possible)if(!required.count(p))optional.push_back(p);
 vector<int> cur(required.begin(),required.end());vector<vector<int>> result;
 auto rec=[&](auto&&self,int start)->void{
  if(cur.size()==3){auto ordered=cur;sort(ordered.begin(),ordered.end(),[](int x,int y){return pair(wt(x),x)<pair(wt(y),y);});
   vector<int>b;for(int i=0;i<14;i++)b.push_back(1<<i);for(int m:ordered){bool ok=false;for(int a:b)for(int z:b)if((a|z)==m)ok=true;if(!ok)return;b.push_back(m);}
   result.push_back(ordered);return;}
  for(int i=start;i<int(optional.size());i++){cur.push_back(optional[i]);self(self,i+1);cur.pop_back();}
 };rec(rec,0);return result;
}
int main(int argc,char**argv){
 if(argc<3)return 2;int d=atoi(argv[1]);ifstream in(argv[2]);int id,c,cap;
 while(in>>id>>c>>cap){vector<int>t(d);int used=0;for(int&x:t){in>>x;used|=x;}if(c!=3||cap<12)continue;
  vector<int>e;for(int j=0;j<d;j++)if(!(used&(3<<(2*j))))e.push_back(j);
  if(e.size()!=2)continue;int A=e[0],B=e[1],pa=3<<(2*A),pb=3<<(2*B);
  Search s(0,5,"/dev/null",false);s.z[0]=~U(0);
  for(int state=0;state<128;state++){int m=0;for(int j=6;j>=0;j--)if(j>=d||(m&t[j]))m|=1<<(2*j+(state>>j&1));
   for(int j=0;j<14;j++)if(!(m>>j&1))s.z[1<<j]|=U(1)<<state;}
  for(int m=1;m<16384;m++)if(wt(m)>1)s.z[m]=s.z[m&(m-1)]&s.z[m&-m];
  long long libs=0,rootPairs=0,volume=0,hits=0;
  for(auto&pure:pureLibraries(t)){
   s.bank.resize(14);s.bank.insert(s.bank.end(),pure.begin(),pure.end());vector<int> opts;
   for(int p:s.bank)if(!(p&(pa|pb)))opts.push_back(p);
   int H=(1<<(2*A))|(1<<(2*B));
   for(int p:opts){int G=H|p,ka=G|pa,kb=G|pb;U za=s.z[ka],zb=s.z[kb];
    if(!za||!zb||(za&zb))continue;++libs;
    bool soft=false;for(int j:{A,B}){U z=j==A?za:zb;
     for(int w:opts){U v=s.z[w|t[j]];if(v&&!(v&~z)){soft=true;break;}}}
    if(soft)continue;++rootPairs;
    s.bank.push_back(H);s.bank.push_back(G);auto raw=s.choices();s.bank.pop_back();s.bank.pop_back();
    U blocked=za|zb;vector<U> events;for(int m:raw)if(wt(m)>1&&!(s.z[m]&blocked))events.push_back(s.z[m]);
    sort(events.begin(),events.end(),[](U x,U y){return pc(x)!=pc(y)?pc(x)<pc(y):x<y;});vector<U> v;
    for(U x:events)if(none_of(v.begin(),v.end(),[&](U y){return !(y&~x);}))v.push_back(x);
    if(v.size()<10)continue;int vol=pc(blocked);for(int j=0;j<10;j++)vol+=pc(v[j]);if(vol>128)continue;
    ++volume;if(s.pack(v,0,10,blocked))++hits;
   }
  }
  cout<<id<<" "<<libs<<" "<<rootPairs<<" "<<volume<<" "<<hits<<endl;
 }
}
