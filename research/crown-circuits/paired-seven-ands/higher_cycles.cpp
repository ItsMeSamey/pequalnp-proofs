#define TRIPLE_NO_MAIN
#include "three_saturated.cpp"
vector<vector<int>> pureLibraries(const vector<int>&t,int count){
 set<int> required,possible;for(int m:t)if(wt(m)>1){required.insert(m);for(int p=m;p;p=(p-1)&m)if(wt(p)>1)possible.insert(p);}
 vector<int> optional;for(int p:possible)if(!required.count(p))optional.push_back(p);
 vector<int> cur(required.begin(),required.end());vector<vector<int>> result;
 auto rec=[&](auto&&self,int start)->void{
  if(cur.size()==count){auto ordered=cur;sort(ordered.begin(),ordered.end(),[](int x,int y){return pair(wt(x),x)<pair(wt(y),y);});
   vector<int>b;for(int i=0;i<14;i++)b.push_back(1<<i);for(int m:ordered){bool ok=false;for(int a:b)for(int z:b)if((a|z)==m)ok=true;if(!ok)return;b.push_back(m);}
   result.push_back(ordered);return;}
  for(int i=start;i<int(optional.size());i++){cur.push_back(optional[i]);self(self,i+1);cur.pop_back();}
 };rec(rec,0);return result;
}
int main(int argc,char**argv){
 if(argc<3)return 2;int d=atoi(argv[1]);ifstream in(argv[2]);int id,c,cap;
 while(in>>id>>c>>cap){vector<int>t(d);int used=0;for(int&x:t){in>>x;used|=x;}if(c>2||cap<12)continue;
  vector<int>e;for(int j=0;j<d;j++)if(!(used&(3<<(2*j))))e.push_back(j);
  if(int(e.size())+c!=5)continue;
  Search s(0,5,"/dev/null",false);s.z[0]=~U(0);
  for(int state=0;state<128;state++){int m=0;for(int j=6;j>=0;j--)if(j>=d||(m&t[j]))m|=1<<(2*j+(state>>j&1));
   for(int j=0;j<14;j++)if(!(m>>j&1))s.z[1<<j]|=U(1)<<state;}
  for(int m=1;m<16384;m++)if(wt(m)>1)s.z[m]=s.z[m&(m-1)]&s.z[m&-m];
  long long libs=0,rootPairs=0,volume=0,hits=0;
  for(auto&pure:pureLibraries(t,c)){
   int pins=0;for(int j:e)pins|=3<<(2*j);
   vector<int> edges;
   auto match=[&](auto&& self,int left)->void{
    if(left){int x=left&-left;left^=x;
     for(int v=left;v;v&=v-1){int y=v&-v;if(countr_zero((unsigned)x)/2==countr_zero((unsigned)y)/2)continue;
      edges.push_back(x|y);self(self,left^y);edges.pop_back();}
     return;}
    ++libs;vector<int> K;U blocked=0;
    for(int j:e){int own=3<<(2*j),m=0;for(int q:edges)if(q&own)m|=q;
     int extra=m&~own;if(extra&(extra>>1)&0x1555)return;
     if(!s.z[m]||(s.z[m]&blocked))return;blocked|=s.z[m];K.push_back(m);}
    ++rootPairs;s.bank.resize(14);s.bank.insert(s.bank.end(),pure.begin(),pure.end());s.bank.insert(s.bank.end(),edges.begin(),edges.end());
    auto raw=s.choices();vector<U> events;for(int m:raw)if(wt(m)>1&&!(s.z[m]&blocked))events.push_back(s.z[m]);
    sort(events.begin(),events.end(),[](U x,U y){return pc(x)!=pc(y)?pc(x)<pc(y):x<y;});vector<U> v;
    for(U z:events)if(none_of(v.begin(),v.end(),[&](U x){return !(x&~z);}))v.push_back(z);
    int need=12-e.size();if(int(v.size())<need)return;int vol=pc(blocked);for(int j=0;j<need;j++)vol+=pc(v[j]);if(vol>128)return;
    ++volume;if(s.pack(v,0,need,blocked))++hits;
   };match(match,pins);
  }
  cout<<id<<" "<<libs<<" "<<rootPairs<<" "<<volume<<" "<<hits<<endl;
 }
}
