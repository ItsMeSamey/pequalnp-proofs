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
 if(argc<4)return 2;int d=atoi(argv[1]),want=atoi(argv[3]);ifstream in(argv[2]);int id,c,cap;
 while(in>>id>>c>>cap){vector<int>t(d);int used=0;for(int&x:t){in>>x;used|=x;}if(c!=1||cap<12)continue;
  vector<int>e;for(int j=0;j<d;j++)if(!(used&(3<<(2*j))))e.push_back(j);
  if(int(e.size())!=want)continue;
  Search s(0,5,"/dev/null",false);s.z[0]=~U(0);
  for(int state=0;state<128;state++){int m=0;for(int j=6;j>=0;j--)if(j>=d||(m&t[j]))m|=1<<(2*j+(state>>j&1));
   for(int j=0;j<14;j++)if(!(m>>j&1))s.z[1<<j]|=U(1)<<state;}
  for(int m=1;m<16384;m++)if(wt(m)>1)s.z[m]=s.z[m&(m-1)]&s.z[m&-m];
  long long libs=0,rootPairs=0,volume=0,hits=0;
  vector<int> slice;for(int j:e)slice.push_back(3<<(2*j));
  vector<int> initial;for(int m:t)if(wt(m)>1&&find(initial.begin(),initial.end(),m)==initial.end())initial.push_back(m);
  if(initial.size()!=1||wt(initial[0])!=2)return 3;
  vector<vector<int>> pureSet;
  s.bank.resize(14);s.bank.push_back(initial[0]);vector<int> current=initial;
  auto extras=[&](auto&&self,int last)->void{
   if(want>2*(4-int(current.size())))return;
   pureSet.push_back(current);if(current.size()==3)return;
   auto next=s.choices();for(int m:next){int rank=wt(m)*16384+m;
    if(wt(m)<2||rank<=last||find(s.bank.begin(),s.bank.end(),m)!=s.bank.end()||
       any_of(slice.begin(),slice.end(),[&](int p){return bool(p&m);}))continue;
    current.push_back(m);s.bank.push_back(m);self(self,rank);s.bank.pop_back();current.pop_back();
   }
  };extras(extras,0);
  for(auto&pure:pureSet){
   s.bank.resize(14);s.bank.insert(s.bank.end(),pure.begin(),pure.end());vector<int> active;
   auto visit=[&](auto&&self,int last)->void{
    int k=active.size(),unused=5-pure.size()-k,mask=0;vector<int> count(want);
    for(int m:active){mask|=m;for(int j=0;j<want;j++)count[j]+=!!(m&slice[j]);}
    if(any_of(count.begin(),count.end(),[&](int v){return v+unused<2;}))return;
    int uncovered=0;for(int p:slice){int sides=0;for(int h:active)if((h&p)!=p)sides|=h&p;uncovered+=wt(p&~sides);}
    if(uncovered>2*unused)return;
    auto raw=s.choices();
    if(unused){for(int m:raw){if(wt(m)<=1||find(s.bank.begin(),s.bank.end(),m)!=s.bank.end())continue;
      int rank=wt(m)*16384+m;if(rank<=last)continue;bool tagged=false,ok=true;
      for(int j=0;j<want;j++)if(m&slice[j]){
       tagged=true;if(!(mask&slice[j])&&((m&slice[j])==(2<<(2*e[j])))){ok=false;break;}}
      if(!tagged||!ok)continue;s.bank.push_back(m);active.push_back(m);self(self,rank);active.pop_back();s.bank.pop_back();
     }if(k<2||uncovered||any_of(count.begin(),count.end(),[](int x){return x<2;}))return;}
    ++libs;vector<vector<int>> roots(want);
    for(int i=0;i<want;i++){int n=e[i],p=slice[i];vector<U> rep{s.z[t[n]]};
     for(int x:s.bank)if(!(x&p)&&s.z[t[n]|x])rep.push_back(s.z[t[n]|x]);
     for(int m:raw)if((m&p)==p&&wt(m&~(p|t[n]))>=2&&none_of(rep.begin(),rep.end(),[&](U a){return !(a&~s.z[m]);}))roots[i].push_back(m);
     if(roots[i].empty())return;
    }
    vector<int> witness;
    auto select=[&](auto&& step,int i,U blocked)->void{
     if(i<want){for(int m:roots[i]){if(find(witness.begin(),witness.end(),m)!=witness.end()){step(step,i+1,blocked);continue;}
       if(s.z[m]&blocked)continue;witness.push_back(m);step(step,i+1,blocked|s.z[m]);witness.pop_back();}return;}
     ++rootPairs;int need=12-witness.size();vector<U> events;for(int m:raw)if(wt(m)>1&&!(s.z[m]&blocked))events.push_back(s.z[m]);
     sort(events.begin(),events.end(),[](U x,U y){return pc(x)!=pc(y)?pc(x)<pc(y):x<y;});vector<U> v;
     for(U z:events)if(none_of(v.begin(),v.end(),[&](U x){return !(x&~z);}))v.push_back(z);
     if(int(v.size())<need)return;int vol=pc(blocked);for(int j=0;j<need;j++)vol+=pc(v[j]);if(vol>128)return;
     ++volume;if(s.pack(v,0,need,blocked))++hits;
    };select(select,0,U(0));
   };visit(visit,0);
  }
  cout<<id<<" "<<libs<<" "<<rootPairs<<" "<<volume<<" "<<hits<<endl;
 }
}
