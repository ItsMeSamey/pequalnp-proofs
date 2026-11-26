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
  for(auto&pure:pureLibraries(t))for(int a=0;a<2;a++)for(int b=0;b<2;b++){
   int H=(1<<(2*A+a))|(1<<(2*B+b));if(!s.z[H])continue;s.bank.resize(14);s.bank.insert(s.bank.end(),pure.begin(),pure.end());s.bank.push_back(H);
   auto gen=s.choices();
   for(int q:gen)if(q!=H&&(q&pa)&&(q&pb)){
    ++libs;s.bank.push_back(q);auto raw=s.choices();
    vector<int> hard[2];
    for(int j=0;j<2;j++){int n=e[j],pair=3<<(2*n);vector<U> rep{s.z[t[n]]};for(int w:s.bank)if(!(w&pair)&&s.z[t[n]|w])rep.push_back(s.z[t[n]|w]);
     for(int m:raw)if((m&pair)==pair&&wt(m&~(pair|t[n]))>=2&&none_of(rep.begin(),rep.end(),[&](U z){return !(z&~s.z[m]);}))hard[j].push_back(m);
    }
    for(int m:hard[0])for(int n:hard[1])if(m==n||!(s.z[m]&s.z[n])){
     ++rootPairs;U blocked=s.z[m]|s.z[n];int k=12-(1+(m!=n));vector<U> events;
     for(int v:raw)if(wt(v)>1&&!(s.z[v]&blocked))events.push_back(s.z[v]);
     sort(events.begin(),events.end(),[](U x,U y){return pc(x)!=pc(y)?pc(x)<pc(y):x<y;});vector<U> minEvents;
     for(U v:events)if(none_of(minEvents.begin(),minEvents.end(),[&](U x){return !(x&~v);}))minEvents.push_back(v);
     if(int(minEvents.size())<k)continue;int tot=pc(blocked);for(int i=0;i<k;i++)tot+=pc(minEvents[i]);if(tot>128)continue;++volume;
     if(s.pack(minEvents,0,k,blocked))++hits;
    }
    s.bank.pop_back();
   }
  }
  cout<<id<<" "<<libs<<" "<<rootPairs<<" "<<volume<<" "<<hits<<endl;
 }
}
