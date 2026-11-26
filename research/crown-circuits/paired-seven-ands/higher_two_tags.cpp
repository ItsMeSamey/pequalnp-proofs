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
  if(e.size()!=1)continue;int A=e[0],pa=3<<(2*A);
  Search s(0,5,"/dev/null",false);s.z[0]=~U(0);
  for(int state=0;state<128;state++){int m=0;for(int j=6;j>=0;j--)if(j>=d||(m&t[j]))m|=1<<(2*j+(state>>j&1));
   for(int j=0;j<14;j++)if(!(m>>j&1))s.z[1<<j]|=U(1)<<state;}
  for(int m=1;m<16384;m++)if(wt(m)>1)s.z[m]=s.z[m&(m-1)]&s.z[m&-m];
  long long libs=0,rootPairs=0,volume=0,hits=0;
  for(auto&pure:pureLibraries(t)){
   s.bank.resize(14);s.bank.insert(s.bank.end(),pure.begin(),pure.end());
   vector<int> opts;for(int m:s.bank)if(!(m&pa))opts.push_back(m);
   for(int p:opts)for(int q:opts){int K=pa|p|q;if(!s.z[K]||wt(K&~(pa|t[A]))<2)continue;
    bool soft=false;for(int x:opts){U z=s.z[x|t[A]];if(z&&!(z&~s.z[K]))soft=true;}if(soft)continue;
    for(int kind=0;kind<2;kind++){
     if(!kind&&p>q)continue;int h1=(1<<(2*A))|p,h2=kind?(h1|q):((2<<(2*A))|q);
     if(h1==h2||!s.z[h1]||!s.z[h2])continue;
     ++libs;s.bank.push_back(h1);s.bank.push_back(h2);auto raw=s.choices();s.bank.pop_back();s.bank.pop_back();
     U blocked=s.z[K];vector<U> events;for(int m:raw)if(wt(m)>1&&!(s.z[m]&blocked))events.push_back(s.z[m]);
     sort(events.begin(),events.end(),[](U x,U y){return pc(x)!=pc(y)?pc(x)<pc(y):x<y;});vector<U> v;
     for(U z:events)if(none_of(v.begin(),v.end(),[&](U x){return !(x&~z);}))v.push_back(z);
     if(v.size()<11)continue;++rootPairs;int total=pc(blocked);for(int j=0;j<11;j++)total+=pc(v[j]);if(total>128)continue;
     ++volume;if(s.pack(v,0,11,blocked))++hits;
    }
   }
  }
  cout<<id<<" "<<libs<<" "<<rootPairs<<" "<<volume<<" "<<hits<<endl;
 }
}
