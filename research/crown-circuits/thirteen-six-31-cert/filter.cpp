#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;using M=uint64_t;constexpr M F=~M(0);
int main(){array<M,6>u,half{};for(int p=0;p<64;p++)for(int j=0;j<6;j++)if((p>>j)&1)half[j]|=M(1)<<p;
 int id;size_t total=0,sparse=0,hotfail=0,portfail=0,pass=0;
 while(cin>>id>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]>>u[5]){total++;
 vector<M>b;for(int j=0;j<6;j++){b.push_back(u[j]&half[j]);b.push_back(u[j]&~half[j]);}
 vector<M>atoms{F};for(M p:b){vector<M> tmp;for(M a:atoms){if(p&a)tmp.push_back(p&a);if(~p&a)tmp.push_back(~p&a);}atoms.swap(tmp);}
 M reps=0;for(M a:atoms)reps|=a&-a;
 bool fail=false;for(M w:u)if(w!=F&&popcount(~w&reps)<=2)fail=true;if(fail){sparse++;continue;}
 vector<M>sources=b;for(M w:u)if(w!=F)sources.push_back(w);
 vector<M>closure{0};for(M p:b){int n=closure.size();for(int i=0;i<n;i++)closure.push_back(closure[i]|p);}
 sort(closure.begin(),closure.end());closure.erase(unique(closure.begin(),closure.end()),closure.end());
 vector<M>good;for(M a:closure)if(a!=F&&popcount(~a&reps)<=int(atoms.size())-12&&none_of(sources.begin(),sources.end(),[a](M p){return !(a&~p);}))good.push_back(a);
 for(M w:u)if(w!=F){bool hot=false;for(M a:good)if(!(w&~a)&&none_of(b.begin(),b.end(),[a,w](M p){return (p|w)!=F&&!(a&~(p|w));})){hot=true;break;}if(!hot)fail=true;}
 if(fail){hotfail++;continue;}
 for(M p:b){vector<M> mins;for(M a:good)if((a|p)==F)mins.push_back(~a);sort(mins.begin(),mins.end(),[](M a,M b){return popcount(a)<popcount(b);});
 bool pack=false;for(int i=0;i<int(mins.size())&&!pack;i++)for(int j=0;j<i&&!pack;j++)if(!(mins[i]&mins[j]))for(int k=0;k<j;k++)if(!((mins[i]|mins[j])&mins[k])){pack=true;break;}
 if(!pack){fail=true;break;}}
 if(fail){portfail++;continue;}pass++;cout<<id;for(M w:u)cout<<' '<<w;cout<<'\n';
 }
 cerr<<"rows "<<total<<" sparse "<<sparse<<" hot "<<hotfail<<" ports "<<portfail<<" passed "<<pass<<'\n';
}
