#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 ifstream f(argv[1]);vector<vector<pair<int,int>>> supports(512);
 int i,p,q,common=atoi(argv[2]);while(f>>i>>p>>q)supports[i].emplace_back(p,q);
 int row=0;
 while(cin>>i){
  array<int,13> tag;for(int&v:tag)cin>>v;
  long long yes=0;
  for(auto [p,q]:supports[i]){
   array<int,13> external,own,opp,partner;
   for(int j=0;j<13;j++){
    int u=tag[j]>>4,b=tag[j]&15;
    int ps=((p>>j)&1)|(((common?p:q)>>j&1)<<1);
    external[j]=b|((u&ps)<<4);own[j]=u&~ps;opp[j]=ps&~u;partner[j]=ps;
   }
   bool ok=true;int orders=3; // Either private product can be earlier.
   for(int a=0;a<13&&ok;a++)if(popcount(unsigned(tag[a]&15))+popcount(unsigned(tag[a]>>4))==2){
    for(int b=0;b<13;b++)if(a!=b&&!((tag[a]&15)&~(tag[b]&15))){
     if(!((tag[a]>>4)&~(tag[b]>>4)&partner[b])){ok=false;break;}
     if((partner[a]&~partner[b])&1)orders&=~1;
     if((partner[a]&~partner[b])&2)orders&=~2;
    }
   }
   if(!orders)ok=false;
   for(int a=0;a<2;a++)for(int b=0;b<2;b++){int covered=0;
    for(int k=0;k<13;k++)covered+=(((a?own[k]:opp[k])&1)||((b?own[k]:opp[k])&2));
    if(covered<4)ok=false;
   }
   for(int a=0;a<13&&ok;a++)if(popcount((unsigned)(tag[a]&15))+popcount((unsigned)(tag[a]>>4))==2){
    for(int b=0;b<13;b++)if(a!=b){
     for(int k=0;k<(common?1:2);k++){
      int ignored=common?48:(16<<k);
      if((partner[a]>>k&1)&&!(partner[b]>>k&1)&&!(external[a]&~ignored&~external[b]))ok=false;
     }
     if(!ok)break;
     if(external[a]&~external[b])continue;
     if((partner[a]&~partner[b])||!(own[a]&opp[b])){ok=false;break;}
    }
   }
   bool feasible=false;
   for(int first=0;ok && first<2;first++){
    if(!(orders & (1<<first)))continue;
    array<int,13> initial;
    for(int k=0;k<13;k++){
     int branching=tag[k]&15, privateUses=tag[k]>>4;
     bool mixed=popcount(unsigned(branching))+popcount(unsigned(privateUses))<2;
     initial[k]=branching | (mixed?(1<<(6+k)):0);
    }
    bool passes=true;
    for(int a=0;a<13&&passes;a++)for(int b=a+1;b<13&&passes;b++){
     int query=initial[a]|initial[b];auto probes=initial;
     bool sharedValue=false;
     for(int step=0;step<2;step++){
      int gate=first^step, bit=1<<gate;
      bool value=true;
      for(int k=0;k<13;k++)if(!(partner[k]&bit)&&!(query&~probes[k]))value=false;
      if(common&&step)value=sharedValue;
      if(!step)sharedValue=value;
      if(value&&(((tag[a]|tag[b])>>4)&bit))query|=bit<<4;
      for(int k=0;k<13;k++)if((partner[k]&(tag[k]>>4))&bit)probes[k]|=bit<<4;
     }
     for(int k=0;k<13;k++)if(!(query&~probes[k]))passes=false;
    }
    feasible|=passes;
   }
   yes+=feasible;
   if(feasible && argc>3){
    cerr<<row<<" "<<p<<" "<<q;
    for(int t:tag)cerr<<" "<<t;
    cerr<<"\n";
   }
  }
  cout<<row++<<" "<<supports[i].size()<<" "<<yes<<endl;
 }
}
