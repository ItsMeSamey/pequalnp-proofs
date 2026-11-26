#include <algorithm>
#include <array>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
struct Partner {int m;array<unsigned char,13> pos,neg,charge;};
int s,rest,buckets,dirty,whole;array<int,13> raw;vector<Partner> opts[3];const Partner* choice[3];
long long total,good;
void search(int j){
 if(j<buckets){for(auto& v:opts[j]){choice[j]=&v;search(j+1);}return;}
 ++total;int mass[16]={};
 for(int i=0;i<13;i++){
  int yes=0,no=0,cap=2+(raw[i]&3);
  for(int b=0;b<buckets;b++){auto v=choice[b];yes|=v->pos[i];no|=v->neg[i];cap-=v->charge[i];}
  if(cap<0)return;
  int weight=1<<(rest-min(rest,cap)),free=((1<<s)-1)^(yes|no);
  for(int t=free;;t=(t-1)&free){if((mass[t|yes]+=weight)>(1<<rest))return;if(!t)break;}
 }
 ++good;
}
int main(int argc,char** argv){
 s=atoi(argv[1]);rest=7-s;dirty=atoi(argv[2]);whole=atoi(argv[3]);buckets=whole?1:s-1;int id=0;
 while(cin>>raw[0]){
  for(int i=1;i<13;i++)cin>>raw[i];int U[4]={};
  for(int j=0;j<s;j++)for(int i=0;i<13;i++)if(raw[i]>>(2+j)&1)U[j]|=1<<i;
  for(int b=0;b<buckets;b++){
   opts[b].clear();int first=b?b+1:0,last=whole?s-1:(b?b+1:1);
   for(int m=1;m<8192;m++){
    bool valid=true;
    for(int k=first;k<=last;k++)
     if(popcount(unsigned(U[k]&m))!=((dirty>>k)&1) || popcount(unsigned(m&~U[k]))<3)valid=false;
    if(!valid)continue;
    Partner a{};a.m=m;
    for(int i=0;i<13;i++){
     int on=m>>i&1;int debit=0;
     for(int k=first;k<=last;k++){
      int u=U[k]>>i&1;
      if(u&&!on)a.pos[i]|=1<<k;
      if(on&&!u)a.neg[i]|=1<<k;
      debit+=u|on;
     }
     a.charge[i]=debit-(whole?2:1)*on;
    }
    opts[b].push_back(a);
   }
  }
  total=good=0;search(0);cout<<id++<<" "<<total<<" "<<good<<endl;
 }
}
