#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <vector>
using namespace std;
struct Rel {int p,n;vector<int> pairs;};
struct Trigger {int p=0,n=0;};
#include "geom.hpp"
int main(int argc,char** argv){
 if(argc!=5)return 1; geometry();
 bool repeated=stoi(argv[4]);
 vector<Rel> rows;ifstream rf(argv[1]),bases(argv[2]);ofstream out(argv[3]);
 int p,n;while(rf>>p>>n){
    Rel r{p,n,{}};
    for(int i=0;i<13;i++)for(int j=0;j<i;j++)if((n>>i&1)&&(n>>j&1))r.pairs.push_back(13*i+j);
    rows.push_back(r);
 }
 assert(rows.size()==2961);
 int targets[7]{};
 bool allowed[8192]{}, primitive[8192]{};
 for(int i=0;i<13;i++)allowed[1<<i]=true;
 for(int i=0;i<6;i++){
   auto at=[&](int d){return 1<<((i+d)%13);};
   allowed[at(0)|at(1)]=allowed[at(3)|at(9)]=allowed[at(0)|at(1)|at(3)|at(9)]=true;
 }
 copy(begin(allowed),end(allowed),begin(primitive));
 for(int l=0;l<7;l++){
   for(int d:{0,1,3,9})targets[l]|=1<<((l+6+d)%13);
   for(int z=targets[l];z;z=(z-1)&targets[l])allowed[z]=true;
 }
 long long hist[22]{}, eqkeep=0,originalEq=0,basecount=0, total=0;
 array<int,9> f;
 while(bases>>f[0]){
   for(int i=1;i<9;i++)bases>>f[i];
   ++basecount;
   Trigger trigger[9][169]{};
   for(auto &r:rows){
     int only=-1;
     for(int i=0;i<9;i++)if((f[i]&r.p)&&!(f[i]&r.n)){if(only!=-1){only=-2;break;}only=i;}
     assert(only!=-1);
     if(only<0)continue;
     for(int k:r.pairs){trigger[only][k].p|=r.p;trigger[only][k].n|=r.n;}
   }
   short loss[8192]{}; int viable=0;
   for(int i=0;i<9;i++){
     if(popcount(unsigned(f[i]))<2)continue;
     for(int t:targets)if(!(f[i]&~t)){
       bool safe=true; set<pair<int,int>> unique;
       for(int a=0;a<13;a++)for(int b=0;b<a;b++)if(!(t&((1<<a)|(1<<b)))){
         auto [req,avoid]=trigger[i][13*a+b];
         if(!req)safe=false;
         else if(!(req&avoid))unique.emplace(req,avoid);
       }
       if(!safe)continue;
       viable|=1<<i;
       for(auto [req,avoid]:unique){
         int free=8191&~(req|avoid), sub=free;
         for(;;){loss[sub|req]|=1<<i;if(!sub)break;sub=(sub-1)&free;}
       }
     }
   }
   array<array<int,7>,512> floors{}; int cache[512];fill(begin(cache),end(cache),-1);
   for(int x=0;x<=8191;x++){
     bool nonDistinct=!x || find(f.begin(),f.end(),x)!=f.end();
     if(nonDistinct!=repeated)continue;
     int keep=viable&~loss[x],&bound=cache[keep];
     if(bound==-1){
       int extra=0;
       for(int tj=0;tj<7;tj++){int t=targets[tj];
         vector<int> masks;
         for(int i=0;i<9;i++)if((keep>>i&1)&&!(f[i]&~t))masks.push_back(f[i]);
         int cost=4;
         for(int s=1;s<(1<<masks.size());s++){
            int covered=0;
            for(unsigned m=s;m;m&=m-1)covered|=masks[countr_zero(m)];
            cost=min(cost,popcount(unsigned(s))+popcount(unsigned(t&~covered)));
         }
         floors[keep][tj]=4-cost;extra+=cost-1;
       }
       bound=21-extra;
     }
     hist[bound]++;total++;
     if(bound<=16 && (bound!=16 || (allowed[x] && all_of(f.begin(),f.end(),[&](int m){return allowed[m];})))){
       if(bound==16){
         originalEq++;
         bool ok=true; int need=0;
         vector<int> all(f.begin(),f.end());if(find(all.begin(),all.end(),x)==all.end())all.push_back(x);
         for(int t:targets){
            for(int a:all)if(!primitive[a] && !(a&~t)){
                bool below=false;
                for(int b:all)if(!primitive[b] && a!=b && !(b&~t)){
                    if((a&b) && (a&~b) && (b&~a))ok=false;
                    if(!(a&~b))below=true;
                }
                if(!below)need+=popcount(unsigned(a))-1;
            }
         }
         if(!ok || need>16) continue;
         eqkeep++;
       }
       if(x && bound>=14&&!possible(f,x,bound,floors[keep]))continue;
       for(int m:f)out<<m<<' ';out<<x<<' '<<bound<<'\n';
     }
   }
 }
 cerr<<basecount<<" bases "<<total<<" augmentations\n";
 for(int i=0;i<22;i++)if(hist[i])cerr<<i<<' '<<hist[i]<<'\n';
 cerr<<"equality survivors "<<eqkeep<<" before laminarity "<<originalEq<<'\n';
}
