#include <iostream>
#include <array>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <bit>
using namespace std;
using Rows=array<unsigned long long,5>;
using Sig=pair<Rows,int>;
vector<pair<int,int>> dataRows;
int P,N;
map<Sig,int> ids;vector<Sig> signs;set<vector<int>> seen;
int intern(Sig s){auto [it,ok]=ids.emplace(s,ids.size());if(ok)signs.push_back(s);return it->second;}
int atom(int side,int m){Rows x{};for(int i=0;i<P+N;i++)if((side?dataRows[i].second:dataRows[i].first)&m)x[i/64]|=1ULL<<(i%64);return intern({x,side});}
bool solve(vector<int> v){
 sort(v.begin(),v.end());if(!seen.insert(v).second)return false;
 int k=v.size(),all=(1<<k)-1;
 int rows[320]={},one[17],zero[17];fill(one,one+k,all);fill(zero,zero+k,all);
 for(int i=0;i<k;i++)for(int a=0;a<P+N;a++)rows[a]|=int((signs[v[i]].first[a/64]>>(a%64))&1)<<i;
 for(int p=0;p<P;p++)for(int n=P;n<P+N;n++){
   int w=rows[p]&~rows[n];if(!w)return false;
   if(has_single_bit(unsigned(w))){int i=countr_zero(unsigned(w));one[i]&=rows[p];zero[i]&=~rows[n];}
 }
 if(k==1)return true;
 for(int i=0;i<k;i++)for(int j=0;j<i;j++){
    if(signs[v[i]].second==signs[v[j]].second&&signs[v[i]].second!=2)continue;
    for(int op=0;op<2;op++){
        auto m=op?one:zero;
        if(!(m[i]>>j&1)||!(m[j]>>i&1))continue;
        Rows x;for(int z=0;z<5;z++)x[z]=op?signs[v[i]].first[z]&signs[v[j]].first[z]:signs[v[i]].first[z]|signs[v[j]].first[z];
        auto t=v;t.erase(t.begin()+i);t.erase(t.begin()+j);t.push_back(intern({x,2}));if(solve(t))return true;
    }
 }
 return false;
}
int main(){cin>>P>>N;for(int i=0;i<P+N;i++){int p,l;cin>>p>>l;dataRows.push_back({p,l});}int first,caseNo=0;while(cin>>first){ids.clear();signs.clear();seen.clear();vector<int> v={atom(0,first)};for(int i=1;i<9;i++){int m;cin>>m;v.push_back(atom(0,m));}for(int i=0;i<7;i++)v.push_back(atom(1,1<<i));int m;cin>>m;v.push_back(atom(1,m));bool sat=solve(v);cout<<caseNo++<<" "<<m<<" "<<sat<<" "<<seen.size()<<endl;}}
