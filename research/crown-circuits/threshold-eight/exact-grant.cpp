#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using M=uint64_t;using Bank=std::vector<M>;
const M FULL=~M(0);
std::array<M,6> act,half;
Bank mandatory,winning,chosen,forbidden;
std::set<Bank> visited;
int demand;
bool has(const Bank& b,M x){return std::find(b.begin(),b.end(),x)!=b.end();}
void add(Bank& b,M x){if(!has(b,x))b.push_back(x);}
bool packing(const Bank& options,unsigned first,M used,int need,Bank& picked){
    if(need==0)return true;
    for(unsigned i=first;i+need<=options.size();i++){
        M r=options[i];
        if(r&used)continue;
        picked.push_back(r);
        if(packing(options,i+1,used|r,need-1,picked))return true;
        picked.pop_back();
    }
    return false;
}
bool receivers(const Bank& available){
    Bank deficits;
    for(unsigned i=0;i<available.size();i++)for(unsigned j=0;j<i;j++){
        M r=available[i]|available[j];
        if(r!=FULL&&!has(forbidden,r))add(deficits,~r);
    }
    std::sort(deficits.begin(),deficits.end(),[](M a,M b){return std::popcount(a)!=std::popcount(b)?std::popcount(a)<std::popcount(b):a<b;});
    if(deficits.size()<unsigned(demand))return false;
    int volume=0;
    for(int i=0;i<demand;i++)volume+=std::popcount(deficits[i]);
    if(volume>64)return false;
    Bank minimal;
    for(M d:deficits)if(std::none_of(minimal.begin(),minimal.end(),[&](M e){return (d&e)==e;}))minimal.push_back(d);
    chosen.clear();
    return packing(minimal,0,0,demand,chosen);
}
bool search(const Bank& helpers){
    Bank key=helpers;std::sort(key.begin(),key.end());
    if(!visited.insert(key).second)return false;
    Bank avail{FULL};unsigned done=0;
    // Recompute all possible free releases, adjoining paid helpers only when both operands exist.
    // The caller constructed each helper from a previous available bank, so these can all be granted.
    for(M h:helpers)add(avail,h);
    for(int pass=0;pass<6;pass++)for(int i=0;i<6;i++){
        if(((done>>i)&1)||!has(avail,act[i]))continue;
        done|=1<<i;add(avail,act[i]&half[i]);add(avail,act[i]&~half[i]);
    }
    if(done==63&&receivers(avail)){winning=helpers;return true;}
    int room=3-helpers.size();
    if(room==0)return false;
    Bank missing;
    for(M h:mandatory)if(!has(helpers,h))missing.push_back(h);
    if(int(missing.size())>room)return false;
    Bank next;
    for(unsigned i=0;i<avail.size();i++)for(unsigned j=0;j<i;j++){
        M u=avail[i]|avail[j];if(has(avail,u)||u==FULL)continue;
        if(int(missing.size())==room&&!has(missing,u))continue;
        add(next,u);
    }
    for(M u:next){Bank h=helpers;h.push_back(u);if(search(h))return true;}
    return false;
}
int main(int argc,char**argv){
    demand=std::stoi(argv[1]);
    for(int i=0;i<6;i++)for(int x=0;x<64;x++)if((x>>i)&1)half[i]|=M(1)<<x;
    unsigned id;
    while(std::cin>>id>>act[0]>>act[1]>>act[2]>>act[3]>>act[4]>>act[5]){
        Bank branches;
        for(int i=0;i<6;i++){add(branches,act[i]&half[i]);add(branches,act[i]&~half[i]);}
        mandatory.clear();for(M a:act)if(a!=FULL&&!has(branches,a))add(mandatory,a);
        forbidden=branches;for(M a:mandatory)add(forbidden,a);
        visited.clear();winning.clear();chosen.clear();
        bool ok=search({});
        std::cout<<id<<" "<<visited.size()<<" "<<ok;
        if(ok){std::cout<<" helpers";for(M h:winning)std::cout<<" "<<h;std::cout<<" deficits";for(M h:chosen)std::cout<<" "<<h;}
        std::cout<<std::endl;
    }
}
