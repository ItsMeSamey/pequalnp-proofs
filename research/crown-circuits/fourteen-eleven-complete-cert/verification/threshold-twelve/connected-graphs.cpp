#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <vector>
using Rows=std::vector<unsigned>;
using Cells=std::vector<std::vector<int>>;
std::string canon(const Rows& g,Cells parts){
    for(;;){
        Cells next;
        for(auto& cell:parts){
            std::map<std::vector<int>,std::vector<int>> split;
            for(int v:cell){
                std::vector<int> signature;
                for(auto& other:parts){int z=0;for(int w:other)z+=(g[v]>>w)&1;signature.push_back(z);}
                split[signature].push_back(v);
            }
            for(auto& [_,vs]:split)next.push_back(vs);
        }
        if(next.size()==parts.size())break;
        parts=std::move(next);
    }
    size_t k=parts.size();
    for(size_t i=0;i<parts.size();i++)if(parts[i].size()>1&&(k==parts.size()||parts[i].size()<parts[k].size()))k=i;
    if(k==parts.size()){
        std::string key;
        for(size_t i=0;i<g.size();i++)for(size_t j=i+1;j<g.size();j++)key+=char('0'+((g[parts[i][0]]>>parts[j][0])&1));
        return key;
    }
    std::string best;
    for(int v:parts[k]){
        auto refined=parts;auto& same=refined[k];
        same.erase(std::find(same.begin(),same.end(),v));
        refined.insert(refined.begin()+k,{v});
        auto code=canon(g,refined);if(best.empty()||code<best)best=code;
    }
    return best;
}
std::string key(const Rows& g){
    std::map<unsigned,std::vector<int>> by;
    for(size_t i=0;i<g.size();i++)by[std::popcount(g[i])].push_back(i);
    Cells parts;for(auto& [_,vs]:by)parts.push_back(vs);return canon(g,parts);
}
int main(){
    std::map<std::string,Rows> states{{"1",{2,1}}};
    for(int edges=2;edges<=12;edges++){
        std::map<std::string,Rows> into;
        for(auto& [_,g]:states)for(size_t i=0;i<g.size();i++)if(std::popcount(g[i])<3){
            for(size_t j=i+1;j<=g.size();j++){
                if(j<g.size()&&((g[i]>>j&1)||std::popcount(g[j])>=3))continue;
                auto c=g;if(j==g.size())c.push_back(0);c[i]|=1u<<j;c[j]|=1u<<i;
                auto tag=key(c);into.try_emplace(std::move(tag),std::move(c));
            }
        }
        states=std::move(into);std::cerr<<edges<<" "<<states.size()<<std::endl;
    }
    for(auto& [code,g]:states){std::cout<<g.size();for(auto v:g)std::cout<<" "<<v;std::cout<<"\n";}
}
