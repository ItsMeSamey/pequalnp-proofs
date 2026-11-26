#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <vector>
using namespace std;
using Mask = uint32_t;
using State = vector<Mask>;
using Triple = array<int,3>;
struct Option {Mask first,second; int cost;};

vector<Option> library(int b, const vector<Mask>& upset){
    State free{0,upset[0]};
    for(int i=0;i<b;i++)free.push_back(upset[1<<i]);
    sort(free.begin(),free.end());
    set<State> states{free};
    map<pair<Mask,Mask>,int> costs;
    for(int depth=0;depth<=b+1;depth++){
        set<State> following;
        for(auto& state:states){
            for(auto a:state)for(auto z:state)costs.try_emplace({a,z},depth);
            if(depth==b+1)continue;
            for(auto a:state)for(auto z:state)if(a<z)for(auto v:{a|z,a&z}){
                auto here=lower_bound(state.begin(),state.end(),v);
                if(here!=state.end()&&*here==v)continue;
                State next=state;next.insert(next.begin()+(here-state.begin()),v);
                following.insert(move(next));
            }
        }
        states=move(following);
    }
    vector<Option> out;
    for(auto [key,cost]:costs)out.push_back({key.first,key.second,cost});
    return out;
}

int rawRepairs(Mask output,int common,Triple points){
    if(!output)return 3;  // Direct four-point raw union.
    int misses=1-int(output>>common&1);
    for(int p:points)misses+=1-int(output>>p&1);
    return misses;
}

int main(){
    for(int b=0;b<=4;b++){
        const int n=1<<b;
        vector<Mask> up(n);
        for(int x=0;x<n;x++)for(int y=0;y<n;y++)if(!(x&~y))up[x]|=Mask(1)<<y;
        auto choices=library(b,up);
        vector<Triple> triples;
        for(int i=0;i<n;i++)for(int j=i;j<n;j++)for(int k=j;k<n;k++)triples.push_back({i,j,k});
        set<pair<Mask,Mask>> possible;
        int count=0,unresolved=0;
        for(int c=0;c<n;c++)for(auto x:triples)for(auto y:triples){
            Mask aa=up[c]|up[x[0]]|up[x[1]]|up[x[2]];
            Mask bb=up[c]|up[y[0]]|up[y[1]]|up[y[2]];
            if(aa>bb)continue; // The marker property is symmetric.
            bool consistent=true;
            for(int p:x)if(bb>>p&1)consistent=false;
            for(int p:y)if(aa>>p&1)consistent=false;
            if(!consistent)continue;
            ++count;possible.emplace(aa,bb);
            Mask upperA=0,upperB=0;
            for(int p=0;p<n;p++){
                int first=0,second=0;
                for(int v:y)first+=aa>>(v|p)&1;
                for(int v:x)second+=bb>>(v|p)&1;
                if(first>=2)upperA|=Mask(1)<<p;
                if(second>=2)upperB|=Mask(1)<<p;
            }
            bool found=false;
            for(auto [h,g,d]:choices){
                if((h&~upperA)||(g&~upperB))continue;
                if(d+rawRepairs(h,c,x)+rawRepairs(g,c,y)<=b+1){found=true;break;}
            }
            if(!found)++unresolved;
        }
        cout<<b<<' '<<possible.size()<<' '<<count<<' '<<unresolved<<'\n';
        if(unresolved)return 1;
    }
}
