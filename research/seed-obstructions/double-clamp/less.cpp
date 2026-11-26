#include <array>
#include <vector>
#include <algorithm>
#include <set>
#include <fstream>
#include <iostream>
#include <cstdint>
using namespace std;
using W=uint32_t;
int main(int argc,char**argv){int n=atoi(argv[1]);set<pair<W,W>> todo;
 vector<W> start{0,~0u};for(int i=0;i<n;i++){W m=0;for(unsigned j=0;j<32;j++)if((j>>i)&1)m|=1u<<j;start.push_back(m);}sort(start.begin(),start.end());
 set<vector<W>> states{start};
 for(int d=0;d<n-1;d++){set<vector<W>> next;
 for(const auto &s:states){for(auto x:s)for(auto y:s)if(x<=y)todo.emplace(x,y);
 for(unsigned i=0;i<s.size();i++)for(unsigned j=i+1;j<s.size();j++)for(W z:{s[i]&s[j],s[i]|s[j]}){
 auto pos=lower_bound(s.begin(),s.end(),z);if(pos!=s.end()&&*pos==z)continue;
 for(W x:s)todo.insert(minmax(z,x));
 if(d<n-2){auto v=s;v.insert(v.begin()+(pos-s.begin()),z);next.insert(move(v));}
 }}
 cerr<<d<<" states "<<states.size()<<" left "<<todo.size()<<endl;states=move(next);
 }
 for(auto [x,y]:todo)cout<<x<<" "<<y<<"\n";
}
