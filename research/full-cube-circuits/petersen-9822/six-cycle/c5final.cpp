#include <algorithm>
#include <cassert>
#include <iostream>
#include <vector>
using namespace std;using U=unsigned;using V=vector<U>;
V add(const V&b,U h){V c=b;for(auto x:b)c.push_back(x&h);sort(c.begin(),c.end());c.erase(unique(c.begin(),c.end()),c.end());return c;}
V ops(const V& b){V c;for(auto x:b){c.push_back(~x);for(auto y:b)if(x<y)c.push_back(x|y);}sort(c.begin(),c.end());c.erase(unique(c.begin(),c.end()),c.end());c.erase(remove_if(c.begin(),c.end(),[&](U x){return binary_search(b.begin(),b.end(),x);}),c.end());return c;}
bool last(const V& b,U t){U g=~0u;for(U x:b)if((x&t)==t)g&=x;if(g==t)return true;for(auto x:b)if((~x&g)==t)return true;for(U x:b)if(!(x&g&~t))for(U y:b)if(!(y&g&~t)&&((x|y)&t)==t)return true;return false;}
int main(){V b;U t=0;for(int m=0;m<32;m++){U a=0;for(int x=0;x<32;x++)if((m&x)==m)a|=1u<<x;b.push_back(a);bool v=false;for(int i=0;i<5;i++)v|=(m>>i&1)&&(m>>((i+1)%5)&1);assert(v==bool(((m&1)&&(m&18))||((m&4)&&(m&10))||((m&24)==24)));if(v)t|=1u<<m;}sort(b.begin(),b.end());assert(last(b,~b[5]));assert(!last(b,t));int ct=0;
for(U h:ops(b)){V c=add(b,h);assert(!last(c,t));for(U j:ops(c)){ct++;if(last(add(c,j),t)){cout<<"SAT "<<h<<" "<<j<<endl;return 0;}}}cout<<"UNSAT "<<ct<<endl;}
