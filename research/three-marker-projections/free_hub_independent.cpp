#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
#include <numeric>
#include <set>
#include <vector>
using namespace std;
using Perm = array<int,12>;
using Part = vector<int>;
int length1,length2,all,eligible,best;
Perm labels,perm0,physical[81];
bool exceptional[81];
int gate[81][12];

struct Dsu {
    Perm p;
    Dsu(){iota(p.begin(),p.end(),0);}
    int root(int x){while(x!=p[x])x=p[x];return x;}
    void unite(int x,int y){p[root(x)]=root(y);}
};
bool connected(int word,const Part& hubs,int r,int s){
    Dsu d;
    for(int i=0;i<12;++i)d.unite(i,physical[word][i]);
    for(int block:hubs)for(int i=0;i<12;++i)if(block>>i&1)d.unite(i,__builtin_ctz(block));
    return d.root(r)==d.root(s);
}
void evaluate(int r,int s,int rcycle){
    ++all;
    vector<Part> alternatives;
    for(int word=0;word<81;++word)if(exceptional[word]){
        Dsu d;
        for(int i=0;i<12;++i){physical[word][i]=perm0[gate[word][i]];d.unite(i,physical[word][i]);}
        if(d.root(r)==d.root(s))return;
        if(word==0)continue;
        Part masks(12);
        for(int i=0;i<12;++i)masks[d.root(i)]|=1<<i;
        Part choices{masks[d.root(r)]};
        for(int i=0;i<12;++i)if(masks[i]&&i!=d.root(r)&&i!=d.root(s)){
            int n=choices.size();
            for(int j=0;j<n;++j)choices.push_back(choices[j]|masks[i]);
        }
        alternatives.push_back(choices);
    }
    ++eligible;
    for(int word=0;word<81;++word)if(!exceptional[word])
        for(int i=0;i<12;++i)physical[word][i]=perm0[gate[word][i]];
    sort(alternatives.begin(),alternatives.end(),[](auto &a,auto &b){return a.size()<b.size();});
    set<Part> partitions{{rcycle,4095^rcycle}};
    for(auto &cuts:alternatives){
        set<Part> next;
        for(const Part &part:partitions)for(int cut:cuts){
            Part child;
            for(int block:part){if(block&cut)child.push_back(block&cut);if(block&~cut)child.push_back(block&~cut);}
            sort(child.begin(),child.end());
            next.insert(child);
        }
        partitions=move(next);
    }
    for(const Part &part:partitions){
        int count=0;
        for(int w=0;w<81;++w)if(!exceptional[w])count+=connected(w,part,r,s);
        best=max(best,count);
    }
}
void label_sockets(){
    int l=length1+length2, firstrepeat=-1,seen=0;
    for(int j=0;j<l;++j){if(seen>>labels[j]&1){firstrepeat=labels[j];break;}seen|=1<<labels[j];}
    for(int signs=0;signs<16;++signs)if(!(signs>>firstrepeat&1)){
        int cnt[4]={},sockets[12],used=0,rcycle=0;
        for(int j=0;j<l;++j){int g=labels[j],k=cnt[g]++;int digit=(signs>>g&1)?(3-k)%3:k;
            sockets[j]=3*g+digit;used|=1<<sockets[j];if(j<length1)rcycle|=1<<sockets[j];}
        for(int j=0;j<l;++j)perm0[sockets[j]]=sockets[j==length1-1?0:(j==l-1?length1:j+1)];
        Part rest;
        for(int k=0;k<12;++k)if(!(used>>k&1))rest.push_back(k);
        Part images=rest;
        do{for(int k=0;k<(int)rest.size();++k)perm0[rest[k]]=images[k];evaluate(sockets[0],sockets[length1],rcycle);}
        while(next_permutation(images.begin(),images.end()));
    }
}
void make_words(int at,int appeared,int secondmask,array<int,4> cnt){
    if(at==length1&&appeared!=4)return;
    if(at==length1+length2){if(secondmask==15)label_sockets();return;}
    for(int g=0;g<4;++g){
        if(at<length1&&(g>appeared||cnt[g]>=2))continue;
        if(cnt[g]==3)continue;
        labels[at]=g;cnt[g]++;
        make_words(at+1,max(appeared,g+1),at<length1?0:secondmask|(1<<g),cnt);
        cnt[g]--;
    }
}
int main(int argc,char **argv){
    length1=atoi(argv[1]);length2=atoi(argv[2]);
    for(int w=0;w<81;++w){int t=w,z[4];for(int i=3;i>=0;--i){z[i]=t%3;t/=3;}
        exceptional[w]=(z[0]+z[2]+z[3])%3==0&&(z[1]+z[2]+3-z[3])%3==0;
        for(int i=0;i<12;++i)gate[w][i]=3*(i/3)+(i%3+z[i/3])%3;}
    make_words(0,0,0,{});printf("%d %d %d %d %d\n",length1,length2,all,eligible,best);
}
