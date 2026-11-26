#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
using PairSet = unsigned __int128;

PairSet contained_pairs(int mask) {
    PairSet result=0;
    int k=0;
    for(int i=0;i<13;i++) for(int j=0;j<i;j++,k++) {
        if((mask>>i&1) && (mask>>j&1)) result |= PairSet(1)<<k;
    }
    return result;
}
struct Relation { int positive, negative; PairSet pairs; };

int main(int argc, char **argv) {
    if(argc!=2) return 1;
    ifstream input(argv[1]);
    vector<Relation> relations;
    int positive, negative;
    while(input>>positive>>negative) relations.push_back({positive,negative,contained_pairs(negative)});
    if(relations.size()!=2961) return 1;
    array<int,9> feature{};
    while(cin>>feature[0]) {
        for(int i=1;i<9;i++) if(!(cin>>feature[i])) return 1;
        array<PairSet,9> rejected{};
        for(auto row:relations) {
            int only=-1;
            for(int i=0;i<9;i++) {
                if(!(feature[i]&row.positive) || (feature[i]&row.negative)) continue;
                if(only!=-1) { only=-2; break; }
                only=i;
            }
            if(only==-1) return 1;
            if(only>=0) rejected[only] |= row.pairs;
        }
        int extra=0;
        for(int j=0;j<7;j++) {
            int target=0;
            array<int,4> points;
            int k=0;
            for(int d:{0,1,3,9}) { points[k++]=(j+6+d)%13; target|=1<<points[k-1]; }
            PairSet outside=contained_pairs(8191^target);
            array<int,16> cost;
            for(unsigned mask=0;mask<16;mask++) cost[mask]=popcount(mask);
            for(int i=0;i<9;i++) {
                if((feature[i]&~target) || (outside&~rejected[i])) continue;
                int part=0;
                for(int p=0;p<4;p++) if(feature[i]>>points[p]&1) part|=1<<p;
                for(int mask=0;mask<16;mask++) cost[mask|part]=min(cost[mask|part],cost[mask]+1);
            }
            extra+=cost[15]-1;
        }
        for(int mask:feature) cout<<mask<<' ';
        cout<<21-extra<<'\n';
    }
}
