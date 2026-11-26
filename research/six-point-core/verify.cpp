// Exact monotone circuit search on the matrix emitted by decode.py.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>

using Mask = std::uint64_t;
using Negatives=Mask;
int num_inputs, num_pos, num_neg;
constexpr Mask bit(int i) { return Mask{1} << i; }
bool any(Negatives x) { return x!=0; }
Mask component(Mask vertices, const std::array<Mask,64> &edges) {
    Mask seen = 0, frontier = vertices & -vertices;
    while (frontier) {
        seen |= frontier;
        Mask neighbors = 0;
        for (; frontier; frontier &= frontier-1) neighbors |= edges[std::countr_zero(frontier)];
        frontier = neighbors & vertices & ~seen;
    }
    return seen;
}
bool compatible(Mask vertices, const std::array<Mask,64> &both, const std::array<Mask,64> &either) {
    if (!(vertices & (vertices-1))) return true;
    Mask part = component(vertices, both);
    if (part == vertices) part = component(vertices, either);
    return part != vertices && compatible(part, both, either) && compatible(vertices ^ part, both, either);
}
bool incompatible(Mask live, int slack, const std::array<unsigned,64> &pos, const std::array<Negatives,64> &neg) {
    std::array<Mask,64> conjunction{}, disjunction{}, conflict{};
    for (Mask a=live; a; a &= a-1) {
        int i=std::countr_zero(a);
        for (Mask b=a&(a-1); b; b &= b-1) {
            int j=std::countr_zero(b);
            bool p=pos[i]&pos[j];
            if (slack && !p) continue;
            bool n=any(neg[i]&neg[j]);
            if (p && n) {
                if (!slack) return true;
                conflict[i] |= bit(j);
                conflict[j] |= bit(i);
            }
            if (slack) continue;
            if (p) {conjunction[i] |= bit(j); conjunction[j] |= bit(i);}
            if (n) {disjunction[i] |= bit(j); disjunction[j] |= bit(i);}
        }
    }
    if (!slack) return !compatible(live,conjunction,disjunction);
    Mask seen=0, colors[2]={0,0};
    while (live & ~seen) {
        Mask frontier=(live & ~seen) & -(live & ~seen);
        for (int color=0; frontier; color^=1) {
            if (frontier & colors[color^1]) return true;
            colors[color] |= frontier;
            seen |= frontier;
            Mask neighbors=0;
            for (; frontier; frontier &= frontier-1) neighbors |= conflict[std::countr_zero(frontier)];
            if (neighbors & colors[color]) return true;
            frontier = neighbors & ~seen;
        }
    }
    return false;
}
bool excess[8192]{};
struct Search {
    Mask witnesses[13][64]{},constants[13]{};
    Mask positive_bits[13]{},negative_bits=0;

    bool project_gate(int a,int b,int next,bool conjunction, Mask &once,Mask &twice,Mask &thrice) {
        for(int q=0;q<13;++q) {
            Mask x=witnesses[q][a], y=witnesses[q][b];
            Mask sig=conjunction ? (((x&y)&positive_bits[q])|((x|y)&negative_bits))
                                 : (((x|y)&positive_bits[q])|((x&y)&negative_bits));
            bool reduced=true;
            if (!(sig&positive_bits[q])) sig=negative_bits;
            else if (!(sig&negative_bits)) sig=positive_bits[q];
            else {
                reduced=false;
                for(int r=0;r<next;++r) if(!(sig&~witnesses[q][r])) {
                    sig=witnesses[q][r]; reduced=true; break;
                }
            }
            witnesses[q][next]=sig;
            constants[q]=(constants[q]&~bit(next)) |
              ((sig==negative_bits || sig==positive_bits[q]) ? bit(next) : 0);
            if(!reduced)continue;
            Mask flag=bit(q);
            if(twice&flag)return false;
            if(twice&flag)thrice|=flag;
            if(once&flag)twice|=flag;
            once|=flag;
        }
        return true;
    }

    std::array<std::array<int,64>,64> perms;
    Mask symmetry=0;
    std::array<Mask, 28> positive_rows{};
    std::array<unsigned, 64> positive_columns{};
    std::array<Negatives, 64> negative_columns{};
    Negatives all_negatives{};

    bool possible(Mask live, int slack, int next = num_inputs, int previous = -1, Mask group=0, Mask used_points=0, Mask point_terms=0, Mask lines_once=0, Mask lines_twice=0, Mask line_and=0,Mask del1=0,Mask del2=0,Mask del3=0, Mask expensive=0) {
        if(previous<0)group=symmetry;
        for(int q=0;q<13;++q) {
            Mask i=bit(q);
            int spent=bool(del1&i)+bool(del2&i)+bool(del3&i);
            if(spent+std::popcount(live&constants[q])>2)return false;
        }
        if (std::popcount(live) == 1) return true;  // Conservative terminal acceptance.
        std::array<Mask, 64> and_partners;
        and_partners.fill(live);
        std::array<Negatives, 64> witnesses{};
        std::array<unsigned,64> positive_witnesses{};
        for (int p=0; p<num_pos; ++p) {
            Mask positive = positive_rows[p];
            std::array<int, 64> bits;
            std::array<Negatives, 65> prefix;
            prefix[0] = all_negatives;
            int length = 0;
            for (Mask rest = positive & live; rest; rest &= rest - 1) {
                int i = std::countr_zero(rest);
                bits[length] = i;
                prefix[length+1] = prefix[length] & negative_columns[i];
                ++length;
            }
            if (any(prefix[length])) return false; // A negative dominates this positive.
            Negatives suffix = all_negatives;
            for (int k = length; k-- > 0;) {
                int i = bits[k];
                Negatives group = prefix[k] & suffix;
                if (any(group)) {
                    // Exactly i distinguishes this positive from these negatives.
                    positive_witnesses[i] |= 1u << p;
                    and_partners[i] &= positive;
                    witnesses[i] |= group;
                }
                suffix &= negative_columns[i];
            }
        }

        if (slack <= 1 && incompatible(live, slack, positive_witnesses,witnesses)) return false;
        Mask output = bit(next);
        for (Mask right = live; right; right &= right - 1) {
            int j = std::countr_zero(right);
            for (Mask left = live & (bit(j)-1); left; left &= left - 1) {
                int i = std::countr_zero(left);
                Mask operands = bit(i) | bit(j);
                Mask stable=0,swapping=0;
                bool canonical=true;
                for(Mask g=group;g;g&=g-1) {
                    int k=std::countr_zero(g), a=perms[k][i], b=perms[k][j];
                    int lo=std::min(a,b),hi=std::max(a,b);
                    if(hi<j || (hi==j && lo<i)) {canonical=false;break;}
                    if(hi==j && lo==i) {stable|=bit(k); if(a!=i)swapping|=bit(k);}
                }
                if(!canonical)continue;
                for (bool conjunction : {false, true}) {
                    constexpr Mask points=(Mask(1)<<13)-1;
                    constexpr Mask lines=((Mask(1)<<13)-1)^points;
                    Mask point_args=operands&points, line_args=operands&lines;
                    if(conjunction && ((point_args&used_points) || (operands&point_terms) || (line_args&lines_twice)))continue;
                    if(line_args&line_and&lines_twice)continue;
                    Mask partial_retire=0;
                    for(int r:{i,j}) if(!negative_columns[r] || positive_columns[r]==(1u<<num_pos)-1)
                        partial_retire |= bit(r);
                    Mask forced_retire=partial_retire | (point_args&used_points) | (operands&point_terms) | (line_args&lines_twice);
                    if(conjunction)forced_retire|=point_args;
                    if(conjunction)forced_retire|=line_args&lines_once;
                    forced_retire|=line_args&line_and&lines_once;
                    int recipe = (j*64 + i)*2 + conjunction;
                    if (recipe <= previous) continue;
                    auto neg = conjunction ? negative_columns[i] & negative_columns[j]
                                           : negative_columns[i] | negative_columns[j];
                    auto pos = conjunction ? positive_columns[i] & positive_columns[j]
                                           : positive_columns[i] | positive_columns[j];
                    if (!pos || !any(all_negatives & ~neg)) continue;
                    Mask allowed = 0;
                    if (conjunction ? bool(and_partners[i] & bit(j))
                                    : !any(witnesses[i] & negative_columns[j])) allowed |= bit(i);
                    if (conjunction ? bool(and_partners[j] & bit(i))
                                    : !any(witnesses[j] & negative_columns[i])) allowed |= bit(j);
                    if (2-std::popcount(allowed)>slack)continue;
                    bool redundant=false;
                    for(int r=0;r<next;++r) {
                        if(!(pos&~positive_columns[r]) && !(negative_columns[r]&~neg)) {redundant=true;break;}
                    }
                    if(redundant)continue;
                    for(int rb=1;rb<=j && !redundant;++rb) {
                        for(int ra=0;ra<rb;++ra) {
                            int old=(rb*64+ra)*2;
                            if(old>=recipe)break;
                            auto pa=positive_columns[ra],pb=positive_columns[rb];
                            auto na=negative_columns[ra],nb=negative_columns[rb];
                            if(!(pos&~(pa|pb)) && !((na|nb)&~neg)) {redundant=true;break;}
                            if(old+1<recipe && !(pos&~(pa&pb)) && !((na&nb)&~neg)) {redundant=true;break;}
                        }
                    }
                    if(redundant)continue;
                    Mask c1=del1,c2=del2,c3=del3;
                    if(!project_gate(i,j,next,conjunction,c1,c2,c3))continue;
                    for (Mask retire : {operands, bit(i), bit(j), Mask{0}}) {
                        int cost = 2 - std::popcount(retire);
                        if (cost > slack || (retire & ~allowed) || (forced_retire&~retire)) continue;
                        Mask new_expensive=expensive | (conjunction ? point_args : (point_args&~retire));
                        if(excess[new_expensive])continue;
                        negative_columns[next] = neg;
                        positive_columns[next] = pos;
                        for (int p=0; p<num_pos; ++p) {
                            Mask &row=positive_rows[p];
                            bool value = conjunction ? (row & operands) == operands : bool(row & operands);
                            row = (row & ~output) | (value ? output : 0);
                        }
                        Mask nextgroup=stable;
                        if(retire==bit(i) || retire==bit(j)) {
                            nextgroup &= ~swapping;
                        }
                        if (possible((live & ~retire) | output, slack-cost, next+1, recipe,nextgroup,used_points|point_args,point_terms|((conjunction&&point_args)?output:0),lines_once|line_args,lines_twice|(lines_once&line_args),line_and|(conjunction?line_args:0),c1,c2,c3,new_expensive)) return true;
                    }
                }
            }
        }
        return false;
    }
};

int main(int argc, char **argv) {
    int budget, positives, negatives, num_cuts;
    if (!(std::cin >> budget >> num_inputs >> positives >> negatives >> num_cuts)) return 2;
    num_pos=positives;num_neg=negatives;
    if (positives>28 || negatives>63 || num_inputs+budget>63) return 2;
    Search search;
    for (int k = 0; k < positives; ++k) {
        Mask &x = search.positive_rows[k];
        if (!(std::cin >> x) || x >= bit(num_inputs)) return 2;
        for (Mask rest=x; rest; rest &= rest-1) search.positive_columns[std::countr_zero(rest)] |= 1u << k;
    }
    for (int k = 0; k < negatives; ++k) {
        Mask row;
        if (!(std::cin >> row) || row >= bit(num_inputs)) return 2;
        search.all_negatives |= bit(k);
        for (; row; row &= row-1) search.negative_columns[std::countr_zero(row)] |= bit(k);
    }
    if(num_inputs!=13 || budget!=21 || positives+negatives>63)return 2;
    search.negative_bits=((bit(negatives)-1)<<positives);
    for(int q=0;q<13;++q) {
        search.positive_bits[q]=(bit(positives)-1)^search.positive_columns[q];
        search.constants[q]=bit(q);
        for(int i=0;i<13;++i) {
            if(q==i)search.witnesses[q][i]=search.negative_bits;
            else search.witnesses[q][i]=(search.positive_columns[i]&search.positive_bits[q]) |
                    ((~search.negative_columns[i]<<positives)&search.negative_bits);
        }
    }
    Mask required=0; std::array<Mask,8192> cuts;
    for(int i=0; i<num_cuts; ++i) {
        std::cin>>cuts[i];
        if (std::has_single_bit(cuts[i])) required|=cuts[i];
    }
    int count_g;
    std::cin>>count_g;
    if(count_g<1 || count_g>63)return 2;
    for(int k=0; k<count_g; ++k) {
        for(int i=0;i<64;++i)search.perms[k][i]=i;
        for(int i=0;i<num_inputs;++i)std::cin>>search.perms[k][i];
        search.symmetry|=bit(k);
    }
    for(int u=0;u<8192;++u)for(int k=0;k<count_g;++k)for(int third:{7,10}) {
        Mask triple=bit(search.perms[k][0])|bit(search.perms[k][6])|bit(search.perms[k][third]);
        if((u&triple)==triple)excess[u]=true;
    }
    Mask opt=(bit(num_inputs)-1)^required;
    size_t tested=0;
    for(Mask e=opt;;e=(e-1)&opt) {
        Mask live=required|e;
        bool hit=std::popcount(live)<=budget+1;
        for(int k=0;hit && k<num_cuts;++k) if(!(live&cuts[k]))hit=false;
        if(hit) {
            ++tested;
            Mask bank=search.symmetry;
            for(Mask g=bank;g;g&=g-1) {
                int k=std::countr_zero(g);Mask image=0;
                for(Mask s=live;s;s&=s-1)image|=bit(search.perms[k][std::countr_zero(s)]);
                if(image!=live)search.symmetry &= ~bit(k);
            }
            if(search.possible(live,budget-std::popcount(live)+1)) {
                std::cout << "POSSIBLE "<<live<<" "<<tested<<std::endl;
                return 1;
            }
            search.symmetry=bank;
        }
        if(!e)break;
    }
    std::cout << "UNSAT "<<tested<<std::endl;
}
