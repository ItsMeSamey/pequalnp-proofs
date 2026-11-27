# Exact mistake capacity with limited point evaluations

One hidden member of a known set of N seeds supplies every label. On a round a fresh arbitrary Boolean function is available through point queries. A deterministic predictor can evaluate it at up to m seeds before forecasting, where m≥1. It then receives the value at the hidden seed. The mistake guarantee is worst case over finite realizable streams, regardless of their length. Preprocessing can depend on the seed domain and past information. The learner has no advance information about the values of future functions. Only evaluations of the current function count toward m.

Let C_r be the largest N permitting a guarantee of at most r mistakes. Then

    C_0 = 1
    C_r = min(2 C_(r−1) + 1, C_(r−1) + ceil(m/2)).

### A strategy and matching adversary

Maintain a set containing the true seed. At size T sample L=min(m,T) distinct members and predict their majority, breaking ties toward zero. On a correct prediction keep the set. On a mistake discard the sampled members that predicted incorrectly. The remaining size is at most

    f(T) = T − ceil(min(m,T)/2) = max(floor(T/2), T−ceil(m/2)).

At T=1 the one evaluation is always correct. Since f(T)≤C precisely when T≤min(2C+1,C+ceil(m/2)), induction gives the upper bound.

For the converse let V be the genuine set consistent with all prior labels, of size T. Answer distinct probes inside V alternately zero and one. Repeat earlier answers on repeated probes and answer probes outside V consistently. After the forecast complete the fresh table by giving every unprobed member of V the opposite bit. On that label at least T−ceil(min(m,T)/2) members remain: among the distinct inspected members at most half rounded up had the forecast bit. For T≥2 the remaining set is nonempty. Thus no learner can promise zero errors at T≥2. Above C_r this adversary forces one mistake with more than C_(r−1) survivors and can continue inductively. Each completed table is fixed before the next round. A seed in the final nested survivor set realizes every label of the finite transcript. Determinism makes the same transcript attainable when the completed tables and that seed are fixed in advance.

The lower proof even permits revelation of each **whole past table** and the exact surviving set immediately after its label. Arbitrary subsequent inspection of those tables or unlimited computation still gives no values of the next fresh function. The upper bound in the basic game uses zero historical evaluations. The stronger information model matters for the following implementation, which checks past labels to return supporting seeds.

### The exact budget for an n-bit seed

Write q=ceil(m/2) and D_r=C_r+1. Then D_0=2 and D_r=D_(r−1)+min(D_(r−1),q). For n≥2 and m≤2^(n−1), the doubling bound gives C_(n−2)≤2^(n−1)−1. The next two increments are at most q each, so C_n≤2^n−1. For m=2^(n−1)+1 put a=2^(n−2). Now q=a+1 and doubling gives C_(n−2)=2a−1, also valid at n=2. The next capacities are 3a and 4a+1, which suffice for all 2^n seeds. Thus **2^(n−1)+1 is the least current-point budget guaranteeing n mistakes**. For n=0 and n=1 the least positive budget is one. Even with unrestricted evaluations, coordinate queries on previously untouched bits can force n mistakes.

### Supporting a positive forecast

The [NAND implementation](limited_query_halving.py) samples the least L candidates and filters them using every stored mistake row and its observed label. Of the v members passing this filter it evaluates the current row at all v and predicts their majority, defaulting to zero if there are no votes. A positive forecast returns a sampled original word satisfying the current row and all stored labels. On an all-wrong history those labels constitute the entire history, including at a state reached by committing only positive labels on mistaken predictions. After correct observations which were ignored, the witness guarantee refers only to the retained observations.

On error discard the L−v inconsistent samples and every viable sampled member voting incorrectly. The number removed is at least (L−v)+ceil(v/2)≥ceil(L/2), so the capacity bound still applies. Every candidate outside the sample remains. The chosen order permits storage as a short sorted list of sampled survivors and an untouched integer suffix. For this particular voting policy complemented thresholds already attain its worst-case population progression when the NAND cap permits them. With the largest word as the seed, make the least ceil(L/2) candidates vote zero and all larger words vote one. Whenever T≥2 this forces an erroneous zero prediction, removes exactly ceil(L/2) candidates, and leaves every survivor consistent. The unrestricted oracle lower bound concerns all deterministic policies; the threshold construction concerns this policy.

With e earlier mistakes, an uncached round uses at most L·e historical evaluations (stopping on the first failed old row per seed) and exactly v≤L current evaluations. On an all-wrong history of e past rows a fresh replay through the current forecast charges at most m(e+1) current-row calls across replay rounds and m·e(e+1)/2 historical calls. Per-trial counters record exact evaluation costs of uncached computations. Cumulative counters saturate at 2^(4n+8) to keep their bit length independent of the horizon. An immediate cache hit makes no new calls. Once no candidates remain on an inconsistent transcript, the incremental learner makes no further point evaluations or history updates. The live sample takes O(m(n+1)) bits in addition to stored circuits and evaluation workspace. Explicit circuit validation, equality testing and evaluation have their own polynomial bit costs per use. At the exact n-mistake budget, m is exponential in n. If all evaluations, including historical ones, share one per-round cap, the basic strategy still meets that cap, while the history-filtered implementation must charge both types of calls. The [independent checker](check_limited_query_halving.py) covers small minimax states, NAND trajectories and positive-support witnesses.

The [unconditional SAT driver](sampled_forecast_sat.py) selects this budget and supplies the sampled learner to the single-history threshold reduction. It handles arbitrary original NAND circuits with deterministic bit cost 2^n times a polynomial in n and the circuit encoding. Direct enumeration already has this exponential rate. A resource-budget refusal is distinct from UNSAT. [Native integration checker](check_sampled_forecast_sat.py)

Seldin, Bartlett, Crammer and Abbasi-Yadkori study limited expert advice with a per-round limit on the experts queried and give regret bounds over a horizon T. Here a single seed predicts perfectly, and the quantity determined is an exact deterministic mistake capacity independent of the horizon. [ICML 2014 paper](https://proceedings.mlr.press/v32/seldin14.html)

Hanneke, Livni and Moran study the expressive power of simple online predictors, including aggregations of proper hypotheses. The present budget instead counts inspections of the fresh query on individual seeds. A learner inspecting a circuit's gate list can obtain additional information about its function; the arbitrary-table lower bound gives no general lower bound for that access model. [COLT 2021 paper](https://proceedings.mlr.press/v134/hanneke21a.html)
