# First-branch certificates for scalar Boolean care tables

The engine checks lower bounds on the number of unit-cost gates in a single-output DAG with binary AND, binary OR, unary NOT and unrestricted fanout. Its API takes the care table and source model explicitly. The library has no filesystem dependencies or benchmark-specific dimensions.

## Care and source model

The care table contains distinct integer pairs [pattern,label]. Bit j of pattern is logical coordinate j, least significant first. Labels are 0 or 1. Unspecified patterns are unconstrained. A dictionary mapping patterns to labels is also accepted by the Python API.

A source model contains literals (one entry per logical coordinate) and fixed_cost (a nonnegative integer). Positive and negative are spelled "positive" and "negative" and supply the corresponding polarity alone; the source may be unused. Negative-only coordinates are automatically recoded. "both_live" is an explicit premise that both complementary physical leaves occur in the pruned DAG. The verifier counts two live leaves and conditions on this coordinate in every group fiber. Use this model exclusively for such an actual-use case. The ambiguous value "both" is rejected.

For **available** free complementary source pairs, use verify_optional_family with the literal "optional". Supply all three choices positive, negative and both_live for each optional coordinate, keeping other coordinates unchanged. A circuit using neither polarity is covered by either one-sided choice. The family verifier requires the entire Cartesian product, a common budget, the same care data, and the declared fixed cost. It rejects missing, duplicate and extraneous liveness cases before running exclusions.

The application must independently justify fixed_cost as an unavoidable charge disjoint from the counted DAG. Zero gives a standalone tail bound. The model allows complementary input sources as declared. Free internal complemented edges and other gate libraries require a separate proof.

## Replay and generation

The library entry points are:

* make_certificate(care, feature_count, model, budget, cases) generates witnesses for a proposed plan.
* verify_case(care, feature_count, model, certificate) validates the witnesses and topology coverage and returns a bound, or raises an exception. A direct caller must verify a generated certificate before relying on it.
* verify_optional_family(care, feature_count, model, certificates) checks an optional-source family. Each list entry has fields literals and certificate. It returns the common total bound and per-case results.

Each plan case specifies positive and signed group capacities, a Boolean ordered flag, and the expected count partitions. Unordered exclusion requires zero compatible partitions; ordered exclusion requires every compatible partition to have zero feasible topological orders. Empty groups are permitted. The verifier checks coverage of every inversion count allowed by the budget and source model. The canonical SHA-256 input binding covers feature count, ordered literals, fixed cost and sorted logical care rows. Applications can additionally authenticate raw input bytes.

The standalone two-input XOR example proves the tight lower bound of four gates:

    python -BO engine/fork_cli.py verify --care applications/xor2/care.json --rows-key care --feature-count 2 --model applications/xor2/model.json --certificate applications/xor2/positive.certificate.json

To generate a certificate, change verify to generate, pass --plan applications/xor2/plan.json, and choose a fresh --certificate path. Generation runs the verifier before writing. The verify-family CLI action accepts the list of family records instead of a single certificate. --rows-key selects care rows from a containing manifest when needed.

## Counting and proof obligations

Let I be the guaranteed number of live physical leaves. Each observed essential one-sided coordinate contributes one; each explicitly both-live pair contributes two. Unobserved essentiality need not be assumed. For B binary and N unary gates, there are 2B+N operand edges and at least I+B+N−1 nonoutput vertices. Pruning leaves every such vertex with an outgoing edge. Thus at most B−I+1 vertices branch, and B≥I−1.

A one-sided input with both directions of change observed must have both NOT parities on its paths to the output. Otherwise unrolling the DAG and pushing negations to its leaves would make that input unate. Assign each such input to its first branch, following its unique initial path. After fixing all inputs outside a group, the output is a unary function of the group's branch signal. Each coordinate is unate in that signal with a globally fixed sign.

At most N−1 groups can have a negative prefix when N≥1. Charge each negative group to a NOT on one negative prefix. Its branch must have a strictly later NOT on some path to permit both output parities, so a maximal NOT cannot be charged. The continuation from a charged NOT to its first branch is fixed; distinct groups charge distinct gates. If N=0, observed binate coordinates are impossible.

The verifier rejects monochromatic sets of coordinates for three reasons:

* Two changing Hamming edges in a fixed outside-group fiber determine the relative signs of their coordinates. Contradictory signs in different fibers prevent a common group. A same-coordinate contradiction needs just one pair of edges.
* For a positive group, an increasing pair labeled 0,1 and another labeled 1,0 within a fiber contradict the unary-decoder property.
* Two coordinates in one group have unique paths merging at a fixed binary gate. Fixing the other inputs leaves a unary/constant output, or a function differing on exactly one corner of the two-coordinate square. That corner is fixed by the incoming path signs and merge operator. A downstream unary decoder can reverse all labels but cannot move this corner. For a positive group only corners 00 and 11 can be exceptional. The checker tests the permitted corners against all fibers.

For a group G in topological order, its signal cannot depend on an input whose first branch is later. Condition on the nongrouped coordinates and on earlier groups. The branch is a monotone function of G after complementing a fixed subset of the group's inputs. Comparable signed patterns give Boolean implications. Opposite labels at rows agreeing outside G force unequal values. A literal mutually reachable with its complement in the implication graph disproves feasibility. The verifier tries all signs and orders and permits unrelated truth tables in different contexts. The final coverage check uses these exclusions only for the group capacities and sign models they actually cover.
