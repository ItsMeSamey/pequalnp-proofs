# Issued 8573, m at most 2n+1

Source proof for the exact two-input AND/OR model. Write n for either
shore size, m for the number of graph edges, q for circuit size. The
permutation supplies n disjoint edges. Every vertex has degree at least
two, and two distinct vertices have at most one common neighbor by the
issued rectangle condition and bipartition. In particular m≥2n. The
matching and m>n exclude the empty case. Neither top form nor the dirty
gate count is required in this range.

**Physical accounting.** Every input is essential, witnessed by a
singleton neighbor. The output is computed. Every gate of a least circuit
is live: keep the backwards output cone, preserve order and remap indices,
preserving exact fanin two. Count consumer pins separately, including ties.
All wires other than the output have positive fanout; the output has no
consumers. The sum over all non-output wires of (fanout−1) is
2q−(2n+q−1)=q−2n+1. Call a wire with at least two consuming pins a fork.

Follow each raw's unique forward path up to its first fork, counting the
raw itself if it forks; stop at the output if no fork is met. This partitions
the raws into blocks indexed by topologically ordered forks and a final
terminal block; empty blocks are allowed. The region of a block is a
formula on its fresh raw leaves and pins supplied by earlier forks: trace
its root backward, stopping at earlier forks. All other internal vertices
have a unique forward pin, so no fresh occurrence can repeat. No earlier
fork depends on a fresh or future raw, and every fresh raw influences
the suffix exclusively via this block's single root bit. These facts also
hold for a terminal region. With earlier raws fixed, the block's bit is
independent of future raws, so its rows over future assignments take at
most two distinct values as functions.

**Emitter lemma.** A block is independent. Otherwise adjacent u,v in the
block give an AND section alone and an OR section when distinct off-edge
neighbors of u and v are enabled. These neighbors are nonadjacent, since
their adjacency would close a rectangle. With other inputs fixed, a
nonconstant section depending on both leaves requires identity propagation
on each leg and above the fixed least common ancestor (unary monotone
Boolean maps are identity or constant). The ancestor cannot be both AND
and OR. The direct fork of a raw has no second fresh leaf.

Call a raw h an emitter if it has a neighbor y in a later block. Its
block must be a singleton. Suppose s is another member. At all earlier
raws zero, compare the empty fresh assignment and the singleton assignments
on the future singleton columns. The former gives zero; the latter have
supports N(h) and N(s) restricted to the future. The one-bit condition
forces these two supports equal if both nonempty. In that case the
rectangle condition makes both equal to {y} and s,h have the same shore.
If s,h have the same shore choose x in N(s) outside N(h), possible by
minimum degree and at most one common neighbor. It is earlier, by the
future-support observation and block independence. It is distinct from
y and nonadjacent to y as they have the same shore. If s,h have opposite
shores, s has no future neighbor. All its neighbors are earlier and on
h's shore. One of them, x, misses y: otherwise s and y would share at
least two neighbors (s≠y). In either case x hits s, misses h and y.
With only x enabled among prior raws, fresh assignments empty,{s},{h}
produce distinct rows 00,11,01 on the future columns empty,{y}.
Contradiction.

The emitters cover all edges: their endpoints belong to different
independent blocks, and the earlier endpoint is an emitter. There are
at least n such vertices by the matching. Their singleton blocks are
nonterminal and give distinct forks. Thus q−2n+1≥n. This settles m=2n.
At m=2n+1 the only remaining case is equality: exactly n emitters S
and n distinct forks, with no further nonterminal blocks. The other n
raws Z all belong to the terminal block; each has a unique path all the
way to the output. They are independent. There is at most one edge in S,
since the total incident at Z is at least 2n.

**Terminal charging.** With no edge in S, use S itself as a fixed
independent setting hitting all Z neighborhoods. If xy is the unique
edge in S, use S minus x; this is independent and hits every neighborhood
by minimum degree. In either setting the function on Z is their OR.
Classify gates according to whether a raw in Z reaches them syntactically.
The Z-bearing gates form a tree after omitting the Z-free side inputs
and suppressing unary vertices: any fork reachable from Z would violate
its unique output path. Any join with two Z-bearing children is OR:
at the fixed setting the baseline output is 0, and turning on either
of two leaves in opposite children independently produces 1; a fixed AND
at their least common ancestor cannot do this. There are n−1 such joins.

On a particular j's route, the ANDs consequently each have one Z-free
side guard, a function of S. For an independent S setting, at all Z zero
the output is zero. The j-singleton is accepted exactly when every AND
guard is true: when all are true a 1 propagates up; when one is false the
j=0 and j=1 trajectories coincide above it. OR siblings off the path do
not depend on j. Thus all its AND guards accept every singleton of N(j).

Without an internal edge, S minus N(j) is independent. With xy present,
partition S by its original shores A containing x and B containing y.
N(j) lies entirely within one shore. For N(j)⊆A, take the independent
complement C_j=S minus (N(j) union {y}); for N(j)⊆B exchange x and y.
In the no-edge case take C_j=S minus N(j). On this setting j is rejected,
so a particular guard g_j rejects C_j. Its singleton support contains
N(j) and is contained in S minus C_j by monotonicity. This chosen physical
AND is distinct for each j: a shared guard must accept N(k) for k≠j.
On the same shore that would give at least two common neighbors; on
opposite shores at most one opposite singleton is permitted.

In the Z-free guard cone retain wires in a backward trace from g_j
that reject C_j, choosing one rejecting child at an AND and both at
an OR. Propagate actual accepted singleton labels down the trace:
at AND send every assigned label to the chosen child; at OR route each
label to an accepting child. Use one consistent choice per wire/label,
or equivalently choose each label's path separately. A path ends only
at its own raw. The union of paths from the guard to the d distinct
neighbor raws is a connected DAG with ≥d−1 distinct branching vertices
(by edge counting, outdegree ≤2). Each branching vertex is an OR that
actually accepts at least two distinct labels, since one label takes
one path; it rejects C_j. These ORs cannot be charged by a different
column: same-shore charges share at most one eligible neighbor and an
opposite-shore trace accepts at most one singleton from this shore.
The charges are pure-S gates, distinct from the n selected ANDs and the
n−1 bearing joins.

Let d be the number of S–Z edges. The total charged is
(d−n)+n+(n−1)=d+n−1. If S has no edge this is the desired m+n−1.
Otherwise d=2n. Equality at 3n−1 would exhaust every gate by pure-S ORs,
chosen Z-bearing ANDs and Z-bearing joins. With Z all zero, every bearing
gate would evaluate to zero inductively; the joins are OR and every
bearing AND has a zero bearing child. The output is bearing, but accepts
S={x,y} at Z zero. Hence q≥3n=m+n−1 as required.

Scope: a source-level proof for m≤2n+1, with no compiler run or claim
on the unrestricted 8573 theorem.
