# Limits of three circuit repairs for L-meta-20579

On the fixed 26-feature interface below, the smallest flat signed DNF that agrees with all required evaluations has **exactly 58 terms**. A single flat signed CNF agreeing with them needs **at least 25 distinct nonunit clauses and 49 binary gates**. A separate repair that preserves eleven product gates and replaces five other products using positive OR networks requires **at least 174 gates in total**. Each result uses the same graph and 180-gate starting circuit.

## Replay

From this directory, run the following command with Python 3.10 or later. The checker uses only the standard library. It reconstructs the required signatures, evaluates the DNF and checks both normal forms. It also enumerates every maximal parent cover and pairing used in the restricted 174-gate proof.

```sh
python3 -I -B check.py
```

## The fixed interface

The graph is the labeled 32 × 32 matrix in the included mathematical statement L-meta-20579. Bit v of hexadecimal word u in `graph.json` describes cell (u,v), counting from zero at the least significant bit. The 180 gate triples in `context.json` are transcribed in order from the construction in L-meta-20578 for the same graph. Each triple contains an operation (0 for AND or 1 for OR) and two earlier wire numbers. On cell (u,v) only input wires u and 32+v are true. Gate j creates wire 64+j, and the output is wire 243.

Cut wires 220, 223, 224, 225 and 226, replacing their values with five local outputs. The ordered bank in `context.json` identifies the 26 available upstream signals. Feature j is bit j of a signature. The complement of wire 121 is already present as a marker. Its first six diagonal evaluations have mask 0x35. The lower bounds grant every signed literal for free.

The checker tries all 32 assignments to the five ports on each of the 1,024 cells. On 98 cells precisely the nonzero assignments are valid. On 613 cells only the all-zero assignment is valid. The other 313 cells accept every assignment. Projecting the constrained cells onto the feature bank produces the 92 positive and 427 negative signatures in `care.json`. Unlisted signatures impose no condition. Each feature has an opposite-label pair differing only at that bit.

The five-port construction keeps 140 old gates plus the marker, leaving 29 local gates under the 170-gate cap. A merged construction routes its local function to port 220 and ties the other four ports low. Simplifying the retained ORs keeps 136 old gates plus the marker, leaving 33 local gates. These budgets concern this fixed construction.

## Exact DNF term count

A signed cube is a conjunction of signed features. A flat DNF is an OR of cubes. The 58 cubes in `terms.json` use positive wire IDs for direct features and negative IDs for complements. Their union contains every required positive and no required negative.

The lower-bound certificate `positive-blockers.json` selects 58 distinct positive signatures. For each of their 1,653 unordered pairs it supplies a required negative agreeing on every coordinate shared by the pair. Every literal true at both positives also holds at that negative. Thus a safe cube of any width can cover at most one of the 58. The explicit cover attains the bound.

Joining 58 distinct terms in one flat OR needs at least 57 binary OR gates. When split across up to five flat DNF outputs, at least 53 local OR gates are still required. Both exceed the respective 33- and 29-gate budgets before charging for literals or conjunctions.

## Flat CNF gate count

A flat CNF is one conjunction of clauses, each a disjunction of signed features. The 25 negative signatures in `negative-clique.json` must each falsify a clause. For all 300 pairs, the checker finds a required positive agreeing on every common coordinate. A clause false at both negatives would also be false at that positive. The 25 negatives therefore require 25 distinct excluding clauses.

For each selected negative and each of the 26 coordinates, some positive has the same bit there. These 650 checks imply that a single literal excluding the negative would exclude a positive. Consequently the 25 clauses require distinct OR outputs. Conjoining them takes at least another 24 binary AND gates. This gives 49 binary gates even when clauses share OR subexpressions and negated features are free.

The CNF bound applies to a single merged CNF. An OR of five CNFs can have a different size. Distributive factoring and interleaved AND/OR/NOT gates also change the representation. The existence of a general 170-gate circuit for this graph and the P versus NP question remain open here.

## Five paired products

The paired-product construction can use all 64 raw inputs and all retained OR signals to build endpoints. Its 174-gate lower bound concerns that separate fixed topology. The proof derives a lower bound of 28 additional endpoint OR gates after checking 214 covers and all 945 pairings per cover. [Proof and enumeration](paired-products.md)
