# Physical readers of the inverter

For a reduced candidate with seven AND gates, one NOT gate and at most seventeen total sites, a hot singleton among inputs 5 through 8 forces exactly one physical reader of the inverter. When two such singletons are hot, that reader excludes both owner raw inputs. The [producer sources and receipts](source-receipts.zip) record the physical gate construction and its standard-axiom endpoints. The pair sector remains open in the complete Lean proof.

The [public nonadjacent supplement](public-nonadjacent.zip) adds the producer kernel exclusion for shared literal high guards on pairs 56, 67 and 78 in the minimum seventeen-site, seven-AND signed case. It uses the earlier source archive in this directory. The axiom report for public_nonadjacent_impossible lists the three standard axioms. The [physical proof](nonadjacent-negative-reader.md) received independent source review.

The [adjacent literal supplement](adjacent-literal.zip), with the two earlier archives, provides the producer kernel exclusion for adjacent pairs 57, 58 and 68 with at least seven AND gates. It covers public and private literal high guards under the theorem's physical candidate assumptions.

The [semantic high-pair supplement](semantic-high-pairs.zip) preserves physical fanout when normalizing the original guard to a literal pair. The resulting kernel endpoints exclude adjacent hot pairs 57, 58 and 68, including private guards, and exclude public nonadjacent hot pairs 56, 67 and 78 at exactly seven ANDs. The terminal log prints the standard three axioms for each theorem.
