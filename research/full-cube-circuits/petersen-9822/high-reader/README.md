# Physical readers of the inverter

For a reduced candidate with seven AND gates, one NOT gate and at most seventeen total sites, a hot singleton among inputs 5 through 8 forces exactly one physical reader of the inverter. When two such singletons are hot, that reader excludes both owner raw inputs. The [producer sources and receipts](source-receipts.zip) record the physical gate construction and its standard-axiom endpoints. The pair sector remains open in the complete Lean proof.

The [public nonadjacent supplement](public-nonadjacent.zip) adds the producer kernel exclusion for shared literal high guards on pairs 56, 67 and 78 in the minimum seventeen-site, seven-AND signed case. It uses the earlier source archive in this directory. The axiom report for public_nonadjacent_impossible lists the three standard axioms. The [physical proof](nonadjacent-negative-reader.md) received independent source review.
