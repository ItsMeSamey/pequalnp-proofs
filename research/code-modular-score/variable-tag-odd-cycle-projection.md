# Unbounded tag rank needed by the clause-coordinate encoding

Use the simple 3-connected bipartite construction in variable-tag-three-bin-hardness.md, with two checks and one tag per hyperedge. Every noninjective linear projection of the tags changes NO to YES on the following family.

For odd L≥3 take cycle variables x₀,…,x_{L−1} and selector variables z₁,z₂,z₃. The hyperedges are the selector triple {z₁,z₂,z₃} and all 3L triples {xᵢ,x_{i+1},zⱼ}, indices cyclic. Thus m=3L+1. In a proper coloring the selectors must be mixed. Any equally colored consecutive cycle vertices form a monochromatic triple with a selector of their color. Alternating all around an odd cycle is impossible.

For every triple E there is a coloring making E red and every other triple mixed. For the selector triple, color all selectors red and all cycle vertices blue. For E={xᵢ,x_{i+1},zⱼ}, alternate along the even-length path left by deleting that cycle edge, making both ends red. Make only zⱼ red among the selectors.

For any nonzero d in F₂ᵐ choose E in its support and use that coloring. Initially assign both E-checks to the red hub block and split all other pairs between the red and blue blocks. The three tag defects are (e_E,e_E,0). For each other F in the support of d move its blue check to red. Every such triple is mixed, so all moved checks attach to red variables and the three blocks stay connected. The resulting defects are (d,d,0). Zero is impossible by the reduction. Thus the possible defects of this form are exactly the nonzero vectors.

Every map of tag rank below m kills one such nonzero d and gives a false positive. For a uniform affine offset add three neutral extra vertices adjacent to all hubs in advance. The original physical order 3+(L+3)+2m is odd. Of the three constructed blocks either one or three have odd size. Give each odd block an extra and put the remaining zero or two at one hub. All block sizes are now even, cancelling any common translation. Extras are adjacent to no checks and do not affect the source NO proof.

The obstruction permits instance-specific linear projections of the specified tags while keeping heights and target fixed. It gives no hardness conclusion for a fixed tag count or for general vertex-dependent rewrites.
