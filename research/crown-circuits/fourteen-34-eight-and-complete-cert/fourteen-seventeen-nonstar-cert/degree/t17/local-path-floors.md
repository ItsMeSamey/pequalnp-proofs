# Local OR minima of the four- and five-vertex paths

A P4 on edges x,y,z has flags a=x, b=x∨y, c=y∨z, d=z. A monomial containing only flags true on all positive edge pairs can use only b and c, both already true on the negative singleton y. Thus at least one OR is needed; bc(a∨d) attains one.

A P5 on edges x,y,z,w has flags a=x, b=x∨y, c=y∨z, d=z∨w, e=w. With at most one OR and any number of ANDs, a circuit is a union of at most two raw monomials, by distributing the output product. An accepting monomial on xy must include a and c: the positive flags there are a,b,c, and omitting a includes it in the y singleton, while omitting c includes it in x. Likewise a monomial accepting zw must include c and e. These must be two different monomials, and both miss xw, where c=0. This proves the two-OR lower; c(a∨e)∨bd attains it.
