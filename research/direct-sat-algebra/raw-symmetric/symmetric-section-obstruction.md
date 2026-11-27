# Padding and the essential input dimension

Let B be a binary vector-valued polar on V with outputs O, and R its common radical. Suppose a raw symmetric certificate embeds O* via Phi into an isotropic leaf L, with S(x) the matrix of pairings of B(x,Phi(u)) against v, symmetric in u,v for every x. Let D(x) denote its diagonal and suppose D has rank r=dim O. Then dim(V/R) is at least 2r.

Both R and L lie in the kernel of D. If Phi(u) lies in R, symmetry implies u·D(x)=uᵀS(x)u=0 for all x, hence u=0. The image of L in V/R has dimension r and lies in the kernel of the induced D, which has rank r. The argument includes r=0.

Each nonempty component of the three-vertex-path compiler over GF(2^m) contributes 3m essential input bits and 2m output bits. Testing the polar against either leaf recovers the center; testing against the center recovers both leaves in separate outputs. Thus k components have dim(V/R)=3mk while 2r=4mk. Appending arbitrarily many variables entering only through affine terms increases the common radical by their dimension and preserves this obstruction, including after invertible affine input/output recoding. Individual projected output tuples can still admit a section.
