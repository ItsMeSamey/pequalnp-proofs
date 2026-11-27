# Low-rank off-diagonal variation

Normalize the n diagonal control forms to the coordinate bits tⱼ with a possible constant offset. Let H have independent rows spanning all varying off-diagonal forms. Put w=rank H. Conditional on Ht=u, the full pencil is D(u)+diag(t), including arbitrary fixed asymmetric drift in D. For each u compute in the binary group algebra of the additive group F₂ʷ. Write zᵃzᵇ=z^(a+b) and Hⱼ for the jth column of H. Multilinearity of the determinant shows that

    Σ_t det(D(u)+diag(t)) z^(Ht)

is the determinant with free column j equal to (1+z^Hⱼ)Dⱼ(u)+z^Hⱼ eⱼ. A pin tⱼ=b replaces the sum by its single term z^(bHⱼ)(Dⱼ(u)+b eⱼ). Extract coefficient zᵘ and sum over all u to obtain precisely the prefix parity. No symmetry is needed for this identity. If full parity is odd, select successive odd children; every target is then attained by solving the terminal leaf system. Symmetric varying matrices with independent diagonals have odd full parity even with arbitrary fixed binary drift (the binary determinant degree argument in symmetric-overlap.md). Without that promise even parity is inconclusive.

The implementation uses the division-free Berkowitz characteristic-polynomial recurrence. With leading scalar a, border row b, column c and trailing block B, its Toeplitz column in characteristic two starts 1,a,bc,bBc,… . Multiplying this Toeplitz factor by the characteristic coefficients of B gives the coefficients for the enlarged matrix, including its determinant. The recurrence works with zero divisors.

Each group-algebra product is an XOR convolution. Lift the coefficient bits to integers, perform two Walsh transforms, multiply pointwise, transform once more and divide every integer result by the transform length before reducing modulo two. Exact integer inversion avoids division in characteristic two. The arrays have at most 2^w entries and O(w+1)-bit intermediate integers; byte-based packing avoids repeated whole-vector shifts. Thus a product costs O*(2^w) bit operations. Berkowitz uses polynomially many products per frozen u. There are 2^w frozen patterns and at most n+1 parity queries for a witness, giving O*(4^w) deterministic bit time and O*(2^w) space. The reference solver also accepts supplied raw sections and verifies every lifted witness against its raw evaluator.

The executable regression compares 330 prefix parities against binary rank enumeration, includes w=0 and w=n, and replays eight supplied-section targets with asymmetric constant drift.
