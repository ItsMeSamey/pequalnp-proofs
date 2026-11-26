# Exact point-side singleton complexity

For the seven residual projective neighborhoods, the minimum number of binary set unions and intersections needed to produce all seven four-point masks is **21**, even granting every mask meeting each target in at most one point as a free input. The 13 actual raw points and 18 supplied point-OR features belong to that library. Seven independent four-point unions attain 21 on the original inputs.

The theorem concerns the point-only singleton restriction. A circuit that computes arbitrary monotone signals on point assignments and has the seven prescribed singleton signatures induces such a set circuit, so it needs at least 21 point gates. This conclusion does not by itself settle residual circuits with additional point boundary signatures or arbitrary mixed-gate architectures.

Read five_certificate/README.md, SIX.md and SEVEN.md in order. The first file proves the initial marked calculations and five-line result. The next two explain the projective graph reduction and final finite case checks. The three uses of a marked target retain the designated intersections even when projection allows equal operands.

Run the complete independent replay from a fresh environment with Python 3, a C++20 compiler, and the two dependencies pinned in requirements.txt:

```sh
python -m pip install -r requirements.txt
python verify_all.py
```

The verifier uses a temporary working directory, regenerates all graph cases, compiles the interval checker, verifies coverage, and runs the SAT solver without a conflict limit. No repository, prior outputs or downloaded geometry tables are needed beyond the installed libraries. The graph-atlas stage checks nonisomorphism and compares exact labeled-graph mass against an inclusion–exclusion count. The six-line graph enumeration is independently reconciled against the graph atlas, including all concurrent three-edge paths. A more constrained final SAT model is also available via `--strong`; its extra inequalities are proved in SEVEN.md.

The archived logs record the authoring runs. The verification script performs fresh checks. To replay an individual stage, for example, run `python verify_all.py --stages seven20`.
