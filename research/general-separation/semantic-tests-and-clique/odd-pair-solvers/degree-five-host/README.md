# Two-pin odd supports on maximum-degree-five hosts

Start with [the theorem and construction](degree-five-two-pin-host.md) and the [first-sensitive-cap lemma](mixed-cap-first-sensitive-step.md). Given a simple undirected graph of maximum degree five and two distinct original vertices, the deterministic solver returns an induced all-odd vertex set containing both pins if one exists, or NO if none exists. The theorem concerns this bounded-degree graph problem. It leaves unrestricted host degree and the P versus NP question open.

## Run the solver

Use Python 3.10 or later. The solver uses the standard library.

    python general_five_cap_host.py input.json

Without the filename the solver reads JSON from standard input. Vertices are numbered from zero; list each edge symmetrically and give two distinct pin indices. For example:

    {"neighbors":[[1],[0]],"pins":[0,1]}

The output for that example is `{"status":"YES","witness":[0,1]}`. Every YES is verified on the original graph. NO certifies absence on the supported class. On graphs exceeding degree five it returns UNKNOWN, except that an adjacent pin pair immediately gives YES. The polynomial bound permits very large constants. The reference implementation makes no resource guarantee for large untested inputs.

## Clean replay

Run from the extracted directory. The controls use NetworkX for the atlas and random-input generation. The release replay used CPython 3.12.14 and NetworkX 3.7.

    sha256sum -c SHA256SUMS
    python general_five_cap_host_check.py
    python general_five_cap_history_check.py

The first control compares the solver with an independent original-subset oracle on 2,910 inputs, checks both previously out-of-promise negative fixtures directly, and exercises 42 remote triple repairs on controlled templates. The second replays 1,042 production transitions in each of three genuine contaminated histories, validates the terminal and restored four-site witness, and checks the retained-pin contact at a nonadjacent triple. A separate complete search on a 2,088-site clean graph returns its full vertex set.

The previous reviewed common-neighbor release is included intact as `prior/common-neighbor-odd-host-release.zip`, SHA-256 `b15ef019e7e864bcbf8ebd9fc7f3fa2d25d14dd1c19e3a96c219b6b511393770`. It includes the earlier width-seven release and their replay instructions. The current top level contains the full solver's transitive Python dependencies, linked mathematical sources and the historical review fixtures. The negative fixtures fail the earlier common-neighbor promise but satisfy the present maximum-degree bound.
