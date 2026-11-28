# Verifying the examples

From this directory run the following commands with Python 3 and sha256sum.

    sha256sum -c SHA256SUMS
    python3 -B examples/verify.py
    python3 -B examples/check-upper.py

The JSON files list the eight undirected edges and the gates in evaluation order. Inputs have indices 0 through 7, and gate j has wire index 8+j, starting at j=0. The first checker verifies the labeled graphs, a perfect matching, absence of four-cycles, and each circuit's output on all 256 assignments. The second provides a shorter independent replay of the upper bounds. The proof that a smaller circuit cannot compute either graph is in lower-bound.md.

The four example files were copied byte for byte from the frozen source archive c6-exact11-w04.tar.gz, SHA-256 1c416b6adcbda71e6dae9d2480c4c0c61b70d285e0cc6a046b56dc7f1ebc2d4e. The present research package is self-contained and uses its general analytic lower bound for both examples.
