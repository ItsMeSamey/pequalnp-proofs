# A 1,785-gate circuit on the 128×128 L-meta-20583 table

Input wires 0 through 127 are row flags and 128 through 255 are column flags. A gate is a JSON triple [operation, left wire, right wire]; its output receives the next unused wire index. The final gate is the output. Row i of rows.hex gives its positive columns from least to most significant bit. The source file includes the public content-addressed desk URL and verbatim formal statement. This construction establishes an upper bound of 1,785; the official question asks for at most 1,350.

The producer covered the 6,485 positive cells with 144 rectangles and combined compatible rectangles in mixed AND terms. The independent verifier evaluates all promised assignments as one 16,384-bit truth table, checks physical predecessor indices and counts used gates by backward traversal. Reproduce with python3 verify.py; no network, compiler or third-party packages are required.
