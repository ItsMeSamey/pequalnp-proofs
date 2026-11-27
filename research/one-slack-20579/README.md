# A one-slack lower bound for a three-output circuit replacement

Outputs 213, 222 and 225 require **at least 14 replacement gates** with the 15 donor signals listed below. Computing their combined contribution through one output requires **at least 16 replacement gates** with the same donors. Attainability at either threshold remains open here. L-meta-20579 asks whether the full graph admits a circuit of at most 170 gates. The full question and search range 53 remain open in this study.

## Replay

Run this command from the package directory with Python 3.10 or later. It uses only the standard library.

```sh
python3 -I -B check.py
```

The checker verifies the control on all 1,024 promised inputs, reconstructs the observable relation at the three replacement outputs, checks 15 oriented witness pairs and 18 original corner samples, and checks the case-summary CNF. The proof derives its clauses from circuit structure. The CNF encodes the final five-way contradiction after these deductions. Direct enumeration of gate lists and exclusion of a whole search range lie outside its scope. [Structural proof](PROOF.md)

## Frozen sources and scope

The source file `control.lean` supplies the prior 180-gate AND/OR circuit for the same labeled graph. Wire 243 is its output. Raw wires 0–31 select the row and wires 32–63 select the column. Gate outputs start at wire 64. Appending a NOT reading wire 121 and retaining output 243 produces the 181-gate control. Its first internal NOT has diagonal bits `1,0,1,0,1,1` in increasing diagonal order, or hexadecimal `35`. [Pinned upstream control](https://github.com/open-goat/pequalnp-proofs/blob/624acb3fb2189a78719c262c1af407bd73fb3b5c/lean/PEqualNP/Outside/L_meta_20578.lean)

`statement.txt` freezes the public L-meta-20579 statement and its 32 row masks. Bit zero denotes column zero. SHA-256 digests are `e233b9b26bab1a8856b41abefce91ad2660f5139effd3df1ad8e11582240f816` for the statement and `08b07ebb1edfb826bb061afcc09558ae5d75a6d4d626e43c373c4d8e6855d731` for the included control. The package includes the upstream Apache 2.0 license.

The replacement removes the following original gate outputs.

```text
96 111 112 116 117 169 170 171 172 187 188 189 190 213 222 225
```

Only the three labeled outputs leave this region. Their fixed downstream use is OR with the thirteen retained AND terms. The available donor wires, in witness bit order from least to most significant, are

```text
42 65 83 86 90 94 95 99 101 102 107 110 115 165 186
```

Donor 165 remains live through term 221. A missing wire reads false. Each new AND, OR or NOT with at most two listed operands costs one gate. Reusing a donor and tapping an output cost zero replacement gates. The physical size of a rebuilt whole circuit depends additionally on retained donor cones and the final OR tree.

On a target zero, all three replacement ports must output zero. On a target one where the retained terms are zero, at least one replacement port must output one. Where a retained term already outputs one, any tuple is allowed. The 1,024 cells yield 171 observed donor vectors. Of these, 96 require the all-zero tuple, 47 require a nonzero tuple, and 28 admit every tuple. The certificate records original cell coordinates so that the checker can independently derive each donor value. [Witness cells](witnesses.json)
