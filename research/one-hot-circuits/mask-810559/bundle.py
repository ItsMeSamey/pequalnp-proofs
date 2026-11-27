from pathlib import Path
research=Path("/workspace/pnp-research/lean/Research/MissingCellRigidity.lean")
generic=Path("/workspace/scratch/one-per-shore-classification")
files=[research]+[generic/(name+".lean") for name in ["TightPhysicalSupport","PhysicalReadOnce","ReadOnceP4","FormulaCorner","PhysicalCornerLower"]]+[Path("Mask810559.lean")]
body="import PEqualNP.Defs\n\n"
for path in files:
    body += "\n".join(s for s in path.read_text().splitlines() if not s.startswith("import "))+"\n\n"
Path("L_meta_23331.lean").write_text(body)
