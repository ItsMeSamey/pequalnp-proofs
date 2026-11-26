"""Rebuild the census and compare the clean-private proof ledger."""
import ast
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as temp:
    work = Path(temp)
    for source in root.glob("*.py"):
        if source.name != "replay.py":
            shutil.copy(source, work)
    subprocess.run([os.environ.get("CXX", "g++"), "-std=c++20", "-O3",
                    str(root / "quartet_models.cpp"), "-o", str(work / "quartet_models")], check=True)
    with (work / "models.tsv").open("w") as models:
        subprocess.run([work / "quartet_models", "7", "5"], cwd=work,
                       stdout=subprocess.DEVNULL, stderr=models, check=True)
    if (work / "models.tsv").read_bytes() != (root / "models.tsv").read_bytes():
        raise ValueError("Regenerated graph decorations differ")
    subprocess.run([sys.executable, str(root / "crosswalk.py")], check=True)
    for stage in ("graph_types", "maximize", "sharpen", "allrows"):
        subprocess.run([sys.executable, stage + ".py"], cwd=work, check=True)
    ledger = subprocess.check_output([sys.executable, "chains_fast.py"], cwd=work)
    if ledger != (root / "chains-fast.log").read_bytes():
        raise ValueError("Regenerated ledger differs")
    rows = [ast.literal_eval(line.split(" ", 2)[2]) for line in ledger.decode().splitlines()]
    if len(rows) != 22 or any(result for result, counts in rows):
        raise ValueError("Incomplete negative census")
    print("All 22 clean-private cases excluded.")
