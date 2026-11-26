"""List workspace Lean modules needed to replay the native T2 dichotomy."""
import hashlib
from pathlib import Path

base = Path(__file__).resolve().parent
visited = set()
table = []


def visit(module):
    if module in visited:
        return
    visited.add(module)
    path = base / f"{module}.lean"
    imports = []
    for line in path.read_text().splitlines():
        if line.startswith("import "):
            imports.extend(line.split()[1:])
    for dep in imports:
        if (base / f"{dep}.lean").exists():
            visit(dep)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    table.append(f"{module}\t{digest}\t{' '.join(imports)}")


visit("T2RegularOrDelete")
print("module\tsource_sha256\tdirect_imports")
print("\n".join(table))
