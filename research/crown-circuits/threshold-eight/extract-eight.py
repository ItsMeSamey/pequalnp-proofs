from pathlib import Path
import sys
profiles=Path(sys.argv[1]).read_text().splitlines()
for line in Path(sys.argv[2]).read_text().splitlines():
    parts=line.split()
    if int(parts[4]):
        i=int(parts[0])
        print(i,profiles[i])
