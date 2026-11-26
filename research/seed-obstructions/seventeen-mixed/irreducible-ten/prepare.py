"""Generate the maximal and raw point/line dominance obligations."""
import argparse
import sys
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('output', type=Path)
parser.add_argument('--sixteen', type=Path, default=Path(__file__).resolve().parent/'source')
args = parser.parse_args()
sys.path.insert(0,str(args.sixteen))
from inputs import canonical, anchors, maximal, obligations

args.output.mkdir(exist_ok=True, parents=True)
with (args.output/'raw.in').open('w') as dest:
    for row in [canonical, *anchors, *maximal]:
        print(*row, file=dest)
with (args.output/'rel.txt').open('w') as dest:
    for row in obligations:
        print(*row, file=dest)
