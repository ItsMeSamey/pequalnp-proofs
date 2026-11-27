"""Replay the five-left/seven-right exclusion in an extracted, sealed packet."""
import argparse, hashlib, json, subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parent
def check(ok,message):
    if not ok:raise ValueError(message)
def verify_hashes():
    for line in (root/'SHA256SUMS').read_text().splitlines():
        expected,name=line.split('  ',1)
        check(hashlib.sha256((root/name).read_bytes()).hexdigest()==expected,('hash',name))
def run(*args):
    output=subprocess.check_output(args,cwd=root,text=True)
    print(args[1],output.strip().splitlines()[-1],flush=True)
    return output
def data(name):return json.loads((root/name).read_text())

parser=argparse.ArgumentParser()
parser.add_argument('--recompute-imports',action='store_true')
opt=parser.parse_args()
verify_hashes()
if opt.recompute_imports:
    r=json.loads(run('node','cut199-tree-two-hit/verify.cjs'))
    check(r==data('cut199-tree-two-hit/replay.json'),'four-port cost receipt')
    r=json.loads(run('node','cut199-free-and-right-six.cjs'))
    check(r['optimum']==6,'minimum free meet cost')
    run('node','cut199-m12-seven-meet-banks.cjs')
    check(len(data('cut199-m12-seven-meet-banks.json'))==1615,'seven-gate meet banks')
    r=json.loads(run('node','cut199-m12-face-three-guards.cjs','7'))
    check((r['states'],r['goalBanks'],r['termBanks'])==(1569329,512001,0),'seven-gate three guards')
    r=json.loads(run('node','cut199-m12-face-four-guards-seven.cjs'))
    check((r['banks'],r['count'],r['pass'],r['hits'])==(1615,27,0,0),'seven-gate four guards')
run(sys.executable,'cut199_all_five_left.py')
run(sys.executable,'cut199_all_five_modules.py')
check(data('cut199-all-five-modules.json')==[[8,16]]*504,'donor left masks')
run('node','replay_cut199_onefork_control.cjs')
run('node','cut199-three-guard-favorable.cjs')
run('node','cut199-four-guard-singletons.cjs')
run('node','cut199-four-guard-favorable.cjs','cut199-four-guard-singletons.json','cut199-four-guard-favorable.json')
check(data('cut199-four-guard-favorable.json')==[],'four guards')
run('node','cut199_contract_quartets.cjs')
run(sys.executable,'cut199_contract_support.py')
run('node','cut199_contract_favorable.cjs')
run(sys.executable,'cut199_contract_templates.py')
run('node','cut199_contract_syntax.cjs')
run('node','cut199-contract-positive.cjs')
r=data('cut199-contraction-syntax-results.json')
check(len(r)==40 and all(t['tree'] is None for t in r),'contraction chart')
verify_hashes()
print('All five-left seven-right branches verified for 12 mixed gates and total size at most 21.')
