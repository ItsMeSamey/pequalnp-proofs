"""Validate four-OR receipts; complete status requires all 55 plus independent review."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT=Path(__file__).resolve().parent
FAMILY='L-meta-18272/exactly-four-productive-OR/at-most-seven-taps'
def need(test,message):
    if not test:raise ValueError(message)
def digest(data):return hashlib.sha256(data).hexdigest()
def sha(path):return digest(path.read_bytes())
def branch_reference():
    lines=(ROOT/'reference/orcut18272-complete.log').read_text().splitlines()
    rows=[list(map(int,re.fullmatch(r'shard (\d+) nodes 1 (\d+) (\d+) hits 0',s).groups())) for s in lines if s.startswith('shard ')]
    need([r[0] for r in rows]==list(range(55)),'invalid three-OR reference')
    return {f:(s,t) for f,s,t in rows}
def raw_values():return json.loads((ROOT/'instance/raw-masks.json').read_text())
def source():
    p=ROOT/'instance/statement.lean'
    need(sha(p)=='9ec4bd7fce25977e79676fd87f567c30812b34f80a264e9df1a9aeb6d972f84b','issued statement')
    c=ROOT/'source/orcut18272_four_coarse.c'
    need(sha(c)=='5f8979284034a3203d0b898ce3aa4e532a07d49d206ae9f8656a678b4deee5d3','C99 source')
    raw=json.loads((ROOT/'instance/raw-masks.json').read_text())
    for literal in (re.search(r'\[([^\]]+)\]\.getD',p.read_text())[1],re.search(r'raw\[11\]=\{([^}]+)\}',c.read_text())[1]):
        need(raw==list(map(int,re.findall(r'\d+',literal))),'raw values')
    return sha(p),sha(c)
def stream(path,f,start=0):
    sec=start;third=0;subtotal=total=leaves=0;closed=False
    text=hashlib.sha256()
    opener=gzip.open if path.suffix=='.gz' else open
    with opener(path,'rb') as fp:
        for line in fp:
            text.update(line)
            need(line.endswith(b'\n') and not closed,'trailing or unterminated line')
            words=line.decode('ascii').split()
            if words[:1]==['leaf']:
                need(len(words)==6 and words[:5]==['leaf',str(f),str(sec),str(third),'states'] and words[5].isdigit(),'unexpected leaf/hit')
                subtotal+=int(words[5]);third+=1
            elif words[:1]==['closed']:
                need(words==['closed',str(f),str(sec),'third-range','0',str(third),'states',str(subtotal)],'subtree closure')
                sec+=1;leaves+=third;total+=subtotal;subtotal=third=0
            elif words[:1]==['range-end']:
                need(words==['range-end',str(f),str(start),'10000','states',str(total)] and not third,'shard closure')
                closed=True
            else:raise ValueError('unexpected receipt or hit '+str(path))
    need(closed,'missing range-end '+str(path))
    return dict(first=f,second_prefixes=sec-start,third_leaves=leaves,fourth_states=total,sha256_text=text.hexdigest())
def legacy():
    d=ROOT/'reference/shard0'
    files=['guardmem.py','runmem.log','orcut18272-four-first0-1-13.log','orcut18272-four-first0-14-25.log','coarseC-0-26.log']
    need("['./orcut18272_four','0','0','1']" in (d/files[0]).read_text(),'legacy invocation')
    lines=(d/files[1]).read_text().splitlines()
    need('shard 0 states 1 1 105 13812 coarse 0 found 0' in lines and lines[-2]=='return 0','legacy first block')
    sec=1;third=0;states=13812;leaves=105
    for name in files[2:4]:
        for line in (d/name).read_text().splitlines():
            w=line.split()
            if w==['partial','0',str(sec)] or re.fullmatch(r'usage [0-9.]+ [0-9.]+',line):continue
            if sec==15 and line=='thirdblock 0 14 144 160 shard 0 states 1 1 0 0 coarse 0 found 0 0':continue
            if w[0]=='block':
                need(w[:5]==['block','0',str(sec),'shard','0'] and not third,'legacy block identity')
                param=w[5:];bound=None
            elif w[0]=='thirdblock':
                need(w[:4]==['thirdblock','0',str(sec),str(third)] and w[5:7]==['shard','0'],'legacy interval')
                bound=int(w[4]);param=w[7:]
            else:raise ValueError('legacy unexpected record')
            need(param[:3]==['states','1','1'] and param[5:]==['coarse','0','found','0','0'],'legacy hits')
            k,v=map(int,param[3:5]);need(k>0 and v>=0,'legacy counts')
            leaves+=k;states+=v
            if bound is None:sec+=1
            else:
                need(third+k<=bound,'overrun')
                third+=k
                # Following second index or EOF closes the split interval.
                if third<bound:sec+=1;third=0
    need(sec==26 and not third and states==534443,'legacy prefix total')
    tail=stream(d/files[-1],0,26)
    return dict(first=0,second_prefixes=26+tail['second_prefixes'],third_leaves=leaves+tail['third_leaves'],fourth_states=states+tail['fourth_states'],
                sha256_text=digest(''.join(name+' '+sha(d/name)+'\n' for name in files).encode()))
def split32(directory):
    names=['fast-32-0-10000.log.gz','fast-32-35-36-103-100000.log.gz','fast-32-36-10000.log.gz']
    parts=[directory/n for n in names]
    totals=[0,0];sec=third=sub=0
    for block,path in enumerate(parts[:2]):
        chunk=gzip.decompress(path.read_bytes())
        need(chunk.endswith(b'\n'),'truncated shard32 segment')
        lines=chunk.decode('ascii').splitlines()
        if block==1:
            need(lines[-2:]==['closed 32 35 third-range 103 121 states 2390','range-end 32 35 36 states 2390'],'shard32 resumed closure')
            lines=lines[:-2];before=sub
        for line in lines:
            w=line.split()
            if w[:1]==['leaf']:
                need(len(w)==6 and w[:5]==['leaf','32',str(sec),str(third),'states'] and w[5].isdigit(),'shard32 leaf')
                sub+=int(w[5]);third+=1
            else:
                need(block==0 and w==['closed','32',str(sec),'third-range','0',str(third),'states',str(sub)],'shard32 prefix closure')
                totals[0]+=third;totals[1]+=sub;sec+=1;third=sub=0
        if block==0:need((sec,third)==(35,103),'shard32 checkpoint boundary')
        else:need((sec,third,sub-before)==(35,121,2390),'shard32 resumed extent')
    tail=stream(parts[2],32,36)
    return dict(first=32,second_prefixes=36+tail['second_prefixes'],third_leaves=totals[0]+third+tail['third_leaves'],
                fourth_states=totals[1]+sub+tail['fourth_states'],sha256_text=digest(''.join(n+' '+sha(p)+'\n' for n,p in zip(names,parts)).encode()))
def main(args):
    need(args.receipts.is_dir(),'receipt directory missing')
    statement,code=source();expected=branch_reference();rows={}
    if args.use_legacy_zero:rows[0]=legacy()
    if args.split32:rows[32]=split32(args.receipts)
    for p in sorted(args.receipts.glob('fast-*-0-10000.log.gz')):
        m=re.fullmatch(r'fast-(0|[1-9]\d*)-0-10000.log.gz',p.name)
        need(m is not None,'invalid first shard name')
        f=int(m[1])
        if f==32 and args.split32:continue
        need(0<=f<55 and f not in rows,'duplicate or out-of-domain shard')
        rows[f]=stream(p,f)
        rows[f]['sha256_gzip']=sha(p)
    for f,r in rows.items():need((r['second_prefixes'],r['third_leaves'])==expected[f],f'shard {f} prefix counts')
    reviewed=set()
    for manifest in args.review_manifest:
        obj=json.loads(manifest.read_text())
        # A partial frontier never contributes to release coverage.
        entries=obj.get('receipts',obj.get('completed',[]))
        for row in entries:
            f=row['first']
            if f not in rows:continue
            for k in ('second_prefixes','third_leaves','fourth_states','sha256_text') + (('sha256_gzip',) if 'sha256_gzip' in rows[f] else ()):
                need(row[k]==rows[f][k],f'receipt mismatch at {f}/{k}')
            reviewed.add(f)
    canonical=[{k:r[k] for k in ('first','second_prefixes','third_leaves','fourth_states','sha256_text')} for _,r in sorted(rows.items())]
    fingerprint=digest(json.dumps(canonical,sort_keys=True,separators=(',',':')).encode())
    if args.producer_index:
        vals=raw_values();first=sorted({a|b for i,a in enumerate(vals) for b in vals[:i]})
        args.producer_index.write_text(json.dumps([dict(**x,first_mask=first[x['first']],hits=0) for x in canonical],indent=2)+'\n')
    missing=sorted(set(range(55))-rows.keys())
    verified=False
    if args.confirmation:
        need(args.confirmation_sha256 and sha(args.confirmation)==args.confirmation_sha256,'independently supplied confirmation digest')
        conf=json.loads(args.confirmation.read_text())
        need(args.normalization and sha(args.normalization)==conf['normalization_evidence_sha256'],'independent normalization evidence digest')
        need(not missing and conf['family']==FAMILY and conf['reviewer']=='/root/site_team_07' and
             conf['statement_sha256']==statement and conf['source_sha256']==code and
             conf['canonical_receipt_set_sha256']==fingerprint and conf['scope']=='independent semantic replay and adjusted canonical count correspondence',
             'independent replay scope or producer evidence mismatch')
        checks=conf['shards']
        need(len(checks)==55 and sorted(x['first'] for x in checks)==list(range(55)), 'independent shard set')
        ids=sorted({a|b for i,a in enumerate(raw_values()) for b in raw_values()[:i]})
        for x in checks:
            f=x['first']
            need(x['reviewed'] is True and x['hits']==0 and x['first_mask']==ids[f],'independent semantic replay')
            need(x['receipt_sha256_text']==rows[f]['sha256_text'],'unreviewed producer receipt')
            need(type(x['raw_fourths']) is int and x['raw_fourths']>=0 and type(x['signed_adjustment']) is int and
                 x['raw_fourths']+x['signed_adjustment']==rows[f]['fourth_states'],'adjusted fourth-count correspondence')
        verified=True
    print(json.dumps(dict(status='verified' if verified else 'pending',absent_first=missing,closed_first=sorted(rows),
                          fourth_states=sum(r['fourth_states'] for r in rows.values()),canonical_receipt_set_sha256=fingerprint,
                          review_matched_first=sorted(reviewed),independent_confirmation=verified),indent=2))
    return 0 if verified or args.status else 3
if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('receipts',type=Path);ap.add_argument('--use-legacy-zero',action='store_true')
    ap.add_argument('--producer-index',type=Path);ap.add_argument('--normalization',type=Path);ap.add_argument('--split32',action='store_true');ap.add_argument('--review-manifest',type=Path,action='append',default=[]);ap.add_argument('--confirmation',type=Path);ap.add_argument('--confirmation-sha256');ap.add_argument('--status',action='store_true')
    try:sys.exit(main(ap.parse_args()))
    except (OSError,ValueError,TypeError,IndexError,KeyError,AttributeError) as exc:sys.exit('verification failed: '+str(exc))
