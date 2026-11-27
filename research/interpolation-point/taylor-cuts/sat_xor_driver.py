"""Staged Linux SAT+XOR driver. Optional stages run in killable child processes."""
import math
import multiprocessing as mp
import pickle
import tempfile
from time import monotonic

STAGES=("anf","resource","choice","closure_cover","horn","semilattice","tree","brute")
MAX_RESULT_BYTES=8 << 20
DEFAULTS=dict(anf=.5,resource=.5,choice=.5,closure_cover=.5,horn=.5,semilattice=.5,tree=.5,brute=None)


def _valid(x,n,clauses,rows):
    return (type(x) is int and 0<=x<1<<n
            and all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
            and all((x&a).bit_count()%2==b for a,b in rows))


def _record_visited(metrics,count):
    if count.bit_length()<=64:
        metrics["visited"]=count
    else:
        metrics["visited_bits"]=count.bit_length()
        metrics["visited_is_power_of_two"]=(count & (count-1))==0


def _run(name,n,clauses,rows):
    """status, witness, metrics, additional implied affine rows."""
    from affine_cell_energy import solve
    metrics={}
    def finish(w):
        return ("UNSAT" if w is None else "SAT",w,metrics,())
    if name=="anf":
        from cnf_anf_prepass import consequences,replay
        conflict,derived=consequences(n,clauses)
        if conflict is not None:
            if not replay(n,clauses,0,1,conflict):
                raise AssertionError("invalid ANF contradiction")
            metrics["contradiction_source_count"]=conflict.bit_count()
            return finish(None)
        extras=[]
        for a,b,proof in derived:
            if not replay(n,clauses,a,b,proof):
                raise AssertionError("invalid ANF consequence")
            extras.append((a,b))
        chart=solve(n,(*rows,*extras))
        metrics["derived_rows"]=len(extras)
        if chart is None:
            return finish(None)
        x,ker=chart
        metrics["free_dimension"]=len(ker)
        if _valid(x,n,clauses,rows):
            return finish(x)
        return "CONTINUE",None,metrics,tuple(extras)
    if name=="resource":
        from affine_resource_cliques import resource_certificate,verify
        cert=resource_certificate(n,clauses)
        if cert is None:
            return "SKIP",None,{"reason":"no verified resource certificate"},()
        if not verify(n,clauses,cert):
            raise AssertionError("invalid resource certificate")
        metrics["certificate_terms"]=len(cert)
        return finish(None)
    if name=="choice":
        from choice_cover_multi_xor import solve_long_covers
        parity=[(tuple(i+1 for i in range(n) if a>>i&1),b) for a,b in rows]
        try:
            status,x,stalled=solve_long_covers(n,clauses,parity)
        except ValueError as exc:
            return "SKIP",None,{"reason":str(exc)},()
        metrics.update(stalled=len(stalled),cover_rows=sum(len(c)>=3 for c in clauses))
        return status,x,metrics,()
    if name=="closure_cover":
        if any(len(c)>2 for c in clauses):
            return "SKIP",None,{"reason":"requires normalized clause width at most two"},()
        from two_sat_closure_cover import solve as solve_cover
        x,details=solve_cover(n,clauses,rows)
        metrics.update(details)
        return finish(x)
    if name in ("horn","semilattice"):
        core=[c for c in clauses if sum(l>0 for l in c)<=1]
        extra=[c for c in clauses if sum(l>0 for l in c)>1]
        metrics.update(core_clauses=len(core),exceptions=len(extra))
        if name=="horn":
            from horn_closure_xor import effective_xor_rank,solve_horn_exceptions
            r=effective_xor_rank(n,core,rows)
            if r is None:
                return finish(None)
            metrics["effective_rank"]=r
            bound=0
            for j in range(min(n,r+len(extra))+1):
                bound+=math.comb(n,j)
                if bound>50000:
                    return "SKIP",None,dict(metrics,reason="seed bound exceeds 50000"),()
            metrics["seed_bound"]=bound
            return finish(solve_horn_exceptions(n,core,extra,rows))
        from horn_semilattice import SupportBudgetExceeded,compile_horn_residual
        try:
            out=compile_horn_residual(n,core,extra,rows,max_support=1024)
        except SupportBudgetExceeded:
            return "SKIP",None,dict(metrics,reason="support exceeds 1024",peak_lower_bound=1025),()
        metrics.update(peak=out.peak,closure_queries=out.closure_queries,support=len(out.support))
        return finish(out.witness)
    if name=="tree":
        from semantic_tree_solver import minimize
        leaves=[[(1,[(1<<(abs(l)-1),int(l<0)) for l in c])] for c in clauses]
        nodes=list(range(len(leaves)))
        while len(nodes)>1:
            nodes=[(nodes[i],nodes[i+1]) if i+1<len(nodes) else nodes[i] for i in range(0,len(nodes),2)]
        opt=minimize(n,leaves,nodes[0] if nodes else None,rows,stats=metrics)
        metrics["leaf_count"]=len(leaves)
        if opt is not None:
            metrics["minimum_violations"]=int(opt[0])
        return finish(None if opt is None or opt[0] else opt[1])
    if name!="brute":
        raise ValueError("unknown stage")
    chart=solve(n,rows)
    if chart is None:
        return finish(None)
    x,ker=chart
    metrics["free_dimension"]=len(ker)
    for index in range(1<<len(ker)):
        if index:
            x^=ker[(index & -index).bit_length()-1]
        if _valid(x,n,clauses,rows):
            _record_visited(metrics,index+1)
            return finish(x)
    _record_visited(metrics,1<<len(ker))
    return finish(None)


def _worker(output,args):
    try:
        result=_run(*args)
    except Exception as exc:
        result=("ERROR",None,{"reason":f"{type(exc).__name__}: {exc}"},())
    wire=pickle.dumps(result)
    # Allow the declared input dimension to determine the witness allowance only.
    witness_limit=max(MAX_RESULT_BYTES,2*((args[1]+7)//8)+4096)
    metadata_size=len(pickle.dumps((result[0],None,result[2],result[3])))
    if metadata_size>MAX_RESULT_BYTES or len(wire)>witness_limit:
        wire=pickle.dumps(("ERROR",None,{"reason":"worker result exceeds export limit"},()))
    output.write(wire)
    output.flush()


def _timed(args,seconds):
    # The child writes an inherited anonymous file so a large result can never
    # block on pipe capacity. Join covers computation and serialization.
    start=monotonic()
    ctx=mp.get_context("fork")
    with tempfile.TemporaryFile() as output:
        proc=ctx.Process(target=_worker,args=(output,args))
        proc.start()
        try:
            remaining=None if seconds is None else max(0,start+seconds-monotonic())
            proc.join(remaining)
            if proc.is_alive():
                return "TIMEOUT",None,{"limit_seconds":seconds},()
            if proc.exitcode:
                return "ERROR",None,{"reason":f"worker exit code {proc.exitcode}"},()
            output.seek(0)
            try:
                return pickle.load(output)
            except (EOFError,pickle.UnpicklingError):
                return "ERROR",None,{"reason":"worker result missing or invalid"},()
        finally:
            if proc.is_alive():
                proc.kill()
            proc.join()
            proc.close()


def solve_sat_xor(n,clauses,xor_rows=(),*,budgets=None,stages=None):
    """Return {status,witness,reports,metrics}; with no cap brute is a complete fallback.

    Budgets map stage names to hard wall seconds (None unbounded; zero skips).
    The worker deadline covers startup, computation and serialization. Parent
    validation, decoding and process cleanup add overhead outside the deadline.
    Input literals are signed and one-based. XOR rows are (bit mask, right side).
    """
    if type(n) is not int or n<0:
        raise ValueError("invalid dimension")
    raw=tuple(tuple(c) for c in clauses)
    rows=tuple(tuple(r) for r in xor_rows)
    if any(type(l) is not int or not 1<=abs(l)<=n for c in raw for l in c):
        raise ValueError("invalid literal")
    if any(len(r)!=2 or type(r[0]) is not int or not 0<=r[0]<1<<n or not isinstance(r[1],int) or r[1] not in (0,1) for r in rows):
        raise ValueError("invalid parity equation")
    canonical=[]
    for c in raw:
        literals=set(c)
        if not any(-l in literals for l in literals):
            canonical.append(tuple(dict.fromkeys(c)))
    cnf=tuple(canonical)
    names=STAGES if stages is None else tuple(stages)
    limits=DEFAULTS.copy()
    limits.update({} if budgets is None else budgets)
    if any(i not in STAGES for i in (*names,*limits)):
        raise ValueError("unknown stage")
    if any(s is not None and (not isinstance(s,(float,int)) or not math.isfinite(s) or s<0)
           for s in limits.values()):
        raise ValueError("invalid time budget")
    reports=[]
    info=dict(variables=n,clauses=len(raw),normalized_clauses=len(cnf),xor_rows=len(rows),
              max_width=max(map(len,cnf),default=0))
    implied=rows
    for name in names:
        start=monotonic()
        if limits[name]==0:
            status,x,metrics,added="SKIP",None,{"reason":"budget zero"},()
        else:
            status,x,metrics,added=_timed((name,n,cnf,implied),limits[name])
        if status=="SAT" and not _valid(x,n,raw,rows):
            status,x,metrics="ERROR",None,dict(metrics,reason="original witness validation failed")
        reports.append(dict(stage=name,status=status,elapsed=monotonic()-start,metrics=metrics))
        if status in ("SAT","UNSAT"):
            return dict(status=status,witness=x,reports=reports,metrics=info)
        if status=="CONTINUE":
            implied=tuple(dict.fromkeys((*implied,*added)))
    return dict(status="UNKNOWN",witness=None,reports=reports,metrics=info)
