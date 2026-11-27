"""Emit packed linear certificates from a saved three-name star transcript."""
import json
from pathlib import Path
import sys


def rows_for(pairs,w,h):
    pivots={}
    for v,z in pairs:
        while v and (i:=v.bit_length()-1) in pivots:
            x,y=pivots[i]; v^=x; z^=y
        if v: pivots[v.bit_length()-1]=v,z
        elif z: raise ValueError("inconsistent images")
    def image(v):
        z=0
        for i in sorted(pivots,reverse=True):
            if (v>>i)&1:
                v^=pivots[i][0]; z^=pivots[i][1]
        return z
    return [sum(((image(1<<i)>>j)&1)<<i for i in range(w)) for j in range(h)]


def extension(initial,cols):
    basis={}; extra=[]
    for i,v in enumerate([*initial,*cols]):
        x=v
        while x:
            j=x.bit_length()-1
            if j not in basis:
                basis[j]=x
                if i>=len(initial): extra.append(v)
                break
            x^=basis[j]
    return extra


def extract(row):
    cert=row['certificate']
    if row['forced'] or cert['terminal']!='star':
        raise ValueError('expected an unpinned star transcript')
    if len(row['names']) != 3 or any(type(v) is not int or v < 0 for v in row['names'] + row['columns']):
        raise ValueError("expected three names and nonnegative integer columns")
    t,a,b=row['names']; c=t^a^b
    vals=[a,b,c,a^b,b^c,c^a,*row['columns']]
    w=max(v.bit_length() for v in vals)
    gs=[list(range(len(vals)))]; steps=[]
    for s in cert['steps']:
        old=gs[-1]
        local=s['keep']
        if (not isinstance(local,list) or any(type(i) is not int or not 0 <= i < len(old) for i in local)
                or sorted(set(local)) != local or local[:6] != list(range(6))):
            raise ValueError("invalid retained positions")
        if (not isinstance(s['interface'],list) or len(s['interface']) > 2
                or any(type(v) is not int or not 0 < v < (1 << w) for v in s['interface'])):
            raise ValueError("invalid interface basis")
        keep=[old[i] for i in local]
        left=[vals[i] for i in keep]
        right=[vals[i] for i in old if i not in keep]
        extra=extension(s['interface'],right)
        rows=rows_for([(v,v) for v in left]+[(v,0) for v in extra],w,w)
        table=[0]
        for v in s['interface']: table += [v^x for x in table]
        gs.append(keep+list(range(len(vals),len(vals)+len(table)-1)))
        vals.extend(table[1:]); steps.append((keep,rows,table))
    edges=cert['edges']
    ids={v:i for i,v in enumerate(sorted({v for e in edges for v in e}))}
    edges=[(ids[u],ids[v]) for u,v in edges]
    inc=[(1<<u)^(1<<v) for u,v in edges]; h=len(ids)
    last=[vals[i] for i in gs[-1]]
    return vals,w,gs,steps,edges,h,inc,rows_for(zip(last,inc),w,h),rows_for(zip(inc,last),h,w)


def array(name,dom,typ,vals):
    return f'def {name} (i : {dom}) : {typ} := ({vals} : List ({typ})).getD i.val 0'


def fs(vals,typ):
    return f'({vals} : List ({typ})).toFinset'


def lean(row, raw=None):
    vals,w,gs,steps,edges,h,inc,fwd,rev=extract(row)
    n=len(vals); t=len(steps)
    o=['import ThreeNamePackedPins','import ThreeNameProjectionStep','import ThreeNameRejection',
       'namespace ThreeNamePackedExample','open ThreeNamePacked ThreeNameChain ThreeNameSplitCircuit',
       'open scoped BigOperators','set_option maxRecDepth 30000','set_option maxHeartbeats 4000000',
       f'abbrev I := Fin {n}',array('words','I',f'BitVec {w}',vals),'def roots : Finset I := {0,1,2}']
    o += [Path(__file__).with_name('diagonal.lean.in').read_text()]
    for i,g in enumerate(gs):
        o += [f'def g{i} : Finset I := '+fs(g,'I'),f'def p{i} : Carrier I (Vec {w}) := ⟨g{i},fun e => decode (words e)⟩']
    for i,(keep,rows,tab) in enumerate(steps):
        o += [f'def x{i} : Finset I := '+fs(keep,'I'), array(f'rows{i}',f'Fin {w}',f'BitVec {w}',rows),
              f'def tab{i} : Finset (BitVec {w}) := '+fs(tab,f'BitVec {w}'),
              f'def step{i} : Step roots p{i} p{i+1} :=']
        if all(v in (0,1<<j) for j,v in enumerate(rows)):
            o += [f'  diagonalStep words g{i} g{i+1} roots x{i} {sum(rows)} tab{i} (by decide)']
        else:
            o += [f'  ThreeNameProjectionStep.checkedStep roots x{i} p{i} p{i+1} (rowHom rows{i}) (tab{i}.image decode) (by decide)']
    o.append(f'def path : Path roots p0 p{t} := '+''.join(f'.cons step{i} (' for i in range(t))+f'.nil p{t}'+')'*t)
    full=[0]*n; tails=[0]*n; heads=[0]*n
    for i,v,(a,b) in zip(gs[-1],inc,edges): full[i],tails[i],heads[i]=v,a,b
    center,=set(edges[0])&set(edges[1])&set(edges[2])
    def sparse(rows,width):
        result=[]
        for j in range(width):
            image=sum(((v>>j)&1)<<i for i,v in enumerate(rows))
            if image:
                result.append((j,image))
        return result
    o += [array('incs','I',f'BitVec {h}',full),array('tails','I',f'Fin {h}',tails),array('heads','I',f'Fin {h}',heads),
          array('frows',f'Fin {h}',f'BitVec {w}',fwd),array('rrows',f'Fin {w}',f'BitVec {h}',rev),
          Path(__file__).with_name('map-word.lean.in').read_text(),
          f'def fops : List (Fin {w} × BitVec {h}) := {sparse(fwd,w)}',
          f'def rops : List (Fin {h} × BitVec {w}) := {sparse(rev,h)}',
          f'theorem fchecked : ∀ e ∈ g{t}, sparseRun fops (words e) = incs e := by decide',
          f'theorem rchecked : ∀ e ∈ g{t}, sparseRun rops (incs e) = words e := by decide',
          Path(__file__).with_name('incidence-word.lean.in').read_text(),
          f'theorem incidenceWord : ∀ e ∈ g{t}, decode (incs e) = ThreeNameIncidenceRank.incidence tails heads e := endpoint_bit_sound g{t} incs tails heads (by decide)',
          f'theorem terminalKernel (T : Finset I) (ht : T ⊆ g{t}) :',
          '(∑ i ∈ T, decode (words i)) = 0 ↔ (∑ i ∈ T, ThreeNameIncidenceRank.incidence tails heads i) = 0 := by',
          '  rw [← Finset.sum_congr rfl (fun i hi => incidenceWord i (ht hi))]',
          f'  exact sparseKernel g{t} words incs fops rops fchecked rchecked T ht',
          'theorem noRooted : ¬ Rooted p0 roots := by',
          f'  apply rejects (R := roots) (p := p0) (q := p{t}) (by exact ⟨0, by decide⟩) (fun v => by funext i; exact (show ∀ z : ZMod 2, z+z=0 by decide) (v i)) path',
          '  rintro ⟨C,hg,hr,hc⟩',
          '  have gc : Circuit (ThreeNameIncidenceRank.incidence tails heads) C :=',
          '    ⟨hc.1,(terminalKernel C hg).mp hc.2.1,fun T ht hn z => hc.2.2 T ht hn ((terminalKernel T (ht.trans hg)).mpr z)⟩',
          f'  exact ThreeNameIncidenceRank.circuit_excludes_three tails heads C gc {center} 0 1 2 (by decide) (by decide) (by decide) hr (by decide) (by decide) (by decide)',
          array('ordinary',f'Fin {len(row["columns"])}',f'BitVec {w}',row['columns']),
          f'def originalLabel (i : Fin {len(row["columns"])}) : I := ⟨i.val+6,by have := i.isLt; omega⟩',
          'theorem original_positions : ∀ i, words (originalLabel i) = ordinary i ∧ originalLabel i ∈ g0 := by decide',
          Path(__file__).with_name('root-masks.lean.in').read_text().replace('WIDTH',str(w)),
          'theorem noPhysical (S : Finset I) (hg : S ⊆ g0) (dj : Disjoint roots S)',
          '    (total : (∑ i ∈ S, p0.col i) = ∑ i ∈ roots, p0.col i)',
          '    (trace : ∀ Q ⊆ S, ∀ P ⊆ roots, (∑ i ∈ Q, p0.col i) = (∑ i ∈ P, p0.col i) →',
          '      (∑ i ∈ P, p0.col i) = 0 ∨ (∑ i ∈ P, p0.col i) = ∑ i ∈ roots, p0.col i) : False := by',
          '  have rn : roots.Nonempty := ⟨0, by decide⟩',
          '  have ind : Independent p0.col roots := root_independent',
          '  have binary : ∀ v : Vec '+str(w)+', v+v=0 := fun v => by funext i; exact (show ∀ z : ZMod 2, z+z=0 by decide) (v i)',
          '  obtain ⟨C,hC,hr,hc⟩ := ThreeNameRootLift.from_trace p0.col roots S rn dj binary ind total trace',
          '  exact noRooted ⟨C,hC.trans (Finset.union_subset (by decide : roots ⊆ g0) hg),hr,hc⟩',
          '#print axioms noPhysical','#print axioms noRooted','end ThreeNamePackedExample']
    if raw is not None:
        if raw['forced'] != [0] or raw['columns'][0] != 3:
            raise ValueError("the pinned demonstration expects original pin 0 with word 3")
        m=len(raw['columns'])
        target,a,b=raw['names']; c=target^a^b
        padded=[a,b,c,a^b,b^c,c^a]
        o[-1:-1]=[
            f'abbrev Raw := Fin {m}',array('orig','Raw',f'BitVec {w}',raw['columns']),
            f'def pinTable : ThreeNamePackedPins.Table {w} := [(1,3)]',
            f'def pivotSource (_ : Fin {w}) : List Raw := [0]',
            'theorem pinOK : ThreeNamePackedPins.check orig [0] pinTable pivotSource = true := by decide',
            f'def rawSite (i : Fin {len(row["columns"])}) : Raw := ⟨i.val+1,by have := i.isLt; omega⟩',
            'theorem optional_word_replay : ∀ j, ThreeNamePackedPins.run pinTable (orig (rawSite j)) = words (originalLabel j) := by decide',
            f'theorem six_name_replay : ({padded} : List (BitVec {w})).map (ThreeNamePackedPins.run pinTable) =',
            '    [words 0,words 1,words 2,words 3,words 4,words 5] := by decide',
            f'theorem target_replay : ThreeNamePackedPins.run pinTable ({target} : BitVec {w}) = words 0 ^^^ words 1 ^^^ words 2 := by decide',
            'theorem all_original_selections (name : ((Fin 2 → ZMod 2) × ZMod 2) →ₗ[ZMod 2] Vec '+str(w)+') (R : Finset Raw) :',
            '    ThreeNamePinReduction.Exact (fun i => decode (ThreeNamePackedPins.run pinTable (orig i)))',
            '      ((ThreeNamePackedPins.asLinear pinTable).comp name) R ↔',
            '    ThreeNamePinReduction.Exact (fun i => decode (orig i)) name (([0] : List Raw).toFinset ∪ R) :=',
            '  ThreeNamePackedPins.checked_lift_iff orig [0] pinTable pivotSource pinOK name R',
            '#print axioms all_original_selections']
        host = Path(__file__).with_name('raw-host.lean.in').read_text()
        for key, value in [('WIDTH', w), ('TARGET', target), ('COMPA', a), ('COMPB', b)]:
            host = host.replace(key, str(value))
        o[-1:-1] = [host]
    return '\n'.join(o)+'\n' 


if __name__=='__main__':
    data=json.loads(Path(sys.argv[1]).read_text())
    if isinstance(data,dict):
        raw=data['no']; q=data['quotient']
        if (raw['forced']!=[0] or raw['columns'][0]!=3 or q['forced'] or q['certificate']!=raw['certificate']
                or any(type(v) is not int or v<0 for v in raw['names']+raw['columns'])):
            raise ValueError('invalid saved pin=3 replay')
        normalize=lambda v: v^3 if v & 2 else v
        if ([normalize(v) for v in raw['columns'][1:]]!=q['columns'] or
                [normalize(v) for v in raw['names']]!=q['names']):
            raise ValueError('saved quotient words disagree with original ordered pivot replay')
        result=lean(q,raw)
    else:
        result=lean(data[int(sys.argv[3]) if len(sys.argv)>3 else 0])
    out=Path(sys.argv[2])
    start=result.index('abbrev I :=')
    split1=result.index('def x2 :') if 'def x2 :' in result else result.index('def path :')
    split2=result.index('def incs (')
    split3=result.index('abbrev Raw :=') if 'abbrev Raw :=' in result else result.rindex('end ThreeNamePackedExample')
    namespace='namespace ThreeNamePackedExample\nopen ThreeNamePacked ThreeNameChain ThreeNameSplitCircuit\nopen scoped BigOperators\nset_option maxRecDepth 30000\nset_option maxHeartbeats 4000000\n'
    end='end ThreeNamePackedExample\n'
    for mod,imports,chunk in [
        ('ThreeNamePackedSteps01','import ThreeNamePacked\nimport ThreeNameProjectionStep',result[start:split1]),
        ('ThreeNamePackedSteps2','import ThreeNamePackedSteps01',result[split1:split2]),
        ('ThreeNamePackedTerminal','import ThreeNamePackedSteps2\nimport ThreeNameRejection',result[split2:split3]),
        (out.stem,'import ThreeNamePackedTerminal\nimport ThreeNamePackedPins',result[split3:-len(end)])]:
        out.with_name(mod+'.lean').write_text(imports+'\n'+namespace+chunk+end)
