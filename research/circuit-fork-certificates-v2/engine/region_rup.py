"""Dependency-free RUP verification for an in-memory DIMACS clause database."""
from collections import defaultdict

class RupChecker:
    """Monotone database: ignoring deletion hints retains only implied lemmas."""
    def __init__(self, nvars, clauses):
        self.nvars = nvars
        self.watches = defaultdict(list)
        self.units = []
        self.inconsistent = False
        for c in clauses:
            self.add(c)

    def add(self,c):
        clause = list(dict.fromkeys(c))
        if any(-lit in clause for lit in clause):
            return
        if not clause:
            self.inconsistent = True
        elif len(clause)==1:
            self.units.append(clause[0])
        else:
            self.watches[clause[0]].append(clause)
            self.watches[clause[1]].append(clause)

    def conflicts(self,clause):
        if self.inconsistent:
            return True
        # -1, 0, 1 denote false, unassigned, true for the positive variable.
        values = [0]*(self.nvars+1)
        queue = self.units+[-lit for lit in clause]
        for literal in queue:  # Python lists include newly appended implications.
            i = abs(literal)
            sign = 1 if literal>0 else -1
            if values[i]==sign:
                continue
            if values[i]==-sign:
                return True
            values[i]=sign
            watched = self.watches[-literal]
            k=0
            while k<len(watched):
                c=watched[k]
                if c[0]==-literal:
                    c[0],c[1]=c[1],c[0]
                other=c[0]
                other_sign=1 if other>0 else -1
                if values[abs(other)]==other_sign:
                    k+=1
                    continue
                for j in range(2,len(c)):
                    alternate=c[j]
                    if values[abs(alternate)] != (-1 if alternate>0 else 1):
                        c[1],c[j]=alternate,c[1]
                        watched[k]=watched[-1]
                        watched.pop()
                        self.watches[alternate].append(c)
                        break
                else:
                    if values[abs(other)]==-other_sign:
                        return True
                    queue.append(other)
                    k+=1
        return False

    def verify(self,proof):
        additions=0
        ended=False
        with proof.open(encoding='ascii') as f:
            for line_no,line in enumerate(f,1):
                parts=line.split()
                if not parts or parts[0]=='c':
                    continue
                if ended:
                    raise ValueError(f'proof continues after empty clause at line {line_no}')
                deletion=parts[0]=='d'
                if deletion:
                    parts=parts[1:]
                if not parts or parts[-1]!='0':
                    raise ValueError(f'unterminated clause at line {line_no}')
                c=[int(x) for x in parts[:-1]]
                if any(not 0<abs(lit)<=self.nvars for lit in c):
                    raise ValueError(f'invalid literal at line {line_no}')
                if deletion:
                    continue
                if not self.conflicts(c):
                    raise ValueError(f'clause fails reverse unit propagation at line {line_no}')
                self.add(c)
                additions+=1
                ended=not c
        if not ended:
            raise ValueError('proof does not finish with a verified empty clause')
        return additions


