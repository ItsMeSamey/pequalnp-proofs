"""Seven selector profiles with six or five unconditional activations."""
def profiles(p):
    full = (1 << 128) - 1
    pos = [sum(1 << n for n in range(128) if n >> i & 1) for i in range(7)]
    def join(parts):
        out = 0
        for v in parts:
            out |= v
        return out
    found = set()
    for t in range(1,p+1):
        u = join(pos[:t])
        if p == 6:
            found.add((full,)*6+(u,))
            continue
        gated = u & pos[p]
        for a in range(t+1):
            for b in range(t-a+1):
                for c in range(p-t+1):
                    pure = join(pos[:a] + [full ^ x for x in pos[a:a+b]] + pos[t:t+c])
                    for extra in (0,gated,u):
                        v = pure | extra
                        if 0 < v < full:
                            found.add((full,)*p+(u,v))
    return sorted(found)
if __name__ == '__main__':
    from pathlib import Path
    for p in (5,6):
        rows = profiles(p)
        path = Path(__file__).with_name(f'full{p}.tsv')
        path.write_text(''.join(' '.join(map(str,row))+'\n' for row in rows))
        print(p,len(rows))
