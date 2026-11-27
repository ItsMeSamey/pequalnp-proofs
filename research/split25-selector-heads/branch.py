def branch_bound(rows, points, form):
    # For DNF the values below describe term satisfaction. For CNF they
    # describe clause falsification, so the signed clause literal is inverted.
    label = int(form == 'DNF')
    packed = [cell for cell,y,sig in rows if cell in points]
    signatures = {cell:sig for cell,y,sig in rows}
    opposite = [sig for _,y,sig in rows if y != label]
    if not opposite:
        return dict(lower=0, nonunits=0, decreasing_edges=[], packed=packed, constant_branch=True)
    units = []
    covered = set()
    for coordinate in range(25):
        values = {(sig >> coordinate) & 1 for sig in opposite}
        for value in {0,1} - values:
            hits = [c for c in packed if (signatures[c] >> coordinate) & 1 == value]
            if hits:
                covered.update(hits)
                units.append(dict(coordinate=coordinate, selected_value=value, packed_cells=hits))
    neg = {s:i for i,y,s in rows if y == 0}
    positive = [(i,s) for i,y,s in rows if y == 1]
    directional = []
    for j in range(25):
        bit = 1 << j
        for i,s in positive:
            if not s & bit and (s | bit) in neg:
                directional.append([j,i,neg[s | bit]])
                break
    k = len(packed)
    # At least k distinct terms or clauses are needed. Each point outside
    # the unit union needs a distinct nonunit output. A decreasing edge
    # requires a NOT of its coordinate. All three gate charges are disjoint.
    nonunits = k - len(covered)
    joins = max(0,k-1)
    return dict(lower=joins + nonunits + len(directional), packed=packed,
                joins=joins, nonunits=nonunits, packed_unit_coverage=sorted(covered),
                units=units, decreasing_edges=directional)


