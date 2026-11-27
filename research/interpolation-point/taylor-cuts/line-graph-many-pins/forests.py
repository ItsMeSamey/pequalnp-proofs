def supports(neighbors, roots, forbidden, limit):
    """Stream odd-side supports (duplicates allowed) for the two boundary tests."""
    roots=tuple(roots)
    active=set(roots)
    def visit(root_index, stack, left):
        if not stack:
            if root_index==len(roots):
                yield frozenset(active)
            else:
                yield from visit(root_index+1, (roots[root_index],), left)
            return
        yield from visit(root_index, stack[:-1], left)
        if left:
            for v in neighbors[stack[-1]]:
                if v not in active and v not in forbidden:
                    active.add(v)
                    yield from visit(root_index, stack+(v,), left-1)
                    active.remove(v)
    yield from visit(0, (), limit)
