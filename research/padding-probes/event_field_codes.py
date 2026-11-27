"""Aligned compiler-field codebooks and affine tests relative to unary support."""
from affine_relation import affine_hull


def field_codebooks(table, outputs, bottom):
    """Build a factory for unpinned raw/marker CodebookView objects.

    All positions use codes from the same source state and alphabet order.
    No ordering of the source labels is required.
    """
    state_ids = {q: i for i, q in enumerate(outputs)}
    top_ids = {bottom: 0}
    for (_, symbol, _), action in table.items():
        top_ids.setdefault(symbol, len(top_ids))
        if action[1] == 'push':
            top_ids.setdefault(action[2], len(top_ids))
    qbits = (len(state_ids)-1).bit_length()
    tbits = (len(top_ids)-1).bit_length()

    def factory(view):
        books = {}
        for v, domain in view.domains.items():
            if v == view.output:
                books[v] = {b: int(b) for b in domain}
                continue
            book = {}
            for row in domain:
                q, t = row.before
                r, s = row.after
                word = int(outputs[r])
                for value, width in ((top_ids[s],tbits),(state_ids[r],qbits),
                                     (top_ids[t],tbits),(state_ids[q],qbits),
                                     (int(row.bit or 0),1)):
                    word = (word << width) | value
                book[row] = word
            if len(set(book.values())) != len(book):
                raise ValueError('physical records collide on compiler boundary fields')
            books[v] = book
        return books
    return factory


def relative_hull(left, right, allowed, left_width, right_width):
    """Compute pair hull equations and all missing pairs with valid endpoints.

    The empty relation returns None. Every other result consists of
    (equations, rank of the difference span, packed valid omitted words).
    Both unary domain factors must be enforced separately.
    """
    for width in (left_width, right_width):
        if type(width) is not int or width < 0:
            raise ValueError('nonnegative width required')
    left, right = set(left), set(right)
    for words, width in ((left,left_width),(right,right_width)):
        if any(type(x) is not int or x < 0 or x.bit_length() > width for x in words):
            raise ValueError('endpoint codeword outside declared width')
    pairs = set(allowed)
    if any(x not in left or y not in right for x,y in pairs):
        raise ValueError('pair outside declared endpoints')
    if not pairs:
        return None
    words = {x | (y << left_width) for x,y in pairs}
    equations, dimension = affine_hull(words,left_width+right_width)
    holes = []
    for x in left:
        for y in right:
            if (x,y) in pairs:
                continue
            word = x | (y << left_width)
            if all((word & mask).bit_count() % 2 == rhs for mask,rhs in equations):
                holes.append(word)
    return equations, dimension, tuple(sorted(holes))
