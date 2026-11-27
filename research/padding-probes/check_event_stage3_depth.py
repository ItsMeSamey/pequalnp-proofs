"""Optional preregistered Stage 3 long-path control, intended only for scheduler04."""
from itertools import pairwise

import event_blocks
import event_block_solver
from padding_cnf import encode
from stack_padding import constant_dpda


def main():
    n = 100
    aliases = list(range(1, n + 2))
    word = encode([], n, 0)
    length = len(word)
    assert length > 1000
    tree = event_blocks.decompose(range(length + 1), pairwise(range(length + 1)))
    assert tree['status'] == 'ok' and tree['blocks'] == length and tree['width'] == 1
    assert len(tree['tree_edges']) == len(tree['bags']) - 1
    result = event_block_solver.solve([], n, aliases, *constant_dpda(1), backend='raw',
                                      occurrence_pins=tuple((i, 0) for i in range(n + 1)))
    assert result['status'] == 'constant' and result['value'] == 1
    sample, = result['samples']
    assert sample['physical'] == word and sample['key'] == 0 and sample['prediction'] == 1
    assert sample['underlying'] == dict.fromkeys(aliases, 0)
    metrics = result['metrics']
    assert metrics['vertices'] == length + 1 and metrics['blocks'] == length
    assert metrics['width'] == 1 and metrics['replay_bytes'] == length
    assert metrics['states'] == metrics['bag_row_bound'] and metrics['max_domain_post'] <= 2
    print('depth control', length, metrics['blocks'], metrics['states'], metrics['steps'])


if __name__ == '__main__':
    main()
