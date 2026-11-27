"""Physical address comparison with signed rereads and a free parity tail."""
from padding_cnf import encode
from event_fixtures import _slot_offsets
from stack_alias import decode_alias


def comparator_fixture(d=1, payload=3):
    """Return byte/macro fixture with 2^(2d+payload-1) pinned words per terminal bit."""
    if type(d) is not int or d < 1 or type(payload) is not int or payload < 1:
        raise ValueError("expected positive address width and payload length")
    width = 2 * d
    addr_mask = (1 << width) - 1
    flag_bit = 1 << width
    parity_bit = flag_bit << 1
    reg_width = width + 2
    reg_mask = (1 << reg_width) - 1
    half_mask = (1 << d) - 1
    address_ids = [23 + 7 * i for i in range(width)]
    aliases = address_ids + [-a for a in reversed(address_ids)]
    aliases.extend(23 + 7 * (width + i) for i in range(payload + 1))
    n = len(aliases) - 1
    challenge = [(1, -2, 3), (-1, n, 2)]
    slots, _ = _slot_offsets(challenge, n)
    prefix_lines = encode(challenge, n, 0).count(b"\n") - len(aliases)

    def update(i, r, bit):
        if i < width:
            address = r | (bit << i)
            if i + 1 == width:
                flag = int((address & half_mask) <= (address >> d))
                return address | (flag * flag_bit)
            return address
        if i < 2 * width:
            r ^= bit * parity_bit
            if i + 1 == 2 * width:
                return int(bool(r & flag_bit) ^ bool(r & parity_bit))
            return r
        return r ^ bit

    # Controls encode the physical line phase and the semantic register. Only
    # phases/registers reachable by the raw parser are allocated. The raw table
    # remains total on all 256 bytes at each allocated state.
    def state(phase, reg):
        return (phase << reg_width) | reg

    table = {}
    outputs = {}
    sink = state(prefix_lines + 2 * len(aliases) + 1, 0)
    outputs[sink] = 0
    for byte in range(256):
        table[sink, 0, byte] = (sink, "stay")
    for j in range(prefix_lines):
        q = state(j, 0)
        outputs[q] = 0
        for byte in range(256):
            table[q, 0, byte] = (state(j + int(byte == 10), 0), "stay")

    regs = {0}
    for i in range(len(aliases)):
        phase = prefix_lines + 2 * i
        tails = set()
        for r in regs:
            q = state(phase, r)
            outputs[q] = 0
            candidates = [update(i, r, bit) for bit in (0, 1)]
            tails.update(candidates)
            for byte in range(256):
                if byte == 45 or 49 <= byte <= 57:
                    dest = state(phase + 1, candidates[int(byte == 45)])
                else:
                    dest = sink
                table[q, 0, byte] = (dest, "stay")
        for r in tails:
            q = state(phase + 1, r)
            outputs[q] = 0
            for byte in range(256):
                dest = state(phase + 1 + int(byte == 10), r)
                table[q, 0, byte] = (dest, "stay")
        regs = tails
    for r in regs:
        q = state(prefix_lines + 2 * len(aliases), r)
        outputs[q] = r
        for byte in range(256):
            table[q, 0, byte] = (sink, "stay")

    def codebooks(events):
        # Include both registers: the nonlinear last seeding transition contains
        # the entire address and comparator result in its own row.
        books = {}
        for v, domain in events.domains.items():
            if v == events.output:
                books[v] = {bit: bit for bit in domain}
                continue
            local = {}
            for row in domain:
                before = row.before[0] & reg_mask
                after = row.after[0] & reg_mask
                local[row] = (before << (reg_width + 1)) | (after << 1) | int(row.bit or 0)
            if len(set(local.values())) != len(local):
                raise ValueError("physical records collide in supplied coordinates")
            books[v] = local
        return books

    raw_witnesses = {}
    for varied in (0, 1):
        # X=Y=0, C=1, even number of complemented rereads, enable=1.
        key = (addr_mask << width) | (varied << (2 * width)) | (1 << n)
        raw = encode(challenge, n, key)
        decode_alias(raw, aliases)
        raw_witnesses[varied] = raw
    return dict(challenge=challenge, n=n, aliases=aliases, occurrence_pins=((n, 1),),
                id_pins=(), table=table, initial=state(0, 0), bottom=0, outputs=outputs,
                schedule={}, macro_schedule=("stay",) * len(aliases), slot_events=slots,
                raw_witnesses=raw_witnesses, record_codes=codebooks)
