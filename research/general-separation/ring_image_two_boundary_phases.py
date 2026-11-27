"""Physical selector-free input to a lifted two-boundary phase projection."""
import ring_image_affine_phases as phase_chart
from two_boundary_kernel import project as project_cnf


class PhaseProjection:
    """All three coordinate systems are explicit; original edges are one-based."""
    def __init__(self, chart):
        self.arity = chart["arity"]
        self.phase_count = chart["phase_count"]
        self.phase_rows = tuple(chart["rows"])
        self._formula = tuple(chart["formula"])
        self._edge_literals = dict(chart["edge_literals"])
        self._kernel = project_cnf(self.phase_count, self.phase_rows)
        self.residual = self._kernel.residual
        self.representatives = {}
        for x in sorted(self._edge_literals):
            lit = self._edge_literals[x]
            if lit > 0:
                self.representatives.setdefault(lit, x)
        if len(self.representatives) != self.phase_count:
            raise AssertionError("missing positive cycle edge")
        self.source_residual = tuple(tuple(self.representatives[abs(i)] *
                                           (1 if i > 0 else -1) for i in row)
                                     for row in self.residual)

    def lift(self, true_phase_ids):
        """Extend a residual phase model to a dense original source assignment."""
        full = set(self._kernel.lift(true_phase_ids))
        if not all(any((abs(i) in full) == (i > 0) for i in row)
                   for row in self.phase_rows):
            raise AssertionError("kernel lift violates original phase clauses")
        bits = [0] * self.arity
        for x, lit in self._edge_literals.items():
            bits[x-1] = int((abs(lit) in full) == (lit > 0))
        if not all(any(bits[abs(i)-1] == (i > 0) for i in row)
                   for row in self._formula):
            raise AssertionError("phase lift violates recovered source")
        return tuple(bits)

    def lift_source(self, true_representative_ids):
        """Extend a sparse model of source_residual in representative-edge labels."""
        inverse = {x: phase for phase, x in self.representatives.items()}
        phases = set()
        for x in true_representative_ids:
            if type(x) is not int or x not in inverse:
                raise ValueError("expected a representative source edge")
            phases.add(inverse[x])
        return self.lift(phases)


def project(n, clauses, point, k):
    chart = phase_chart.certified_phases(n, clauses, point, k)
    if chart["status"] != "certified":
        return chart
    return dict(status="projected", projection=PhaseProjection(chart))


def decide(n, clauses, point, k):
    result = project(n, clauses, point, k)
    if result["status"] != "projected":
        return result
    projection = result["projection"]
    if any(len(row) > 2 for row in projection.residual):
        if not any(not row for row in projection.residual):
            return dict(status="unknown", reason="residual_width",
                        residual=projection.residual, source_residual=projection.source_residual,
                        projection=projection)
        return dict(status="zero")
    import networkx as nx

    bits = phase_chart._two_sat(nx, projection.phase_count, projection.residual)
    if bits is None:
        return dict(status="zero")
    live = {abs(i) for row in projection.residual for i in row}
    assignment = projection.lift(i for i in live if bits[i-1])
    return dict(status="nonzero", assignment=assignment)
