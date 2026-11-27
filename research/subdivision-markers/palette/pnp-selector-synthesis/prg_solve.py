"""Exact chart-image solver using a selected determinant filtration level."""
from fixed_height import recognize, prior
from hybrid import filtration, minors
from image_solver import normalize
from image_prg import assignments
from recognizer import tag_at

def solve(columns,d,n,encoder,selector_degree,height_degree,level=None):
    if d<0 or n<0: raise ValueError("negative dimension")
    columns=tuple(columns)
    encoder=tuple(normalize(poly,n) for poly in encoder)
    if len(encoder)!=2*d: raise ValueError("expected two chart bits per private dimension")
    cert=recognize(columns,d,selector_degree,height_degree)
    profile=dict(filtration(minors(columns,cert),2*d))
    if level is None: level=max(profile)
    if level not in profile: raise ValueError("no such filtration level")
    cap=profile[level]+2*(d-len(cert.anchors)+2)
    a=max((m.bit_count() for f in encoder for m in f),default=0)
    for assignment in assignments(n,a,cap,level):
        chart=sum((sum(m&assignment==m for m in f)%2)<<i for i,f in enumerate(encoder))
        private,lifted,ids={},{},[]
        for i,(k,b,h) in enumerate(columns):
            if tag_at(chart,k,d)==b:
                prior['add'](private,k)
                if prior['add'](lifted,k<<2|h): ids.append(i)
        if len(lifted)-len(private)==2:
            return assignment,ids
    return None
