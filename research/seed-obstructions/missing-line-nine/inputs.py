from pathlib import Path
from samples import raw_samples
P,N=raw_samples(Path(__file__).with_name('L-meta-18968.json'))
stars=[sum(1<<((q+d)%13) for d in (0,1,3,9)) for q in range(6,13)]
