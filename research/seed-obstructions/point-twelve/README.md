# Minimum point cost at width twelve

A point preprocessing circuit offering at most twelve outputs to arbitrary monotone mixed postprocessing, with all seven raw lines available, needs exactly five point gates on the normalized sample. Run `python verify.py` with python-sat installed. The raw JSON is included.

Three freely chosen nonprimitive singleton signatures and the remaining raw singletons cannot separate all positive-negative pairs (abstract.py). Thus any four-gate solution must output four nonprimitive wires produced by distinct gates. k4.py enumerates the corresponding four-gate synthesis constraints by SAT. The remaining raw outputs may be padded to reach width twelve. Finally verify.py gives five explicit OR gates and checks every positive-negative pair in the projection. The upward closure of the projected positives realizes a monotone separator. No mixed-gate budget is imposed here.
