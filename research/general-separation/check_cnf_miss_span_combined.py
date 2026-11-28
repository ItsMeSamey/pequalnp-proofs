"""One scheduled run for distinct raw-CNF controls if the prior suite is pending."""
from check_cnf_miss_span import main as span_suite
from check_cnf_miss_guard_saving import main as guard_saving


if __name__=='__main__':
    span_suite()
    guard_saving()
