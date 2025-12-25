# solve_tasknet.py
from pprint import pprint
from tasknet_parser import parse_tasknet_file
from tasknet_smt import TaskNetSMT, TaskNetTL 

def main(path: str):
    print('\n\n\n\n\n\n\n*** NEW SCHEDULE***\n')
    tn = parse_tasknet_file(path)    
    enc = TaskNetTL(tn, error_trace=True)
    m = enc.solve()
    if m is None:
        print("UNSAT: No valid schedule found!")
        return
    enc.pretty_print(m)
    enc.check_temporal_properties()

if __name__ == "__main__":
    import sys
    main(sys.argv[1])


