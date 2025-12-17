from pathlib import Path
from pprint import pprint
from parse import parse_tasknet_file
# from solver import TaskNetSMT   # your SMT module

def main():
    here = Path(__file__).resolve().parent
    parse_path = here / "tasknet1.tn"
    tn = parse_tasknet_file(parse_path)
    pprint(tn)

    #enc = TaskNetSMT(tn)
    #model = enc.solve()
    #enc.pretty_print(model)
    #enc.check_temporal_properties()

if __name__ == "__main__":
    main()
