# example.py
#
# Simple Z3 examples:
#   1) tiny sanity-check (x,y)
#   2) trace-based model with heating/driving/... and clamped temperature

from z3 import *

# ============================================================
# 2. Trace model for timelines + safe helpers + clamping
# ============================================================

def clamp(x, lo, hi):
    """Z3 clamp: max(lo, min(hi, x))."""
    return If(x < lo, lo, If(x > hi, hi, x))


class TraceModel:
    """
    Very simple discrete-time trace model with:
      - heating, driving, communicating: Int (0 = off, 1 = on)
      - radio: Bool
      - memory, distance, temperature, battery: Real

    Time is 0..T.
    """

    def __init__(self, T: int):
        self.T = T

        # --- Timelines over time 0..T ---
        self.heating       = [Int(f"heating_{t}")       for t in range(T + 1)]
        self.driving       = [Int(f"driving_{t}")       for t in range(T + 1)]
        self.communicating = [Int(f"communicating_{t}") for t in range(T + 1)]

        self.radio         = [Bool(f"radio_{t}")        for t in range(T + 1)]

        self.memory        = [Real(f"memory_{t}")       for t in range(T + 1)]
        self.distance      = [Real(f"distance_{t}")     for t in range(T + 1)]
        self.temperature   = [Real(f"temperature_{t}")  for t in range(T + 1)]
        self.battery       = [Real(f"battery_{t}")      for t in range(T + 1)]

        self.s = Solver()

    # ----------------------------
    # Safe "after" helpers (no IndexError)
    # ----------------------------

    def temp_after(self, k: int):
        if k < self.T:
            return self.temperature[k + 1]
        else:
            return self.temperature[k]

    def dist_after(self, k: int):
        if k < self.T:
            return self.distance[k + 1]
        else:
            return self.distance[k]

    def mem_after(self, k: int):
        if k < self.T:
            return self.memory[k + 1]
        else:
            return self.memory[k]

    # ----------------------------
    # Example constraints
    # ----------------------------

    def add_basic_constraints(self):
        T = self.T

        # 0/1 for categorical timelines
        for t in range(T + 1):
            self.s.add(self.heating[t] >= 0, self.heating[t] <= 1)
            self.s.add(self.driving[t] >= 0, self.driving[t] <= 1)
            self.s.add(self.communicating[t] >= 0, self.communicating[t] <= 1)

        # Initial state
        self.s.add(self.heating[0] == 0)
        self.s.add(self.driving[0] == 0)
        self.s.add(self.communicating[0] == 0)
        self.s.add(self.radio[0] == False)
        self.s.add(self.memory[0] == 100.0)
        self.s.add(self.distance[0] == 100.0)
        self.s.add(self.temperature[0] == 50.0)
        self.s.add(self.battery[0] == 100.0)

        # Timeline ranges (like RealRange in Lean)
        for t in range(T + 1):
            self.s.add(self.temperature[t] >= 0.0, self.temperature[t] <= 100.0)
            self.s.add(self.battery[t]     >= 20.0, self.battery[t]     <= 100.0)
            self.s.add(self.memory[t]      >= 0.0,  self.memory[t]      <= 100.0)
            self.s.add(self.distance[t]    >= 0.0,  self.distance[t]    <= 100.0)

        # --------------------------------------------------
        # Very coarse "schedule" encoded directly
        # --------------------------------------------------
        # heating: on in [10, 90], off otherwise
        for t in range(T + 1):
            self.s.add(
                Implies(And(t >= 10, t <= 90), self.heating[t] == 1)
            )
            self.s.add(
                Implies(Or(t < 10, t > 90), self.heating[t] == 0)
            )

        # driving: on in [110, 190], off otherwise
        for t in range(T + 1):
            self.s.add(
                Implies(And(t >= 110, t <= 190), self.driving[t] == 1)
            )
            self.s.add(
                Implies(Or(t < 110, t > 190), self.driving[t] == 0)
            )

        # communicating: on in [210, 290], off otherwise
        for t in range(T + 1):
            self.s.add(
                Implies(And(t >= 210, t <= 290), self.communicating[t] == 1)
            )
            self.s.add(
                Implies(Or(t < 210, t > 290), self.communicating[t] == 0)
            )

        # radio: true iff communicating is on
        for t in range(T + 1):
            self.s.add(self.radio[t] == (self.communicating[t] == 1))

        # --------------------------------------------------
        # "Impact-like" dynamics with clamped temperature
        #   (not a full faithful copy of Lean, just enough to be consistent)
        # --------------------------------------------------
        for k in range(T):
            # heating contribution: +1 deg, -0.01 battery
            heat_delta_temp  = If(self.heating[k] == 1, 1.0, 0.0)
            heat_delta_batt  = If(self.heating[k] == 1, -0.01, 0.0)

            # driving contribution: -1 distance, -0.2 temperature, -0.2 battery
            drive_delta_dist = If(self.driving[k] == 1, -1.0, 0.0)
            drive_delta_temp = If(self.driving[k] == 1, -0.2, 0.0)
            drive_delta_batt = If(self.driving[k] == 1, -0.2, 0.0)

            # communicating: -0.2 battery; memory change only at end, ignored here
            comm_delta_batt  = If(self.communicating[k] == 1, -0.2, 0.0)

            # temperature: apply deltas then clamp
            raw_temp = self.temperature[k] + heat_delta_temp + drive_delta_temp
            self.s.add(self.temperature[k + 1] == clamp(raw_temp, 0.0, 100.0))

            # distance: apply delta, clamp to [0,100]
            raw_dist = self.distance[k] + drive_delta_dist
            self.s.add(self.distance[k + 1] == clamp(raw_dist, 0.0, 100.0))

            # battery: sum of all contributions, clamp to [20,100]
            raw_batt = (self.battery[k]
                        + heat_delta_batt
                        + drive_delta_batt
                        + comm_delta_batt)
            self.s.add(self.battery[k + 1] == clamp(raw_batt, 20.0, 100.0))

            # memory: just keep constant for now
            self.s.add(self.memory[k + 1] == self.memory[k])

        # --------------------------------------------------
        # Example use of temp_after / dist_after / mem_after
        # --------------------------------------------------
        for k in range(T + 1):
            self.s.add(self.temp_after(k) >= 0.0)
            self.s.add(self.dist_after(k) >= 0.0)
            self.s.add(self.mem_after(k)  >= 0.0)

        # Just one random extra: final temperature at least 20
        self.s.add(self.temperature[T] >= 20.0)

    def solve(self):
        if self.s.check() == sat:
            m = self.s.model()
            print("Trace model: SAT")
            # Show a few interesting time points
            for t in [0, 10, 90, 110, 190, 210, 290, self.T]:
                print(f"\n--- t = {t} ---")
                print("heating      =", m[self.heating[t]])
                print("driving      =", m[self.driving[t]])
                print("communicating=", m[self.communicating[t]])
                print("radio        =", m[self.radio[t]])
                print("memory       =", m[self.memory[t]])
                print("distance     =", m[self.distance[t]])
                print("temperature  =", m[self.temperature[t]])
                print("battery      =", m[self.battery[t]])
        else:
            print("Trace model: UNSAT")


# ============================================================
# Main
# ============================================================

def main():
    print("\n=============================")
    print("Now solving trace model SMT...")
    print("=============================\n")

    T = 300
    tm = TraceModel(T)
    tm.add_basic_constraints()
    tm.solve()


if __name__ == "__main__":
    main()
