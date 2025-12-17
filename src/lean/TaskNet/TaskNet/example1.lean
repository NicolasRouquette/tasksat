
import TaskNet.Syntax
import TaskNet.Semantics

namespace TaskNet

open Std

-- ========
-- Task Net
-- ========

def tasknet : TaskNet :=
  { id := "HeatDriveCommunicate",
    timelines := [
      Timeline.stateTimeline "heating" ["off", "on"] "off",
      Timeline.stateTimeline "driving" ["off", "on"] "off",
      Timeline.stateTimeline "communicating" ["off", "on"] "off",
      Timeline.atomicTimeline "radio",
      Timeline.claimableTimeline "memory" {low := 0.0, high := 100.0} 0.0,
      Timeline.cumulativeTimeline "distance" {low := 0.0, high := 100.0} {low := 0.0, high := 100.0} 100.0,
      Timeline.rateTimeline "temperature" {low := 0.0, high := 100.0} {low := 0.0, high := 100.0} 50.0,
      Timeline.rateTimeline "battery" {low := 20.0, high := 100.0} {low := 0.0, high := 100.0} 30.0
    ],
    tasks := [
      --------------
      -- heating: --
      --------------
      { id := "heating",
        ident := 1,
        priority := 1,
        startrng := {low := 0, high := 20},
        endrng   := {low := 80, high := 100},
        dur := 80,
        start := 10,
        after := [],
        pre := [
          {id := "driving", cons := [Con.val (Value.strVal "off")]},
          {id := "communicating", cons := [Con.val (Value.strVal "off")]},
          {id := "battery", cons := [Con.r_rng {low := 40, high := 100}]},
          ],
        inv := [
          {id := "driving", cons := [Con.val (Value.strVal "off")]},
          {id := "communicating", cons := [Con.val (Value.strVal "off")]},
          {id := "battery", cons := [Con.r_rng {low := 30, high := 100}]},
          ],
        post := [{id := "temperature", cons := [Con.r_rng {low := 80, high := 100}]}],
        impacts := [
          {id := "heating", when := ImpactWhen.pre, how := ImpactHow.assign (Value.strVal "on")},
          {id := "heating", when := ImpactWhen.post, how := ImpactHow.assign (Value.strVal "off")},
          {id := "temperature", when := ImpactWhen.maint, how := ImpactHow.rate 1.0},
          {id := "battery", when := ImpactWhen.maint, how := ImpactHow.rate (-1.0)}
        ]},
        --------------
        -- driving: --
        --------------
        { id := "driving",
          ident := 2,
          priority := 1,
          startrng := {low := 100, high := 120},
          endrng   := {low := 180, high := 200},
          dur := 80,
          start := 110,
          after := ["heating"],
          pre := [
            {id := "communicating", cons := [Con.val (Value.strVal "off")]},
            {id := "distance", cons := [Con.i_rng {low := 5, high := 100}]},
            {id := "temperature", cons := [Con.r_rng {low := 50, high := 100}]},
            {id := "battery", cons := [Con.r_rng {low := 40, high := 100}]},
          ],
          inv := [
            {id := "communicating", cons := [Con.val (Value.strVal "off")]},
            {id := "temperature", cons := [Con.r_rng {low := 50, high := 100}]},
            {id := "battery", cons := [Con.r_rng {low := 20, high := 100}]},
          ],
          post := [{id := "distance", cons := [Con.r_rng {low := 20, high := 50}]}],
          impacts := [
            {id := "driving", when := ImpactWhen.pre, how := ImpactHow.assign (Value.strVal "on")},
            {id := "driving", when := ImpactWhen.post, how := ImpactHow.assign (Value.strVal "off")},
            {id := "distance", when := ImpactWhen.maint, how := ImpactHow.rate (-2.0)},
            {id := "temperature", when := ImpactWhen.maint, how := ImpactHow.rate (-1.0)},
            {id := "battery", when := ImpactWhen.maint, how := ImpactHow.rate (-2.0)}
        ]},
        --------------------
        -- communicating: --
        --------------------
        { id := "communicating",
          ident := 3,
          priority := 1,
          startrng := {low := 200, high := 220},
          endrng   := {low := 280, high := 300},
          dur := 80,
          start := 210,
          after := [],
          pre := [
            {id := "driving", cons := [Con.val (Value.strVal "off")]},
            {id := "radio", cons := [Con.val (Value.boolVal false)]},
            {id := "memory", cons := [Con.r_rng {low := 40, high := 100}]},
            {id := "battery", cons := [Con.r_rng {low := 50, high := 100}]},
          ],
          inv := [
            {id := "driving", cons := [Con.val (Value.strVal "off")]},
            {id := "battery", cons := [Con.r_rng {low := 20, high := 100}]},
          ],
          post := [
            {id := "memory", cons := [Con.r_rng {low := 0, high := 0}]}
          ],
          impacts := [
            {id := "communicating", when := ImpactWhen.pre, how := ImpactHow.assign (Value.strVal "on")},
            {id := "communicating", when := ImpactWhen.post, how := ImpactHow.assign (Value.strVal "off")},
            {id := "radio", when := ImpactWhen.pre, how := ImpactHow.assign (Value.boolVal true)},
            {id := "radio", when := ImpactWhen.post, how := ImpactHow.assign (Value.boolVal false)},
            {id := "memory", when := ImpactWhen.post, how := ImpactHow.cumulative (-100.0)},
            {id := "battery", when := ImpactWhen.maint, how := ImpactHow.rate (-2.0)}
        ]}

    ],
    endTime := 400
    }

-- ========
-- Schedule
-- ========

def sch : Schedule :=
  (Std.HashMap.emptyWithCapacity : Schedule)
    |>.insert "heating"       (10, 90)
    |>.insert "driving"       (110, 190)
    |>.insert "communicating" (210, 290)

-- ======================================
-- Proof that it is an admisible schedule
-- ======================================

theorem dom_sch_eq_ids :
  dom sch = TaskNamesOf tasknet.tasks := by
  -- TODO: prove by ext on HashSet; unfold `sch` and `TaskNamesOf`.
  sorry

theorem no_simul_assigns :
  NoSimultaneousAssignments tasknet.tasks sch := by
  -- TODO: case-analyze impacts; times are distinct.
  sorry

theorem times_ok :
  StartEndTimesOkTasks tasknet.tasks sch tasknet.endTime := by
  -- TODO: arithmetic checks for each task (dur and ranges).
  sorry

theorem StartEndTimesOk_sch : StartEndTimesOk tasknet sch := by
  dsimp [StartEndTimesOk]
  refine And.intro ?domOk (And.intro ?noSimul ?timeOk)
  · exact dom_sch_eq_ids
  · exact no_simul_assigns
  · exact times_ok

end TaskNet
