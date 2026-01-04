# Analysis: Timeline-Impact Type Checking

## Summary

**You are correct!** There is currently **NO** formal type checking or validation that enforces a relationship between timeline types and impact types in the parser or AST layer.

The only checking that exists happens **implicitly during SMT encoding**, where type mismatches cause the solver to add `False` constraints, making the problem unsolvable.

## Current State

### Timeline Types
From [tasknet_ast.py](src/smt/tasknet_ast.py:44-83):
- **StateTimeline**: Discrete states (e.g., "idle", "active", "done")
- **AtomicTimeline**: Boolean values (true/false)
- **ClaimableTimeline**: Numeric with range
- **CumulativeTimeline**: Numeric with range and bounds
- **RateTimeline**: Numeric with range and bounds

### Impact Types
From [tasknet_ast.py](src/smt/tasknet_ast.py:85-107):
- **ImpactAssign**: Assignment (=) of a Value (int, real, string, bool)
- **ImpactCumulative**: Numeric delta (+=, -=)
- **ImpactRate**: Rate of change over time (+rate, -rate)

### Where Type Checking Happens

#### 1. Parser/Grammar Layer ([grammar.txt](src/smt/grammar.txt))
**No type checking at all.** The grammar accepts any syntactically valid combination:
- Line 204-212: Impact syntax allows any timeline name with any impact operator
- No cross-reference to timeline declarations
- No validation of value types against timeline types

#### 2. AST Layer ([tasknet_ast.py](src/smt/tasknet_ast.py))
**No type checking.** The AST is just data structures with no validation:
- Timeline types are simple dataclasses
- Impact types use Union types that accept any combination
- No validation methods or type constraints

#### 3. SMT Encoding Layer ([tasknet_smt.py](src/smt/tasknet_smt.py))
**Implicit runtime checking** that happens during encoding:

For **StateTimeline** impacts (lines 512-550):
- Accepts only ImpactAssign
- Checks if value is StrVal at line 530
- If not StrVal: `self.solver.add(False)` → unsolvable
- ImpactCumulative/ImpactRate: Not handled → implicitly ignored

For **AtomicTimeline** impacts (lines 552-578):
- Accepts only ImpactAssign
- Checks if value is BoolVal at line 569
- If not BoolVal: `self.solver.add(False)` → unsolvable
- ImpactCumulative/ImpactRate: Not handled → implicitly ignored

For **Numeric timelines** (lines 422-501 in `_numeric_delta_zone`):
- Handles ImpactCumulative (lines 446-462)
- Handles ImpactRate (lines 465-490)
- If ImpactAssign found: `self.solver.add(False)` at line 494 → unsolvable

### Actual Type Compatibility Matrix

| Timeline Type | ImpactAssign | ImpactCumulative | ImpactRate |
|---------------|--------------|------------------|------------|
| StateTimeline | ✓ (StrVal only) | ✗ (ignored) | ✗ (ignored) |
| AtomicTimeline | ✓ (BoolVal only) | ✗ (ignored) | ✗ (ignored) |
| ClaimableTimeline | ✗ (solver.add(False)) | ✓ | ✓ |
| CumulativeTimeline | ✗ (solver.add(False)) | ✓ | ✓ |
| RateTimeline | ✗ (solver.add(False)) | ✓ | ✓ |

### Complete Impact Behavior Table

This table shows what happens for each combination of timeline type, impact type, and timing (PRE/MAINT/POST):

| Timeline Type | Impact Type | When | Supported? | Behavior | Code Reference |
|---------------|-------------|------|------------|----------|----------------|
| **StateTimeline** | ImpactAssign (StrVal) | PRE | ✓ | Assigns state value at task start boundary (`zone == start`) | [L536-541](src/smt/tasknet_smt.py#L536-L541) |
| | | MAINT | ✗ | **FORBIDDEN**: `solver.add(False)` → unsolvable | [L549](src/smt/tasknet_smt.py#L549) |
| | | POST | ✓ | Assigns state value at task end boundary (`zone == end`) | [L542-546](src/smt/tasknet_smt.py#L542-L546) |
| | ImpactCumulative | * | ✗ | Not handled (implicitly ignored in encoding) | [L512-550](src/smt/tasknet_smt.py#L512-L550) |
| | ImpactRate | * | ✗ | Not handled (implicitly ignored in encoding) | [L512-550](src/smt/tasknet_smt.py#L512-L550) |
| **AtomicTimeline** | ImpactAssign (BoolVal) | PRE | ✓ | Assigns boolean value at task start boundary (`zone == start`) | [L572-573](src/smt/tasknet_smt.py#L572-L573) |
| | | MAINT | ✗ | **FORBIDDEN**: `solver.add(False)` → unsolvable | [L577](src/smt/tasknet_smt.py#L577) |
| | | POST | ✓ | Assigns boolean value at task end boundary (`zone == end`) | [L574-575](src/smt/tasknet_smt.py#L574-L575) |
| | ImpactCumulative | * | ✗ | Not handled (implicitly ignored in encoding) | [L552-578](src/smt/tasknet_smt.py#L552-L578) |
| | ImpactRate | * | ✗ | Not handled (implicitly ignored in encoding) | [L552-578](src/smt/tasknet_smt.py#L552-L578) |
| **ClaimableTimeline** | ImpactAssign | * | ✗ | **FORBIDDEN**: `solver.add(False)` → unsolvable | [L492-494](src/smt/tasknet_smt.py#L492-L494) |
| | ImpactCumulative | PRE | ✓ | Instant delta `+v` at start boundary (`zone == start`) | [L448-450](src/smt/tasknet_smt.py#L448-L450) |
| | | MAINT | ✓ | Adds `+v` at start, `-v` at end (temporary consumption) | [L451-453](src/smt/tasknet_smt.py#L451-L453) |
| | | POST | ✓ | Instant delta `+v` at end boundary (`zone == end`) | [L454-457](src/smt/tasknet_smt.py#L454-L457) |
| | ImpactRate | PRE | ✓ | Rate `r*dt` active from start onward forever (`zone >= start`) | [L478-479](src/smt/tasknet_smt.py#L478-L479) |
| | | MAINT | ✓ | Rate `r*dt` active only during task (`start <= zone < end`) | [L480-481](src/smt/tasknet_smt.py#L480-L481) |
| | | POST | ✓ | Rate `r*dt` active from end onward forever (`zone >= end`) | [L482-485](src/smt/tasknet_smt.py#L482-L485) |
| **CumulativeTimeline** | ImpactAssign | * | ✗ | **FORBIDDEN**: `solver.add(False)` → unsolvable | [L492-494](src/smt/tasknet_smt.py#L492-L494) |
| | ImpactCumulative | PRE | ✓ | Instant delta `+v` at start boundary (`zone == start`) | [L448-450](src/smt/tasknet_smt.py#L448-L450) |
| | | MAINT | ✓ | Adds `+v` at start, `-v` at end (temporary consumption) | [L451-453](src/smt/tasknet_smt.py#L451-L453) |
| | | POST | ✓ | Instant delta `+v` at end boundary (`zone == end`) | [L454-457](src/smt/tasknet_smt.py#L454-L457) |
| | ImpactRate | PRE | ✓ | Rate `r*dt` active from start onward forever (`zone >= start`) | [L478-479](src/smt/tasknet_smt.py#L478-L479) |
| | | MAINT | ✓ | Rate `r*dt` active only during task (`start <= zone < end`) | [L480-481](src/smt/tasknet_smt.py#L480-L481) |
| | | POST | ✓ | Rate `r*dt` active from end onward forever (`zone >= end`) | [L482-485](src/smt/tasknet_smt.py#L482-L485) |
| **RateTimeline** | ImpactAssign | * | ✗ | **FORBIDDEN**: `solver.add(False)` → unsolvable | [L492-494](src/smt/tasknet_smt.py#L492-L494) |
| | ImpactCumulative | PRE | ✓ | Instant delta `+v` at start boundary (`zone == start`) | [L448-450](src/smt/tasknet_smt.py#L448-L450) |
| | | MAINT | ✓ | Adds `+v` at start, `-v` at end (temporary consumption) | [L451-453](src/smt/tasknet_smt.py#L451-L453) |
| | | POST | ✓ | Instant delta `+v` at end boundary (`zone == end`) | [L454-457](src/smt/tasknet_smt.py#L454-L457) |
| | ImpactRate | PRE | ✓ | Rate `r*dt` active from start onward forever (`zone >= start`) | [L478-479](src/smt/tasknet_smt.py#L478-L479) |
| | | MAINT | ✓ | Rate `r*dt` active only during task (`start <= zone < end`) | [L480-481](src/smt/tasknet_smt.py#L480-L481) |
| | | POST | ✓ | Rate `r*dt` active from end onward forever (`zone >= end`) | [L482-485](src/smt/tasknet_smt.py#L482-L485) |

**Legend:**
- ✓ = Supported and implemented
- ✗ = Not supported (causes error or ignored)
- `*` = Applies to all timing values (PRE, MAINT, POST)
- `dt` = Duration of zone interval `[zone_i, zone_{i+1}]`

## Implications

1. **No early error detection**: Users can write invalid impact-timeline combinations and only discover the error when the SMT solver fails
2. **Poor error messages**: When `solver.add(False)` is called, the solver just says "unsat" without explaining which type mismatch caused it
3. **Grammar allows invalid programs**: The parser accepts programs that can never be solved
4. **Type safety is runtime only**: There's no static or parse-time validation
