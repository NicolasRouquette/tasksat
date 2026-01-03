
# TaskVet

Tool set for verifying (vetting) task networks written in the TaskNet DSL using SMT solving.

## Installation

```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

## VS Code Syntax Highlighting (Optional)

Install the TaskNet language extension for syntax highlighting of `.tn` files.

If the `.vsix` file already exists, simply install it:
```bash
cd vscode-dsl
code --install-extension tasknet-0.0.1.vsix --force
```

If you've made changes or the `.vsix` doesn't exist, repackage first:
```bash
cd vscode-dsl
vsce package --allow-missing-repository
code --install-extension tasknet-0.0.1.vsix --force
```

## Usage

### 1. Write a TaskNet File

Create a `.tn` file defining your task network. A TaskNet specification includes:

- **Timelines**: State variables and resources (state, atomic, claim, rate)
- **Tasks**: Operations with preconditions, invariants, postconditions, and resource impacts
- **Properties**: Temporal logic properties to verify (using `always`, `eventually`, `once`, etc.)

### 2. Verify Your TaskNet

Run the verifier on your TaskNet file:

```bash
python src/smt/tasknet_verifier.py path/to/your_tasknet.tn
```

The verifier will either:
- **SAT**: Find and display a valid schedule satisfying all constraints
- **UNSAT**: Report that no valid schedule exists

#### Solver Modes

The verifier supports two modes via the `--mode` flag:

- **optimize** (default): Uses Z3's `Optimize` solver to minimize the number of optional tasks included
  ```bash
  python src/smt/tasknet_verifier.py path/to/your_tasknet.tn --mode optimize
  ```

- **satisfy**: Uses Z3's `Solver` to find any valid schedule without optimization. This mode is faster and provides unsat core debugging when no solution exists
  ```bash
  python src/smt/tasknet_verifier.py path/to/your_tasknet.tn --mode satisfy
  ```

### Example

See [tasknet1.tn](src/smt/tasknet1.tn) for a complete example demonstrating:
- State timelines (heating, driving, communicating)
- Resources with bounds (battery, memory, distance, temperature)
- Task definitions with temporal constraints
- Temporal properties like `always (battery >= 60.0)`

## TaskNet Language Features

- **Timeline Types**: `state`, `atomic`, `claim`, `cumulative`, `rate`
- **Task Constraints**: `pre`, `inv`, `post`, `impacts`, `after`
- **Resource Operations**: `=`, `+=`, `-=`, `+~`, `-~`, `in [min, max]`
- **Temporal Operators**: `always`, `eventually`, `once`, `sofar`, `until`, `since`
- **Logical Operators**: `not`, `and`, `or`, `->`, `>=`, `<=`, `<`, `>`

## Modifying Syntax Highlighting

To update the syntax highlighting after making changes:

1. Edit [tasknet.tmLanguage.json](vscode-dsl/syntaxes/tasknet.tmLanguage.json)
2. Repackage the extension:
   ```bash
   cd vscode-dsl && vsce package --allow-missing-repository
   ```
3. Reinstall the extension:
   ```bash
   code --install-extension tasknet-0.0.1.vsix --force
   ```
4. Reload VS Code window (Command Palette → "Developer: Reload Window")

