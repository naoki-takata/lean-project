# Lean Project

A Lean 4 project demonstrating theorem proving and functional programming.

## Requirements

- [Lean 4](https://lean-lang.org/) (v4.26.0 or later)
- [elan](https://github.com/leanprover/elan) - Lean version manager

## Installation

Install elan (Lean version manager):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## Build

```bash
lake build
```

## Run

```bash
lake exe myproject
```

Output: `Hello, world!`

## Project Structure

```
.
├── Main.lean              # Entry point
├── MyProject.lean         # Library root
├── MyProject/
│   └── Basic.lean         # Core definitions and theorems
├── lakefile.toml          # Build configuration
└── lean-toolchain         # Lean version specification
```

## Theorems

The project includes several example theorems in `MyProject/Basic.lean`:

| Theorem | Statement | Description |
|---------|-----------|-------------|
| `add_zero` | `n + 0 = n` | Right identity of addition |
| `identity` | `P → P` | Identity function for propositions |
| `add_comm_example` | `a + b = b + a` | Commutativity of addition |
| `eq_trans_example` | `a = b → b = c → a = c` | Transitivity of equality |

## License

MIT
