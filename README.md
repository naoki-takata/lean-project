# Lean Project

A Lean 4 project for learning and enjoying mathematical theorem proving!

## About

This project is designed for anyone who wants to:
- **Learn** formal mathematics through interactive theorem proving
- **Explore** the beauty of mathematical proofs
- **Enjoy** the satisfaction of proving theorems with computer verification

Lean 4 is a powerful theorem prover that lets you write mathematical proofs that are verified by the computer. It's like having a math tutor that checks every step of your reasoning!

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

Explore these example theorems in `MyProject/Basic.lean`:

### 1. Right Identity of Addition
```lean
theorem add_zero (n : Nat) : n + 0 = n := rfl
```
Any number plus zero equals itself. Simple but fundamental!

### 2. Identity Function
```lean
theorem identity (P : Prop) : P → P := fun h => h
```
If P is true, then P is true. The simplest logical tautology!

### 3. Commutativity of Addition
```lean
theorem add_comm_example (a b : Nat) : a + b = b + a := Nat.add_comm a b
```
Order doesn't matter in addition: 2 + 3 = 3 + 2

### 4. Transitivity of Equality
```lean
theorem eq_trans_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]
```
If a = b and b = c, then a = c. A chain of equalities!

## Learn More

- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/) - Community support

## Why Lean?

- **Interactive**: Get instant feedback as you write proofs
- **Powerful**: Used for serious mathematics research (Mathlib)
- **Fun**: Proving theorems feels like solving puzzles!
- **Educational**: Learn rigorous mathematical thinking

Happy theorem proving!

## License

MIT
