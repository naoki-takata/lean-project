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
├── Main.lean                    # Entry point
├── MyProject.lean               # Library root (imports all modules)
├── MyProject/
│   ├── Basic.lean               # Core definitions
│   ├── Logic.lean               # Logic theorems
│   ├── NumberTheory.lean        # Number theory theorems
│   ├── Lists.lean               # List theorems
│   ├── Functions.lean           # Function theorems
│   └── Equality.lean            # Equality theorems
├── lakefile.toml                # Build configuration
└── lean-toolchain               # Lean version specification
```

## Theorem Categories

### Logic (`MyProject/Logic.lean`)
Fundamental logical propositions and their proofs:
- **De Morgan's Law**: `¬(P ∨ Q) ↔ (¬P ∧ ¬Q)`
- **Contrapositive**: `(P → Q) → (¬Q → ¬P)`
- **Modus Ponens**: `P ∧ (P → Q) → Q`
- **Double Negation**: `P → ¬¬P` and `¬¬P → P`
- **Currying**: `(P ∧ Q → R) ↔ (P → Q → R)`
- **And/Or Commutativity and Distributivity**

### Number Theory (`MyProject/NumberTheory.lean`)
Proofs about natural numbers and arithmetic:
- **Sum Formula (Gauss)**: `2 * (0 + 1 + ... + n) = n * (n + 1)`
- **Even Number Properties**: Sum of even numbers is even
- **Basic Arithmetic**: Commutativity, associativity, distributivity

### Lists (`MyProject/Lists.lean`)
Proofs about list operations:
- **Reverse Involution**: `xs.reverse.reverse = xs`
- **Length Preservation**: `(xs ++ ys).length = xs.length + ys.length`
- **Map Length**: `(xs.map f).length = xs.length`
- **Append Associativity**: `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)`

### Functions (`MyProject/Functions.lean`)
Proofs about functions and composition:
- **Composition Associativity**: `(f ∘ g) ∘ h = f ∘ (g ∘ h)`
- **Injectivity Properties**: Composition preserves injectivity
- **Surjectivity Properties**: Composition preserves surjectivity
- **Identity Function Properties**

### Equality (`MyProject/Equality.lean`)
Proofs about equality relations:
- **Reflexivity, Symmetry, Transitivity**
- **Substitution and Congruence**
- **Equality with Arithmetic Operations**

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
