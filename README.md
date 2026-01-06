# Lean Project

A Lean 4 project for learning and enjoying mathematical theorem proving!

## About

This project is designed for anyone who wants to:
- **Learn** formal mathematics through interactive theorem proving
- **Explore** the beauty of mathematical proofs
- **Enjoy** the satisfaction of proving theorems with computer verification

Lean 4 is a powerful theorem prover that lets you write mathematical proofs that are verified by the computer. It's like having a math tutor that checks every step of your reasoning!

## Features

- **Mathlib Integration**: Uses the powerful [Mathlib](https://github.com/leanprover-community/mathlib4) library for advanced mathematics
- **Organized by Category**: Theorems organized into logical modules
- **Beginner to Advanced**: From simple proofs to sophisticated mathematics

## Requirements

- [Lean 4](https://lean-lang.org/) (v4.27.0 or later)
- [elan](https://github.com/leanprover/elan) - Lean version manager

## Installation

Install elan (Lean version manager):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Clone and build:

```bash
git clone https://github.com/naoki-takata/lean-project.git
cd lean-project
lake update
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
│   ├── Equality.lean            # Equality theorems
│   └── Advanced.lean            # Advanced proofs using Mathlib
├── lakefile.toml                # Build configuration (includes Mathlib)
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

### Advanced (`MyProject/Advanced.lean`)
Powerful proofs using Mathlib tactics:

#### Algebra
```lean
-- Using ring tactic for polynomial identities
theorem square_expand (x y : ℤ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by ring
theorem diff_of_squares (a b : ℤ) : a^2 - b^2 = (a + b) * (a - b) := by ring
```

#### Linear Arithmetic
```lean
-- Using omega tactic
theorem linear_arith (a b c : Nat) (h1 : a + b ≤ c) (h2 : c ≤ a + b + 10) :
    c - a ≤ b + 10 := by omega
```

#### Real Analysis
```lean
-- Absolute value and inequalities
theorem triangle_ineq (x y : ℝ) : |x + y| ≤ |x| + |y| := abs_add_le x y
theorem sq_nonneg_example (x : ℝ) : 0 ≤ x^2 := sq_nonneg x
```

#### Set Theory
```lean
-- De Morgan's laws for sets
theorem set_deMorgan_union {α : Type*} (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ
theorem set_deMorgan_inter {α : Type*} (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ
```

#### Group Theory
```lean
-- Group axioms
theorem group_inv_mul {G : Type*} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
theorem group_inv_inv {G : Type*} [Group G] (a : G) : a⁻¹⁻¹ = a
```

#### Number Theory
```lean
-- Prime numbers
theorem two_prime : Nat.Prime 2 := Nat.prime_two
theorem three_prime : Nat.Prime 3 := Nat.prime_three
theorem even_or_odd (n : Nat) : Even n ∨ Odd n := Nat.even_or_odd n
```

## Mathlib Tactics

This project uses powerful Mathlib tactics:

| Tactic | Description | Example |
|--------|-------------|---------|
| `ring` | Solves polynomial equations | `(x+y)^2 = x^2+2*x*y+y^2` |
| `omega` | Linear integer arithmetic | `a + b ≤ c → ...` |
| `simp` | Simplification with lemmas | `n + 0 = n` |
| `decide` | Decidable propositions | `2 + 2 = 4` |
| `aesop` | Automated reasoning | Complex goal search |
| `by_contra` | Proof by contradiction | Classical proofs |

## Learn More

- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/) - Community support

## Why Lean + Mathlib?

- **Interactive**: Get instant feedback as you write proofs
- **Powerful**: Access to 100,000+ mathematical theorems in Mathlib
- **Automated**: Tactics like `ring`, `omega`, and `aesop` automate tedious steps
- **Fun**: Proving theorems feels like solving puzzles!
- **Educational**: Learn rigorous mathematical thinking

Happy theorem proving!

## License

MIT
