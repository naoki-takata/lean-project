/-
  Advanced Theorems using Mathlib
  Demonstrates powerful tactics and mathematical structures
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

-- ============================================================================
-- ARITHMETIC WITH OMEGA AND RING
-- ============================================================================

-- Using omega tactic for linear arithmetic
theorem linear_arith (a b c : Nat) (h1 : a + b ≤ c) (h2 : c ≤ a + b + 10) :
    c - a ≤ b + 10 := by omega

-- Using ring tactic for polynomial equalities
theorem square_expand (x y : ℤ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by ring

theorem cube_expand (x : ℤ) : (x + 1)^3 = x^3 + 3*x^2 + 3*x + 1 := by ring

-- Difference of squares
theorem diff_of_squares (a b : ℤ) : a^2 - b^2 = (a + b) * (a - b) := by ring

-- ============================================================================
-- REAL NUMBER THEOREMS
-- ============================================================================

-- Absolute value properties
theorem abs_nonneg_example (x : ℝ) : 0 ≤ |x| := abs_nonneg x

-- Triangle inequality
theorem triangle_ineq (x y : ℝ) : |x + y| ≤ |x| + |y| := abs_add_le x y

-- Square of real is non-negative
theorem sq_nonneg_example (x : ℝ) : 0 ≤ x^2 := sq_nonneg x

-- ============================================================================
-- SET THEORY THEOREMS
-- ============================================================================

-- Set intersection is commutative
theorem set_inter_comm {α : Type*} (A B : Set α) : A ∩ B = B ∩ A := Set.inter_comm A B

-- Set union is commutative
theorem set_union_comm {α : Type*} (A B : Set α) : A ∪ B = B ∪ A := Set.union_comm A B

-- De Morgan for sets: complement of union
theorem set_deMorgan_union {α : Type*} (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := Set.compl_union A B

-- De Morgan for sets: complement of intersection
theorem set_deMorgan_inter {α : Type*} (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := Set.compl_inter A B

-- Subset transitivity
theorem subset_trans_example {α : Type*} (A B C : Set α) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
  Set.Subset.trans h1 h2

-- ============================================================================
-- GROUP THEORY BASICS
-- ============================================================================

-- In a group, (a * b)⁻¹ = b⁻¹ * a⁻¹
theorem group_inv_mul {G : Type*} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  mul_inv_rev a b

-- Double inverse equals original
theorem group_inv_inv {G : Type*} [Group G] (a : G) : a⁻¹⁻¹ = a := inv_inv a

-- Identity element property
theorem group_mul_one {G : Type*} [Group G] (a : G) : a * 1 = a := mul_one a

-- ============================================================================
-- NUMBER THEORY WITH DECIDABILITY
-- ============================================================================

-- Every natural number is either even or odd
theorem even_or_odd (n : Nat) : Even n ∨ Odd n := Nat.even_or_odd n

-- 2 is prime
theorem two_prime : Nat.Prime 2 := Nat.prime_two

-- 3 is prime
theorem three_prime : Nat.Prime 3 := Nat.prime_three

-- ============================================================================
-- PROOF AUTOMATION WITH AESOP AND SIMP
-- ============================================================================

-- Simp can solve many simple goals automatically
theorem simp_example (n : Nat) : n + 0 = n := by simp

-- More complex simp usage
theorem simp_list_example (xs : List Nat) : (xs ++ []).length = xs.length := by simp

-- Using decide for computable propositions
theorem decide_example : 2 + 2 = 4 := by decide

-- ============================================================================
-- FINSET (FINITE SETS)
-- ============================================================================

-- Sum over empty finset is zero
theorem finset_sum_empty : (∅ : Finset Nat).sum (fun x => x) = 0 := Finset.sum_empty

-- ============================================================================
-- ADVANCED LOGIC WITH CLASSICAL REASONING
-- ============================================================================

-- Proof by contradiction
theorem by_contra_example (P : Prop) : ¬¬P → P := by
  intro hnnp
  by_contra hp
  exact hnnp hp

-- Excluded middle
theorem em_example (P : Prop) : P ∨ ¬P := Classical.em P

-- Double negation elimination using classical logic
theorem dne_classical (P : Prop) : ¬¬P ↔ P := not_not
