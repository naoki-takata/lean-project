def hello := "world"

-- Simple theorem: for all natural numbers n, n + 0 = n
theorem add_zero (n : Nat) : n + 0 = n := rfl

-- Theorem: for all propositions P, P implies P
theorem identity (P : Prop) : P → P := fun h => h

-- Theorem: addition is commutative (using built-in proof)
theorem add_comm_example (a b : Nat) : a + b = b + a := Nat.add_comm a b

-- Theorem: if a = b and b = c, then a = c
theorem eq_trans_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

-- ============================================================================
-- COMPLICATED THEOREMS
-- ============================================================================

-- Proof by induction: 0 + 1 + 2 + ... + n = n * (n + 1) / 2
-- We prove: 2 * (0 + 1 + 2 + ... + n) = n * (n + 1)
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

theorem sum_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumTo]
    rw [Nat.mul_add, ih]
    -- 2*(k+1) + k*(k+1) = (k+1)*(k+2)
    -- Factor out (k+1): (k+1)*(2 + k) = (k+1)*(k+2)
    rw [← Nat.add_mul, Nat.add_comm 2 k, Nat.mul_comm]

-- De Morgan's Law: ¬(P ∨ Q) ↔ (¬P ∧ ¬Q)
theorem deMorgan_or (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro ⟨hnp, hnq⟩ hpq
    cases hpq with
    | inl hp => exact hnp hp
    | inr hq => exact hnq hq

-- Contrapositive: (P → Q) → (¬Q → ¬P)
theorem contrapositive (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro hpq hnq hp
  exact hnq (hpq hp)

-- List reverse twice equals original
theorem reverse_reverse (α : Type) (xs : List α) : xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons]
    rw [List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [List.singleton_append, ih]

-- Length of concatenated lists
theorem length_append (α : Type) (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons]
    rw [ih, Nat.add_assoc, Nat.add_comm ys.length 1, ← Nat.add_assoc]

-- Distributive law: a * (b + c) = a * b + a * c
theorem mul_add_distrib (a b c : Nat) : a * (b + c) = a * b + a * c :=
  Nat.mul_add a b c

-- Associativity of function composition
theorem comp_assoc {α β γ δ : Type} (f : γ → δ) (g : β → γ) (h : α → β) :
    (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

-- A number is even iff it's divisible by 2
def isEven (n : Nat) : Prop := ∃ k, n = 2 * k

theorem even_add_even (a b : Nat) (ha : isEven a) (hb : isEven b) : isEven (a + b) := by
  match ha, hb with
  | ⟨ka, hka⟩, ⟨kb, hkb⟩ =>
    exact ⟨ka + kb, by rw [hka, hkb, Nat.mul_add]⟩

-- Modus ponens: P ∧ (P → Q) → Q
theorem modus_ponens (P Q : Prop) : P ∧ (P → Q) → Q := by
  intro ⟨hp, hpq⟩
  exact hpq hp

-- Double negation introduction: P → ¬¬P
theorem double_neg_intro (P : Prop) : P → ¬¬P := by
  intro hp hnp
  exact hnp hp

-- Currying: (P ∧ Q → R) ↔ (P → Q → R)
theorem curry_uncurry (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) := by
  constructor
  · intro h hp hq
    exact h ⟨hp, hq⟩
  · intro h ⟨hp, hq⟩
    exact h hp hq

-- Law of excluded middle application: ¬¬P → P (classical logic)
-- Note: This requires classical reasoning
theorem double_neg_elim (P : Prop) : ¬¬P → P := by
  intro hnnp
  by_cases hp : P
  · exact hp
  · exact absurd hp hnnp

-- Proof that addition is associative
theorem add_assoc_proof (a b c : Nat) : (a + b) + c = a + (b + c) :=
  Nat.add_assoc a b c

-- Proof: if f is injective and f(a) = f(b), then a = b
theorem injective_eq {α β : Type} (f : α → β) (hf : Function.Injective f)
    (a b : α) (h : f a = f b) : a = b :=
  hf h

-- Proof: map preserves length
theorem map_length {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.length_cons]
    rw [ih]

-- Logical equivalence is reflexive
theorem iff_refl (P : Prop) : P ↔ P := Iff.rfl

-- Logical equivalence is symmetric
theorem iff_symm (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := Iff.symm

-- Logical equivalence is transitive
theorem iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := Iff.trans

-- Proof: And is commutative
theorem and_comm_proof (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩

-- Proof: Or is commutative
theorem or_comm_proof (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

-- Proof: And distributes over Or
theorem and_or_distrib (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro ⟨hp, hqr⟩
    cases hqr with
    | inl hq => exact Or.inl ⟨hp, hq⟩
    | inr hr => exact Or.inr ⟨hp, hr⟩
  · intro h
    cases h with
    | inl hpq => exact ⟨hpq.1, Or.inl hpq.2⟩
    | inr hpr => exact ⟨hpr.1, Or.inr hpr.2⟩
