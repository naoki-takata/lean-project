/-
  Logic Theorems
  Fundamental logical propositions and their proofs
-/

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

-- Modus ponens: P ∧ (P → Q) → Q
theorem modus_ponens (P Q : Prop) : P ∧ (P → Q) → Q := by
  intro ⟨hp, hpq⟩
  exact hpq hp

-- Double negation introduction: P → ¬¬P
theorem double_neg_intro (P : Prop) : P → ¬¬P := by
  intro hp hnp
  exact hnp hp

-- Law of excluded middle application: ¬¬P → P (classical logic)
theorem double_neg_elim (P : Prop) : ¬¬P → P := by
  intro hnnp
  by_cases hp : P
  · exact hp
  · exact absurd hp hnnp

-- Currying: (P ∧ Q → R) ↔ (P → Q → R)
theorem curry_uncurry (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) := by
  constructor
  · intro h hp hq
    exact h ⟨hp, hq⟩
  · intro h ⟨hp, hq⟩
    exact h hp hq

-- Logical equivalence is reflexive
theorem iff_refl (P : Prop) : P ↔ P := Iff.rfl

-- Logical equivalence is symmetric
theorem iff_symm (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := Iff.symm

-- Logical equivalence is transitive
theorem iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := Iff.trans

-- And is commutative
theorem and_comm_proof (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩

-- Or is commutative
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

-- And distributes over Or
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
