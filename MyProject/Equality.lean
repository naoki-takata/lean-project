/-
  Equality Theorems
  Proofs about equality and its properties
-/

-- Equality is reflexive
theorem eq_refl' {α : Type} (a : α) : a = a := rfl

-- Equality is symmetric
theorem eq_symm' {α : Type} (a b : α) (h : a = b) : b = a := h.symm

-- Equality is transitive
theorem eq_trans' {α : Type} (a b c : α) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

-- Substitution: if a = b, then P a → P b
theorem subst {α : Type} {a b : α} (P : α → Prop) (h : a = b) (pa : P a) : P b := by
  rw [← h]
  exact pa

-- Congruence: if a = b, then f a = f b
theorem congr_arg' {α β : Type} (f : α → β) {a b : α} (h : a = b) : f a = f b := by
  rw [h]

-- Congruence for two arguments
theorem congr_arg2 {α β γ : Type} (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β}
    (ha : a₁ = a₂) (hb : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ := by
  rw [ha, hb]

-- If a = b and b = c and c = d, then a = d
theorem eq_trans3 {α : Type} (a b c d : α)
    (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  rw [h1, h2, h3]

-- Equality respects operations
theorem eq_add_left {a b c : Nat} (h : a = b) : c + a = c + b := by
  rw [h]

theorem eq_add_right {a b c : Nat} (h : a = b) : a + c = b + c := by
  rw [h]

theorem eq_mul_left {a b c : Nat} (h : a = b) : c * a = c * b := by
  rw [h]

theorem eq_mul_right {a b c : Nat} (h : a = b) : a * c = b * c := by
  rw [h]
