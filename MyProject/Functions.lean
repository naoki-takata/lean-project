/-
  Function Theorems
  Proofs about functions, composition, and properties
-/

-- Identity function
def id' {α : Type} (x : α) : α := x

-- Theorem: for all propositions P, P implies P (identity)
theorem identity (P : Prop) : P → P := fun h => h

-- Associativity of function composition
theorem comp_assoc {α β γ δ : Type} (f : γ → δ) (g : β → γ) (h : α → β) :
    (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

-- If f is injective and f(a) = f(b), then a = b
theorem injective_eq {α β : Type} (f : α → β) (hf : Function.Injective f)
    (a b : α) (h : f a = f b) : a = b :=
  hf h

-- Composition of injective functions is injective
theorem injective_comp {α β γ : Type} (f : β → γ) (g : α → β)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (f ∘ g) := by
  intro a b h
  apply hg
  apply hf
  exact h

-- Composition of surjective functions is surjective
theorem surjective_comp {α β γ : Type} (f : β → γ) (g : α → β)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (f ∘ g) := by
  intro c
  obtain ⟨b, hb⟩ := hf c
  obtain ⟨a, ha⟩ := hg b
  exact ⟨a, by simp [Function.comp, ha, hb]⟩

-- Identity function is injective
theorem id_injective {α : Type} : Function.Injective (id : α → α) := by
  intro a b h
  exact h

-- Identity function is surjective
theorem id_surjective {α : Type} : Function.Surjective (id : α → α) := by
  intro a
  exact ⟨a, rfl⟩

-- Composing with identity on the left
theorem comp_id_left {α β : Type} (f : α → β) : id ∘ f = f := rfl

-- Composing with identity on the right
theorem comp_id_right {α β : Type} (f : α → β) : f ∘ id = f := rfl
