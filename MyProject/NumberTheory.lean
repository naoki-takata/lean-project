/-
  Number Theory Theorems
  Proofs about natural numbers and arithmetic
-/

-- Simple theorem: for all natural numbers n, n + 0 = n
theorem nat_add_zero (n : Nat) : n + 0 = n := rfl

-- Addition is commutative
theorem add_comm_example (a b : Nat) : a + b = b + a := Nat.add_comm a b

-- Addition is associative
theorem add_assoc_proof (a b c : Nat) : (a + b) + c = a + (b + c) :=
  Nat.add_assoc a b c

-- Distributive law: a * (b + c) = a * b + a * c
theorem mul_add_distrib (a b c : Nat) : a * (b + c) = a * b + a * c :=
  Nat.mul_add a b c

-- Sum of first n natural numbers: 0 + 1 + 2 + ... + n = n * (n + 1) / 2
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
    rw [← Nat.add_mul, Nat.add_comm 2 k, Nat.mul_comm]

-- A number is even iff it's divisible by 2
def isEven (n : Nat) : Prop := ∃ k, n = 2 * k

-- Sum of two even numbers is even
theorem even_add_even (a b : Nat) (ha : isEven a) (hb : isEven b) : isEven (a + b) := by
  match ha, hb with
  | ⟨ka, hka⟩, ⟨kb, hkb⟩ =>
    exact ⟨ka + kb, by rw [hka, hkb, Nat.mul_add]⟩

-- A number is odd iff it's not even
def isOdd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

-- Zero is even
theorem zero_is_even : isEven 0 := ⟨0, rfl⟩

-- One is odd
theorem one_is_odd : isOdd 1 := ⟨0, rfl⟩

-- Two is even
theorem two_is_even : isEven 2 := ⟨1, rfl⟩
