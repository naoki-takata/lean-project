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
