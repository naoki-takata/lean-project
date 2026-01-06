/-
  List Theorems
  Proofs about list operations and properties
-/

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

-- Map preserves length
theorem map_length {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.length_cons]
    rw [ih]

-- Empty list appended to any list equals that list
theorem nil_append (α : Type) (xs : List α) : [] ++ xs = xs := rfl

-- Any list appended to empty list equals that list
theorem append_nil (α : Type) (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append]
    rw [ih]

-- Append is associative
theorem append_assoc (α : Type) (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append]
    rw [ih]

-- Length of reversed list equals original length
theorem length_reverse (α : Type) (xs : List α) :
    xs.reverse.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, List.length_append, List.length_cons, List.length_nil]
    rw [ih]

-- Map distributes over append
theorem map_append {α β : Type} (f : α → β) (xs ys : List α) :
    (xs ++ ys).map f = xs.map f ++ ys.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, List.map_cons]
    rw [ih]
