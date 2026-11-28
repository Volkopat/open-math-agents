import OMAStatements.S_oeis_a001076

open OMA.S_oeis_a001076 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001076.main := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    change 2 * ((4 * A001076 (n + 2) + A001076 (n + 1) : ℕ) : ℤ) =
      ((4 * A001076 (n + 3) + A001076 (n + 2) : ℕ) : ℤ) -
      ((4 * A001077 (n + 2) + A001077 (n + 1) : ℕ) : ℤ)
    push_cast
    linear_combination 4 * h₁ + h₀
