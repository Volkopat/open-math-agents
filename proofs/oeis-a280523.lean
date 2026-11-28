import OMAStatements.S_oeis_a280523

-- Credit: @oh-meh
open OMA.S_oeis_a280523

private theorem shifted (k : ℕ) : b k = (Nat.fib (k+3) : ℤ) - ((k+1)/2 : ℕ) - 1 := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h₀ h₁ =>
    rw [b, h₀, h₁, Nat.fib_add_two (n := k+3)]
    rw [show k+1+3 = k+3+1 by omega, Nat.cast_add]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a280523.main := by
  intro n hn
  rw [shifted, a, show 2*n-2+3 = 2*n+1 by omega]
  omega
