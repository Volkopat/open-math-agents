import OMAStatements.S_oeis_a034496

/-!
# Proof of OEIS A034496 conjecture

Credit: @AkiRA-COM-FP
-/

open OMA.S_oeis_a034496

theorem OMA.solution : type_of% @OMA.S_oeis_a034496.main := by
  intro n
  refine Nat.not_prime_of_mul_eq (a := 1 + 2 ^ n) (b := 1 + 4 ^ n) ?_ ?_ ?_
  · rw [a, show (8 : ℕ).divisors = {1, 2, 4, 8} by decide]
    simp
    rw [show (8 : ℕ) = 2 * 4 by decide, mul_pow]
    ring
  all_goals
    apply (lt_add_of_pos_right 1 ?_).ne'
    positivity
