import OMAStatements.S_oeis_a182519
import Mathlib

/-! Firoozbakht's conjecture reduced to a prime-gap bound.

Write `p = prime(n)`, `q = prime(n+1)` and `x = (q - p) / p`. Then
`q^n = p^n (1 + x)^n ≤ p^n e^(n x)`, and `e^(n x) < p` as soon as `n (q - p) < p log p`. So
`prime(n+1)^n < prime(n)^(n+1)` follows from the gap bound `n g_n < p_n log p_n`. That is `H1`,
an analytic inequality valid for all `n` and all `2 ≤ p ≤ q`, not progress on the conjecture.
The cases `n ≤ 4` are checked directly (`3 < 4`, `25 < 27`, `343 < 625`, `14641 < 16807`); the
gap bound fails at `n = 2` and `n = 4`, and holds for every `n ≤ 216815` beyond them.

`H2` is the open rest: `n (prime(n+1) - prime(n)) < prime(n) log prime(n)` for `n ≥ 5`, a gap
bound of the strength `g_n < log^2 p_n` (Cramér type).
-/

namespace OMA.R_oeis_a182519_R1

open OMA.S_oeis_a182519

/-- Analytic criterion: a gap with `n (q - p) < p log p` gives `q^n < p^(n+1)`. -/
def H1 : Prop := ∀ n p q : ℕ, 2 ≤ p → p ≤ q →
  (n : ℝ) * ((q : ℝ) - p) < p * Real.log p → q ^ n < p ^ (n + 1)

/-- The open rest: the gap bound `n (p_(n+1) - p_n) < p_n log p_n` for `n ≥ 5`. -/
def H2 : Prop := ∀ n : ℕ, 5 ≤ n →
  (n : ℝ) * ((prime (n + 1) : ℝ) - prime n) < prime n * Real.log (prime n)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a182519.main := by
  intro h1 h2 n hn
  by_cases h5 : 5 ≤ n
  · apply h1 n (prime n) (prime (n + 1)) (Nat.prime_nth_prime (n - 1)).two_le
    · exact Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)
    · exact h2 n h5
  · interval_cases n <;>
      simp [prime, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
        Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]

end OMA.R_oeis_a182519_R1
