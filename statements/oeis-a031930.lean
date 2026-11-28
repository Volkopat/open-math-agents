import Mathlib

/-!
# A031930: Lower prime of a difference of 12 between consecutive primes.

Source: https://oeis.org/A031930
Credit: @jagraj28

Conjecture (Jahangeer Kholdi and Farideh Firoozbakht, 2014, stated in A031930): the sequence is
infinite and for every `n`, `a(n+1) < a(n) ^ (1 + 1/n)`; that is, `a(n) ^ (1/n)` is strictly
decreasing.

Formalization notes:
* `p` is a term when `p` and `p + 12` are prime and no number strictly between them is prime
  (they are consecutive primes).
* The sequence has offset 1: `a(n) = Nat.nth IsTerm (n - 1)` for `n ≥ 1`, so `a(n + 1)` is
  `Nat.nth IsTerm n`.
* The exponent `1 + 1/n` is real, so the inequality is stated in `ℝ` with `Real.rpow`.
* `main` is the conjunction of the two conjectures. A direct computation finds 65513 terms below
  `10 ^ 7` and no violation of the inequality among them.
-/

namespace OMA.S_oeis_a031930

/-- `p` and `p + 12` are consecutive primes. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ (p + 12).Prime ∧ ∀ q, p < q → q < p + 12 → ¬ q.Prime

/-- The conjecture of A031930: the sequence is infinite and `a(n+1) < a(n) ^ (1 + 1/n)` for
`n ≥ 1`. -/
theorem main :
    {p : ℕ | IsTerm p}.Infinite ∧
      ∀ n : ℕ, 1 ≤ n →
        (Nat.nth IsTerm n : ℝ) < (Nat.nth IsTerm (n - 1) : ℝ) ^ (1 + 1 / (n : ℝ)) := by
  sorry

end OMA.S_oeis_a031930
