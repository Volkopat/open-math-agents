import Mathlib

/-!
# A135470: Composite numbers n that divide 2 * sigma(n) - d(n) [that is, 2 * sum of divisors - number of divisors].

Source: https://oeis.org/A135470
Credit: @luciusacarr

The entry records two conjectures: there are no odd terms, and the sequence is infinite. `main`
states both, as a conjunction, in that order. Its terms begin 18, 70, 88, 132, 780, 11096, ...
(18: 2 * sigma(18) - d(18) = 2 * 39 - 6 = 72 = 4 * 18).

Reading of the source:
* `n` is composite: `1 < n` and `n` is not prime.
* `sigma(n)` is the sum of the divisors of `n` and `d(n)` their number; `2 * sigma(n) - d(n)` is
  positive for `n ≥ 1` (each divisor contributes at least `2 - 1`), so the subtraction in `ℕ` is
  exact.
-/

namespace OMA.S_oeis_a135470

/-- `n` is a term of A135470. -/
def IsTerm (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ n ∣ 2 * ArithmeticFunction.sigma 1 n - n.divisors.card

theorem main :
    -- Conjecture 1: there are no odd terms.
    (∀ n : ℕ, IsTerm n → Even n) ∧
    -- Conjecture 2: the sequence is infinite.
    {n : ℕ | IsTerm n}.Infinite := by
  sorry

end OMA.S_oeis_a135470
