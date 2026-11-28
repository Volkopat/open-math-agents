import Mathlib

/-!
# A308394: Numbers which can be written in the form m^k - m with m prime and k a positive integer.

Source: https://oeis.org/A308394
Credit: @luciusacarr

Data: 0, 2, 6, 14, 20, 24, 30, 42, 62, 78, 110, 120, 126, 156, 240, ...

The entry says: the only known terms which have two representations where m is prime are 6 and
2184. It is conjectured by Bennett these are the only terms with this property. `main` states
that conjecture. (6 = 2^3 - 2 = 3^2 - 3 and 2184 = 3^7 - 3 = 13^3 - 13.)

Reading of the source:
* A representation of `N` is a pair `(m, k)` with `m` prime, `k ≥ 1` and `N = m^k - m`.
  "Two representations" means two different such pairs.
* The term 0 is excluded: `0 = m^1 - m` for every prime `m`, so it trivially has infinitely many
  representations, and the entry's statement is about the positive terms.
* "These are the only terms with this property" is stated as: a positive `N` has two different
  representations if and only if `N = 6` or `N = 2184` (no other such N with prime base below
  20000 and value below 10^9, checked numerically).
* Related upstream statement: `statements/mse-3202090.lean` states the odd-prime case (only
  2184); the claim here also allows the prime 2 and so also covers 6 = 2^3 - 2 = 3^2 - 3.
-/

namespace OMA.S_oeis_a308394

/-- `N` has two different representations `p^a - p = q^b - q` with `p, q` prime, `a, b ≥ 1`. -/
def HasTwoReps (N : ℕ) : Prop :=
  ∃ p a q b : ℕ, p.Prime ∧ q.Prime ∧ 1 ≤ a ∧ 1 ≤ b ∧ (p, a) ≠ (q, b) ∧
    N = p ^ a - p ∧ N = q ^ b - q

theorem main :
    -- Bennett: 6 and 2184 are the only positive terms with two representations.
    ∀ N : ℕ, 0 < N → (HasTwoReps N ↔ (N = 6 ∨ N = 2184)) := by
  sorry

end OMA.S_oeis_a308394
