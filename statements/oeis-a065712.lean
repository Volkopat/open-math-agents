import Mathlib

/-!
# A065712: Number of 1's in decimal expansion of 2^n.

Source: https://oeis.org/A065712
Credit: @luciusacarr

Conjecture (M. F. Hasler, Jul 09 2025). Any value x = 0, 1, 2, ... occurs only a finite number of
times N(x) = 26, 34, 30, 40, 26, 33, 39, 30, 30, 30, 38, ... in this sequence, for the last time
at well defined indices i(x) = 91, 152, 185, 412, 245, 505, 346, 422, 499, 565, 529, 575, ...

Reading of the source:
* `a n` is the number of digits equal to `1` in the decimal expansion of `2^n` (offset 0), written
  `(Nat.digits 10 (2 ^ n)).count 1`.
* `main` states the three parts of the comment: every value occurs only finitely often; the value
  `x` occurs exactly `N(x)` times for each of the listed values `N(0), ..., N(10)`; and the last
  occurrence of `x` is at index `i(x)` for each of the listed values `i(0), ..., i(11)`.
  ("Last time at index i" means `a (i x) = x` and `a n = x` implies `n ≤ i x`.)
* The listed counts and indices agree with a direct computation of `a n` for `n ≤ 12000`.
-/

namespace OMA.S_oeis_a065712

/-- A065712: the number of 1's in the decimal expansion of `2^n`. -/
def a (n : ℕ) : ℕ := (Nat.digits 10 (2 ^ n)).count 1

/-- The listed numbers of occurrences `N(0), N(1), ...`. -/
def N : List ℕ := [26, 34, 30, 40, 26, 33, 39, 30, 30, 30, 38]

/-- The listed indices of last occurrence `i(0), i(1), ...`. -/
def I : List ℕ := [91, 152, 185, 412, 245, 505, 346, 422, 499, 565, 529, 575]

theorem main :
    (∀ x : ℕ, {n : ℕ | a n = x}.Finite) ∧
    (∀ x : ℕ, x < N.length → Nat.card {n : ℕ | a n = x} = N.getD x 0) ∧
    (∀ x : ℕ, x < I.length → a (I.getD x 0) = x ∧ ∀ n : ℕ, a n = x → n ≤ I.getD x 0) := by
  sorry

end OMA.S_oeis_a065712
