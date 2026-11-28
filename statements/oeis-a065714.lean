import Mathlib

/-!
# A065714: Number of 3's in decimal expansion of 2^n.

Source: https://oeis.org/A065714
Credit: @luciusacarr

Conjecture (M. F. Hasler, Jul 09 2025). Any value x = 0, 1, 2, ... occurs only a finite number of
times N(x) = 34, 34, 24, 34, 39, 34, 35, 34, 35, 32, 33, 31, ... in this sequence, for the last time
at well defined indices i(x) = 153, 139, 226, 237, 308, 386, 413, 506, 461, 578, 644, 732, 857, 657,
743, 768, 784, 848, 906, ...

Reading of the source:
* `a n` is the number of digits equal to `3` in the decimal expansion of `2^n` (offset 0), written
  `(Nat.digits 10 (2 ^ n)).count 3`.
* `main` states the three parts of the comment: every value occurs only finitely often; the value
  `x` occurs exactly `N(x)` times for each of the listed values `N(0), ..., N(11)`; and the last
  occurrence of `x` is at index `i(x)` for each of the listed values `i(0), ..., i(18)`.
  ("Last time at index i" means `a (i x) = x` and `a n = x` implies `n ≤ i x`.)
* The listed counts and indices agree with a direct computation of `a n` for `n ≤ 12000`.
-/

namespace OMA.S_oeis_a065714

/-- A065714: the number of 3's in the decimal expansion of `2^n`. -/
def a (n : ℕ) : ℕ := (Nat.digits 10 (2 ^ n)).count 3

/-- The listed numbers of occurrences `N(0), N(1), ...`. -/
def N : List ℕ := [34, 34, 24, 34, 39, 34, 35, 34, 35, 32, 33, 31]

/-- The listed indices of last occurrence `i(0), i(1), ...`. -/
def I : List ℕ :=
  [153, 139, 226, 237, 308, 386, 413, 506, 461, 578, 644, 732, 857, 657, 743, 768, 784, 848, 906]

theorem main :
    (∀ x : ℕ, {n : ℕ | a n = x}.Finite) ∧
    (∀ x : ℕ, x < N.length → Nat.card {n : ℕ | a n = x} = N.getD x 0) ∧
    (∀ x : ℕ, x < I.length → a (I.getD x 0) = x ∧ ∀ n : ℕ, a n = x → n ≤ I.getD x 0) := by
  sorry

end OMA.S_oeis_a065714
