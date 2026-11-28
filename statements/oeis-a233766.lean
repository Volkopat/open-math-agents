import Mathlib

/-!
# A233766: Digital root of Lucas numbers (A030133) indexed by natural numbers not divisible by 2, 3 or 5 (A007775).

Source: https://oeis.org/A233766

Conjectures from Colin Barker, Sep 22 2019:
  G.f.: x*(2 + 9*x + 6*x^2 + 7*x^3 + 2*x^4 + 9*x^5 + 3*x^6 + 7*x^7 + 9*x^8 + 7*x^9 + 2*x^10
    + 9*x^11 + 3*x^12 + 2*x^13 + 7*x^14 + 6*x^15 + 7*x^16 + 9*x^17 + 3*x^18 + 2*x^19 + 7*x^20
    + 9*x^21 + 6*x^22 + 2*x^23) / ((1 - x)*(1 + x)*(1 - x + x^2)*(1 + x^2)*(1 + x + x^2)
    *(1 - x^2 + x^4)*(1 + x^4)*(1 - x^4 + x^8)).
  a(n) = a(n-24) for n>24.

Conventions:
* A030133 is defined as in its entry: A030133(0) = 2, A030133(1) = 1, and A030133(m+2) is the sum
  of the decimal digits of A030133(m) + A030133(m+1) (these are the digital roots of the Lucas
  numbers).
* A007775(n), n ≥ 1, is the n-th positive integer not divisible by 2, 3 or 5
  (1, 7, 11, 13, 17, 19, 23, 29, 31, ...).
* Indexing: a(n) = A030133(A007775(n) - 1) for n ≥ 1 (offset 1). This is the indexing that
  reproduces the listed data: it gives 2, 9, 6, 7, 2, 9, 3, 7, 9, 7, 2, 9, 3, 2, 7, 6, 7, 9, 3, 2,
  7, 9, 6, 2, the first 24 listed terms. (Read with A030133's own offset 0, A030133(A007775(n)) is
  1, 2, 1, 8, ..., which does not match the data at all.)
* The g.f. is the ordinary generating function Sum_{n >= 1} a(n) x^n (here `a 0 = 0`), stated over
  the rationals with the denominator multiplied out.
-/

namespace OMA.S_oeis_a233766

open PowerSeries

/-- A030133: `2, 1`, then each term is the decimal digit sum of the sum of the two previous terms. -/
def A030133 : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | m + 2 => (Nat.digits 10 (A030133 m + A030133 (m + 1))).sum

/-- A007775(n), `n ≥ 1`: the `n`-th positive integer not divisible by 2, 3 or 5. -/
noncomputable def A007775 (n : ℕ) : ℕ :=
  Nat.nth (fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m) (n - 1)

/-- A233766(n) for `n ≥ 1`, with `a 0 = 0`. -/
noncomputable def a (n : ℕ) : ℕ := if n = 0 then 0 else A030133 (A007775 n - 1)

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) * (1 + X) * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2) * (1 - X ^ 2 + X ^ 4) *
          (1 + X ^ 4) * (1 - X ^ 4 + X ^ 8)) =
      X * (2 + 9 * X + 6 * X ^ 2 + 7 * X ^ 3 + 2 * X ^ 4 + 9 * X ^ 5 + 3 * X ^ 6 + 7 * X ^ 7 +
        9 * X ^ 8 + 7 * X ^ 9 + 2 * X ^ 10 + 9 * X ^ 11 + 3 * X ^ 12 + 2 * X ^ 13 + 7 * X ^ 14 +
        6 * X ^ 15 + 7 * X ^ 16 + 9 * X ^ 17 + 3 * X ^ 18 + 2 * X ^ 19 + 7 * X ^ 20 + 9 * X ^ 21 +
        6 * X ^ 22 + 2 * X ^ 23)) ∧
    ∀ n : ℕ, 24 < n → a n = a (n - 24) := by
  sorry

end OMA.S_oeis_a233766
