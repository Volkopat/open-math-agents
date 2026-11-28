import Mathlib

/-!
# A300388: Paths of length 11n from the origin to the line y = 2x/9 staying below or touching it

Source: https://oeis.org/A300388

a(n), offset 0: the number of paths of length 11*n from the origin to the line y = 2*x/9
with unit East and North steps that stay below the line or touch it.
Data: 1, 5, 345, 35246, 4255288, 563796161, ...
Known (Peter Bala, Jan 03 2019, Bizley): a(0) = 1 and for n >= 1,
a(n) = (1/n) * Sum_{k = 0..n-1} (1/11)*binomial(11*n-11*k, 2*n-2*k)*a(k).

Conjecture (Peter Bala, Sep 14 2021): the sequence b(n) := [x^n] A(x)^n, where A(x) is the
o.g.f. of a, satisfies b(p) == b(1) (mod p^3) for prime p >= 5 except p = 11
(checked up to p = 101). Here b(1) = 5.

Formalized: a is defined over ℚ by the Bizley recurrence above (this reproduces the data).
Since [x^n] A(x)^n only depends on a(0), ..., a(n), b(n) is the coefficient of X^n in
(Sum_{k = 0..n} a(k) X^k)^n as a polynomial over ℚ. The congruence is stated as: b(p) is
the image of an integer z with p^3 dividing z - 5 in ℤ. Range: p prime, p >= 5, p ≠ 11.
Checked numerically in exact arithmetic for all primes 5 <= p <= 103 (p = 11 fails).
-/

namespace OMA.S_oeis_a300388

/-- A300388 via the Bizley recurrence, over ℚ. -/
def a : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
    (1 / ((n + 1 : ℕ) : ℚ)) *
      ∑ k : Fin (n + 1),
        (1 / 11 : ℚ) * ((Nat.choose (11 * (n + 1) - 11 * k) (2 * (n + 1) - 2 * k) : ℕ) : ℚ) *
          a k
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (Nat.le_of_lt_succ k.isLt)

/-- The o.g.f. of a truncated after degree n. -/
noncomputable def A (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (a k) * Polynomial.X ^ k

/-- b(n) = [x^n] A(x)^n. -/
noncomputable def b (n : ℕ) : ℚ := ((A n) ^ n).coeff n

theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ 11 →
    ∃ z : ℤ, (z : ℚ) = b p ∧ (p : ℤ) ^ 3 ∣ z - 5 := by
  sorry

end OMA.S_oeis_a300388
