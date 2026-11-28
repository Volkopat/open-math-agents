import Mathlib

/-!
# A300386: Number of paths of length 7*n from the origin to the line y = 2*x/5
with unit East and North steps that stay below the line or touch it.

Source: https://oeis.org/A300386

Offset 0. Peter Bala (Jan 02 2019): the o.g.f. is
A(x) = exp( Sum_{n >= 1} (1/7)*binomial(7*n, 2*n)*x^n/n ), equivalently
a(0) = 1 and a(n) = (1/n) * Sum_{k = 0..n-1} (1/7)*binomial(7*n-7*k, 2*n-2*k)*a(k).
Conjecture (Peter Bala, Sep 14 2021): b(n) := [x^n] A(x)^n satisfies
b(p) == b(1) (mod p^3) for every prime p >= 11 (b(1) = 3).

Formalized: a(n) is defined in ℚ by the recurrence above (Bizley's formula as given in
the entry). Since [x^n] A(x)^n only depends on a(0..n), b(n) is the coefficient of X^n in
the n-th power of the polynomial Sum_{k = 0..n} a(k) X^k. The congruence is stated as:
b(p) - 3 equals p^3 times an integer.
-/

namespace OMA.S_oeis_a300386

/-- Bizley's recurrence for A300386, in ℚ. -/
def a : ℕ → ℚ
  | 0 => 1
  | n + 1 => (1 / ((n + 1 : ℕ) : ℚ)) * ∑ k : Fin (n + 1),
      (1 / 7 : ℚ) * ((Nat.choose (7 * (n + 1 - k.val)) (2 * (n + 1 - k.val)) : ℕ) : ℚ) *
        a k.val
  decreasing_by exact k.isLt

/-- b(n) = [x^n] A(x)^n, using the truncation of A(x) at degree n. -/
noncomputable def b (n : ℕ) : ℚ :=
  ((∑ k ∈ Finset.range (n + 1), Polynomial.C (a k) * Polynomial.X ^ k) ^ n).coeff n

theorem main : ∀ p : ℕ, p.Prime → 11 ≤ p →
    ∃ m : ℤ, b p - 3 = ((p : ℤ) ^ 3 * m : ℤ) := by
  sorry

end OMA.S_oeis_a300386
