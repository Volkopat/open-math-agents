import Mathlib

/-!
# A182960: G.f.: exp( Sum_{n>=1} C(6n-1,2n-1)*x^n/n )

Source: https://oeis.org/A182960

Definition: A(x) = Sum_{n>=0} a(n) x^n = exp( Sum_{n>=1} C(6n-1,2n-1) x^n / n ), offset 0.
Claim (Peter Bala, Sep 14 2021, formula section): the sequence b(n) := [x^n] A(x)^n
(1, 5, 215, 10463, 537287, ...) conjecturally satisfies b(p) == b(1) (mod p^3)
for every prime p >= 5 (checked up to p = 101 by the author).

Formalized:
* a(n) is defined over the rationals by the logarithmic-derivative recursion equivalent to
  the exp definition: a(0) = 1 and n a(n) = Sum_{k=1}^{n} C(6k-1,2k-1) a(n-k); in the code
  the index k+1 runs over Fin (n+1), and C(6(k+1)-1, 2(k+1)-1) is written C(6k+5, 2k+1).
* A(x) is the formal power series with coefficients a(n); b(n) is the coefficient of x^n
  in A(x)^n, a rational number.
* The congruence b(p) == b(1) (mod p^3) is stated as: b(p) - b(1) equals p^3 times an integer.
  This also asserts that the difference is integral (all a(n) are integers).
-/

namespace OMA.S_oeis_a182960

/-- Coefficients of exp( Sum_{n>=1} C(6n-1,2n-1) x^n / n ). -/
def a : ℕ → ℚ
  | 0 => 1
  | n + 1 => (1 / ((n : ℚ) + 1)) *
      ∑ k : Fin (n + 1), ((Nat.choose (6 * (k : ℕ) + 5) (2 * (k : ℕ) + 1) : ℕ) : ℚ) * a (n - (k : ℕ))
decreasing_by omega

/-- The g.f. A(x). -/
noncomputable def A : PowerSeries ℚ := PowerSeries.mk a

/-- b(n) = [x^n] A(x)^n. -/
noncomputable def b (n : ℕ) : ℚ := PowerSeries.coeff n (A ^ n)

theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∃ c : ℤ, b p - b 1 = ((p : ℚ) ^ 3) * (c : ℚ) := by
  sorry

end OMA.S_oeis_a182960
