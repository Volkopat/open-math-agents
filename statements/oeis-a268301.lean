import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OMA.S_oeis_a268301

/-!
OEIS A268301: G.f. A(x) = Sum_{n>=0} (a(n)/2) * (x/4)^n satisfies
  -1 = Product_{n>=1} (1 - x^n) * (1 - x^n * A(x)) * (1 - x^(n-1) / A(x)).
Setting y = x/4 and B(y) = Sum_{n>=0} a(n) * y^n (so A(4*y) = B(y)/2), this becomes
  -1 = Product_{n>=1} (1 - 4^n * y^n) * (1 - 2^(2*n-1) * y^n * B(y)) * (1 - 2^(2*n-1) * y^(n-1) / B(y))
over Z[[y]]. For any degree r, factors with n > r + 1 have valuation >= r + 1, so the
coefficient of y^r equals that of the truncated product over n = 1..r+1.
Conjecture: a(n) is odd iff n = 2^k - 1 for some k >= 0.
-/

theorem main : ∀ (B : PowerSeries ℤ),
    PowerSeries.constantCoeff B = 1 →
    (∀ r : ℕ, (if r = 0 then (-1 : ℤ) else 0) =
      PowerSeries.coeff r
        (∏ n ∈ Finset.Icc 1 (r + 1),
          (1 - (4 : PowerSeries ℤ) ^ n * PowerSeries.X ^ n) *
          (1 - (2 : PowerSeries ℤ) ^ (2 * n - 1) * PowerSeries.X ^ n * B) *
          (1 - (2 : PowerSeries ℤ) ^ (2 * n - 1) * PowerSeries.X ^ (n - 1) * Ring.inverse B))) →
    ∀ n : ℕ, Odd (PowerSeries.coeff n B) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

end OMA.S_oeis_a268301
