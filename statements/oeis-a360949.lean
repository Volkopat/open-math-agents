import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a360949

/-!
OEIS A360949: G.f. A(x) satisfies 1 = Sum_{n>=0} (-x/2)^n * (A(x)^n + (-1)^n)^n.
Clearing denominators by multiplying the coefficient of x^r by 2^r gives the exact
integer power series recurrence over Z[[x]].
Conjecture: a(0) = 1; for k >= 1, a(2*k) == 0 (mod 4), and for n >= 0,
a(2*n + 1) == 2 (mod 4) iff A010060(n) != A010060(n + 2) (i.e. n in A161674),
where A010060 is the Thue-Morse sequence (popcount mod 2), otherwise a(2*n + 1) == 0 (mod 4).
-/

/-- The Thue-Morse sequence A010060(n) = binary digit sum of n mod 2. -/
def thueMorse (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n % 2 + thueMorse (n / 2)) % 2

theorem main : ∀ (A : PowerSeries ℤ),
    PowerSeries.constantCoeff A = 1 →
    (∀ r : ℕ, (if r = 0 then (1 : ℤ) else 0) =
      ∑ n ∈ Finset.range (r + 1),
        (2 : ℤ) ^ (r - n) * (-1 : ℤ) ^ n *
          PowerSeries.coeff r (PowerSeries.X ^ n * (A ^ n + (-1 : PowerSeries ℤ) ^ n) ^ n)) →
    (∀ k : ℕ, 1 ≤ k → PowerSeries.coeff (2 * k) A % 4 = 0) ∧
    (∀ n : ℕ, PowerSeries.coeff (2 * n + 1) A % 4 =
      if thueMorse n ≠ thueMorse (n + 2) then 2 else 0) := by
  sorry

end OMA.S_oeis_a360949
