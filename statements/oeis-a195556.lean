import Mathlib

/-!
# Recurrence and generating function for OEIS A195556

Source: https://oeis.org/A195556 and the construction in https://oeis.org/A195500.
Credit: Clark Kimberling (sequence), Peter Shiu (continued-fraction method),
Peter J. C. Moses (Mathematica program), R. J. Mathar (recurrence, 2011),
Colin Barker (empirical generating function, 2015), Robert Leshner (@rleshner, formalization).

With r=1/3, Moses takes the first n partial quotients of r+√(1+r²)=(1+√10)/3.
For the convergent p/q the resulting Pythagorean approximation is
(p²−q²)/(2pq). Its reduced positive denominator is A195556(n).
The first nine terms are 1, 12, 24, 35, 468, 900, 1333, 17760, 34188.
The zero constant term fixes the index-one convention in the generating function.
-/

namespace OMA.S_oeis_a195556

/-- The numerator and denominator of the finite continued fraction with n digits.
The pair (1,0) for zero digits gives (⌊r⌋,1) at the first step. -/
noncomputable def conv (r : ℝ) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | n+1 => let u := conv ((r-(⌊r⌋₊ : ℝ))⁻¹) n
           (⌊r⌋₊ * u.1 + u.2, u.1)

/-- Reduced denominator of the Pythagorean approximation, extended by a(0)=0. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    let u := conv ((1+Real.sqrt 10)/3) n
    ((2*(u.1*u.2) / Nat.gcd (2*(u.1*u.2)) (u.1^2-u.2^2) : ℕ) : ℤ)

/-- Mathar's recurrence and Barker's series in denominator-cleared form. The
denominator has constant coefficient 1 in ℤ[[X]]. -/
theorem main :
    (∀ n : ℕ, 10 ≤ n → a n = 37*a (n-3)+37*a (n-6)-a (n-9)) ∧
    (let X : PowerSeries ℤ := PowerSeries.X
     (X^9-37*X^6-37*X^3+1)*PowerSeries.mk a =
       X*(X^6+12*X^5+24*X^4-2*X^3+24*X^2+12*X+1)) := by
  sorry

end OMA.S_oeis_a195556
