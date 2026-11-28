import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Defs

/-!
# Mathar's recurrence for OEIS A026019

Source: https://oeis.org/A026019 (OEIS Foundation, CC BY-SA 4.0).
The offset is zero. The formula is choose(3n,n) minus choose(3n,n-3),
with the second binomial coefficient zero at a negative lower index.
The recurrence starts at n=2 so all three indices are nonnegative.
-/

namespace OMA.S_oeis_a026019

def a (n : ℕ) : ℚ := ((3*n).choose n : ℚ) -
  (if 3 ≤ n then ((3*n).choose (n-3) : ℚ) else 0)

theorem main : ∀ n : ℕ, 2 ≤ n →
    -2*(2*(n:ℚ)+3)*(13*(n:ℚ)-9)*((n:ℚ)+1)*a n +
      (499*(n:ℚ)^3-7*(n:ℚ)^2-120*(n:ℚ)-54)*a (n-1) -
      3*(3*(n:ℚ)-5)*(37*(n:ℚ)-24)*(3*(n:ℚ)-4)*a (n-2) = 0 := by
  sorry

end OMA.S_oeis_a026019
