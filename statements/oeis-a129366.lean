import Mathlib

/-!
# A129366: a(n) = Sum_{k=0..floor(n/2)} A000108(n-k).

Source: https://oeis.org/A129366 (conjecture by R. J. Mathar, Feb 05 2015)

`a(n)` (offset 0) is defined as in the title: `a(n) = Sum_{k=0..floor(n/2)} C(n-k)`, where
`C(m) = A000108(m)` is the `m`-th Catalan number (Mathlib's `catalan`). The values are taken in `ℚ`.

The conjecture, stated for `n >= 6` (where every index is defined):
Conjecture: n*(12*n+35)*(n-1)*a(n) + (n-1)*(12*n^2-701*n+1236)*a(n-1) + 2*(6*n^3-385*n^2+2285*n-3432)*a(n-2) + 4*(-405*n^3+5313*n^2-19970*n +23175)*a(n-3) + 8*(156*n^3-1724*n^2+5498*n-5175)*a(n-4) + 16*(393*n^3-4981*n^2+20393*n-26820)*a(n-5) - 32*(n-5)*(93*n-268)*(2*n-9)*a(n-6) = 0.
-/

namespace OMA.S_oeis_a129366

/-- `a(n) = Sum_{k=0..floor(n/2)} A000108(n-k)`. -/
def a (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n / 2 + 1), (catalan (n - k) : ℚ)

theorem main : ∀ n : ℕ, 6 ≤ n →
      ((n : ℚ)*(12*(n : ℚ)+35)*((n : ℚ)-1)) * a n +
        (((n : ℚ)-1)*(12*(n : ℚ)^2-701*(n : ℚ)+1236)) * a (n - 1) +
        (2*(6*(n : ℚ)^3-385*(n : ℚ)^2+2285*(n : ℚ)-3432)) * a (n - 2) +
        (4*(-405*(n : ℚ)^3+5313*(n : ℚ)^2-19970*(n : ℚ) +23175)) * a (n - 3) +
        (8*(156*(n : ℚ)^3-1724*(n : ℚ)^2+5498*(n : ℚ)-5175)) * a (n - 4) +
        (16*(393*(n : ℚ)^3-4981*(n : ℚ)^2+20393*(n : ℚ)-26820)) * a (n - 5) +
        (-32*((n : ℚ)-5)*(93*(n : ℚ)-268)*(2*(n : ℚ)-9)) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a129366
