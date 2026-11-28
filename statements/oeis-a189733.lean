import Mathlib

/-!
# A189733: Denominator of B(0,n) where B(n,n)=0, B(n-1,n) = (-1)^(n+1)/n, and B(m,n) = B(m+1,n-1) + B(m,n-1), n >= 0, m >= 0, is an array of fractions.

Source: https://oeis.org/A189733
Credit: @agchua

In the formula section of A189733 (entry by Paul Curtz, May 23 2011):
  a(n) = denominator(B(0,n)). Conjecture: a(6*n)=1, a(1+6*n)=1+3*n, a(2+6*n)=1+2*n,
  a(3+6*n)=2+3*n, a(4+6*n)=1, a(5+6*n)=6+6*n. a(n) = 2*a(n-6) - a(n-12).
Row 0 of the array lies on and above its diagonal. There the array is determined by
B(m,m) = 0, B(m,m+1) = (-1)^(m+2)/(m+1) (the value (-1)^(n+1)/n at n = m+1), and, for n ≥ m+2,
B(m,n) = B(m,n-1) + B(m+1,n-1); this is exactly how the Maple program of the entry computes the
entries with n ≥ m. Below, `U d m` stands for B(m, m+d), so B(0,n) = `U n 0`.
The offset is 0. The six closed forms are stated for all n ≥ 0; the recurrence uses a(n-12), so it
is stated for n ≥ 12.
-/

namespace OMA.S_oeis_a189733

/-- `U d m` = B(m, m+d): B(m,m) = 0, B(m,m+1) = (-1)^(m+2)/(m+1),
B(m,m+d+2) = B(m,m+d+1) + B(m+1,m+d+1). -/
def U : ℕ → ℕ → ℚ
  | 0, _ => 0
  | 1, m => (-1) ^ (m + 2) / ((m : ℚ) + 1)
  | d + 2, m => U (d + 1) m + U d (m + 1)

/-- A189733(n) = denominator of B(0,n). -/
def a (n : ℕ) : ℕ := (U n 0).den

/-- The conjectures of A189733: the six closed forms and a(n) = 2 a(n-6) - a(n-12). -/
theorem main :
    (∀ n : ℕ, a (6 * n) = 1 ∧ a (1 + 6 * n) = 1 + 3 * n ∧ a (2 + 6 * n) = 1 + 2 * n ∧
      a (3 + 6 * n) = 2 + 3 * n ∧ a (4 + 6 * n) = 1 ∧ a (5 + 6 * n) = 6 + 6 * n) ∧
    ∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 2 * (a (n - 6) : ℤ) - (a (n - 12) : ℤ) := by
  sorry

end OMA.S_oeis_a189733
