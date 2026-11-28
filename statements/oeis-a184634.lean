import Mathlib

/-!
# A184634: a(n) = floor(1/{(10+n^4)^(1/4)}), where {}=fractional part.

Source: https://oeis.org/A184634
Credit: @agchua

Formula lines of A184634 (Robert Israel, Feb 25 2019), verbatim:
  2*n^3/5 + 3/(2*n) > 1/{(10+n^4)^(1/4)} > 2*n^3/5 for all n.
  From this we can show that a(5*k) = 50*k^3 for k >= 1,
  a(5*k+1) = 50*k^3 + 30*k^2 + 6*k for k >= 1,
  a(5*k+2) = 50*k^3 + 60*k^2 + 24*k + 3,
  a(5*k+3) = 50*k^3 + 90*k^2 + 54*k + 10 for k >= 1,
  a(5*k+4) = 50*k^3 + 120*k^2 + 96*k + 25.
  This implies the conjectured recurrence for n >= 12.
The conjectured recurrence is the formula line of the entry:
  It appears that a(n)=3a(n-1)-3a(n-2)+a(n-3)+a(n-5)-3a(n-6)+3a(n-7)-a(n-8).
The offset is 1, so the inequality is stated for n >= 1 (at n = 0 the term 3/(2*n) is
undefined). The formulas for 5*k+2 and 5*k+4 carry no condition on k and are stated for all
k >= 0. {x} is the fractional part (Int.fract) and the fourth root is the real power with
exponent 1/4.
-/

namespace OMA.S_oeis_a184634

/-- A184634: a(n) = floor(1/{(10+n^4)^(1/4)}). -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊1 / Int.fract (((10 : ℝ) + (n : ℝ) ^ 4) ^ ((1 : ℝ) / 4))⌋

theorem main :
    (∀ n : ℕ, 1 ≤ n →
      2 * (n : ℝ) ^ 3 / 5 + 3 / (2 * (n : ℝ)) >
          1 / Int.fract (((10 : ℝ) + (n : ℝ) ^ 4) ^ ((1 : ℝ) / 4)) ∧
        1 / Int.fract (((10 : ℝ) + (n : ℝ) ^ 4) ^ ((1 : ℝ) / 4)) > 2 * (n : ℝ) ^ 3 / 5) ∧
    (∀ k : ℕ, 1 ≤ k → a (5 * k) = 50 * (k : ℤ) ^ 3) ∧
    (∀ k : ℕ, 1 ≤ k → a (5 * k + 1) = 50 * (k : ℤ) ^ 3 + 30 * (k : ℤ) ^ 2 + 6 * (k : ℤ)) ∧
    (∀ k : ℕ, a (5 * k + 2) = 50 * (k : ℤ) ^ 3 + 60 * (k : ℤ) ^ 2 + 24 * (k : ℤ) + 3) ∧
    (∀ k : ℕ, 1 ≤ k →
      a (5 * k + 3) = 50 * (k : ℤ) ^ 3 + 90 * (k : ℤ) ^ 2 + 54 * (k : ℤ) + 10) ∧
    (∀ k : ℕ, a (5 * k + 4) = 50 * (k : ℤ) ^ 3 + 120 * (k : ℤ) ^ 2 + 96 * (k : ℤ) + 25) ∧
    (∀ n : ℕ, 12 ≤ n → a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) + a (n - 5) -
      3 * a (n - 6) + 3 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a184634
