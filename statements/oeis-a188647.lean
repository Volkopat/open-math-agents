import Mathlib

/-!
# A188647: array of a(n) = a(n-1)*k - ((k-1)/(k^n)), a(0) = 1, k = (sqrt(x^2+1)+x)^2

Source: https://oeis.org/A188647
Credit: @xor2k

Formalizes the OEIS A188647 conjecture:
Conjecture: Given function f(x, y)=(sqrt(x^2+y)+x)^2; constant k=f(x, y); and initial term a(0)=1;
then for all integers x>=1 and y=[+-]1, k may be irrational, but sequence
a(n)=a(n-1)*k-((k-1)/(k^n)) always produces integer sequences; y=1 results shown here;
y=-1 results are A188646.

Conventions:
* `k x y = (Real.sqrt (x ^ 2 + y) + x) ^ 2` as a real number (for `x ≥ 1`, `y = ±1` the radicand
  is nonnegative and `k ≥ 1`, so all divisions below are by positive reals).
* `a x y n` is the real sequence with `a x y 0 = 1` and
  `a x y (n + 1) = a x y n * k x y - (k x y - 1) / (k x y) ^ (n + 1)` for `n ≥ 0`, i.e. the OEIS
  recurrence for `n ≥ 1`.
* The claim that the sequence is an integer sequence is: every term equals some integer.
  The statement covers both `y = 1` (this array) and `y = -1` (A188646), as the conjecture does.
-/

namespace OMA.S_oeis_a188647

/-- The constant `k = f(x, y) = (sqrt(x ^ 2 + y) + x) ^ 2`. -/
noncomputable def k (x y : ℤ) : ℝ :=
  (Real.sqrt ((x : ℝ) ^ 2 + y) + x) ^ 2

/-- `a(0) = 1`, `a(n) = a(n - 1) * k - (k - 1) / k ^ n`. -/
noncomputable def a (x y : ℤ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => a x y n * k x y - (k x y - 1) / k x y ^ (n + 1)

/-- For all integers `x ≥ 1` and `y = ±1`, every term `a(n)` is an integer. -/
theorem main :
    ∀ x y : ℤ, 1 ≤ x → (y = 1 ∨ y = -1) → ∀ n : ℕ, ∃ z : ℤ, a x y n = z := by
  sorry

end OMA.S_oeis_a188647
