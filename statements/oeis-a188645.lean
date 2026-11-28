import Mathlib

/-!
# A188645: Array of ((k^n)+(k^(-n)))/2 where k=(sqrt(x^2+1)+x)^2 for integers x>=1

Source: https://oeis.org/A188645
Credit: @xor2k

Formalizes the OEIS A188645 conjecture:
Conjecture: Given function f(x, y)=(sqrt(x^2+y)+x)^2; and constant k=f(x, y); then for all
integers x>=1 and y=[+-]1, k may be irrational, but ((k^n)+(k^(-n)))/2 always produces integer
sequences; y=1 results shown here; y=-1 results are A188644.

Conventions:
* `k x y = (Real.sqrt (x^2 + y) + x)^2` as a real number, for integers `x ≥ 1` and `y ∈ {1, -1}`
  (for `y = -1` the radicand `x^2 - 1` is nonnegative, so `Real.sqrt` is the true square root).
* The array columns are indexed by `n ≥ 0` (offset 0), so `n : ℕ`; `k^n` and `k^(-n)` are integer
  powers (`zpow`) in `ℝ`.
* Producing integer sequences means: for every such `x`, `y`, `n`, the real number
  `(k^n + k^(-n)) / 2` equals some integer. The clause that `k may be irrational` asserts nothing
  and is not formalized.
-/

namespace OMA.S_oeis_a188645

/-- `f(x, y) = (sqrt(x^2 + y) + x)^2` as a real number. -/
noncomputable def k (x y : ℤ) : ℝ :=
  (Real.sqrt ((x : ℝ) ^ 2 + y) + x) ^ 2

/-- For all integers `x ≥ 1`, `y = ±1` and `n ≥ 0`, `(k^n + k^(-n)) / 2` is an integer. -/
theorem main :
    ∀ x y : ℤ, 1 ≤ x → (y = 1 ∨ y = -1) → ∀ n : ℕ,
      ∃ m : ℤ, ((k x y) ^ (n : ℤ) + (k x y) ^ (-(n : ℤ))) / 2 = m := by
  sorry

end OMA.S_oeis_a188645
