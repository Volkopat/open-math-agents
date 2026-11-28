import Mathlib

/-!
# Are the determinants `det[μ(i+j-1)]_{1≤i,j≤n}` and `det[μ(i+j)^2]_{1≤i,j≤n}` always nonzero?

Source: https://mathoverflow.net/questions/302095
Credit: @JeremyDevs

Question (Zhi-Wei Sun, MathOverflow 302095, 2018). Let `μ` be the Möbius function. Are the
Hankel-type determinants `det[μ(i+j-1)]_{1≤i,j≤n}` and `det[μ(i+j)^2]_{1≤i,j≤n}` always nonzero?
The source says "It seems that the answer is positive" (data: OEIS A228548, A228549). `main`
states the affirmative answer for both determinants and every `n ≥ 1`.

Conventions:
* `μ` is `ArithmeticFunction.moebius` (values in `ℤ`); the determinants are of integer matrices.
* The `n × n` matrices are indexed by `Fin n`, so the indices of the source are `i + 1`, `j + 1`
  for `i j : Fin n`: the entry `μ(i + j - 1)` of the source becomes `μ(i + j + 1)` and the entry
  `μ(i + j)^2` becomes `μ(i + j + 2)^2`.
* "Always" is read as: for every positive integer `n` (for `n = 0` the determinant of the empty
  matrix is `1`).
-/

namespace OMA.S_mo_302095

open ArithmeticFunction in
/-- For every `n ≥ 1` both Hankel-type Möbius determinants are nonzero. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (Matrix.of fun i j : Fin n => moebius (i.val + j.val + 1)).det ≠ 0 ∧
      (Matrix.of fun i j : Fin n => moebius (i.val + j.val + 2) ^ 2).det ≠ 0 := by
  sorry

end OMA.S_mo_302095
