import Mathlib

/-!
# Permanents of integer matrices of finite order

Source: https://mathoverflow.net/questions/371412
Asked by MathOverflow user Mare.

Question 1 of the post: if `M` is an `n × n` matrix with integer entries such that `M ^ k` is
the identity matrix for some `k ≥ 1`, is the permanent of `M` nonzero?

Translation choices.
* `M` is a `Matrix (Fin n) (Fin n) ℤ` and `Matrix.permanent` is the usual permanent
  `∑ σ, ∏ i, M (σ i) i`.
* `main` is the affirmative answer to Question 1, for every size `n` (for `n = 0` the
  permanent of the empty matrix is `1`). Question 2 of the post (the largest absolute value of
  the permanent for entries in `{-1, 0, 1}`) is not formalized here.
-/

namespace OMA.S_mo_371412

theorem main :
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ), 1 ≤ k → M ^ k = 1 →
      M.permanent ≠ 0 := by
  sorry

end OMA.S_mo_371412
