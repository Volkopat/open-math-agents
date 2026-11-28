import Mathlib

/-!
# A305562: the diagonal numerators of A386393

Sources: https://oeis.org/A305562 and https://oeis.org/A386393.

The normalized power-series recurrence is written with the triangular
exponents T(n) = n(n-1)/2. Both indices of the rational triangle are
shifted down by one so its first entry is row 0, column 0.
-/

namespace OMA.S_oeis_a305562

def tri : ℕ → ℕ
  | 0 => 0
  | n+1 => tri n+n

def a : ℕ → ℕ
  | 0 => 1
  | n+1 => ∑ j : Fin (n+1), n.choose j.val * a j.val * 2^(tri (n+1)-tri (j.val+1))
decreasing_by exact j.isLt

def row : ℕ → ℕ → ℚ
  | 0, k => if k = 0 then 1 else 0
  | n+1, 0 => row n n
  | n+1, k+1 => row (n+1) k / 2 + row n k
termination_by n k => (n,k)
decreasing_by all_goals simp_wf; omega

theorem main : ∀ n : ℕ, 0 < n → (a n : ℤ) = (row (n-1) (n-1)).num := by
  sorry

end OMA.S_oeis_a305562
