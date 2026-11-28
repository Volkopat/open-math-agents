import Mathlib

/-!
# Determinants of Fibonacci-sum graphs

Source: zoha, https://mathoverflow.net/questions/121243 (CC BY-SA 3.0).
Credit: @connoranderson

The vertices are numbered from 1 to n. The graph is simple, so every diagonal
entry is zero, as the author confirmed in the linked cross-post.
-/

namespace OMA.S_mo_121243

noncomputable def adjacency (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := by
  classical
  exact Matrix.of fun i j => if i ≠ j ∧ ∃ k, (i.val + 1) + (j.val + 1) = Nat.fib k then 1 else 0

theorem main : ∀ n : ℕ, 0 < n →
    (Odd n → (adjacency n).det = 0) ∧
    (Even n → (adjacency n).det = 1 ∨ (adjacency n).det = -1 ∨ (adjacency n).det = 0) := by
  sorry

end OMA.S_mo_121243
