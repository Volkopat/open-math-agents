import Mathlib

namespace OMA.S_oeis_a346934

/-- The permanent of an `m × m` integer matrix. -/
def permanent {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) : ℤ :=
  ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, M i (σ i)

/-- The `2n × 2n` matrix with `(i, j)`-entry `i - j` (for `1 ≤ i, j ≤ 2n`, indexed by `Fin (2 * n)`). -/
def diffMatrix (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℤ :=
  Matrix.of fun i j => ((i.val + 1 : ℕ) : ℤ) - ((j.val + 1 : ℕ) : ℤ)

/-- OEIS A346934 Conjecture 1 (congruence part, Zhi-Wei Sun):
For every `n ≥ 1` such that `2 * n + 1` is composite, the permanent of `[i - j]_{1 ≤ i, j ≤ 2n}`
is divisible by `2 * n + 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (2 * n + 1) →
      ((2 * n + 1 : ℕ) : ℤ) ∣ permanent (diffMatrix n) := by
  sorry

end OMA.S_oeis_a346934
