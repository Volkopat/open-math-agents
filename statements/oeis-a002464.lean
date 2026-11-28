import Mathlib

/-!
# OEIS A002464: Hertzsprung's problem, a conjectured formula

Source: https://oeis.org/A002464
`a n` is the number of permutations of length `n` without rising or falling successions
(no two adjacent entries differ by `1`). Conjecture (John Keith):
`a n = ∑_{k=1}^{n} k! * T(n-1, k-1)` for `n > 0`, where `T = A080246` is the signed version
of A035607, given by `T(n,k) = T(n-1,k-1) - T(n-1,k) - T(n-2,k-1)` with `T(0,0) = 1`,
`T(1,0) = -2`, `T(1,1) = 1` and `T(n,k) = 0` for `k < 0` or `k > n` (Deléham's recurrence on
the A080246 page).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a002464

/-- The triangle A080246. -/
def T : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | 1, 0 => -2
  | 1, 1 => 1
  | 1, _ + 2 => 0
  | n + 2, 0 => -T (n + 1) 0
  | n + 2, k + 1 => T (n + 1) k - T (n + 1) (k + 1) - T n k

/-- Permutations of `Fin n` with no two adjacent entries differing by `1`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ∀ i j : Fin n, j.val = i.val + 1 →
      (σ j).val ≠ (σ i).val + 1 ∧ (σ i).val ≠ (σ j).val + 1).card

theorem main :
    ∀ n : ℕ, 0 < n →
      (a n : ℤ) = ∑ k ∈ Finset.Icc 1 n, (k.factorial : ℤ) * T (n - 1) (k - 1) := by
  sorry

end OMA.S_oeis_a002464
