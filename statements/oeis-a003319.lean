import Mathlib

/-!
# A003319: connected permutations and the array A370380

Source: https://oeis.org/A003319
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A003319): `a(n) = A370380(n-2, 0)` for `n > 1`, where `a(n)` is the number
of connected (indecomposable) permutations of `[1..n]`: those not fixing `[1..j]` setwise for
any `0 < j < n`.

Conventions:
* `A370380` is the array `A(n, k) = (k+2) A(n-1, k+1) + ∑_{j=0}^{k} A(n-1, j)` with
  `A(0, k) = 1` (from its OEIS entry).
* The entry also states `a(n) = A370381(n-2, 0)`; this file states the `A370380` form.
* Permutations of `Fin n`; "fixing `[1..j]`" means mapping `{0, …, j-1}` onto itself.
-/

namespace OMA.S_oeis_a003319

/-- The array A370380. -/
def A : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, k => (k + 2) * A n (k + 1) + ∑ j ∈ Finset.range (k + 1), A n j

/-- `σ` is a connected permutation of `Fin n`. -/
def IsConnected {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ j : ℕ, 0 < j → j < n → ¬ ∀ i : Fin n, (i : ℕ) < j → ((σ i : Fin n) : ℕ) < j

/-- The number of connected permutations of `Fin n`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {σ : Equiv.Perm (Fin n) // IsConnected σ}

theorem main : ∀ n : ℕ, 1 < n → a n = A (n - 2) 0 := by
  sorry

end OMA.S_oeis_a003319
