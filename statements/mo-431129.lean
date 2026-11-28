import Mathlib

/-!
# Uniform lower bounds for normalized power-sum polynomials

Source: Brendan McKay, https://mathoverflow.net/questions/431129 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)

A partition of k is indexed by the multiplicity of each part of size 1 through k.
For coefficient vectors of maximum absolute value 1, the supremum on the cube
is bounded below by a positive constant depending only on k once n is large
enough. This is the requested positivity of the lower limit of the minimax values.
-/

namespace OMA.S_mo_431129

abbrev Part (k : ℕ) := {e : Fin k → Fin (k+1) // ∑ j, (j.val+1)*(e j).val=k}

noncomputable def moment {n : ℕ} (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  (∑ i, x i^j) / n

noncomputable def form {k n : ℕ} (a : Part k → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ e, a e * ∏ j : Fin k, moment x (j.val+1) ^ (e.val j).val

theorem main : ∀ k : ℕ, 0<k → ∃ c : ℝ, 0<c ∧ ∃ N : ℕ, ∀ n ≥ N,
    ∀ a : Part k → ℝ, (∀ e, |a e|≤1) → (∃ e, |a e|=1) →
      ∃ x : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (-1) 1) ∧ c≤|form a x| := by
  sorry

end OMA.S_mo_431129
