import Mathlib

/-!
# Sum of the first T terms of a(r+1) = a(r) + a(r)^2 started at 1/T

Source: https://mathoverflow.net/questions/469329
Asked by MathOverflow user Guest_User_101.

Fix `T ∈ ℕ` and consider the recurrence `a_{r+1} = a_r + a_r^2` with `a_0 = 1/T`.
The question asks to prove that `∑_{r=0}^{T-1} a_r = Ω(log T)`.

Translation choices.
* `seq T r` is the term `a_r` of the recurrence started at `a_0 = 1/T`, as a real number.
* `Ω(log T)` is spelled out in the usual way: there are a constant `c > 0` and a threshold
  `T₀` such that the sum is at least `c * log T` for every `T ≥ T₀`.
-/

namespace OMA.S_mo_469329

/-- The recurrence `a_0 = 1/T`, `a_{r+1} = a_r + a_r^2`. -/
noncomputable def seq (T : ℕ) : ℕ → ℝ
  | 0 => 1 / (T : ℝ)
  | r + 1 => seq T r + seq T r ^ 2

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      c * Real.log T ≤ ∑ r ∈ Finset.range T, seq T r := by
  sorry

end OMA.S_mo_469329
