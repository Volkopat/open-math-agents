import OMAStatements.S_mse_2390542
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2390542.main) := by
  intro conjecture
  obtain ⟨s, t, u, v, _, hp, hst, huv, _⟩ := conjecture 1 1 (by decide)
  have hsum : u + v = 4 := by omega
  have hu : u ≤ 4 := by omega
  have hv : v = 4 - u := by omega
  subst v
  revert hp
  interval_cases u <;> decide