import OMAStatements.S_mo_380950
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_380950.main) := fun h => by
  obtain ⟨x, y, z, m, hm, he, hp⟩ := h 1 1 1
  obtain rfl : z = -(x + y) := by linarith
  clear hp
  induction' hk : m.natAbs using Nat.strong_induction_on with k ih generalizing x y m
  have H (a : ℤ) (e : (a : ZMod 4) + a = 0) : ∃ b, a = 2 * b := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a + a) 4).1 (by push_cast; exact e)
    exact ⟨a / 2, by omega⟩
  have := congrArg (Int.cast : ℤ → ZMod 4) he
  push_cast at this
  obtain ⟨a, b, c⟩ := (by decide : ∀ a b c : ZMod 4, a ^ 2 + b ^ 2 + (-(a + b)) ^ 2 = c ^ 2 → a + a = 0 ∧ b + b = 0 ∧ c + c = 0) _ _ _ this
  obtain ⟨x, rfl⟩ := H x a
  obtain ⟨y, rfl⟩ := H y b
  obtain ⟨m, rfl⟩ := H m c
  exact ih _ (by omega) x y m (by omega) (by linarith) rfl
