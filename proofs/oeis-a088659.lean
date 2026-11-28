import OMAStatements.S_oeis_a088659
import Mathlib

open OMA.S_oeis_a088659

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a088659.main) := by
  intro h
  have p2 : proposedPeriod 2 = 2 := by decide +kernel
  have p3 : proposedPeriod 3 = 6 := by decide +kernel
  have p6 : proposedPeriod 6 = 12 := by decide +kernel
  have h2 := (h 2 (by norm_num)).1
  have h3 := (h 3 (by norm_num)).1
  have h6 := (h 6 (by norm_num)).2
  rw [p2] at h2
  rw [p3] at h3
  rw [p6] at h6
  have m6 : 6 ∈ tailPeriods 6 := by
    refine ⟨by norm_num, fun k hk => ?_⟩
    have e2 : ∀ j : ℕ, 2 < j → b (j + 2) % 2 = b j % 2 := h2.2
    have a2 : b (k + 6) % 2 = b k % 2 := by
      rw [show k + 6 = (k + 4) + 2 by ring, e2 (k + 4) (by omega), show k + 4 = (k + 2) + 2 by ring,
        e2 (k + 2) (by omega), e2 k (by omega)]
    have a3 : b (k + 6) % 3 = b k % 3 := h3.2 k (by omega)
    have : b (k + 6) ≡ b k [MOD 2 * 3] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num)).mp ⟨a2, a3⟩
    exact this
  have := h6 m6
  norm_num at this
