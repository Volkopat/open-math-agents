import OMAStatements.S_oeis_a329126
import Mathlib

open OMA.S_oeis_a329126

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a329126.main) := by
  intro h
  have ht : (2 : ℕ) ∈ {m : ℕ | 0 < m ∧ ∀ b ≥ 2, 2 ∣ Nat.ofDigits b (Nat.digits 10 m)} := by
    refine ⟨by decide, fun b _ => ?_⟩
    rw [show Nat.digits 10 2 = [2] by decide, Nat.ofDigits_singleton]
  have ha : a 2 = 2 := by
    unfold a
    apply le_antisymm (Nat.sInf_le ht)
    apply le_csInf ⟨2, ht⟩
    intro m hm
    change 0 < m ∧ ∀ b ≥ 2, 2 ∣ Nat.ofDigits b (Nat.digits 10 m) at hm
    have hm' : 2 ∣ m := by
      simpa only [Nat.ofDigits_digits] using hm.2 10 (by decide)
    exact Nat.le_of_dvd hm.1 hm'
  have hk := h 2 (by decide)
  rw [ha] at hk
  exact (by decide : ¬ (Nat.digits 10 2).count 1 = 2) hk