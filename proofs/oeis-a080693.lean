import OMAStatements.S_oeis_a080693
import Mathlib

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a080693.main) := by
  intro h
  obtain ⟨p, q, r, s, hp, hq, hr, hs, he⟩ := h 68 (by decide)
  have hp₂ := hp.two_le
  have hq₂ := hq.two_le
  have hr₂ := hr.two_le
  have hs₂ := hs.two_le
  have hp₆ : p < 6 := by
    by_contra! hge
    have hsq : 6 ^ 2 ≤ p ^ 2 := by gcongr
    have hm := Nat.mul_le_mul hsq hq₂
    omega
  have hq₁₈ : q < 18 := by
    have hsq : 2 ^ 2 ≤ p ^ 2 := by gcongr
    have hm := Nat.mul_le_mul_right q hsq
    omega
  have hr₃₅ : r < 35 := by
    have hm := Nat.mul_le_mul_left r hs₂
    omega
  have hs₃₅ : s < 35 := by
    have hm := Nat.mul_le_mul_right s hr₂
    omega
  have hfinite : ∀ p : Fin 6, p.val.Prime → ∀ q : Fin 18, q.val.Prime →
      ∀ r : Fin 35, r.val.Prime → ∀ s : Fin 35, s.val.Prime →
        68 ≠ p.val ^ 2 * q.val + r.val * s.val := by
    decide +kernel
  exact hfinite ⟨p, hp₆⟩ hp ⟨q, hq₁₈⟩ hq ⟨r, hr₃₅⟩ hr ⟨s, hs₃₅⟩ hs he