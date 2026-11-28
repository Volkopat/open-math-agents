import OMAReductions.R_Erdos398_erdos_398_R1
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Ring.Parity

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H1 := fun n hn => by
  obtain ⟨v, hv⟩ := Nat.dvd_factorial (by decide : 0 < 4) hn
  rw [hv, Nat.mul_div_cancel_left _ (by norm_num)]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨x, rfl⟩ : ∃ x, m = 2 * x + 1 := ⟨m / 2, by
      rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩ <;> ring_nf at hm <;> omega⟩
    exact ⟨x, by nlinarith⟩
  · rintro ⟨x, rfl⟩
    exact ⟨2 * x + 1, by ring⟩
