import OMAReductions.R_Erdos711_erdos_711_parts_i_R2_H2_R2

open Finset

theorem OMA.solution : OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R2.H1 := by
  intro U Y q D multiples diffs
  classical
  rw [Nat.mul_sub_one Y.card, ← Finset.offDiag_card]
  apply Finset.card_mul_le_card_mul (fun d z => d ∣ z.1 ∧ d ∣ z.2)
  · intro d hd
    let B := Y.filter (d ∣ ·)
    have hc : q ≤ B.card := multiples d hd
    calc
      q * (q - 1) ≤ B.card * (B.card - 1) := Nat.mul_le_mul hc (Nat.sub_le_sub_right hc 1)
      _ = B.offDiag.card := by rw [Finset.offDiag_card, Nat.mul_sub_one]
      _ ≤ _ := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hz
        exact Finset.mem_filter.mpr ⟨Finset.offDiag_mono (Finset.filter_subset _ _) hz,
          (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
    have bound {a b : ℕ} (ha : a ∈ Y) (hb : b ∈ Y) (hab : a < b) :
        (U.filter fun d => d ∣ a ∧ d ∣ b).card ≤ D := by
      refine (Finset.card_le_card (t := (b - a).divisors) ?_).trans (diffs a ha b hb hab)
      intro d hd
      obtain ⟨_, hda, hdb⟩ := Finset.mem_filter.mp hd
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_sub hdb hda, by omega⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact bound hx hy h
    · simpa only [Finset.bipartiteBelow, and_comm] using bound hy hx h
