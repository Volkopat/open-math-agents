import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R4

/-!
# Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2

Block j occupies (4 4^j, 5 4^j]. Consecutive blocks are separated by a gap larger than the
length of a block, so an arithmetic progression of length at least three whose first two terms
lie in different blocks has its third term in a gap. Hence the first two terms share a block,
the common difference is less than 4^j, and by induction every term stays in that block. The
progression then translates to one inside B j, which is excluded.
-/

namespace OMA.Helpers

theorem pow4_cases (j j' : ℕ) : j = j' ∨ 4 * 4 ^ j ≤ 4 ^ j' ∨ 4 * 4 ^ j' ≤ 4 ^ j := by
  have step {i k : ℕ} (h : i < k) : 4 * 4 ^ i ≤ 4 ^ k := by
    simpa only [pow_succ'] using ((show (4 : ℕ) ^ (i + 1) ≤ 4 ^ k from Nat.pow_le_pow_right (by decide) h))
  rcases lt_trichotomy j j' with h | h | h
  · exact Or.inr (Or.inl (step h))
  · exact Or.inl h
  · exact Or.inr (Or.inr (step h))

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R4.H2 := by
  intro k hk B hB hfree ⟨a, d, hd, h⟩
  have bounds {j b : ℕ} (hb : b ∈ B j) := Finset.mem_Icc.mp (hB j hb)
  obtain ⟨j0, b0, hb0, e0⟩ := h 0 (by omega)
  obtain ⟨j1, b1, hb1, e1⟩ := h 1 (by omega)
  obtain ⟨j2, b2, hb2, e2⟩ := h 2 (by omega)
  have B0 := bounds hb0
  have B1 := bounds hb1
  have B2 := bounds hb2
  simp only [zero_mul, add_zero, one_mul] at e0 e1
  have j10 : j1 = j0 := by
    rcases pow4_cases j0 j1 with h01 | h01 | h01
    · exact h01.symm
    · rcases pow4_cases j1 j2 with h12 | h12 | h12
      · subst h12; omega
      all_goals omega
    · omega
  subst j10
  have hdP : d < 4 ^ j1 := by omega
  have all : ∀ i, i < k → ∃ b ∈ B j1, a + i * d = 4 * 4 ^ j1 + b := by
    intro i
    induction i with
    | zero => intro _; exact ⟨b0, hb0, by simpa using e0⟩
    | succ i ih =>
      intro hi
      obtain ⟨b, hb, e⟩ := ih (by omega)
      obtain ⟨j, b', hb', e'⟩ := h (i + 1) hi
      have Bi := bounds hb
      have Bs := bounds hb'
      rw [add_mul, one_mul] at e'
      rcases pow4_cases j1 j with rfl | hj | hj
      · exact ⟨b', hb', by simpa [add_mul] using e'⟩
      all_goals exfalso; omega
  apply hfree j1
  refine ⟨a - 4 * 4 ^ j1, d, hd, fun i hi => ?_⟩
  obtain ⟨b, hb, e⟩ := all i hi
  rwa [show a - 4 * 4 ^ j1 + i * d = b by omega]
