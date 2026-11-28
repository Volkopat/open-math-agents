import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

-- Step Erdos142.erdos_142.variants.lower.R2.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2
-- Shorter proof: the first three terms force d < 4^j, then one induction keeps every term in block j.
-- Credit: @Cryptokraken974

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB hf ⟨a, d, hd, h⟩
  have P : ∀ j j' : ℕ, j < j' → 4 * 4 ^ j ≤ 4 ^ j' := fun j j' l => by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) l
  have Q := fun j b (m : b ∈ B j) => Finset.mem_Icc.1 (hB j m)
  obtain ⟨j, b, m, e⟩ := h 0 (by omega)
  obtain ⟨j1, b1, m1, e1⟩ := h 1 (by omega)
  obtain ⟨j2, b2, m2, e2⟩ := h 2 (by omega)
  have := Q _ _ m; have := Q _ _ m1; have := Q _ _ m2
  have dj : d < 4 ^ j := by
    rcases lt_trichotomy j j1 with l | rfl | l
    · have := P _ _ l
      rcases lt_trichotomy j1 j2 with l' | rfl | l'
      · have := P _ _ l'; omega
      · omega
      · have := P _ _ l'; omega
    · omega
    · have := P _ _ l; omega
  have A : ∀ i < k, ∃ c ∈ B j, a + i * d = 4 * 4 ^ j + c := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨b, m, e⟩
    | succ i ih =>
      intro hi
      obtain ⟨c, mc, ec⟩ := ih (by omega)
      obtain ⟨j', c', mc', ec'⟩ := h _ hi
      have := Q _ _ mc; have := Q _ _ mc'
      rw [add_mul] at ec'
      rcases lt_trichotomy j j' with l | rfl | l
      · have := P _ _ l; omega
      · exact ⟨c', mc', by rw [add_mul]; exact ec'⟩
      · have := P _ _ l; omega
  exact hf j ⟨b, d, hd, fun i hi => by
    obtain ⟨c, mc, ec⟩ := A i hi
    exact (show b + i * d = c by omega) ▸ mc⟩
