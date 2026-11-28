import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

-- Credit: @PianothShaveck

/-!
# From AP-free cardinality bounds to monochromatic progressions

If the interval has more than `M * r k N` points, one of its `M` color
classes exceeds the maximum size of a k-AP-free subset. The finite bridge
works for any palette size, independently of the eventual bounds below.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1

open Erdos142 Filter

/-- The four-term extremal bound at the parent's color threshold. -/
def H1 : Prop :=
  ∀ᶠ N : ℕ in atTop,
    (r 4 N : ℝ) < (N : ℝ) / (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)

/-- The extremal bound for each fixed length at least five. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∀ᶠ N : ℕ in atTop,
    (r k N : ℝ) < (N : ℝ) / (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)

/-- Every coloring has a monochromatic positive-step progression once the
average size of a color class exceeds the AP-free maximum. -/
theorem monochromatic_of_density_bound {N M k : ℕ} (hM : 0 < M)
    (bound : (r k N : ℝ) < (N : ℝ) / (M : ℝ)) (c : ℕ → Fin M) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k,
      a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a := by
  classical
  have hmass : r k N * M < N := by
    exact_mod_cast (lt_div_iff₀ (Nat.cast_pos.mpr hM : 0 < (M : ℝ))).mp bound
  obtain ⟨color, _, hlarge⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.Icc 1 N) (t := Finset.univ) (f := c) (n := r k N)
    (fun _ _ => Finset.mem_univ _) (by simpa [Nat.mul_comm] using hmass)
  let S := (Finset.Icc 1 N).filter fun x => c x = color
  have hnotfree : ¬ (S : Set ℕ).IsAPOfLengthFree k := by
    intro hfree
    apply hlarge.not_ge
    change S.card ≤ r k N
    unfold r Set.IsAPOfLengthFree.maxCard
    refine le_csSup ?_ ⟨S, Finset.filter_subset _ _, hfree, rfl⟩
    refine ⟨N, ?_⟩
    rintro _ ⟨U, hU, _, rfl⟩
    simpa using Finset.card_le_card hU
  unfold Set.IsAPOfLengthFree at hnotfree
  push Not at hnotfree
  obtain ⟨T, hsub, ⟨a, d, hcard, hterms⟩, hk⟩ := hnotfree
  have hk' : 1 < k := by exact_mod_cast hk
  have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
    rw [hterms]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  have ha : a ∈ T := by simpa using hmem 0 (by omega)
  have hd : 0 < d := by
    by_contra! h
    have he : d = 0 := by omega
    have hs : T = {a} := by
      apply Set.Subset.antisymm _ (Set.singleton_subset_iff.mpr ha)
      rw [hterms, he]
      rintro _ ⟨i, _, rfl⟩
      simp
    rw [hs] at hcard
    exact hk.ne (by simpa using hcard)
  refine ⟨a, d, hd, ?_⟩
  intro i hi
  obtain ⟨hx, hc⟩ := Finset.mem_filter.mp (hsub (hmem i hi) : a + i * d ∈ S)
  exact ⟨hx, hc.trans (Finset.mem_filter.mp (hsub ha : a ∈ S)).2.symm⟩

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H1 := by
  intro hfour hlong k hk
  have hb : ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) < (N : ℝ) / (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
    rcases eq_or_lt_of_le hk with h | h
    · subst k
      exact hfour
    · exact hlong k h
  filter_upwards [hb] with N hN
  exact monochromatic_of_density_bound (by positivity) hN

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1
