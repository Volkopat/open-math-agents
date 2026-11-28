import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

/-! Each target x+N has exactly |S| covering shifts: they form the reflected
copy x+N−S inside [0,2N). Count the tuples missing a point by taking a union
of Cartesian powers of these complements. -/

open Finset

private theorem union_threshold (N q s : ℕ) (hN : 0 < N) (hs : s ≤ N)
    (h : 2*(N:ℝ)*Real.log N < q*s) : N*(2*N-s)^q < (2*N)^q := by
  let D : ℝ := 2*N
  have hD : 0 < D := by dsimp [D]; positivity
  have hx : ((2*N-s : ℕ) : ℝ) / D ≤ Real.exp (-(s:ℝ)/D) := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
    change (D-s)/D ≤ _
    rw [sub_div, div_self hD.ne']
    rw [neg_div]
    linarith [Real.add_one_le_exp (-((s:ℝ)/D))]
  have hq : Real.log N + q*(-(s:ℝ)/D) < 0 := by
    have ht : Real.log N < q*(s:ℝ)/D := (lt_div_iff₀ hD).mpr (by dsimp [D]; linarith)
    rw [neg_div, mul_neg, ← sub_eq_add_neg, ← mul_div_assoc]
    exact sub_neg.mpr ht
  have hratio : (N:ℝ)*(((2*N-s:ℕ):ℝ)/D)^q < 1 := calc
    _ ≤ (N:ℝ)*Real.exp (-(s:ℝ)/D)^q := by gcongr
    _ = Real.exp (Real.log N + q*(-(s:ℝ)/D)) := by
      rw [Real.exp_add, Real.exp_log (by exact_mod_cast hN), Real.exp_nat_mul]
    _ < 1 := Real.exp_lt_one_iff.mpr hq
  rw [div_pow, ← mul_div_assoc, div_lt_one (pow_pos hD q)] at hratio
  dsimp [D] at hratio
  exact_mod_cast hratio

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H2 := by
  intro N q S hN _ hS h
  let shifts := range (2*N)
  let good (x : ℕ) := S.image (fun b => x+N-b)
  let bad (x : ℕ) := Fintype.piFinset (fun _ : Fin q => shifts \ good x)
  let allShifts := Fintype.piFinset (fun _ : Fin q => shifts)
  have hcard (x) (hx : x ∈ Icc 1 N) : (bad x).card = (2*N-S.card)^q := by
    have hsub : good x ⊆ shifts := by
      rintro _ hu
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hu
      have := mem_Icc.mp (hS hb)
      have := mem_Icc.mp hx
      exact mem_range.mpr (by omega)
    have hgood : (good x).card = S.card := by
      apply card_image_of_injOn
      intro b hb c hc he
      have := mem_Icc.mp (hS hb)
      have := mem_Icc.mp (hS hc)
      dsimp at he
      omega
    simp [bad, card_sdiff_of_subset hsub, hgood, shifts]
  have hfewer : ((Icc 1 N).biUnion bad).card < allShifts.card := calc
    _ ≤ ∑ x ∈ Icc 1 N, (bad x).card := card_biUnion_le
    _ = N*(2*N-S.card)^q := by rw [sum_const_nat hcard]; simp
    _ < (2*N)^q := union_threshold N q _ hN (by simpa using card_le_card hS) h
    _ = _ := by simp [allShifts, shifts]
  obtain ⟨f, hf, hnot⟩ := exists_mem_notMem_of_card_lt_card hfewer
  refine ⟨f, fun x hx => ?_⟩
  have hmiss : f ∉ bad x := fun hfx => hnot (mem_biUnion.mpr ⟨x, hx, hfx⟩)
  obtain ⟨i, hi⟩ := not_forall.mp (mt Fintype.mem_piFinset.mpr hmiss)
  have hit : f i ∈ good x := by
    by_contra hbad
    exact hi (mem_sdiff.mpr ⟨Fintype.mem_piFinset.mp hf i, hbad⟩)
  obtain ⟨b, hb, he⟩ := mem_image.mp hit
  have := mem_Icc.mp (hS hb)
  exact ⟨i, b, hb, by omega⟩
