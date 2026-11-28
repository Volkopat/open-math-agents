import OMAStatements.S_mse_2937341

/-!
# Finitely Additive Translation-Invariant Measure on `ℚ`

We construct a finitely additive, monotone, translation-invariant set function
`m : Set ℚ → ENNReal` vanishing on singletons and assigning `ENNReal.ofReal (b - a)` to
every rational open interval `(a, b) ∩ ℚ`:

1. On `[0, 1) ∩ ℚ`, for each `N : ℕ`, define the uniform probability measure `μN N` on the
   factorial grid `{j / N! | 0 ≤ j < N!}`.
2. Take an ultrafilter limit `μ S := limUnder U (fun N => μN N S)` along a nonprincipal
   ultrafilter `U = Ultrafilter.of Filter.atTop` using compactness of `[0, 1]`.
   Because `r.den ∣ N!` for all `N ≥ r.den`, rational shifts inside `[0, 1)` and wrap-around
   shifts from `[1 - r, 1)` to `[0, r)` induce exact bijections on the grid for all large `N`.
3. Extend `μ` periodically to all of `ℚ` via unit-interval slices
   `m A := ∑' n : ℤ, ENNReal.ofReal (μ {y : ℚ | 0 ≤ y ∧ y < 1 ∧ y + n ∈ A})`,
   which yields `m ∅ = 0`, `m Set.univ = ⊤`, `m {q} = 0`, exact interval lengths
   `m ((a, b) ∩ ℚ) = ENNReal.ofReal (b - a)`, finite additivity, monotonicity, and full
   rational translation invariance.
-/

namespace Mse2937341

open scoped Classical

private noncomputable def U : Ultrafilter ℕ :=
  Ultrafilter.of Filter.atTop

private noncomputable def gridSet (N : ℕ) (S : Set ℚ) : Finset ℕ :=
  (Finset.range N.factorial).filter fun (j : ℕ) => ((j : ℚ) / (N.factorial : ℚ)) ∈ S

private lemma mem_gridSet {N : ℕ} {S : Set ℚ} {j : ℕ} :
    j ∈ gridSet N S ↔ j < N.factorial ∧ ((j : ℚ) / (N.factorial : ℚ)) ∈ S := by
  unfold gridSet
  rw [Finset.mem_filter, Finset.mem_range]

private noncomputable def countN (N : ℕ) (S : Set ℚ) : ℕ :=
  (gridSet N S).card

private noncomputable def μN (N : ℕ) (S : Set ℚ) : ℝ :=
  (countN N S : ℝ) / (N.factorial : ℝ)

private lemma μN_mem_Icc (N : ℕ) (S : Set ℚ) : μN N S ∈ Set.Icc (0 : ℝ) 1 := by
  have hpos : (0 : ℝ) < (N.factorial : ℝ) := by positivity
  refine ⟨by unfold μN; positivity, ?_⟩
  unfold μN countN gridSet
  rw [div_le_one hpos]
  exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_range N.factorial)

private noncomputable def μ (S : Set ℚ) : ℝ :=
  (U : Filter ℕ).limUnder (fun N => μN N S)

private lemma μ_tendsto_and_mem (S : Set ℚ) :
    μ S ∈ Set.Icc (0 : ℝ) 1 ∧ Filter.Tendsto (fun N => μN N S) (U : Filter ℕ) (nhds (μ S)) := by
  have hle : ((U.map (fun N => μN N S)) : Filter ℝ) ≤ Filter.principal (Set.Icc 0 1) := by
    rw [Ultrafilter.coe_map, Filter.map_le_iff_le_comap, Filter.comap_principal]
    exact Filter.le_principal_iff.mpr (Filter.Eventually.of_forall fun N => μN_mem_Icc N S)
  obtain ⟨x, hx_mem, hx_le⟩ := isCompact_Icc.ultrafilter_le_nhds (U.map (fun N => μN N S)) hle
  have htx : Filter.Tendsto (fun N => μN N S) (U : Filter ℕ) (nhds x) := hx_le
  have heq : μ S = x := htx.limUnder_eq
  exact ⟨heq.symm ▸ hx_mem, heq.symm ▸ htx⟩

private lemma μ_nonneg (S : Set ℚ) : 0 ≤ μ S :=
  (μ_tendsto_and_mem S).1.1

private lemma μ_eq_of_tendsto (S : Set ℚ) (c : ℝ)
    (h : Filter.Tendsto (fun N => μN N S) Filter.atTop (nhds c)) : μ S = c :=
  tendsto_nhds_unique (μ_tendsto_and_mem S).2 (h.mono_left (Ultrafilter.of_le Filter.atTop))

private lemma μ_eq_of_eventually_eq (S T : Set ℚ)
    (h : ∀ᶠ N in Filter.atTop, μN N S = μN N T) : μ S = μ T := by
  have hU : ∀ᶠ N in (U : Filter ℕ), μN N S = μN N T :=
    Ultrafilter.of_le Filter.atTop h
  exact tendsto_nhds_unique (μ_tendsto_and_mem S).2
    ((μ_tendsto_and_mem T).2.congr' (hU.mono fun _ h => h.symm))

private lemma μ_empty : μ ∅ = 0 := by
  refine μ_eq_of_tendsto ∅ 0 ?_
  have h0 : (fun N => μN N ∅) = fun _ => (0 : ℝ) := by
    funext N
    simp [μN, countN, gridSet]
  rw [h0]
  exact tendsto_const_nhds

private lemma μ_unit : μ {q : ℚ | 0 ≤ q ∧ q < 1} = 1 := by
  refine μ_eq_of_tendsto _ 1 ?_
  have h1 : (fun N => μN N {q : ℚ | 0 ≤ q ∧ q < 1}) = fun _ => (1 : ℝ) := by
    funext N
    have hMpos : (0 : ℚ) < (N.factorial : ℚ) := by positivity
    have hMne : (N.factorial : ℝ) ≠ 0 := by positivity
    have hfilt : gridSet N {q : ℚ | 0 ≤ q ∧ q < 1} = Finset.range N.factorial := by
      ext j
      rw [mem_gridSet, Finset.mem_range]
      constructor
      · exact fun h => h.1
      · intro hjlt
        refine ⟨hjlt, by positivity, ?_⟩
        rw [div_lt_one hMpos]
        exact_mod_cast hjlt
    unfold μN countN
    rw [hfilt, Finset.card_range, div_self hMne]
  rw [h1]
  exact tendsto_const_nhds

private lemma μ_singleton (q : ℚ) : μ {q} = 0 := by
  refine μ_eq_of_tendsto {q} 0 ?_
  have hle : ∀ N : ℕ, 1 ≤ N → μN N {q} ≤ 1 / (N : ℝ) := by
    intro N hN
    have hcard : countN N {q} ≤ 1 := by
      unfold countN
      refine Finset.card_le_one.mpr fun j₁ hj₁ j₂ hj₂ => ?_
      have h1 : (j₁ : ℚ) / (N.factorial : ℚ) = q := (mem_gridSet.mp hj₁).2
      have h2 : (j₂ : ℚ) / (N.factorial : ℚ) = q := (mem_gridSet.mp hj₂).2
      have hMne : (N.factorial : ℚ) ≠ 0 := by positivity
      have heq : (j₁ : ℚ) = (j₂ : ℚ) := by
        have := h1.trans h2.symm
        rwa [div_left_inj' hMne] at this
      exact_mod_cast heq
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hMle : (N : ℝ) ≤ (N.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial N
    calc μN N {q} = (countN N {q} : ℝ) / (N.factorial : ℝ) := rfl
      _ ≤ 1 / (N.factorial : ℝ) := by
          gcongr
          exact_mod_cast hcard
      _ ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hNpos hMle
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun N => (μN_mem_Icc N {q}).1)
    (Filter.eventually_atTop.mpr ⟨1, hle⟩)
    tendsto_one_div_atTop_nhds_zero_nat

private lemma μ_union (S T : Set ℚ) (h : Disjoint S T) : μ (S ∪ T) = μ S + μ T := by
  have hN : ∀ N : ℕ, μN N (S ∪ T) = μN N S + μN N T := by
    intro N
    unfold μN countN
    have hunion : gridSet N (S ∪ T) = gridSet N S ∪ gridSet N T := by
      ext j
      simp only [Finset.mem_union, mem_gridSet, Set.mem_union]
      tauto
    have hdisj : Disjoint (gridSet N S) (gridSet N T) := by
      rw [Finset.disjoint_left]
      intro j hjS hjT
      exact Set.disjoint_left.mp h (mem_gridSet.mp hjS).2 (mem_gridSet.mp hjT).2
    rw [hunion, Finset.card_union_of_disjoint hdisj, Nat.cast_add, add_div]
  have hT : Filter.Tendsto (fun N => μN N (S ∪ T)) (U : Filter ℕ) (nhds (μ S + μ T)) := by
    have hsum := (μ_tendsto_and_mem S).2.add (μ_tendsto_and_mem T).2
    exact hsum.congr fun N => (hN N).symm
  exact tendsto_nhds_unique (μ_tendsto_and_mem (S ∪ T)).2 hT

private lemma μ_mono (S T : Set ℚ) (h : S ⊆ T) : μ S ≤ μ T := by
  have hN : ∀ N : ℕ, μN N S ≤ μN N T := by
    intro N
    have hcard : countN N S ≤ countN N T :=
      Finset.card_le_card fun j hj => mem_gridSet.mpr ⟨(mem_gridSet.mp hj).1, h (mem_gridSet.mp hj).2⟩
    unfold μN
    gcongr
  exact le_of_tendsto_of_tendsto (μ_tendsto_and_mem S).2 (μ_tendsto_and_mem T).2
    (Filter.Eventually.of_forall hN)

private lemma μ_Ico (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    μ {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) < b} = b - a := by
  refine μ_eq_of_tendsto _ (b - a) ?_
  have hcount : ∀ N : ℕ,
      countN N {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) < b} =
        Nat.ceil (b * (N.factorial : ℝ)) - Nat.ceil (a * (N.factorial : ℝ)) := by
    intro N
    have hMpos : (0 : ℝ) < (N.factorial : ℝ) := by positivity
    have hfilt :
        gridSet N {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) < b} =
          Finset.Ico (Nat.ceil (a * (N.factorial : ℝ))) (Nat.ceil (b * (N.factorial : ℝ))) := by
      ext j
      rw [mem_gridSet, Finset.mem_Ico]
      simp only [Set.mem_ofPred_eq, Rat.cast_div, Rat.cast_natCast]
      rw [le_div_iff₀ hMpos, div_lt_iff₀ hMpos, ← Nat.ceil_le, ← Nat.lt_ceil]
      constructor
      · rintro ⟨_, h1, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h1, h2⟩
        have hceil_le : Nat.ceil (b * (N.factorial : ℝ)) ≤ N.factorial := by
          rw [Nat.ceil_le]
          nlinarith
        exact lt_of_lt_of_le h2 hceil_le
    unfold countN
    rw [hfilt, Nat.card_Ico]
  have hlo : ∀ N : ℕ, 1 ≤ N → (b - a) - 1 / (N : ℝ) ≤ μN N {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) < b} := by
    intro N hN
    have hMpos : (0 : ℝ) < (N.factorial : ℝ) := by positivity
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hMle : (N : ℝ) ≤ (N.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial N
    have hle_ceil : Nat.ceil (a * (N.factorial : ℝ)) ≤ Nat.ceil (b * (N.factorial : ℝ)) :=
      Nat.ceil_mono (by nlinarith)
    have ha_lt : (Nat.ceil (a * (N.factorial : ℝ)) : ℝ) < a * (N.factorial : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hb_ge : b * (N.factorial : ℝ) ≤ (Nat.ceil (b * (N.factorial : ℝ)) : ℝ) :=
      Nat.le_ceil _
    have h1 : (b - a) - 1 / (N.factorial : ℝ) ≤ μN N {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) < b} := by
      unfold μN
      rw [hcount N, Nat.cast_sub hle_ceil, le_div_iff₀ hMpos]
      have hdiv : ((b - a) - 1 / (N.factorial : ℝ)) * (N.factorial : ℝ) =
          (b - a) * (N.factorial : ℝ) - 1 := by
        field_simp
      linarith
    have h2 : 1 / (N.factorial : ℝ) ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hNpos hMle
    linarith
  have hhi : ∀ N : ℕ, 1 ≤ N → μN N {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) < b} ≤ (b - a) + 1 / (N : ℝ) := by
    intro N hN
    have hMpos : (0 : ℝ) < (N.factorial : ℝ) := by positivity
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hMle : (N : ℝ) ≤ (N.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial N
    have hle_ceil : Nat.ceil (a * (N.factorial : ℝ)) ≤ Nat.ceil (b * (N.factorial : ℝ)) :=
      Nat.ceil_mono (by nlinarith)
    have ha_ge : a * (N.factorial : ℝ) ≤ (Nat.ceil (a * (N.factorial : ℝ)) : ℝ) :=
      Nat.le_ceil _
    have hb_lt : (Nat.ceil (b * (N.factorial : ℝ)) : ℝ) < b * (N.factorial : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by nlinarith)
    have h1 : μN N {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) < b} ≤ (b - a) + 1 / (N.factorial : ℝ) := by
      unfold μN
      rw [hcount N, Nat.cast_sub hle_ceil, div_le_iff₀ hMpos]
      have hdiv : ((b - a) + 1 / (N.factorial : ℝ)) * (N.factorial : ℝ) =
          (b - a) * (N.factorial : ℝ) + 1 := by
        field_simp
      linarith
    have h2 : 1 / (N.factorial : ℝ) ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hNpos hMle
    linarith
  have ht_lo : Filter.Tendsto (fun N : ℕ => (b - a) - 1 / (N : ℝ)) Filter.atTop (nhds (b - a)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := b - a)).sub tendsto_one_div_atTop_nhds_zero_nat
  have ht_hi : Filter.Tendsto (fun N : ℕ => (b - a) + 1 / (N : ℝ)) Filter.atTop (nhds (b - a)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := b - a)).add tendsto_one_div_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ht_lo ht_hi
    (Filter.eventually_atTop.mpr ⟨1, hlo⟩)
    (Filter.eventually_atTop.mpr ⟨1, hhi⟩)

private lemma μ_Ioo (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    μ {q : ℚ | a < (q : ℝ) ∧ (q : ℝ) < b} = b - a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have hempty : {q : ℚ | a < (q : ℝ) ∧ (q : ℝ) < a} = ∅ := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => not_lt.mpr (le_of_lt h)
    rw [hempty, sub_self, μ_empty]
  · by_cases hrat : ∃ q₀ : ℚ, (q₀ : ℝ) = a
    · obtain ⟨q₀, rfl⟩ := hrat
      have hunion : {q : ℚ | (q₀ : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < b} =
          {q₀} ∪ {q : ℚ | (q₀ : ℝ) < (q : ℝ) ∧ (q : ℝ) < b} := by
        ext q
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hle, hltb⟩
          rcases eq_or_lt_of_le hle with hq | hq
          · left
            exact_mod_cast hq.symm
          · right
            exact ⟨hq, hltb⟩
        · rintro (rfl | ⟨hq, hltb⟩)
          · exact ⟨le_rfl, hlt⟩
          · exact ⟨le_of_lt hq, hltb⟩
      have hdisj : Disjoint ({q₀} : Set ℚ) {q : ℚ | (q₀ : ℝ) < (q : ℝ) ∧ (q : ℝ) < b} := by
        rw [Set.disjoint_singleton_left]
        intro hmem
        exact lt_irrefl _ hmem.1
      have hIco := μ_Ico (q₀ : ℝ) b ha (le_of_lt hlt) hb
      rw [hunion, μ_union _ _ hdisj, μ_singleton q₀, zero_add] at hIco
      exact hIco
    · have heq : {q : ℚ | a < (q : ℝ) ∧ (q : ℝ) < b} = {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) < b} := by
        ext q
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨le_of_lt h1, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨lt_of_le_of_ne h1 ?_, h2⟩
          intro he
          exact hrat ⟨q, he.symm⟩
      rw [heq]
      exact μ_Ico a b ha (le_of_lt hlt) hb

private lemma rat_eq_nat_div_factorial (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (N : ℕ) (hN : r.den ≤ N) :
    ∃ k : ℕ, k < N.factorial ∧ r = (k : ℚ) / (N.factorial : ℚ) := by
  have hnum_nonneg : 0 ≤ r.num := Rat.num_nonneg.mpr hr0
  have hdvd : r.den ∣ N.factorial := Nat.dvd_factorial r.pos hN
  obtain ⟨m, hm⟩ := hdvd
  have hm_pos : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, mul_zero] at hm
    exact (Nat.factorial_pos N).ne' hm
  let p : ℕ := r.num.toNat
  have hp_eq : (p : ℤ) = r.num := Int.toNat_of_nonneg hnum_nonneg
  have hp_lt : p < r.den := by
    have hr_eq : (p : ℚ) / (r.den : ℚ) = r := by
      have : (p : ℚ) = (r.num : ℚ) := by exact_mod_cast hp_eq
      rw [this, Rat.num_div_den]
    have hltq : (p : ℚ) < (r.den : ℚ) := by
      rw [← div_lt_one (by positivity : (0 : ℚ) < (r.den : ℚ)), hr_eq]
      exact hr1
    exact_mod_cast hltq
  refine ⟨p * m, ?_, ?_⟩
  · rw [hm]
    exact Nat.mul_lt_mul_of_pos_right hp_lt hm_pos
  · have hm_ne : (m : ℚ) ≠ 0 := by positivity
    have hpq : (p : ℚ) = (r.num : ℚ) := by exact_mod_cast hp_eq
    rw [hm]
    push_cast
    rw [mul_div_mul_right _ _ hm_ne, hpq, Rat.num_div_den]

private lemma μ_shift_right (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r < 1) (A : Set ℚ)
    (hA : A ⊆ {q : ℚ | 0 ≤ q ∧ q < 1 - r}) :
    μ ((· + r) '' A) = μ A := by
  refine μ_eq_of_eventually_eq _ _ ?_
  refine Filter.eventually_atTop.mpr ⟨r.den, fun N hN => ?_⟩
  obtain ⟨k, hk_lt, hr_eq⟩ := rat_eq_nat_div_factorial r hr0 hr1 N hN
  have hMpos : (0 : ℚ) < (N.factorial : ℚ) := by positivity
  have hcard : countN N A = countN N ((· + r) '' A) := by
    unfold countN gridSet
    refine Finset.card_bij (fun (j : ℕ) _ => j + k) ?_ ?_ ?_
    · intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hj_range, hjA⟩
      have hj_lt : (j : ℚ) / (N.factorial : ℚ) < 1 - r := (hA hjA).2
      have hjk_lt : j + k < N.factorial := by
        have h1 : ((j + k : ℕ) : ℚ) / (N.factorial : ℚ) < 1 := by
          push_cast
          rw [add_div, ← hr_eq]
          linarith
        rw [div_lt_one hMpos] at h1
        exact_mod_cast h1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjk_lt, ?_⟩
      refine ⟨(j : ℚ) / (N.factorial : ℚ), hjA, ?_⟩
      push_cast
      rw [add_div, ← hr_eq]
    · intro j₁ _ j₂ _ heq
      omega
    · intro j' hj'
      rcases Finset.mem_filter.mp hj' with ⟨hj'_range, x, hxA, hx_eq⟩
      have hx0 : 0 ≤ x := (hA hxA).1
      have hk_le : k ≤ j' := by
        have h1 : (k : ℚ) / (N.factorial : ℚ) ≤ (j' : ℚ) / (N.factorial : ℚ) := by
          rw [← hr_eq, ← hx_eq]
          linarith
        rw [div_le_div_iff_of_pos_right hMpos] at h1
        exact_mod_cast h1
      refine ⟨j' - k, ?_, by omega⟩
      have hj_lt : j' - k < N.factorial := lt_of_le_of_lt (Nat.sub_le j' k) (Finset.mem_range.mp hj'_range)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj_lt, ?_⟩
      have hval : ((j' - k : ℕ) : ℚ) / (N.factorial : ℚ) = x := by
        rw [Nat.cast_sub hk_le, sub_div, ← hr_eq, ← hx_eq]
        ring
      rwa [hval]
  unfold μN
  rw [hcard]

private lemma μ_shift_wrap (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r < 1) (A : Set ℚ)
    (hA : A ⊆ {q : ℚ | 1 - r ≤ q ∧ q < 1}) :
    μ ((· + (r - 1)) '' A) = μ A := by
  refine μ_eq_of_eventually_eq _ _ ?_
  refine Filter.eventually_atTop.mpr ⟨r.den, fun N hN => ?_⟩
  obtain ⟨k, hk_lt, hr_eq⟩ := rat_eq_nat_div_factorial r hr0 hr1 N hN
  have hMpos : (0 : ℚ) < (N.factorial : ℚ) := by positivity
  let k' : ℕ := N.factorial - k
  have hk'_eq : (k' : ℚ) / (N.factorial : ℚ) = 1 - r := by
    have hMne : (N.factorial : ℚ) ≠ 0 := by positivity
    rw [Nat.cast_sub (le_of_lt hk_lt), sub_div, div_self hMne, ← hr_eq]
  have hcard : countN N ((· + (r - 1)) '' A) = countN N A := by
    unfold countN gridSet
    refine Finset.card_bij (fun (j' : ℕ) _ => j' + k') ?_ ?_ ?_
    · intro j' hj'
      rcases Finset.mem_filter.mp hj' with ⟨_, x, hxA, hx_eq⟩
      have hx_lt1 : x < 1 := (hA hxA).2
      have hjk'_lt : j' + k' < N.factorial := by
        have h1 : ((j' + k' : ℕ) : ℚ) / (N.factorial : ℚ) < 1 := by
          push_cast
          rw [add_div, hk'_eq, ← hx_eq]
          linarith
        rw [div_lt_one hMpos] at h1
        exact_mod_cast h1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjk'_lt, ?_⟩
      have hval : ((j' + k' : ℕ) : ℚ) / (N.factorial : ℚ) = x := by
        push_cast
        rw [add_div, hk'_eq, ← hx_eq]
        ring
      rwa [hval]
    · intro j₁ _ j₂ _ heq
      omega
    · intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hj_range, hjA⟩
      have hj_ge : 1 - r ≤ (j : ℚ) / (N.factorial : ℚ) := (hA hjA).1
      have hk'_le : k' ≤ j := by
        have h1 : (k' : ℚ) / (N.factorial : ℚ) ≤ (j : ℚ) / (N.factorial : ℚ) := by
          rwa [hk'_eq]
        rw [div_le_div_iff_of_pos_right hMpos] at h1
        exact_mod_cast h1
      refine ⟨j - k', ?_, by omega⟩
      have hj'_lt : j - k' < N.factorial := lt_of_le_of_lt (Nat.sub_le j k') (Finset.mem_range.mp hj_range)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj'_lt, ?_⟩
      refine ⟨(j : ℚ) / (N.factorial : ℚ), hjA, ?_⟩
      rw [Nat.cast_sub hk'_le, sub_div, hk'_eq]
      ring
  unfold μN
  rw [hcard]

private def slice (A : Set ℚ) (n : ℤ) : Set ℚ :=
  {y : ℚ | 0 ≤ y ∧ y < 1 ∧ y + (n : ℚ) ∈ A}

private noncomputable def m (A : Set ℚ) : ENNReal :=
  ∑' n : ℤ, ENNReal.ofReal (μ (slice A n))

private lemma m_empty : m ∅ = 0 := by
  unfold m
  have h0 : ∀ n : ℤ, ENNReal.ofReal (μ (slice ∅ n)) = 0 := by
    intro n
    have hs : slice ∅ n = ∅ := by ext y; simp [slice]
    rw [hs, μ_empty, ENNReal.ofReal_zero]
  simp [h0]

private lemma m_univ : m Set.univ = ⊤ := by
  unfold m
  have h1 : ∀ n : ℤ, ENNReal.ofReal (μ (slice Set.univ n)) = 1 := by
    intro n
    have hs : slice Set.univ n = {y : ℚ | 0 ≤ y ∧ y < 1} := by ext y; simp [slice]
    rw [hs, μ_unit, ENNReal.ofReal_one]
  simp_rw [h1]
  refine eq_top_iff.mpr (le_of_forall_lt fun c hc => ?_)
  obtain ⟨k, hk⟩ := exists_nat_gt c.toReal
  let F : Finset ℤ := (Finset.range k).image Int.ofNat
  have hF_card : F.card = k := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Int.ofNat.inj h), Finset.card_range]
  have hle_tsum : (k : ENNReal) ≤ ∑' _ : ℤ, (1 : ENNReal) := by
    have hsum := ENNReal.sum_le_tsum F (f := fun _ : ℤ => (1 : ENNReal))
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hF_card] at hsum
    exact hsum
  have hc_lt : c < (k : ENNReal) := by
    rw [← ENNReal.ofReal_toReal hc.ne, ← ENNReal.ofReal_natCast k]
    exact ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hk) |>.mpr hk
  exact lt_of_lt_of_le hc_lt hle_tsum

private lemma m_singleton (q : ℚ) : m {q} = 0 := by
  unfold m
  have h0 : ∀ n : ℤ, ENNReal.ofReal (μ (slice {q} n)) = 0 := by
    intro n
    have hsub : slice {q} n ⊆ {q - (n : ℚ)} := by
      intro y hy
      have : y + (n : ℚ) = q := hy.2.2
      simp only [Set.mem_singleton_iff]
      linarith
    have hle : μ (slice {q} n) ≤ 0 := (μ_mono _ _ hsub).trans_eq (μ_singleton _)
    have heq : μ (slice {q} n) = 0 := le_antisymm hle (μ_nonneg _)
    rw [heq, ENNReal.ofReal_zero]
  simp [h0]

private lemma m_union (A B : Set ℚ) (h : Disjoint A B) : m (A ∪ B) = m A + m B := by
  unfold m
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun n => ?_
  have hs : slice (A ∪ B) n = slice A n ∪ slice B n := by
    ext y
    simp only [slice, Set.mem_ofPred_eq, Set.mem_union]
    tauto
  have hdisj : Disjoint (slice A n) (slice B n) := by
    rw [Set.disjoint_left]
    intro y hyA hyB
    exact Set.disjoint_left.mp h hyA.2.2 hyB.2.2
  rw [hs, μ_union _ _ hdisj, ENNReal.ofReal_add (μ_nonneg _) (μ_nonneg _)]

private lemma m_mono (A B : Set ℚ) (h : A ⊆ B) : m A ≤ m B := by
  unfold m
  refine ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal ?_
  refine μ_mono _ _ fun y hy => ⟨hy.1, hy.2.1, h hy.2.2⟩

private lemma sum_Icc_min_sub_max (a b : ℝ) (hab : a < b) :
    ∑ n ∈ Finset.Icc (Int.floor a) (Int.floor b),
      (min 1 (b - (n : ℝ)) - max 0 (a - (n : ℝ))) = b - a := by
  have hLU : Int.floor a ≤ Int.floor b := Int.floor_mono (le_of_lt hab)
  suffices h : ∀ k : ℕ, ∀ (L : ℤ) (a b : ℝ),
      (L : ℝ) ≤ a → a < (L : ℝ) + 1 → a ≤ b →
      ((L + (k : ℤ) : ℤ) : ℝ) ≤ b → b ≤ ((L + (k : ℤ) : ℤ) : ℝ) + 1 →
      ∑ n ∈ Finset.Icc L (L + (k : ℤ)),
        (min 1 (b - (n : ℝ)) - max 0 (a - (n : ℝ))) = b - a by
    let L := Int.floor a
    let U := Int.floor b
    let k : ℕ := (U - L).toNat
    have hk : L + (k : ℤ) = U := by
      have : (k : ℤ) = U - L := Int.toNat_of_nonneg (sub_nonneg.mpr hLU)
      omega
    change ∑ n ∈ Finset.Icc L U, (min 1 (b - (n : ℝ)) - max 0 (a - (n : ℝ))) = b - a
    rw [← hk]
    exact h k L a b (Int.floor_le a) (Int.lt_floor_add_one a) (le_of_lt hab)
      (hk.symm ▸ Int.floor_le b) (hk.symm ▸ le_of_lt (Int.lt_floor_add_one b))
  intro k
  induction k with
  | zero =>
    intro L a b hLa haL hab hLb hbL
    simp only [Nat.cast_zero, add_zero] at hbL
    simp only [Nat.cast_zero, add_zero, Finset.Icc_self, Finset.sum_singleton]
    have hmin : min 1 (b - (L : ℝ)) = b - (L : ℝ) := min_eq_right (by linarith)
    have hmax : max 0 (a - (L : ℝ)) = a - (L : ℝ) := max_eq_right (by linarith)
    rw [hmin, hmax]
    ring
  | succ k ih =>
    intro L a b hLa haL hab hLb hbL
    have hL_le : L ≤ L + (k : ℤ) + 1 := by omega
    have hsplit : Finset.Icc L (L + ((k + 1 : ℕ) : ℤ)) =
        insert (L + (k : ℤ) + 1) (Finset.Icc L (L + (k : ℤ))) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : L + (k : ℤ) + 1 ∉ Finset.Icc L (L + (k : ℤ)) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert hnotmem]
    have htop_min : min 1 (b - ((L + (k : ℤ) + 1 : ℤ) : ℝ)) = b - ((L + (k : ℤ) + 1 : ℤ) : ℝ) := by
      apply min_eq_right
      push_cast at hbL ⊢
      linarith
    have htop_max : max 0 (a - ((L + (k : ℤ) + 1 : ℤ) : ℝ)) = 0 := by
      apply max_eq_left
      push_cast
      linarith
    have hrest : ∑ n ∈ Finset.Icc L (L + (k : ℤ)),
        (min 1 (b - (n : ℝ)) - max 0 (a - (n : ℝ))) =
        ∑ n ∈ Finset.Icc L (L + (k : ℤ)),
          (min 1 (((L + (k : ℤ) + 1 : ℤ) : ℝ) - (n : ℝ)) - max 0 (a - (n : ℝ))) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn_le : n ≤ L + (k : ℤ) := (Finset.mem_Icc.mp hn).2
      have h1 : min 1 (b - (n : ℝ)) = 1 := by
        apply min_eq_left
        have hn_r : (n : ℝ) ≤ (L : ℝ) + (k : ℝ) := by exact_mod_cast hn_le
        push_cast at hLb
        linarith
      have h2 : min 1 (((L + (k : ℤ) + 1 : ℤ) : ℝ) - (n : ℝ)) = 1 := by
        apply min_eq_left
        have hn_r : (n : ℝ) ≤ (L : ℝ) + (k : ℝ) := by exact_mod_cast hn_le
        push_cast
        linarith
      rw [h1, h2]
    rw [hrest, ih L a ((L + (k : ℤ) + 1 : ℤ) : ℝ) hLa haL
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith),
      htop_min, htop_max]
    ring

private lemma m_Ioo (a b : ℝ) (hab : a < b) :
    m {q : ℚ | a < (q : ℝ) ∧ (q : ℝ) < b} = ENNReal.ofReal (b - a) := by
  let I : Set ℚ := {q : ℚ | a < (q : ℝ) ∧ (q : ℝ) < b}
  have hslice_val : ∀ n : ℤ,
      μ (slice I n) = max 0 (min 1 (b - (n : ℝ)) - max 0 (a - (n : ℝ))) := by
    intro n
    let lo : ℝ := max 0 (a - (n : ℝ))
    let hi : ℝ := min 1 (b - (n : ℝ))
    by_cases hlt : lo < hi
    · have hlo0 : 0 ≤ lo := le_max_left 0 _
      have hhi1 : hi ≤ 1 := min_le_left 1 _
      have hsub1 : {y : ℚ | lo < (y : ℝ) ∧ (y : ℝ) < hi} ⊆ slice I n := by
        intro y hy
        have hy0 : (0 : ℝ) < (y : ℝ) := lt_of_le_of_lt hlo0 hy.1
        have hy1 : (y : ℝ) < 1 := lt_of_lt_of_le hy.2 hhi1
        have hya : a - (n : ℝ) < (y : ℝ) := lt_of_le_of_lt (le_max_right _ _) hy.1
        have hyb : (y : ℝ) < b - (n : ℝ) := lt_of_lt_of_le hy.2 (min_le_right _ _)
        refine ⟨by exact_mod_cast le_of_lt hy0, by exact_mod_cast hy1, ?_, ?_⟩
        · push_cast; linarith
        · push_cast; linarith
      have hsub2 : slice I n ⊆ {y : ℚ | lo ≤ (y : ℝ) ∧ (y : ℝ) < hi} := by
        intro y hy
        refine ⟨max_le (by exact_mod_cast hy.1) ?_, lt_min (by exact_mod_cast hy.2.1) ?_⟩
        · have h1 : a < (y : ℝ) + (n : ℝ) := by exact_mod_cast hy.2.2.1
          linarith
        · have h2 : (y : ℝ) + (n : ℝ) < b := by exact_mod_cast hy.2.2.2
          linarith
      have hge : hi - lo ≤ μ (slice I n) :=
        (μ_Ioo lo hi hlo0 (le_of_lt hlt) hhi1) ▸ μ_mono _ _ hsub1
      have hle : μ (slice I n) ≤ hi - lo :=
        (μ_Ico lo hi hlo0 (le_of_lt hlt) hhi1) ▸ μ_mono _ _ hsub2
      rw [le_antisymm hle hge, max_eq_right (sub_nonneg.mpr (le_of_lt hlt))]
    · have hle : hi ≤ lo := not_lt.mp hlt
      have hempty : slice I n = ∅ := by
        ext y
        simp only [slice, I, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hy0, hy1, hya, hyb⟩
        have hy0' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0
        have hy1' : (y : ℝ) < 1 := by exact_mod_cast hy1
        have hya' : a < (y : ℝ) + (n : ℝ) := by exact_mod_cast hya
        have hyb' : (y : ℝ) + (n : ℝ) < b := by exact_mod_cast hyb
        have h1 : lo ≤ (y : ℝ) := max_le hy0' (by linarith)
        have h2 : (y : ℝ) < hi := lt_min hy1' (by linarith)
        linarith
      rw [hempty, μ_empty, max_eq_left (sub_nonpos.mpr hle)]
  change ∑' n : ℤ, ENNReal.ofReal (μ (slice I n)) = ENNReal.ofReal (b - a)
  simp_rw [hslice_val]
  let S : Finset ℤ := Finset.Icc (Int.floor a) (Int.floor b)
  have hzero_out : ∀ n : ℤ, n ∉ S →
      ENNReal.ofReal (max 0 (min 1 (b - (n : ℝ)) - max 0 (a - (n : ℝ)))) = 0 := by
    intro n hn
    rw [ENNReal.ofReal_eq_zero]
    apply max_le le_rfl
    simp only [S, Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hnL | hnU
    · have ha_ge : (n : ℝ) + 1 ≤ a := by
        have : n + 1 ≤ Int.floor a := by omega
        have h1 : ((n + 1 : ℤ) : ℝ) ≤ (Int.floor a : ℝ) := by exact_mod_cast this
        push_cast at h1
        linarith [Int.floor_le a]
      have h1 : 1 ≤ max 0 (a - (n : ℝ)) := le_trans (by linarith) (le_max_right _ _)
      have h2 : min 1 (b - (n : ℝ)) ≤ 1 := min_le_left _ _
      linarith
    · have hb_le : b ≤ (n : ℝ) := by
        have : Int.floor b + 1 ≤ n := by omega
        have h1 : ((Int.floor b + 1 : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
        push_cast at h1
        linarith [Int.lt_floor_add_one b]
      have h1 : min 1 (b - (n : ℝ)) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
      have h2 : 0 ≤ max 0 (a - (n : ℝ)) := le_max_left _ _
      linarith
  rw [tsum_eq_sum hzero_out]
  have hnonneg_in : ∀ n ∈ S, 0 ≤ min 1 (b - (n : ℝ)) - max 0 (a - (n : ℝ)) := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hLn, hnU⟩
    have ha_lt : a < (n : ℝ) + 1 := by
      have : (Int.floor a : ℝ) ≤ (n : ℝ) := by exact_mod_cast hLn
      linarith [Int.lt_floor_add_one a]
    have hb_gt : (n : ℝ) < b ∨ (n : ℝ) = b := by
      have : (n : ℝ) ≤ (Int.floor b : ℝ) := by exact_mod_cast hnU
      have hle : (n : ℝ) ≤ b := le_trans this (Int.floor_le b)
      exact lt_or_eq_of_le hle
    have hlo_le : max 0 (a - (n : ℝ)) ≤ min 1 (b - (n : ℝ)) := by
      refine max_le (le_min zero_le_one ?_) (le_min (by linarith) (by linarith))
      rcases hb_gt with h | h <;> linarith
    linarith
  have hmax_in : ∀ n ∈ S,
      ENNReal.ofReal (max 0 (min 1 (b - (n : ℝ)) - max 0 (a - (n : ℝ)))) =
        ENNReal.ofReal (min 1 (b - (n : ℝ)) - max 0 (a - (n : ℝ))) := by
    intro n hn
    rw [max_eq_right (hnonneg_in n hn)]
  rw [Finset.sum_congr rfl hmax_in, ← ENNReal.ofReal_sum_of_nonneg hnonneg_in,
    sum_Icc_min_sub_max a b hab]

private lemma m_translate_int (A : Set ℚ) (k : ℤ) : m ((· + (k : ℚ)) '' A) = m A := by
  unfold m
  have hslice : ∀ n : ℤ, slice ((· + (k : ℚ)) '' A) n = slice A (n - k) := by
    intro n
    ext y
    simp only [slice, Set.mem_ofPred_eq, Set.mem_image, Int.cast_sub]
    constructor
    · rintro ⟨hy0, hy1, x, hxA, hxeq⟩
      refine ⟨hy0, hy1, ?_⟩
      have : y + ((n : ℚ) - (k : ℚ)) = x := by linarith
      rwa [this]
    · rintro ⟨hy0, hy1, hmem⟩
      exact ⟨hy0, hy1, y + ((n : ℚ) - (k : ℚ)), hmem, by ring⟩
  simp_rw [hslice]
  exact Equiv.tsum_eq (Equiv.subRight k) (fun n => ENNReal.ofReal (μ (slice A n)))

private lemma m_translate_frac (A : Set ℚ) (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    m ((· + r) '' A) = m A := by
  let P : ℤ → Set ℚ := fun n => slice A n ∩ {y : ℚ | 0 ≤ y ∧ y < 1 - r}
  let Q : ℤ → Set ℚ := fun n => slice A n ∩ {y : ℚ | 1 - r ≤ y ∧ y < 1}
  have hA_split : ∀ n : ℤ,
      ENNReal.ofReal (μ (slice A n)) =
        ENNReal.ofReal (μ (P n)) + ENNReal.ofReal (μ (Q n)) := by
    intro n
    have hunion : slice A n = P n ∪ Q n := by
      ext y
      simp only [P, Q, slice, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hy0, hy1, hyA⟩
        by_cases h : y < 1 - r
        · exact Or.inl ⟨⟨hy0, hy1, hyA⟩, hy0, h⟩
        · exact Or.inr ⟨⟨hy0, hy1, hyA⟩, not_lt.mp h, hy1⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hdisj : Disjoint (P n) (Q n) := by
      rw [Set.disjoint_left]
      intro y hyP hyQ
      linarith [hyP.2.2, hyQ.2.1]
    rw [hunion, μ_union _ _ hdisj, ENNReal.ofReal_add (μ_nonneg _) (μ_nonneg _)]
  have hshift_split : ∀ n : ℤ,
      ENNReal.ofReal (μ (slice ((· + r) '' A) n)) =
        ENNReal.ofReal (μ (Q (n - 1))) + ENNReal.ofReal (μ (P n)) := by
    intro n
    have hunion : slice ((· + r) '' A) n =
        ((· + (r - 1)) '' Q (n - 1)) ∪ ((· + r) '' P n) := by
      ext y
      simp only [P, Q, slice, Set.mem_union, Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Int.cast_sub, Int.cast_one]
      constructor
      · rintro ⟨hy0, hy1, x, hxA, hxeq⟩
        by_cases hyr : y < r
        · left
          refine ⟨y + 1 - r, ⟨⟨by linarith, by linarith, ?_⟩, by linarith, by linarith⟩, by ring⟩
          have : y + 1 - r + ((n : ℚ) - 1) = x := by linarith
          rwa [this]
        · right
          refine ⟨y - r, ⟨⟨by linarith, by linarith, ?_⟩, by linarith, by linarith⟩, by ring⟩
          have : y - r + (n : ℚ) = x := by linarith
          rwa [this]
      · rintro (⟨z, ⟨⟨_, _, hzA⟩, hz1, hz2⟩, rfl⟩ | ⟨z, ⟨⟨_, _, hzA⟩, hz1, hz2⟩, rfl⟩)
        · refine ⟨by linarith, by linarith, z + ((n : ℚ) - 1), hzA, by ring⟩
        · refine ⟨by linarith, by linarith, z + (n : ℚ), hzA, by ring⟩
    have hdisj : Disjoint ((· + (r - 1)) '' Q (n - 1)) ((· + r) '' P n) := by
      rw [Set.disjoint_left]
      rintro y ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, heq⟩
      linarith [hz₁.2.2, hz₂.2.1]
    have hQ : μ ((· + (r - 1)) '' Q (n - 1)) = μ (Q (n - 1)) :=
      μ_shift_wrap r hr0 hr1 (Q (n - 1)) Set.inter_subset_right
    have hP : μ ((· + r) '' P n) = μ (P n) :=
      μ_shift_right r hr0 hr1 (P n) Set.inter_subset_right
    rw [hunion, μ_union _ _ hdisj, hQ, hP, ENNReal.ofReal_add (μ_nonneg _) (μ_nonneg _)]
  calc m ((· + r) '' A)
      = ∑' n : ℤ, (ENNReal.ofReal (μ (Q (n - 1))) + ENNReal.ofReal (μ (P n))) := by
          unfold m
          exact tsum_congr hshift_split
    _ = (∑' n : ℤ, ENNReal.ofReal (μ (Q (n - 1)))) + (∑' n : ℤ, ENNReal.ofReal (μ (P n))) :=
          ENNReal.tsum_add
    _ = (∑' n : ℤ, ENNReal.ofReal (μ (Q n))) + (∑' n : ℤ, ENNReal.ofReal (μ (P n))) := by
          congr 1
          exact Equiv.tsum_eq (Equiv.subRight (1 : ℤ)) (fun n => ENNReal.ofReal (μ (Q n)))
    _ = (∑' n : ℤ, ENNReal.ofReal (μ (P n))) + (∑' n : ℤ, ENNReal.ofReal (μ (Q n))) :=
          add_comm _ _
    _ = ∑' n : ℤ, (ENNReal.ofReal (μ (P n)) + ENNReal.ofReal (μ (Q n))) :=
          ENNReal.tsum_add.symm
    _ = m A := by
          unfold m
          exact tsum_congr fun n => (hA_split n).symm

private lemma m_translate (A : Set ℚ) (t : ℚ) : m ((· + t) '' A) = m A := by
  let k : ℤ := Int.floor t
  let r : ℚ := t - (k : ℚ)
  have hr0 : 0 ≤ r := sub_nonneg.mpr (Int.floor_le t)
  have hr1 : r < 1 := by
    have : t < (k : ℚ) + 1 := Int.lt_floor_add_one t
    linarith
  have hcomp : (· + t) '' A = (· + r) '' ((· + (k : ℚ)) '' A) := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a + (k : ℚ), ⟨a, ha, rfl⟩, by dsimp [r]; ring⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by dsimp [r]; ring⟩
  rw [hcomp, m_translate_frac _ r hr0 hr1, m_translate_int A k]

end Mse2937341

theorem OMA.solution : type_of% @OMA.S_mse_2937341.main :=
  ⟨Mse2937341.m,
    Mse2937341.m_empty,
    Mse2937341.m_univ,
    Mse2937341.m_singleton,
    Mse2937341.m_Ioo,
    Mse2937341.m_union,
    Mse2937341.m_mono,
    Mse2937341.m_translate⟩
