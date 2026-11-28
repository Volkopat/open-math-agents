import OMAStatements.S_arxiv_1909_07141

-- Credit: @ryansolves
namespace OMA.R_arxiv_1909_07141_R1
open Filter Topology MeasureTheory Set OMA.S_arxiv_1909_07141

/-- Every balanced colored word admits contiguous blocks meeting all own-color integer quotas. -/
def H1 : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ (N L : ℕ) (w : Fin L → Fin n), 0 < N →
  let cnt (i : Fin n) (j : Fin (L+1)) := (Finset.univ.filter fun h : Fin L => h.val < j.val ∧ w h = i).card
  (∀ i, cnt i (Fin.last L) = N) →
  ∀ (a : Fin n → ℕ), ∑ i, a i ≤ N →
    ∃ (q : Fin (2*n-2+2) → Fin (L+1)) (o : Fin (2*n-2+1) → Fin n),
      Monotone q ∧ q 0 = 0 ∧ q (Fin.last _) = Fin.last L ∧
      ∀ i, a i ≤ ∑ j, if o j = i then
        cnt i (q j.succ) - cnt i (q j.castSucc) else 0

/-- A sorted quantile word approximates every cumulative value to one bead. -/
def H2 : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ (μ : Fin n → Measure ℝ),
  (∀ i, IsProbabilityMeasure (μ i)) → (∀ i, NullSingletonClass (μ i)) → (∀ i, μ i (Icc 0 1) = 1) →
  ∀ N : ℕ, 0 < N → ∃ (L : ℕ) (w : Fin L → Fin n) (p : Fin (L+1) → Icc (0:ℝ) 1),
    let cnt (i : Fin n) (j : Fin (L+1)) := (Finset.univ.filter fun h : Fin L => h.val < j.val ∧ w h = i).card
    (∀ i, cnt i (Fin.last L) = N) ∧ Monotone p ∧ (p 0 : ℝ) = 0 ∧
    (p (Fin.last L) : ℝ) = 1 ∧ ∀ i j,
      (cnt i j : ℝ) ≤ N * (μ i).real (Iic (p j)) ∧
      N * (μ i).real (Iic (p j)) ≤ cnt i j + 1

theorem count_mono {n L : ℕ} (w : Fin L → Fin n) (i : Fin n) : Monotone (fun j : Fin (L+1) => (Finset.univ.filter fun h : Fin L => h.val < j.val ∧ w h = i).card) := by
  intro a b hab
  apply Finset.card_le_card
  intro x hx
  obtain ⟨_, hx, hi⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hx hab, hi⟩

/-- Vanishing errors in every entitlement can be removed without increasing
the cut budget. Owners and cut positions are both allowed to vary. -/
theorem remove_error {n k : ℕ} (F : Fin n → ℝ → ℝ) (cont : ∀ i, Continuous (F i))
    (demands : Fin n → ℝ) (err : ℕ → ℝ) (limit : Tendsto err atTop (𝓝 0))
    (approx : ∀ m, ∃ (c : Fin (k+2) → Set.Icc (0:ℝ) 1) (owners : Fin (k+1) → Fin n),
      Monotone c ∧ (c 0 : ℝ) = 0 ∧ (c (Fin.last (k+1)) : ℝ) = 1 ∧
      ∀ i, demands i ≤ (∑ j, if owners j = i then F i (c j.succ) - F i (c j.castSucc) else 0) + err m) :
    ∃ (c : Fin (k+2) → Set.Icc (0:ℝ) 1) (owners : Fin (k+1) → Fin n),
      Monotone c ∧ (c 0 : ℝ) = 0 ∧ (c (Fin.last (k+1)) : ℝ) = 1 ∧
      ∀ i, demands i ≤ (∑ j, if owners j = i then F i (c j.succ) - F i (c j.castSucc) else 0) := by
  classical
  choose c o mono lo hi pay using approx
  obtain ⟨⟨C,O⟩,φ,up,conv⟩ := CompactSpace.tendsto_subseq (fun m => (c m,o m))
  have cuts : Tendsto (fun m => c (φ m)) atTop (𝓝 C) := continuous_fst.continuousAt.tendsto.comp conv
  have coord (j) : Tendsto (fun m => (c (φ m) j : ℝ)) atTop (𝓝 (C j : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_pi_nhds.mp cuts j)
  have owners : Tendsto (fun m => o (φ m)) atTop (𝓝 O) := continuous_snd.continuousAt.tendsto.comp conv
  have stable : ∀ᶠ m in atTop, o (φ m) = O := owners (isOpen_discrete {O} |>.mem_nhds (by rfl))
  refine ⟨C,O,?_,?_,?_,?_⟩
  · intro a b ab
    change (C a : ℝ) ≤ (C b : ℝ)
    exact le_of_tendsto_of_tendsto' (coord a) (coord b) (fun m => mono (φ m) ab)
  · exact tendsto_nhds_unique (coord 0) (by simpa only [lo] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)))
  · exact tendsto_nhds_unique (coord _) (by simpa only [hi] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)))
  · intro i
    have fixed : Tendsto (fun m => (∑ j, if O j = i then F i (c (φ m) j.succ) - F i (c (φ m) j.castSucc) else 0)) atTop (𝓝 ((∑ j, if O j = i then F i (C j.succ) - F i (C j.castSucc) else 0))) := by
      apply tendsto_finsetSum
      intro j _
      by_cases same : O j = i
      · simp only [if_pos same]
        exact ((cont i).continuousAt.tendsto.comp (coord j.succ)).sub
          ((cont i).continuousAt.tendsto.comp (coord j.castSucc))
      · simp [same]
    have values := fixed.add (limit.comp up.tendsto_atTop)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa [Function.comp_def] using values)
    filter_upwards [stable] with m hm
    simpa only [← hm] using pay (φ m) i

private theorem interval_value (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (h : a ≤ b) :
    μ.real (Iic b) - μ.real (Iic a) = μ.real (Ioc a b) := by
  have disjoint : Disjoint (Iic a) (Ioc a b) := Set.disjoint_left.mpr (fun _ hx hy => hy.1.not_ge hx)
  have eqn := measureReal_union (μ := μ) disjoint measurableSet_Ioc
  rw [Iic_union_Ioc_eq_Iic h] at eqn
  linarith

/-- A certificate in cumulative values certifies a division in the catalog's
original measure-of-unions formulation, including coincident cuts. -/
theorem of_cumulative_values {n k : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (demands : Fin n → ℝ) (c : Fin (k+2) → Icc (0:ℝ) 1) (o : Fin (k+1) → Fin n)
    (mono : Monotone c) (lo : (c 0 : ℝ) = 0) (hi : (c (Fin.last (k+1)) : ℝ) = 1)
    (valid : ∀ i, demands i ≤ (∑ j, if o j = i then (μ i).real (Iic (c j.succ)) - (μ i).real (Iic (c j.castSucc)) else 0)) :
    DivisionWithCuts μ demands k := by
  classical
  let x := fun j => (c j : ℝ)
  have order : Monotone x := fun _ _ h => mono h
  refine ⟨x,o,order,lo,hi,?_⟩
  intro i
  let slots := Finset.univ.filter (fun j => o j = i)
  let piece := fun j : Fin (k+1) => Ioc (x j.castSucc) (x j.succ)
  have before (a b : Fin (k+1)) (ab : a < b) : x a.succ ≤ x b.castSucc :=
    order (by change a.val+1 ≤ b.val; exact ab)
  have apart : (↑slots : Set (Fin (k+1))).PairwiseDisjoint piece := by
    intro a _ b _ ne
    rcases lt_or_gt_of_ne ne with ab|ba
    · exact Set.disjoint_left.mpr (fun _ ha hb => (hb.1.trans_le' (before a b ab)).not_ge ha.2)
    · exact (Set.disjoint_left.mpr (fun _ hb ha => (ha.1.trans_le' (before b a ba)).not_ge hb.2)).symm
  have sumval : (∑ j, if o j = i then (μ i).real (Iic (c j.succ)) - (μ i).real (Iic (c j.castSucc)) else 0) =
      (μ i).real (⋃ j ∈ slots, piece j) := by
    rw [measureReal_biUnion_finset apart (fun _ _ => measurableSet_Ioc)]
    unfold slots
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : o j = i
    · simp only [if_pos hj]
      exact interval_value _ (order (Fin.castSucc_le_succ j))
    · simp [hj]
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
  apply ((valid i).trans sumval.le).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro y hy
  obtain ⟨j,hj,hmem⟩ := mem_iUnion₂.mp hy
  exact mem_iUnion₂.mpr ⟨j,(Finset.mem_filter.mp hj).2,hmem.1.le,hmem.2⟩

theorem continuous_cumulative (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    Continuous (fun x => μ.real (Iic x)) := by
  simp_rw [← ProbabilityTheory.cdf_eq_real]
  apply continuous_iff_continuousAt.mpr
  intro x
  let F := ProbabilityTheory.cdf μ
  apply F.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [F.rightLim_eq]
  have atom := F.measure_singleton x
  rw [show F.measure = μ from ProbabilityTheory.measure_cdf μ,measure_singleton] at atom
  have below := ENNReal.ofReal_eq_zero.mp atom.symm
  exact le_antisymm (F.mono.leftLim_le le_rfl) (sub_nonpos.mp below)

theorem division_of_vanishing_error {n k : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (demands : Fin n → ℝ) (err : ℕ → ℝ) (limit : Filter.Tendsto err Filter.atTop (nhds 0))
    (approx : ∀ m, ∃ (c : Fin (k+2) → Icc (0:ℝ) 1) (o : Fin (k+1) → Fin n),
      Monotone c ∧ (c 0 : ℝ) = 0 ∧ (c (Fin.last (k+1)) : ℝ) = 1 ∧
      ∀ i, demands i ≤ (∑ j, if o j = i then (μ i).real (Iic (c j.succ)) - (μ i).real (Iic (c j.castSucc)) else 0) + err m) :
    DivisionWithCuts μ demands k := by
  obtain ⟨c,o,hc,lo,hi,values⟩ := remove_error _ (fun i => continuous_cumulative (μ i)) demands err limit approx
  exact of_cumulative_values μ demands c o hc lo hi values

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_1909_07141.main := by
  intro h1 h2
  intro n hn μ prob atoms support α nonneg total
  let k := 2*n-2
  let F (i : Fin n) (x : ℝ) := (μ i).real (Iic x)
  apply @division_of_vanishing_error n k μ prob atoms α (fun m => ((k:ℝ)+2) * (1 / ((m:ℝ)+1)))
  · simpa using (tendsto_const_nhds (x := ((k:ℝ)+2))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  intro m
  let N := m+1
  have posN : 0 < N := Nat.succ_pos _
  have posR : (0:ℝ) < N := by exact_mod_cast posN
  let a (i : Fin n) := ⌊(N:ℝ) * α i⌋₊
  have budget : ∑ i, a i ≤ N := by
    have bound : ∑ i, (a i : ℝ) ≤ ∑ i, (N:ℝ) * α i :=
      Finset.sum_le_sum fun i _ => Nat.floor_le (mul_nonneg posR.le (nonneg i))
    rw [← Finset.mul_sum, total, mul_one] at bound
    exact_mod_cast bound
  obtain ⟨L,w,p,balanced,monop,p0,p1,sample⟩ := h2 n hn μ prob atoms support N posN
  obtain ⟨q,o,monoq,q0,q1,pay⟩ := h1 n hn N L w posN balanced a budget
  let c := p ∘ q
  refine ⟨c,o,monop.comp monoq,by simpa [c,q0] using p0,by simpa [k,c,q1] using p1,?_⟩
  intro i
  let cnt (i : Fin n) (j : Fin (L+1)) := (Finset.univ.filter fun h : Fin L => h.val < j.val ∧ w h = i).card
  let beads (j : Fin (k+1)) := if o j = i then
    cnt i (q j.succ) - cnt i (q j.castSucc) else 0
  let val (j : Fin (k+1)) : ℝ := if o j = i then F i (c j.succ) - F i (c j.castSucc) else 0
  have block (j : Fin (k+1)) : (beads j : ℝ) ≤ (N:ℝ) * val j + 1 := by
    by_cases hi : o j = i
    · have ord := count_mono w i (monoq (Fin.castSucc_le_succ j))
      change cnt i (q j.castSucc) ≤ cnt i (q j.succ) at ord
      simp only [beads, val, if_pos hi, Nat.cast_sub ord, F, c, Function.comp_apply, mul_sub]
      have lower : (cnt i (q j.succ) : ℝ) ≤ _ := (sample i (q j.succ)).1
      have upper : _ ≤ (cnt i (q j.castSucc) : ℝ) + 1 := (sample i (q j.castSucc)).2
      linarith only [lower, upper]
    · simp [beads,val,hi]
  have allblocks := Finset.sum_le_sum (s := Finset.univ) (fun j _ => block j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at allblocks
  have target : (a i : ℝ) ≤ ∑ j, (beads j : ℝ) := by exact_mod_cast (pay i)
  have size : ∑ _j : Fin (k+1), (1:ℝ) = (k:ℝ)+1 := by simp
  rw [size] at allblocks
  have approx : (N:ℝ) * α i ≤ (N:ℝ) * (∑ j, val j) + ((k:ℝ)+2) := by
    have floorbound := Nat.lt_floor_add_one ((N:ℝ) * α i)
    change (N:ℝ) * α i < (a i : ℝ) + 1 at floorbound
    linarith
  change α i ≤ (∑ j, val j) + ((k:ℝ)+2) * (1 / ((m:ℝ)+1))
  have NM : ((m:ℝ)+1) = (N:ℝ) := by simp [N]
  rw [NM,mul_one_div]
  apply (mul_le_mul_iff_left₀ posR).mp
  rw [add_mul, div_mul_cancel₀ _ posR.ne']
  simpa only [mul_comm (N:ℝ)] using approx

end OMA.R_arxiv_1909_07141_R1
