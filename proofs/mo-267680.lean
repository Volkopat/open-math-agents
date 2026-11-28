import OMAStatements.S_mo_267680

/-!
Complete proof by @connoranderson, linked by statement PR #25013 and desk DONE #115003.
Pinned source: https://github.com/connoranderson/open-math-agents/blob/e2ed71df9a5413f53257d1fb7baab4572abccaef/proofs/mo-267680.lean
Source: Sung-En Chiu, https://mathoverflow.net/questions/267680 (CC BY-SA 3.0).
The registered topology is pointwise convergence. All mathematical source is unchanged;
this port adds provenance and current-checker validation, not a new discovery.
Port and validation: @rodolfoquint.
-/

namespace OMA.S_mo_267680
open Set

lemma family_compact (n : ℕ) (C : ℝ) : IsCompact (family n C) := by
  have hcl : IsClosed (family n C) := by
    change IsClosed ({f : Δ n → ℝ | ∀ x, |f x| ≤ C} ∩ {f | ∀ x y, Maj x y → f x ≤ f y})
    simp only [Set.ofPred_forall]
    exact (isClosed_iInter fun x => isClosed_le (continuous_apply x).abs continuous_const).inter
      (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
        isClosed_le (continuous_apply x) (continuous_apply y))
  apply (isCompact_Icc (a:=fun _ : Δ n => -C) (b:=fun _ => C)).of_isClosed_subset hcl
  intro f hf
  exact ⟨fun x => (abs_le.mp (hf.1 x)).1,fun x => (abs_le.mp (hf.1 x)).2⟩

end OMA.S_mo_267680

namespace OMA.S_mo_267680
open Filter Set Topology
private lemma select_countable {ι : Type*} [Countable ι] (u : ℕ → ι → ℝ) (C : ℝ)
    (hb : ∀ n i, |u n i| ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ a : ℝ, Tendsto (fun n => u (φ n) i) atTop (𝓝 a) := by
  let v (n : ℕ) (i : ι) : Icc (-C) C := ⟨u n i, abs_le.mp (hb n i)⟩
  obtain ⟨z, φ, hφ, hz⟩ := CompactSpace.tendsto_subseq v
  refine ⟨φ, hφ, fun i => ⟨z i, ?_⟩⟩
  exact continuous_subtype_val.continuousAt.tendsto.comp (tendsto_pi_nhds.mp hz i)

lemma helly (f : ℕ → ℝ → ℝ) (C : ℝ) (hm : ∀ n, Monotone (f n))
    (hb : ∀ n x, |f n x| ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ x, ∃ y : ℝ, Tendsto (fun n => f (φ n) x) atTop (𝓝 y) := by
  classical
  obtain ⟨φ, hφ, hrat⟩ := select_countable (fun n (q : ℚ) => f n q) C (fun n q => hb n q)
  let u (x : ℝ) (n : ℕ) := f (φ n) x
  let lo (x : ℝ) := liminf (u x) atTop
  let hi (x : ℝ) := limsup (u x) atTop
  have hl (x : ℝ) : IsBoundedUnder (· ≥ ·) atTop (u x) :=
    isBoundedUnder_of ⟨-C, fun n => (abs_le.mp (hb (φ n) x)).1⟩
  have hh (x : ℝ) : IsBoundedUnder (· ≤ ·) atTop (u x) :=
    isBoundedUnder_of ⟨C, fun n => (abs_le.mp (hb (φ n) x)).2⟩
  have sep {x y : ℝ} (h : x < y) : hi x ≤ lo y := by
    obtain ⟨q, hx, hy⟩ := exists_rat_btwn h
    obtain ⟨v, hv⟩ := hrat q
    change Tendsto (u q) atTop (𝓝 v) at hv
    calc
      hi x ≤ limsup (u q) atTop := limsup_le_limsup
        (Eventually.of_forall (fun n => hm (φ n) hx.le)) (hl x).isCoboundedUnder_le (hh q)
      _ = v := hv.limsup_eq
      _ = liminf (u q) atTop := hv.liminf_eq.symm
      _ ≤ lo y := liminf_le_liminf
        (Eventually.of_forall (fun n => hm (φ n) hy.le)) (hl q) (hh y).isCoboundedUnder_ge
  let bad : Set ℝ := {x | lo x < hi x}
  have hdis : bad.PairwiseDisjoint (fun x => Ioo (lo x) (hi x)) := by
    intro x _ y _ hxy
    apply Set.disjoint_iff.mpr
    intro v hv
    rcases lt_or_gt_of_ne hxy with h | h
    · exact (not_lt_of_ge (sep h) (hv.2.1.trans hv.1.2)).elim
    · exact (not_lt_of_ge (sep h) (hv.1.1.trans hv.2.2)).elim
  have hc : bad.Countable := hdis.countable_of_isOpen
    (fun _ _ => isOpen_Ioo) (fun _ hx => Set.nonempty_Ioo.mpr hx)
  let : Countable bad := countable_coe_iff.mpr hc
  obtain ⟨ψ, hψ, he⟩ := select_countable (fun n (x : bad) => u x n) C
    (fun n x => hb (φ n) x)
  refine ⟨φ ∘ ψ, hφ.comp hψ, fun x => ?_⟩
  by_cases hx : x ∈ bad
  · exact he ⟨x,hx⟩
  · have hx' : hi x ≤ lo x := le_of_not_gt hx
    exact ⟨lo x, (tendsto_of_le_liminf_of_limsup_le le_rfl hx' (hh x) (hl x)).comp hψ.tendsto_atTop⟩
end OMA.S_mo_267680

namespace OMA.S_mo_267680

open Matrix Filter
open scoped Topology

private lemma pair_sum (x : Δ 2) : x.val 0+x.val 1 = 1 := by
  simpa [Fin.sum_univ_two] using x.property.2

private lemma pair_mix (x y : Δ 2) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (he : t*y.val 0 + (1-t)*y.val 1 = x.val 0) : Maj x y := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![t, 1-t; 1-t,t]
  refine ⟨M,mem_doublyStochastic_iff_sum.mpr ⟨?_,?_,?_⟩,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [M,ht,ht']
  · intro i
    fin_cases i <;> simp [M,Fin.sum_univ_two]
  · intro j
    fin_cases j <;> simp [M,Fin.sum_univ_two]
  · funext i
    fin_cases i
    · simpa [M,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using he
    · change (M *ᵥ y.val) 1 = x.val 1
      simp [M,Matrix.mulVec,dotProduct, Fin.sum_univ_two]
      linarith [pair_sum x, pair_sum y]

private noncomputable def clamp (s : ℝ) := max (1/2 : ℝ) (min 1 s)

private lemma clamp_lo (s : ℝ) : 1/2 ≤ clamp s := le_max_left _ _
private lemma clamp_hi (s : ℝ) : clamp s ≤ 1 := max_le (by norm_num) (min_le_left _ _)

private noncomputable def canonical (s : ℝ) : Δ 2 :=
  ⟨![clamp s,1-clamp s],by
    constructor
    · intro i
      fin_cases i
      · exact (by norm_num : (0:ℝ) ≤ 1/2).trans (clamp_lo s)
      · exact sub_nonneg.mpr (clamp_hi s)
    · simp [Fin.sum_univ_two]⟩

private lemma canonical_order {s t : ℝ} (hst : s ≤ t) : Maj (canonical s) (canonical t) := by
  have hst' : clamp s ≤ clamp t := max_le_max_left _ (min_le_min_left _ hst)
  have h0 := clamp_lo s
  have h1 := clamp_lo t
  by_cases h : 2*clamp t - 1 = 0
  · apply pair_mix _ _ 1 (by norm_num) (by norm_num)
    change 1*clamp t + (1-1)*(1-clamp t) = clamp s
    linarith
  have hpos : 0 < 2*clamp t-1 := lt_of_le_of_ne (by linarith) (Ne.symm h)
  let a := (clamp s+clamp t-1)/(2*clamp t-1)
  refine pair_mix _ _ a (div_nonneg (by linarith) hpos.le) ((div_le_one hpos).mpr (by linarith)) ?_
  change a * clamp t + (1-a)*(1-clamp t) = clamp s
  have ha : a * (2*clamp t-1) = clamp s+clamp t-1 := div_mul_cancel₀ _ h
  linear_combination ha

private lemma canonical_value (f : Δ 2 → ℝ) {C : ℝ} (hf : f ∈ family 2 C) (x : Δ 2) :
    f (canonical (max (x.val 0) (x.val 1))) = f x := by
  have hs := pair_sum x
  have h0 := x.property.1 0
  have h1 := x.property.1 1
  let r := max (x.val 0) (x.val 1)
  have hr : clamp r = r := by
    have hu : r ≤ 1 := max_le (by linarith) (by linarith)
    have hl : 1/2 ≤ r := by
      dsimp [r]
      rcases le_total (x.val 0) (x.val 1) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    rw [clamp,min_eq_right hu,max_eq_right hl]
  have he : (canonical r).val 0 = r := hr
  have he1 : (canonical r).val 1 = 1-r := by change 1-clamp r=1-r; rw [hr]
  by_cases h : x.val 1 ≤ x.val 0
  · have hxr : r = x.val 0 := max_eq_left h
    apply congrArg f
    apply Subtype.ext
    funext i
    fin_cases i
    · exact he.trans hxr
    · change (canonical r).val 1 = x.val 1
      rw [he1,hxr]; linarith
  · have hxr : r = x.val 1 := max_eq_right (le_of_not_ge h)
    apply le_antisymm
    · exact hf.2 _ _ (pair_mix _ _ 0 (by norm_num) (by norm_num) (by rw [he,hxr]; ring))
    · exact hf.2 _ _ (pair_mix _ _ 0 (by norm_num) (by norm_num) (by rw [he1,hxr]; linarith))

private lemma pair_seq_compact (C : ℝ) : IsSeqCompact (family 2 C) := by
  intro f hf
  let g (k : ℕ) (s : ℝ) := f k (canonical s)
  have hm (k : ℕ) : Monotone (g k) := fun _ _ h => (hf k).2 _ _ (canonical_order h)
  obtain ⟨φ,hφ,h⟩ := helly g C hm fun k s => (hf k).1 _
  choose a ha using h
  let F (x : Δ 2) := a (max (x.val 0) (x.val 1))
  have hc (x : Δ 2) : Tendsto (fun k => f (φ k) x) atTop (𝓝 (F x)) := by
    simpa only [g,canonical_value _ (hf _) x,F] using ha (max (x.val 0) (x.val 1))
  refine ⟨F,?_,φ,hφ,tendsto_pi_nhds.mpr hc⟩
  exact (family_compact 2 C).isClosed.mem_of_tendsto (tendsto_pi_nhds.mpr hc)
    (Eventually.of_forall fun k => hf (φ k))

lemma small (n : ℕ) (C : ℝ) (hn : n ≤ 2) : IsSeqCompact (family n C) := by
  interval_cases n
  · exact (family_compact 0 C).isSeqCompact
  · exact (family_compact 1 C).isSeqCompact
  · exact pair_seq_compact C

end OMA.S_mo_267680

namespace OMA.S_mo_267680
open Filter Matrix Finset Set
open scoped Topology Classical

private lemma maj_refl {n : ℕ} (x : Δ n) : Maj x x :=
  ⟨1,(doublyStochastic ℝ _).one_mem,Matrix.one_mulVec _⟩

private lemma maj_trans {n : ℕ} {x y z : Δ n} (hxy : Maj x y) (hyz : Maj y z) : Maj x z := by
  obtain ⟨A,hA,hxy⟩ := hxy
  obtain ⟨B,hB,hyz⟩ := hyz
  exact ⟨A*B,(doublyStochastic ℝ _).mul_mem hA hB,by rw [← Matrix.mulVec_mulVec,hyz,hxy]⟩

private lemma maj_bounds {n : ℕ} {x y : Δ n} (h : Maj x y) (a b : ℝ)
    (hy : ∀ j, a ≤ y.val j ∧ y.val j ≤ b) (i : Fin n) : a ≤ x.val i ∧ x.val i ≤ b := by
  obtain ⟨A,hA,he⟩ := h
  obtain ⟨hn,hs,_⟩ := mem_doublyStochastic_iff_sum.mp hA
  rw [←he]
  change a ≤ ∑ j, A i j*y.val j ∧ ∑ j, A i j*y.val j ≤ b
  constructor
  · calc
      a = ∑ j, A i j*a := by rw [←sum_mul,hs,one_mul]
      _ ≤ _ := sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy j).1 (hn i j))
  · calc
      _ ≤ ∑ j, A i j*b := sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy j).2 (hn i j))
      _ = b := by rw [← sum_mul,hs,one_mul]

private noncomputable def raw (m : ℕ) (t : ℝ) : Fin (m+3) → ℝ :=
  Fin.cons (5+t/4) (Fin.cons (4-t/2) (Fin.cons (3+t/4) (fun _ => 4)))

private lemma raw_bounds (m : ℕ) (t : Icc (0:ℝ) 1) (j : Fin (m+3)) :
    3+t.val/4 ≤ raw m t.val j ∧ raw m t.val j ≤ 5+t.val/4 := by
  have hz := t.property.1
  have ho := t.property.2
  revert j
  simp only [raw,Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ]
  repeat' first | constructor | intro
  all_goals linarith

private noncomputable def point (m : ℕ) (t : Icc (0:ℝ) 1) : Δ (m+3) :=
  ⟨fun j => raw m t.val j / (4*((m:ℝ)+3)),by
    constructor
    · intro i
      apply div_nonneg _ (by positivity)
      linarith [(raw_bounds m t i).1,t.property.1]
    · rw [← sum_div]
      simp [raw,Fin.sum_univ_succ]
      field_simp
      ring⟩

private lemma point_antichain (m : ℕ) (s t : Icc (0:ℝ) 1) (h : Maj (point m s) (point m t)) :
    s=t := by
  let N : ℝ := 4*((m:ℝ)+3)
  have hN : 0<N := by dsimp [N]; positivity
  have hb := maj_bounds h ((3+t.val/4)/N) ((5+t.val/4)/N)
    (fun j => ⟨div_le_div_of_nonneg_right (raw_bounds m t j).1 hN.le,
      div_le_div_of_nonneg_right (raw_bounds m t j).2 hN.le⟩)
  have h1 : (5+s.val/4)/N ≤ (5+t.val/4)/N := (hb 0).2
  have h2 : (3+t.val/4)/N ≤ (3+s.val/4)/N := (hb (Fin.succ (Fin.succ 0))).1
  apply Subtype.ext
  have hu := (div_le_div_iff_of_pos_right hN).mp h1
  have hl := (div_le_div_iff_of_pos_right hN).mp h2
  linarith

private noncomputable def code : Set ℕ ≃ Icc (0:ℝ) 1 :=
  Classical.choice (Cardinal.eq.mp (Cardinal.mk_set_nat.trans (Cardinal.mk_Icc_real zero_lt_one).symm))

private noncomputable def test (m : ℕ) (C : ℝ) (j : ℕ) (x : Δ (m+3)) : ℝ := by
  classical
  exact if ∃ s : Set ℕ, j∈s ∧ Maj (point m (code s)) x then C else 0

private lemma on_point (m : ℕ) (C : ℝ) (j : ℕ) (s : Set ℕ) :
    test m C j (point m (code s)) = if j∈s then C else 0 := by
  classical
  have hh : (∃ t : Set ℕ, j∈t ∧ Maj (point m (code t)) (point m (code s))) ↔ j∈s := by
    constructor
    · rintro ⟨t,hj,ht⟩
      exact code.injective (point_antichain m _ _ ht) ▸ hj
    · intro hj
      exact ⟨s,hj,maj_refl _⟩
  simp [test,hh]

private lemma large (m : ℕ) {C : ℝ} (hC : 0<C) : ¬IsSeqCompact (family (m+3) C) := by
  classical
  intro hh
  have hm (j : ℕ) : test m C j ∈ family (m+3) C := by
    constructor
    · intro x; unfold test; split <;> simp [abs_of_pos hC,hC.le]
    · intro x y hxy
      unfold test
      split_ifs with ha hb hb
      · exact le_rfl
      · obtain ⟨s,hs,h⟩ := ha; exact (hb ⟨s,hs,maj_trans h hxy⟩).elim
      · exact hC.le
      · exact le_rfl
  obtain ⟨f,_,r,hr,ht⟩ := hh hm
  let s : Set ℕ := Set.range (fun i : ℕ => r (2*i))
  let x := point m (code s)
  have hv := tendsto_pi_nhds.mp ht x
  have he (i : ℕ) : r (2*i) ∈ s := ⟨i,rfl⟩
  have ho (i : ℕ) : r (2*i+1) ∉ s := by
    rintro ⟨j,hj⟩; have := hr.injective hj; omega
  have h1 : Tendsto (fun _ : ℕ => C) atTop (𝓝 (f x)) := by
    simpa [Function.comp_def,x,on_point,he] using
      (hv.comp (show StrictMono (fun k : ℕ => 2*k) from fun i j h => by dsimp; omega).tendsto_atTop)
  have h2 : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 (f x)) := by
    simpa [Function.comp_def,x,on_point,ho] using
      (hv.comp (show StrictMono (fun k : ℕ => 2*k+1) from fun i j h => by dsimp; omega).tendsto_atTop)
  have e1 : C = f x := tendsto_nhds_unique tendsto_const_nhds h1
  have e2 : 0 = f x := tendsto_nhds_unique tendsto_const_nhds h2
  linarith

end OMA.S_mo_267680

open OMA.S_mo_267680

theorem OMA.solution : type_of% @OMA.S_mo_267680.main := by
  intro n C
  refine ⟨family_compact n C,fun hC => ⟨?_,small n C⟩⟩
  intro hc
  by_contra! hn
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
  rw [Nat.add_comm] at hc
  exact large m hC hc
