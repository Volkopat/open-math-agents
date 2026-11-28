import OMAStatements.S_mo_419913

namespace OMA.S_mo_419913
open scoped ENNReal

private theorem slice_mem {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : Seq}
    (hf : Memℓp f p) (b : Bool) : Memℓp (fun i : ℕ => f (b,i)) p := by
  by_cases ht : p = ⊤
  · subst p
    obtain ⟨C,hC⟩ := hf.bddAbove
    exact memℓp_infty ⟨C, by rintro _ ⟨i,rfl⟩; exact hC ⟨(b,i),rfl⟩⟩
  have hp := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' ht
  apply memℓp_gen
  exact (summable_prod_of_nonneg (f := fun i : I => ‖f i‖ ^ p.toReal)
    (by intro i; positivity)).1 (hf.summable hp) |>.1 b

private theorem join_mem {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : Seq}
    (hf : ∀ b : Bool, Memℓp (fun n : ℕ => f (b,n)) p) : Memℓp f p := by
  by_cases ht : p = ⊤
  · subst p
    obtain ⟨C,hC⟩ := (hf false).bddAbove
    obtain ⟨D,hD⟩ := (hf true).bddAbove
    apply memℓp_infty
    refine ⟨max C D, ?_⟩
    rintro _ ⟨⟨b,n⟩,rfl⟩
    cases b
    · exact (hC ⟨n,rfl⟩).trans (le_max_left ..)
    · exact (hD ⟨n,rfl⟩).trans (le_max_right ..)
  have hp := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' ht
  exact memℓp_gen ((summable_prod_of_nonneg (f := fun i : I => ‖f i‖ ^ p.toReal)
    (by intro i; positivity)).2 ⟨fun b => (hf b).summable hp, (hasSum_fintype _).summable⟩)

private theorem parent_mem {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℕ → ℝ}
    (hf : Memℓp f p) : Memℓp (fun n : ℕ => f (n/5)) p := by
  by_cases ht : p = ⊤
  · subst p
    obtain ⟨C,hC⟩ := hf.bddAbove
    exact memℓp_infty ⟨C,by rintro _ ⟨n,rfl⟩; exact hC ⟨n/5,rfl⟩⟩
  have hp := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' ht
  apply memℓp_gen
  have hs : Summable (fun i : ℕ × Fin 5 => ‖f i.1‖ ^ p.toReal) := by
    apply (summable_prod_of_nonneg (by intro n; positivity)).2
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simpa [tsum_fintype] using (hf.summable hp).mul_left 5
  exact (Nat.divModEquiv 5).summable_iff.mpr hs

private theorem child_mem {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℕ → ℝ}
    (hf : Memℓp f p) (j : Fin 5) : Memℓp (fun n => f (child n j)) p := by
  by_cases ht : p = ⊤
  · subst p
    obtain ⟨C,hC⟩ := hf.bddAbove
    exact memℓp_infty ⟨C,by rintro _ ⟨n,rfl⟩; exact hC ⟨child n j,rfl⟩⟩
  have hp := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' ht
  apply memℓp_gen
  exact (hf.summable hp).comp_injective (i := fun n => child n j) (by
    intro n m h; change 5*n+j.val=5*m+j.val at h; omega)

private theorem mem_b {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space p) :
    Memℓp (bAct (fun i => f i)) p := by
  apply join_mem
  intro b
  cases b
  · simpa [bAct] using slice_mem f.property false
  · change Memℓp (fun n : ℕ => f (true,n) + (f (false,n/5)-3*f (false,n))) p
    exact (slice_mem f.property true).add ((parent_mem (slice_mem f.property false)).sub
      ((slice_mem f.property false).const_smul (3:ℝ)))

private theorem mem_bt {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space p) :
    Memℓp (btAct (fun i => f i)) p := by
  apply join_mem
  intro b
  cases b
  · have hs : Memℓp (fun n : ℕ => ∑ j : Fin 5, f (true,child n j)) p :=
      Memℓp.finsetSum (f := fun (j : Fin 5) (n : ℕ) => f (true,child n j))
        Finset.univ (fun j _ => child_mem (slice_mem f.property true) j)
    change Memℓp (fun n : ℕ => f (false,n) + ((∑ j : Fin 5, f (true,child n j))-3*f (true,n))) p
    exact (slice_mem f.property false).add (hs.sub ((slice_mem f.property true).const_smul (3:ℝ)))
  · simpa [btAct] using slice_mem f.property true

end OMA.S_mo_419913

namespace OMA.S_mo_419913
open scoped ENNReal
open Filter Topology

private noncomputable def rawB : Seq →ₗ[ℝ] Seq where
  toFun := bAct
  map_add' f g := by
    funext ⟨b,n⟩; cases b <;> (simp [bAct,Pi.add_apply] <;> ring)
  map_smul' a f := by
    funext ⟨b,n⟩; cases b <;> (simp [bAct,Pi.smul_apply,smul_eq_mul] <;> ring)

private noncomputable def rawT : Seq →ₗ[ℝ] Seq where
  toFun := btAct
  map_add' f g := by
    funext ⟨b,n⟩; cases b <;> (simp [btAct,Pi.add_apply,Finset.sum_add_distrib] <;> ring)
  map_smul' a f := by
    funext ⟨b,n⟩; cases b <;> (simp [btAct,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum] <;> ring)

private theorem lift_operator {p : ℝ≥0∞} [Fact (1 ≤ p)] (T : Seq →ₗ[ℝ] Seq)
    (hm : ∀ f : Space p, Memℓp (T (fun j => f j)) p)
    (hc : ∀ i : I, Continuous (fun f : Seq => T f i)) :
    ∃ L : Space p →L[ℝ] Space p, extendsAt T p L := by
  let L : Space p →ₗ[ℝ] Space p := {
    toFun := fun f => ⟨T (fun j => f j), hm f⟩
    map_add' := fun f g => by
      apply Subtype.ext
      exact T.map_add (fun j => f j) (fun j => g j)
    map_smul' := fun a f => by
      apply Subtype.ext
      exact T.map_smul a (fun j => f j) }
  have ev (i : I) : Continuous (fun f : Space p => f i) := (lp.lipschitzWith_one_eval p i).continuous
  have cont : Continuous (fun f : Space p => fun j : I => f j) := continuous_pi ev
  refine ⟨⟨L, L.continuous_of_seq_closed_graph ?_⟩,fun _ _ => rfl⟩
  intro u x y hu hv
  apply lp.ext
  funext i
  apply tendsto_nhds_unique ((ev i).continuousAt.tendsto.comp hv)
  exact ((hc i).comp cont).continuousAt.tendsto.comp hu

private theorem both_lift (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ B BT : Space p →L[ℝ] Space p, extendsAt bAct p B ∧ extendsAt btAct p BT := by
  obtain ⟨B,hB⟩ := lift_operator rawB (p := p) mem_b (by
    rintro ⟨b,n⟩; cases b <;> simp only [rawB,LinearMap.coe_mk,AddHom.coe_mk,bAct,
      Bool.false_eq_true,if_false,if_true] <;> fun_prop)
  obtain ⟨BT,hBT⟩ := lift_operator rawT (p := p) mem_bt (by
    rintro ⟨b,n⟩; cases b <;> simp only [rawT,LinearMap.coe_mk,AddHom.coe_mk,btAct,
      Bool.false_eq_true,if_false,if_true] <;> fun_prop)
  exact ⟨B,BT,hB,hBT⟩

end OMA.S_mo_419913

namespace OMA.S_mo_419913
open scoped ENNReal

private lemma sum_child (m n : ℕ) :
    (∑ j : Fin 5, if child m j = n then (1:ℝ) else 0) = if n/5=m then 1 else 0 := by
  by_cases h : n/5=m
  · subst m
    let k : Fin 5 := ⟨n%5,by omega⟩
    have iff' (j : Fin 5) : child (n/5) j=n ↔ j=k := by
      unfold child
      constructor
      · intro hh; apply Fin.ext; change j.val=n%5; omega
      · rintro rfl; change 5*(n/5)+n%5=n; omega
    simp [iff']
  · have ne (j : Fin 5) : child m j ≠ n := by unfold child; omega
    simp [h,ne]

private theorem transpose_entries (i j : I) :
    bAct (Pi.single j 1) i = btAct (Pi.single i 1) j := by
  obtain ⟨b,n⟩ := i
  obtain ⟨c,m⟩ := j
  cases b <;> cases c <;> simp [bAct,btAct,Pi.single_apply,Prod.mk.injEq,eq_comm]
  simpa [eq_comm] using (sum_child m n).symm

private theorem bij_b : Function.Bijective bAct := by
  let undo (f : Seq) (i : I) : ℝ :=
    if i.1 then f i - (f (false,i.2/5)-3*f (false,i.2)) else f i
  have left : Function.LeftInverse undo bAct := by
    intro f; funext ⟨b,n⟩; cases b <;> simp [undo,bAct]
  have right : Function.RightInverse undo bAct := by
    intro f; funext ⟨b,n⟩; cases b <;> simp [undo,bAct]
  exact ⟨left.injective,right.surjective⟩

private theorem bij_bt : Function.Bijective btAct := by
  let undo (f : Seq) (i : I) : ℝ :=
    if i.1 then f i else f i - ((∑ j : Fin 5, f (true,child i.2 j))-3*f (true,i.2))
  have left : Function.LeftInverse undo btAct := by
    intro f; funext ⟨b,n⟩; cases b <;> simp [undo,btAct]
  have right : Function.RightInverse undo btAct := by
    intro f; funext ⟨b,n⟩; cases b <;> simp [undo,btAct]
  exact ⟨left.injective,right.surjective⟩

private theorem counter : ∃ x : Space ⊤, x ≠ 0 ∧ ∀ i : I,
    (1/2 : ℝ)*x i + (1-1/2 : ℝ)*btAct (bAct (fun j => x j)) i=0 := by
  let x : Space ⊤ := ⟨fun _ => 1,memℓp_infty ⟨1,by rintro _ ⟨i,rfl⟩; norm_num⟩⟩
  refine ⟨x,?_,?_⟩
  · intro hz
    have := congrArg (fun f : Space ⊤ => f (false,0)) hz
    norm_num [x] at this
  · rintro ⟨b,n⟩
    cases b <;> norm_num [x,btAct,bAct]

end OMA.S_mo_419913

namespace OMA.S_mo_419913
lemma inner_adjoint_of_entries (T U : Space 2 →L[ℝ] Space 2)
    (h : ∀ i j : I, (T (lp.single 2 j 1)) i = (U (lp.single 2 i 1)) j) :
    ∀ x y, inner ℝ (T x) y = inner ℝ x (U y) := by
  have hadj : T.adjoint = U := by
    refine lp.ext_continuousLinearMap (by simp) fun i => ?_
    apply ContinuousLinearMap.ext_ring
    apply lp.ext
    funext j
    change (T.adjoint (lp.single 2 i 1)) j = (U (lp.single 2 i 1)) j
    have e := T.adjoint_inner_right (lp.single 2 j 1) (lp.single 2 i 1)
    simpa only [lp.inner_single_left,lp.inner_single_right,Real.inner_apply,one_mul,mul_one]
      using e.trans (by simpa only [lp.inner_single_right,Real.inner_apply,one_mul,mul_one] using h i j)
  intro x y
  rw [← hadj,T.adjoint_inner_right]
end OMA.S_mo_419913

open OMA.S_mo_419913
theorem OMA.solution : type_of% @OMA.S_mo_419913.main := by
  refine ⟨both_lift,?_,bij_b,bij_bt,counter⟩
  intro B BT hB hBT
  apply inner_adjoint_of_entries
  intro i j
  rw [hB,hBT]
  simpa only [lp.coeFn_single] using transpose_entries i j
