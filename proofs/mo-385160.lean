import OMAStatements.S_mo_385160

namespace OMA.S_mo_385160
open Finset Matrix Set

private def reachable {n : ℕ} (y : V n) : Set (V n) := {z | ∃ M : Mat n, Ordered M ∧ M *ᵥ y=z}

private lemma contRow {n : ℕ} (y : V n) : Continuous (fun M : Mat n => M *ᵥ y) := by
  unfold Matrix.mulVec dotProduct
  fun_prop

private lemma closedAll {X ι : Type*} [TopologicalSpace X] {p : ι → X → Prop}
    (h : ∀ i, IsClosed {x | p i x}) : IsClosed {x | ∀ i, p i x} := by
  simpa only [Set.ofPred_forall] using isClosed_iInter h

private lemma compactReach {n : ℕ} (y : V n) : IsCompact (reachable y) := by
  have hclosed : IsClosed {M : Mat n | Ordered M} := by
    simp only [Ordered,mem_doublyStochastic_iff_sum, Monotone]
    apply IsClosed.inter
    · apply IsClosed.inter
      · apply closedAll; intro i; apply closedAll; intro j
        exact isClosed_le continuous_const (by fun_prop)
      · apply IsClosed.inter <;> apply closedAll <;> intro i <;> exact isClosed_eq (by fun_prop) continuous_const
    · apply closedAll; intro k
      change IsClosed {M : Mat n | ∀ i j, i≤j → (∑ a ∈ Finset.Ici k, M i a) ≤ ∑ a ∈ Finset.Ici k, M j a}
      apply closedAll; intro i; apply closedAll; intro j
      by_cases h : i≤j
      · simpa only [h,true_implies] using
          (isClosed_le (f := fun M : Mat n => ∑ a ∈ Finset.Ici k, M i a)
            (g := fun M => ∑ a ∈ Finset.Ici k,M j a) (by fun_prop) (by fun_prop))
      · simp [h]
  have hc : IsCompact {M : Mat n | Ordered M} := by
    apply (isCompact_Icc (a:=(0:ℝ)) (b:=1)).matrix.of_isClosed_subset hclosed
    intro M hm i j
    exact ⟨nonneg_of_mem_doublyStochastic hm.1,le_one_of_mem_doublyStochastic hm.1⟩
  exact hc.image (contRow y)

private lemma convexReach {n : ℕ} (y : V n) : Convex ℝ (reachable y) := by
  rintro x ⟨M,hM,rfl⟩ z ⟨N,hN,rfl⟩ a b ha hb hab
  refine ⟨a • M+b • N,⟨convex_doublyStochastic hM.1 hN.1 ha hb hab,?_⟩,?_⟩
  · intro k i j hij
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,sum_add_distrib,←Finset.mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left (hM.2 k hij) ha) (mul_le_mul_of_nonneg_left (hN.2 k hij) hb)
  · simp [Matrix.add_mulVec,Matrix.smul_mulVec]

private lemma selfReach {n : ℕ} (y : V n) : y ∈ reachable y := by
  refine ⟨1,⟨(doublyStochastic ℝ (Fin (n+1))).one_mem,?_⟩,by simp⟩
  intro k i j hij
  simp only [Matrix.one_apply,sum_ite_eq,Finset.mem_Ici]
  split <;> split <;> grind

private lemma necessary {n : ℕ} {x y : V n} (hy : Monotone y) (h : x ∈ reachable y) :
    ((∑ i,x i)=∑ i,y i) ∧ ∀ i, (∑ j ∈ Iic i,y j) ≤ ∑ j ∈ Iic i,x j := by
  obtain ⟨M,hM,rfl⟩ := h
  refine ⟨sum_mulVec_of_mem_doublyStochastic hM.1,?_⟩
  intro k
  let s := Finset.Iic k
  let w (j : Fin (n+1)) := ∑ i ∈ s, M i j
  have hw0 (j) : 0≤w j := sum_nonneg fun _ _ => nonneg_of_mem_doublyStochastic hM.1
  have hw1 (j) : w j≤1 := by
    rw [←sum_col_of_mem_doublyStochastic hM.1 j]
    exact sum_le_univ_sum_of_nonneg fun _ => nonneg_of_mem_doublyStochastic hM.1
  have hws : ∑ j, w j = (s.card:ℝ) := by
    dsimp [w]; rw [sum_comm]; simp [sum_row_of_mem_doublyStochastic hM.1]
  have hcalc : (∑ j ∈ s,(y j-y k)) ≤ ∑ j,w j*(y j-y k) := by
    conv_lhs => rw [←Finset.filter_univ_mem s, Finset.sum_filter]
    apply sum_le_sum
    intro j _
    by_cases hj : j∈s
    · rw [if_pos hj]
      exact le_mul_of_le_one_left (sub_nonpos.mpr (hy (Finset.mem_Iic.mp hj))) (hw1 j)
    · rw [if_neg hj]
      exact mul_nonneg (hw0 _) (sub_nonneg.mpr (hy (le_of_not_ge (fun hj' => hj (Finset.mem_Iic.mpr hj')))))
  have he : ∑ i ∈ s,(M *ᵥ y) i = ∑ j,w j*y j := by
    simp only [mulVec,dotProduct,w,Finset.sum_mul]; rw [sum_comm]
  change (∑ j ∈ s,y j) ≤ ∑ i ∈ s,(M *ᵥ y) i
  rw [he]
  simp only [sum_sub_distrib,mul_sub,←sum_mul,hws,sum_const,nsmul_eq_mul] at hcalc
  linarith

private noncomputable def step {n : ℕ} (i : Fin n) : Mat n :=
  (1/2:ℝ) • 1 + (1/2:ℝ) • (Equiv.swap i.castSucc i.succ).permMatrix ℝ

private lemma stepDS {n : ℕ} (i : Fin n) : step i ∈ doublyStochastic ℝ (Fin (n+1)) :=
  convex_doublyStochastic (one_mem _) permMatrix_mem_doublyStochastic (by norm_num) (by norm_num) (by norm_num)

private lemma step_val {n : ℕ} (i : Fin n) (z : V n) (j : Fin (n+1)) :
    (step i *ᵥ z) j = if j=i.castSucc ∨ j=i.succ then (z i.castSucc+z i.succ)/2 else z j := by
  simp only [step,add_mulVec,smul_mulVec,one_mulVec,Matrix.permMatrix_mulVec,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul,Function.comp_apply]
  by_cases h1 : j=i.castSucc
  · subst j; simp; ring
  by_cases h2 : j=i.succ
  · subst j; simp; ring
  simp [h1,h2,Equiv.swap_apply_of_ne_of_ne h1 h2]; ring

private lemma step_mono {n : ℕ} (i : Fin n) {z : V n} (hz : Monotone z) : Monotone (step i *ᵥ z) := by
  intro j k hj
  simp only [step_val]
  have hv1 : i.castSucc.val = i.val := rfl
  have hv2 : i.succ.val = i.val+1 := rfl
  have hpair : z i.castSucc ≤ z i.succ := hz (by omega)
  split_ifs with hj' hk' hk'
  · rfl
  · have hv : i.succ≤k := by rcases hj' with h|h <;> omega
    linarith [hz hv]
  · have hv : j ≤ i.castSucc := by rcases hk' with h|h <;> omega
    linarith [hz hv]
  · exact hz hj

private lemma step_reach {n : ℕ} {y z : V n} (hz : z∈reachable y) (i : Fin n) :
    step i *ᵥ z ∈ reachable y := by
  obtain ⟨M,hM,rfl⟩ := hz
  refine ⟨step i*M,⟨mul_mem (stepDS i) hM.1,?_⟩,(mulVec_mulVec _ _ _).symm⟩
  intro k
  have he : (fun r => ∑ j ∈ Finset.Ici k,(step i*M) r j) =
      step i *ᵥ (fun r => ∑ j ∈ Finset.Ici k,M r j) := by
    ext r; simp only [Matrix.mul_apply,mulVec,dotProduct,Finset.mul_sum]; rw [sum_comm]
  rw [he]; exact step_mono i (hM.2 k)

private lemma step_lipschitz {n : ℕ} (i : Fin n) (x z : V n) :
    ‖step i *ᵥ x-step i *ᵥ z‖ ≤ ‖x-z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  change ‖(step i *ᵥ x) j - (step i *ᵥ z) j‖ ≤ _
  simp only [step_val]
  split
  · have ha := norm_le_pi_norm (x-z) i.castSucc
    have hb := norm_le_pi_norm (x-z) i.succ
    simp only [Pi.sub_apply,Real.norm_eq_abs,abs_le] at *
    constructor <;> linarith
  · exact norm_le_pi_norm (x-z) _

private lemma edge_flows {n : ℕ} (x y : V n) (hx : StrictMono x)
    (ht : (∑ i,x i)=∑ i,y i) (hpre : ∀ i,(∑ j ∈ Finset.Iic i,y j) ≤ ∑ j ∈ Finset.Iic i,x j) :
    ∃ w : Fin n → ℝ, (∀ i,0≤w i) ∧ ∑ i, w i • (step i *ᵥ x-x) = x-y := by
  let H (i : Fin (n+1)) := ∑ j ∈ Finset.Iic i,(x j-y j)
  let G (i : Fin (n+1)) := ∑ j ∈ Finset.Iio i,(x j-y j)
  have hH (i) : 0≤H i := by simpa [H,sum_sub_distrib] using sub_nonneg.mpr (hpre i)
  have hull : Finset.Iic (Fin.last n) = Finset.univ := by
    ext j; simp [Fin.le_last]
  have hlast : H (Fin.last n)=0 := by unfold H; rw [hull,sum_sub_distrib,ht,sub_self]
  have hzero : G 0=0 := by simp [G,show Finset.Iio (0:Fin (n+1))=∅ by ext j; simp]
  have hsucc (i : Fin n) : G i.succ=H i.castSucc := by
    have he : Finset.Iio i.succ=Finset.Iic i.castSucc := by ext j; simp only [Finset.mem_Iio,Finset.mem_Iic]; change (j.val < i.val+1) ↔ j.val ≤ i.val; omega
    simp [G,H,he]
  have hdiff (j) : H j-G j=x j-y j := by
    dsimp only [H,G]; rw [Finset.Iic_eq_cons_Iio,Finset.sum_cons]; abel
  let w (i : Fin n) := 2*H i.castSucc/(x i.succ-x i.castSucc)
  have hpos (i : Fin n) : 0<x i.succ-x i.castSucc := sub_pos.mpr (hx (Fin.castSucc_lt_succ))
  refine ⟨w,fun i => div_nonneg (mul_nonneg (by norm_num) (hH _)) (hpos _).le,?_⟩
  funext j
  have edge (i : Fin n) : w i*((step i *ᵥ x) j-x j) =
      (if j=i.castSucc then H i.castSucc else 0)-(if j=i.succ then G i.succ else 0) := by
    rw [step_val,hsucc]
    have hne : i.castSucc ≠ i.succ := ne_of_lt (Fin.castSucc_lt_succ)
    by_cases h1 : j=i.castSucc
    · subst j; simp [w,hne]; field_simp [(hpos i).ne']; ring
    by_cases h2 : j=i.succ
    · subst j; simp [w,hne.symm]; field_simp [(hpos i).ne']; ring
    simp [h1,h2]
  have hsum (f : Fin (n+1) → ℝ) : (∑ v, if j=v then f v else 0) = f j := by simp
  have h1 := hsum H
  rw [Fin.sum_univ_castSucc] at h1
  simp [hlast] at h1
  have h2 := hsum G
  rw [Fin.sum_univ_succ] at h2
  simp [hzero] at h2
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,edge,sum_sub_distrib]
  rw [h1,h2,hdiff]

private lemma reach_of_flows {n : ℕ} (x y : V n) (w : Fin n → ℝ) (hw : ∀ i,0≤w i)
    (hf : ∑ i,w i • (step i *ᵥ x-x) = x-y) : x∈reachable y := by
  let W := 1+∑ i,w i
  have hsum : 0≤∑ i,w i := sum_nonneg fun i _ => hw i
  have hW : 0<W := by dsimp [W]; linarith
  let F (z : V n) := W⁻¹ • (y+∑ i,w i • (step i *ᵥ z))
  have hF (z : V n) (hz : z∈reachable y) : F z ∈ reachable y := by
    let u : Fin (n+1) → ℝ := Fin.cons 1 w
    let f : Fin (n+1) → V n := Fin.cons y (fun i => step i *ᵥ z)
    have h := (convexReach y).centerMass_mem (t:=univ) (w:=u) (z:=f)
      (fun i _ => Fin.cases (by norm_num [u]) (fun j => by simpa [u] using hw j) i)
      (by simpa [u,Fin.sum_univ_succ,W] using hW)
      (fun i _ => Fin.cases (selfReach y) (fun j => step_reach hz j) i)
    simpa [Finset.centerMass,Fin.sum_univ_succ,u,f,W,F] using h
  have hfix : F x=x := by
    simp only [smul_sub,sum_sub_distrib,←Finset.sum_smul] at hf
    have he : y+∑ i,w i • (step i *ᵥ x)=W • x := by
      dsimp [W]; rw [add_smul,one_smul,sub_eq_iff_eq_add.mp hf]; abel
    change W⁻¹ • (y+∑ i,w i • (step i *ᵥ x)) = x
    rw [he,smul_smul,inv_mul_cancel₀ hW.ne',one_smul]
  have hcontract (z : V n) : ‖F z-F x‖ ≤ W⁻¹*(∑ i,w i)*‖z-x‖ := by
    have he : F z-F x = W⁻¹ • (∑ i,w i • (step i *ᵥ z-step i *ᵥ x)) := by
      dsimp only [F]; rw [←smul_sub,add_sub_add_left_eq_sub]
      simp only [smul_sub,sum_sub_distrib]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW),mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hW).le
    calc
      _ ≤ ∑ i,‖w i • (step i *ᵥ z-step i *ᵥ x)‖ := norm_sum_le _ _
      _ ≤ ∑ i,w i * ‖z-x‖ := by
        apply sum_le_sum; intro i _
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (step_lipschitz _ _ _) (hw _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  obtain ⟨z,hz,hmin⟩ := (compactReach y).exists_infDist_eq_dist ⟨y,selfReach y⟩ x
  by_contra hx
  have hn : 0<‖z-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => hx (he ▸ hz)))
  have hle := Metric.infDist_le_dist_of_mem (x:=x) (hF z hz)
  rw [hmin,dist_comm x z,dist_comm x (F z),dist_eq_norm,dist_eq_norm] at hle
  have hco := hcontract z
  rw [hfix] at hco
  have hlt : W⁻¹*(∑ i,w i)<1 := by
    rw [←div_eq_inv_mul,div_lt_one hW]; dsimp [W]; linarith
  nlinarith [mul_lt_mul_of_pos_right hlt hn]

private lemma sufficient {n : ℕ} (x y : V n) (hx : Monotone x) (hy : StrictMono y)
    (ht : (∑ i,x i)=∑ i,y i) (hpre : ∀ i,(∑ j ∈ Finset.Iic i,y j) ≤ ∑ j ∈ Finset.Iic i,x j) :
    x∈reachable y := by
  let z (t : ℝ) := (1-t) • x+t • y
  have hcont : Continuous z := by dsimp [z]; fun_prop
  have hsub : Set.Ioo (0:ℝ) 1 ⊆ z ⁻¹' reachable y := by
    intro t h
    have h0 := h.1
    have h1 := h.2
    have hlt : StrictMono (z t) := by
      intro i j hij
      change (1-t)*x i+t*y i < (1-t)*x j+t*y j
      exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (hx hij.le) (by linarith))
        (mul_lt_mul_of_pos_left (hy hij) h0)
    have ht' : (∑ i,z t i) = ∑ i,y i := by
      simp only [z,Pi.add_apply,Pi.smul_apply,smul_eq_mul,sum_add_distrib,←Finset.mul_sum,ht]
      ring
    have hp' (i) : (∑ j ∈ Finset.Iic i,y j) ≤ ∑ j ∈ Finset.Iic i,z t j := by
      simp only [z,Pi.add_apply,Pi.smul_apply,smul_eq_mul,sum_add_distrib,←Finset.mul_sum]
      linarith [mul_le_mul_of_nonneg_left (hpre i) (sub_nonneg.mpr h1.le)]
    obtain ⟨w,hw,hf⟩ := edge_flows (z t) y hlt ht' hp'
    exact reach_of_flows _ _ _ hw hf
  have hcl := closure_minimal hsub ((compactReach y).isClosed.preimage hcont)
  have hz : (0:ℝ) ∈ closure (Set.Ioo (0:ℝ) 1) := by rw [closure_Ioo (by norm_num)]; simp
  simpa [z] using hcl hz

end OMA.S_mo_385160

theorem OMA.solution : type_of% @OMA.S_mo_385160.main := by
  intro n x y hx hy
  exact ⟨fun h => OMA.S_mo_385160.sufficient _ _ hx hy h.1 h.2,
    OMA.S_mo_385160.necessary hy.monotone⟩
