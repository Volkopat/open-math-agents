import OMAStatements.S_mo_271151

namespace OMA.S_mo_271151
open Finset Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

private def isotone (r : ι→ι→Prop) (x : ι→ℝ) : Prop := ∀ i j, r i j → x i ≤ x j
private def loss (a x : ι→ℝ) : ℝ := ∑ i, (x i-a i)^2

private lemma minimum (r : ι→ι→Prop) (a : ι→ℝ) :
    ∃ x : ι→ℝ, isotone r x ∧ ∀ y, isotone r y → loss a x ≤ loss a y := by
  classical
  let E := EuclideanSpace ℝ ι
  let K : Set E := {x | isotone r (fun i => x i)}
  have hcl : IsClosed K := by
    have he : K = ⋂ i, ⋂ j, ⋂ (_ : r i j), {x : E | x i≤x j} := by
      ext x
      simp [K,isotone]
    rw [he]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun _ =>
      isClosed_le (PiLp.continuous_apply 2 _ i) (PiLp.continuous_apply 2 _ j))))
  have hcv : Convex ℝ K := by
    intro x hx y hy s t hs ht _ i j hij
    exact add_le_add (mul_le_mul_of_nonneg_left (hx i j hij) hs) (mul_le_mul_of_nonneg_left (hy i j hij) ht)
  obtain ⟨v,hv,ht⟩ := exists_norm_eq_iInf_of_complete_convex (K:=K) ⟨0,fun _ _ _ => le_rfl⟩
    hcl.isComplete hcv (WithLp.toLp 2 a)
  refine ⟨fun i => v i,hv,?_⟩
  intro y hy
  have h := ciInf_le (f:=fun z : K => ‖WithLp.toLp 2 a-z.val‖)
    (show BddBelow (range (fun z : K => ‖WithLp.toLp 2 a-z.val‖)) from
      ⟨0,Set.forall_mem_range.mpr (fun z => norm_nonneg _)⟩) ⟨WithLp.toLp 2 y,hy⟩
  rw [← ht] at h
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  change ‖(WithLp.toLp 2 a : EuclideanSpace ℝ ι)-v‖^2 ≤
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ ι)-WithLp.toLp 2 y‖^2 at hh
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq] at hh
  change (∑ i,(a i-v i)^2)≤∑ i,(a i-y i)^2 at hh
  simpa only [loss, sub_sq_comm] using hh

private lemma directions {r : ι→ι→Prop} {x : ι→ℝ} (hx : isotone r x)
    (v : ι→ℝ) (h : ∀ i j, r i j → x i=x j → v i≤v j) :
    ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), isotone r (fun i => x i+t*v i) := by
  classical
  have he (i j) : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      r i j → x i+t*v i ≤ x j+t*v j := by
    by_cases hij : r i j
    · rcases (hx i j hij).lt_or_eq with hlt|heq
      · have ht : ∀ᶠ t : ℝ in 𝓝 0, x i+t*v i < x j+t*v j := by
          apply ContinuousAt.eventually_lt (f:=fun t : ℝ => x i+t*v i) (g:=fun t : ℝ => x j+t*v j)
          · fun_prop
          · fun_prop
          · simpa using hlt
        filter_upwards [ht.filter_mono nhdsWithin_le_nhds] with t ht using fun _ => ht.le
      · filter_upwards [self_mem_nhdsWithin] with t ht
        intro _
        exact add_le_add heq.le (mul_le_mul_of_nonneg_left (h i j hij heq) (le_of_lt ht))
    · exact Eventually.of_forall (fun t hh => (hij hh).elim)
  apply (eventually_all.mpr fun i => eventually_all.mpr (he i))

private lemma primal_residual {r : ι→ι→Prop} (a x : ι→ℝ) (hx : isotone r x)
    (hm : ∀ y, isotone r y → loss a x ≤ loss a y)
    (v : ι→ℝ) (hd : ∀ i j, r i j → x i=x j → v i≤v j) :
    0 ≤ ∑ i,(x i-a i)*v i := by
  let c := ∑ i,(x i-a i)*v i
  let b := ∑ i,(v i)^2
  have he (t : ℝ) : loss a (fun i => x i+t*v i)-loss a x = t*(2*c+t*b) := by
    unfold loss
    rw [← Finset.sum_sub_distrib]
    simp only [c,b,Finset.mul_sum]
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hn : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), 0 ≤ 2*c+t*b := by
    filter_upwards [directions hx v hd,self_mem_nhdsWithin] with t ht ht'
    have h := sub_nonneg.mpr (hm _ ht)
    rw [he] at h
    exact nonneg_of_mul_nonneg_right h (show 0<t from ht')
  have hlim : Tendsto (fun t : ℝ => 2*c+t*b) (nhdsWithin 0 (Ioi 0)) (𝓝 (2*c)) := by
    have h : Continuous (fun t : ℝ => 2*c+t*b) := by fun_prop
    simpa using (h.continuousAt.continuousWithinAt (s:=Ioi 0) (x:=0)).tendsto
  have h0 := ge_of_tendsto hlim hn
  change 0≤c
  linarith


private lemma fit_eq {r : ι→ι→Prop} (a x : ι→ℝ) (hx : isotone r x)
    (hm : ∀ y, isotone r y → loss a x ≤ loss a y) (p : ι) :
    fitted r a p=x p := by
  classical
  let L := univ.filter (fun i => x i ≤ x p)
  let U := univ.filter (fun i => x p ≤ x i)
  have hc {ρ : ι→ι→Prop} {s : Finset ι} : s∈choices ρ p ↔ p∈s ∧ upper ρ s := by
    simp [choices]
  have hL : L∈choices (Function.swap r) p := by
    apply hc.mpr
    refine ⟨by simp [L],?_⟩
    intro i j h hi
    exact mem_filter.mpr ⟨mem_univ _,(hx j i h).trans ((mem_filter.mp hi).2)⟩
  have hU : U∈choices r p := by
    apply hc.mpr
    refine ⟨by simp [U],?_⟩
    intro i j h hi
    exact mem_filter.mpr ⟨mem_univ _,((mem_filter.mp hi).2).trans (hx i j h)⟩
  unfold fitted
  apply le_antisymm
  · apply Finset.sup'_le
    intro S hS
    apply Finset.inf'_le_of_le _ hL
    let T:=S∩L
    have hp : p∈T := mem_inter.mpr ⟨(hc.mp hS).1,(hc.mp hL).1⟩
    have hpos : 0<(T.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨p,hp⟩
    let v (i : ι) : ℝ := if i∈T then 1 else 0
    have hv (i j) (h : r i j) (he : x i=x j) : v i ≤ v j := by
      by_cases hi : i∈T
      · obtain ⟨hiS,hiL⟩:=mem_inter.mp hi
        have hjS := (hc.mp hS).2 i j h hiS
        have hjL : j∈L := by simpa [L,← he] using hiL
        have hj : j∈T := mem_inter.mpr ⟨hjS,hjL⟩
        simp [v,hi,hj]
      · by_cases hj : j∈T <;> simp [v,hi,hj]
    have hr := primal_residual a x hx hm v hv
    have hh : (∑ i,(x i-a i)*v i) = ∑ i∈T, (x i-a i) := by simp [v,mul_ite]
    rw [hh,Finset.sum_sub_distrib] at hr
    change (∑ i∈T,a i)/(T.card:ℝ) ≤ x p
    apply (div_le_iff₀ hpos).mpr
    have hxt : (∑ i∈T,x i) ≤ ∑ _∈T,x p := sum_le_sum fun i hi =>
      (mem_filter.mp (mem_inter.mp hi).2).2
    simp only [sum_const,nsmul_eq_mul] at hxt
    linarith
  · apply Finset.le_sup'_of_le _ hU
    apply Finset.le_inf'
    intro S hS
    let T:=U∩S
    have hp : p∈T := mem_inter.mpr ⟨(hc.mp hU).1,(hc.mp hS).1⟩
    have hpos : 0<(T.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨p,hp⟩
    let v (i : ι) : ℝ := if i∈T then -1 else 0
    have hv (i j) (h : r i j) (he : x i=x j) : v i≤v j := by
      by_cases hj : j∈T
      · obtain ⟨hjU,hjS⟩:=mem_inter.mp hj
        have hiS := (hc.mp hS).2 j i h hjS
        have hiU : i∈U := by simpa [U,he] using hjU
        have hi : i∈T := mem_inter.mpr ⟨hiU,hiS⟩
        simp [v,hi,hj]
      · by_cases hi : i∈T <;> simp [v,hi,hj]
    have hr := primal_residual a x hx hm v hv
    have hh : (∑ i,(x i-a i)*v i) = ∑ i∈T, (a i-x i) := by simp [v,mul_ite]
    rw [hh,Finset.sum_sub_distrib] at hr
    change x p≤(∑ i∈T,a i)/(T.card:ℝ)
    apply (le_div_iff₀ hpos).mpr
    have hxt : (∑ _∈T,x p) ≤ ∑ i∈T,x i := sum_le_sum fun i hi =>
      (mem_filter.mp (mem_inter.mp hi).1).2
    simp only [sum_const,nsmul_eq_mul] at hxt
    linarith


private lemma fea_iff {n} (X : Mat n) :
    Feasible X ↔ isotone edge (fun p : Cell n => X p.1 p.2) := by
  constructor
  · rintro ⟨hs,hx⟩ ⟨i,j⟩ q (rfl|rfl)
    · exact (hs.apply j i).le
    · exact hx i j
  · intro h
    refine ⟨?_,fun i j => h (i,j) (i,i) (Or.inr rfl)⟩
    ext i j
    apply le_antisymm (h (j,i) (i,j) (Or.inl rfl)) (h (i,j) (j,i) (Or.inl rfl))

private lemma cost_eq {n} (A X : Mat n) :
    cost A X=loss (fun p : Cell n => A p.1 p.2) (fun p : Cell n => X p.1 p.2) := by
  simp [cost,loss,Fintype.sum_prod_type]

end OMA.S_mo_271151
open OMA.S_mo_271151
theorem OMA.solution : type_of% @OMA.S_mo_271151.main := by
  intro n A
  let a : Cell n→ℝ := fun p => A p.1 p.2
  obtain ⟨x,hx,hm⟩:=minimum edge a
  have he : fitted edge a = x := funext (fit_eq a x hx hm)
  have hx' : ∀ p : Cell n, projection A p.1 p.2 = x p := fun p => congrFun he p
  have hproj : (fun p : Cell n => projection A p.1 p.2)=x := funext hx'
  have hf : Feasible (projection A) := by rw [fea_iff,hproj];exact hx
  refine ⟨hf, ?_, ?_⟩
  · intro Y hy
    rw [cost_eq,cost_eq,hproj]
    exact hm _ ((fea_iff _).mp hy)
  · intro Y hy eq
    let y : Cell n→ℝ := fun p => Y p.1 p.2
    have hye : isotone edge y := (fea_iff _).mp hy
    have hle : ∀ z, isotone edge z → loss a y ≤ loss a z := by
      intro z hz
      have heq : loss a x = loss a y := by
        rw [cost_eq,cost_eq,hproj] at eq
        exact eq
      exact heq ▸ hm z hz
    have h := funext (fit_eq a y hye hle)
    ext i j
    exact (congrFun h (i,j)).symm
