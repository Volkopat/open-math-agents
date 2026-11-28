import OMAStatements.S_mo_238612

namespace OMA.S_mo_238612
open Matrix Set Finset

private lemma box_criterion {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]
    (M : Matrix ι α ℝ) (cap : α→ℝ) (d : ι→ℝ) (hc : 0 ≤ cap) :
    (∃ p ∈ Icc (0:α→ℝ) cap, d ≤ M*ᵥp) ↔ ∀ w : ι→ℝ, 0 ≤ w →
      (∑ i,w i*d i) ≤ ∑ j,cap j*max (∑ i,w i*M i j) 0 := by
  have hcost (w : ι→ℝ) (p : α→ℝ) : ∑ i,w i*(M*ᵥp) i = ∑ j,(∑ i,w i*M i j)*p j := by
    simp only [mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    rw [sum_comm]
  constructor
  · rintro ⟨p,hp,hd⟩ w hw
    calc
      _ ≤ ∑ i,w i*(M*ᵥp) i := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hd i) (hw i)
      _ = _ := hcost w p
      _ ≤ _ := by
        apply sum_le_sum
        intro j _
        rw [mul_comm (cap j)]
        exact mul_le_mul (le_max_left _ _) (hp.2 j) (hp.1 j) (le_max_right _ _)
  · intro hd
    by_contra! hfail
    let F := M.mulVecLin
    let box := Icc (0:α→ℝ) cap
    let T := F '' box
    have hcx : Convex ℝ T := (convex_Icc _ _).linear_image F
    have hcp : IsCompact T := isCompact_Icc.image F.continuous_of_finiteDimensional
    have hdis : Disjoint T (Ici d) := by
      rw [Set.disjoint_left]
      rintro x ⟨p,hp,rfl⟩ hx
      exact hfail p hp hx
    obtain ⟨ℓ,u,v,hU,huv,hV⟩ :=
      geometric_hahn_banach_compact_closed hcx hcp (convex_Ici d) isClosed_Ici hdis
    let w (i : ι) := ℓ (Pi.single i 1)
    have hrep (x : ι→ℝ) : ℓ x = ∑ i,w i*x i := by
      have he : x=∑ i,x i • Pi.single i (1:ℝ) := by
        ext j; simp [Finset.sum_apply,Pi.single_apply]
      calc
        _ = ℓ (∑ i,x i • Pi.single i (1:ℝ)) := congrArg ℓ he
        _ = _ := by simp only [map_sum,map_smul,smul_eq_mul,w]; apply sum_congr rfl; intro; intros; ring
    have hw : 0 ≤ w := by
      intro i
      change 0 ≤ w i
      by_contra! hz
      have hv := hV d (Set.mem_Ici.mpr le_rfl)
      let r := (ℓ d-v+1)/(-w i)
      have hr : 0 ≤ r := div_nonneg (by linarith) (by linarith)
      have hy : d ≤ d+r • Pi.single i (1:ℝ) := by
        intro j
        simp only [Pi.add_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
        split_ifs <;> linarith
      have hh := hV _ hy
      rw [map_add,map_smul,smul_eq_mul] at hh
      change v < ℓ d+r*w i at hh
      have he : r*(-w i)=ℓ d-v+1 := div_mul_cancel₀ _ (by linarith)
      linarith
    let q (j : α) := ∑ i,w i*M i j
    let p (j : α) := if 0 ≤ q j then cap j else 0
    have hp : p∈box := by
      constructor <;> intro j <;> dsimp [p] <;> split_ifs <;> first | exact hc j | exact le_rfl
    have hopt : ∑ j,q j*p j = ∑ j,cap j*max (q j) 0 := by
      apply sum_congr rfl
      intro j _
      dsimp [p]
      split_ifs with h
      · rw [max_eq_left h,mul_comm]
      · rw [max_eq_right (le_of_not_ge h),mul_zero,mul_zero]
    have hup := hU (F p) ⟨p,hp,rfl⟩
    have hlo := hV d (Set.mem_Ici.mpr le_rfl)
    rw [hrep] at hup hlo
    change (∑ i, w i*(M*ᵥp) i)<u at hup
    rw [hcost] at hup
    change (∑ j,q j*p j)<u at hup
    rw [hopt] at hup
    exact (not_lt_of_ge (hd w hw)) (hup.trans (huv.trans hlo))

end OMA.S_mo_238612
namespace OMA.S_mo_238612
open Finset

private lemma cutoff {n : ℕ} (q cap : Fin n → ℝ) (hc : ∀ j, 0 ≤ cap j) (hmass : 1 ≤ ∑ j,cap j) :
    ∃ s : Fin n, ∀ t : ℝ, q s+∑ j,cap j*max (q j-q s) 0 ≤ t+∑ j,cap j*max (q j-t) 0 := by
  have hn : 0<n := by
    by_contra! h
    have hz : n=0 := by omega
    subst n
    norm_num at hmass
  let _ : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let mass (v : ℝ) := ∑ j, if v ≤ q j then cap j else 0
  let A := univ.filter fun j => 1 ≤ mass (q j)
  have hA : A.Nonempty := by
    obtain ⟨j,_,hj⟩ := univ.exists_min_image q univ_nonempty
    refine ⟨j,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    simpa [mass,fun i => hj i (mem_univ _)] using hmass
  obtain ⟨s,hs,hmax⟩ := A.exists_max_image q hA
  have hge : 1 ≤ mass (q s) := (mem_filter.mp hs).2
  let B := univ.filter fun j => q s<q j
  have hgt : (∑ j, if q s<q j then cap j else 0) ≤ 1 := by
    by_cases hB : B.Nonempty
    · obtain ⟨i,hi,hmin⟩ := B.exists_min_image q hB
      have ht : q s<q i := (mem_filter.mp hi).2
      have hiff (j : Fin n) : q s<q j ↔ q i ≤ q j :=
        ⟨fun h => hmin j (mem_filter.mpr ⟨mem_univ _,h⟩),fun h => ht.trans_le h⟩
      simp_rw [hiff]
      by_contra! h
      have hmem : i∈A := mem_filter.mpr ⟨mem_univ _,h.le⟩
      exact (not_lt_of_ge (hmax i hmem)) ht
    · have hj (i : Fin n) : ¬q s<q i := by intro h; exact hB ⟨i,mem_filter.mpr ⟨mem_univ _,h⟩⟩
      simp [hj]
  refine ⟨s,fun t => ?_⟩
  rcases le_total (q s) t with ht|ht
  · have hpt (j : Fin n) : cap j*max (q j-q s) 0 ≤ cap j*max (q j-t) 0+
        (t-q s)*(if q s<q j then cap j else 0) := by
      by_cases h : q s<q j
      · rw [if_pos h,max_eq_left (sub_nonneg.mpr h.le)]
        have := mul_le_mul_of_nonneg_left (le_max_left (q j-t) 0) (hc j)
        linarith
      · rw [if_neg h,max_eq_right (sub_nonpos.mpr (le_of_not_gt h))]
        simp
        exact mul_nonneg (hc j) (le_max_right _ _)
    have hh := sum_le_sum (s:=univ) fun j _ => hpt j
    rw [sum_add_distrib,← mul_sum] at hh
    linarith only [hh,mul_le_mul_of_nonneg_left hgt (sub_nonneg.mpr ht)]
  · have hpt (j : Fin n) : cap j*max (q j-q s) 0+
        (q s-t)*(if q s ≤ q j then cap j else 0) ≤ cap j*max (q j-t) 0 := by
      by_cases h : q s ≤ q j
      · rw [if_pos h,max_eq_left (sub_nonneg.mpr h),max_eq_left (sub_nonneg.mpr (ht.trans h))]
        linarith
      · rw [if_neg h,max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
        simp
        exact mul_nonneg (hc j) (le_max_right _ _)
    have hh := sum_le_sum (s:=univ) fun j _ => hpt j
    rw [sum_add_distrib,← mul_sum] at hh
    change 1 ≤ ∑ j, if q s ≤ q j then cap j else 0 at hge
    linarith only [hh,mul_le_mul_of_nonneg_left hge (sub_nonneg.mpr ht)]
end OMA.S_mo_238612
namespace OMA.S_mo_238612
open Finset Matrix
private lemma event_cost {n k : ℕ} (A : Fin k→Finset (Fin n)) (w : Fin k→ℝ) (p : Fin n→ℝ) :
    (∑ i,w i*(∑ j ∈ A i,p j))=∑ j,p j*score A w j := by
  calc
    _ = ∑ i,∑ j,(if j∈A i then w i else 0)*p j := by
      apply sum_congr rfl
      intro i _
      simp [ite_mul,mul_sum]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [score,← sum_mul,mul_comm]

private lemma upper_score {n k : ℕ} (A : Fin k→Finset (Fin n)) (cap : Fin n→ℝ) (d : Fin k→ℝ)
    (h : feasible A cap d) (w : Fin k→ℝ) (hw : ∀ i,0 ≤ w i) (t : ℝ) :
    (∑ i,w i*d i) ≤ t+∑ j,cap j*max (score A w j - t) 0 := by
  obtain ⟨p,hp,hs,hd⟩ := h
  calc
    _ ≤ ∑ i,w i*(∑ j ∈ A i,p j) := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hd i) (hw i)
    _ = ∑ j,p j*score A w j := event_cost A w p
    _ = t+∑ j,p j*(score A w j-t) := by simp only [mul_sub,sum_sub_distrib,← sum_mul,hs,one_mul]; ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply sum_le_sum
      intro j _
      calc
        _ ≤ p j*max (score A w j-t) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) (hp j).1
        _ ≤ _ := mul_le_mul_of_nonneg_right (hp j).2 (le_max_right _ _)


private lemma exact_criterion {n k : ℕ} (A : Fin k→Finset (Fin n)) (cap : Fin n→ℝ) (d : Fin k→ℝ)
    (hc : ∀ j,0 ≤ cap j) : feasible A cap d ↔ 1 ≤ ∑ j,cap j ∧
        ∀ (w : Fin k→ℝ), (∀ i, 0 ≤ w i) → ∀ s : Fin n, (∑ i, w i*d i) ≤
          score A w s+∑ j, cap j*max (score A w j-score A w s) 0 := by
  constructor
  · intro hh
    refine ⟨?_,fun w hw s => upper_score A cap d hh w hw _⟩
    obtain ⟨p,hp,he,_⟩ := hh
    rw [← he]
    exact sum_le_sum fun j _ => (hp j).2
  · rintro ⟨hcap,ht⟩
    have H (w : Fin k→ℝ) (hw : ∀ i,0 ≤ w i) (t : ℝ) :
        (∑ i,w i*d i) ≤ t+∑ j, cap j*max (score A w j-t) 0 := by
      obtain ⟨s,hs⟩ := cutoff (score A w) cap hc hcap
      exact (ht w hw s).trans (hs t)
    let M : Matrix (Bool ⊕ Fin k) (Fin n) ℝ := fun i j => i.elim
      (fun b => if b then -1 else 1) (fun l => if j∈A l then 1 else 0)
    let D : Bool ⊕ Fin k → ℝ := Sum.elim (fun b => if b then -1 else 1) d
    have hdual (W : Bool ⊕ Fin k→ℝ) (hW : 0 ≤ W) :
        (∑ i,W i*D i) ≤ ∑ j,cap j*max (∑ i,W i*M i j) 0 := by
      let w (i : Fin k) := W (.inr i)
      let t := W (.inl true)-W (.inl false)
      have hi (j : Fin n) : ∑ i,W i*M i j = score A w j-t := by
        simp only [M,Fintype.sum_sum_type,Fintype.sum_bool,Sum.elim_inl,Sum.elim_inr,
          Bool.false_eq_true,if_false,if_true,mul_one,mul_neg, mul_ite,mul_zero,score,w,t]
        ring
      simp_rw [hi]
      have hh := H w (fun i => hW (.inr i)) t
      simp only [D,Fintype.sum_sum_type,Fintype.sum_bool,Sum.elim_inl,Sum.elim_inr,
        Bool.false_eq_true,if_false,if_true,mul_one,mul_neg]
      dsimp [w,t] at hh
      linarith
    obtain ⟨p,hp,hd⟩ := (box_criterion M cap D hc).mpr hdual
    refine ⟨p,fun j => ⟨hp.1 j,hp.2 j⟩,?_,?_⟩
    · have h1 := hd (.inl false)
      have h2 := hd (.inl true)
      simp [M,D,mulVec,dotProduct] at h1 h2
      linarith
    · intro i
      simpa [M,D,mulVec,dotProduct,ite_mul] using hd (.inr i)
end OMA.S_mo_238612
namespace OMA.S_mo_238612
open Finset
private def exampleEvents (i : Fin 6) : Finset (Fin 6) :=
  univ.filter fun j => if j=0 then i=0 else i=j ∨ i.val=j.val%5+1

private def exampleDemand (i : Fin 6) : ℚ := if i=0 then 1/4 else 7/20

private lemma weird :
    ∃ (A : Fin 6→Finset (Fin 6)) (d : Fin 6→ℝ), (∀ i, 0 ≤ d i ∧ d i ≤ 1) ∧
      (∀ S : Finset (Fin 6), ∃ j : Fin 6, (∑ i ∈ S,d i) ≤ ∑ i ∈ S, (if j∈A i then (1:ℝ) else 0)) ∧
      ¬feasible A (fun _ => 1) d := by
  let d (i : Fin 6) : ℝ := (exampleDemand i:ℝ)
  have hw : ∀ S : Finset (Fin 6), ∃ j : Fin 6, (∑ i ∈ S,exampleDemand i) ≤
      ∑ i ∈ S, (if j∈exampleEvents i then (1:ℚ) else 0) := by decide +kernel
  refine ⟨exampleEvents,d,?_,?_,?_⟩
  · intro i
    have hh : ∀ j, 0 ≤ exampleDemand j ∧ exampleDemand j ≤ 1 := by decide +kernel
    dsimp [d]
    exact_mod_cast hh i
  · intro S
    obtain ⟨j,hj⟩ := hw S
    refine ⟨j,?_⟩
    dsimp [d]
    let v (i : Fin 6) : ℚ := if j∈exampleEvents i then 1 else 0
    change (∑ i ∈ S,exampleDemand i) ≤ ∑ i ∈ S,v i at hj
    have he : (∑ i ∈ S,(exampleDemand i:ℝ)) ≤ ∑ i ∈ S,(v i:ℝ) := by exact_mod_cast hj
    refine he.trans_eq (sum_congr rfl (fun i _ => ?_))
    by_cases h : j∈exampleEvents i <;> simp [v,h]
  · intro hf
    let w (i : Fin 6) : ℝ := if i=0 then 2 else 1
    have hx : ∀ j, score exampleEvents w j=2 := by
      intro j
      fin_cases j <;> norm_num [score,w,Fin.sum_univ_succ,exampleEvents] <;> norm_cast
    have hh := upper_score exampleEvents (fun _=>1) d hf w (fun i => by dsimp [w]; split <;> norm_num) 2
    simp only [hx,sub_self,max_self,mul_zero,sum_const_zero,add_zero] at hh
    norm_num [d,w,exampleDemand,Fin.sum_univ_succ] at hh
end OMA.S_mo_238612

theorem OMA.solution : type_of% @OMA.S_mo_238612.main :=
  ⟨fun _ _ A cap d hc => OMA.S_mo_238612.exact_criterion A cap d hc,OMA.S_mo_238612.weird⟩
