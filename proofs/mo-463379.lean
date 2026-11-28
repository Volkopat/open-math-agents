import OMAStatements.S_mo_463379

namespace OMA.S_mo_463379
open Matrix Finset
private lemma flux_sum {m} (w : M m) (hw : network w) (x : V m→ℝ) :
    (∑ i, ∑ j,w i j*(x i-x j))=0 := by
  have he : (∑ i,∑ j,w i j*(x i-x j)) = -(∑ i,∑ j,w i j*(x i-x j)) := by
    conv_rhs => rw [sum_comm]
    simp only [←Finset.sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hw.1 j i]
    ring
  linarith

private lemma network_mul {m} (w : M m) (x : V m→ℝ) (i : V m) :
    ((lap w+J m)*ᵥx) i=(∑ j,w i j*(x i-x j))+(m+1:ℝ)⁻¹*∑ j,x j := by
  rw [add_mulVec,Pi.add_apply,lap,sub_mulVec,Pi.sub_apply,mulVec_diagonal]
  simp only [mulVec,dotProduct,J,Finset.mul_sum,Finset.sum_mul,mul_sub,Finset.sum_sub_distrib]

private lemma network_constant {m} (w : M m) (hw : network w) (x : V m→ℝ)
    (hx : ∀ i,(∑ j,w i j*(x i-x j))=0) : ∃ c, ∀ i,x i=c := by
  obtain ⟨a,_,ha⟩ := Finset.exists_max_image univ x univ_nonempty
  let S := univ.filter (fun i => x i=x a)
  have hS : S.Nonempty := ⟨a,by simp [S]⟩
  have hb (i : V m) (hi : i∈S) (j : V m) (hj : j ∉ S) : w i j=0 := by
    have he : x i=x a := (mem_filter.mp hi).2
    have hj' : x j<x a := lt_of_le_of_ne (ha j (mem_univ _)) (by simpa [S] using hj)
    have hrow (l : V m) : 0≤w i l*(x i-x l) :=
      mul_nonneg (hw.2.1 _ _) (sub_nonneg.mpr (he ▸ ha l (mem_univ _)))
    have hz := (sum_eq_zero_iff_of_nonneg (fun l _ => hrow l)).mp (hx i) j (mem_univ _)
    exact (mul_eq_zero.mp hz).resolve_right (by linarith)
  have hall : S=univ := by
    by_contra hh
    have hn := hw.2.2 S hS hh
    have hzero : cut w S=0 := by
      apply sum_eq_zero
      intro i hi
      exact sum_eq_zero fun j hj => hb i hi j (mem_sdiff.mp hj).2
    linarith
  exact ⟨x a,fun i => (mem_filter.mp (show i∈S from hall ▸ mem_univ i)).2⟩

private lemma network_mass {m} (w : M m) (hw : network w) (x : V m→ℝ) :
    ∑ i, ((lap w+J m)*ᵥx) i = ∑ i,x i := by
  simp only [network_mul,sum_add_distrib,flux_sum w hw,zero_add,sum_const,
    card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  field_simp

private lemma network_unit {m} (w : M m) (hw : network w) : IsUnit (lap w+J m).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hd
  obtain ⟨x,hx,hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hsum := (network_mass w hw x).symm
  rw [hz] at hsum
  simp only [Pi.zero_apply,Finset.sum_const_zero] at hsum
  obtain ⟨c,hc⟩ := network_constant w hw x (fun i => by
    have e := congrFun hz i
    simpa [network_mul,hsum] using e)
  have hcz : c=0 := by
    simpa [hc,show (m:ℝ)+1≠0 by positivity] using hsum
  exact hx (funext fun i => (hc i).trans hcz)

lemma green_is_column {m} (w : M m) (hw : network w) (s : V m) :
    greenColumn w s (fun i => green w i s) := by
  let y (i : V m) := (lap w+J m)⁻¹ i s
  have he (i : V m) : ((lap w+J m)*ᵥy) i = if i=s then 1 else 0 := by
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv _ (network_unit w hw)) i) s
    simpa only [Matrix.mul_apply,Matrix.one_apply,Matrix.mulVec,dotProduct,y] using h
  have hs : (∑ j,y j)=1 := by rw [←network_mass w hw y]; simp [he]
  have hz (i : V m) : green w i s = y i-(m+1:ℝ)⁻¹ := rfl
  constructor
  · simp only [hz,Finset.sum_sub_distrib,hs,sum_const,card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    field_simp
    norm_num
  · intro i
    simp only [hz,sub_sub_sub_cancel_right]
    have e := he i
    rw [network_mul,hs,mul_one] at e
    linarith

lemma green_unique {m} (w : M m) (hw : network w) (s : V m) {x : V m→ℝ}
    (hx : greenColumn w s x) : x=(fun i => green w i s) := by
  have h := green_is_column w hw s
  apply Matrix.mulVec_injective_of_isUnit (A:=lap w+J m)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (network_unit w hw))
  funext i
  simp only [network_mul,hx.1,h.1,mul_zero,add_zero,hx.2 i,h.2 i]
end OMA.S_mo_463379

namespace OMA.S_mo_463379
open Matrix Finset
lemma green_penrose {m} (w : M m) (hw : network w) :
    lap w*green w*lap w=lap w ∧ green w*lap w*green w=green w ∧
    (lap w*green w).IsSymm ∧ (green w*lap w).IsSymm := by
  let L := lap w
  let B := J m
  let U := L+B
  have lj : L*B=0 := by
    ext i j
    change (((diagonal (fun i => ∑ j,w i j) - w)*J m):M m) i j=0
    rw [Matrix.sub_mul,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_apply]
    simp [J,← Finset.sum_mul]
  have jl : B*L=0 := by
    ext i j
    change ((J m*(diagonal (fun i => ∑ j,w i j) - w)):M m) i j=0
    rw [Matrix.mul_sub,Matrix.sub_apply,Matrix.mul_diagonal,Matrix.mul_apply]
    simp [J,← Finset.mul_sum,hw.1 j]
  have jj : B*B=B := by
    ext i j
    change (∑ _ : V m,(m+1:ℝ)⁻¹*(m+1:ℝ)⁻¹)=(m+1:ℝ)⁻¹
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    field_simp
  have hu : U⁻¹*U=1 := Matrix.nonsing_inv_mul _ (network_unit w hw)
  have hv : U*U⁻¹=1 := Matrix.mul_nonsing_inv _ (network_unit w hw)
  have ub : U*B=B := by change (L+B)*B=B; rw [Matrix.add_mul,lj,jj,zero_add]
  have bu : B*U=B := by change B*(L+B)=B; rw [Matrix.mul_add,jl,jj,zero_add]
  have ib : U⁻¹*B=B := by calc
    _ = U⁻¹*(U*B) := by rw [ub]
    _ = B := by rw [←Matrix.mul_assoc,hu,one_mul]
  have bi : B*U⁻¹=B := by calc
    _ = (B*U)*U⁻¹ := by rw [bu]
    _ = B := by rw [Matrix.mul_assoc,hv,mul_one]
  have el : L=U-B := by simp [U]
  have lp : L*(U⁻¹-B)=1-B := by rw [Matrix.mul_sub,lj,sub_zero,el,Matrix.sub_mul,hv,bi]
  have pl : (U⁻¹-B)*L=1-B := by rw [Matrix.sub_mul,jl,sub_zero,el,Matrix.mul_sub,hu,ib]
  have hsym : (1-B).IsSymm := by
    change ((1-B):M m).transpose=1-B
    rw [Matrix.transpose_sub,Matrix.transpose_one]
    rfl
  change L*(U⁻¹-B)*L=L ∧ (U⁻¹-B)*L*(U⁻¹-B)=U⁻¹-B ∧
    (L*(U⁻¹-B)).IsSymm ∧ ((U⁻¹-B)*L).IsSymm
  rw [lp,pl,Matrix.sub_mul,one_mul,jl,sub_zero,Matrix.sub_mul,one_mul,Matrix.mul_sub,bi,jj,
    sub_self,sub_zero]
  exact ⟨rfl,rfl,hsym,hsym⟩
end OMA.S_mo_463379

namespace OMA.S_mo_463379
open Finset
private lemma sum_gaps {m : ℕ} (x : V m → ℝ) (h : (∑ i,x i)=0) :
    (∑ t : Fin m, ((m:ℝ)-t.val)*(x t.castSucc-x t.succ))=(m+1:ℝ)*x 0 ∧
    (∑ t : Fin m, ((t.val:ℝ)+1)*(x t.castSucc-x t.succ))= -(m+1:ℝ)*x (Fin.last m) := by
  have tel (f : V m → ℝ) : (∑ t : Fin m, (f t.castSucc-f t.succ))=f 0-f (Fin.last m) := by
    rw [sum_sub_distrib]
    have h1 := Fin.sum_univ_castSucc f
    have h2 := Fin.sum_univ_succ f
    linarith
  have h1 := tel (fun i => ((m:ℝ)-i.val)*x i)
  have h2 := tel (fun i => (i.val:ℝ)*x i)
  simp only [Fin.val_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one,Fin.val_zero,Nat.cast_zero,
    Fin.val_last,sub_self,zero_mul,sub_zero] at h1 h2
  have e1 := Fin.sum_univ_succ x
  have e2 := Fin.sum_univ_castSucc x
  constructor
  · calc _ = (∑ t : Fin m, (((m:ℝ)-t.val)*x t.castSucc -
              ((m:ℝ)-(t.val+1))*x t.succ)) - ∑ t : Fin m,x t.succ := by
                rw [←sum_sub_distrib]
                apply sum_congr rfl; intro t _; ring
         _ = _ := by linarith
  · calc _ = (∑ t : Fin m, ((t.val:ℝ)*x t.castSucc -
              ((t.val:ℝ)+1)*x t.succ)) + ∑ t : Fin m,x t.castSucc := by
                rw [←sum_add_distrib]
                apply sum_congr rfl; intro t _; ring
         _ = _ := by linarith
end OMA.S_mo_463379

namespace OMA.S_mo_463379
open Finset
private lemma flow_bound {m : ℕ} (w : M m) (hs : ∀ i j,w i j=w j i)
    {s : V m} {x : V m → ℝ} (hx : greenColumn w s x) (S : Finset (V m)) :
    (∑ i ∈ S,∑ j ∈ univ \ S,w i j*(x i-x j)) ≤ 1-(S.card:ℝ)/(m+1:ℝ) := by
  classical
  let F (i j : V m) := w i j*(x i-x j)
  have hn (i j) : F j i = -F i j := by dsimp [F]; rw [hs j i]; ring
  have hswap := sum_comm (s:=S) (t:=S) (f:=F)
  have hneg : (∑ j ∈ S,∑ i ∈ S,F i j) = -(∑ i ∈ S,∑ j ∈ S,F i j) := by
    simp only [←sum_neg_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => hn i j
  have hz : (∑ i ∈ S,∑ j ∈ S,F i j)=0 := by linarith
  have hrow (i : V m) : (∑ j ∈ S,F i j)+(∑ j ∈ univ \ S,F i j)=
      (if i=s then 1 else 0)-(m+1:ℝ)⁻¹ := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ S)]
    have h := hx.2 i
    change (∑ j,F i j)=_ at h
    linarith
  have h := sum_congr (s₁:=S) rfl (fun i _ => hrow i)
  rw [sum_add_distrib,hz,zero_add,sum_sub_distrib] at h
  change (∑ i ∈ S,∑ j ∈ univ \ S,F i j) ≤ _
  rw [h]
  simp only [sum_const,nsmul_eq_mul,div_eq_mul_inv]
  apply sub_le_sub_right
  by_cases he : s∈S <;> simp [he]
private lemma sorted_gaps {m : ℕ} (w : M m) (hw : network w) (c : Fin m → ℝ) (hc : profile w c)
    {s : V m} {x : V m → ℝ} (hx : greenColumn w s x) (σ : Equiv.Perm (V m))
    (hm : Antitone (x ∘ σ)) (t : Fin m) :
    x (σ t.castSucc)-x (σ t.succ) ≤ ((m:ℝ)-t.val)/((m+1:ℝ)*c t) := by
  classical
  let S := (Iic t.castSucc).map σ.toEmbedding
  have hS : S.card=t.val+1 := by simp [S,Fin.card_Iic]
  let δ := x (σ t.castSucc)-x (σ t.succ)
  have hδ : 0≤δ := sub_nonneg.mpr (hm (Fin.castSucc_le_succ t))
  have his (i : V m) : i∈S ↔ σ.symm i≤t.castSucc := by
    change i∈(Iic t.castSucc).map σ.toEmbedding ↔ _
    simp
  have hcross (i) (hi : i∈S) (j) (hj : j∈univ \ S) : δ≤x i-x j := by
    have h₁ := hm ((his i).mp hi)
    have hj' := (his j).not.mp (mem_sdiff.mp hj).2
    have h₂ := hm (show t.succ ≤ σ.symm j by
      change t.val+1 ≤ (σ.symm j).val
      exact Nat.succ_le_of_lt (lt_of_not_ge hj'))
    simpa [δ,Function.comp_def] using sub_le_sub h₁ h₂
  have hflow := flow_bound w hw.1 hx S
  have hbound : δ*c t≤1-(S.card:ℝ)/(m+1:ℝ) := by
    calc δ*c t ≤ δ*cut w S := mul_le_mul_of_nonneg_left ((hc t).2 S hS) hδ
         _ ≤ ∑ i ∈ S,∑ j ∈ univ \ S,w i j*(x i-x j) := by
           simp only [cut,mul_sum]
           exact sum_le_sum fun i hi => sum_le_sum fun j hj =>
             (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left (hcross i hi j hj) (hw.2.1 i j))
         _ ≤ _ := hflow
  rw [hS] at hbound
  change δ≤_
  apply (le_div_iff₀ (mul_pos (by positivity) (hc t).1)).mpr
  have h := (mul_le_mul_iff_of_pos_right (show 0<(m+1:ℝ) by positivity)).mpr hbound
  field_simp at h ⊢
  push_cast at h
  nlinarith
end OMA.S_mo_463379

namespace OMA.S_mo_463379
open Finset
lemma column_bound {m : ℕ} (w : M m) (hw : network w) (c : Fin m → ℝ) (hc : profile w c)
    (s : V m) (x : V m → ℝ) (hx : greenColumn w s x) (i : V m) :
    -lowerMag c ≤ x i ∧ x i ≤ upper c := by
  let σ := Tuple.sort (fun j => -x j)
  let f := x ∘ σ
  have hm : Antitone f := by
    intro a b h
    have e := Tuple.monotone_sort (fun j => -x j) h
    exact neg_le_neg_iff.mp e
  have hsum : (∑ j,f j)=0 := (Equiv.sum_comp σ x).trans hx.1
  obtain ⟨h₁,h₂⟩ := sum_gaps f hsum
  let N : ℝ := m+1
  have hn : 0<N := by dsimp [N]; positivity
  have h (t : Fin m) : N*(f t.castSucc-f t.succ) ≤ ((m:ℝ)-t.val)/c t := by
    have hd := (le_div_iff₀ (mul_pos hn (hc t).1)).mp (sorted_gaps w hw c hc hx σ hm t)
    apply (le_div_iff₀ (hc t).1).mpr
    change N*(x (σ t.castSucc)-x (σ t.succ))*c t ≤ _
    nlinarith only [hd]
  have weighted (a : Fin m → ℝ) (ha : ∀ t,0≤a t) :
      N*(∑ t : Fin m,a t*(f t.castSucc-f t.succ)) ≤
        ∑ t : Fin m,(a t*((m:ℝ)-t.val))/c t := by
    rw [mul_sum]
    exact sum_le_sum fun t _ => by
      calc _ = a t*(N*(f t.castSucc-f t.succ)) := by ring
           _ ≤ a t*(((m:ℝ)-t.val)/c t) := mul_le_mul_of_nonneg_left (h t) (ha t)
           _ = _ := by ring
  have hu := weighted (fun t => (m:ℝ)-t.val)
    (fun t => by exact sub_nonneg.mpr (by exact_mod_cast t.isLt.le))
  have hl := weighted (fun t => (t.val:ℝ)+1) (fun t => by positivity)
  rw [h₁] at hu
  rw [h₂] at hl
  have hlo : f (Fin.last m) ≤ x i := by simpa [f] using hm (Fin.le_last (σ.symm i))
  have hup : x i ≤ f 0 := by simpa [f] using hm (Fin.zero_le (σ.symm i))
  constructor
  · have hlow : -f (Fin.last m)≤lowerMag c := by
      change -f (Fin.last m)≤(∑ t : Fin m, _)/N^2
      apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
      change N*(-N*f (Fin.last m)) ≤ _ at hl
      nlinarith only [hl]
    linarith
  · apply hup.trans
    change f 0≤(∑ t : Fin m, _)/N^2
    apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
    simp only [←sq] at hu
    change N*(N*f 0) ≤ _ at hu
    nlinarith only [hu]
end OMA.S_mo_463379

namespace OMA.S_mo_463379
open Finset
lemma spectral_bound {m : ℕ} (w : M m) (s i : V m) (x : V m → ℝ)
    (hx : greenColumn w s x) (l : ℝ) (hl : 0<l) (hs : spectralLower w l) :
    |x i| ≤ (m:ℝ)/((m+1)*l) := by
  classical
  let Q := ∑ k,x k^2
  let a : ℝ := m/(m+1)
  have hQ : 0≤Q := sum_nonneg fun _ _ => sq_nonneg _
  have ha : 0≤a := by dsimp [a]; positivity
  have hn : 0<(m+1:ℝ) := by positivity
  have hd (k : V m) : x k^2 ≤ a*Q := by
    have h := sum_mul_sq_le_sq_mul_sq (univ.erase k) (fun _ => (1:ℝ)) x
    have h₁ := sum_erase_add (univ:Finset (V m)) x (mem_univ k)
    have h₂ := sum_erase_add (univ:Finset (V m)) (fun j => x j^2) (mem_univ k)
    rw [hx.1] at h₁
    have h₃ : (∑ j ∈ univ.erase k,x j)= -x k := by linarith
    have hc : (univ.erase k).card=m := by simp
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,hc,h₃,neg_sq] at h
    change (∑ j ∈ univ.erase k,x j^2)+x k^2=Q at h₂
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hn).mpr
    nlinarith only [h,congrArg (fun b : ℝ => (m:ℝ)*b) h₂]
  have he := hs x hx.1
  simp_rw [hx.2,mul_sub,mul_ite,mul_one,mul_zero] at he
  simp only [sum_sub_distrib,sum_ite_eq',mem_univ,if_true,←sum_mul,hx.1,zero_mul,sub_zero] at he
  change l*Q≤x s at he
  have hsq : l^2*Q≤a := by
    rcases hQ.eq_or_lt with h0|hq
    · simpa [←h0] using ha
    · have h₁ := sq_le_sq' (by linarith [mul_nonneg hl.le hQ] : -(x s)≤l*Q) he
      apply (mul_le_mul_iff_of_pos_right hq).mp
      nlinarith only [h₁,hd s]
  have hxi : (l*|x i|)^2 ≤ a^2 := by
    have h1 := mul_le_mul_of_nonneg_left (hd i) (sq_nonneg l)
    have h2 := mul_le_mul_of_nonneg_left hsq ha
    rw [mul_pow,sq_abs]
    nlinarith only [h1,h2]
  have hfinal : l*|x i|≤a := (sq_le_sq₀ (mul_nonneg hl.le (abs_nonneg _)) ha).mp hxi
  rw [←div_div]
  exact (le_div_iff₀ hl).mpr (by simpa only [mul_comm] using hfinal)
end OMA.S_mo_463379

namespace OMA.S_mo_463379
open Finset
lemma constant_profile_values (m : ℕ) (a : ℝ) (ha : 0<a) :
    upper (fun _ : Fin m => a) = (m:ℝ)*(2*m+1)/(6*(m+1)*a) ∧
    lowerMag (fun _ : Fin m => a) = (m:ℝ)*(m+2)/(6*(m+1)*a) := by
  have h₁ (n : ℕ) : (∑ i : Fin n,(i.val:ℝ))=(n:ℝ)*(n-1)/2 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Fin.sum_univ_castSucc]; simp [ih]; ring
  have h₂ (n : ℕ) : (∑ i : Fin n,(i.val:ℝ)^2)=(n:ℝ)*(n-1)*(2*n-1)/6 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Fin.sum_univ_castSucc]; simp [ih]; ring
  have hU (i : Fin m) : ((m:ℝ)-i.val)^2=(m:ℝ)^2-(2*m)*(i.val:ℝ)+(i.val:ℝ)^2 := by ring
  have hL (i : Fin m) : ((i.val:ℝ)+1)*((m:ℝ)-i.val)=((m:ℝ)-1)*(i.val:ℝ)+m-(i.val:ℝ)^2 := by ring
  have hn : (m:ℝ)+1≠0 := by positivity
  constructor <;>
    simp only [upper,lowerMag,←sum_div,hU,hL,sum_add_distrib,sum_sub_distrib,←mul_sum,
      sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,h₁,h₂] <;>
    field_simp [ne_of_gt ha,hn] <;> ring
end OMA.S_mo_463379

namespace OMA.S_mo_463379
open Finset
lemma path_network (m : ℕ) : network (pathWeight m) ∧ profile (pathWeight m) (fun _ => 1) := by
  classical
  have nonneg (i j : V m) : 0≤pathWeight m i j := by simp [pathWeight]; split <;> norm_num
  have one (S : Finset (V m)) (hne : S.Nonempty) (hproper : S≠univ) : 1≤cut (pathWeight m) S := by
    obtain ⟨i,hi,j,hj,he⟩ : ∃ i∈S,∃ j∈univ \ S,pathWeight m i j=1 := by
      by_contra! h
      have same (t : Fin m) : t.castSucc∈S ↔ t.succ∈S := by
        constructor
        · intro ht
          by_contra hn
          exact h _ ht _ (mem_sdiff.mpr ⟨mem_univ _,hn⟩) (by simp [pathWeight])
        · intro ht
          by_contra hn
          exact h _ ht _ (mem_sdiff.mpr ⟨mem_univ _,hn⟩) (by simp [pathWeight])
      have allmem (i : V m) : i∈S ↔ 0∈S := by
        induction i using Fin.induction with
        | zero => rfl
        | succ t ih => exact (same t).symm.trans ih
      obtain ⟨i,hi⟩ := hne
      exact hproper (eq_univ_of_forall (fun j => (allmem j).mpr ((allmem i).mp hi)))
    rw [←he]
    exact (single_le_sum (fun j _ => nonneg i j) hj).trans (single_le_sum
      (f:=fun i => ∑ j ∈ univ \ S,pathWeight m i j) (fun i _ => sum_nonneg (fun j _ => nonneg i j)) hi)
  refine ⟨⟨fun i j => by simp only [pathWeight,or_comm],nonneg,fun S h h' => zero_lt_one.trans_le (one S h h')⟩,?_⟩
  intro t
  refine ⟨by norm_num,?_⟩
  intro S hS
  apply one
  · exact card_pos.mp (hS ▸ Nat.zero_lt_succ _)
  · intro he
    rw [he,card_univ,Fintype.card_fin] at hS
    omega
end OMA.S_mo_463379

namespace OMA.S_mo_463379
open Finset

lemma path_column (m : ℕ) : ∃ x : V m → ℝ, greenColumn (pathWeight m) 0 x ∧
    x 0=upper (fun _ : Fin m => (1:ℝ)) ∧ x (Fin.last m)= -lowerMag (fun _ : Fin m => (1:ℝ)) := by
  classical
  let N : ℝ := (m:ℝ)+1
  let a (t : Fin m) := (m:ℝ)-t.val
  let b (t : Fin m) := (t.val:ℝ)+1
  let c (i : V m) (t : Fin m) := if i.val ≤ t.val then a t else -b t
  let x (i : V m) := (∑ t : Fin m, c i t*a t)/N^2
  have hn : 0 < N := by dsimp [N];positivity
  have hcent (t : Fin m) : ∑ i : V m,c i t=0 := by
    let S := univ.filter (fun i : V m => i.val ≤ t.val)
    have hs : S.card=t.val+1 := by
      have e : S=univ.filter (fun i : Fin (m+1) => i.val < t.val+1) := by
        ext i; simp [S]
      rw [e,Fin.card_filter_val_lt,min_eq_right (by omega)]
    have hcs : Sᶜ.card=m-t.val := by
      rw [Finset.card_compl,hs,Fintype.card_fin];omega
    have e (i : V m) : c i t=(if i∈S then a t else 0)+(if i∈Sᶜ then -b t else 0) := by
      by_cases h : i.val ≤ t.val <;> simp [c,S,h]
    simp only [e,Finset.sum_add_distrib,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,
      nsmul_eq_mul,hs,hcs]
    rw [Nat.cast_sub (show t.val ≤ m by omega),Nat.cast_add,Nat.cast_one]
    dsimp [a,b]
    ring
  have hgap (i j : V m) (h : i.val+1=j.val) :
      x i-x j=((m:ℝ)-i.val)/N := by
    let u : Fin m := ⟨i.val,by omega⟩
    have he (t : Fin m) : c i t*a t-c j t*a t=if t=u then N*a u else 0 := by
      by_cases htu : t=u
      · subst t
        have h1 : i.val ≤ u.val := le_rfl
        have h2 : ¬j.val ≤ u.val := by dsimp [u];omega
        simp only [c,h1,h2,if_pos,if_false]
        change ((m:ℝ)-↑i.val)*_ -(-((i.val:ℝ)+1))*_ = ((m:ℝ)+1)*_
        ring
      · have ht : t.val≠i.val := fun hh => htu (Fin.ext hh)
        have hequiv : (i.val ≤ t.val) ↔ (j.val ≤ t.val) := by omega
        simp [c,hequiv,htu]
    simp only [x, ← sub_div, ← Finset.sum_sub_distrib, he, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    change N*((m:ℝ)-i.val)/N^2=_
    field_simp
  let g (i : V m) := ((m:ℝ)-i.val)/N
  have hterm (i j : V m) : pathWeight m i j*(x i-x j)=
      (if i.val+1=j.val then g i else 0) - (if j.val+1=i.val then g j else 0) := by
    by_cases h : i.val+1=j.val
    · have h' : ¬j.val+1=i.val := by omega
      simp [pathWeight,h,h',hgap i j h,g]
    by_cases h' : j.val+1=i.val
    · have hg := hgap j i h'
      simp [pathWeight,h,h',g]
      linarith
    · simp [pathWeight,h,h']
  have hout (i : V m) : (∑ j : V m,if i.val+1=j.val then g i else 0) = g i := by
    by_cases hi : i.val < m
    · let j : V m:=⟨i.val+1,by omega⟩
      have eq (k : V m) : (i.val+1=k.val) ↔ k=j := by
        constructor
        · intro h;exact Fin.ext h.symm
        · rintro rfl;rfl
      simp [eq]
    · have hh : g i=0 := by
        have e : i.val=m := by omega
        simp [g,e]
      simp [hh]
  have hin (i : V m) : (∑ j : V m,if j.val+1=i.val then g j else 0) =
      if i=0 then 0 else ((m:ℝ)-(i.val:ℝ)+1)/N := by
    by_cases hi : i=0
    · simp [hi]
    · have hi' : 0 < i.val := by
        by_contra! hh
        exact hi (Fin.ext (show i.val=0 by omega))
      let j : V m:=⟨i.val-1,by omega⟩
      have eq (k : V m) : (k.val+1=i.val) ↔ k=j := by
        constructor
        · intro h;apply Fin.ext;change k.val=i.val-1;omega
        · rintro rfl;change i.val-1+1=i.val;omega
      simp only [eq,Finset.sum_ite_eq',Finset.mem_univ,if_true,if_neg hi]
      change ((m:ℝ)-↑(i.val-1))/N=_
      rw [Nat.cast_sub (show 1 ≤ i.val by omega),Nat.cast_one]
      ring
  refine ⟨x,⟨?_,?_⟩,?_,?_⟩
  · dsimp only [x]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hcent,zero_mul]
    simp
  · intro i
    simp only [hterm,Finset.sum_sub_distrib,hout,hin]
    by_cases h : i=0
    · simp [h,g,N]
      field_simp
      ring
    · simp only [if_neg h,zero_sub,g,N]
      ring_nf
  · simp [x,c,a,N,upper,sq]
  · have h (t : Fin m) : ¬(Fin.last m).val ≤ t.val := by simp
    have eq (t : Fin m) : c (Fin.last m) t * a t = -(b t*a t) := by
      rw [show c (Fin.last m) t = -b t from if_neg (h t),neg_mul]
    simp only [x,eq,Finset.sum_neg_distrib,neg_div,lowerMag,div_one,b,a,N]
end OMA.S_mo_463379

open OMA.S_mo_463379
theorem OMA.solution : type_of% @OMA.S_mo_463379.main := by
  refine ⟨?_,constant_profile_values,?_⟩
  · intro m w h
    exact ⟨green_penrose w h,fun c hc i j => column_bound w h c hc j _ (green_is_column w h j) i,
      fun l hl hs i j => spectral_bound w j i _ (green_is_column w h j) l hl hs⟩
  · intro m
    obtain ⟨hn,hp⟩ := path_network m
    obtain ⟨x,hx,h₁,h₂⟩ := path_column m
    rw [green_unique _ hn 0 hx] at h₁ h₂
    exact ⟨hn,hp,h₁,h₂⟩
