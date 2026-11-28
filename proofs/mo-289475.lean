import OMAStatements.S_mo_289475

namespace OMA.S_mo_289475
open Matrix Finset

private abbrev form {n : ℕ} (A : Mat n) (x y : Vec n) := x ⬝ᵥ (A *ᵥ y)

private lemma select_apply {n : ℕ} (i j : Fin n) (x : Vec n) :
    selectPair i j *ᵥ x = ![x i,x j] := by
  ext1 t
  have h : (selectPair i j *ᵥ x) t=x (vertices i j t) := by
    change ∑ k, (if vertices i j t = k then (1:ℝ) else 0)*x k = _
    simp only [ite_mul,one_mul,zero_mul,sum_ite_eq,mem_univ,if_true]
  rw [h]
  fin_cases t <;> rfl

private lemma pair_pd {n : ℕ} {A : Mat n} (ha : A.PosDef) {i j : Fin n} (hij : j≠i) :
    (principal A i j).PosDef := by
  apply ha.submatrix
  intro p q h
  fin_cases p <;> fin_cases q <;> simp_all [vertices]

private lemma pair_form {n : ℕ} (A : Mat n) (i j : Fin n) (x y : Vec n) :
    form (liftInv A i j) x y =
      ![x i,x j] ⬝ᵥ ((principal A i j)⁻¹ *ᵥ ![y i,y j]) := by
  simp only [form,liftInv,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,
    select_apply]

private lemma square_pair (C : Mat 2) (hC : C.PosDef) (x y : Vec 2) :
    0 ≤ form C⁻¹ x x - 2*(x ⬝ᵥ y) + form C y y := by
  have h := hC.posSemidef.dotProduct_mulVec_nonneg (C⁻¹ *ᵥ x-y)
  simp only [star_trivial,Matrix.mulVec_sub,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (C.isUnit_iff_isUnit_det.mp hC.isUnit),Matrix.one_mulVec,
    sub_dotProduct,dotProduct_sub] at h
  have he : (C⁻¹ *ᵥ x) ⬝ᵥ (C *ᵥ y)=x ⬝ᵥ y := by
    rw [dotProduct_comm,←Matrix.dotProduct_transpose_mulVec,show C⁻¹ᵀ=C⁻¹ from hC.inv.1,Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (C.isUnit_iff_isUnit_det.mp hC.isUnit),Matrix.one_mulVec]
  rw [he,dotProduct_comm (C⁻¹ *ᵥ x) x,dotProduct_comm y x] at h
  dsimp [form]
  linarith

private lemma sum_pairs_diag {n : ℕ} (hn : 2≤n) (f : Fin n→ℝ) :
    (∑ i,∑ j ∈ univ.erase i,(f i+f j))= (2*((n:ℝ)-1))*∑ i,f i := by
  have hcard (i : Fin n) : ((univ.erase i).card : ℝ) = (n:ℝ)-1 := by
    rw [card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin,Nat.cast_sub (by omega)]
    simp
  have hj (i : Fin n) : ∑ j ∈ univ.erase i,f j=(∑ j,f j)-f i := by
    exact eq_sub_of_add_eq (sum_erase_add _ f (mem_univ i))
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,hcard,hj,sum_sub_distrib,card_univ,Fintype.card_fin,
    ←Finset.mul_sum]
  ring

private lemma sum_pairs_cross {n : ℕ} (f : Fin n→Fin n→ℝ) :
    (∑ i,∑ j ∈ univ.erase i,(f i j+f j i))=2*((∑ i,∑ j,f i j)-∑ i,f i i) := by
  have h1 (i : Fin n) : ∑ j ∈ univ.erase i,f i j = (∑ j,f i j)-f i i :=
    eq_sub_of_add_eq (sum_erase_add _ _ (mem_univ i))
  have h2 (i : Fin n) : ∑ j ∈ univ.erase i,f j i = (∑ j,f j i)-f i i :=
    eq_sub_of_add_eq (sum_erase_add _ _ (mem_univ i))
  simp only [sum_add_distrib,h1,h2,sum_sub_distrib]
  rw [Finset.sum_comm (f:=fun i j => f j i)]
  ring

private lemma average_quadratic {n : ℕ} (hn : 2≤n) (A : Mat n) (ha : A.PosDef) (x y : Vec n) :
    0 ≤ form (pairAverage A) x x - 2*(x ⬝ᵥ y) +
      (((n:ℝ)-2)*form (diagPart A) y y + form A y y)/((n:ℝ)-1) := by
  have hh (i j : Fin n) (hij : j≠i) := square_pair _ (pair_pd ha hij) ![x i,x j] ![y i,y j]
  have he (i j : Fin n) (hij : j≠i) : 0≤
      form (liftInv A i j) x x - 2*(x i*y i+x j*y j) +
      ((y i*A i i*y i+y j*A j j*y j)+(y i*A i j*y j+y j*A j i*y i)) := by
    have h := hh i j hij
    rw [pair_form]
    change 0≤_ at h
    simp only [form,Matrix.mulVec,dotProduct,Fin.sum_univ_two,principal,Matrix.submatrix_apply,vertices,
      Matrix.cons_val_zero,Matrix.cons_val_one] at h ⊢
    linarith only [h]
  have H := sum_nonneg (s:=univ) (fun i _ =>
    sum_nonneg (s:=univ.erase i) (fun j hj => he i j (mem_erase.mp hj).1))
  let d (i j : Fin n) := x i*y i+x j*y j
  let e (i j : Fin n) := y i*A i i*y i+y j*A j j*y j
  let g (i j : Fin n) := y i*A i j*y j+y j*A j i*y i
  change 0 ≤ ∑ i, ∑ j ∈ univ.erase i, (form (liftInv A i j) x x - 2*d i j + (e i j+g i j)) at H
  simp only [sum_add_distrib,sum_sub_distrib,←Finset.mul_sum] at H
  have dd : ∑ i,∑ j ∈ univ.erase i,d i j = _ := sum_pairs_diag hn (fun i=>x i*y i)
  have ee : ∑ i,∑ j ∈ univ.erase i,e i j = _ := sum_pairs_diag hn (fun i=>y i*A i i*y i)
  have gg : ∑ i,∑ j ∈ univ.erase i,g i j = _ := sum_pairs_cross (fun i j=>y i*A i j*y j)
  rw [dd,ee,gg] at H
  have hA : (∑ i,∑ j,y i*A i j*y j)=form A y y := by simp [form,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
  have hD : (∑ i,y i*A i i*y i)=form (diagPart A) y y := by simp [form,diagPart,mulVec_diagonal,dotProduct,mul_assoc]
  have hB : form (pairAverage A) x x = (2*((n:ℝ)-1))⁻¹ * ∑ i, ∑ j ∈ univ.erase i, form (liftInv A i j) x x := by
    simp only [pairAverage,form,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,Matrix.sum_mulVec,dotProduct_sum]
  rw [hA,hD] at H
  rw [hB]
  have hn' : 1<(n:ℝ) := by exact_mod_cast (show 1<n by omega)
  apply nonneg_of_mul_nonneg_left (b := 2*((n:ℝ)-1)) _ (by linarith)
  convert H using 1
  · rfl
  · change ((_ - 2*(∑ i,x i*y i) + _)*_ : ℝ)=_
    field_simp [show (n:ℝ)-1 ≠ 0 by linarith]
    ring
end OMA.S_mo_289475

namespace OMA.S_mo_289475
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.L2Operator

private lemma cyclic_spec {n : ℕ} (A B : Mat n) : spectrum ℝ (A*B)=spectrum ℝ (B*A) := by
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Matrix.mem_spectrum_iff_isRoot_charpoly,Matrix.charpoly_mul_comm]

private lemma shifted_nonneg {n : ℕ} (A : Mat n) (ha : A.IsHermitian) (t : ℝ)
    (hb : ∀ z ∈ spectrum ℝ A, t ≤ z) : (A-t • (1:Mat n)).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ) _ (ha.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t)))).mpr
  intro z hz
  have he : z+t ∈ spectrum ℝ A := by
    rw [spectrum.mem_iff,Algebra.algebraMap_eq_smul_one,add_smul]
    rwa [spectrum.mem_iff,Algebra.algebraMap_eq_smul_one,sub_sub_eq_add_sub] at hz
  linarith [hb _ he]

private lemma min_product {n : ℕ} [Nonempty (Fin n)] (A D : Mat n) (ha : A.IsHermitian) (hd : D.PosDef) :
    ∃ l : ℝ, IsLeast (spectrum ℝ (D⁻¹*A)) l ∧ (A - l • D).PosSemidef := by
  let T := CFC.sqrt D
  have ht : T.PosSemidef := (CFC.sqrt_nonneg D).posSemidef
  have hT : T*T=D := CFC.sqrt_mul_sqrt_self D hd.posSemidef.nonneg
  have hu : IsUnit T := (CFC.isUnit_sqrt_iff D hd.posSemidef.nonneg).mpr hd.isUnit
  have hi := T.isUnit_iff_isUnit_det.mp hu
  let C := T⁻¹*A*T⁻¹
  have hs : C.IsHermitian := by
    have he := isHermitian_mul_mul_conjTranspose T⁻¹ ha
    simpa only [ht.inv.1.eq] using he
  have hspec : spectrum ℝ C = spectrum ℝ (D⁻¹*A) := by
    rw [show C = (T⁻¹*A)*T⁻¹ from rfl,cyclic_spec,← Matrix.mul_assoc,← Matrix.mul_inv_rev T T, hT]
  obtain ⟨l,hl⟩ : ∃ l, IsLeast (spectrum ℝ C) l := by
    rw [hs.spectrum_real_eq_range_eigenvalues]
    let s := univ.image hs.eigenvalues
    have he : (s : Set ℝ) = Set.range hs.eigenvalues := by simp [s]
    have hs' : s.Nonempty := univ_nonempty.image _
    exact ⟨s.min' hs',he ▸ Finset.isLeast_min' _ _⟩
  have hc := shifted_nonneg C hs l hl.2
  have hcon := hc.mul_mul_conjTranspose_same T
  rw [ht.1.eq,mul_sub,sub_mul, Matrix.mul_smul,Matrix.mul_one, Matrix.smul_mul,hT] at hcon
  have hc' : T*C*T=A := by
    change T*(T⁻¹*A*T⁻¹)*T=A
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hi,one_mul,
      Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hi,mul_one]
  rw [hc'] at hcon
  exact ⟨l,hspec ▸ hl,hcon⟩

private lemma spectral_vec {n : ℕ} {A : Mat n} {z : ℝ} (hz : z∈spectrum ℝ A) :
    ∃ v : Vec n, v≠0 ∧ A *ᵥ v=z • v := by
  rw [←Matrix.spectrum_toLin'] at hz
  obtain ⟨v,hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  exact ⟨v,hv.2,Module.End.mem_eigenspace_iff.mp hv.1⟩

private lemma spectral_of_vec {n : ℕ} (A : Mat n) (v : Vec n) (hv : v≠0) (z : ℝ) (hz : A*ᵥv=z•v) :
    z∈spectrum ℝ A := by
  rw [←Matrix.spectrum_toLin',←Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector (show Module.End.HasEigenvector A.toLin' z v from
    ⟨Module.End.mem_eigenspace_iff.mpr hz,hv⟩)

end OMA.S_mo_289475

namespace OMA.S_mo_289475
open Matrix Finset

private lemma dia_pd {n : ℕ} {A : Mat n} (ha : A.PosDef) : (diagPart A).PosDef :=
  Matrix.PosDef.diagonal (fun _ => ha.diag_pos)

private lemma average_herm {n : ℕ} (A : Mat n) (ha : A.PosDef) : (pairAverage A).IsHermitian := by
  have hp (i j : Fin n) (hij : j≠i) : (liftInv A i j).PosSemidef := by
    have h := (pair_pd ha hij).inv.posSemidef.conjTranspose_mul_mul_same (selectPair i j)
    exact h
  have hs : (∑ i,∑ j ∈ univ.erase i,liftInv A i j).PosSemidef :=
    Matrix.posSemidef_sum _ (fun i _ => Matrix.posSemidef_sum _ (fun j hj => hp i j (mem_erase.mp hj).1))
  exact hs.1.smul (IsSelfAdjoint.all _)

private lemma lower_pair {n : ℕ} (hn : 2≤n) (A : Mat n) (ha : A.PosDef) {l : ℝ} (hl : 0<l)
    (hD : (A-l • diagPart A).PosSemidef) :
    ∀ z ∈ spectrum ℝ (pairAverage A*A), sharp n l ≤ z := by
  intro z hz
  obtain ⟨v,hv,he⟩ := spectral_vec hz
  let x := A *ᵥ v
  let m := sharp n l
  have hq : 0 < v ⬝ᵥ x := by simpa only [star_trivial] using ha.dotProduct_mulVec_pos hv
  have hpd := hD.dotProduct_mulVec_nonneg v
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul] at hpd
  have hc := average_quadratic hn A ha x (m • v)
  have he' : pairAverage A*ᵥx=z•v := by rw [←Matrix.mulVec_mulVec] at he; exact he
  simp only [form,he',dotProduct_smul,Matrix.mulVec_smul,smul_dotProduct,smul_eq_mul] at hc
  rw [dotProduct_comm x v] at hc
  change 0 ≤ z*(v⬝ᵥx)-2*(m*(v⬝ᵥx))+
    ((n-2:ℝ)*(m*(m*form (diagPart A) v v)) + m*(m*(v⬝ᵥx)))/(n-1:ℝ) at hc
  change 0 ≤ v⬝ᵥx-l*form (diagPart A) v v at hpd
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hden : 0<(n:ℝ)-2+l := by linarith
  have hm : 0 < m := div_pos (mul_pos (by linarith) hl) hden
  have hmrel : m*((n:ℝ)-2+l)=((n:ℝ)-1)*l := by
    dsimp [m,sharp]
    field_simp
  have hbound : ((n-2:ℝ)*(m*(m*form (diagPart A) v v))+m*(m*(v⬝ᵥx)))/(n-1:ℝ) ≤ m*(v⬝ᵥx) := by
    apply (div_le_iff₀ (by linarith : 0 < (n:ℝ)-1)).mpr
    apply (mul_le_mul_iff_of_pos_right hl).mp
    have hp := mul_nonneg (mul_nonneg (sub_nonneg.mpr hn') (sq_nonneg m)) hpd
    nlinarith only [hp, congrArg (fun w : ℝ => w*m*(v⬝ᵥx)) hmrel]
  change m ≤ z
  apply (mul_le_mul_iff_of_pos_right hq).mp
  linarith only [hc,hbound]

private lemma main_lower (n : ℕ) (hn : 2≤n) (A : Mat n) (ha : A.PosDef) :
    ∃ l m : ℝ, IsLeast (spectrum ℝ ((diagPart A)⁻¹*A)) l ∧
      IsLeast (spectrum ℝ (pairAverage A*A)) m ∧ 0<l ∧ l≤1 ∧ l ≤ sharp n l ∧ sharp n l ≤ m := by
  let i : Fin n := ⟨0,by omega⟩
  let _ : Nonempty (Fin n) := ⟨i⟩
  let D := diagPart A
  have hd := dia_pd ha
  obtain ⟨l,hs,hL⟩ := min_product A D ha.1 hd
  obtain ⟨m,hm,_⟩ := min_product (pairAverage A) A⁻¹ (average_herm A ha) ha.inv
  rw [Matrix.nonsing_inv_nonsing_inv _ (A.isUnit_iff_isUnit_det.mp ha.isUnit),cyclic_spec] at hm
  have h1 : 0 ≤ (A-l • D) i i := hL.diag_nonneg
  change 0≤ A i i - l * (diagPart A) i i at h1
  rw [diagPart,diagonal_apply_eq] at h1
  have hdii : 0<A i i := ha.diag_pos
  have hu : l≤1 := by nlinarith only [h1,hdii]
  obtain ⟨v,hv,hv'⟩ := spectral_vec hs.1
  have hvec := congrArg (fun y => D *ᵥ y) hv'
  have hdU := D.isUnit_iff_isUnit_det.mp hd.isUnit
  simp only [Matrix.mulVec_mulVec,←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hdU,one_mul,Matrix.mulVec_smul] at hvec
  have hpA := ha.dotProduct_mulVec_pos hv
  have hpD := hd.dotProduct_mulVec_pos hv
  simp only [star_trivial] at hpA hpD
  rw [hvec,dotProduct_smul,smul_eq_mul] at hpA
  have hl : 0<l := pos_of_mul_pos_left hpA hpD.le
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hsharp : l ≤ sharp n l := by
    apply (le_div_iff₀ (by linarith : 0 < (n:ℝ)-2+l)).mpr
    nlinarith only [mul_nonneg hl.le (sub_nonneg.mpr hu)]
  exact ⟨l,m,hs,hm,hl,hu,hsharp,lower_pair hn A ha hl hL m hm.1⟩
end OMA.S_mo_289475

namespace OMA.S_mo_289475
open Matrix Finset

private def onesMatrix (n : ℕ) : Mat n := Matrix.of (fun _ _ => 1)
private noncomputable def simplex (n : ℕ) : Mat n := (n:ℝ) • (1:Mat n) - onesMatrix n

private lemma simplex_psd (n : ℕ) : (simplex n).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)).sub (by ext; simp [onesMatrix])
  intro v
  have h : (∑ i,v i)^2 ≤ (n:ℝ)*∑ i,(v i)^2 := by simpa using
    (sq_sum_le_card_mul_sum_sq (s:=univ) (f:=v))
  have he : onesMatrix n *ᵥ v = fun _ => ∑ j,v j := by ext; simp [onesMatrix,mulVec,dotProduct]
  simp only [simplex,sub_mulVec,smul_mulVec,one_mulVec,he,star_trivial,dotProduct_sub,dotProduct_smul,
    smul_eq_mul]
  simp only [dotProduct,←Finset.sum_mul,←sq]
  nlinarith only [h]

private lemma average_const {n : ℕ} (hn : 2 ≤ n) (A : Mat n) (ha : A.PosDef) (r : ℝ)
    (hd : ∀ i,A i i=1) (ho : ∀ i j,i≠j → A i j=r) (hr : 0 < 1+r) :
    pairAverage A *ᵥ (fun _ => 1)=(1+r)⁻¹ • (fun _ => 1 : Vec n) := by
  let f (k i : Fin n) : ℝ := if i=k then 1 else 0
  let v : Vec n := fun _ => 1
  have hx (i j : Fin n) (hij : j≠i) :
      (principal A i j)⁻¹ *ᵥ ![1,1] = (1+r)⁻¹ • (![1,1] : Vec 2) := by
    let C := principal A i j
    have row : C *ᵥ ![1,1]=(1+r) • (![1,1] : Vec 2) := by
      ext t
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul]
      fin_cases t
      · change A i i * 1 + A i j * 1 = (1+r)*1
        rw [hd,ho _ _ hij.symm]
        ring
      · change A j i * 1 + A j j * 1 = (1+r)*1
        rw [hd,ho _ _ hij]
        ring
    have eq := congrArg (fun y => C⁻¹ *ᵥ y) row
    simp only [mulVec_mulVec,nonsing_inv_mul _ (C.isUnit_iff_isUnit_det.mp (pair_pd ha hij).isUnit),
      one_mulVec,mulVec_smul] at eq
    have h := congrArg (fun y : Vec 2 => (1+r)⁻¹ • y) eq
    simpa only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul] using h.symm
  have lift (i j : Fin n) (hij : j≠i) (k : Fin n) :
      (liftInv A i j *ᵥ v) k=(1+r)⁻¹*(f k i + f k j) := by
    simp only [liftInv,←mulVec_mulVec,select_apply,v,hx i j hij,mulVec_smul,Pi.smul_apply,smul_eq_mul]
    apply congrArg ((1+r)⁻¹ * ·)
    simp only [mulVec,dotProduct,Fin.sum_univ_two,selectPair,transpose_apply,vertices,cons_val_zero,cons_val_one,mul_one]
    rfl
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnorm : 2*((n:ℝ)-1) ≠ 0 := by linarith
  ext1 k
  change (pairAverage A *ᵥ v) k = _
  simp only [pairAverage,smul_mulVec,sum_mulVec,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,mul_one]
  have e := sum_congr (s₁:=univ) rfl (fun i _ => sum_congr (s₁:=univ.erase i) rfl (fun j hj => lift i j (mem_erase.mp hj).1 k))
  rw [e]
  simp only [←Finset.mul_sum,sum_pairs_diag hn]
  rw [show (∑ i,f k i)=1 by simp [f],mul_one,mul_left_comm,inv_mul_cancel₀ hnorm,mul_one]

private lemma sharp_case (n : ℕ) (hn : 2 ≤ n) (l : ℝ) (hl : 0 < l) (hu : l ≤ 1) :
    ∃ A : Mat n, A.PosDef ∧ (∀ i, A i i=1) ∧ IsLeast (spectrum ℝ ((diagPart A)⁻¹*A)) l ∧
      IsLeast (spectrum ℝ (pairAverage A*A)) (sharp n l) := by
  let c := (1-l)/((n:ℝ)-1)
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)-1 := by linarith
  have hcn : c*((n:ℝ)-1)=1-l := by exact div_mul_cancel₀ _ hd.ne'
  have hcp : 0 ≤ c := div_nonneg (sub_nonneg.mpr hu) hd.le
  have hcl : c < 1 := (div_lt_iff₀ hd).mpr (by linarith)
  let A : Mat n := l • (1:Mat n)+c • simplex n
  have hp : A.PosDef := (Matrix.PosDef.one.smul hl).add_posSemidef ((simplex_psd n).smul hcp)
  have hshift : (A-l • (1:Mat n)).PosSemidef := by
    simpa [A] using (simplex_psd n).smul hcp
  have hdiag (i : Fin n) : A i i=1 := by
    simp [A,simplex,onesMatrix]
    linarith only [hcn]
  have hoff (i j : Fin n) (hij : i≠j) : A i j = -c := by simp [A,simplex,onesMatrix,one_apply_ne hij]
  have hD : diagPart A=1 := by simp [diagPart,hdiag]
  let v : Vec n := fun _ => 1
  have hv : v≠0 := by
    intro h
    have := congrFun h (⟨0,by omega⟩ : Fin n)
    norm_num [v] at this
  have hs : simplex n *ᵥ v=0 := by
    rw [simplex,sub_mulVec,smul_mulVec,one_mulVec]
    ext i
    simp [v,onesMatrix,mulVec,dotProduct]
  have he : A*ᵥv=l•v := by simp [A,add_mulVec,smul_mulVec,hs]
  have hlmin : IsLeast (spectrum ℝ A) l := by
    refine ⟨spectral_of_vec _ _ hv _ he,?_⟩
    intro z hz
    obtain ⟨w,hw,hz'⟩ := spectral_vec hz
    have hh := hshift.dotProduct_mulVec_nonneg w
    simp only [star_trivial,sub_mulVec,hz',smul_mulVec,one_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul] at hh
    have hw' : 0 < w ⬝ᵥ w := by simpa using (Matrix.PosDef.one (n:=Fin n) (R:=ℝ)).dotProduct_mulVec_pos hw
    exact (mul_le_mul_iff_of_pos_right hw').mp (sub_nonneg.mp hh)
  have hb := average_const hn A hp (-c) hdiag hoff (by linarith)
  have hsl : l*(1+-c)⁻¹=sharp n l := by
    dsimp [sharp]
    field_simp [show (1+-c)≠0 by linarith,show (n:ℝ)-2+l≠0 by linarith]
    nlinarith only [hcn,congrArg (fun x : ℝ => l*x) hcn]
  refine ⟨A,hp,hdiag,by simpa only [hD,inv_one,one_mul] using hlmin,?_,?_⟩
  · apply spectral_of_vec _ v hv
    rw [←mulVec_mulVec,he,mulVec_smul]
    change pairAverage A *ᵥ v = (1+-c)⁻¹ • v at hb
    rw [hb,smul_smul,hsl]
  · apply lower_pair hn A hp hl
    rwa [hD]
end OMA.S_mo_289475

open OMA.S_mo_289475 in
theorem OMA.solution : type_of% @OMA.S_mo_289475.main := ⟨main_lower,sharp_case⟩
