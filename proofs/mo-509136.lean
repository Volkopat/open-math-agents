import OMAStatements.S_mo_509136

namespace OMA.S_mo_509136
open Matrix Polynomial Finset

private lemma low_rank {ι κ R : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [CommRing R] (B : Matrix ι ι R) (U : Matrix ι κ R) (V : Matrix κ ι R) :
    (B+U*V).det * B.det^(Fintype.card κ) =
      B.det * (B.det • (1 : Matrix κ κ R) + V*B.adjugate*U).det := by
  let L := fromBlocks B U (-V) (1 : Matrix κ κ R)
  let Q := fromBlocks (1 : Matrix ι ι R) (-(B.adjugate*U)) (0 : Matrix κ ι R)
    (B.det • (1 : Matrix κ κ R))
  have he : L*Q = fromBlocks B 0 (-V) (B.det • (1: Matrix κ κ R)+V*B.adjugate*U) := by
    simp [L,Q,fromBlocks_multiply,← Matrix.mul_assoc, mul_adjugate, add_comm]
  have hd := congrArg Matrix.det he
  simpa [L,Q,det_mul,det_fromBlocks_one₂₂,det_fromBlocks_zero₂₁,det_fromBlocks_zero₁₂,
    det_smul] using hd

private lemma sel_left {ι κ μ R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    (f : κ → ι) (M : Matrix ι μ R) : (select (R := R) f)ᵀ * M = M.submatrix f id := by
  ext i j
  simp [select,Matrix.mul_apply,transpose_apply,ite_mul]

private lemma sel_right {ι κ μ R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    (f : κ → ι) (M : Matrix μ ι R) : M * select (R := R) f = M.submatrix id f := by
  ext i j
  simp [select,Matrix.mul_apply,mul_ite]

private lemma sel_square {ι κ μ R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    (f : κ → ι) (g : μ → ι) (M : Matrix ι ι R) : (select (R := R) f)ᵀ * M * select (R := R) g =
    M.submatrix f g := by
  rw [sel_left,sel_right]
  rfl

private lemma outside_match {n : ℕ} {r c y : Fin (n+1)} (hy : y ∉ Finset.uIcc r c) :
    ∃ k : Fin n, r.succAbove k=y ∧ c.succAbove k=y := by
  have hne : y≠r := by rintro rfl; exact hy Finset.left_mem_uIcc
  obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hne
  refine ⟨k,hk,?_⟩
  have hv (z : Fin (n+1)) : (z.succAbove k).val = if k.val < z.val then k.val else k.val+1 := by
    unfold Fin.succAbove
    by_cases h : k.val < z.val <;> simp [Fin.lt_def,h]
  have hk' := congrArg Fin.val hk
  rw [hv] at hk'
  apply Fin.ext
  rw [hv]
  by_cases hrc : r≤c
  · rw [Finset.uIcc_of_le hrc,Finset.mem_Icc] at hy
    simp only [Fin.le_def] at hy hrc
    split_ifs at hk' ⊢ <;> omega
  · rw [Finset.uIcc_of_ge (le_of_not_ge hrc),Finset.mem_Icc] at hy
    simp only [Fin.le_def] at hy hrc
    split_ifs at hk' ⊢ <;> omega

private lemma transfer_row {n : ℕ} {R : Type} [CommRing R] (r c : Fin (n+1))
    (k : Fin n) (y : Fin (n+1)) : (transfer r c : Matrix _ _ R) (c.succAbove k) y =
      if y=r.succAbove k then 1 else 0 := by
  rw [transfer,Matrix.mul_apply,Finset.sum_eq_single k]
  · simp [select,transpose_apply]
  · intro b _ h
    simp [select,transpose_apply,Ne.symm h]
  · simp
private lemma transfer_col {n : ℕ} {R : Type} [CommRing R] (r c : Fin (n+1))
    (k : Fin n) (y : Fin (n+1)) : (transfer r c : Matrix _ _ R) y (r.succAbove k) =
      if y=c.succAbove k then 1 else 0 := by
  simp [transfer,select,Matrix.mul_apply,mul_ite,transpose_apply]

private lemma cut_entry {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    (s : Finset ι) (B : Matrix s s R) (x y : ι) :
    (select (R := R) (Subtype.val : s→ι)*B*(select (R := R) (Subtype.val : s→ι))ᵀ) x y =
      if hx : x ∈ s then if hy : y ∈ s then B ⟨x,hx⟩ ⟨y,hy⟩ else 0 else 0 := by
  by_cases hx : x∈s
  · by_cases hy : y∈s
    · let a : s := ⟨x,hx⟩
      let b : s := ⟨y,hy⟩
      have hx' (k : s) : x=k.val ↔ a=k := by simp [a,Subtype.ext_iff]
      have hy' (k : s) : y=k.val ↔ b=k := by simp [b,Subtype.ext_iff]
      simp [select,Matrix.mul_apply,transpose_apply,hx,hy,hx',hy',ite_mul,mul_ite,a,b]
    · have hy' (k : s) : y≠k.val := by rintro rfl; exact hy k.property
      simp [Matrix.mul_apply,select,hx,hy,hy',transpose_apply]
  · have hx' (k : s) : x≠k.val := by rintro rfl; exact hx k.property
    simp [Matrix.mul_apply,select,hx,hx',transpose_apply]

private lemma localized {n : ℕ} {R : Type} [CommRing R] (r c : Fin (n+1)) :
    (1-transfer r c : Matrix _ _ R) =
      select (R := R) (Subtype.val : Window r c → _)*(1-shift (R := R) r c)*(select (R := R) (Subtype.val : Window r c → _))ᵀ := by
  ext x y
  rw [cut_entry]
  by_cases hx : x∈Finset.uIcc r c
  · by_cases hy : y∈Finset.uIcc r c
    · simp [hx,hy,shift,submatrix_apply,one_apply,Subtype.ext_iff]
    · obtain ⟨k,hk,hk'⟩ := outside_match hy
      rw [Matrix.sub_apply,← hk,transfer_col, hk,hk']
      simp [hx,hy,one_apply]
  · obtain ⟨k,hk,hk'⟩ := outside_match hx
    rw [Matrix.sub_apply,← hk',transfer_row,hk',hk]
    simp [hx,one_apply,eq_comm]

private lemma compressed {ι κ F : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [CommRing F] (z p : F) (A B T : Matrix ι ι F) (f : κ → ι) (hf : Function.Injective f)
    (S : Matrix κ κ F) (hB : B=z • 1-A) (hp : B.det=p)
    (hT : 1-T=select (R := F) f*(1-S)*(select (R := F) f)ᵀ) :
    (z • 1-A*T).det * p ^ Fintype.card κ =
      p * (p • S + z • (B.adjugate.submatrix f f * (1-S))).det := by
  let E := select (R := F) f
  have hlarge : B+A*E*(1-S)*Eᵀ=z • 1-A*T := by
    rw [hB,Matrix.mul_assoc A E, Matrix.mul_assoc A, ← hT,Matrix.mul_sub,Matrix.mul_one]
    abel
  have hprod : B.adjugate*A=z • B.adjugate-p • 1 := by
    rw [show A=z • 1-B by rw [hB]; abel,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,adjugate_mul,hp]
  have he : Eᵀ*(B.adjugate*A)*E=z • B.adjugate.submatrix f f-p • 1 := by
    rw [hprod,sel_square]
    simp [submatrix_sub,submatrix_smul,submatrix_one _ hf]
  have hsmall : p • 1+Eᵀ*B.adjugate*(A*E*(1-S)) = p • S+z • (B.adjugate.submatrix f f*(1-S)) := by
    rw [show Eᵀ*B.adjugate*(A*E*(1-S)) = (Eᵀ*(B.adjugate*A)*E)*(1-S) by simp [Matrix.mul_assoc],he]
    simp [Matrix.sub_mul,Matrix.mul_sub,smul_sub]
    abel
  have hh := low_rank B (A*E*(1-S)) Eᵀ
  rw [hlarge,hp,hsmall] at hh
  exact hh

private lemma char_transfer {n : ℕ} {R : Type} [CommRing R]
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (r c : Fin (n+1)) :
    (A * transfer r c).charpoly = X * (minor A r c).charpoly := by
  rw [transfer,←Matrix.mul_assoc, charpoly_mul_comm_of_le _ _ (by simp)]
  simp [← Matrix.mul_assoc,sel_square,minor]

private lemma char_matrix {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R) : A.charmatrix = (X : R[X]) • 1 - A.map (C : R →+* R[X]) := by
  rw [Matrix.smul_one_eq_diagonal]
  rfl

private lemma transfer_C {n : ℕ} {R : Type} [CommRing R] (r c : Fin (n+1)) :
    (transfer (R := R) r c).map C = transfer (R := R[X]) r c := by
  ext i j
  simp [transfer,select,mul_apply,transpose_apply,apply_ite]

set_option maxHeartbeats 700000 in
private lemma formula {n : ℕ} {R : Type} [CommRing R] [IsDomain R]
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (r c : Fin (n+1)) :
    X * (minor A r c).charpoly * A.charpoly^(Fintype.card (Window r c)-1) =
      (A.charpoly • shift (R := R[X]) r c + (X:R[X]) • (adjWindow A r c*(1-shift (R := R[X]) r c))).det := by
  let p := A.charpoly
  have hh := compressed (X:R[X]) p (A.map (C : R →+* R[X])) A.charmatrix
    (transfer (R := R[X]) r c) (Subtype.val : Window r c → _) Subtype.val_injective
    (shift r c) (char_matrix A) rfl (localized r c)
  have he : (A*transfer r c).charmatrix =
      (X:R[X]) • 1-A.map (C : R →+* R[X]) *transfer (R := R[X]) r c := by
    rw [char_matrix,Matrix.map_mul,transfer_C]
  rw [← he] at hh
  have hraw : X*(minor A r c).charpoly*p^Fintype.card (Window r c) =
      p * (p • shift (R := R[X]) r c+(X:R[X]) • (adjWindow A r c*(1-shift r c))).det := by
    rw [← char_transfer]
    exact hh
  have hi : Nonempty (Window r c) := ⟨⟨r, Finset.left_mem_uIcc⟩⟩
  have hcard : Fintype.card (Window r c)-1+1=Fintype.card (Window r c) := by
    have := Fintype.card_pos (α := Window r c)
    omega
  apply mul_left_cancel₀ (show p≠0 from A.charpoly_monic.ne_zero)
  calc
    _ = X*(minor A r c).charpoly*(p^(Fintype.card (Window r c)-1)*p) := by ring
    _ = _ := by rw [← pow_succ,hcard]; exact hraw

private def windowTwo {n : ℕ} (k : Fin n) : Fin 2 ≃ Window k.succ k.castSucc where
  toFun i := if i=0 then ⟨k.castSucc,Finset.right_mem_uIcc⟩ else ⟨k.succ,Finset.left_mem_uIcc⟩
  invFun x := if x.val=k.castSucc then 0 else 1
  left_inv := by
    intro i
    fin_cases i <;> simp [Fin.ne_of_gt k.castSucc_lt_succ]
  right_inv := by
    rintro ⟨x,hx⟩
    rw [Finset.uIcc_of_ge (Fin.le_of_lt k.castSucc_lt_succ),Finset.mem_Icc] at hx
    by_cases h : x=k.castSucc
    · simp [h]
    · have hx' : x=k.succ := by
        apply Fin.ext
        simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ,Fin.ext_iff] at *
        omega
      simp [hx',Fin.ne_of_gt k.castSucc_lt_succ]

private lemma transfer_missing {n : ℕ} {R : Type} [CommRing R] (r c y : Fin (n+1)) :
    (transfer r c : Matrix _ _ R) c y=0 := by
  simp [transfer,select,Matrix.mul_apply]

private lemma adjacent {n : ℕ} {R : Type} [CommRing R] [IsDomain R]
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (k : Fin n) :
    A.charpoly*(minor A k.succ k.castSucc).charpoly =
      X*(A.charmatrix.adjugate k.castSucc k.castSucc * A.charmatrix.adjugate k.succ k.succ -
        A.charmatrix.adjugate k.castSucc k.succ * A.charmatrix.adjugate k.succ k.castSucc) -
      A.charpoly*A.charmatrix.adjugate k.castSucc k.succ := by
  let e := windowTwo k
  let S := shift (R := R[X]) k.succ k.castSucc
  let H := adjWindow A k.succ k.castSucc
  let p := A.charpoly
  have e0 : (e 0).val=k.castSucc := rfl
  have e1 : (e 1).val=k.succ := rfl
  have hshift : S.submatrix e e = !![0,0;1,0] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact transfer_missing (R := R[X]) _ _ _
    · exact transfer_missing (R := R[X]) _ _ _
    · change transfer (R := R[X]) k.succ k.castSucc k.succ k.castSucc=1
      simpa using transfer_row (R := R[X]) k.succ k.castSucc k k.castSucc
    · change transfer (R := R[X]) k.succ k.castSucc k.succ k.succ=0
      simpa [Fin.ne_of_gt k.castSucc_lt_succ] using transfer_row (R := R[X]) k.succ k.castSucc k k.succ
  have hh := formula A k.succ k.castSucc
  have hcard : Fintype.card (Window k.succ k.castSucc)=2 := by simp [Fintype.card_congr e.symm]
  rw [hcard] at hh
  change X*(minor A k.succ k.castSucc).charpoly*p^(2-1)=(p • S+(X:R[X]) • (H*(1-S))).det at hh
  rw [← det_submatrix_equiv_self e] at hh
  have hcorrect : (p • S + (X:R[X]) • (H*(1-S))).submatrix e e =
      p • !![0,0;1,0] + (X:R[X]) • (H.submatrix e e * (1-!![0,0;1,0])) := by
    rw [submatrix_add,submatrix_smul,submatrix_smul]
    change p • S.submatrix e e + (X:R[X]) • (H*(1-S)).submatrix e e = _
    rw [← submatrix_mul_equiv H (1-S) e e e,
      submatrix_sub]
    change p • S.submatrix e e + (X:R[X]) • (H.submatrix e e * ((1 : Matrix _ _ R[X]).submatrix e e-S.submatrix e e)) = _
    rw [submatrix_one_equiv,hshift]
  rw [hcorrect,det_fin_two] at hh
  simp [Matrix.mul_apply,Fin.sum_univ_two,H,adjWindow,submatrix_apply,e0,e1,one_apply] at hh
  apply mul_left_cancel₀ (X_ne_zero (R := R))
  change X*(p*(minor A k.succ k.castSucc).charpoly)=_
  linear_combination hh

private lemma transfer_ite {n : ℕ} {R : Type} [CommRing R] (r c u v : Fin (n+1)) :
    (transfer r c : Matrix _ _ R) u v =
      if ∃ k, c.succAbove k=u ∧ r.succAbove k=v then 1 else 0 := by
  by_cases h : u=c
  · subst u
    simp [transfer_missing]
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq h
    rw [transfer_row]
    simp [eq_comm]

private lemma entry {n : ℕ} {R : Type} [CommRing R] (r c : Fin (n+1))
    (u v : Window r c) : shift (R := R) r c u v =
      if (c<r ∧ u.val.val=v.val.val+1) ∨ (r<c ∧ v.val.val=u.val.val+1) then 1 else 0 := by
  change (transfer r c : Matrix _ _ R) u.val v.val=_
  rw [transfer_ite]
  congr 1
  apply propext
  have hu := u.property
  have hv := v.property
  have hval (z : Fin (n+1)) (k : Fin n) : (z.succAbove k).val =
      if k.val<z.val then k.val else k.val+1 := by
    unfold Fin.succAbove
    by_cases h : k.val<z.val <;> simp [Fin.lt_def,h]
  change u.val∈Finset.uIcc r c at hu
  change v.val∈Finset.uIcc r c at hv
  rw [Finset.mem_uIcc'] at hu hv
  change (r.val≤u.val.val ∧ u.val.val≤c.val) ∨ (c.val≤u.val.val ∧ u.val.val≤r.val) at hu
  change (r.val≤v.val.val ∧ v.val.val≤c.val) ∨ (c.val≤v.val.val ∧ v.val.val≤r.val) at hv
  simp only [Fin.lt_def]
  constructor
  · rintro ⟨k,hk,hl⟩
    have huv := congrArg Fin.val hk
    have hvv := congrArg Fin.val hl
    rw [hval] at huv hvv
    split_ifs at huv hvv <;> omega
  · rintro (⟨h₁,h₂⟩|⟨h₁,h₂⟩)
    · let k : Fin n := ⟨v.val.val,by have := u.val.isLt; omega⟩
      refine ⟨k, Fin.ext ?_, Fin.ext ?_⟩
      all_goals rw [hval]; dsimp [k]; split_ifs <;> omega
    · let k : Fin n := ⟨u.val.val,by have := v.val.isLt; omega⟩
      refine ⟨k, Fin.ext ?_, Fin.ext ?_⟩
      all_goals rw [hval]; dsimp [k]; split_ifs <;> omega

end OMA.S_mo_509136
open OMA.S_mo_509136 in
theorem OMA.solution : type_of% @OMA.S_mo_509136.main := by
  intro R _ _ n A
  exact ⟨formula A, fun r c => entry r c, adjacent A⟩
