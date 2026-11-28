import OMAStatements.S_mo_440872

namespace OMA.S_mo_440872
open Matrix Polynomial Finset

open Unitary

private lemma family_mul {n : ℕ} {A : Mat n} (h : A.IsHermitian) (f g : ℝ → ℝ) :
    spectral h f * spectral h g = spectral h (fun x => f x*g x) := by
  unfold spectral
  rw [← map_mul,diagonal_mul_diagonal]

private lemma family_add {n : ℕ} {A : Mat n} (h : A.IsHermitian) (f g : ℝ → ℝ) :
    spectral h f + spectral h g = spectral h (fun x => f x+g x) := by
  unfold spectral
  rw [← map_add,diagonal_add]

private lemma family_zero {n : ℕ} {A : Mat n} (h : A.IsHermitian) :
    spectral h (fun _ => 0)=0 := by simp [spectral,-conjStarAlgAut_apply]

private lemma family_one {n : ℕ} {A : Mat n} (h : A.IsHermitian) :
    spectral h (fun _ => 1)=1 := by simp [spectral,-conjStarAlgAut_apply]

private lemma family_id {n : ℕ} {A : Mat n} (h : A.IsHermitian) :
    spectral h id=A := by simpa [spectral] using h.spectral_theorem.symm

private lemma proj_sym {n : ℕ} {A : Mat n} (h : A.IsHermitian) : (kernelProj h)ᵀ=kernelProj h := by
  simp [kernelProj,spectral,conjStarAlgAut_apply,star_eq_conjTranspose,Matrix.transpose_mul,
    Matrix.mul_assoc]

private lemma ker_laws {n : ℕ} {A : Mat n} (h : A.IsHermitian) :
    A*kernelProj h=0 ∧ kernelProj h*A=0 ∧ kernelProj h*kernelProj h=kernelProj h ∧
      A*pinv h+kernelProj h=1 ∧ pinv h*A+kernelProj h=1 ∧
      kernelProj h*pinv h=0 ∧ pinv h*kernelProj h=0 := by
  let q := fun x : ℝ => if x=0 then (1:ℝ) else 0
  change A*spectral h q=0 ∧ spectral h q*A=0 ∧ spectral h q*spectral h q=spectral h q ∧
    A*spectral h (fun x => x⁻¹)+spectral h q=1 ∧ spectral h (fun x => x⁻¹)*A+spectral h q=1 ∧
    spectral h q*spectral h (fun x => x⁻¹)=0 ∧ spectral h (fun x => x⁻¹)*spectral h q=0
  have h1 : spectral h id*spectral h q=0 := by
    rw [family_mul, ← family_zero h]; congr 1; funext x; by_cases hx : x=0 <;> simp [q,hx]
  have h2 : spectral h q*spectral h id=0 := by
    rw [family_mul, ← family_zero h]; congr 1; funext x; by_cases hx : x=0 <;> simp [q,hx]
  have h3 : spectral h q*spectral h q=spectral h q := by
    rw [family_mul]; congr 1; funext x; by_cases hx : x=0 <;> simp [q,hx]
  have h4 : spectral h id*spectral h (fun x => x⁻¹)+spectral h q=1 := by
    rw [family_mul,family_add,← family_one h]; congr 1; funext x; by_cases hx : x=0 <;> simp [q,hx]
  have h5 : spectral h (fun x => x⁻¹)*spectral h id+spectral h q=1 := by
    rw [family_mul,family_add,← family_one h]; congr 1; funext x; by_cases hx : x=0 <;> simp [q,hx]
  have h6 : spectral h q*spectral h (fun x => x⁻¹)=0 := by
    rw [family_mul,← family_zero h]; congr 1; funext x; by_cases hx : x=0 <;> simp [q,hx]
  have h7 : spectral h (fun x => x⁻¹)*spectral h q=0 := by
    rw [family_mul,← family_zero h]; congr 1; funext x; by_cases hx : x=0 <;> simp [q,hx]
  rw [family_id] at h1 h2 h4 h5
  exact ⟨h1,h2,h3,h4,h5,h6,h7⟩

private lemma pencil_mul {n : ℕ} (A B C D : Mat n) :
    pencil A B * pencil C D = pencil (A*C) (A*D+B*C) + (X:ℝ[X])^2 • (B*D).map Polynomial.C := by
  simp [pencil,Matrix.add_mul,Matrix.mul_add,Matrix.map_mul,
    Matrix.map_add _ (map_add Polynomial.C),smul_add,smul_smul,pow_two]
  abel

private lemma constant_det {n : ℕ} (A P : Mat n) : (pencil A P).det.coeff 0 = A.det := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  change (evalRingHom (0:ℝ)) (pencil A P).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [pencil,RingHom.mapMatrix_apply,Matrix.map_apply]

private lemma factor_reg {n : ℕ} (A P Q : Mat n) (hQA : Q*A=0) (hQQ : Q*Q=Q) (hQP : Q*P=Q) :
    pencil A P=pencil (1-Q) Q * pencil (A+Q) (P-Q) := by
  rw [pencil_mul]
  have h1 : (1-Q)*(A+Q)=A := by simp [Matrix.sub_mul,Matrix.mul_add,hQA,hQQ]
  have h2 : (1-Q)*(P-Q)+Q*(A+Q)=P := by simp [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_add,hQP,hQQ,hQA]
  rw [h1,h2,Matrix.mul_sub,hQP,hQQ,sub_self]
  simp

private lemma pdet_regular {n : ℕ} (A P : Mat n) (hA : A.IsHermitian)
    (hQP : kernelProj hA*P=kernelProj hA) : (pencil A P).det.trailingCoeff = pdet A := by
  let Q := kernelProj hA
  obtain ⟨hAQ,hQA,hQQ,hplus,_,hQinv,hinvQ⟩ := ker_laws hA
  have hdet : (A+Q).det ≠ 0 := by
    have hright : (A+Q)*(pinv hA+Q)=1 := by
      change (A+kernelProj hA)*(pinv hA+kernelProj hA)=1
      simp [Matrix.add_mul,Matrix.mul_add,hAQ,hQinv,hQQ,hplus]
    have hd := congrArg Matrix.det hright
    rw [det_mul,det_one] at hd
    exact left_ne_zero_of_mul_eq_one hd
  have htr (T : Mat n) : (pencil (A+Q) T).det.trailingCoeff=(A+Q).det := by
    rw [Polynomial.trailingCoeff_eq_coeff_zero (by rw [constant_det]; exact hdet),constant_det]
  have he : pdet A = (pencil A 1).det.trailingCoeff := by
    unfold pdet Matrix.charpoly
    congr 2
    ext i j
    simp [Matrix.charmatrix_apply,pencil,one_apply,diagonal,add_comm]
  rw [he,factor_reg A P Q hQA hQQ hQP,factor_reg A 1 Q hQA hQQ (Matrix.mul_one Q),
    det_mul,det_mul,Polynomial.trailingCoeff_mul,Polynomial.trailingCoeff_mul,htr,htr]

private lemma proj_update {n : ℕ} (A B : Mat n) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    kernelProj (hA.add hB).1 * kernelProj hA.1 = kernelProj (hA.add hB).1 := by
  let Q := kernelProj (hA.add hB).1
  have hQ : (A+B)*Q=0 := (ker_laws (hA.add hB).1).1
  have hAQ : A*Q=0 := by
    ext i j
    let x := fun a => Q a j
    have hx : (A+B)*ᵥx=0 := by
      funext a
      exact congrFun (congrFun hQ a) j
    have hsum := (hA.add hB).dotProduct_mulVec_zero_iff x |>.2 hx
    rw [Matrix.add_mulVec,dotProduct_add] at hsum
    have hzero : star x ⬝ᵥ (A*ᵥx)=0 := by
      linarith [hA.dotProduct_mulVec_nonneg x,hB.dotProduct_mulVec_nonneg x]
    exact congrFun ((hA.dotProduct_mulVec_zero_iff x).1 hzero) i
  have hrel := (ker_laws hA.1).2.2.2.2.1
  have hh := congrArg (fun T : Mat n => T*Q) hrel
  simp only [Matrix.add_mul,Matrix.mul_assoc,hAQ,Matrix.mul_zero,zero_add,Matrix.one_mul] at hh
  have hh' := congrArg Matrix.transpose hh
  simpa [Matrix.transpose_mul,proj_sym,Q] using hh'

private lemma scaled_update {ι κ R : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [CommRing R] (B J : Matrix ι ι R) (U : Matrix ι κ R) (V : Matrix κ ι R) (d : R) (hb : B*J=d • 1) :
    (B+U*V).det * d^(Fintype.card κ) =
      B.det * (d • (1 : Matrix κ κ R) + V*J*U).det := by
  let L := fromBlocks B U (-V) (1 : Matrix κ κ R)
  let Q := fromBlocks (1 : Matrix ι ι R) (-(J*U)) (0 : Matrix κ ι R)
    (d • (1 : Matrix κ κ R))
  have he : L*Q = fromBlocks B 0 (-V) (d • (1: Matrix κ κ R)+V*J*U) := by
    simp [L,Q,fromBlocks_multiply,← Matrix.mul_assoc, hb, add_comm]
  have hd := congrArg Matrix.det he
  simpa [L,Q,det_mul,det_fromBlocks_one₂₂,det_fromBlocks_zero₂₁,det_fromBlocks_zero₁₂,
    det_smul] using hd


private lemma sandwich {n k : ℕ} (L : Rect k n) (A B : Mat n) (U : Rect n k) :
    L.map Polynomial.C * pencil A B * U.map Polynomial.C = pencil (L*A*U) (L*B*U) := by
  simp [pencil,Matrix.mul_add,Matrix.add_mul,Matrix.map_mul]

private lemma trailing_X_pow (k : ℕ) : ((X:ℝ[X])^k).trailingCoeff=1 := by
  have hX : (X:ℝ[X]).trailingCoeff=1 := by
    simp [Polynomial.trailingCoeff]
  induction k with
  | zero => simp [Polynomial.trailingCoeff]
  | succ k ih => rw [pow_succ,Polynomial.trailingCoeff_mul,ih,hX,one_mul]

private lemma update_semidef {n k : ℕ} (A : Mat n) (U : Rect n k) (W : Mat k)
    (hA : A.PosSemidef) (hW : W.PosSemidef) :
    pdet (A+U*W*Uᵀ)=pdet A *
      (pencil (W*Uᵀ*kernelProj hA.1*U) (1+W*Uᵀ*pinv hA.1*U)).det.trailingCoeff := by
  let P := kernelProj hA.1
  let D := pinv hA.1
  have hregular : pencil A P * pencil P D = (X:ℝ[X]) • 1 := by
    obtain ⟨hAP,_,hPP,hplus,_,hPD,_⟩ := ker_laws hA.1
    rw [pencil_mul]
    simp [P,D,hAP,hPP,hplus,hPD,pencil]
  have hd := scaled_update (pencil A P) (pencil P D) (U.map Polynomial.C)
    ((W*Uᵀ).map Polynomial.C) X hregular
  have hleft : pencil A P+U.map Polynomial.C*(W*Uᵀ).map Polynomial.C =
      pencil (A+U*W*Uᵀ) P := by
    simp [pencil,Matrix.map_mul,Matrix.map_add _ (map_add Polynomial.C),Matrix.mul_assoc]
    abel
  have hright : (X:ℝ[X]) • (1 : Matrix (Fin k) (Fin k) ℝ[X]) +
      (W*Uᵀ).map Polynomial.C*pencil P D*U.map Polynomial.C =
      pencil (W*Uᵀ*P*U) (1+W*Uᵀ*D*U) := by
    rw [sandwich]
    simp [pencil,Matrix.map_add _ (map_add Polynomial.C),smul_add]
    abel
  rw [hleft,hright,Fintype.card_fin] at hd
  have h := congrArg Polynomial.trailingCoeff hd
  have hB : (U*W*Uᵀ).PosSemidef := by
    simpa using hW.mul_mul_conjTranspose_same U
  rw [Polynomial.trailingCoeff_mul,Polynomial.trailingCoeff_mul,trailing_X_pow,mul_one,
    pdet_regular _ P (hA.add hB).1 (proj_update A _ hA hB),
    pdet_regular A P hA.1 (ker_laws hA.1).2.2.1] at h
  exact h

private lemma pdet_eigen {n : ℕ} (A : Mat n) (h : A.IsHermitian) :
    pdet A = ∏ i, if h.eigenvalues i=0 then 1 else h.eigenvalues i := by
  have he : (-A).charpoly = ∏ i, (X+C (h.eigenvalues i)) := by
    have hd : -A = Unitary.conjStarAlgAut ℝ _ h.eigenvectorUnitary
        (diagonal fun i => -h.eigenvalues i) := by
      rw [← diagonal_neg, map_neg]
      simpa [Unitary.conjStarAlgAut_apply] using congrArg Neg.neg h.spectral_theorem
    rw [hd,Unitary.conjStarAlgAut_apply,charpoly_mul_comm,← mul_assoc]
    simp [charpoly_diagonal]
  unfold pdet
  rw [he]
  have hfactor (x : ℝ) : ((X:ℝ[X])+C x).trailingCoeff = if x=0 then 1 else x := by
    by_cases hx : x=0
    · simp [hx,Polynomial.trailingCoeff]
    · rw [Polynomial.trailingCoeff_eq_coeff_zero (by simpa using hx)]
      simp [hx]
  generalize (Finset.univ : Finset (Fin n)) = S
  induction S using Finset.induction_on with
  | empty => simp [Polynomial.trailingCoeff]
  | insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Polynomial.trailingCoeff_mul,hfactor,ih]

private lemma pdet_pencil {n : ℕ} (A : Mat n) :
    (pencil A 1).det.trailingCoeff=pdet A := by
  unfold pdet Matrix.charpoly
  congr 2
  ext i j
  simp [pencil,Matrix.charmatrix_apply,one_apply,diagonal,add_comm]

private lemma left_pencil {n : ℕ} (L G H : Mat n) :
    L.map Polynomial.C * pencil G H = pencil (L*G) (L*H) := by
  simp [pencil,Matrix.mul_add,Matrix.map_mul]

private lemma trailing_left {n : ℕ} (L G H : Mat n) :
    (pencil (L*G) (L*H)).det.trailingCoeff = L.det*(pencil G H).det.trailingCoeff := by
  rw [← left_pencil,det_mul,Polynomial.trailingCoeff_mul]
  have ha : (L.map Polynomial.C).det = C L.det := (Polynomial.C.map_det L).symm
  rw [ha]
  simp [Polynomial.trailingCoeff]

private lemma definite_update {n k : ℕ} (A : Mat n) (U : Rect n k) (W : Mat k)
    (hA : A.PosSemidef) (hW : W.PosDef) :
    let G := Uᵀ * kernelProj hA.1 * U
    let H := W⁻¹ + Uᵀ * pinv hA.1 * U
    pdet (A+U*W*Uᵀ) = pdet A * W.det * (pencil G H).det.trailingCoeff ∧
    pdet (A+U*W*Uᵀ) = pdet A * W.det * H.det * pdet (H⁻¹*G) := by
  dsimp only
  let G := Uᵀ * kernelProj hA.1 * U
  let H := W⁻¹ + Uᵀ * pinv hA.1 * U
  change _ = _ * _ * (pencil G H).det.trailingCoeff ∧ _ = _ * _ * H.det * pdet (H⁻¹*G)
  have hD : (pinv hA.1).PosSemidef := by
    let V := hA.1.eigenvectorUnitary
    have hdiag : (diagonal fun i => (hA.1.eigenvalues i)⁻¹).PosSemidef :=
      PosSemidef.diagonal fun i => inv_nonneg.mpr (hA.eigenvalues_nonneg i)
    simpa [pinv,spectral,Unitary.conjStarAlgAut_apply,star_eq_conjTranspose,V] using
      hdiag.mul_mul_conjTranspose_same (V : Mat n)
  have hH : H.PosDef := hW.inv.add_posSemidef (by simpa using hD.conjTranspose_mul_mul_same U)
  have hleft : W*G = W*Uᵀ*kernelProj hA.1*U := by simp [G,Matrix.mul_assoc]
  have hright : W*H = 1+W*Uᵀ*pinv hA.1*U := by
    simp [H,Matrix.mul_add,Matrix.mul_assoc,Matrix.mul_nonsing_inv W (W.isUnit_iff_isUnit_det.mp hW.isUnit)]
  have first : pdet (A+U*W*Uᵀ) = pdet A*W.det*(pencil G H).det.trailingCoeff := by
    rw [update_semidef A U W hA hW.posSemidef,← hleft,← hright,trailing_left,mul_assoc]
  refine ⟨first,?_⟩
  have hd := trailing_left H (H⁻¹*G) 1
  rw [← Matrix.mul_assoc,H.mul_nonsing_inv (H.isUnit_iff_isUnit_det.mp hH.isUnit),one_mul,
    Matrix.mul_one,pdet_pencil] at hd
  simp only [first,hd,mul_assoc]

private lemma contained_update {n k : ℕ} (A : Mat n) (U : Rect n k) (W : Mat k)
    (hA : A.PosSemidef) (hW : W.PosDef) (h : kernelProj hA.1*U=0) :
    pdet (A+U*W*Uᵀ) = pdet A*W.det*(W⁻¹+Uᵀ*pinv hA.1*U).det := by
  have hz : pdet (0:Mat k)=1 := by
    simp [pdet,Matrix.charpoly_zero,trailing_X_pow]
  have hh := (definite_update A U W hA hW).2
  have hg : Uᵀ * kernelProj hA.1 * U = 0 := by rw [Matrix.mul_assoc,h,Matrix.mul_zero]
  rw [hg,Matrix.mul_zero,hz,mul_one] at hh
  exact hh

private lemma scalar_trailing (a b : ℝ) : (C a+X*C b).trailingCoeff = if a=0 then b else a := by
  by_cases ha : a=0
  · rw [if_pos ha,ha,map_zero,zero_add,Polynomial.trailingCoeff_mul]
    simp [Polynomial.trailingCoeff]
  · rw [Polynomial.trailingCoeff_eq_coeff_zero (by simpa using ha)]
    simp [ha]

private lemma one_column {n : ℕ} (A : Mat n) (U : Rect n 1) (W : Mat 1)
    (hA : A.PosSemidef) (hW : W.PosSemidef) :
    let g := (W*Uᵀ*kernelProj hA.1*U) 0 0
    let h := (1+W*Uᵀ*pinv hA.1*U : Mat 1) 0 0
    pdet (A+U*W*Uᵀ) = pdet A*(if g=0 then h else g) := by
  dsimp only
  rw [update_semidef A U W hA hW,det_fin_one]
  exact congrArg (pdet A * ·) (scalar_trailing _ _)

end OMA.S_mo_440872
open OMA.S_mo_440872 in
theorem OMA.solution : type_of% @OMA.S_mo_440872.main := by
  exact ⟨pdet_eigen,update_semidef,definite_update,contained_update,one_column⟩
