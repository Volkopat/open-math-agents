import OMAStatements.S_mo_149350

namespace OMA.S_mo_149350
open Matrix Finset Set

private noncomputable def planeMatrix (ε x y : ℝ) : Mat (Fin 2) :=
  !![x, -ε*y; y, ε*x]

private lemma plane_orth (ε x y : ℝ) (he : ε^2=1) (hxy : x^2 + y^2 = 1) :
    orth (planeMatrix ε x y) := by
  unfold orth
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,planeMatrix] <;>
    nlinarith only [hxy,he,congrArg (fun t : ℝ => t * (x^2+y^2)) he]

private lemma plane_shape (M : Mat (Fin 2)) (hM : orth M) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ x y : ℝ, x^2 + y^2 = 1 ∧ M = planeMatrix ε x y := by
  let x := M 0 0
  let b := M 0 1
  let y := M 1 0
  let d := M 1 1
  let ε := x*d-b*y
  have h (i j : Fin 2) := congrFun (congrFun hM i) j
  have hxy : x^2+y^2=1 := by simpa [x,y,sq,Matrix.mul_apply,Fin.sum_univ_two] using h 0 0
  have hbd : b^2+d^2=1 := by simpa [b,d,sq,Matrix.mul_apply,Fin.sum_univ_two] using h 1 1
  have hcross : x*b+y*d=0 := by simpa [x,b,y,d,Matrix.mul_apply,Fin.sum_univ_two] using h 0 1
  have he : ε^2=1 := by
    dsimp only [ε]
    nlinarith only [congrArg₂ (·*·) hxy hbd,congrArg (·^2) hcross]
  have heb : -ε*y = b := by
    dsimp only [ε]
    linear_combination b*hxy-x*hcross
  have hed : ε*x = d := by
    dsimp only [ε]
    linear_combination d*hxy-y*hcross
  refine ⟨ε,?_,x,y,hxy,?_⟩
  · rcases sq_eq_one_iff.mp he with hε|hε
    · exact Or.inl hε
    · exact Or.inr hε
  · ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact heb.symm
    · rfl
    · exact hed.symm

private lemma plane_value {R : Type} [Fintype R] (A B : R → Fin 2 → ℝ) (ε x y : ℝ) :
    cost A B (planeMatrix ε x y) =
      (∑ r, (planeU (A r) (B r) ε)^2)*x^2 +
      2*(∑ r, planeU (A r) (B r) ε * planeV (A r) (B r) ε)*x*y +
      (∑ r, (planeV (A r) (B r) ε)^2)*y^2 := by
  classical
  unfold cost
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp [innerTerm,Fin.sum_univ_two,planeMatrix,planeU,planeV]
  ring

private lemma least_quadratic (p q s : ℝ) :
    let low := (p+s-Real.sqrt ((p-s)^2+4*q^2))/2
    (∀ x y : ℝ, x^2+y^2=1 → low ≤ p*x^2+2*q*x*y+s*y^2) ∧
    (∃ x y : ℝ, x^2+y^2=1 ∧ low = p*x^2+2*q*x*y+s*y^2) := by
  dsimp only
  let r := Real.sqrt ((p-s)^2+4*q^2)
  let l := (p+s-r)/2
  change (∀ x y : ℝ, x^2+y^2=1 → l ≤ _) ∧ ∃ x y : ℝ, x^2+y^2=1 ∧ l = _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr : r^2 = (p-s)^2+4*q^2 := Real.sq_sqrt (by positivity)
  have hab := Real.le_sqrt_of_sq_le (show (p-s)^2 ≤ (p-s)^2+4*q^2 by nlinarith [sq_nonneg q])
  have hba := Real.le_sqrt_of_sq_le (show (s-p)^2 ≤ (p-s)^2+4*q^2 by nlinarith [sq_nonneg q])
  change p-s ≤ r at hab
  change s-p ≤ r at hba
  have hp : 0 ≤ p-l := by dsimp [l]; linarith
  have hs : 0 ≤ s-l := by dsimp [l]; linarith
  have he : (p-l)*(s-l)=q^2 := by dsimp [l]; nlinarith only [hr]
  by_cases hz : p-l=0
  · have hq : q=0 := by rw [hz,zero_mul] at he; nlinarith
    constructor
    · intro x y h
      rw [hq]
      nlinarith only [mul_nonneg hs (sq_nonneg y),congrArg (fun t : ℝ => t*l) h,
        congrArg (fun t : ℝ => t*x^2) hz]
    · exact ⟨1,0,by norm_num,by simp; linarith⟩
  · have hpos : 0 < p-l := lt_of_le_of_ne hp (Ne.symm hz)
    have hsq (x y : ℝ) (hxy : x^2+y^2=1) :
        (p*x^2+2*q*x*y+s*y^2-l)*(p-l) = ((p-l)*x+q*y)^2 := by
      linear_combination y^2*he + l*(p-l)*hxy
    constructor
    · intro x y hxy
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_left
        ((hsq x y hxy).symm ▸ sq_nonneg _) hpos)
    · let t := Real.sqrt (q^2+(p-l)^2)
      have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
      have hts : t^2 = q^2+(p-l)^2 := Real.sq_sqrt (by positivity)
      have hxy : (q/t)^2+(-(p-l)/t)^2=1 := by
        field_simp
        nlinarith only [hts]
      refine ⟨q/t,-(p-l)/t,hxy,?_⟩
      have h := hsq _ _ hxy
      have hn : (p-l)*(q/t)+q*(-(p-l)/t)=0 := by ring
      rw [hn,zero_pow (by decide : (2:ℕ) ≠ 0)] at h
      exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hz)).symm

lemma planar_min {R : Type} [Fintype R] (A B : R → Fin 2 → ℝ) :
    IsLeast {c : ℝ | ∃ M : Mat (Fin 2), orth M ∧ cost A B M = c}
      (min (planeEigen A B 1) (planeEigen A B (-1))) := by
  classical
  let p (ε : ℝ) := ∑ r, (planeU (A r) (B r) ε)^2
  let q (ε : ℝ) := ∑ r, planeU (A r) (B r) ε * planeV (A r) (B r) ε
  let s (ε : ℝ) := ∑ r, (planeV (A r) (B r) ε)^2
  have att (ε : ℝ) (he : ε^2=1) : ∃ M : Mat (Fin 2), orth M ∧ cost A B M = planeEigen A B ε := by
    obtain ⟨x,y,hxy,h⟩ := (least_quadratic (p ε) (q ε) (s ε)).2
    exact ⟨_,plane_orth ε x y he hxy,(plane_value A B ε x y).trans h.symm⟩
  constructor
  · rcases le_total (planeEigen A B 1) (planeEigen A B (-1)) with h|h
    · rw [min_eq_left h]; exact att 1 (by norm_num)
    · rw [min_eq_right h]; exact att (-1) (by norm_num)
  · rintro c ⟨M,hM,rfl⟩
    obtain ⟨ε,he,x,y,hxy,rfl⟩ := plane_shape M hM
    rw [plane_value]
    have h := (least_quadratic (p ε) (q ε) (s ε)).1 x y hxy
    rcases he with rfl|rfl
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans h

end OMA.S_mo_149350

namespace OMA.S_mo_149350
open Matrix Finset
private noncomputable def sgn (x : ℝ) : ℝ := if 0≤x then 1 else -1
private def colsum {I : Type} [Fintype I] (M : Mat I) (j : I) : ℝ := ∑ i, M i j

private lemma approx_col {I : Type} [Fintype I] [DecidableEq I] {M : Mat I}
    (ho : orth M) {δ : ℝ} (hp : 0 ≤ δ) (hd : (Fintype.card I : ℝ)*δ ≤ 1)
    (he : ∀ i j, i ≠ j → |M i j| ≤ δ) (j : I) :
    |colsum M j - sgn (M j j)| ≤ (Fintype.card I:ℝ)*δ := by
  classical
  have ht : ∑ i, (M i j)^2 = 1 := by
    have hh := congrFun (congrFun ho j) j
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,pow_two] using hh
  have hj : (M j j)^2 ≤ 1 := ht ▸ Finset.single_le_sum (fun i _ => sq_nonneg (M i j)) (Finset.mem_univ j)
  have hs : ∑ i, (M i j)^2 ≤ ∑ i : I, ((if i=j then (M j j)^2 else 0)+δ^2) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with eq
    · subst i; linarith [sq_nonneg δ]
    · simpa using sq_le_sq' (abs_le.mp (he i j eq)).1 (abs_le.mp (he i j eq)).2
  rw [ht] at hs
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have hdp : (Fintype.card I:ℝ)*δ^2 ≤ δ := by nlinarith [mul_le_mul_of_nonneg_right hd hp]
  have hx : |M j j - sgn (M j j)| ≤ δ := by
    unfold sgn
    split_ifs with h
    · have hx := (abs_le.mp ((sq_le_one_iff_abs_le_one _).mp hj)).2
      rw [abs_of_nonpos (sub_nonpos.mpr hx)]
      nlinarith [mul_nonneg h (sub_nonneg.mpr hx)]
    · have hx := (abs_le.mp ((sq_le_one_iff_abs_le_one _).mp hj)).1
      rw [abs_of_nonneg (sub_nonneg.mpr hx)]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (show 0 ≤ 1 + M j j by linarith)]
  have huv : colsum M j - sgn (M j j) =
      ∑ i, (M i j - if i=j then sgn (M j j) else 0) := by simp [colsum,Finset.sum_sub_distrib]
  rw [huv]
  calc
    _ ≤ ∑ i, |M i j - if i=j then sgn (M j j) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : I, δ := Finset.sum_le_sum fun i _ => by
      split_ifs with hh
      · subst i; exact hx
      · simpa using he i j hh
    _ = _ := by simp

private lemma tol_bounds (I : Type) [Fintype I] :
    0 < tolerance I ∧ tolerance I ≤ 1/16 ∧ (Fintype.card I:ℝ)*tolerance I ≤ 1/16 := by
  have h : 0 ≤ (Fintype.card I:ℝ) := Nat.cast_nonneg _
  have hp : 0 < 16*((Fintype.card I:ℝ)+1) := by positivity
  unfold tolerance
  refine ⟨by positivity, (div_le_iff₀ hp).2 (by linarith), ?_⟩
  rw [← mul_div_assoc,div_le_iff₀ hp]
  linarith
end OMA.S_mo_149350

namespace OMA.S_mo_149350
open Matrix Finset

private lemma entry_measure {v m : ℕ} (edges : Edges v m) (M : Mat (Index v m))
    (p : Off (Index v m)) :
    innerTerm (dataA v m (.inl p)) (dataB edges (.inl p)) M = M p.val.1 p.val.2 := by
  simp [innerTerm,dataA,dataB,Pi.single_apply,ite_mul,mul_ite]
private lemma clause_measure {v m : ℕ} (edges : Edges v m) (M : Mat (Index v m)) (r : Fin m) :
    innerTerm (dataA v m (.inr r)) (dataB edges (.inr r)) M =
      colsum M (.inl (edges r 0)) + colsum M (.inl (edges r 1)) +
      colsum M (.inl (edges r 2)) + colsum M (.inr r) := by
  simp [innerTerm,dataA,dataB,colsum,Pi.single_apply,mul_add,mul_ite,Finset.sum_add_distrib]

private lemma binary {v m : ℕ} (edges : Edges v m) (hi : ∀ r, Function.Injective (edges r))
    (r : Measurement v m) (i : Index v m) :
    (dataA v m r i=0 ∨ dataA v m r i=1) ∧ (dataB edges r i=0 ∨ dataB edges r i=1) := by
  cases r with
  | inl p => simp [dataA,dataB,Pi.single_apply]; grind
  | inr r =>
    have h01 : edges r 0 ≠ edges r 1 := (hi r).ne (by decide)
    have h02 : edges r 0 ≠ edges r 2 := (hi r).ne (by decide)
    have h12 : edges r 1 ≠ edges r 2 := (hi r).ne (by decide)
    simp [dataA,dataB,Pi.single_apply]
    grind

private def bit (b : Bool) : ℝ := if b then 1 else -1
private lemma encode {v m : ℕ} {edges : Edges v m} (hc : twoColorable edges) :
    ∃ M : Mat (Index v m), orth M ∧ cost (dataA v m) (dataB edges) M = 0 := by
  obtain ⟨c,hc⟩ := hc
  let σ : Index v m → ℝ := Sum.elim (fun i => bit (c i))
    (fun r => -(bit (c (edges r 0)) + bit (c (edges r 1)) + bit (c (edges r 2))))
  have hs (i : Index v m) : σ i * σ i = 1 := by
    cases i with
    | inl i => cases hx : c i <;> simp [σ,bit,hx]
    | inr r =>
      have hn := hc r
      cases h0 : c (edges r 0) <;> cases h1 : c (edges r 1) <;> cases h2 : c (edges r 2) <;>
        simp [h0,h1,h2] at hn <;> norm_num [σ,bit,h0,h1,h2]
  refine ⟨Matrix.diagonal σ, ?_, ?_⟩
  · unfold orth
    rw [Matrix.diagonal_transpose,Matrix.diagonal_mul_diagonal]
    exact Matrix.diagonal_eq_one.mpr (funext hs)
  · unfold cost
    apply Finset.sum_eq_zero
    intro r _
    cases r with
    | inl p => simp [entry_measure,Matrix.diagonal_apply_ne _ p.property]
    | inr r =>
      rw [clause_measure]
      simp [colsum,Matrix.diagonal_apply,σ]
end OMA.S_mo_149350

namespace OMA.S_mo_149350
open Matrix Finset
private lemma decode {v m : ℕ} (edges : Edges v m) {M : Mat (Index v m)} (ho : orth M)
    (hs : cost (dataA v m) (dataB edges) M < (tolerance (Index v m))^2) : twoColorable edges := by
  classical
  let δ := tolerance (Index v m)
  obtain ⟨hδ,hδ1,hd⟩ := tol_bounds (Index v m)
  have small (r : Measurement v m) : |innerTerm (dataA v m r) (dataB edges r) M| ≤ δ := by
    have hh : (innerTerm (dataA v m r) (dataB edges r) M)^2 ≤ cost (dataA v m) (dataB edges) M :=
      Finset.single_le_sum (fun t _ => sq_nonneg (innerTerm (dataA v m t) (dataB edges t) M))
        (Finset.mem_univ r)
    exact abs_le.mpr (abs_le_of_sq_le_sq' (hh.trans hs.le) hδ.le)
  have off (i j : Index v m) (hij : i≠j) : |M i j| ≤ δ := by
    simpa only [entry_measure] using small (.inl ⟨(i,j),hij⟩)
  have hcol (i : Index v m) : |colsum M i - sgn (M i i)| ≤ 1/16 :=
    (approx_col ho hδ.le (by linarith) off i).trans hd
  let color (i : Index v m) := decide (0 ≤ M i i)
  have hbit (i : Index v m) : sgn (M i i) = bit (color i) := by simp [sgn,bit,color]
  refine ⟨fun i => color (.inl i),?_⟩
  intro r hmono
  let i : Index v m := .inl (edges r 0)
  let j : Index v m := .inl (edges r 1)
  let k : Index v m := .inl (edges r 2)
  let l : Index v m := .inr r
  change color i = color j ∧ color j = color k at hmono
  have hi := abs_le.mp (hcol i)
  have hj := abs_le.mp (hcol j)
  have hk := abs_le.mp (hcol k)
  have hl := abs_le.mp (hcol l)
  rw [hbit] at hi hj hk hl
  rw [← hmono.1] at hj
  rw [← hmono.2, ← hmono.1] at hk
  have he := abs_le.mp ((small (.inr r)).trans hδ1)
  rw [clause_measure] at he
  change -(1/16:ℝ) ≤ colsum M i + colsum M j + colsum M k + colsum M l ∧
    colsum M i + colsum M j + colsum M k + colsum M l ≤ 1/16 at he
  cases hc : color i <;> cases haux : color l <;>
    simp only [hc,haux,bit,Bool.false_eq_true,if_false,if_true] at hi hj hk hl <;>
    linarith [hi.1,hi.2,hj.1,hj.2,hk.1,hk.2,hl.1,hl.2,he.1,he.2]
end OMA.S_mo_149350

open OMA.S_mo_149350
theorem OMA.solution : type_of% @OMA.S_mo_149350.main := by
  refine ⟨fun _ _ => planar_min,fun _ _ edges hi => ⟨binary edges hi,encode,?_⟩⟩
  intro hn M ho
  exact le_of_not_gt fun hs => hn (decode edges ho hs)
