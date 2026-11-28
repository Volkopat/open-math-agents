import OMAStatements.S_mo_248693

namespace OMA.S_mo_248693
open Matrix
lemma equation_entry {n : ℕ} (A X : Mat n) (i j : Fin n) :
    equation A X i j=∑ k,(A i k+A k j)*X i k*X j k := by
  simp only [equation,Matrix.add_apply,Matrix.mul_apply,Matrix.hadamard_apply,Matrix.transpose_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
private lemma gram_rep {n : ℕ} (G : Mat n) (h : gramCode G) :
    ∃ x : Fin n → ℝ, ∀ i j,G i j=x i*x j := by
  by_cases H : ∃ p,0<G p p
  · obtain ⟨p,hp⟩ := H
    refine ⟨fun i => G i p/Real.sqrt (G p p),?_⟩
    intro i j
    have hmul := h.2.2 i j p p
    rw [h.1.apply j p] at hmul
    rw [div_mul_div_comm,←pow_two,Real.sq_sqrt hp.le,eq_div_iff hp.ne']
    exact hmul
  · push Not at H
    refine ⟨0,?_⟩
    intro i j
    have hd (k : Fin n) : G k k=0 := le_antisymm (H k) (h.2.1 k)
    have hmul := h.2.2 i j j i
    rw [h.1.apply i j,hd i,hd j,zero_mul] at hmul
    simpa using (mul_self_eq_zero.mp hmul)
lemma lift_equiv {n : ℕ} (A B : Mat n) :
    (∃ X : Mat n,equation A X=B) ↔
    ∃ G : Fin n → Mat n, (∀ k,gramCode (G k)) ∧
      ∀ i j,B i j=∑ k,(A i k+A k j)*G k i j := by
  constructor
  · rintro ⟨X,rfl⟩
    let G (k : Fin n) : Mat n := .of fun i j => X i k*X j k
    refine ⟨G,fun k => ⟨?_,fun i => mul_self_nonneg _,?_⟩,?_⟩
    · ext i j
      exact mul_comm _ _
    · intro i j l q
      change (X i k*X j k)*(X l k*X q k)=(X i k*X q k)*(X l k*X j k)
      ring
    · intro i j
      rw [equation_entry]
      simp [G,mul_assoc]
  · rintro ⟨G,hg,hB⟩
    choose x hx using fun k => gram_rep (G k) (hg k)
    refine ⟨Matrix.of fun i k => x k i,?_⟩
    ext i j
    rw [equation_entry,hB]
    simp [hx,mul_assoc]
end OMA.S_mo_248693

namespace OMA.S_mo_248693
open Matrix Finset

lemma residual_pos {n : ℕ} (A B : Mat (n+1)) (hA : goodWeight A) (hB : B.PosDef) :
    (residual A B).PosDef := by
  classical
  let a := A 0 0
  let b := B 0 0
  let l := fun i : Fin n => A i.succ 0
  let c := fun i : Fin n => B i.succ 0
  have ha : 0 < a := hA.2.1 0
  have hb : 0 < b := hB.diag_pos
  have hden (i : Fin n) : a+l i ≠ 0 := hA.2.2 0 i.succ (Fin.succ_pos i)
  let J : Matrix (Fin (n+1)) (Fin n) ℝ := .of fun i j => Fin.cases (-c j/b)
    (fun k => if k=j then 1 else 0) i
  have hj (v : Fin n → ℝ) (i : Fin n) : (J*ᵥv) i.succ=v i := by
    simp [J,mulVec,dotProduct,ite_mul]
  have hinj : Function.Injective J.mulVec := by
    intro u v h
    ext i
    simpa only [hj] using congrFun h i.succ
  have hJ := hB.conjTranspose_mul_mul_same hinj
  have hbs (j : Fin n) : B 0 j.succ = c j := by
    simpa [c] using hB.1.apply j.succ 0
  have hs (i j : Fin n) : (Jᴴ*B*J) i j = B i.succ j.succ-c i*c j/b := by
    simp [J,Matrix.mul_apply,Fin.sum_univ_succ,
      ite_mul,mul_ite,hbs,c,b]
    field_simp [show B 0 0 ≠ 0 from hb.ne']
    ring
  let w := fun i : Fin n => c i*(l i-a)/(a+l i)
  have hw := (Matrix.posSemidef_vecMulVec_self_star w).smul (inv_nonneg.mpr hb.le)
  have hpos := hJ.add_posSemidef hw
  convert hpos using 1
  ext i j
  change _ = (Jᴴ*B*J) i j+b⁻¹*(w i*w j)
  rw [hs]
  let t := pivot A B
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hb (mul_pos (by norm_num) ha))
  have hts : t^2 = b/(2*a) := Real.sq_sqrt (by positivity)
  change B i.succ j.succ - (l i+l j)*(c i/((a+l i)*t))*(c j/((a+l j)*t)) =
    B i.succ j.succ - c i*c j/b+b⁻¹*(w i*w j)
  have hprod : (c i/((a+l i)*t))*(c j/((a+l j)*t)) =
      (c i*c j)/((a+l i)*(a+l j)*t^2) := by rw [div_mul_div_comm]; congr 1; ring
  rw [mul_assoc,hprod,hts]
  dsimp only [w]
  field_simp [hden i,hden j,ha.ne',hb.ne']
  ring
end OMA.S_mo_248693

namespace OMA.S_mo_248693
open Matrix
private lemma tail_good {n : ℕ} {A : Mat (n+1)} (hA : goodWeight A) : goodWeight (tailM A) := by
  exact ⟨hA.1.submatrix Fin.succ,fun i => hA.2.1 i.succ,fun i j h => hA.2.2 _ _ (Fin.succ_lt_succ_iff.mpr h)⟩
private lemma positive_pivot {n : ℕ} {A B : Mat (n+1)} (hA : goodWeight A) (hB : B.PosDef) :
    0<pivot A B ∧ (2*A 0 0)*(pivot A B)^2=B 0 0 := by
  have ha := hA.2.1 0
  have hb : 0<B 0 0 := hB.diag_pos
  have h2 := mul_pos two_pos ha
  exact ⟨Real.sqrt_pos.mpr (div_pos hb h2),by rw [pivot,Real.sq_sqrt (div_pos hb h2).le]; field_simp⟩
private lemma col_eq {n : ℕ} {A B : Mat (n+1)} (hA : goodWeight A) (hB : B.PosDef) (i : Fin n) :
    (A 0 0+A i.succ 0)*pivot A B*lowerCol A B i=B i.succ 0 := by
  unfold lowerCol
  field_simp [hA.2.2 0 i.succ (Fin.succ_pos i),(positive_pivot hA hB).1.ne']
private lemma assemble_rule {n : ℕ} (A B : Mat (n+1)) (hA : goodWeight A) (hB : B.PosDef)
    (ih : equation (tailM A) (solve n (tailM A) (residual A B))=residual A B) :
    equation A (solve (n+1) A B)=B := by
  ext i j
  rw [equation_entry,Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [solve,←two_mul,←pow_two]
    nlinarith [(positive_pivot hA hB).2]
  · simp [solve]
    have hs := col_eq hA hB j
    have hsA := hA.1.apply 0 j.succ
    have hsB := hB.isHermitian.apply 0 j.succ
    simp only [star_trivial] at hsB
    rw [← hsA,← hsB]
    exact hs
  · simp [solve]
    nlinarith only [col_eq hA hB i]
  · simp only [solve,Matrix.of_apply,Fin.cases_zero,Fin.cases_succ]
    have hx := congrArg (fun M : Mat n => M i j) ih
    rw [equation_entry] at hx
    change (∑ k,(A i.succ k.succ+A k.succ j.succ)*(solve n (tailM A) (residual A B)) i k*
      (solve n (tailM A) (residual A B)) j k) =
      B i.succ j.succ-(A i.succ 0+A j.succ 0)*lowerCol A B i*lowerCol A B j at hx
    rw [hx]
    have hs := hA.1.apply 0 j.succ
    nlinarith only [congrArg (fun a : ℝ => (A i.succ 0+a)*lowerCol A B i*lowerCol A B j) hs]
private lemma assemble_lower {n : ℕ} (A B : Mat (n+1)) (hp : 0<pivot A B)
    (ih : lowerPositive (solve n (tailM A) (residual A B))) : lowerPositive (solve (n+1) A B) := by
  constructor
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [solve]
    · simp
    · simpa [solve] using ih.1 _ _
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [solve] using hp
    · simpa [solve] using ih.2 i
end OMA.S_mo_248693

namespace OMA.S_mo_248693
open Matrix
private lemma tail_lower {n : ℕ} {X : Mat (n+1)} (hx : lowerPositive X) : lowerPositive (tailM X) :=
  ⟨fun i j h => hx.1 i.succ j.succ (Fin.succ_lt_succ_iff.mpr h),fun i => hx.2 i.succ⟩
lemma lower_injective (n : ℕ) (A X Y : Mat n) (hA : goodWeight A)
    (hx : lowerPositive X) (hy : lowerPositive Y) (he : equation A X=equation A Y) : X=Y := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    have hentry (i j : Fin (n+1)) := congrArg (fun M : Mat (n+1) => M i j) he
    have hrow (i : Fin (n+1)) :
        (A i 0+A 0 0)*X i 0*X 0 0=(A i 0+A 0 0)*Y i 0*Y 0 0 := by
      have hh := hentry i 0
      change equation A X i 0=equation A Y i 0 at hh
      rw [equation_entry,equation_entry,Fin.sum_univ_succ,Fin.sum_univ_succ] at hh
      simpa [fun k : Fin n => hx.1 0 k.succ (Fin.succ_pos k),fun k : Fin n => hy.1 0 k.succ (Fin.succ_pos k)] using hh
    have h00 : X 0 0=Y 0 0 := by
      have e := hrow 0
      rw [mul_assoc,mul_assoc] at e
      have e' := mul_left_cancel₀ (show A 0 0+A 0 0≠0 by linarith [hA.2.1 0]) e
      nlinarith only [e',hx.2 0,hy.2 0]
    have hcol (i : Fin n) : X i.succ 0=Y i.succ 0 := by
      have e := hrow i.succ
      rw [h00] at e
      have e' := mul_right_cancel₀ (hy.2 0).ne' e
      exact mul_left_cancel₀ (by simpa [add_comm] using hA.2.2 0 i.succ (Fin.succ_pos i)) e'
    have htail : tailM X=tailM Y := by
      apply ih (tailM A) _ _ (tail_good hA) (tail_lower hx) (tail_lower hy)
      ext i j
      have e := hentry i.succ j.succ
      change equation A X i.succ j.succ=equation A Y i.succ j.succ at e
      rw [equation_entry,equation_entry,Fin.sum_univ_succ,Fin.sum_univ_succ,hcol i,hcol j] at e
      rw [equation_entry,equation_entry]
      exact add_left_cancel e
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · exact h00
    · rw [hx.1 _ _ (Fin.succ_pos j),hy.1 _ _ (Fin.succ_pos j)]
    · exact hcol i
    · exact congrArg (fun M : Mat n => M i j) htail
end OMA.S_mo_248693

open OMA.S_mo_248693
theorem OMA.solution : type_of% @OMA.S_mo_248693.main := by
  refine ⟨fun _ => lift_equiv,?_⟩
  intro n
  induction n with
  | zero =>
    intro A B _ _
    refine ⟨⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩,?_,?_⟩
    · ext i; exact Fin.elim0 i
    · intro X _ _; ext i; exact Fin.elim0 i
  | succ n ih =>
    intro A B hA hB
    obtain ⟨hl,he,_⟩ := ih (tailM A) (residual A B) (tail_good hA) (residual_pos A B hA hB)
    have hL := assemble_lower A B (positive_pivot hA hB).1 hl
    have hE := assemble_rule A B hA hB he
    exact ⟨hL,hE,fun X hx h => lower_injective _ A X _ hA hx hL (h.trans hE.symm)⟩
