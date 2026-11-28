import OMAStatements.S_mo_262273

/-!
# The matching formula for Trummer's determinant

Source: Jeannette, https://mathoverflow.net/questions/262273 (CC BY-SA 3.0).
Credit: @connoranderson.

Border expansion reduces the determinant to a quadratic form in the
reciprocal differences from the first vertex. Partial fractions and both
adjugate identities cancel the off-diagonal part. Each diagonal cofactor
deletes a partner for the first vertex, which gives the matching sum.
On the unit circle a common factor makes every even-order summand positive.
-/

namespace OMA.S_mo_262273
open Matrix Finset

lemma det_border {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (h : M 0 0 = 0) :
    M.det = - ∑ i : Fin n, ∑ j : Fin n,
      M 0 i.succ * (M.submatrix Fin.succ Fin.succ).adjugate i j * M j.succ 0 := by
  classical
  cases n with
  | zero => simpa [Matrix.det_fin_one] using h
  | succ n =>
    rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ,h]
    simp only [mul_zero,zero_mul,zero_add,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.det_succ_column_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have he : ((M.submatrix Fin.succ i.succ.succAbove).submatrix j.succAbove Fin.succ) =
        (M.submatrix Fin.succ Fin.succ).submatrix j.succAbove i.succAbove := by
      ext a b
      simp [Matrix.submatrix_apply,Fin.succ_succAbove_succ]
    rw [he]
    simp only [Matrix.submatrix_apply,Fin.succ_succAbove_zero,Fin.val_succ,pow_add,pow_succ]
    ring
end OMA.S_mo_262273

namespace OMA.S_mo_262273

open Finset

private lemma cancel_terms {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ)
    (hr : ∀ i j, i ≠ j → t i * t j = (t i - t j) * C i j) :
    (∑ i, ∑ j, t j * C.adjugate j i * t i) = ∑ i, (t i)^2 * C.adjugate i i := by
  classical
  have hdecomp (i j : Fin n) :
      t j * C.adjugate j i * t i =
        (if i = j then t i ^ 2 * C.adjugate i i else 0) +
        (t i - t j) * C i j * C.adjugate j i := by
    by_cases h : i = j
    · subst j
      simp only [if_true, sub_self, zero_mul, add_zero]
      ring
    · rw [if_neg h,zero_add,← hr i j h]
      ring
  have hrow (i : Fin n) : ∑ j, C i j * C.adjugate j i = C.det := by
    have e := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i i) C.mul_adjugate
    simpa [Matrix.mul_apply,Matrix.one_apply] using e
  have hcol (j : Fin n) : ∑ i, C i j * C.adjugate j i = C.det := by
    have e := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M j j) C.adjugate_mul
    simpa [Matrix.mul_apply,Matrix.one_apply,mul_comm] using e
  simp_rw [hdecomp,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  suffices hzero : (∑ i, ∑ j, (t i - t j) * C i j * C.adjugate j i) = 0 by
    rw [hzero,add_zero]
  simp_rw [sub_mul,Finset.sum_sub_distrib,mul_assoc]
  simp_rw [← Finset.mul_sum,hrow]
  rw [Finset.sum_comm (f:=fun i j => t j * (C i j * C.adjugate j i))]
  simp_rw [← Finset.mul_sum,hcol,sub_self]

private lemma det_step {n : ℕ} (z : Fin (n+2) → ℂ) (hz : Function.Injective z) :
    (trummer z).det = ∑ j : Fin (n+1), ((z 0-z j.succ)⁻¹)^2 *
      (trummer (fun i => z (j.succAbove i).succ)).det := by
  classical
  let t (i : Fin (n+1)) := (z 0-z i.succ)⁻¹
  let C := trummer (fun i : Fin (n+1) => z i.succ)
  have hdist (i : Fin (n+1)) : z 0 - z i.succ ≠ 0 :=
    sub_ne_zero.mpr (hz.ne (Fin.succ_ne_zero i).symm)
  have hr (i j : Fin (n+1)) (h : i ≠ j) : t i * t j = (t i-t j) * C i j := by
    change (z 0-z i.succ)⁻¹ * (z 0-z j.succ)⁻¹ =
      ((z 0-z i.succ)⁻¹-(z 0-z j.succ)⁻¹) * (z i.succ-z j.succ)⁻¹
    have hdist' : z i.succ-z j.succ ≠ 0 := sub_ne_zero.mpr (hz.ne (Fin.succ_injective _ |>.ne h))
    field_simp [hdist,hdist']
    ring
  have he := det_border (trummer z) (by simp [trummer])
  have hn (j : Fin (n+1)) : (trummer z) j.succ 0 = -(t j) := by
    change (z j.succ-z 0)⁻¹ = -(z 0-z j.succ)⁻¹
    rw [← neg_sub,inv_neg]
  simp_rw [hn,mul_neg,Finset.sum_neg_distrib,neg_neg] at he
  change (trummer z).det = ∑ i, ∑ j, t i * C.adjugate i j * t j at he
  rw [he,Finset.sum_comm,cancel_terms C t hr]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, ← two_mul, pow_mul, neg_one_sq,one_pow,one_mul]
  rfl

end OMA.S_mo_262273

namespace OMA.S_mo_262273

private lemma matching_formula : ∀ (n : ℕ) (z : Fin n → ℂ), Function.Injective z →
    (trummer z).det = ∑ p : Pairing n, pairWeight n z p
  | 0, z, _ => by
    change (trummer z).det = ∑ _p : Unit, (1 : ℂ)
    simp
  | 1, z, _ => by
    calc
      (trummer z).det = 0 := by simp [trummer]
      _ = _ := (Finset.sum_eq_zero (fun (p : Pairing 1) _ => (show False from nomatch p).elim)).symm
  | n+2, z, hz => by
    rw [det_step z hz]
    change _ = ∑ p : Fin (n+1) × Pairing n, ((z 0-z p.1.succ)⁻¹)^2 *
      pairWeight n (fun i => z (p.1.succAbove i).succ) p.2
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    rw [← Finset.mul_sum]
    congr 1
    exact matching_formula n _ (hz.comp ((Fin.succ_injective _).comp j.succAbove_right_injective))

end OMA.S_mo_262273

namespace OMA.S_mo_262273

open scoped ComplexConjugate

private lemma unit_pair (a b : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (hab : a ≠ b) :
    ∃ r : ℝ, 0 < r ∧ -(a*b) * ((a-b)⁻¹)^2 = (r : ℂ) := by
  have ha' : Complex.normSq a = 1 := by simp [Complex.normSq_eq_norm_sq,ha]
  have hb' : Complex.normSq b = 1 := by simp [Complex.normSq_eq_norm_sq,hb]
  have hca : conj a = a⁻¹ := by simp [Complex.inv_def,ha']
  have hcb : conj b = b⁻¹ := by simp [Complex.inv_def,hb']
  have hna : a ≠ 0 := fun h => by simp [h] at ha
  have hnb : b ≠ 0 := fun h => by simp [h] at hb
  have hd := sub_ne_zero.mpr hab
  have hnorm : (Complex.normSq (a-b) : ℂ) = -(a-b)^2/(a*b) := by
    rw [← Complex.mul_conj,map_sub,hca,hcb]
    field_simp
    ring
  refine ⟨_, inv_pos.mpr (Complex.normSq_pos.mpr hd), ?_⟩
  rw [Complex.ofReal_inv,hnorm]
  field_simp

private lemma even_pairing (k : ℕ) : Nonempty (Pairing (2*k)) := by
  induction k with
  | zero => exact ⟨()⟩
  | succ k ih => exact ⟨(0,Classical.choice ih)⟩

private lemma circle_term (k : ℕ) (z : Fin (2*k) → ℂ) (hz : Function.Injective z)
    (hu : ∀ i, ‖z i‖=1) (p : Pairing (2*k)) :
    ∃ r : ℝ, 0 < r ∧ (-1 : ℂ)^k * (∏ i, z i) * pairWeight (2*k) z p = (r : ℂ) := by
  induction k with
  | zero => exact ⟨1,by norm_num,by simp [pairWeight]⟩
  | succ k ih =>
    obtain ⟨j,p⟩ := p
    let z' (i : Fin (2*k)) := z (j.succAbove i).succ
    obtain ⟨u,hu',eu⟩ := ih z' (hz.comp ((Fin.succ_injective _).comp j.succAbove_right_injective))
      (fun i => hu _) p
    obtain ⟨v,hv,ev⟩ := unit_pair _ _ (hu 0) (hu j.succ) (hz.ne (Fin.succ_ne_zero j).symm)
    refine ⟨v*u,mul_pos hv hu',?_⟩
    rw [Complex.ofReal_mul,← ev,← eu]
    change (-1 : ℂ)^(k+1) * (∏ i : Fin (2*k+2), z i) *
      (((z 0-z j.succ)⁻¹)^2 * pairWeight (2*k) z' p) = _
    have hprod : (∏ i : Fin (2*k+2), z i) =
        z 0 * (z j.succ * ∏ i, z' i) := by
      rw [Fin.prod_univ_succ (n:=2*k+1) (fun i => z i)]
      rw [Fin.prod_univ_succAbove (n:=2*k) (fun i => z i.succ) j]
    rw [hprod,pow_succ]
    dsimp only [z']
    ring

private lemma circle_nonsingular (k : ℕ) (z : Fin (2*k) → ℂ) (hz : Function.Injective z)
    (hu : ∀ i, ‖z i‖=1) : (trummer z).det ≠ 0 := by
  classical
  choose r hr he using circle_term k z hz hu
  let _ := even_pairing k
  have hpos : 0 < ∑ p : Pairing (2*k), r p := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have h : (-1:ℂ)^k * (∏ i, z i) * (trummer z).det = ((∑ p, r p : ℝ) : ℂ) := by
    rw [matching_formula _ _ hz,Finset.mul_sum,Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun p _ => he p
  intro hzero
  rw [hzero,mul_zero] at h
  exact hpos.ne' (by exact_mod_cast h.symm)

end OMA.S_mo_262273

namespace OMA.S_mo_262273

private lemma no_odd_pairing (k : ℕ) : Pairing (2*k+1) → False := by
  induction k with
  | zero => exact Empty.elim
  | succ k ih => exact fun p => ih p.2

private lemma odd_det (k : ℕ) (z : Fin (2*k+1) → ℂ) (hz : Function.Injective z) :
    (trummer z).det = 0 := by
  rw [matching_formula _ _ hz]
  exact Finset.sum_eq_zero fun p _ => (no_odd_pairing k p).elim

end OMA.S_mo_262273

theorem OMA.solution : type_of% @OMA.S_mo_262273.main :=
  ⟨OMA.S_mo_262273.matching_formula, OMA.S_mo_262273.odd_det, OMA.S_mo_262273.circle_nonsingular⟩
