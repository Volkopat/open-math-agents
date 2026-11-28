import OMAStatements.S_mo_191942
import Mathlib

namespace OMA.Mo191942

noncomputable def aFn (t : ℝ) : ℝ := (1 : ℝ) / 4 + t ^ 4

noncomputable def qFn (t : ℝ) : ℝ := (1 : ℝ) / 2 + (19 : ℝ) / 16 * t ^ 2 + (9 : ℝ) / 16 * t ^ 4

noncomputable def gFn (t : ℝ) : ℝ := qFn t - (aFn t - 1) * t

lemma aFn_pos (t : ℝ) : 0 < aFn t := by
  unfold aFn
  positivity

lemma aFn_ne_zero (t : ℝ) : aFn t ≠ 0 := (aFn_pos t).ne'

lemma qFn_pos (t : ℝ) : 0 < qFn t := by
  unfold qFn
  positivity

noncomputable def fMap (p : ℝ × ℝ) : ℝ × ℝ := (p.2, aFn p.2 * p.1 + gFn p.2)

noncomputable def fInv (p : ℝ × ℝ) : ℝ × ℝ := ((p.2 - gFn p.1) / aFn p.1, p.1)

lemma continuous_aFn : Continuous aFn := by
  unfold aFn
  fun_prop

lemma continuous_qFn : Continuous qFn := by
  unfold qFn
  fun_prop

lemma continuous_gFn : Continuous gFn := by
  unfold gFn
  exact continuous_qFn.sub ((continuous_aFn.sub continuous_const).mul continuous_id)

noncomputable def hProd : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := fMap
  invFun := fInv
  left_inv p := by
    ext <;> simp only [fMap, fInv]
    · field_simp [aFn_ne_zero p.2]
      ring
  right_inv p := by
    ext <;> simp only [fMap, fInv]
    · field_simp [aFn_ne_zero p.1]
      ring
  continuous_toFun := by
    unfold fMap
    exact continuous_snd.prodMk
      (((continuous_aFn.comp continuous_snd).mul continuous_fst).add
        (continuous_gFn.comp continuous_snd))
  continuous_invFun := by
    unfold fInv
    exact ((continuous_snd.sub (continuous_gFn.comp continuous_fst)).div
      (continuous_aFn.comp continuous_fst) (fun p => aFn_ne_zero p.1)).prodMk continuous_fst

lemma hProd_no_fixed (p : ℝ × ℝ) : hProd p ≠ p := by
  intro hp
  have h1 : p.2 = p.1 := congrArg Prod.fst hp
  have h2 : aFn p.2 * p.1 + gFn p.2 = p.2 := congrArg Prod.snd hp
  rw [h1] at h2
  have hq : qFn p.1 = 0 := by
    unfold gFn at h2
    linarith
  linarith [qFn_pos p.1]

lemma hProd_step1 : hProd (0, 1) = (1, 2) := by
  change fMap (0, 1) = (1, 2)
  ext
  · simp only [fMap]
  · simp only [fMap, aFn, gFn, qFn]; norm_num

lemma hProd_step2 : hProd (1, 2) = (2, 0) := by
  change fMap (1, 2) = (2, 0)
  ext
  · simp only [fMap]
  · simp only [fMap, aFn, gFn, qFn]; norm_num

lemma hProd_step3 : hProd (2, 0) = (0, 1) := by
  change fMap (2, 0) = (0, 1)
  ext
  · simp only [fMap]
  · simp only [fMap, aFn, gFn, qFn]; norm_num

lemma hProd_iter3 : hProd^[3] (0, 1) = (0, 1) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  rw [hProd_step1, hProd_step2, hProd_step3]

def fin2Prod : (Fin 2 → ℝ) ≃ₜ (ℝ × ℝ) where
  toFun v := (v 0, v 1)
  invFun p := ![p.1, p.2]
  left_inv v := by
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    ext <;> rfl
  continuous_toFun := (continuous_apply 0).prodMk (continuous_apply 1)
  continuous_invFun := continuous_pi fun i => by
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd

noncomputable def euclidProd : EuclideanSpace ℝ (Fin 2) ≃ₜ (ℝ × ℝ) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans fin2Prod

noncomputable def hPlane : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  (euclidProd.trans hProd).trans euclidProd.symm

lemma hPlane_apply (x : EuclideanSpace ℝ (Fin 2)) :
    hPlane x = euclidProd.symm (hProd (euclidProd x)) := rfl

lemma hPlane_iter (n : ℕ) (p : ℝ × ℝ) :
    hPlane^[n] (euclidProd.symm p) = euclidProd.symm (hProd^[n] p) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hPlane_apply]
    simp

lemma hPlane_no_fixed (x : EuclideanSpace ℝ (Fin 2)) : hPlane x ≠ x := by
  intro hx
  apply hProd_no_fixed (euclidProd x)
  have h1 := congrArg euclidProd hx
  simpa [hPlane_apply] using h1

lemma hPlane_minimalPeriod : Function.minimalPeriod hPlane (euclidProd.symm (0, 1)) = 3 := by
  have hper : Function.IsPeriodicPt hPlane 3 (euclidProd.symm (0, 1)) := by
    change hPlane^[3] (euclidProd.symm (0, 1)) = euclidProd.symm (0, 1)
    rw [hPlane_iter, hProd_iter3]
  have hdvd : Function.minimalPeriod hPlane (euclidProd.symm (0, 1)) ∣ 3 :=
    Function.IsPeriodicPt.minimalPeriod_dvd hper
  have hpos : 0 < Function.minimalPeriod hPlane (euclidProd.symm (0, 1)) :=
    Function.minimalPeriod_pos_of_mem_periodicPts (Function.mem_periodicPts.mpr ⟨3, by decide, hper⟩)
  have hne1 : Function.minimalPeriod hPlane (euclidProd.symm (0, 1)) ≠ 1 := by
    intro h1
    have hper1 := Function.isPeriodicPt_minimalPeriod hPlane (euclidProd.symm (0, 1))
    rw [h1] at hper1
    have hfix : hPlane (euclidProd.symm (0, 1)) = euclidProd.symm (0, 1) := by
      simpa [Function.IsPeriodicPt, Function.IsFixedPt] using hper1
    exact hPlane_no_fixed _ hfix
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvd with h1 | h3
  · exact absurd h1 hne1
  · exact h3

end OMA.Mo191942

theorem OMA.solution : type_of% @OMA.S_mo_191942.main :=
  ⟨OMA.Mo191942.hPlane, ⟨OMA.Mo191942.euclidProd.symm (0, 1), OMA.Mo191942.hPlane_minimalPeriod⟩,
    OMA.Mo191942.hPlane_no_fixed⟩
