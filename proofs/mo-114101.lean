import OMAStatements.S_mo_114101
import Mathlib

noncomputable section

namespace OMA.CauchySignMatrix

open Finset OMA.S_mo_114101

private def toggle (i j : Fin 256) : Fin 256 :=
  ⟨i.val ^^^ j.val, Nat.xor_lt_two_pow (n := 8) i.isLt j.isLt⟩

private def translate (i : Fin 256) : Fin 256 ≃ Fin 256 :=
  have twice : Function.Involutive (toggle i) := by
    intro j
    apply Fin.ext
    change i.val ^^^ (i.val ^^^ j.val) = j.val
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  ⟨toggle i, toggle i, twice, twice⟩

private def sign (i : Fin 256) (l : Fin 8) : ℚ :=
  if i.val.testBit l.val then -1 else 1

private def weight (i : Fin 256) : ℚ := ∏ l : Fin 8, sign i l

private theorem sign_mul (i j : Fin 256) (l : Fin 8) :
    sign i l * sign j l = sign (toggle i j) l := by
  simp only [sign, toggle, Nat.testBit_xor]
  cases i.val.testBit l.val <;> cases j.val.testBit l.val <;> norm_num [Bool.xor]

private theorem weight_mul (i j : Fin 256) :
    weight i * weight j = weight (toggle i j) := by
  simp only [weight, ← Finset.prod_mul_distrib, sign_mul]

private def row (j : Fin 256) : ℚ :=
  (∑ T ∈ (univ : Finset (Fin 8)).powersetCard 2, ∏ l ∈ T, (1-sign j l/4))⁻¹

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem row_negative : (∑ j : Fin 256, row j * weight j) < 0 := by
  decide +kernel

private def sample (i : Fin 256) (l : Fin 8) : ℝ := (sign i l : ℝ)/2

private def vector (i : Fin 256) : ℝ := weight i

private theorem entry (i j : Fin 256) :
    cauchy 2 sample i j = (row (toggle i j) : ℝ) := by
  unfold cauchy elementary row
  push_cast
  apply congrArg Inv.inv
  apply sum_congr rfl
  intro T _
  apply prod_congr rfl
  intro l _
  have h := congrArg (fun q : ℚ => (q : ℝ)) (sign_mul i j l)
  push_cast at h
  rw [← h]
  unfold sample
  ring

private def eigenvalue : ℝ := ∑ j : Fin 256, (row j : ℝ) * vector j

private theorem row_form (i : Fin 256) :
    vector i * (∑ j : Fin 256, cauchy 2 sample i j * vector j) = eigenvalue := by
  rw [mul_sum]
  calc
    _ = ∑ j : Fin 256, (row (toggle i j) : ℝ) * vector (toggle i j) := by
      apply sum_congr rfl
      intro j _
      have hw := congrArg (fun q : ℚ => (q : ℝ)) (weight_mul i j)
      push_cast at hw
      simp only [entry, vector]
      rw [← hw]
      ring
    _ = eigenvalue := (translate i).sum_comp (fun j => (row j : ℝ) * vector j)

theorem witness : type_of% @OMA.S_mo_114101.main := by
  refine ⟨256, 8, 2, sample, by decide, by decide, by decide, ?_, ?_⟩
  · intro i l
    unfold sample sign
    split <;> norm_num
  · intro h
    have quadratic := h.dotProduct_mulVec_nonneg vector
    simp only [dotProduct, Matrix.mulVec, star_trivial, row_form, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul] at quadratic
    have he : eigenvalue < 0 := by
      have cast : ((∑ j : Fin 256, row j * weight j : ℚ) : ℝ) < 0 := by
        exact_mod_cast row_negative
      simpa [eigenvalue, vector] using cast
    have hp : (0 : ℝ) < ((256 : ℕ) : ℝ) := by norm_num
    exact (not_lt_of_ge quadratic) (mul_neg_of_pos_of_neg hp he)

end OMA.CauchySignMatrix

theorem OMA.solution : type_of% @OMA.S_mo_114101.main :=
  OMA.CauchySignMatrix.witness