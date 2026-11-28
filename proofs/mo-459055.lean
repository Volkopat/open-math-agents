import OMAStatements.S_mo_459055
import Mathlib

namespace OMA.S_mo_459055
open Polynomial

lemma kk (k : ℕ) (hk : 2 ≤ k) : ((k - 1 : ℕ) : ℝ) = (k - 1 : ℝ) := by
  rw [Nat.cast_sub (by omega)]; simp

lemma factor_same (k : ℕ) (hk : 2 ≤ k) (μ : ℝ) (r : Fin k) :
    ∑ b : Fin k, C (edit μ r b) * (if r ≠ b then (X : ℝ[X]) else 1) = C (1-μ) + C μ * X := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  have : ∀ b ∈ Finset.univ.erase r, C (edit μ r b) * (if r ≠ b then (X : ℝ[X]) else 1) = C (μ/(k-1:ℝ)) * X := by
    intro b hb
    have hb' : b ≠ r := Finset.ne_of_mem_erase hb
    simp [edit, hb', Ne.symm hb']
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ r)]
  simp only [edit, if_true, ne_eq, not_true_eq_false, if_false, mul_one, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : ((k - 1 : ℕ) : ℝ[X]) * (C (μ/(k-1:ℝ)) * X) = C μ * X := by
    have hne : ((k:ℝ) - 1) ≠ 0 := by
      have : (2:ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have : ((k - 1 : ℕ) : ℝ[X]) = C (((k - 1 : ℕ) : ℝ)) := by simp
    rw [this, ← mul_assoc, ← C_mul, kk k hk]
    congr 2
    field_simp
  rw [h1]

lemma factor_diff (k : ℕ) (hk : 2 ≤ k) (μ : ℝ) (a r : Fin k) (har : a ≠ r) :
    ∑ b : Fin k, C (edit μ a b) * (if r ≠ b then (X : ℝ[X]) else 1) =
      C (μ/(k-1:ℝ)) + C (1 - μ/(k-1:ℝ)) * X := by
  have hne : ((k:ℝ) - 1) ≠ 0 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  have hmem : a ∈ Finset.univ.erase r := Finset.mem_erase.2 ⟨har, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ hmem]
  have : ∀ b ∈ (Finset.univ.erase r).erase a, C (edit μ a b) * (if r ≠ b then (X : ℝ[X]) else 1) = C (μ/(k-1:ℝ)) * X := by
    intro b hb
    have hb1 : b ≠ a := Finset.ne_of_mem_erase hb
    have hb2 : b ≠ r := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hb)
    simp [edit, hb1, hb2, Ne.symm hb1, Ne.symm hb2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem hmem,
    Finset.card_erase_of_mem (Finset.mem_univ r)]
  simp only [edit, if_true, ne_eq, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, har, if_false,
    Ne.symm har, not_false_eq_true, not_true_eq_false, mul_one, if_neg]
  have : ((k - 1 - 1 : ℕ) : ℝ[X]) = C (((k - 1 - 1 : ℕ) : ℝ)) := by simp
  rw [this]
  have e2 : (((k - 1 - 1 : ℕ) : ℝ)) = (k:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [e2]
  have e3 : (1 - μ) + ((k:ℝ) - 2) * (μ/(k-1:ℝ)) = 1 - μ/(k-1:ℝ) := by field_simp; ring
  have h : C (1-μ) * X + C ((k:ℝ)-2) * (C (μ/(k-1:ℝ)) * X) = C (1 - μ/(k-1:ℝ)) * X := by
    rw [← mul_assoc, ← C_mul, ← add_mul, ← C_add, e3]
  rw [h]

lemma G_eq (L k : ℕ) (hk : 2 ≤ k) (μ : ℝ) (ref old : Fin L → Fin k) :
    ∑ y : Fin L → Fin k, C (editMass μ old y) * (X : ℝ[X]) ^ (hammingDist ref y) =
      distanceLaw L k (hammingDist ref old) μ := by
  have h1 : ∀ y : Fin L → Fin k, C (editMass μ old y) * (X : ℝ[X]) ^ (hammingDist ref y) =
      ∏ i, (C (edit μ (old i) (y i)) * (if ref i ≠ y i then (X : ℝ[X]) else 1)) := by
    intro y
    rw [Finset.prod_mul_distrib, editMass, map_prod]
    congr 1
    rw [Finset.prod_ite, hammingDist]
    simp
  rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Fintype.prod_sum (fun i b => C (edit μ (old i) b) * (if ref i ≠ b then (X : ℝ[X]) else 1))]
  have h2 : ∀ i, ∑ b : Fin k, C (edit μ (old i) b) * (if ref i ≠ b then (X : ℝ[X]) else 1) =
      if old i = ref i then C (1-μ) + C μ * X else C (μ/(k-1:ℝ)) + C (1 - μ/(k-1:ℝ)) * X := by
    intro i
    by_cases h : old i = ref i
    · rw [if_pos h, h]; exact factor_same k hk μ (ref i)
    · rw [if_neg h]; exact factor_diff k hk μ _ _ h
  rw [Finset.prod_congr rfl (fun i _ => h2 i), Finset.prod_ite]
  simp only [Finset.prod_const]
  have c1 : (Finset.univ.filter fun i => ¬ old i = ref i).card = hammingDist ref old := by
    rw [hammingDist]; congr 1; ext i; simp [eq_comm]
  have c2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin L))) (fun i => old i = ref i)
  rw [c1] at c2 ⊢
  have c3 : (Finset.univ.filter fun i => old i = ref i).card = L - hammingDist ref old := by
    simp at c2; omega
  rw [c3, distanceLaw]

theorem sum_form (L k : ℕ) (hk : 2 ≤ k) (μ : ℝ) (ref old : Fin L → Fin k) (z : ℤ) :
    (∑ y : Fin L → Fin k, if (hammingDist ref old : ℤ) - hammingDist ref y = z
      then editMass μ old y else 0) =
    if z ≤ (hammingDist ref old : ℤ) then
      (distanceLaw L k (hammingDist ref old) μ).coeff (((hammingDist ref old : ℤ)-z).toNat)
    else 0 := by
  split_ifs with hz
  · rw [← G_eq L k hk μ ref old, Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro y _
    rw [coeff_C_mul, coeff_X_pow]
    by_cases h : (hammingDist ref old : ℤ) - hammingDist ref y = z
    · rw [if_pos h, if_pos (by omega), mul_one]
    · rw [if_neg h, if_neg (by omega), mul_zero]
  · apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    omega

end OMA.S_mo_459055

theorem OMA.solution : type_of% @OMA.S_mo_459055.main := by
  intro L k hk μ _ _ ref old z
  exact OMA.S_mo_459055.sum_form L k hk μ ref old z
