import OMAStatements.S_oeis_a289916
import Mathlib

open PowerSeries

namespace OMA.RoundedSeries

private def signed (n : ℕ) : ℤ :=
  (-1)^n * round (9*((n : ℚ)+1)/7)

private def F : ℤ⟦X⟧ := mk signed
private noncomputable def B : ℤ⟦X⟧ := invOfUnit F 1
private noncomputable def P : ℤ⟦X⟧ := 1 - C 2*X + X^2 - X^3 + X^4 - C 2*X^5 + X^6
private noncomputable def numerator : ℤ⟦X⟧ := (1+X)^2*(1+X^7)
private noncomputable def gap : ℤ⟦X⟧ := (1-X)*B

private theorem signed_seven (n : ℕ) : signed (n+7) + signed n = -9*((-1 : ℤ)^n) := by
  have h : 9*((↑(n+7) : ℚ)+1)/7 = 9*((n : ℚ)+1)/7 + (↑(9 : ℤ) : ℚ) := by
    push_cast
    ring
  unfold signed
  rw [h, round_add_intCast, pow_add]
  norm_num
  ring

set_option maxRecDepth 6000 in
private theorem rounded_identity : (1+X)*(1+X^7)*F = P := by
  rw [show (1+X)*(1+X^7)*F = F+X^1*F+X^7*F+X^8*F by ring]
  ext n
  simp only [map_add, map_sub, coeff_X_pow_mul', F, coeff_mk, P, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]
  rcases lt_or_ge n 8 with h | h
  · interval_cases n <;> decide +kernel
  · have h₀ : n ≠ 0 := by omega
    have h₁ : n ≠ 1 := by omega
    have h₂ : n ≠ 2 := by omega
    have h₃ : n ≠ 3 := by omega
    have h₄ : n ≠ 4 := by omega
    have h₅ : n ≠ 5 := by omega
    have h₆ : n ≠ 6 := by omega
    simp only [if_neg h₀, if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_neg h₆,
      if_pos (by omega : 1 ≤ n), if_pos (by omega : 7 ≤ n), if_pos h,
      mul_zero, add_zero, sub_zero]
    have hA := signed_seven (n-7)
    have hD := signed_seven (n-8)
    rw [show n-7+7=n by omega] at hA
    rw [show n-8+7=n-1 by omega] at hD
    calc
      _ = (signed n + signed (n-7)) + (signed (n-1) + signed (n-8)) := by ring
      _ = -9*((-1:ℤ)^(n-7)) + -9*((-1:ℤ)^(n-8)) := by rw [hA,hD]
      _ = 0 := by rw [show n-7=n-8+1 by omega, pow_succ]; ring

private theorem reciprocal_identity : (1-X^6)*gap = numerator+(X^2+X^5)*B := by
  have h0 : constantCoeff F = (1 : (ℤ)ˣ) := by
    change signed 0 = 1
    decide +kernel
  have hinv : F*B = 1 := mul_invOfUnit F 1 h0
  have hPB : P*B = (1+X)*(1+X^7) := by
    rw [← rounded_identity, mul_assoc, hinv, mul_one]
  have hPol : (1-X^6)*(1-X)-(X^2+X^5) = (1+X)*P := by
    unfold P
    rw [show C (2:ℤ) = (2 : ℤ⟦X⟧) by simp]
    ring
  have hB := congrArg (fun y : ℤ⟦X⟧ => y*B) hPol
  rw [sub_mul, mul_assoc (1+X), hPB] at hB
  unfold gap numerator
  linear_combination hB

private theorem gap_succ (n : ℕ) : coeff (n+1) gap = coeff (n+1) B - coeff n B := by
  simp [gap, sub_mul, coeff_succ_X_mul]

private theorem coefficient_step (n : ℕ) :
    coeff n gap = (if 6 ≤ n then coeff (n-6) gap else 0) + coeff n numerator +
      (if 2 ≤ n then coeff (n-2) B else 0) + (if 5 ≤ n then coeff (n-5) B else 0) := by
  have h := congrArg (coeff (R := ℤ) n) reciprocal_identity
  simp only [sub_mul, add_mul, one_mul, map_add, map_sub, coeff_X_pow_mul'] at h
  linarith

private theorem product_nonneg {P Q : ℤ⟦X⟧} (hP : ∀ n, 0 ≤ coeff n P)
    (hQ : ∀ n, 0 ≤ coeff n Q) (n : ℕ) : 0 ≤ coeff n (P*Q) := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hP i.1) (hQ i.2)

private theorem numerator_nonneg (n : ℕ) : 0 ≤ coeff n numerator := by
  have h₁ (m : ℕ) : 0 ≤ coeff m (1+X : ℤ⟦X⟧) := by
    simp only [map_add, coeff_one, coeff_X]
    split_ifs <;> omega
  have h₇ (m : ℕ) : 0 ≤ coeff m (1+X^7 : ℤ⟦X⟧) := by
    simp only [map_add, coeff_one, coeff_X_pow]
    split_ifs <;> omega
  unfold numerator
  rw [pow_two]
  exact product_nonneg (product_nonneg h₁ h₁) h₇ n

private theorem numerator_one : coeff 1 numerator = 2 := by
  rw [show numerator = 1 + C 2*X + X^2 + X^7 + C 2*X^8 + X^9 by
    unfold numerator; rw [show C (2:ℤ) = (2 : ℤ⟦X⟧) by simp]; ring]
  simp only [map_add, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]
  decide +kernel

private theorem positive (n : ℕ) : 0 < coeff n B ∧ 0 < coeff n gap := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · have hb : coeff 0 B = 1 := by
        rw [coeff_zero_eq_constantCoeff_apply]
        simp [B]
      constructor
      · omega
      · have hz : coeff 0 (X*B) = 0 := by simp [coeff_zero_eq_constantCoeff_apply]
        rw [gap, sub_mul, one_mul, map_sub, hz, sub_zero, hb]
        norm_num
    have hs := coefficient_step (n+1)
    have h₆ : 0 ≤ (if 6 ≤ n+1 then coeff (n+1-6) gap else 0) := by
      split_ifs with h
      · exact (ih _ (by omega)).2.le
      · exact le_rfl
    have h₅ : 0 ≤ (if 5 ≤ n+1 then coeff (n+1-5) B else 0) := by
      split_ifs with h
      · exact (ih _ (by omega)).1.le
      · exact le_rfl
    have hg : 0 < coeff (n+1) gap := by
      by_cases hn : n = 0
      · subst n
        change 0 < coeff 1 gap
        rw [coefficient_step 1, numerator_one]
        norm_num
      · have hp := (ih (n+1-2) (by omega)).1
        rw [if_pos (by omega : 2 ≤ n+1)] at hs
        linarith [numerator_nonneg (n+1)]
    have he := gap_succ n
    have hb := (ih n (by omega)).1
    exact ⟨by linarith, hg⟩

end OMA.RoundedSeries

open OMA.S_oeis_a289916 OMA.RoundedSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a289916.main := by
  apply strictMono_nat_of_lt_succ
  intro n
  change coeff n B < coeff (n+1) B
  have h := (positive (n+1)).2
  rw [gap_succ] at h
  linarith