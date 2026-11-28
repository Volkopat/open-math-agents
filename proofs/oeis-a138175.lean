import OMAStatements.S_oeis_a138175
import Mathlib

namespace OMA.S_oeis_a138175

open PowerSeries

noncomputable def fi : ℕ → ℚ⟦X⟧
  | 0 => 0
  | k + 1 => X + fi k ^ 3

lemma fi_X : ∀ k, (X : ℚ⟦X⟧) ∣ fi k := by
  intro k
  induction k with
  | zero => simp [fi]
  | succ k ih => exact dvd_add dvd_rfl (dvd_pow ih (by norm_num))

lemma fi_d : ∀ k, (X : ℚ⟦X⟧) ^ (k + 1) ∣ fi (k + 1) - fi k := by
  intro k
  induction k with
  | zero => simp [fi]
  | succ k ih =>
    have e : fi (k + 2) - fi (k + 1) =
        (fi (k + 1) - fi k) * (fi (k + 1) ^ 2 + fi (k + 1) * fi k + fi k ^ 2) := by
      show X + fi (k + 1) ^ 3 - (X + fi k ^ 3) = _
      ring
    rw [e, pow_succ]
    exact mul_dvd_mul ih (dvd_add (dvd_add (dvd_pow (fi_X _) (by norm_num))
      (Dvd.dvd.mul_right (fi_X _) _)) (dvd_pow (fi_X _) (by norm_num)))

lemma fi_stab (n : ℕ) : ∀ m, n ≤ m → coeff n (fi m) = coeff n (fi n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [← ih]
    have h1 : (X : ℚ⟦X⟧) ^ (n + 1) ∣ fi (m + 1) - fi m :=
      dvd_trans (pow_dvd_pow _ (by omega)) (fi_d m)
    have := (X_pow_dvd_iff.mp h1) n (by omega)
    rw [map_sub] at this
    linarith

noncomputable def Ts : ℚ⟦X⟧ := PowerSeries.mk fun n => coeff n (fi n)

lemma Ts_dvd (n : ℕ) : (X : ℚ⟦X⟧) ^ (n + 1) ∣ Ts - fi n := by
  rw [X_pow_dvd_iff]
  intro j hj
  rw [map_sub, Ts, coeff_mk, fi_stab j n (by omega)]
  simp

lemma Ts_eq : Ts - Ts ^ 3 = X := by
  ext n
  have h3 : (X : ℚ⟦X⟧) ^ (n + 1) ∣ Ts ^ 3 - fi n ^ 3 :=
    dvd_trans (Ts_dvd n) (sub_dvd_pow_sub_pow _ _ 3)
  have h3' := (X_pow_dvd_iff.mp h3) n (by omega)
  rw [map_sub] at h3'
  have hs : coeff n (fi (n + 1)) = coeff n Ts := by
    rw [fi_stab n (n + 1) (by omega), Ts, coeff_mk]
  have hs2 : coeff n (fi (n + 1)) = coeff n X + coeff n (fi n ^ 3) := by
    show coeff n (X + fi n ^ 3) = _
    rw [map_add]
  rw [map_sub]
  linarith

lemma Ts_zero : coeff 0 Ts = 0 := by simp [Ts, fi]

lemma exists_TG : ∃ T G : ℚ⟦X⟧, T - T ^ 3 = X ∧ coeff 0 T = 0 ∧ G * (1 - 2 * T) = 1 := by
  refine ⟨Ts, (1 - 2 * Ts)⁻¹, Ts_eq, Ts_zero, ?_⟩
  apply PowerSeries.inv_mul_cancel
  have h := Ts_zero
  rw [coeff_zero_eq_constantCoeff_apply] at h
  simp [h]

lemma coefs (T G : ℚ⟦X⟧) (h : T - T ^ 3 = X) (h0 : coeff 0 T = 0)
    (hG : G * (1 - 2 * T) = 1) :
    coeff 0 G = 1 ∧ coeff 1 G = 2 ∧ coeff 2 G = 4 ∧ coeff 3 G = 10 := by
  have e1 := congrArg (coeff 1) h
  have e2 := congrArg (coeff 2) h
  have e3 := congrArg (coeff 3) h
  have hC : (C (2:ℚ) : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have hG' : G = 1 + C (2:ℚ) * (T * G) := by rw [hC]; linear_combination hG
  have g0 := congrArg (coeff 0) hG'
  have g1 := congrArg (coeff 1) hG'
  have g2 := congrArg (coeff 2) hG'
  have g3 := congrArg (coeff 3) hG'
  simp [pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ, h0, coeff_one, coeff_X] at e1 e2 e3 g0 g1 g2 g3
  have h0' : constantCoeff T = 0 := by rwa [coeff_zero_eq_constantCoeff_apply] at h0
  rw [h0'] at g0
  have c0 : constantCoeff G = 1 := by linarith
  have c1 : coeff 1 G = 2 := by rw [g1, e1, c0]; norm_num
  have c3T : coeff 3 T = 1 := by rw [e1] at e3; linarith
  have c2 : coeff 2 G = 4 := by rw [g2, e1, e2, c0, c1]; norm_num
  have c3 : coeff 3 G = 10 := by rw [g3, e1, e2, c3T, c0, c1, c2]; norm_num
  refine ⟨?_, c1, c2, c3⟩
  rw [coeff_zero_eq_constantCoeff_apply]; exact c0

end OMA.S_oeis_a138175

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a138175.main) := by
  intro H
  obtain ⟨T, G, h, h0, hG⟩ := OMA.S_oeis_a138175.exists_TG
  obtain ⟨c0, c1, c2, c3⟩ := OMA.S_oeis_a138175.coefs T G h h0 hG
  have := H T G h h0 hG 3 le_rfl
  norm_num [c0, c1, c2, c3] at this
