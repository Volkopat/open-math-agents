import OMAStatements.S_oeis_a242396
import Mathlib

namespace OMA.A242396Proof

open OMA.S_oeis_a242396 PowerSeries

lemma rows_iff (n M : ℕ) (hn : 1 ≤ n) (h1 : 3 * M ^ 2 ≤ 4 * n ^ 2) (h2 : 4 * n ^ 2 < 3 * (M + 1) ^ 2) (k : ℤ) :
    RowMeetsCircle n k ↔ -(M : ℤ) - 1 ≤ k ∧ k ≤ M := by
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s0 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h1r : (3 : ℝ) * (M : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by exact_mod_cast h1
  have h2r : (4 : ℝ) * (n : ℝ) ^ 2 < 3 * ((M : ℝ) + 1) ^ 2 := by exact_mod_cast h2
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have sq : ∀ t : ℝ, (t * (Real.sqrt 3 / 2)) ^ 2 = 3 * t ^ 2 / 4 := by
    intro t; rw [mul_pow, div_pow, s3]; ring
  have hA : 0 ≤ ((M : ℝ) + 1) * (Real.sqrt 3 / 2) := by positivity
  have hh : 0 ≤ Real.sqrt 3 / 2 := by positivity
  constructor
  · rintro ⟨x, y, hxy, hy1, hy2⟩
    have hy : y ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg x]
    constructor
    · by_contra hk
      have hk' : k ≤ -(M : ℤ) - 2 := by omega
      have hkr : (k : ℝ) + 1 ≤ -((M : ℝ) + 1) := by
        have : (k : ℝ) ≤ -(M : ℝ) - 2 := by exact_mod_cast hk'
        linarith
      have h3 : ((k : ℝ) + 1) * (Real.sqrt 3 / 2) ≤ -((M : ℝ) + 1) * (Real.sqrt 3 / 2) :=
        mul_le_mul_of_nonneg_right hkr hh
      have h4 : ((M : ℝ) + 1) * (Real.sqrt 3 / 2) ≤ -y := by linarith
      have h5 : (((M : ℝ) + 1) * (Real.sqrt 3 / 2)) ^ 2 ≤ (-y) ^ 2 := pow_le_pow_left₀ hA h4 2
      rw [sq] at h5
      nlinarith
    · by_contra hk
      have hk' : (M : ℤ) + 1 ≤ k := by omega
      have hkr : (M : ℝ) + 1 ≤ k := by exact_mod_cast hk'
      have h3 : ((M : ℝ) + 1) * (Real.sqrt 3 / 2) ≤ (k : ℝ) * (Real.sqrt 3 / 2) :=
        mul_le_mul_of_nonneg_right hkr hh
      have h5 : (((M : ℝ) + 1) * (Real.sqrt 3 / 2)) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hA (by linarith) 2
      rw [sq] at h5
      nlinarith
  · rintro ⟨hk1, hk2⟩
    by_cases hk : 0 ≤ k
    · have hkr : (k : ℝ) ≤ M := by exact_mod_cast hk2
      have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk
      have hk2' : (k : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ hk0 hkr 2
      refine ⟨Real.sqrt ((n : ℝ) ^ 2 - ((k : ℝ) * (Real.sqrt 3 / 2)) ^ 2), (k : ℝ) * (Real.sqrt 3 / 2), ?_, le_refl _, ?_⟩
      · rw [Real.sq_sqrt]; ring
        rw [sq]; nlinarith
      · nlinarith
    · have hk' : k + 1 ≤ 0 := by omega
      have hkr : -(M : ℝ) - 1 ≤ k := by exact_mod_cast hk1
      have hk0 : -((k : ℝ) + 1) ≥ 0 := by
        have : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast hk'
        linarith
      have hk2' : (-((k : ℝ) + 1)) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ hk0 (by linarith) 2
      refine ⟨Real.sqrt ((n : ℝ) ^ 2 - (((k : ℝ) + 1) * (Real.sqrt 3 / 2)) ^ 2), ((k : ℝ) + 1) * (Real.sqrt 3 / 2), ?_, ?_, le_refl _⟩
      · rw [Real.sq_sqrt]; ring
        rw [sq]; nlinarith
      · nlinarith

lemma a_eq (n M : ℕ) (hn : 1 ≤ n) (h1 : 3 * M ^ 2 ≤ 4 * n ^ 2) (h2 : 4 * n ^ 2 < 3 * (M + 1) ^ 2) :
    a n = 2 * M + 2 := by
  unfold a
  have : Nat.card {k : ℤ // RowMeetsCircle n k} = Nat.card (Finset.Icc (-(M : ℤ) - 1) M) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl ℤ) (fun k => by simpa using rows_iff n M hn h1 h2 k)
  rw [this, Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc]
  omega

lemma a83 : a 83 = 192 := a_eq 83 95 (by norm_num) (by norm_num) (by norm_num)
lemma a84 : a 84 = 194 := a_eq 84 96 (by norm_num) (by norm_num) (by norm_num)
lemma a96 : a 96 = 222 := a_eq 96 110 (by norm_num) (by norm_num) (by norm_num)
lemma a97 : a 97 = 226 := a_eq 97 112 (by norm_num) (by norm_num) (by norm_num)

end OMA.A242396Proof

open OMA.A242396Proof OMA.S_oeis_a242396 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a242396.main) := by
  intro h
  have h97 := congrArg (coeff 97) h
  have e : (X * mk (fun n => (a (n + 1) : ℚ)) * (X ^ 14 - X ^ 13 - X + 1) : PowerSeries ℚ) =
      mk (fun n => (a (n + 1) : ℚ)) * X ^ 15 - mk (fun n => (a (n + 1) : ℚ)) * X ^ 14
        - mk (fun n => (a (n + 1) : ℚ)) * X ^ 2 + mk (fun n => (a (n + 1) : ℚ)) * X ^ 1 := by ring
  have hp : (-2 * X ^ 14 + 4 * X ^ 13 + 2 * X ^ 12 + 2 * X ^ 11 + 2 * X ^ 10 + 2 * X ^ 9 + 2 * X ^ 8 + 4 * X ^ 7 + 2 * X ^ 6 + 2 * X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + 2 * X ^ 2 + 4 * X : PowerSeries ℚ) = C (-2:ℚ) * X ^ 14 + C (4:ℚ) * X ^ 13 + C (2:ℚ) * X ^ 12 + C (2:ℚ) * X ^ 11 + C (2:ℚ) * X ^ 10 + C (2:ℚ) * X ^ 9 + C (2:ℚ) * X ^ 8 + C (4:ℚ) * X ^ 7 + C (2:ℚ) * X ^ 6 + C (2:ℚ) * X ^ 5 + C (2:ℚ) * X ^ 4 + C (2:ℚ) * X ^ 3 + C (2:ℚ) * X ^ 2 + C (4:ℚ) * X ^ 1 := by
    simp only [map_ofNat, map_neg]; ring
  have hR : coeff 97 (-2 * X ^ 14 + 4 * X ^ 13 + 2 * X ^ 12 + 2 * X ^ 11 + 2 * X ^ 10 + 2 * X ^ 9 + 2 * X ^ 8 + 4 * X ^ 7 + 2 * X ^ 6 + 2 * X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + 2 * X ^ 2 + 4 * X : PowerSeries ℚ) = 0 := by
    rw [hp]
    simp only [map_add, coeff_C_mul, coeff_X_pow]
    norm_num
  rw [e, hR] at h97
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_mk] at h97
  norm_num [a83, a84, a96, a97] at h97

