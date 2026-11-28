import OMAStatements.S_oeis_a171849
import Mathlib

namespace OMA.A171849Proof

open PowerSeries

lemma dnum (m : ℕ) [m.AtLeastTwo] : derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]; exact derivative_C

lemma cnum (m n : ℕ) [m.AtLeastTwo] (f : ℚ⟦X⟧) :
    coeff n ((no_index (OfNat.ofNat m : ℚ⟦X⟧)) * f) = (OfNat.ofNat m : ℚ) * coeff n f := by
  rw [← map_ofNat C m, coeff_C_mul]

lemma cx (f : ℚ⟦X⟧) (j k : ℕ) : coeff (k + j) (X ^ j * f) = coeff k f :=
  coeff_X_pow_mul f j k

lemma tx (G : ℚ⟦X⟧) (m : ℕ) : coeff m (X * derivative ℚ G) = (m : ℚ) * coeff m G := by
  rcases m with _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

lemma ode (T G : ℚ⟦X⟧) (hT : T = 1 + X * T + X ^ 2 * T * (T - 1))
    (hG : G * ((1 + X + X ^ 2) * (1 - 3 * X + X ^ 2)) = X ^ 3 * T ^ 2) :
    4 * ((X ^ 0 * (X * derivative ℚ G)) - 5 * (X ^ 1 * (X * derivative ℚ G)) + 7 * (X ^ 2 * (X * derivative ℚ G)) - 6 * (X ^ 3 * (X * derivative ℚ G)) + 13 * (X ^ 4 * (X * derivative ℚ G)) - 11 * (X ^ 5 * (X * derivative ℚ G)) + 13 * (X ^ 6 * (X * derivative ℚ G)) - 6 * (X ^ 7 * (X * derivative ℚ G)) + 7 * (X ^ 8 * (X * derivative ℚ G)) - 5 * (X ^ 9 * (X * derivative ℚ G)) + (X ^ 10 * (X * derivative ℚ G)) + (X ^ 0 * G) - 5 * (X ^ 1 * G) + 3 * (X ^ 2 * G) + 2 * (X ^ 3 * G) + 21 * (X ^ 4 * G) - 11 * (X ^ 5 * G) + 5 * (X ^ 6 * G) - 14 * (X ^ 7 * G) + 11 * (X ^ 8 * G) - 5 * (X ^ 9 * G) + (X ^ 10 * G)) = 16 * X ^ 3 - 16 * X ^ 5 := by
  obtain ⟨V, hVdef⟩ : ∃ V : ℚ⟦X⟧, V = 2 * X ^ 2 * T - (1 - X + X ^ 2) := ⟨_, rfl⟩
  have h1 : X ^ 2 * T ^ 2 - (1 - X + X ^ 2) * T + 1 = 0 := by linear_combination (-1) * hT
  have hV : V ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 := by
    rw [hVdef]; linear_combination 4 * X ^ 2 * h1
  have hVd : 2 * V * derivative ℚ V = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
    have := congrArg (derivative ℚ) hV
    rw [sq, Derivation.leibniz, smul_eq_mul] at this
    have h2 : derivative ℚ (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) =
        -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
      simp [dnum]
      ring
    rw [h2] at this
    linear_combination this
  have hode : 2 * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * derivative ℚ V =
      (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3) * V := by
    linear_combination (-2 * derivative ℚ V) * hV + V * hVd
  have hi : 2 * X * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * G =
      (1 - X + X ^ 2) * V + (1 - X + X ^ 2) ^ 2 - 2 * X ^ 2 := by
    rw [hVdef]
    linear_combination 2 * X * hG + 2 * X ^ 2 * h1
  have hd : 2 * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * G +
      2 * X * (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3) * G +
      2 * X * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * derivative ℚ G =
      (-1 + 2 * X) * V + (1 - X + X ^ 2) * derivative ℚ V +
        2 * (1 - X + X ^ 2) * (-1 + 2 * X) - 4 * X := by
    have := congrArg (derivative ℚ) hi
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, map_mul, map_pow] at this
    simp [dnum] at this
    linear_combination this
  linear_combination (2 * (1 - X + X ^ 2) * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * hd
    + (1 - X + X ^ 2) ^ 2 * hode
    - ((1 - X + X ^ 2) * (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3)
      + 2 * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * (-1 + 2 * X)) * hi)

lemma rec_G (T G : ℚ⟦X⟧) (hT : T = 1 + X * T + X ^ 2 * T * (T - 1))
    (hG : G * ((1 + X + X ^ 2) * (1 - 3 * X + X ^ 2)) = X ^ 3 * T ^ 2) (k : ℕ) :
    (1 * ((k:ℚ) + 10) + (1)) * coeff (k + 10) G + (-5 * ((k:ℚ) + 9) + (-5)) * coeff (k + 9) G + (7 * ((k:ℚ) + 8) + (3)) * coeff (k + 8) G + (-6 * ((k:ℚ) + 7) + (2)) * coeff (k + 7) G + (13 * ((k:ℚ) + 6) + (21)) * coeff (k + 6) G + (-11 * ((k:ℚ) + 5) + (-11)) * coeff (k + 5) G + (13 * ((k:ℚ) + 4) + (5)) * coeff (k + 4) G + (-6 * ((k:ℚ) + 3) + (-14)) * coeff (k + 3) G + (7 * ((k:ℚ) + 2) + (11)) * coeff (k + 2) G + (-5 * ((k:ℚ) + 1) + (-5)) * coeff (k + 1) G + (1 * ((k:ℚ) + 0) + (1)) * coeff k G = 0 := by
  have E := ode T G hT hG
  have h := congrArg (coeff (k + 10)) E
  simp only [map_add, map_sub, cnum] at h
  rw [cx (X * derivative ℚ G) 0 (k + 10), cx (X * derivative ℚ G) 1 (k + 9), cx (X * derivative ℚ G) 2 (k + 8), cx (X * derivative ℚ G) 3 (k + 7), cx (X * derivative ℚ G) 4 (k + 6), cx (X * derivative ℚ G) 5 (k + 5), cx (X * derivative ℚ G) 6 (k + 4), cx (X * derivative ℚ G) 7 (k + 3), cx (X * derivative ℚ G) 8 (k + 2), cx (X * derivative ℚ G) 9 (k + 1), cx (X * derivative ℚ G) 10 k, cx G 0 (k + 10), cx G 1 (k + 9), cx G 2 (k + 8), cx G 3 (k + 7), cx G 4 (k + 6), cx G 5 (k + 5), cx G 6 (k + 4), cx G 7 (k + 3), cx G 8 (k + 2), cx G 9 (k + 1), cx G 10 k] at h
  simp only [tx, coeff_X_pow] at h
  simp at h
  linear_combination h

end OMA.A171849Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a171849.main := by
  intro T G hT hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  have hr := OMA.A171849Proof.rec_G T G hT hG k
  simp only [show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega,
    show k + 10 - 3 = k + 7 by omega, show k + 10 - 4 = k + 6 by omega,
    show k + 10 - 5 = k + 5 by omega, show k + 10 - 6 = k + 4 by omega,
    show k + 10 - 7 = k + 3 by omega, show k + 10 - 8 = k + 2 by omega,
    show k + 10 - 9 = k + 1 by omega, show k + 10 - 10 = k by omega]
  push_cast
  linear_combination hr
