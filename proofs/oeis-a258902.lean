import OMAStatements.S_oeis_a258902

-- Problem: A258902 (OEIS), conjecture of R. J. Mathar: 19 a(n) + 21 (3 - 2n) a(n-1) - 4 (3n-5)(3n-7) a(n-2) = 0.
-- Credit: @AngelHS12
-- Proof: let D = A' and D2 = A''. Differentiating 6A - 3A^2 - 2A^3 = 6x gives (1 - A - A^2) D = 1, and again
-- (1 - A - A^2) D2 = (1 + 2A) D^2. Eliminating A (x = A - A^2/2 - A^3/3) yields the linear ODE
-- (19 - 42x - 36x^2) A'' - (21 + 36x) A' + 4A + 2 = 0, whose coefficient of x^(n-2), times (n-2)!, is
-- exactly the conjectured recurrence for n >= 3.

open PowerSeries

namespace OMAProof258902

open OMA.S_oeis_a258902

lemma ofNat_ne_zero' (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg (coeff 0) h
  simp only [coeff_zero_eq_constantCoeff_apply, map_ofNat, map_zero] at this
  exact absurd this (by norm_num)

theorem rec_main (A : PowerSeries ℚ)
    (hA : A - C (1 / 2 : ℚ) * A ^ 2 - C (1 / 3 : ℚ) * A ^ 3 = X) (n : ℕ) (hn : 3 ≤ n) :
    19 * a A n + 21 * (-2 * (n : ℚ) + 3) * a A (n - 1)
      - 4 * (3 * (n : ℚ) - 5) * (3 * (n : ℚ) - 7) * a A (n - 2) = 0 := by
  have c2 : C (1 / 2 : ℚ) * 2 = 1 := by
    rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  have c3 : C (1 / 3 : ℚ) * 3 = 1 := by
    rw [show (3 : ℚ⟦X⟧) = C 3 from (map_ofNat C 3).symm, ← map_mul]
    norm_num
  have hA6 : 6 * A - 3 * A ^ 2 - 2 * A ^ 3 = 6 * X := by
    linear_combination 6 * hA + 3 * A ^ 2 * c2 + 2 * A ^ 3 * c3
  have hA6C : C (6 : ℚ) * A - C (3 : ℚ) * A ^ 2 - C (2 : ℚ) * A ^ 3 = C (6 : ℚ) * X := by
    simp only [map_ofNat]
    exact hA6
  have hd := congrArg (d⁄dX ℚ) hA6C
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, derivative_C, derivative_X,
    smul_eq_mul, nsmul_eq_mul, Nat.reduceSub] at hd
  simp only [map_ofNat, Nat.cast_ofNat] at hd
  set D := d⁄dX ℚ A with hD
  have E1' : 6 * ((1 - A - A ^ 2) * D - 1) = 0 := by linear_combination hd
  have E1 : (1 - A - A ^ 2) * D = 1 := by
    have := (mul_eq_zero.mp E1').resolve_left (ofNat_ne_zero' 6)
    linear_combination this
  have hd2 := congrArg (d⁄dX ℚ) E1
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, Derivation.map_one_eq_zero,
    smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, Nat.cast_ofNat] at hd2
  set D2 := d⁄dX ℚ D with hD2
  have E2 : (1 - A - A ^ 2) * D2 = (1 + 2 * A) * D ^ 2 := by linear_combination hd2
  have h36G : 36 * ((19 - 42 * X - 36 * X ^ 2) * D2 - (21 + 36 * X) * D + 4 * A + 2) = 0 := by
    linear_combination
      (-(684 - 252 * (6 * A - 3 * A ^ 2 - 2 * A ^ 3) - 36 * (6 * A - 3 * A ^ 2 - 2 * A ^ 3) ^ 2)
          * D2
        + (756 + 216 * (6 * A - 3 * A ^ 2 - 2 * A ^ 3)) * D * (1 + (1 - A - A ^ 2) * D)
        - (144 * A + 72) * (1 + (1 - A - A ^ 2) * D + (1 - A - A ^ 2) ^ 2 * D ^ 2)) * E1
      + ((684 - 252 * (6 * A - 3 * A ^ 2 - 2 * A ^ 3)
          - 36 * (6 * A - 3 * A ^ 2 - 2 * A ^ 3) ^ 2) * D) * E2
      + (252 * D2 + 36 * (6 * X + (6 * A - 3 * A ^ 2 - 2 * A ^ 3)) * D2 + 216 * D) * hA6
  have G := (mul_eq_zero.mp h36G).resolve_left (ofNat_ne_zero' 36)
  have GC : C (19 : ℚ) * D2 - C (42 : ℚ) * (X ^ 1 * D2) - C (36 : ℚ) * (X ^ 2 * D2)
      - C (21 : ℚ) * D - C (36 : ℚ) * (X ^ 1 * D) + C (4 : ℚ) * A + C (2 : ℚ) = 0 := by
    simp only [map_ofNat]
    linear_combination G
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hc := congrArg (coeff (k + 1)) GC
  simp only [hD2, hD, map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_C, map_zero,
    coeff_derivative] at hc
  simp at hc
  simp only [show k + 1 + 1 + 1 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl] at hc
  rw [show k + 3 - 1 = k + 2 from rfl, show k + 3 - 2 = k + 1 from rfl]
  have f3 : (((k + 3).factorial : ℕ) : ℚ) = ((k : ℚ) + 3) * ((k : ℚ) + 2) * (k + 1).factorial := by
    rw [show k + 3 = (k + 1) + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f2 : (((k + 2).factorial : ℕ) : ℚ) = ((k : ℚ) + 2) * (k + 1).factorial := by
    rw [show k + 2 = (k + 1) + 1 from rfl, Nat.factorial_succ]
    push_cast
    ring
  simp only [a]
  rw [f3, f2]
  split_ifs at hc with hk
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hc
    push_cast at hc ⊢
    linear_combination (((j + 1 + 1).factorial : ℕ) : ℚ) * hc
  · obtain rfl : k = 0 := by omega
    push_cast at hc ⊢
    linear_combination (((0 + 1).factorial : ℕ) : ℚ) * hc

end OMAProof258902

theorem OMA.solution : type_of% @OMA.S_oeis_a258902.main := by
  intro A _ hA n hn
  exact OMAProof258902.rec_main A hA n hn
