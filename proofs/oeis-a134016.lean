import OMAStatements.S_oeis_a134016

-- Problem: A134016: Inverse score permutation of an Fibonacci -anti-Fibonacci zero sum game of 2 X 2 matrices.
-- Upstream: formal-conjectures statements/oeis-a134016.lean:0 (declaration OMA.S_oeis_a134016.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the step w -> p.M.w maps (w0, w1, w2, w3) to (3w2 + w3, w2, w0 + w1, w1). Applied
-- twice it gives (3w0 + 4w1, w0 + w1, 4w2 + w3, w2), and four times
-- (13w0 + 16w1, 4w0 + 5w1, 17w2 + 4w3, 4w2 + w3), which is 4 times the double step plus w itself
-- (the square of p.M satisfies X^2 - 4X - 1 = 0). So v(k+5) = 4v(k+3) + v(k+1), and summing the
-- entries a(k+5) = 4a(k+3) + a(k+1). The g.f. follows by comparing coefficients, with
-- a(0..4) = 0, 2, 6, 10, 23.

open OMA.S_oeis_a134016 in
theorem OMA.solution : type_of% @OMA.S_oeis_a134016.main := by
  have hS0 : ∀ w : Fin 4 → ℤ, p.mulVec (M.mulVec w) 0 = 3 * w 2 + w 3 := by
    intro w
    have e : p.mulVec (M.mulVec w) 0 =
        0 * (0 * w 0 + 1 * w 1 + 0 * w 2 + 0 * w 3) + 0 * (1 * w 0 + 1 * w 1 + 0 * w 2 + 0 * w 3) +
          0 * (0 * w 0 + 0 * w 1 + 1 * w 2 + 0 * w 3) +
          1 * (0 * w 0 + 0 * w 1 + 3 * w 2 + 1 * w 3) := by
      simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
      rfl
    linear_combination e
  have hS1 : ∀ w : Fin 4 → ℤ, p.mulVec (M.mulVec w) 1 = w 2 := by
    intro w
    have e : p.mulVec (M.mulVec w) 1 =
        0 * (0 * w 0 + 1 * w 1 + 0 * w 2 + 0 * w 3) + 0 * (1 * w 0 + 1 * w 1 + 0 * w 2 + 0 * w 3) +
          1 * (0 * w 0 + 0 * w 1 + 1 * w 2 + 0 * w 3) +
          0 * (0 * w 0 + 0 * w 1 + 3 * w 2 + 1 * w 3) := by
      simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
      rfl
    linear_combination e
  have hS2 : ∀ w : Fin 4 → ℤ, p.mulVec (M.mulVec w) 2 = w 0 + w 1 := by
    intro w
    have e : p.mulVec (M.mulVec w) 2 =
        0 * (0 * w 0 + 1 * w 1 + 0 * w 2 + 0 * w 3) + 1 * (1 * w 0 + 1 * w 1 + 0 * w 2 + 0 * w 3) +
          0 * (0 * w 0 + 0 * w 1 + 1 * w 2 + 0 * w 3) +
          0 * (0 * w 0 + 0 * w 1 + 3 * w 2 + 1 * w 3) := by
      simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
      rfl
    linear_combination e
  have hS3 : ∀ w : Fin 4 → ℤ, p.mulVec (M.mulVec w) 3 = w 1 := by
    intro w
    have e : p.mulVec (M.mulVec w) 3 =
        1 * (0 * w 0 + 1 * w 1 + 0 * w 2 + 0 * w 3) + 0 * (1 * w 0 + 1 * w 1 + 0 * w 2 + 0 * w 3) +
          0 * (0 * w 0 + 0 * w 1 + 1 * w 2 + 0 * w 3) +
          0 * (0 * w 0 + 0 * w 1 + 3 * w 2 + 1 * w 3) := by
      simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
      rfl
    linear_combination e
  have c0 : ∀ k, v (k + 2) 0 = 3 * v (k + 1) 2 + v (k + 1) 3 := fun k => hS0 (v (k + 1))
  have c1 : ∀ k, v (k + 2) 1 = v (k + 1) 2 := fun k => hS1 (v (k + 1))
  have c2 : ∀ k, v (k + 2) 2 = v (k + 1) 0 + v (k + 1) 1 := fun k => hS2 (v (k + 1))
  have c3 : ∀ k, v (k + 2) 3 = v (k + 1) 1 := fun k => hS3 (v (k + 1))
  have hA : ∀ n, a n = v n 0 + v n 1 + v n 2 + v n 3 := by
    intro n
    unfold a
    rw [Fin.sum_univ_four]
  have key : ∀ k, a (k + 5) = 4 * a (k + 3) + a (k + 1) := by
    intro k
    have e50 : v (k + 5) 0 = 3 * v (k + 4) 2 + v (k + 4) 3 := c0 (k + 3)
    have e51 : v (k + 5) 1 = v (k + 4) 2 := c1 (k + 3)
    have e52 : v (k + 5) 2 = v (k + 4) 0 + v (k + 4) 1 := c2 (k + 3)
    have e53 : v (k + 5) 3 = v (k + 4) 1 := c3 (k + 3)
    have e40 : v (k + 4) 0 = 3 * v (k + 3) 2 + v (k + 3) 3 := c0 (k + 2)
    have e41 : v (k + 4) 1 = v (k + 3) 2 := c1 (k + 2)
    have e42 : v (k + 4) 2 = v (k + 3) 0 + v (k + 3) 1 := c2 (k + 2)
    have e43 : v (k + 4) 3 = v (k + 3) 1 := c3 (k + 2)
    have e30 : v (k + 3) 0 = 3 * v (k + 2) 2 + v (k + 2) 3 := c0 (k + 1)
    have e31 : v (k + 3) 1 = v (k + 2) 2 := c1 (k + 1)
    have e32 : v (k + 3) 2 = v (k + 2) 0 + v (k + 2) 1 := c2 (k + 1)
    have e33 : v (k + 3) 3 = v (k + 2) 1 := c3 (k + 1)
    have e20 : v (k + 2) 0 = 3 * v (k + 1) 2 + v (k + 1) 3 := c0 k
    have e21 : v (k + 2) 1 = v (k + 1) 2 := c1 k
    have e22 : v (k + 2) 2 = v (k + 1) 0 + v (k + 1) 1 := c2 k
    have e23 : v (k + 2) 3 = v (k + 1) 1 := c3 k
    rw [hA (k + 5), hA (k + 3), hA (k + 1)]
    rw [e50, e51, e52, e53, e40, e41, e42, e43, e30, e31, e32, e33, e20, e21, e22, e23]
    ring
  have hrec : ∀ n : ℕ, 5 ≤ n → a n = 4 * a (n - 2) + a (n - 4) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [show k + 5 - 2 = k + 3 by omega, show k + 5 - 4 = k + 1 by omega]
    exact key k
  have v00 : v 0 0 = 0 := rfl
  have v01 : v 0 1 = 0 := rfl
  have v02 : v 0 2 = 0 := rfl
  have v03 : v 0 3 = 0 := rfl
  have v10 : v 1 0 = 0 := rfl
  have v11 : v 1 1 = 1 := rfl
  have v12 : v 1 2 = 1 := rfl
  have v13 : v 1 3 = 0 := rfl
  have e20 : v 2 0 = 3 * v 1 2 + v 1 3 := c0 0
  have e21 : v 2 1 = v 1 2 := c1 0
  have e22 : v 2 2 = v 1 0 + v 1 1 := c2 0
  have e23 : v 2 3 = v 1 1 := c3 0
  have v20 : v 2 0 = 3 := by linear_combination e20 + 3 * v12 + v13
  have v21 : v 2 1 = 1 := by linear_combination e21 + v12
  have v22 : v 2 2 = 1 := by linear_combination e22 + v10 + v11
  have v23 : v 2 3 = 1 := by linear_combination e23 + v11
  have e30 : v 3 0 = 3 * v 2 2 + v 2 3 := c0 1
  have e31 : v 3 1 = v 2 2 := c1 1
  have e32 : v 3 2 = v 2 0 + v 2 1 := c2 1
  have e33 : v 3 3 = v 2 1 := c3 1
  have v30 : v 3 0 = 4 := by linear_combination e30 + 3 * v22 + v23
  have v31 : v 3 1 = 1 := by linear_combination e31 + v22
  have v32 : v 3 2 = 4 := by linear_combination e32 + v20 + v21
  have v33 : v 3 3 = 1 := by linear_combination e33 + v21
  have e40 : v 4 0 = 3 * v 3 2 + v 3 3 := c0 2
  have e41 : v 4 1 = v 3 2 := c1 2
  have e42 : v 4 2 = v 3 0 + v 3 1 := c2 2
  have e43 : v 4 3 = v 3 1 := c3 2
  have v40 : v 4 0 = 13 := by linear_combination e40 + 3 * v32 + v33
  have v41 : v 4 1 = 4 := by linear_combination e41 + v32
  have v42 : v 4 2 = 5 := by linear_combination e42 + v30 + v31
  have v43 : v 4 3 = 1 := by linear_combination e43 + v31
  have a0 : a 0 = 0 := by
    rw [hA]
    linear_combination v00 + v01 + v02 + v03
  have a1 : a 1 = 2 := by
    rw [hA]
    linear_combination v10 + v11 + v12 + v13
  have a2 : a 2 = 6 := by
    rw [hA]
    linear_combination v20 + v21 + v22 + v23
  have a3 : a 3 = 10 := by
    rw [hA]
    linear_combination v30 + v31 + v32 + v33
  have a4 : a 4 = 23 := by
    rw [hA]
    linear_combination v40 + v41 + v42 + v43
  have q0 : (a 0 : ℚ) = 0 := by exact_mod_cast a0
  have q1 : (a 1 : ℚ) = 2 := by exact_mod_cast a1
  have q2 : (a 2 : ℚ) = 6 := by exact_mod_cast a2
  have q3 : (a 3 : ℚ) = 10 := by exact_mod_cast a3
  have q4 : (a 4 : ℚ) = 23 := by exact_mod_cast a4
  have hq : ∀ m, 5 ≤ m → (a m : ℚ) = 4 * (a (m - 2) : ℚ) + (a (m - 4) : ℚ) := by
    intro m hm
    have h := hrec m hm
    exact_mod_cast h
  refine ⟨hrec, ?_⟩
  have e : PowerSeries.mk (fun n => (a n : ℚ)) * (PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 2 - 1) =
      PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
        - PowerSeries.mk (fun n => (a n : ℚ)) := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
    ring
  have e2 : (PowerSeries.X * (PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 2 - 6 * PowerSeries.X - 2) :
      PowerSeries ℚ) =
      PowerSeries.X ^ 4 - PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        - PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6
        - PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_C]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m
    · norm_num [q0]
    · norm_num [q1]
    · norm_num [q0, q2]
    · norm_num [q1, q3]
    · norm_num [q0, q2, q4]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [hq m hm]
