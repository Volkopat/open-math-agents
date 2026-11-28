import OMAStatements.S_oeis_a115399
import Mathlib

/-!
Proof of Mathar's recurrence for A115399.

The defining sum is the coefficient formula of the composition G = c(u) of the Catalan generating
function c with u = X^3 - X^2 (the signs of the entry correspond to this u). From c = 1 + X c^2 we get
G = 1 + u G^2, so H = u G satisfies H^2 = H - u. For a power series with such a quadratic equation,
differentiating and eliminating H^2 gives a first-order linear differential equation, hence a linear
recurrence for the coefficients of H (theorem rec_of_quadratic); written in terms of
a(n) it is the stated recurrence up to sign.
-/

namespace OMA.QC


open PowerSeries Finset

/-- Coefficients of the square of a power series without constant term. -/
lemma coeff_sq (a : ℕ → ℤ) (h0 : a 0 = 0) (n : ℕ) :
    coeff (n + 2) ((PowerSeries.mk a) ^ 2) = ∑ k ∈ range (n + 1), a (k + 1) * a (n + 1 - k) := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [coeff_mk, h0, zero_mul, add_zero]
  rw [show n + 2 - (n + 1 + 1) = 0 by omega, h0, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n + 1 := Finset.mem_range.mp hk
  have e : n + 2 - (k + 1) = n + 1 - k := by omega
  rw [e]

lemma coeff_sq_zero (a : ℕ → ℤ) (h0 : a 0 = 0) : coeff 0 ((PowerSeries.mk a) ^ 2) = 0 := by
  rw [pow_two, coeff_mul]
  simp [h0]

lemma coeff_sq_one (a : ℕ → ℤ) (h0 : a 0 = 0) : coeff 1 ((PowerSeries.mk a) ^ 2) = 0 := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, h0]

/-- If the generating function G of `a` satisfies G^2 = L G - R with L = 1 + l1 X + l2 X^2 and
R = r1 X + r2 X^2 + r3 X^3 + r4 X^4, then `a` satisfies a linear recurrence of order four with
linear coefficients. -/
theorem rec_of_quadratic (a : ℕ → ℤ) (l1 l2 r1 r2 r3 r4 : ℤ)
    (hE : (PowerSeries.mk a) ^ 2 = (1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
      - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) (N : ℕ) :
    ((N : ℤ) + 6) * a (N + 6) + (l1 - 2 * r1) * (2 * (N : ℤ) + 9) * a (N + 5)
      + (l1 ^ 2 + 2 * l2 - 4 * r2) * ((N : ℤ) + 3) * a (N + 4)
      + (l1 * l2 - 2 * r3) * (2 * (N : ℤ) + 3) * a (N + 3)
      + (l2 ^ 2 - 4 * r4) * (N : ℤ) * a (N + 2) = 0 := by
  set G : PowerSeries ℤ := PowerSeries.mk a with hG
  set G' : PowerSeries ℤ := derivative ℤ G with hG'
  have hD : 2 * G * G' = (C l1 + 2 * C l2 * X) * G + (1 + C l1 * X + C l2 * X ^ 2) * G'
      - (C r1 + 2 * C r2 * X + 3 * C r3 * X ^ 2 + 4 * C r4 * X ^ 3) := by
    have h := congrArg (derivative ℤ) hE
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, derivative_C,
      derivative_X, smul_eq_mul, nsmul_eq_mul, Derivation.map_one_eq_zero] at h
    simp only [← hG'] at h
    push_cast at h
    linear_combination h
  have hODE : G' + C (2 * l1 - 4 * r1) * (X * G') + C (l1 ^ 2 + 2 * l2 - 4 * r2) * (X ^ 2 * G')
      + C (2 * l1 * l2 - 4 * r3) * (X ^ 3 * G') + C (l2 ^ 2 - 4 * r4) * (X ^ 4 * G')
      - (C (l1 - 2 * r1) * G + C (l1 ^ 2 + 2 * l2 - 4 * r2) * (X * G)
        + C (3 * l1 * l2 - 6 * r3) * (X ^ 2 * G) + C (2 * l2 ^ 2 - 8 * r4) * (X ^ 3 * G))
      - (C r1 + C (2 * r2 - l1 * r1) * X + C (3 * r3 - 3 * l2 * r1) * X ^ 2
        + C (l1 * r3 - 2 * l2 * r2 + 4 * r4) * X ^ 3 + C (2 * l1 * r4 - l2 * r3) * X ^ 4) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination (2 * (C l1 + 2 * C l2 * X) - 4 * G') * hE
      - ((1 + C l1 * X + C l2 * X ^ 2) - 2 * G) * hD
  have h := congrArg (coeff (N + 5)) hODE
  have d0 : coeff (N + 5) G' = a (N + 6) * ((N : ℤ) + 6) := by
    rw [hG', coeff_derivative, hG, coeff_mk]; push_cast; ring
  have d1 : coeff (N + 5) (X * G') = a (N + 5) * ((N : ℤ) + 5) := by
    rw [coeff_succ_X_mul, hG', coeff_derivative, hG, coeff_mk]; push_cast; ring
  have d2 : coeff (N + 5) (X ^ 2 * G') = a (N + 4) * ((N : ℤ) + 4) := by
    rw [show N + 5 = N + 3 + 2 from rfl, coeff_X_pow_mul, hG', coeff_derivative, hG, coeff_mk]
    push_cast; ring
  have d3 : coeff (N + 5) (X ^ 3 * G') = a (N + 3) * ((N : ℤ) + 3) := by
    rw [show N + 5 = N + 2 + 3 from rfl, coeff_X_pow_mul, hG', coeff_derivative, hG, coeff_mk]
    push_cast; ring
  have d4 : coeff (N + 5) (X ^ 4 * G') = a (N + 2) * ((N : ℤ) + 2) := by
    rw [show N + 5 = N + 1 + 4 from rfl, coeff_X_pow_mul, hG', coeff_derivative, hG, coeff_mk]
    push_cast; ring
  have g0 : coeff (N + 5) G = a (N + 5) := by rw [hG, coeff_mk]
  have g1 : coeff (N + 5) (X * G) = a (N + 4) := by rw [coeff_succ_X_mul, hG, coeff_mk]
  have g2 : coeff (N + 5) (X ^ 2 * G) = a (N + 3) := by
    rw [show N + 5 = N + 3 + 2 from rfl, coeff_X_pow_mul, hG, coeff_mk]
  have g3 : coeff (N + 5) (X ^ 3 * G) = a (N + 2) := by
    rw [show N + 5 = N + 2 + 3 from rfl, coeff_X_pow_mul, hG, coeff_mk]
  have s0 : coeff (N + 5) (C r1 : PowerSeries ℤ) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have s1 : coeff (N + 5) (C (2 * r2 - l1 * r1) * X : PowerSeries ℤ) = 0 := by
    rw [coeff_C_mul, coeff_X, if_neg (by omega), mul_zero]
  have s2 : coeff (N + 5) (C (3 * r3 - 3 * l2 * r1) * X ^ 2 : PowerSeries ℤ) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  have s3 : coeff (N + 5) (C (l1 * r3 - 2 * l2 * r2 + 4 * r4) * X ^ 3 : PowerSeries ℤ) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  have s4 : coeff (N + 5) (C (2 * l1 * r4 - l2 * r3) * X ^ 4 : PowerSeries ℤ) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, d0, d1, d2, d3, d4, g0, g1, g2, g3,
    s0, s1, s2, s3, s4, LinearMap.map_zero] at h
  linear_combination h


/-- The right-hand side L G - R, expanded into monomial multiples of G. -/
lemma rhs_expand (a : ℕ → ℤ) (l1 l2 r1 r2 r3 r4 : ℤ) :
    (1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
      - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)
    = PowerSeries.mk a + C l1 * (X * PowerSeries.mk a) + C l2 * (X ^ 2 * PowerSeries.mk a)
      - C r1 * X - C r2 * X ^ 2 - C r3 * X ^ 3 - C r4 * X ^ 4 := by
  ring

lemma coeff_rhs_big (a : ℕ → ℤ) (l1 l2 r1 r2 r3 r4 : ℤ) (n : ℕ) :
    coeff (n + 5) ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
      - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4))
    = a (n + 5) + l1 * a (n + 4) + l2 * a (n + 3) := by
  rw [rhs_expand]
  have e2 : coeff (n + 5) (X ^ 2 * PowerSeries.mk a) = a (n + 3) := by
    rw [show n + 5 = n + 3 + 2 from rfl, coeff_X_pow_mul, coeff_mk]
  simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_mk, e2,
    coeff_X, coeff_X_pow]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  ring

lemma coeff_rhs_small (a : ℕ → ℤ) (l1 l2 r1 r2 r3 r4 : ℤ) (h0 : a 0 = 0) :
    coeff 0 ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
        - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) = 0
    ∧ coeff 1 ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
        - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) = a 1 - r1
    ∧ coeff 2 ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
        - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) = a 2 + l1 * a 1 - r2
    ∧ coeff 3 ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
        - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) = a 3 + l1 * a 2 + l2 * a 1 - r3
    ∧ coeff 4 ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
        - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4))
        = a 4 + l1 * a 3 + l2 * a 2 - r4 := by
  rw [rhs_expand]
  have x0 : coeff 0 (X * PowerSeries.mk a) = 0 := coeff_zero_X_mul _
  have x1 : coeff 1 (X * PowerSeries.mk a) = a 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_mk]
  have x2 : coeff 2 (X * PowerSeries.mk a) = a 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, coeff_succ_X_mul, coeff_mk]
  have x3 : coeff 3 (X * PowerSeries.mk a) = a 2 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, coeff_succ_X_mul, coeff_mk]
  have x4 : coeff 4 (X * PowerSeries.mk a) = a 3 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, coeff_succ_X_mul, coeff_mk]
  have y0 : coeff 0 (X ^ 2 * PowerSeries.mk a) = 0 := by
    rw [coeff_X_pow_mul']; simp
  have y1 : coeff 1 (X ^ 2 * PowerSeries.mk a) = 0 := by
    rw [coeff_X_pow_mul']; simp
  have y2 : coeff 2 (X ^ 2 * PowerSeries.mk a) = a 0 := by
    rw [show (2 : ℕ) = 0 + 2 from rfl, coeff_X_pow_mul, coeff_mk]
  have y3 : coeff 3 (X ^ 2 * PowerSeries.mk a) = a 1 := by
    rw [show (3 : ℕ) = 1 + 2 from rfl, coeff_X_pow_mul, coeff_mk]
  have y4 : coeff 4 (X ^ 2 * PowerSeries.mk a) = a 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, coeff_X_pow_mul, coeff_mk]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, coeff_mk, x0, x1, x2, x3, x4,
      y0, y1, y2, y3, y4, coeff_X, coeff_X_pow, h0]
     norm_num)

end OMA.QC

namespace OMA.P399

open PowerSeries

/-- The Catalan generating function over the integers. -/
noncomputable def Cz : PowerSeries ℤ := PowerSeries.mk fun n => (catalan n : ℤ)

lemma hC : Cz = 1 + X * Cz ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  have hm : PowerSeries.map (Nat.castRingHom ℤ) PowerSeries.catalanSeries = Cz := by
    ext n
    simp [Cz, PowerSeries.catalanSeries]
  simp only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X, hm] at h
  linear_combination (-1 : PowerSeries ℤ) * h

/-- The substituted series X^3 - X^2. -/
noncomputable def u : PowerSeries ℤ := X ^ 3 - X ^ 2

lemma hu : HasSubst u := HasSubst.of_constantCoeff_zero' (by simp [u])

/-- The composition c(X^3 - X^2). -/
noncomputable def G : PowerSeries ℤ := Cz.subst u

lemma hG : G = 1 + u * G ^ 2 := by
  have h := congrArg (PowerSeries.subst u) hC
  rw [subst_add hu, subst_mul hu, subst_pow hu, subst_X hu] at h
  have h1 : (1 : PowerSeries ℤ).subst u = 1 := by
    rw [← coe_substAlgHom hu]
    exact map_one _
  rw [h1] at h
  exact h

lemma coeff_u_pow (k n : ℕ) : coeff n (u ^ k)
    = if 2 * k ≤ n then (-1) ^ (k - (n - 2 * k)) * (k.choose (n - 2 * k) : ℤ) else 0 := by
  have e : u ^ k = X ^ (2 * k)
      * (((Polynomial.X + Polynomial.C (-1 : ℤ)) ^ k : Polynomial ℤ) : PowerSeries ℤ) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C]
    unfold u
    have e2 : (X : PowerSeries ℤ) ^ 3 - X ^ 2 = X ^ 2 * (X + PowerSeries.C (-1)) := by
      simp only [map_neg, map_one]
      ring
    rw [e2, mul_pow, ← pow_mul]
  rw [e, coeff_X_pow_mul']
  split_ifs with h
  · rw [Polynomial.coeff_coe, Polynomial.coeff_X_add_C_pow]
  · rfl

lemma coeff_G (n : ℕ) : coeff n G = OMA.S_oeis_a115399.a n := by
  unfold G OMA.S_oeis_a115399.a
  rw [coeff_subst' hu, finsum_eq_sum_of_support_subset (s := Finset.range (n / 2 + 1))]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < n / 2 + 1 := Finset.mem_range.mp hk
    have h2 : 2 * k ≤ n := by omega
    rw [coeff_u_pow, if_pos h2]
    simp only [Cz, coeff_mk, smul_eq_mul]
    rcases Nat.lt_or_ge k (n - 2 * k) with hlt | hge
    · rw [Nat.choose_eq_zero_of_lt hlt]
      simp
    · have hp : (-1 : ℤ) ^ (k - (n - 2 * k)) = (-1) ^ (n - k) := by
        rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := n - k)]
        congr 1
        omega
      rw [hp]
      ring
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    apply hd
    rw [coeff_u_pow, if_neg (by omega)]
    simp

/-- H = u G satisfies H^2 = H - u. -/
noncomputable def H : PowerSeries ℤ := u * G

lemma hH : (PowerSeries.mk fun n => coeff n H) ^ 2
    = (1 + C 0 * X + C 0 * X ^ 2) * (PowerSeries.mk fun n => coeff n H)
      - (C 0 * X + C (-1) * X ^ 2 + C 1 * X ^ 3 + C 0 * X ^ 4) := by
  have hmk : (PowerSeries.mk fun n => coeff n H) = H := by
    ext n
    simp
  rw [hmk]
  simp only [map_neg, map_one, map_zero]
  have h := hG
  unfold H u at *
  linear_combination (-(X ^ 3 - X ^ 2)) * h

lemma coeff_H (m : ℕ) : coeff (m + 3) H = OMA.S_oeis_a115399.a m - OMA.S_oeis_a115399.a (m + 1) := by
  have e : H = X ^ 3 * G - X ^ 2 * G := by
    unfold H u
    ring
  rw [e, LinearMap.map_sub, coeff_X_pow_mul, show m + 3 = m + 1 + 2 from rfl, coeff_X_pow_mul,
    coeff_G, coeff_G]

lemma three (N : ℕ) :
    ((N : ℤ) + 6) * (OMA.S_oeis_a115399.a (N + 3) - OMA.S_oeis_a115399.a (N + 4))
      + 4 * ((N : ℤ) + 3) * (OMA.S_oeis_a115399.a (N + 1) - OMA.S_oeis_a115399.a (N + 2))
      - 2 * (2 * (N : ℤ) + 3) * (OMA.S_oeis_a115399.a N - OMA.S_oeis_a115399.a (N + 1)) = 0 := by
  have h := OMA.QC.rec_of_quadratic (fun n => coeff n H) 0 0 0 (-1) 1 0 hH N
  have c6 : coeff (N + 6) H = OMA.S_oeis_a115399.a (N + 3) - OMA.S_oeis_a115399.a (N + 4) := coeff_H (N + 3)
  have c4 : coeff (N + 4) H = OMA.S_oeis_a115399.a (N + 1) - OMA.S_oeis_a115399.a (N + 2) := coeff_H (N + 1)
  have c3 : coeff (N + 3) H = OMA.S_oeis_a115399.a N - OMA.S_oeis_a115399.a (N + 1) := coeff_H N
  simp only [c6, c4, c3] at h
  linear_combination h

end OMA.P399

theorem OMA.solution : type_of% @OMA.S_oeis_a115399.main := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 4 := ⟨n - 4, by omega⟩
  have h := OMA.P399.three N
  have e1 : N + 4 - 1 = N + 3 := by omega
  have e2 : N + 4 - 2 = N + 2 := by omega
  have e3 : N + 4 - 3 = N + 1 := by omega
  have e4 : N + 4 - 4 = N := by omega
  rw [e1, e2, e3, e4]
  push_cast
  linear_combination (-1 : ℤ) * h
