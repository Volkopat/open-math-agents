import OMAStatements.S_oeis_a013663

-- Problem: A013663: Decimal expansion of zeta(5).
-- Upstream: formal-conjectures statements/oeis-a013663.lean:0 (declaration OMA.S_oeis_a013663.main)
-- Credit: @Jakeybakeypants (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a013663

open Finset Filter Topology OMA.S_oeis_a013663

section Polynomials

private def p00 {R : Type*} [CommRing R] (k : R) : R :=
  -140 + 1785 * k - 9415 * k ^ 2 + 26145 * k ^ 3 - 40045 * k ^ 4 + 32050 * k ^ 5 -
    10500 * k ^ 6

private def p01 {R : Type*} [CommRing R] (k : R) : R :=
  -140 + 1435 * k - 5535 * k ^ 2 + 9350 * k ^ 3 - 5500 * k ^ 4

private def p10 {R : Type*} [CommRing R] (k : R) : R :=
  20 - 255 * k + 1313 * k ^ 2 - 3447 * k ^ 3 + 4907 * k ^ 4 - 3630 * k ^ 5 + 1100 * k ^ 6

private def p11 {R : Type*} [CommRing R] (k : R) : R :=
  20 - 205 * k + 745 * k ^ 2 - 1050 * k ^ 3 + 500 * k ^ 4

private def tP0 {R : Type*} [CommRing R] (k X : R) : R :=
  let t := 2 * k - 1
  t ^ 7 * (-35 + 525 * k - 3180 * k ^ 2 + 9400 * k ^ 3 - 11768 * k ^ 4)
    + 20 * X ^ 2 * t ^ 6 * (-7 + 84 * k - 366 * k ^ 2 + 592 * k ^ 3)
    + 70 * X ^ 4 * t ^ 4 * (3 - 33 * k + 126 * k ^ 2 - 164 * k ^ 3)
    + 140 * X ^ 6 * t ^ 2 * (-1 + 10 * k - 34 * k ^ 2 + 40 * k ^ 3)
    + 5 * X ^ 8 * (7 - 63 * k + 198 * k ^ 2 - 220 * k ^ 3)

private def tP1 {R : Type*} [CommRing R] (k X : R) : R :=
  let t := 2 * k - 1
  t ^ 7 * (5 - 75 * k + 388 * k ^ 2 - 440 * k ^ 3 - 2200 * k ^ 4)
    + 4 * X ^ 2 * t ^ 6 * (5 - 60 * k + 218 * k ^ 2 - 96 * k ^ 3)
    + 10 * X ^ 4 * t ^ 4 * (-3 + 33 * k - 110 * k ^ 2 + 84 * k ^ 3)
    + 4 * X ^ 6 * t ^ 2 * (5 - 50 * k + 154 * k ^ 2 - 120 * k ^ 3)
    + 5 * X ^ 8 * (-1 + 9 * k - 26 * k ^ 2 + 20 * k ^ 3)

private lemma poly_id_0 (k u : ℚ) :
    (u - k) ^ 5 * tP0 k (2 * u + 1) - (u + k) ^ 5 * tP0 k (2 * u - 1) =
      65536 * k ^ 9 * (2 * k - 1) ^ 7 -
        512 * (p00 k + p01 k * u ^ 2) * (u ^ 2 - k ^ 2) ^ 5 := by
  unfold tP0 p00 p01
  ring

private lemma poly_id_1 (k u : ℚ) :
    (u - k) ^ 5 * tP1 k (2 * u + 1) - (u + k) ^ 5 * tP1 k (2 * u - 1) =
      65536 * k ^ 7 * (2 * k - 1) ^ 7 * u ^ 2 -
        512 * (p10 k + p11 k * u ^ 2) * (u ^ 2 - k ^ 2) ^ 5 := by
  unfold tP1 p10 p11
  ring

private lemma poly_det (k : ℚ) :
    p00 k * p11 k - p01 k * p10 k =
      16 * k * (2 * k - 1) ^ 4 * (5 * k) * (5 * k - 1) * (5 * k - 2) * (5 * k - 3) *
        (5 * k - 4) := by
  unfold p00 p01 p10 p11
  ring

end Polynomials

section MatrixAndProducts

private def d0 (k : ℕ) : ℚ :=
  128 * ((k : ℚ) + 1) ^ 9 * (2 * ((k : ℚ) + 1) - 1) ^ 7

private def d1 (k : ℕ) : ℚ :=
  128 * ((k : ℚ) + 1) ^ 7 * (2 * ((k : ℚ) + 1) - 1) ^ 7

private lemma d0_pos (k : ℕ) : 0 < d0 k := by
  unfold d0
  have h1 : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have h2 : (0 : ℚ) < 2 * ((k : ℚ) + 1) - 1 := by linarith
  positivity

private lemma d1_pos (k : ℕ) : 0 < d1 k := by
  unfold d1
  have h1 : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have h2 : (0 : ℚ) < 2 * ((k : ℚ) + 1) - 1 := by linarith
  positivity

private lemma d0_eq (k : ℕ) : d0 k = ((k : ℚ) + 1) ^ 2 * d1 k := by
  unfold d0 d1
  ring

private def M00 (k : ℕ) : ℚ := p00 ((k : ℚ) + 1) / d0 k
private def M01 (k : ℕ) : ℚ := p01 ((k : ℚ) + 1) / d0 k
private def M10 (k : ℕ) : ℚ := p10 ((k : ℚ) + 1) / d1 k
private def M11 (k : ℕ) : ℚ := p11 ((k : ℚ) + 1) / d1 k

private lemma detM_pos (k : ℕ) : 0 < M00 k * M11 k - M01 k * M10 k := by
  unfold M00 M01 M10 M11
  have hd0 : 0 < d0 k := d0_pos k
  have hd1 : 0 < d1 k := d1_pos k
  have heq :
      p00 ((k : ℚ) + 1) / d0 k * (p11 ((k : ℚ) + 1) / d1 k) -
          p01 ((k : ℚ) + 1) / d0 k * (p10 ((k : ℚ) + 1) / d1 k) =
        (p00 ((k : ℚ) + 1) * p11 ((k : ℚ) + 1) - p01 ((k : ℚ) + 1) * p10 ((k : ℚ) + 1)) /
          (d0 k * d1 k) := by
    field_simp
  rw [heq, poly_det ((k : ℚ) + 1)]
  have hK : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have h2K : (0 : ℚ) < 2 * ((k : ℚ) + 1) - 1 := by linarith
  have h50 : (0 : ℚ) < 5 * ((k : ℚ) + 1) := by linarith
  have h51 : (0 : ℚ) < 5 * ((k : ℚ) + 1) - 1 := by linarith
  have h52 : (0 : ℚ) < 5 * ((k : ℚ) + 1) - 2 := by linarith
  have h53 : (0 : ℚ) < 5 * ((k : ℚ) + 1) - 3 := by linarith
  have h54 : (0 : ℚ) < 5 * ((k : ℚ) + 1) - 4 := by linarith
  positivity

private def Qℚ (k m : ℕ) : ℚ :=
  ∏ j ∈ range (2 * k + 1), ((m : ℚ) + 1 + (j : ℚ))

private def Rℚ (k m : ℕ) : ℚ :=
  ∏ j ∈ range (2 * k), ((m : ℚ) + 1 + (j : ℚ))

private lemma Qℚ_pos (k m : ℕ) : 0 < Qℚ k m := by
  unfold Qℚ
  refine Finset.prod_pos fun j _ => ?_
  positivity

private lemma Rℚ_pos (k m : ℕ) : 0 < Rℚ k m := by
  unfold Rℚ
  refine Finset.prod_pos fun j _ => ?_
  positivity

private lemma Qℚ_cast (k m : ℕ) :
    ((Qℚ k m : ℚ) : ℂ) = ∏ j ∈ range (2 * k + 1), (((m : ℂ) + 1) + (j : ℂ)) := by
  unfold Qℚ
  push_cast
  rfl

private lemma Qℚ_zero (m : ℕ) : Qℚ 0 m = (m : ℚ) + 1 := by
  simp [Qℚ]

private lemma Rℚ_succ_eq (k m : ℕ) : Rℚ (k + 1) m = ((m : ℚ) + 1) * Qℚ k (m + 1) := by
  have hlen : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  unfold Rℚ Qℚ
  rw [hlen, Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast
  ring

private lemma Rℚ_succ_shift (k m : ℕ) :
    Rℚ (k + 1) (m + 1) = (((m : ℚ) + 1) + 2 * ((k : ℚ) + 1)) * Qℚ k (m + 1) := by
  have hlen : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  unfold Rℚ Qℚ
  rw [hlen, Finset.prod_range_succ, mul_comm]
  congr 1
  push_cast
  ring

private lemma Qℚ_succ_eq (k m : ℕ) :
    Qℚ (k + 1) m = ((m : ℚ) + 1) * (((m : ℚ) + 1) + 2 * ((k : ℚ) + 1)) * Qℚ k (m + 1) := by
  have h1 : Qℚ (k + 1) m = Rℚ (k + 1) m * ((m : ℚ) + 1 + ((2 * (k + 1) : ℕ) : ℚ)) := by
    unfold Qℚ Rℚ
    rw [Finset.prod_range_succ]
  rw [h1, Rℚ_succ_eq]
  push_cast
  ring

private lemma add_one_pow_le_Qℚ (k m : ℕ) :
    ((m : ℚ) + 1) ^ (2 * k + 1) ≤ Qℚ k m := by
  unfold Qℚ
  calc
    ((m : ℚ) + 1) ^ (2 * k + 1)
      = ∏ _j ∈ range (2 * k + 1), ((m : ℚ) + 1) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ j ∈ range (2 * k + 1), ((m : ℚ) + 1 + (j : ℚ)) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro j _
          positivity
        · intro j _
          linarith [Nat.cast_nonneg (α := ℚ) j]

private lemma add_one_pow_le_Rℚ (k m : ℕ) :
    ((m : ℚ) + 1) ^ (2 * k) ≤ Rℚ k m := by
  unfold Rℚ
  calc
    ((m : ℚ) + 1) ^ (2 * k)
      = ∏ _j ∈ range (2 * k), ((m : ℚ) + 1) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ j ∈ range (2 * k), ((m : ℚ) + 1 + (j : ℚ)) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro j _
          positivity
        · intro j _
          linarith [Nat.cast_nonneg (α := ℚ) j]

private lemma add_one_le_Qℚ_real (k m : ℕ) : (m : ℝ) + 1 ≤ (Qℚ k m : ℝ) := by
  have hq : ((m : ℚ) + 1) ^ (2 * k + 1) ≤ Qℚ k m := add_one_pow_le_Qℚ k m
  have hr : ((m : ℝ) + 1) ^ (2 * k + 1) ≤ (Qℚ k m : ℝ) := by exact_mod_cast hq
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hp : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) ^ (2 * k + 1) :=
    le_self_pow₀ hm (by omega)
  exact hp.trans hr

private lemma add_one_sq_le_Rℚ_succ_real (k m : ℕ) :
    ((m : ℝ) + 1) ^ 2 ≤ (Rℚ (k + 1) m : ℝ) := by
  have hq : ((m : ℚ) + 1) ^ (2 * (k + 1)) ≤ Rℚ (k + 1) m := add_one_pow_le_Rℚ (k + 1) m
  have hr : ((m : ℝ) + 1) ^ (2 * (k + 1)) ≤ (Rℚ (k + 1) m : ℝ) := by exact_mod_cast hq
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hp : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ (2 * (k + 1)) := by
    exact pow_le_pow_right₀ hm (by omega)
  exact hp.trans hr

end MatrixAndProducts

section SeriesAndTelescoping

private noncomputable def f0 (k m : ℕ) : ℂ :=
  1 / ((Qℚ k m : ℚ) : ℂ) ^ 5

private noncomputable def f2 (k m : ℕ) : ℂ :=
  ((m : ℂ) + 1 + (k : ℂ)) ^ 2 / ((Qℚ k m : ℚ) : ℂ) ^ 5

private def G0ℚ (k m : ℕ) : ℚ :=
  tP0 ((k : ℚ) + 1) (2 * ((m : ℚ) + 1 + (k : ℚ) + 1) - 1) /
    (65536 * ((k : ℚ) + 1) ^ 9 * (2 * ((k : ℚ) + 1) - 1) ^ 7 * (Rℚ (k + 1) m) ^ 5)

private def G1ℚ (k m : ℕ) : ℚ :=
  tP1 ((k : ℚ) + 1) (2 * ((m : ℚ) + 1 + (k : ℚ) + 1) - 1) /
    (65536 * ((k : ℚ) + 1) ^ 7 * (2 * ((k : ℚ) + 1) - 1) ^ 7 * (Rℚ (k + 1) m) ^ 5)

private noncomputable def G0 (k m : ℕ) : ℂ := (G0ℚ k m : ℂ)
private noncomputable def G1 (k m : ℕ) : ℂ := (G1ℚ k m : ℂ)

private lemma summable_one_div_add_one_pow (p : ℕ) (hp : 1 < p) :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1 (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p)).mpr
    (Real.summable_one_div_nat_pow.mpr hp)
  simpa [Nat.cast_add, Nat.cast_one] using h

private lemma summable_f0 (k : ℕ) : Summable (f0 k) := by
  refine Summable.of_norm_bounded (summable_one_div_add_one_pow 5 (by omega)) fun m => ?_
  have hQ : (m : ℝ) + 1 ≤ (Qℚ k m : ℝ) := add_one_le_Qℚ_real k m
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hQpos0 : (0 : ℝ) < (Qℚ k m : ℝ) := by linarith
  have hQpow : ((m : ℝ) + 1) ^ 5 ≤ (Qℚ k m : ℝ) ^ 5 := by gcongr
  have hQpos : (0 : ℝ) < (Qℚ k m : ℝ) ^ 5 := by positivity
  unfold f0
  have hnorm : ‖(1 : ℂ) / ((Qℚ k m : ℚ) : ℂ) ^ 5‖ = 1 / (Qℚ k m : ℝ) ^ 5 := by
    have heq : ((Qℚ k m : ℚ) : ℂ) = (((Qℚ k m : ℚ) : ℝ) : ℂ) := by norm_cast
    rw [heq, ← Complex.ofReal_pow, one_div, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hQpos.le, one_div]
  rw [hnorm]
  exact one_div_le_one_div_of_le (by positivity) hQpow

private lemma summable_f2 (k : ℕ) : Summable (f2 k) := by
  have hmaj : Summable (fun m : ℕ => ((k : ℝ) + 1) ^ 2 * ((1 : ℝ) / ((m : ℝ) + 1) ^ 3)) :=
    (summable_one_div_add_one_pow 3 (by omega)).mul_left (((k : ℝ) + 1) ^ 2)
  refine Summable.of_norm_bounded hmaj fun m => ?_
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hnum : (m : ℝ) + 1 + (k : ℝ) ≤ ((k : ℝ) + 1) * ((m : ℝ) + 1) := by nlinarith
  have hnumsq : ((m : ℝ) + 1 + (k : ℝ)) ^ 2 ≤ (((k : ℝ) + 1) * ((m : ℝ) + 1)) ^ 2 := by gcongr
  have hQ : (m : ℝ) + 1 ≤ (Qℚ k m : ℝ) := add_one_le_Qℚ_real k m
  have hQpos0 : (0 : ℝ) < (Qℚ k m : ℝ) := by linarith
  have hQpow : ((m : ℝ) + 1) ^ 5 ≤ (Qℚ k m : ℝ) ^ 5 := by gcongr
  have hQpos : (0 : ℝ) < (Qℚ k m : ℝ) ^ 5 := by positivity
  unfold f2
  have hcast :
      ((m : ℂ) + 1 + (k : ℂ)) ^ 2 / ((Qℚ k m : ℚ) : ℂ) ^ 5 =
        (((((m : ℝ) + 1 + (k : ℝ)) ^ 2 / (Qℚ k m : ℝ) ^ 5 : ℝ)) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    ((m : ℝ) + 1 + (k : ℝ)) ^ 2 / (Qℚ k m : ℝ) ^ 5
      ≤ (((k : ℝ) + 1) * ((m : ℝ) + 1)) ^ 2 / ((m : ℝ) + 1) ^ 5 := by gcongr
    _ = ((k : ℝ) + 1) ^ 2 * ((1 : ℝ) / ((m : ℝ) + 1) ^ 3) := by
        field_simp

private lemma mul_div_mul_cancel_left' (x y z : ℚ) (hy : y ≠ 0) :
    (z * y) * (x / y) = z * x := by
  rw [mul_assoc, mul_div_cancel₀ _ hy]

private lemma rational_step_0 (K u q a b g1 g2 : ℚ)
    (hK : K ≠ 0) (h2K : 2 * K - 1 ≠ 0) (hu1 : u - K ≠ 0) (hu2 : u + K ≠ 0) (hq : q ≠ 0)
    (hid : (u - K) ^ 5 * g1 - (u + K) ^ 5 * g2 =
      65536 * K ^ 9 * (2 * K - 1) ^ 7 - 512 * (a + b * u ^ 2) * (u ^ 2 - K ^ 2) ^ 5) :
    1 / ((u - K) * (u + K) * q) ^ 5 =
      a / (128 * K ^ 9 * (2 * K - 1) ^ 7) * (1 / q ^ 5) +
        b / (128 * K ^ 9 * (2 * K - 1) ^ 7) * (u ^ 2 / q ^ 5) +
        (g1 / (65536 * K ^ 9 * (2 * K - 1) ^ 7 * ((u + K) * q) ^ 5) -
          g2 / (65536 * K ^ 9 * (2 * K - 1) ^ 7 * ((u - K) * q) ^ 5)) := by
  let C9 : ℚ := 65536 * K ^ 9 * (2 * K - 1) ^ 7
  let den : ℚ := 128 * K ^ 9 * (2 * K - 1) ^ 7
  let D : ℚ := C9 * (u - K) ^ 5 * (u + K) ^ 5 * q ^ 5
  have hC9 : C9 ≠ 0 := by dsimp [C9]; simp [hK, h2K]
  have hden : den ≠ 0 := by dsimp [den]; simp [hK, h2K]
  have hD : D ≠ 0 := by dsimp [D]; simp [hC9, hu1, hu2, hq]
  have hden0 : ((u - K) * (u + K) * q) ^ 5 ≠ 0 :=
    pow_ne_zero 5 (mul_ne_zero (mul_ne_zero hu1 hu2) hq)
  have hdenq : den * q ^ 5 ≠ 0 := mul_ne_zero hden (pow_ne_zero 5 hq)
  have hden1 : C9 * ((u + K) * q) ^ 5 ≠ 0 := mul_ne_zero hC9 (pow_ne_zero 5 (mul_ne_zero hu2 hq))
  have hden2 : C9 * ((u - K) * q) ^ 5 ≠ 0 := mul_ne_zero hC9 (pow_ne_zero 5 (mul_ne_zero hu1 hq))
  have hD2 : D = (512 * (u ^ 2 - K ^ 2) ^ 5) * (den * q ^ 5) := by dsimp [D, C9, den]; ring
  have h1 : D * (1 / ((u - K) * (u + K) * q) ^ 5) = C9 := by
    have hD1 : D = C9 * ((u - K) * (u + K) * q) ^ 5 := by dsimp [D]; ring
    rw [hD1, mul_div_mul_cancel_left' _ _ _ hden0, mul_one]
  have h2 : D * (a / den * (1 / q ^ 5)) = 512 * a * (u ^ 2 - K ^ 2) ^ 5 := by
    rw [div_mul_div_comm, mul_one, hD2, mul_div_mul_cancel_left' _ _ _ hdenq]
    ring
  have h3 : D * (b / den * (u ^ 2 / q ^ 5)) = 512 * b * u ^ 2 * (u ^ 2 - K ^ 2) ^ 5 := by
    rw [div_mul_div_comm, hD2, mul_div_mul_cancel_left' _ _ _ hdenq]
    ring
  have h4 : D * (g1 / (C9 * ((u + K) * q) ^ 5)) = (u - K) ^ 5 * g1 := by
    have hD4 : D = (u - K) ^ 5 * (C9 * ((u + K) * q) ^ 5) := by dsimp [D]; ring
    rw [hD4, mul_div_mul_cancel_left' _ _ _ hden1]
  have h5 : D * (g2 / (C9 * ((u - K) * q) ^ 5)) = (u + K) ^ 5 * g2 := by
    have hD5 : D = (u + K) ^ 5 * (C9 * ((u - K) * q) ^ 5) := by dsimp [D]; ring
    rw [hD5, mul_div_mul_cancel_left' _ _ _ hden2]
  apply mul_left_cancel₀ hD
  rw [mul_add D, mul_add D, mul_sub D]
  change D * (1 / ((u - K) * (u + K) * q) ^ 5) =
    (D * (a / den * (1 / q ^ 5)) + D * (b / den * (u ^ 2 / q ^ 5))) +
      (D * (g1 / (C9 * ((u + K) * q) ^ 5)) - D * (g2 / (C9 * ((u - K) * q) ^ 5)))
  rw [h1, h2, h3, h4, h5]
  dsimp [C9]
  rw [hid]
  ring

private lemma rational_step_1 (K u q a b g1 g2 : ℚ)
    (hK : K ≠ 0) (h2K : 2 * K - 1 ≠ 0) (hu1 : u - K ≠ 0) (hu2 : u + K ≠ 0) (hq : q ≠ 0)
    (hid : (u - K) ^ 5 * g1 - (u + K) ^ 5 * g2 =
      65536 * K ^ 7 * (2 * K - 1) ^ 7 * u ^ 2 - 512 * (a + b * u ^ 2) * (u ^ 2 - K ^ 2) ^ 5) :
    u ^ 2 / ((u - K) * (u + K) * q) ^ 5 =
      a / (128 * K ^ 7 * (2 * K - 1) ^ 7) * (1 / q ^ 5) +
        b / (128 * K ^ 7 * (2 * K - 1) ^ 7) * (u ^ 2 / q ^ 5) +
        (g1 / (65536 * K ^ 7 * (2 * K - 1) ^ 7 * ((u + K) * q) ^ 5) -
          g2 / (65536 * K ^ 7 * (2 * K - 1) ^ 7 * ((u - K) * q) ^ 5)) := by
  let C7 : ℚ := 65536 * K ^ 7 * (2 * K - 1) ^ 7
  let den : ℚ := 128 * K ^ 7 * (2 * K - 1) ^ 7
  let D : ℚ := C7 * (u - K) ^ 5 * (u + K) ^ 5 * q ^ 5
  have hC7 : C7 ≠ 0 := by dsimp [C7]; simp [hK, h2K]
  have hden : den ≠ 0 := by dsimp [den]; simp [hK, h2K]
  have hD : D ≠ 0 := by dsimp [D]; simp [hC7, hu1, hu2, hq]
  have hden0 : ((u - K) * (u + K) * q) ^ 5 ≠ 0 :=
    pow_ne_zero 5 (mul_ne_zero (mul_ne_zero hu1 hu2) hq)
  have hdenq : den * q ^ 5 ≠ 0 := mul_ne_zero hden (pow_ne_zero 5 hq)
  have hden1 : C7 * ((u + K) * q) ^ 5 ≠ 0 := mul_ne_zero hC7 (pow_ne_zero 5 (mul_ne_zero hu2 hq))
  have hden2 : C7 * ((u - K) * q) ^ 5 ≠ 0 := mul_ne_zero hC7 (pow_ne_zero 5 (mul_ne_zero hu1 hq))
  have hD2 : D = (512 * (u ^ 2 - K ^ 2) ^ 5) * (den * q ^ 5) := by dsimp [D, C7, den]; ring
  have h1 : D * (u ^ 2 / ((u - K) * (u + K) * q) ^ 5) = C7 * u ^ 2 := by
    have hD1 : D = C7 * ((u - K) * (u + K) * q) ^ 5 := by dsimp [D]; ring
    rw [hD1, mul_div_mul_cancel_left' _ _ _ hden0]
  have h2 : D * (a / den * (1 / q ^ 5)) = 512 * a * (u ^ 2 - K ^ 2) ^ 5 := by
    rw [div_mul_div_comm, mul_one, hD2, mul_div_mul_cancel_left' _ _ _ hdenq]
    ring
  have h3 : D * (b / den * (u ^ 2 / q ^ 5)) = 512 * b * u ^ 2 * (u ^ 2 - K ^ 2) ^ 5 := by
    rw [div_mul_div_comm, hD2, mul_div_mul_cancel_left' _ _ _ hdenq]
    ring
  have h4 : D * (g1 / (C7 * ((u + K) * q) ^ 5)) = (u - K) ^ 5 * g1 := by
    have hD4 : D = (u - K) ^ 5 * (C7 * ((u + K) * q) ^ 5) := by dsimp [D]; ring
    rw [hD4, mul_div_mul_cancel_left' _ _ _ hden1]
  have h5 : D * (g2 / (C7 * ((u - K) * q) ^ 5)) = (u + K) ^ 5 * g2 := by
    have hD5 : D = (u + K) ^ 5 * (C7 * ((u - K) * q) ^ 5) := by dsimp [D]; ring
    rw [hD5, mul_div_mul_cancel_left' _ _ _ hden2]
  apply mul_left_cancel₀ hD
  rw [mul_add D, mul_add D, mul_sub D]
  change D * (u ^ 2 / ((u - K) * (u + K) * q) ^ 5) =
    (D * (a / den * (1 / q ^ 5)) + D * (b / den * (u ^ 2 / q ^ 5))) +
      (D * (g1 / (C7 * ((u + K) * q) ^ 5)) - D * (g2 / (C7 * ((u - K) * q) ^ 5)))
  rw [h1, h2, h3, h4, h5]
  dsimp [C7]
  rw [hid]
  ring

private lemma telescoping_0_rat (k m : ℕ) :
    1 / (Qℚ (k + 1) m) ^ 5 =
      M00 k * (1 / (Qℚ k (m + 1)) ^ 5) +
        M01 k * (((m : ℚ) + 2 + (k : ℚ)) ^ 2 / (Qℚ k (m + 1)) ^ 5) +
        (G0ℚ k (m + 1) - G0ℚ k m) := by
  unfold M00 M01 G0ℚ d0
  rw [Qℚ_succ_eq k m, Rℚ_succ_shift k m, Rℚ_succ_eq k m]
  set K : ℚ := (k : ℚ) + 1
  set u : ℚ := (m : ℚ) + 1 + K
  have hK : K ≠ 0 := by dsimp [K]; positivity
  have h2K1 : 2 * K - 1 ≠ 0 := by dsimp [K]; linarith [Nat.cast_nonneg (α := ℚ) k]
  have huK1 : u - K ≠ 0 := by
    have hsub : u - K = (m : ℚ) + 1 := by dsimp [u, K]; ring
    rw [hsub]; positivity
  have huK2 : u + K ≠ 0 := by dsimp [u, K]; positivity
  have hQ : Qℚ k (m + 1) ≠ 0 := (Qℚ_pos k (m + 1)).ne'
  have hm1 : (m : ℚ) + 1 = u - K := by dsimp [u, K]; ring
  have hm2 : (m : ℚ) + 1 + 2 * ((k : ℚ) + 1) = u + K := by dsimp [u, K]; ring
  have hm3 : (m : ℚ) + 2 + (k : ℚ) = u := by dsimp [u, K]; ring
  have hm4 : 2 * ((m : ℚ) + 1 + (k : ℚ) + 1) - 1 = 2 * u - 1 := by dsimp [u, K]; ring
  have hm5 : 2 * (((m + 1 : ℕ) : ℚ) + 1 + (k : ℚ) + 1) - 1 = 2 * u + 1 := by
    push_cast; dsimp [u, K]; ring
  rw [hm5, hm4, hm3, hm2, hm1]
  change
    1 / ((u - K) * (u + K) * Qℚ k (m + 1)) ^ 5 =
      p00 K / (128 * K ^ 9 * (2 * K - 1) ^ 7) * (1 / (Qℚ k (m + 1)) ^ 5) +
        p01 K / (128 * K ^ 9 * (2 * K - 1) ^ 7) * (u ^ 2 / (Qℚ k (m + 1)) ^ 5) +
        (tP0 K (2 * u + 1) / (65536 * K ^ 9 * (2 * K - 1) ^ 7 * ((u + K) * Qℚ k (m + 1)) ^ 5) -
          tP0 K (2 * u - 1) / (65536 * K ^ 9 * (2 * K - 1) ^ 7 * ((u - K) * Qℚ k (m + 1)) ^ 5))
  exact rational_step_0 K u (Qℚ k (m + 1)) (p00 K) (p01 K) (tP0 K (2 * u + 1)) (tP0 K (2 * u - 1))
    hK h2K1 huK1 huK2 hQ (poly_id_0 K u)

private lemma telescoping_1_rat (k m : ℕ) :
    ((m : ℚ) + 1 + (k : ℚ) + 1) ^ 2 / (Qℚ (k + 1) m) ^ 5 =
      M10 k * (1 / (Qℚ k (m + 1)) ^ 5) +
        M11 k * (((m : ℚ) + 2 + (k : ℚ)) ^ 2 / (Qℚ k (m + 1)) ^ 5) +
        (G1ℚ k (m + 1) - G1ℚ k m) := by
  unfold M10 M11 G1ℚ d1
  rw [Qℚ_succ_eq k m, Rℚ_succ_shift k m, Rℚ_succ_eq k m]
  set K : ℚ := (k : ℚ) + 1
  set u : ℚ := (m : ℚ) + 1 + K
  have hK : K ≠ 0 := by dsimp [K]; positivity
  have h2K1 : 2 * K - 1 ≠ 0 := by dsimp [K]; linarith [Nat.cast_nonneg (α := ℚ) k]
  have huK1 : u - K ≠ 0 := by
    have hsub : u - K = (m : ℚ) + 1 := by dsimp [u, K]; ring
    rw [hsub]; positivity
  have huK2 : u + K ≠ 0 := by dsimp [u, K]; positivity
  have hQ : Qℚ k (m + 1) ≠ 0 := (Qℚ_pos k (m + 1)).ne'
  have hm1 : (m : ℚ) + 1 = u - K := by dsimp [u, K]; ring
  have hm2 : (m : ℚ) + 1 + 2 * ((k : ℚ) + 1) = u + K := by dsimp [u, K]; ring
  have hm3 : (m : ℚ) + 2 + (k : ℚ) = u := by dsimp [u, K]; ring
  have hm4 : 2 * ((m : ℚ) + 1 + (k : ℚ) + 1) - 1 = 2 * u - 1 := by dsimp [u, K]; ring
  have hm5 : 2 * (((m + 1 : ℕ) : ℚ) + 1 + (k : ℚ) + 1) - 1 = 2 * u + 1 := by
    push_cast; dsimp [u, K]; ring
  have hm7 : (m : ℚ) + 1 + (k : ℚ) + 1 = u := by dsimp [u, K]; ring
  rw [hm5, hm4, hm7, hm3, hm2, hm1]
  change
    u ^ 2 / ((u - K) * (u + K) * Qℚ k (m + 1)) ^ 5 =
      p10 K / (128 * K ^ 7 * (2 * K - 1) ^ 7) * (1 / (Qℚ k (m + 1)) ^ 5) +
        p11 K / (128 * K ^ 7 * (2 * K - 1) ^ 7) * (u ^ 2 / (Qℚ k (m + 1)) ^ 5) +
        (tP1 K (2 * u + 1) / (65536 * K ^ 7 * (2 * K - 1) ^ 7 * ((u + K) * Qℚ k (m + 1)) ^ 5) -
          tP1 K (2 * u - 1) / (65536 * K ^ 7 * (2 * K - 1) ^ 7 * ((u - K) * Qℚ k (m + 1)) ^ 5))
  exact rational_step_1 K u (Qℚ k (m + 1)) (p10 K) (p11 K) (tP1 K (2 * u + 1)) (tP1 K (2 * u - 1))
    hK h2K1 huK1 huK2 hQ (poly_id_1 K u)

private lemma telescoping_0 (k m : ℕ) :
    f0 (k + 1) m =
      (M00 k : ℂ) * f0 k (m + 1) + (M01 k : ℂ) * f2 k (m + 1) + (G0 k (m + 1) - G0 k m) := by
  unfold f0 f2 G0
  have h := congrArg (fun x : ℚ => (x : ℂ)) (telescoping_0_rat k m)
  push_cast at h
  convert h using 3
  push_cast
  ring

private lemma telescoping_1 (k m : ℕ) :
    f2 (k + 1) m =
      (M10 k : ℂ) * f0 k (m + 1) + (M11 k : ℂ) * f2 k (m + 1) + (G1 k (m + 1) - G1 k m) := by
  unfold f0 f2 G1
  have h := congrArg (fun x : ℚ => (x : ℂ)) (telescoping_1_rat k m)
  push_cast at h
  convert h using 3 <;> (push_cast; ring)

private lemma tendsto_poly_div_R_pow_five
    (k : ℕ) (a0 a2 a4 a6 a8 D : ℝ) (hD : 0 < D) :
    Tendsto
      (fun m : ℕ =>
        (((a0 + a2 * (2 * ((m : ℝ) + 1 + (k : ℝ) + 1) - 1) ^ 2
            + a4 * (2 * ((m : ℝ) + 1 + (k : ℝ) + 1) - 1) ^ 4
            + a6 * (2 * ((m : ℝ) + 1 + (k : ℝ) + 1) - 1) ^ 6
            + a8 * (2 * ((m : ℝ) + 1 + (k : ℝ) + 1) - 1) ^ 8) /
          (D * (Rℚ (k + 1) m : ℝ) ^ 5) : ℝ) : ℂ))
      atTop (𝓝 0) := by
  let M : ℝ := 2 * (k : ℝ) + 4
  let C : ℝ := (|a0| + |a2| + |a4| + |a6| + |a8|) * M ^ 8 / D
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hlim : Tendsto (fun m : ℕ => C * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    simpa [mul_zero] using
      (tendsto_const_nhds (x := C)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine squeeze_zero_norm (fun m => ?_) hlim
  set y : ℝ := (m : ℝ) + 1
  set X : ℝ := 2 * (y + (k : ℝ) + 1) - 1
  have hy1 : 1 ≤ y := by dsimp [y]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hX0 : 0 ≤ X := by dsimp [X]; linarith
  have hXM : X ≤ M * y := by
    dsimp [X, M]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hy8 : 1 ≤ y ^ 8 := one_le_pow₀ hy1
  have hM2 : M ^ 2 ≤ M ^ 8 := pow_le_pow_right₀ hM (by omega)
  have hM4 : M ^ 4 ≤ M ^ 8 := pow_le_pow_right₀ hM (by omega)
  have hM6 : M ^ 6 ≤ M ^ 8 := pow_le_pow_right₀ hM (by omega)
  have hM8 : 1 ≤ M ^ 8 := one_le_pow₀ hM
  have hy28 : y ^ 2 ≤ y ^ 8 := pow_le_pow_right₀ hy1 (by omega)
  have hy48 : y ^ 4 ≤ y ^ 8 := pow_le_pow_right₀ hy1 (by omega)
  have hy68 : y ^ 6 ≤ y ^ 8 := pow_le_pow_right₀ hy1 (by omega)
  have hX2 : X ^ 2 ≤ M ^ 8 * y ^ 8 := by
    calc X ^ 2 ≤ (M * y) ^ 2 := by gcongr
    _ = M ^ 2 * y ^ 2 := by ring
    _ ≤ M ^ 8 * y ^ 8 := by gcongr
  have hX4 : X ^ 4 ≤ M ^ 8 * y ^ 8 := by
    calc X ^ 4 ≤ (M * y) ^ 4 := by gcongr
    _ = M ^ 4 * y ^ 4 := by ring
    _ ≤ M ^ 8 * y ^ 8 := by gcongr
  have hX6 : X ^ 6 ≤ M ^ 8 * y ^ 8 := by
    calc X ^ 6 ≤ (M * y) ^ 6 := by gcongr
    _ = M ^ 6 * y ^ 6 := by ring
    _ ≤ M ^ 8 * y ^ 8 := by gcongr
  have hX8 : X ^ 8 ≤ M ^ 8 * y ^ 8 := by
    calc X ^ 8 ≤ (M * y) ^ 8 := by gcongr
    _ = M ^ 8 * y ^ 8 := by ring
  have hnum :
      |a0 + a2 * X ^ 2 + a4 * X ^ 4 + a6 * X ^ 6 + a8 * X ^ 8| ≤
        (|a0| + |a2| + |a4| + |a6| + |a8|) * M ^ 8 * y ^ 8 := by
    calc
      |a0 + a2 * X ^ 2 + a4 * X ^ 4 + a6 * X ^ 6 + a8 * X ^ 8|
        ≤ |a0| + |a2 * X ^ 2| + |a4 * X ^ 4| + |a6 * X ^ 6| + |a8 * X ^ 8| := by
          linarith [abs_add_le (a0 + a2 * X ^ 2 + a4 * X ^ 4 + a6 * X ^ 6) (a8 * X ^ 8),
            abs_add_le (a0 + a2 * X ^ 2 + a4 * X ^ 4) (a6 * X ^ 6),
            abs_add_le (a0 + a2 * X ^ 2) (a4 * X ^ 4),
            abs_add_le a0 (a2 * X ^ 2)]
      _ = |a0| + |a2| * X ^ 2 + |a4| * X ^ 4 + |a6| * X ^ 6 + |a8| * X ^ 8 := by
          simp only [abs_mul, abs_pow, abs_of_nonneg hX0]
      _ ≤ |a0| * (M ^ 8 * y ^ 8) + |a2| * (M ^ 8 * y ^ 8) + |a4| * (M ^ 8 * y ^ 8) +
            |a6| * (M ^ 8 * y ^ 8) + |a8| * (M ^ 8 * y ^ 8) := by
          have h1M : 1 ≤ M ^ 8 * y ^ 8 := by nlinarith
          gcongr
          exact le_mul_of_one_le_right (abs_nonneg a0) h1M
      _ = (|a0| + |a2| + |a4| + |a6| + |a8|) * M ^ 8 * y ^ 8 := by ring
  have hR : y ^ 2 ≤ (Rℚ (k + 1) m : ℝ) := add_one_sq_le_Rℚ_succ_real k m
  have hRpos0 : (0 : ℝ) < (Rℚ (k + 1) m : ℝ) := by exact_mod_cast Rℚ_pos (k + 1) m
  have hR5 : y ^ 10 ≤ (Rℚ (k + 1) m : ℝ) ^ 5 := by
    calc y ^ 10 = (y ^ 2) ^ 5 := by ring
    _ ≤ (Rℚ (k + 1) m : ℝ) ^ 5 := by gcongr
  have hden : D * y ^ 10 ≤ D * (Rℚ (k + 1) m : ℝ) ^ 5 := by gcongr
  have hDRpos : 0 < D * (Rℚ (k + 1) m : ℝ) ^ 5 := by positivity
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hy2 : y ≤ y ^ 2 := by
    rw [sq]
    exact le_mul_of_one_le_right hy0 hy1
  have hinv : 1 / y ^ 2 ≤ 1 / y := one_div_le_one_div_of_le (by positivity) hy2
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hDRpos]
  calc
    |a0 + a2 * X ^ 2 + a4 * X ^ 4 + a6 * X ^ 6 + a8 * X ^ 8| / (D * (Rℚ (k + 1) m : ℝ) ^ 5)
      ≤ ((|a0| + |a2| + |a4| + |a6| + |a8|) * M ^ 8 * y ^ 8) / (D * y ^ 10) := by gcongr
    _ = C * (1 / y ^ 2) := by dsimp [C]; field_simp
    _ ≤ C * (1 / y) := by gcongr

private lemma tendsto_G0 (k : ℕ) : Tendsto (G0 k) atTop (𝓝 0) := by
  let K : ℝ := (k : ℝ) + 1
  let t : ℝ := 2 * K - 1
  let a0 := t ^ 7 * (-35 + 525 * K - 3180 * K ^ 2 + 9400 * K ^ 3 - 11768 * K ^ 4)
  let a2 := 20 * t ^ 6 * (-7 + 84 * K - 366 * K ^ 2 + 592 * K ^ 3)
  let a4 := 70 * t ^ 4 * (3 - 33 * K + 126 * K ^ 2 - 164 * K ^ 3)
  let a6 := 140 * t ^ 2 * (-1 + 10 * K - 34 * K ^ 2 + 40 * K ^ 3)
  let a8 := 5 * (7 - 63 * K + 198 * K ^ 2 - 220 * K ^ 3)
  let D : ℝ := 65536 * K ^ 9 * t ^ 7
  have hK : 0 < K := by dsimp [K]; positivity
  have ht : 0 < t := by dsimp [t, K]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hlim := tendsto_poly_div_R_pow_five k a0 a2 a4 a6 a8 D hD
  refine hlim.congr fun m => ?_
  have hq :
      ((G0 k m)) =
        (((G0ℚ k m : ℚ) : ℝ) : ℂ) := by
    unfold G0
    norm_cast
  rw [hq]
  congr 1
  unfold G0ℚ tP0
  push_cast
  dsimp [a0, a2, a4, a6, a8, D, t, K]
  ring

private lemma tendsto_G1 (k : ℕ) : Tendsto (G1 k) atTop (𝓝 0) := by
  let K : ℝ := (k : ℝ) + 1
  let t : ℝ := 2 * K - 1
  let a0 := t ^ 7 * (5 - 75 * K + 388 * K ^ 2 - 440 * K ^ 3 - 2200 * K ^ 4)
  let a2 := 4 * t ^ 6 * (5 - 60 * K + 218 * K ^ 2 - 96 * K ^ 3)
  let a4 := 10 * t ^ 4 * (-3 + 33 * K - 110 * K ^ 2 + 84 * K ^ 3)
  let a6 := 4 * t ^ 2 * (5 - 50 * K + 154 * K ^ 2 - 120 * K ^ 3)
  let a8 := 5 * (-1 + 9 * K - 26 * K ^ 2 + 20 * K ^ 3)
  let D : ℝ := 65536 * K ^ 7 * t ^ 7
  have hK : 0 < K := by dsimp [K]; positivity
  have ht : 0 < t := by dsimp [t, K]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hlim := tendsto_poly_div_R_pow_five k a0 a2 a4 a6 a8 D hD
  refine hlim.congr fun m => ?_
  have hq :
      ((G1 k m)) =
        (((G1ℚ k m : ℚ) : ℝ) : ℂ) := by
    unfold G1
    norm_cast
  rw [hq]
  congr 1
  unfold G1ℚ tP1
  push_cast
  dsimp [a0, a2, a4, a6, a8, D, t, K]
  ring

private lemma sum_range_sub_succ (g : ℕ → ℂ) (N : ℕ) :
    ∑ m ∈ range N, (g (m + 1) - g m) = g N - g 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private lemma tendsto_sum_range_succ_of_summable {g : ℕ → ℂ} (hg : Summable g) :
    Tendsto (fun N : ℕ => ∑ m ∈ range N, g (m + 1)) atTop (𝓝 ((∑' m : ℕ, g m) - g 0)) := by
  have heq :
      (fun N : ℕ => ∑ m ∈ range N, g (m + 1)) =
        (fun N : ℕ => (∑ m ∈ range (N + 1), g m) - g 0) := by
    ext N
    rw [Finset.sum_range_succ']
    ring
  rw [heq]
  have h1 : Tendsto (fun N : ℕ => ∑ m ∈ range (N + 1), g m) atTop (𝓝 (∑' m : ℕ, g m)) :=
    hg.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact h1.sub tendsto_const_nhds

private noncomputable def S0 (k : ℕ) : ℂ := ∑' m : ℕ, f0 k m
private noncomputable def S2 (k : ℕ) : ℂ := ∑' m : ℕ, f2 k m

private lemma S0_succ (k : ℕ) :
    S0 (k + 1) =
      (M00 k : ℂ) * (S0 k - f0 k 0) + (M01 k : ℂ) * (S2 k - f2 k 0) - G0 k 0 := by
  have hL :
      Tendsto (fun N : ℕ => ∑ m ∈ range N, f0 (k + 1) m) atTop (𝓝 (S0 (k + 1))) :=
    (summable_f0 (k + 1)).hasSum.tendsto_sum_nat
  have hsum :
      (fun N : ℕ => ∑ m ∈ range N, f0 (k + 1) m) =
        fun N : ℕ =>
          (M00 k : ℂ) * (∑ m ∈ range N, f0 k (m + 1)) +
            (M01 k : ℂ) * (∑ m ∈ range N, f2 k (m + 1)) +
            (G0 k N - G0 k 0) := by
    ext N
    simp_rw [telescoping_0, Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_sub_succ]
  have hR :
      Tendsto
        (fun N : ℕ =>
          (M00 k : ℂ) * (∑ m ∈ range N, f0 k (m + 1)) +
            (M01 k : ℂ) * (∑ m ∈ range N, f2 k (m + 1)) +
            (G0 k N - G0 k 0))
        atTop
        (𝓝 ((M00 k : ℂ) * (S0 k - f0 k 0) + (M01 k : ℂ) * (S2 k - f2 k 0) + (0 - G0 k 0))) := by
    refine ((tendsto_const_nhds.mul (tendsto_sum_range_succ_of_summable (summable_f0 k))).add
      (tendsto_const_nhds.mul (tendsto_sum_range_succ_of_summable (summable_f2 k)))).add
      ((tendsto_G0 k).sub tendsto_const_nhds)
  have heq := tendsto_nhds_unique hL (hsum ▸ hR)
  rw [heq]
  ring

private lemma S2_succ (k : ℕ) :
    S2 (k + 1) =
      (M10 k : ℂ) * (S0 k - f0 k 0) + (M11 k : ℂ) * (S2 k - f2 k 0) - G1 k 0 := by
  have hL :
      Tendsto (fun N : ℕ => ∑ m ∈ range N, f2 (k + 1) m) atTop (𝓝 (S2 (k + 1))) :=
    (summable_f2 (k + 1)).hasSum.tendsto_sum_nat
  have hsum :
      (fun N : ℕ => ∑ m ∈ range N, f2 (k + 1) m) =
        fun N : ℕ =>
          (M10 k : ℂ) * (∑ m ∈ range N, f0 k (m + 1)) +
            (M11 k : ℂ) * (∑ m ∈ range N, f2 k (m + 1)) +
            (G1 k N - G1 k 0) := by
    ext N
    simp_rw [telescoping_1, Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_sub_succ]
  have hR :
      Tendsto
        (fun N : ℕ =>
          (M10 k : ℂ) * (∑ m ∈ range N, f0 k (m + 1)) +
            (M11 k : ℂ) * (∑ m ∈ range N, f2 k (m + 1)) +
            (G1 k N - G1 k 0))
        atTop
        (𝓝 ((M10 k : ℂ) * (S0 k - f0 k 0) + (M11 k : ℂ) * (S2 k - f2 k 0) + (0 - G1 k 0))) := by
    refine ((tendsto_const_nhds.mul (tendsto_sum_range_succ_of_summable (summable_f0 k))).add
      (tendsto_const_nhds.mul (tendsto_sum_range_succ_of_summable (summable_f2 k)))).add
      ((tendsto_G1 k).sub tendsto_const_nhds)
  have heq := tendsto_nhds_unique hL (hsum ▸ hR)
  rw [heq]
  ring

private lemma S0_zero : S0 0 = riemannZeta (5 : ℂ) := by
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow (s := (5 : ℂ)) (by norm_num)
  rw [hz]
  unfold S0 f0
  congr 1 with m
  have h5 : ((5 : ℕ) : ℂ) = (5 : ℂ) := by norm_cast
  rw [Qℚ_zero]
  push_cast
  rw [← h5, Complex.cpow_natCast]

private lemma S2_zero : S2 0 = riemannZeta (3 : ℂ) := by
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow (s := (3 : ℂ)) (by norm_num)
  rw [hz]
  unfold S2 f2
  congr 1 with m
  have h3 : ((3 : ℕ) : ℂ) = (3 : ℂ) := by norm_cast
  have hm : (m : ℂ) + 1 ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  rw [Qℚ_zero]
  push_cast
  rw [← h3, Complex.cpow_natCast]
  field_simp
  ring

end SeriesAndTelescoping

section LinearRecurrenceAndCone

private def seq : ℕ → ℚ × ℚ × ℚ × ℚ × ℚ × ℚ
  | 0 => (0, 1, 0, 0, 0, 1)
  | k + 1 =>
    let (r0, q5, q3, r2, p5, p3) := seq k
    let f00 := 1 / (Qℚ k 0) ^ 5
    let f20 := ((k : ℚ) + 1) ^ 2 / (Qℚ k 0) ^ 5
    ( M00 k * (r0 - f00) + M01 k * (r2 - f20) - G0ℚ k 0
    , M00 k * q5 + M01 k * p5
    , M00 k * q3 + M01 k * p3
    , M10 k * (r0 - f00) + M11 k * (r2 - f20) - G1ℚ k 0
    , M10 k * q5 + M11 k * p5
    , M10 k * q3 + M11 k * p3 )

private def r0 (k : ℕ) : ℚ := (seq k).1
private def q5 (k : ℕ) : ℚ := (seq k).2.1
private def q3 (k : ℕ) : ℚ := (seq k).2.2.1
private def r2 (k : ℕ) : ℚ := (seq k).2.2.2.1
private def p5 (k : ℕ) : ℚ := (seq k).2.2.2.2.1
private def p3 (k : ℕ) : ℚ := (seq k).2.2.2.2.2

private lemma r0_succ (k : ℕ) :
    r0 (k + 1) =
      M00 k * (r0 k - 1 / (Qℚ k 0) ^ 5) + M01 k * (r2 k - ((k : ℚ) + 1) ^ 2 / (Qℚ k 0) ^ 5) -
        G0ℚ k 0 := rfl

private lemma q5_succ (k : ℕ) : q5 (k + 1) = M00 k * q5 k + M01 k * p5 k := rfl
private lemma q3_succ (k : ℕ) : q3 (k + 1) = M00 k * q3 k + M01 k * p3 k := rfl

private lemma r2_succ (k : ℕ) :
    r2 (k + 1) =
      M10 k * (r0 k - 1 / (Qℚ k 0) ^ 5) + M11 k * (r2 k - ((k : ℚ) + 1) ^ 2 / (Qℚ k 0) ^ 5) -
        G1ℚ k 0 := rfl

private lemma p5_succ (k : ℕ) : p5 (k + 1) = M10 k * q5 k + M11 k * p5 k := rfl
private lemma p3_succ (k : ℕ) : p3 (k + 1) = M10 k * q3 k + M11 k * p3 k := rfl

private lemma seq_linear_form (k : ℕ) :
    S0 k = (r0 k : ℂ) + (q5 k : ℂ) * riemannZeta 5 + (q3 k : ℂ) * riemannZeta 3 ∧
      S2 k = (r2 k : ℂ) + (p5 k : ℂ) * riemannZeta 5 + (p3 k : ℂ) * riemannZeta 3 := by
  induction k with
  | zero =>
    simp [r0, q5, q3, r2, p5, p3, seq, S0_zero, S2_zero]
  | succ k ih =>
    rcases ih with ⟨ih0, ih2⟩
    have hf00 : f0 k 0 = ((1 / (Qℚ k 0) ^ 5 : ℚ) : ℂ) := by
      unfold f0; push_cast; rfl
    have hf20 : f2 k 0 = ((((k : ℚ) + 1) ^ 2 / (Qℚ k 0) ^ 5 : ℚ) : ℂ) := by
      unfold f2; push_cast; ring
    have hG00 : G0 k 0 = (G0ℚ k 0 : ℂ) := rfl
    have hG10 : G1 k 0 = (G1ℚ k 0 : ℂ) := rfl
    have hrec0 := S0_succ k
    have hrec2 := S2_succ k
    rw [ih0, ih2, hf00, hf20, hG00] at hrec0
    rw [ih0, ih2, hf00, hf20, hG10] at hrec2
    constructor
    · rw [hrec0, r0_succ, q5_succ, q3_succ]
      push_cast
      ring
    · rw [hrec2, r2_succ, p5_succ, p3_succ]
      push_cast
      ring

private lemma seq_det_pos (k : ℕ) : 0 < q5 k * p3 k - q3 k * p5 k := by
  induction k with
  | zero =>
    norm_num [q5, q3, p5, p3, seq]
  | succ k ih =>
    have hstep :
        q5 (k + 1) * p3 (k + 1) - q3 (k + 1) * p5 (k + 1) =
          (M00 k * M11 k - M01 k * M10 k) * (q5 k * p3 k - q3 k * p5 k) := by
      rw [q5_succ, p3_succ, q3_succ, p5_succ]
      ring
    rw [hstep]
    exact mul_pos (detM_pos k) ih

private def coneX (k : ℕ) : ℚ := (-1 : ℚ) ^ k * q3 k
private def coneY (k : ℕ) : ℚ := (-1 : ℚ) ^ (k + 1) * p3 k

private lemma cone_invariant (j : ℕ) :
    0 < coneX (j + 1) ∧ 0 < coneY (j + 1) ∧ coneY (j + 1) < ((j : ℚ) + 1) ^ 2 * coneX (j + 1) := by
  induction j with
  | zero =>
    have hx1 : coneX 1 = 195 / 64 := by
      simp [coneX, q3, seq, M00, M01, p00, p01, d0]
      norm_num
    have hy1 : coneY 1 = 5 / 64 := by
      simp [coneY, p3, seq, M10, M11, p10, p11, d1]
      norm_num
    simp [hx1, hy1]
    norm_num
  | succ j ih =>
    rcases ih with ⟨hx, hy, hyx⟩
    set t : ℚ := (j : ℚ)
    have ht : 0 ≤ t := Nat.cast_nonneg j
    set K : ℚ := t + 2
    have hKcast : ((j + 1 : ℕ) : ℚ) + 1 = K := by dsimp [K, t]; push_cast; ring
    have hd0_pos : 0 < d0 (j + 1) := d0_pos (j + 1)
    have hd1_pos : 0 < d1 (j + 1) := d1_pos (j + 1)
    have hd0_eq : d0 (j + 1) = K ^ 2 * d1 (j + 1) := by
      rw [d0_eq (j + 1), hKcast]
    have hstepX :
        d0 (j + 1) * coneX (j + 2) =
          (-p00 K) * coneX (j + 1) - (-p01 K) * coneY (j + 1) := by
      unfold coneX coneY
      have hq3 : q3 (j + 2) = M00 (j + 1) * q3 (j + 1) + M01 (j + 1) * p3 (j + 1) := by
        unfold q3 seq; dsimp only; rfl
      rw [hq3]
      unfold M00 M01
      rw [hKcast]
      have hd0_ne : d0 (j + 1) ≠ 0 := hd0_pos.ne'
      field_simp
      ring
    have hstepY :
        d1 (j + 1) * coneY (j + 2) =
          p10 K * coneX (j + 1) - p11 K * coneY (j + 1) := by
      unfold coneX coneY
      have hp3 : p3 (j + 2) = M10 (j + 1) * q3 (j + 1) + M11 (j + 1) * p3 (j + 1) := by
        unfold p3 seq; dsimp only; rfl
      rw [hp3]
      unfold M10 M11
      rw [hKcast]
      have hd1_ne : d1 (j + 1) ≠ 0 := hd1_pos.ne'
      field_simp
      ring
    set a : ℚ := -p00 K
    set b : ℚ := -p01 K
    set c : ℚ := p10 K
    set d : ℚ := p11 K
    have hb_eq : b = 32610 + 84505 * t + 81435 * t ^ 2 + 34650 * t ^ 3 + 5500 * t ^ 4 := by
      dsimp [b, K]; unfold p01; ring
    have hd_eq : d = 2190 + 6175 * t + 6445 * t ^ 2 + 2950 * t ^ 3 + 500 * t ^ 4 := by
      dsimp [d, K]; unfold p11; ring
    have hbd_eq : b - d = 30420 + 78330 * t + 74990 * t ^ 2 + 31700 * t ^ 3 + 5000 * t ^ 4 := by
      rw [hb_eq, hd_eq]; ring
    have hab_eq :
        a - b * (t + 1) ^ 2 =
          79580 + 305850 * t + 486570 * t ^ 2 + 410190 * t ^ 3 + 193310 * t ^ 4 +
            48300 * t ^ 5 + 5000 * t ^ 6 := by
      dsimp [a, b, K]; unfold p00 p01; ring
    have hcd_eq :
        c - d * (t + 1) ^ 2 =
          7748 + 30902 * t + 51014 * t ^ 2 + 44594 * t ^ 3 + 21762 * t ^ 4 +
            5620 * t ^ 5 + 600 * t ^ 6 := by
      dsimp [c, d, K]; unfold p10 p11; ring
    have hacbd_eq :
        (a - c) - (b - d) * (t + 1) ^ 2 =
          71832 + 274948 * t + 435556 * t ^ 2 + 365596 * t ^ 3 + 171548 * t ^ 4 +
            42680 * t ^ 5 + 4400 * t ^ 6 := by
      rw [show (a - c) - (b - d) * (t + 1) ^ 2 =
        (a - b * (t + 1) ^ 2) - (c - d * (t + 1) ^ 2) by ring, hab_eq, hcd_eq]
      ring
    have hb_pos : 0 < b := by rw [hb_eq]; positivity
    have hd_pos : 0 < d := by rw [hd_eq]; positivity
    have hbd_pos : 0 < b - d := by rw [hbd_eq]; positivity
    have hab_pos : 0 < a - b * (t + 1) ^ 2 := by rw [hab_eq]; positivity
    have hcd_pos : 0 < c - d * (t + 1) ^ 2 := by rw [hcd_eq]; positivity
    have hacbd_pos : 0 < (a - c) - (b - d) * (t + 1) ^ 2 := by rw [hacbd_eq]; positivity
    have hX_scaled : 0 < d0 (j + 1) * coneX (j + 2) := by
      rw [hstepX]
      nlinarith
    have hY_scaled : 0 < d1 (j + 1) * coneY (j + 2) := by
      rw [hstepY]
      nlinarith
    have hYX_scaled : d1 (j + 1) * coneY (j + 2) < d0 (j + 1) * coneX (j + 2) := by
      rw [hstepX, hstepY]
      nlinarith
    have hx' : 0 < coneX (j + 2) := (mul_pos_iff_of_pos_left hd0_pos).mp hX_scaled
    have hy' : 0 < coneY (j + 2) := (mul_pos_iff_of_pos_left hd1_pos).mp hY_scaled
    have hyx' : coneY (j + 2) < (((j + 1 : ℕ) : ℚ) + 1) ^ 2 * coneX (j + 2) := by
      have hcastK : (((j + 1 : ℕ) : ℚ) + 1) ^ 2 = K ^ 2 := by rw [hKcast]
      rw [hcastK]
      rw [hd0_eq] at hYX_scaled
      have hmul : d1 (j + 1) * coneY (j + 2) < d1 (j + 1) * (K ^ 2 * coneX (j + 2)) := by
        linarith
      exact lt_of_mul_lt_mul_left hmul hd1_pos.le
    exact ⟨hx', hy', hyx'⟩

private lemma q3_ne_zero (k : ℕ) (hk : 1 ≤ k) : q3 k ≠ 0 := by
  cases k with
  | zero => omega
  | succ j =>
    have hx : 0 < coneX (j + 1) := (cone_invariant j).1
    intro h0
    unfold coneX at hx
    rw [h0, mul_zero] at hx
    exact lt_irrefl 0 hx

end LinearRecurrenceAndCone

end OMA.P_oeis_a013663

open OMA.P_oeis_a013663 OMA.S_oeis_a013663 in
theorem OMA.solution : type_of% @OMA.S_oeis_a013663.main := by
  intro k hk
  let lam : ℚ := -p3 k / q3 k
  let c : ℚ := (k : ℚ) ^ 2 + lam
  let α : ℚ := p5 k + lam * q5 k
  let β : ℚ := r2 k + lam * r0 k
  let A : ℚ := -β / α
  let B : ℚ := 1 / α
  have hq3 : q3 k ≠ 0 := q3_ne_zero k hk
  have hdet : 0 < q5 k * p3 k - q3 k * p5 k := seq_det_pos k
  have hα : α ≠ 0 := by
    intro h0
    have hmul : α * q3 k = -(q5 k * p3 k - q3 k * p5 k) := by
      dsimp [α, lam]
      field_simp
      ring
    rw [h0, zero_mul] at hmul
    linarith
  have hterm :
      (fun m : ℕ => balaTerm k c m) = fun m : ℕ => f2 k m + (lam : ℂ) * f0 k m := by
    ext m
    unfold balaTerm f2 f0
    dsimp only
    rw [← Qℚ_cast]
    have hc : (c : ℂ) = ((k : ℂ) ^ 2 + (lam : ℂ)) := by
      dsimp [c]; push_cast; rfl
    rw [hc]
    ring
  have htsum :
      ∑' m : ℕ, balaTerm k c m = S2 k + (lam : ℂ) * S0 k := by
    rw [hterm, (summable_f2 k).tsum_add ((summable_f0 k).mul_left (lam : ℂ)), tsum_mul_left]
    rfl
  have hlin := seq_linear_form k
  have hz3 : p3 k + lam * q3 k = 0 := by
    dsimp [lam]
    field_simp
    ring
  refine ⟨A, B, c, ?_⟩
  rw [htsum, hlin.1, hlin.2]
  have hcomb :
      ((r2 k : ℂ) + (p5 k : ℂ) * riemannZeta 5 + (p3 k : ℂ) * riemannZeta 3) +
          (lam : ℂ) * ((r0 k : ℂ) + (q5 k : ℂ) * riemannZeta 5 + (q3 k : ℂ) * riemannZeta 3) =
        (β : ℂ) + (α : ℂ) * riemannZeta 5 := by
    have h1 : (β : ℂ) = (r2 k : ℂ) + (lam : ℂ) * (r0 k : ℂ) := by dsimp [β]; push_cast; rfl
    have h2 : (α : ℂ) = (p5 k : ℂ) + (lam : ℂ) * (q5 k : ℂ) := by dsimp [α]; push_cast; rfl
    have h3 : (p3 k : ℂ) + (lam : ℂ) * (q3 k : ℂ) = 0 := by exact_mod_cast hz3
    rw [h1, h2]
    linear_combination riemannZeta 3 * h3
  rw [hcomb]
  have hA : (A : ℂ) = -(β : ℂ) / (α : ℂ) := by dsimp [A]; push_cast; rfl
  have hB : (B : ℂ) = 1 / (α : ℂ) := by dsimp [B]; push_cast; rfl
  have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  rw [hA, hB]
  field_simp
  ring
