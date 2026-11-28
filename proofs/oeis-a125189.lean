import OMAStatements.S_oeis_a125189

open PowerSeries

namespace ProofA125189

abbrev S := OMA.S_oeis_a125189.Series

lemma radical_sq : OMA.S_oeis_a125189.radical ^ 2 = OMA.S_oeis_a125189.radicand := by
  set b := PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)
  have hb2 : b ^ 2 = 1 + (X : S) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    have hhalf : (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) := by norm_num
    rw [hhalf, PowerSeries.binomialSeries_nat, pow_one]
  have h0 : MvPowerSeries.constantCoeff (OMA.S_oeis_a125189.radicand - 1) = 0 := by
    change constantCoeff (OMA.S_oeis_a125189.radicand - 1) = 0
    simp [OMA.S_oeis_a125189.radicand]
  have hsub : PowerSeries.HasSubst (OMA.S_oeis_a125189.radicand - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero h0
  have heval := congr_arg (PowerSeries.substAlgHom hsub) hb2
  rw [map_pow, map_add, map_one, PowerSeries.substAlgHom_X hsub,
    PowerSeries.coe_substAlgHom hsub] at heval
  change b.subst (OMA.S_oeis_a125189.radicand - 1) ^ 2 = OMA.S_oeis_a125189.radicand
  rw [heval]
  ring

lemma radical_constantCoeff : constantCoeff OMA.S_oeis_a125189.radical = 1 := by
  set b := PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)
  set u := OMA.S_oeis_a125189.radicand - 1
  have hu0 : MvPowerSeries.constantCoeff u = 0 := by
    change constantCoeff u = 0
    simp [u, OMA.S_oeis_a125189.radicand]
  have hsub : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu0
  have hb0 : (b - 1).constantCoeff = 0 := by simp [b]
  have hzero : MvPowerSeries.constantCoeff ((b - 1).subst u) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hu0 (b - 1) hb0
  have hdiff : (b - 1).subst u = OMA.S_oeis_a125189.radical - 1 := by
    rw [PowerSeries.subst_sub hsub]
    have h1 : (1 : S).subst u = 1 := by
      rw [← PowerSeries.coe_substAlgHom hsub, map_one]
    rw [h1]
    rfl
  have hc : constantCoeff (OMA.S_oeis_a125189.radical - 1) = 0 := by
    rw [← hdiff]
    exact hzero
  rw [map_sub, map_one, sub_eq_zero] at hc
  exact hc

lemma gf_relation :
    (X : S) * OMA.S_oeis_a125189.denominatorFactor * OMA.S_oeis_a125189.gf =
      OMA.S_oeis_a125189.numeratorHead -
        OMA.S_oeis_a125189.radicalFactor * OMA.S_oeis_a125189.radical := by
  set φ := OMA.S_oeis_a125189.numeratorHead -
    OMA.S_oeis_a125189.radicalFactor * OMA.S_oeis_a125189.radical
  have hφ0 : constantCoeff φ = 0 := by
    simp [φ, OMA.S_oeis_a125189.numeratorHead, OMA.S_oeis_a125189.radicalFactor,
      radical_constantCoeff]
  have hshift : (X : S) * OMA.S_oeis_a125189.removeX φ = φ := by
    have h := (PowerSeries.sub_const_eq_X_mul_shift φ).symm
    rw [hφ0, map_zero, sub_zero] at h
    exact h
  have hden0 : constantCoeff OMA.S_oeis_a125189.denominatorFactor ≠ 0 := by
    simp [OMA.S_oeis_a125189.denominatorFactor, map_ofNat]
  calc (X : S) * OMA.S_oeis_a125189.denominatorFactor * OMA.S_oeis_a125189.gf
    _ = ((X : S) * OMA.S_oeis_a125189.removeX φ) *
        (OMA.S_oeis_a125189.denominatorFactor * OMA.S_oeis_a125189.denominatorFactor⁻¹) := by
      unfold OMA.S_oeis_a125189.gf
      ring
    _ = φ := by rw [hshift, PowerSeries.mul_inv_cancel _ hden0, mul_one]

lemma deriv_natCast (m : ℕ) : (PowerSeries.derivative ℚ) (m : S) = 0 := by
  rw [← map_natCast C m]
  exact PowerSeries.derivative_C

lemma deriv_X_pow (k : ℕ) : (PowerSeries.derivative ℚ) ((X : S) ^ k) = (k : S) * X ^ (k - 1) := by
  rw [PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one]

lemma ode_proof :
    OMA.S_oeis_a125189.odeConstant + OMA.S_oeis_a125189.odeValue * OMA.S_oeis_a125189.gf +
      OMA.S_oeis_a125189.odeDerivative * (PowerSeries.derivative ℚ OMA.S_oeis_a125189.gf) = 0 := by
  set D := PowerSeries.derivative ℚ
  set R := OMA.S_oeis_a125189.radicand
  set N := OMA.S_oeis_a125189.numeratorHead
  set F := OMA.S_oeis_a125189.radicalFactor
  set Q := OMA.S_oeis_a125189.denominatorFactor
  set Rad := OMA.S_oeis_a125189.radical
  set G := OMA.S_oeis_a125189.gf
  have hDX : D (X : S) = 1 := PowerSeries.derivative_X
  have hDR : D R = -4 * X - 12 * X ^ 3 := by
    dsimp [R, OMA.S_oeis_a125189.radicand]
    have h1 : (1 : S) = ((1 : ℕ) : S) := by norm_num
    have h2 : (2 : S) = ((2 : ℕ) : S) := by norm_num
    have h3 : (3 : S) = ((3 : ℕ) : S) := by norm_num
    rw [map_sub, map_sub, h1, h2, h3, D.leibniz, D.leibniz,
      deriv_natCast 1, deriv_natCast 2, deriv_natCast 3, deriv_X_pow 2, deriv_X_pow 4]
    simp only [smul_eq_mul]; norm_num; ring
  have hDN : D N = -4 * X ^ 3 := by
    dsimp [N, OMA.S_oeis_a125189.numeratorHead]
    have h1 : (1 : S) = ((1 : ℕ) : S) := by norm_num
    rw [map_sub, h1, deriv_natCast 1, deriv_X_pow 4]
    norm_num
  have hDF : D F = 2 * (1 + X) := by
    dsimp [F, OMA.S_oeis_a125189.radicalFactor]
    have h1 : (1 : S) = ((1 : ℕ) : S) := by norm_num
    rw [PowerSeries.derivative_pow, map_add, h1, deriv_natCast 1, hDX]
    norm_num
  have hDQ : D Q = 2 * (3 * X ^ 2 + 2 * X + 1) := by
    dsimp [Q, OMA.S_oeis_a125189.denominatorFactor]
    have h2 : (2 : S) = ((2 : ℕ) : S) := by norm_num
    have h1 : (1 : S) = ((1 : ℕ) : S) := by norm_num
    rw [h2, D.leibniz, deriv_natCast 2, map_sub, map_add, map_add,
      deriv_X_pow 3, deriv_X_pow 2, hDX, h1, deriv_natCast 1]
    simp only [smul_eq_mul]; norm_num
  have hRad_ne : constantCoeff Rad ≠ 0 := by rw [radical_constantCoeff]; norm_num
  have hRad_inv : Rad⁻¹ * Rad = 1 := PowerSeries.inv_mul_cancel Rad hRad_ne
  have hD_Rad2 : 2 * Rad * D Rad = D R := by
    have h := congr_arg D radical_sq
    rw [sq, D.leibniz] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  have hRad_ode : 2 * R * D Rad = D R * Rad := by
    calc 2 * R * D Rad
      _ = (Rad⁻¹ * Rad) * (2 * R * D Rad) := by rw [hRad_inv, one_mul]
      _ = Rad⁻¹ * (Rad ^ 2) * (2 * Rad * D Rad) := by rw [radical_sq]; ring
      _ = Rad⁻¹ * (Rad ^ 2) * D R := by rw [hD_Rad2]
      _ = (Rad⁻¹ * Rad) * (D R * Rad) := by ring
      _ = D R * Rad := by rw [hRad_inv, one_mul]
  have hrel : X * Q * G + F * Rad = N := by
    have := gf_relation
    dsimp [Q, G, N, F, Rad]
    linear_combination this
  have hD_rel : (Q + X * D Q) * G + X * Q * D G + D F * Rad + F * D Rad = D N := by
    have h := congr_arg D hrel
    rw [map_add, D.leibniz, D.leibniz, D.leibniz, hDX] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  set K : S := 4 * R + (1 + X) * D R
  have hF_factor : (1 + X) * (2 * R * D F + F * D R) = K * F := by
    rw [hDF]
    dsimp [K, F, OMA.S_oeis_a125189.radicalFactor]
    ring
  have hmaster :
      2 * R * (1 + X) * ((Q + X * D Q) * G + X * Q * D G - D N) + K * (N - X * Q * G) = 0 := by
    linear_combination 2 * R * (1 + X) * hD_rel - (1 + X) * F * hRad_ode - Rad * hF_factor - K * hrel
  have hquarter : C (-1 / 4 : ℚ) * (-4 : S) = 1 := by
    have hm4 : (-4 : S) = C (-4 : ℚ) := by simp [map_ofNat]
    rw [hm4, ← map_mul]; norm_num
  have hpoly :
      (-4 : S) * (OMA.S_oeis_a125189.odeConstant + OMA.S_oeis_a125189.odeValue * G +
        OMA.S_oeis_a125189.odeDerivative * D G) =
      2 * R * (1 + X) * ((Q + X * D Q) * G + X * Q * D G - D N) + K * (N - X * Q * G) := by
    dsimp only [K]
    rw [hDR, hDN, hDQ]
    dsimp [R, N, Q, OMA.S_oeis_a125189.radicand, OMA.S_oeis_a125189.numeratorHead,
      OMA.S_oeis_a125189.denominatorFactor, OMA.S_oeis_a125189.odeConstant,
      OMA.S_oeis_a125189.odeValue, OMA.S_oeis_a125189.odeDerivative]
    simp only [map_ofNat, map_one]
    ring
  calc OMA.S_oeis_a125189.odeConstant + OMA.S_oeis_a125189.odeValue * G +
        OMA.S_oeis_a125189.odeDerivative * D G
    _ = C (-1 / 4 : ℚ) * ((-4 : S) * (OMA.S_oeis_a125189.odeConstant +
        OMA.S_oeis_a125189.odeValue * G + OMA.S_oeis_a125189.odeDerivative * D G)) := by
      rw [← mul_assoc, hquarter, one_mul]
    _ = C (-1 / 4 : ℚ) * 0 := by rw [hpoly, hmaster]
    _ = 0 := mul_zero _

lemma coeff_C_mul_X_pow_mul (c : ℚ) (k n : ℕ) (hk : k ≤ n) (f : S) :
    coeff n (C c * X ^ k * f) = c * coeff (n - k) f := by
  rw [mul_assoc, coeff_C_mul, ← Nat.sub_add_cancel hk, coeff_X_pow_mul, Nat.add_sub_cancel]

lemma coeff_C_mul_X_pow_eq_zero (c : ℚ) (k n : ℕ) (hk : k < n) :
    coeff n (C c * (X : S) ^ k) = 0 := by
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

lemma coeff_X_pow_deriv {c : ℚ} {k n : ℕ} (hkn : k ≤ n) (f : S) :
    coeff n (C c * X ^ k * PowerSeries.derivative ℚ f) =
      c * (((n : ℚ) - (k : ℚ) + 1) * coeff (n + 1 - k) f) := by
  rw [coeff_C_mul_X_pow_mul c k n hkn (PowerSeries.derivative ℚ f), PowerSeries.coeff_derivative]
  have hidx : n - k + 1 = n + 1 - k := by omega
  have hcast : ((n - k : ℕ) : ℚ) + 1 = (n : ℚ) - (k : ℚ) + 1 := by
    have : (n : ℚ) = ((n - k : ℕ) : ℚ) + (k : ℚ) := by exact_mod_cast (by omega : n = (n - k) + k)
    linarith
  rw [hidx, hcast]
  ring

lemma rec_proof (n : ℕ) (hn : 8 ≤ n) :
    ((n : ℚ) + 1) * OMA.S_oeis_a125189.a n - 3 * OMA.S_oeis_a125189.a (n - 1) +
      (-4 * (n : ℚ) + 5) * OMA.S_oeis_a125189.a (n - 2) +
      (-2 * (n : ℚ) + 7) * OMA.S_oeis_a125189.a (n - 3) + 3 * OMA.S_oeis_a125189.a (n - 4) +
      (4 * (n : ℚ) - 5) * OMA.S_oeis_a125189.a (n - 5) +
      (8 * (n : ℚ) - 49) * OMA.S_oeis_a125189.a (n - 6) +
      3 * (2 * (n : ℚ) - 13) * OMA.S_oeis_a125189.a (n - 7) +
      3 * ((n : ℚ) - 8) * OMA.S_oeis_a125189.a (n - 8) = 0 := by
  set G := OMA.S_oeis_a125189.gf
  set D := PowerSeries.derivative ℚ
  have hc0 := congr_arg (coeff n) ode_proof
  simp only [map_zero, map_add] at hc0
  have hC0 : coeff n OMA.S_oeis_a125189.odeConstant = 0 := by
    unfold OMA.S_oeis_a125189.odeConstant
    simp only [map_add, map_sub]
    rw [coeff_C_mul_X_pow_eq_zero 3 7 n (by omega),
      coeff_C_mul_X_pow_eq_zero 1 6 n (by omega),
      coeff_C_mul_X_pow_eq_zero 3 5 n (by omega),
      coeff_C_mul_X_pow_eq_zero 5 4 n (by omega),
      coeff_C_mul_X_pow_eq_zero 1 3 n (by omega),
      coeff_C_mul_X_pow_eq_zero 3 2 n (by omega),
      coeff_C_mul_X_pow_eq_zero 1 1 n (by omega),
      coeff_C_mul_X_pow_eq_zero 1 0 n (by omega)]
    norm_num
  have hV : coeff n (OMA.S_oeis_a125189.odeValue * G) =
      3 * coeff (n - 7) G - 1 * coeff (n - 6) G + 15 * coeff (n - 5) G +
      3 * coeff (n - 4) G + 1 * coeff (n - 3) G - 3 * coeff (n - 2) G -
      3 * coeff (n - 1) G + 1 * coeff n G := by
    unfold OMA.S_oeis_a125189.odeValue
    simp only [add_mul, sub_mul, map_add, map_sub]
    rw [coeff_C_mul_X_pow_mul 3 7 n (by omega) G,
      coeff_C_mul_X_pow_mul 1 6 n (by omega) G,
      coeff_C_mul_X_pow_mul 15 5 n (by omega) G,
      coeff_C_mul_X_pow_mul 3 4 n (by omega) G,
      coeff_C_mul_X_pow_mul 1 3 n (by omega) G,
      coeff_C_mul_X_pow_mul 3 2 n (by omega) G,
      coeff_C_mul_X_pow_mul 3 1 n (by omega) G,
      coeff_C_mul_X_pow_mul 1 0 n (by omega) G]
    simp only [Nat.sub_zero]
  have hX9 : coeff n (C 3 * X ^ 9 * D G) = 3 * ((n : ℚ) - 8) * coeff (n - 8) G := by
    by_cases hn8 : n = 8
    · subst hn8
      rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg (by omega), mul_zero]
      norm_num
    · have hn9 : 9 ≤ n := by omega
      rw [coeff_X_pow_deriv (c := 3) hn9 G]
      have hidx : n + 1 - 9 = n - 8 := by omega
      rw [hidx]
      ring
  have hD : coeff n (OMA.S_oeis_a125189.odeDerivative * D G) =
      3 * ((n : ℚ) - 8) * coeff (n - 8) G +
      6 * ((n : ℚ) - 8 + 1) * coeff (n - 7) G +
      8 * ((n : ℚ) - 7 + 1) * coeff (n - 6) G +
      4 * ((n : ℚ) - 6 + 1) * coeff (n - 5) G -
      2 * ((n : ℚ) - 4 + 1) * coeff (n - 3) G -
      4 * ((n : ℚ) - 3 + 1) * coeff (n - 2) G +
      1 * ((n : ℚ) - 1 + 1) * coeff n G := by
    unfold OMA.S_oeis_a125189.odeDerivative
    simp only [add_mul, sub_mul, map_add, map_sub]
    rw [hX9,
      coeff_X_pow_deriv (c := 6) (by omega) G,
      coeff_X_pow_deriv (c := 8) (by omega) G,
      coeff_X_pow_deriv (c := 4) (by omega) G,
      coeff_X_pow_deriv (c := 2) (by omega) G,
      coeff_X_pow_deriv (c := 4) (by omega) G,
      coeff_X_pow_deriv (c := 1) (by omega) G]
    have i8 : n + 1 - 8 = n - 7 := by omega
    have i7 : n + 1 - 7 = n - 6 := by omega
    have i6 : n + 1 - 6 = n - 5 := by omega
    have i4 : n + 1 - 4 = n - 3 := by omega
    have i3 : n + 1 - 3 = n - 2 := by omega
    have i1 : n + 1 - 1 = n := by omega
    rw [i8, i7, i6, i4, i3, i1]
    simp only [Nat.cast_ofNat, Nat.cast_one]
    ring
  rw [hC0, hV, hD] at hc0
  unfold OMA.S_oeis_a125189.a
  linarith

end ProofA125189

theorem OMA.solution : type_of% @OMA.S_oeis_a125189.main :=
  ⟨ProofA125189.ode_proof, ProofA125189.rec_proof⟩
