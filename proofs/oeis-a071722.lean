import OMAStatements.S_oeis_a071722

open OMA.S_oeis_a071722
open PowerSeries

private abbrev PS := PowerSeries ℚ
private noncomputable abbrev 𝓧 : PS := PowerSeries.X
private noncomputable abbrev D := PowerSeries.derivative ℚ

private theorem derivative_ofNat (k : ℕ) [k.AtLeastTwo] :
    D (ofNat(k) : PS) = 0 :=
  D.map_natCast k

private theorem coeff_ofNat_mul (n k : ℕ) [k.AtLeastTwo] (f : PS) :
    coeff n ((ofNat(k) : PS) * f) = ofNat(k) * coeff n f := by
  rw [← map_ofNat (PowerSeries.C : ℚ →+* PS), coeff_C_mul]

private theorem series_ofNat_ne_zero (k : ℕ) [k.AtLeastTwo] (hk : (ofNat(k) : ℚ) ≠ 0) :
    (ofNat(k) : PS) ≠ 0 := by
  intro h
  have hz := congrArg (constantCoeff (R := ℚ)) h
  rw [map_ofNat, map_zero] at hz
  exact hk hz

theorem OMA.solution : type_of% @OMA.S_oeis_a071722.main := by
  let c : PS := PowerSeries.map (Int.castRingHom ℚ) catGF
  let A : PS := (1 + 𝓧 ^ 2 * c ^ 2) * c ^ 3
  have hcoeff (n : ℕ) : coeff n A = (a n : ℚ) := by
    change coeff n A = (Int.castRingHom ℚ) (a n)
    rw [a, ← coeff_map]
    simp only [A, c, map_mul, map_add, map_one, map_pow, map_X]
  have hc (n : ℕ) : coeff n c = (catalan n : ℚ) := by
    simp [c, catGF]
  have hcat : c = 1 + 𝓧 * c ^ 2 := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
        simp only [hc, map_add, coeff_zero_one, coeff_zero_X_mul, add_zero,
          catalan_zero, Nat.cast_one]
    | succ n =>
        rw [map_add, coeff_one, if_neg (Nat.succ_ne_zero n), zero_add,
          coeff_succ_X_mul, pow_two, coeff_mul]
        simp_rw [hc]
        exact_mod_cast catalan_succ' n

  let S : PS := 1 - 2 * 𝓧 * c
  have hSsq : S ^ 2 = 1 - 4 * 𝓧 := by
    dsimp only [S]
    linear_combination (-4 * 𝓧) * hcat
  have hS_ne : S ≠ 0 := by
    intro h
    have hzero := congrArg (constantCoeff (R := ℚ)) h
    simp [S] at hzero
  have hSderiv : (1 - 4 * 𝓧) * D S = -2 * S := by
    have hd := congrArg (fun f : PS => D f) hSsq
    change D (S ^ 2) = D (1 - 4 * 𝓧) at hd
    simp only [derivative_pow, map_sub, Derivation.leibniz, Derivation.map_one_eq_zero,
      derivative_ofNat, derivative_X, smul_eq_mul] at hd
    apply mul_left_cancel₀ (a := 2 * S) (mul_ne_zero (series_ofNat_ne_zero 2 (by norm_num)) hS_ne)
    calc
      (2 * S) * ((1 - 4 * 𝓧) * D S) = S ^ 2 * (2 * S * D S) := by
        rw [hSsq]
        ring
      _ = (2 * S) * (-2 * S) := by linear_combination S ^ 2 * hd

  -- After clearing X³, the expression for A reduces to a linear polynomial in S.
  let P : PS := 8 - 32 * 𝓧 + 20 * 𝓧 ^ 2
  let q : PS := 2 - 4 * 𝓧 + 𝓧 ^ 2
  let B : PS := 8 * 𝓧 ^ 3 * A
  have hB : B = P - 4 * q * S := by
    have hdouble : 2 * 𝓧 * c = 1 - S := by dsimp only [S]; ring
    apply mul_left_cancel₀ (series_ofNat_ne_zero 4 (by norm_num))
    calc
      4 * B = (4 + (2 * 𝓧 * c) ^ 2) * (2 * 𝓧 * c) ^ 3 := by
        dsimp only [B, A]
        ring
      _ = (4 + (1 - S) ^ 2) * (1 - S) ^ 3 := by rw [hdouble]
      _ = 4 * (P - 4 * q * S) := by
        dsimp only [P, q]
        linear_combination
          (-S ^ 3 + 5 * S ^ 2 + (4 * 𝓧 - 15) * S + 27 - 20 * 𝓧) * hSsq

  have hPderiv : D P = -32 + 40 * 𝓧 := by
    dsimp only [P]
    simp only [map_add, map_sub, Derivation.leibniz, derivative_ofNat, derivative_X,
      derivative_pow, smul_eq_mul]
    ring
  have hqderiv : D q = -4 + 2 * 𝓧 := by
    dsimp only [q]
    simp only [map_add, map_sub, Derivation.leibniz, derivative_ofNat, derivative_X,
      derivative_pow, smul_eq_mul]
    ring
  have hBderiv : D B = 8 * 𝓧 ^ 3 * D A + 24 * 𝓧 ^ 2 * A := by
    dsimp only [B]
    simp only [Derivation.leibniz, derivative_ofNat, derivative_pow, derivative_X,
      smul_eq_mul]
    ring

  -- Differentiate B and eliminate S using its differential equation.
  let R : PS := (1 - 4 * 𝓧) * (-4 + 2 * 𝓧) - 2 * q
  have hDright : D B = -32 + 40 * 𝓧 - (4 * q * D S + 4 * (-4 + 2 * 𝓧) * S) := by
    rw [hB]
    simp only [map_sub, Derivation.leibniz, smul_eq_mul, derivative_ofNat, hPderiv,
      hqderiv]
    ring
  have helim : (1 - 4 * 𝓧) * q * D B - R * B =
      (1 - 4 * 𝓧) * q * (-32 + 40 * 𝓧) - R * P := by
    rw [hDright, hB]
    dsimp only [R]
    linear_combination (-4 * q ^ 2) * hSderiv
  let E : PS := 𝓧 * D A
  have hODE : (1 - 4 * 𝓧) * q * E + (3 * (1 - 4 * 𝓧) * q - 𝓧 * R) * A =
      6 - 4 * 𝓧 + 5 * 𝓧 ^ 2 := by
    apply mul_left_cancel₀ (a := 8 * 𝓧 ^ 2)
      (mul_ne_zero (series_ofNat_ne_zero 8 (by norm_num)) (pow_ne_zero _ X_ne_zero))
    calc
      _ = (1 - 4 * 𝓧) * q * D B - R * B := by rw [hBderiv]; dsimp only [B, E]; ring
      _ = (1 - 4 * 𝓧) * q * (-32 + 40 * 𝓧) - R * P := helim
      _ = _ := by dsimp only [P, q, R]; ring
  have hexpand : 2 * E - 12 * (𝓧 ^ 1 * E) + 17 * (𝓧 ^ 2 * E) - 4 * (𝓧 ^ 3 * E) +
      (6 * A - 28 * (𝓧 ^ 1 * A) + 25 * (𝓧 ^ 2 * A) - 2 * (𝓧 ^ 3 * A)) =
      6 - 4 * (1 * 𝓧 ^ 1) + 5 * (1 * 𝓧 ^ 2) := by
    dsimp only [q, R] at hODE
    linear_combination hODE
  have hE (m : ℕ) : coeff m E = coeff m A * (m : ℚ) := by
    dsimp only [E]
    cases m with
    | zero => simp [coeff_zero_X_mul]
    | succ m => rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]
  intro n hn
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  have hconstant : coeff n (6 : PS) = 0 := by
    rw [← map_ofNat (PowerSeries.C : ℚ →+* PS), coeff_C_of_ne_zero hn0]
  have hrec := congrArg (fun f : PS => coeff n f) hexpand
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_X_pow_mul', if_pos h1, if_pos h2,
    if_pos hn, one_mul, coeff_X_pow, if_neg hn1, if_neg hn2, hconstant, mul_zero, sub_zero,
    add_zero, hE, hcoeff, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub hn, Nat.cast_one,
    Nat.cast_ofNat] at hrec
  have hrat : 2 * ((n : ℚ) + 3) * (a n : ℚ) + 4 * (-3 * (n : ℚ) - 4) * (a (n - 1) : ℚ) +
      (17 * (n : ℚ) - 9) * (a (n - 2) : ℚ) + 2 * (-2 * (n : ℚ) + 5) * (a (n - 3) : ℚ) = 0 := by
    linear_combination hrec
  exact_mod_cast hrat
