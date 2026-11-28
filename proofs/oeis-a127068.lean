import OMAStatements.S_oeis_a127068

namespace OMA.P_oeis_a127068

open OMA.S_oeis_a127068

/-! ### Part 1: Formal power series helpers (`PowerSeries ℚ`) -/

private lemma coeff_mul_eq_sum_range (f g : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (f * g) =
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * PowerSeries.coeff (n - i) g := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g) n

private lemma coeff_X_mul_zero (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (PowerSeries.X * f) = 0 := by
  rw [coeff_mul_eq_sum_range]; simp

private lemma coeff_X_mul_succ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.X * f) = PowerSeries.coeff n f := by
  rw [coeff_mul_eq_sum_range, Finset.sum_eq_single 1]
  · simp
  · intro b _ hb
    rw [PowerSeries.coeff_X, if_neg hb, zero_mul]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

private noncomputable def invOneSubAux (f : PowerSeries ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * invOneSubAux f (n - i)

private noncomputable def invOneSub (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (invOneSubAux f)

private noncomputable def invUnit1 (f : PowerSeries ℚ) : PowerSeries ℚ :=
  invOneSub (PowerSeries.mk (fun n => -PowerSeries.coeff (n + 1) f))

private lemma coeff_invOneSub (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (invOneSub f) = invOneSubAux f n := by
  unfold invOneSub; simp

private lemma one_sub_X_mul_invOneSub (f : PowerSeries ℚ) :
    (1 - PowerSeries.X * f) * invOneSub f = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub]
  cases n with
  | zero =>
    rw [mul_assoc, coeff_X_mul_zero, PowerSeries.coeff_one, if_pos rfl, coeff_invOneSub]
    simp [invOneSubAux]
  | succ m =>
    rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), coeff_invOneSub, invOneSubAux]
    rw [mul_assoc, coeff_X_mul_succ, coeff_mul_eq_sum_range]
    have hsum : ∑ i ∈ Finset.range (m + 1),
          PowerSeries.coeff i f * PowerSeries.coeff (m - i) (invOneSub f) =
        ∑ i ∈ Finset.range (m + 1),
          PowerSeries.coeff i f * invOneSubAux f (m - i) :=
      Finset.sum_congr rfl (fun i _ => by rw [coeff_invOneSub])
    rw [hsum, sub_self]

private lemma mul_invUnit1 (f : PowerSeries ℚ) (hc0 : PowerSeries.coeff 0 f = 1) :
    f * invUnit1 f = 1 := by
  have h1 : 1 - PowerSeries.X * PowerSeries.mk (fun n => -PowerSeries.coeff (n + 1) f) = f := by
    ext n
    rw [map_sub]
    cases n with
    | zero => rw [PowerSeries.coeff_one, if_pos rfl, coeff_X_mul_zero, sub_zero, hc0]
    | succ m =>
      rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), coeff_X_mul_succ,
        PowerSeries.coeff_mk, zero_sub, neg_neg]
  unfold invUnit1
  conv_lhs => arg 1; rw [← h1]
  exact one_sub_X_mul_invOneSub _

private lemma coeff_zero_invUnit1 (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (invUnit1 f) = 1 := by
  unfold invUnit1; rw [coeff_invOneSub]; simp [invOneSubAux]

private noncomputable def derivPS (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) f)

private lemma derivPS_zero : derivPS 0 = 0 := by
  ext n; simp [derivPS]

private lemma derivPS_one : derivPS 1 = 0 := by
  ext n; simp [derivPS, PowerSeries.coeff_one]

private lemma derivPS_X : derivPS PowerSeries.X = 1 := by
  ext n
  cases n with
  | zero => simp [derivPS, PowerSeries.coeff_X, PowerSeries.coeff_one]
  | succ m => simp [derivPS, PowerSeries.coeff_X, PowerSeries.coeff_one]

private lemma derivPS_add (f g : PowerSeries ℚ) :
    derivPS (f + g) = derivPS f + derivPS g := by
  ext n; simp [derivPS]; ring

private lemma derivPS_sub (f g : PowerSeries ℚ) :
    derivPS (f - g) = derivPS f - derivPS g := by
  ext n; simp [derivPS]; ring

private lemma derivPS_neg (f : PowerSeries ℚ) :
    derivPS (-f) = -derivPS f := by
  ext n; simp [derivPS]

private lemma derivPS_C_mul (a : ℚ) (f : PowerSeries ℚ) :
    derivPS (PowerSeries.C a * f) = PowerSeries.C a * derivPS f := by
  ext n; simp [derivPS]; ring

private lemma derivPS_mul (f g : PowerSeries ℚ) :
    derivPS (f * g) = derivPS f * g + f * derivPS g := by
  ext n
  simp only [derivPS, PowerSeries.coeff_mk, map_add]
  rw [coeff_mul_eq_sum_range, coeff_mul_eq_sum_range, coeff_mul_eq_sum_range]
  simp only [PowerSeries.coeff_mk]
  have hsum : ((n + 1 : ℕ) : ℚ) *
        ∑ i ∈ Finset.range (n + 2), PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g =
      (∑ i ∈ Finset.range (n + 2),
        ((i : ℚ) * PowerSeries.coeff i f) * PowerSeries.coeff (n + 1 - i) g) +
      (∑ i ∈ Finset.range (n + 2),
        PowerSeries.coeff i f * (((n + 1 - i : ℕ) : ℚ) * PowerSeries.coeff (n + 1 - i) g)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hile : i ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hadd : (i : ℚ) + ((n + 1 - i : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) := by
      exact_mod_cast (by omega : i + (n + 1 - i) = n + 1)
    linear_combination -(PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g) * hadd
  rw [hsum]
  congr 1
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show n + 1 - (i + 1) = n - i by omega]
  · rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show n + 1 - i = (n - i) + 1 by omega]

private lemma derivPS_pow (f : PowerSeries ℚ) (k : ℕ) :
    derivPS (f ^ k) = PowerSeries.C (k : ℚ) * f ^ (k - 1) * derivPS f := by
  induction k with
  | zero => simp [derivPS_one]
  | succ k ih =>
    cases k with
    | zero => simp
    | succ k' =>
      rw [pow_succ, derivPS_mul, ih]
      simp only [Nat.add_sub_cancel]
      have hpow : f ^ k' * f = f ^ (k' + 1) := (pow_succ f k').symm
      have hcast : PowerSeries.C ((k' + 2 : ℕ) : ℚ) =
          PowerSeries.C ((k' + 1 : ℕ) : ℚ) + 1 := by
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add, map_one, map_ofNat]; ring
      rw [hcast]
      linear_combination PowerSeries.C ((k' + 1 : ℕ) : ℚ) * derivPS f * hpow

private lemma eq_of_derivPS_eq (f g : PowerSeries ℚ)
    (hc0 : PowerSeries.coeff 0 f = PowerSeries.coeff 0 g)
    (hd : derivPS f = derivPS g) : f = g := by
  ext n
  cases n with
  | zero => exact hc0
  | succ m =>
    have h := congr_arg (PowerSeries.coeff m) hd
    simp only [derivPS, PowerSeries.coeff_mk] at h
    have hne : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hne h

private lemma derivPS_inv_of_mul_eq_one (f g : PowerSeries ℚ) (h : f * g = 1) :
    derivPS g = -(derivPS f) * g ^ 2 := by
  have hd : derivPS f * g + f * derivPS g = 0 := by
    rw [← derivPS_mul, h, derivPS_one]
  calc
    derivPS g = 1 * derivPS g := (one_mul _).symm
    _ = (f * g) * derivPS g := by rw [h]
    _ = g * (f * derivPS g) := by ring
    _ = g * (-(derivPS f * g)) := by
          have : f * derivPS g = -(derivPS f * g) := eq_neg_of_add_eq_zero_right hd
          rw [this]
    _ = -(derivPS f) * g ^ 2 := by ring

/-! ### Part 2: Even substitution `substX2 f(X) = f(X^2)` -/

private noncomputable def substX2 (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n % 2 = 0 then PowerSeries.coeff (n / 2) f else 0)

private lemma coeff_substX2_even (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (2 * n) (substX2 f) = PowerSeries.coeff n f := by
  unfold substX2
  rw [PowerSeries.coeff_mk, if_pos (by omega), show (2 * n) / 2 = n by omega]

private lemma coeff_substX2_odd (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) (substX2 f) = 0 := by
  unfold substX2
  rw [PowerSeries.coeff_mk, if_neg (by omega)]

private lemma substX2_one : substX2 1 = 1 := by
  ext n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [coeff_substX2_even, PowerSeries.coeff_one, PowerSeries.coeff_one]
    by_cases hk : k = 0 <;> simp [hk]
  · rw [coeff_substX2_odd, PowerSeries.coeff_one, if_neg (by omega)]

private lemma substX2_X : substX2 PowerSeries.X = PowerSeries.X ^ 2 := by
  ext n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [coeff_substX2_even, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    by_cases hk : k = 1
    · subst hk; simp
    · simp [hk, show 2 * k ≠ 2 by omega]
  · rw [coeff_substX2_odd, PowerSeries.coeff_X_pow, if_neg (by omega)]

private lemma substX2_add (f g : PowerSeries ℚ) :
    substX2 (f + g) = substX2 f + substX2 g := by
  ext n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · simp [coeff_substX2_even]
  · simp [coeff_substX2_odd]

private lemma substX2_C_mul (a : ℚ) (f : PowerSeries ℚ) :
    substX2 (PowerSeries.C a * f) = PowerSeries.C a * substX2 f := by
  ext n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · simp [coeff_substX2_even]
  · simp [coeff_substX2_odd]

private lemma substX2_mul (f g : PowerSeries ℚ) :
    substX2 (f * g) = substX2 f * substX2 g := by
  ext n
  rw [coeff_mul_eq_sum_range]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [coeff_substX2_even, coeff_mul_eq_sum_range]
    have hfilt : ∑ i ∈ Finset.range (2 * k + 1),
          PowerSeries.coeff i (substX2 f) * PowerSeries.coeff (2 * k - i) (substX2 g) =
        ∑ i ∈ (Finset.range (2 * k + 1)).filter (fun i => i % 2 = 0),
          PowerSeries.coeff i (substX2 f) * PowerSeries.coeff (2 * k - i) (substX2 g) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : i % 2 = 0
      · rw [if_pos hi]
      · rw [if_neg hi]
        have hodd : i = 2 * (i / 2) + 1 := by omega
        rw [hodd, coeff_substX2_odd, zero_mul]
    rw [hfilt]
    refine Finset.sum_nbij (fun j => 2 * j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega
    · intro j1 _ j2 _ h; dsimp only at h; omega
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      refine ⟨i / 2, by simp only [Finset.mem_coe, Finset.mem_range]; omega, ?_⟩
      dsimp only; omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have hsub : 2 * k - 2 * j = 2 * (k - j) := by omega
      rw [coeff_substX2_even, hsub, coeff_substX2_even]
  · rw [coeff_substX2_odd]
    symm
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hile : i ≤ 2 * k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hev : i % 2 = 0
    · have hodd : 2 * k + 1 - i = 2 * ((2 * k + 1 - i) / 2) + 1 := by omega
      rw [hodd, coeff_substX2_odd, mul_zero]
    · have hodd : i = 2 * (i / 2) + 1 := by omega
      rw [hodd, coeff_substX2_odd, zero_mul]

private lemma substX2_pow (f : PowerSeries ℚ) (m : ℕ) :
    substX2 (f ^ m) = (substX2 f) ^ m := by
  induction m with
  | zero => simp [substX2_one]
  | succ m ih => rw [pow_succ, pow_succ, substX2_mul, ih]

private lemma derivPS_substX2 (f : PowerSeries ℚ) :
    derivPS (substX2 f) = PowerSeries.C 2 * PowerSeries.X * substX2 (derivPS f) := by
  ext n
  simp only [derivPS, PowerSeries.coeff_mk]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [coeff_substX2_odd, mul_zero, mul_assoc, PowerSeries.coeff_C_mul]
    cases k with
    | zero => rw [coeff_X_mul_zero, mul_zero]
    | succ k' =>
      rw [show 2 * (k' + 1) = (2 * k' + 1) + 1 by omega, coeff_X_mul_succ,
        coeff_substX2_odd, mul_zero]
  · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, coeff_substX2_even,
      mul_assoc, PowerSeries.coeff_C_mul, coeff_X_mul_succ, coeff_substX2_even,
      PowerSeries.coeff_mk]
    push_cast; ring

/-! ### Part 3: `(1 + 2u)^(-1/2)` and `S = sqrt(1 + 2*X^2)` -/

private noncomputable def invSqrt1p2u : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (-1 : ℚ) ^ n * (Nat.choose (2 * n) n : ℚ) / (2 : ℚ) ^ n)

private lemma coeff_zero_invSqrt1p2u : PowerSeries.coeff 0 invSqrt1p2u = 1 := by
  simp [invSqrt1p2u]

private lemma choose_two_succ (n : ℕ) :
    (n + 1) * Nat.choose (2 * (n + 1)) (n + 1) = 2 * (2 * n + 1) * Nat.choose (2 * n) n := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 2 * (n + 1) by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * (n + 1) - (n + 1) = n + 1 by omega] at h1
  rw [show 2 * n - n = n by omega] at h2
  have hfac1 : (2 * (n + 1)).factorial = (2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
  have hfac2 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
  have hpos : 0 < (n + 1).factorial * n.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    (n + 1) * Nat.choose (2 * (n + 1)) (n + 1) * ((n + 1).factorial * n.factorial)
      = Nat.choose (2 * (n + 1)) (n + 1) * (n + 1).factorial * (n + 1).factorial := by
          rw [hfac2]; ring
    _ = (2 * (n + 1)).factorial := h1
    _ = (2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) := hfac1
    _ = (2 * n + 2) * ((2 * n + 1) * (Nat.choose (2 * n) n * n.factorial * n.factorial)) := by
          rw [← h2]
    _ = 2 * (2 * n + 1) * Nat.choose (2 * n) n * ((n + 1).factorial * n.factorial) := by
          rw [hfac2]; ring

private lemma ode_invSqrt1p2u :
    (1 + PowerSeries.C 2 * PowerSeries.X) * derivPS invSqrt1p2u + invSqrt1p2u = 0 := by
  ext n
  rw [add_mul, one_mul, map_add, map_add, map_zero, mul_assoc, PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
    rw [coeff_X_mul_zero, mul_zero, add_zero]
    simp [derivPS, invSqrt1p2u]
  | succ m =>
    rw [coeff_X_mul_succ]
    simp only [derivPS, invSqrt1p2u, PowerSeries.coeff_mk]
    have hch : ((m + 2 : ℕ) : ℚ) * (Nat.choose (2 * (m + 2)) (m + 2) : ℚ) =
        2 * (2 * ((m + 1 : ℕ) : ℚ) + 1) * (Nat.choose (2 * (m + 1)) (m + 1) : ℚ) := by
      exact_mod_cast choose_two_succ (m + 1)
    have hpow : (2 : ℚ) ^ (m + 2) = 2 * (2 : ℚ) ^ (m + 1) := by rw [pow_succ']
    have hneg : (-1 : ℚ) ^ (m + 2) = -((-1 : ℚ) ^ (m + 1)) := by rw [pow_succ]; ring
    have hne : (2 : ℚ) ^ (m + 1) ≠ 0 := by positivity
    rw [hpow, hneg]
    field_simp [hne]
    push_cast at hch ⊢
    linear_combination -((-1 : ℚ) ^ (m + 1)) * hch

private lemma sq_invSqrt1p2u :
    (1 + PowerSeries.C 2 * PowerSeries.X) * invSqrt1p2u ^ 2 = 1 := by
  apply eq_of_derivPS_eq
  · rw [add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul, coeff_X_mul_zero,
      mul_zero, add_zero, PowerSeries.coeff_one, if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff,
      map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_invSqrt1p2u, one_pow]
  · rw [derivPS_mul, derivPS_add, derivPS_one, derivPS_C_mul, derivPS_X, derivPS_pow]
    rw [show (2 : ℕ) - 1 = 1 by rfl, pow_one]
    simp only [zero_add, mul_one, Nat.cast_ofNat]
    have hode := ode_invSqrt1p2u
    linear_combination PowerSeries.C 2 * invSqrt1p2u * hode

/-! ### Part 4: Exact EGF `F m = W^m * R` and recurrence for `dSeq m k` -/

private noncomputable def rSeries : PowerSeries ℚ := substX2 invSqrt1p2u

private noncomputable def sSeries : PowerSeries ℚ := (1 + PowerSeries.C 2 * PowerSeries.X ^ 2) * rSeries

private noncomputable def q1u : PowerSeries ℚ := invUnit1 (1 + PowerSeries.X)

private noncomputable def q1Series : PowerSeries ℚ := substX2 q1u

private noncomputable def wSeries : PowerSeries ℚ := (PowerSeries.X + sSeries) * q1Series

private noncomputable def fSeries (m : ℕ) : PowerSeries ℚ := wSeries ^ m * rSeries

private lemma mul_q1u : (1 + PowerSeries.X) * q1u = 1 := by
  apply mul_invUnit1
  rw [map_add, PowerSeries.coeff_one, if_pos rfl, PowerSeries.coeff_X, if_neg (by decide : 0 ≠ 1),
    add_zero]

private lemma derivPS_q1u : derivPS q1u = -(q1u ^ 2) := by
  have h := derivPS_inv_of_mul_eq_one (1 + PowerSeries.X) q1u mul_q1u
  rw [derivPS_add, derivPS_one, derivPS_X, zero_add] at h
  simpa using h

private lemma mul_q1Series : (1 + PowerSeries.X ^ 2) * q1Series = 1 := by
  have h := congr_arg substX2 mul_q1u
  rw [substX2_mul, substX2_add, substX2_one, substX2_X] at h
  exact h

private lemma sq_rSeries : (1 + PowerSeries.C 2 * PowerSeries.X ^ 2) * rSeries ^ 2 = 1 := by
  have h := congr_arg substX2 sq_invSqrt1p2u
  rw [substX2_mul, substX2_add, substX2_one, substX2_C_mul, substX2_X, substX2_pow] at h
  exact h

private lemma sSeries_mul_rSeries : sSeries * rSeries = 1 := by
  unfold sSeries
  calc
    (1 + PowerSeries.C 2 * PowerSeries.X ^ 2) * rSeries * rSeries
      = (1 + PowerSeries.C 2 * PowerSeries.X ^ 2) * rSeries ^ 2 := by ring
    _ = 1 := sq_rSeries

private lemma sSeries_sq : sSeries ^ 2 = 1 + PowerSeries.C 2 * PowerSeries.X ^ 2 := by
  unfold sSeries
  calc
    ((1 + PowerSeries.C 2 * PowerSeries.X ^ 2) * rSeries) ^ 2
      = (1 + PowerSeries.C 2 * PowerSeries.X ^ 2) *
          ((1 + PowerSeries.C 2 * PowerSeries.X ^ 2) * rSeries ^ 2) := by ring
    _ = (1 + PowerSeries.C 2 * PowerSeries.X ^ 2) * 1 := by rw [sq_rSeries]
    _ = 1 + PowerSeries.C 2 * PowerSeries.X ^ 2 := mul_one _

private lemma derivPS_rSeries :
    (1 + PowerSeries.C 2 * PowerSeries.X ^ 2) * derivPS rSeries =
      -PowerSeries.C 2 * PowerSeries.X * rSeries := by
  unfold rSeries
  rw [derivPS_substX2]
  have h := congr_arg substX2 ode_invSqrt1p2u
  rw [substX2_add, substX2_mul, substX2_add, substX2_one, substX2_C_mul, substX2_X] at h
  have hz : substX2 0 = 0 := by
    ext n; rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · simp [coeff_substX2_even]
    · simp [coeff_substX2_odd]
  rw [hz] at h
  linear_combination PowerSeries.C 2 * PowerSeries.X * h

private lemma derivPS_sSeries : derivPS sSeries = PowerSeries.C 2 * PowerSeries.X * rSeries := by
  unfold sSeries
  rw [derivPS_mul, derivPS_add, derivPS_one, derivPS_C_mul, derivPS_pow, derivPS_X]
  rw [show (2 : ℕ) - 1 = 1 by rfl, pow_one]
  simp only [zero_add, Nat.cast_ofNat, mul_one, map_ofNat]
  have hr := derivPS_rSeries
  simp only [map_ofNat] at hr
  linear_combination hr

private lemma derivPS_q1Series : derivPS q1Series = -PowerSeries.C 2 * PowerSeries.X * q1Series ^ 2 := by
  have h := derivPS_inv_of_mul_eq_one (1 + PowerSeries.X ^ 2) q1Series mul_q1Series
  rw [derivPS_add, derivPS_one, derivPS_pow, derivPS_X, show (2 : ℕ) - 1 = 1 by rfl, pow_one] at h
  simp only [zero_add, Nat.cast_ofNat, mul_one] at h
  linear_combination h

private lemma one_add_X_mul_wSeries : 1 + PowerSeries.X * wSeries = sSeries * wSeries := by
  unfold wSeries
  have hsq := sSeries_sq
  have hq := mul_q1Series
  calc
    1 + PowerSeries.X * ((PowerSeries.X + sSeries) * q1Series)
      = ((1 + PowerSeries.X ^ 2) * q1Series) + PowerSeries.X * ((PowerSeries.X + sSeries) * q1Series) := by
          rw [hq]
    _ = ((1 + PowerSeries.C 2 * PowerSeries.X ^ 2) + PowerSeries.X * sSeries) * q1Series := by
          have hc2 : PowerSeries.C (2 : ℚ) = 1 + 1 := by rw [← map_one PowerSeries.C, ← map_add]; norm_num
          rw [hc2]; ring
    _ = (sSeries ^ 2 + PowerSeries.X * sSeries) * q1Series := by rw [← hsq]
    _ = sSeries * ((PowerSeries.X + sSeries) * q1Series) := by ring

private lemma fSeries_add_X_succ (m : ℕ) :
    fSeries m + PowerSeries.X * fSeries (m + 1) = wSeries ^ (m + 1) := by
  unfold fSeries
  have h1 := one_add_X_mul_wSeries
  have hsr := sSeries_mul_rSeries
  calc
    wSeries ^ m * rSeries + PowerSeries.X * (wSeries ^ (m + 1) * rSeries)
      = wSeries ^ m * (1 + PowerSeries.X * wSeries) * rSeries := by rw [pow_succ]; ring
    _ = wSeries ^ m * (sSeries * wSeries) * rSeries := by rw [h1]
    _ = wSeries ^ (m + 1) * (sSeries * rSeries) := by rw [pow_succ]; ring
    _ = wSeries ^ (m + 1) * 1 := by rw [hsr]
    _ = wSeries ^ (m + 1) := mul_one _

private lemma derivPS_wSeries :
    derivPS wSeries = wSeries * (1 - PowerSeries.X * wSeries) * rSeries := by
  unfold wSeries
  rw [derivPS_mul, derivPS_add, derivPS_X, derivPS_sSeries, derivPS_q1Series]
  have hq := mul_q1Series
  have hsr := sSeries_mul_rSeries
  have hsq := sSeries_sq
  have hc2 : PowerSeries.C (2 : ℚ) = 1 + 1 := by rw [← map_one PowerSeries.C, ← map_add]; norm_num
  have h1 : (1 + PowerSeries.C 2 * PowerSeries.X * rSeries) * q1Series =
      ((1 + PowerSeries.X ^ 2) * sSeries + PowerSeries.C 2 * PowerSeries.X * (1 + PowerSeries.X ^ 2)) *
        q1Series ^ 2 * rSeries := by
    calc
      (1 + PowerSeries.C 2 * PowerSeries.X * rSeries) * q1Series
        = (1 + PowerSeries.C 2 * PowerSeries.X * rSeries) * q1Series *
            ((1 + PowerSeries.X ^ 2) * q1Series) := by rw [hq, mul_one]
      _ = (1 * (sSeries * rSeries) + PowerSeries.C 2 * PowerSeries.X * rSeries) *
            (1 + PowerSeries.X ^ 2) * q1Series ^ 2 := by rw [hsr]; ring
      _ = ((1 + PowerSeries.X ^ 2) * sSeries + PowerSeries.C 2 * PowerSeries.X * (1 + PowerSeries.X ^ 2)) *
            q1Series ^ 2 * rSeries := by ring
  have h2 : (PowerSeries.X + sSeries) * (-PowerSeries.C 2 * PowerSeries.X * q1Series ^ 2) =
      (-PowerSeries.C 2 * PowerSeries.X * (PowerSeries.X + sSeries) * sSeries) * q1Series ^ 2 * rSeries := by
    calc
      (PowerSeries.X + sSeries) * (-PowerSeries.C 2 * PowerSeries.X * q1Series ^ 2)
        = (PowerSeries.X + sSeries) * (-PowerSeries.C 2 * PowerSeries.X * q1Series ^ 2) *
            (sSeries * rSeries) := by rw [hsr, mul_one]
      _ = (-PowerSeries.C 2 * PowerSeries.X * (PowerSeries.X + sSeries) * sSeries) * q1Series ^ 2 * rSeries := by
            ring
  have h3 : (PowerSeries.X + sSeries) * q1Series * (1 - PowerSeries.X * ((PowerSeries.X + sSeries) * q1Series)) * rSeries =
      ((PowerSeries.X + sSeries) * ((1 + PowerSeries.X ^ 2) - PowerSeries.X * (PowerSeries.X + sSeries))) *
        q1Series ^ 2 * rSeries := by
    calc
      (PowerSeries.X + sSeries) * q1Series * (1 - PowerSeries.X * ((PowerSeries.X + sSeries) * q1Series)) * rSeries
        = (PowerSeries.X + sSeries) * q1Series *
            ((1 + PowerSeries.X ^ 2) * q1Series - PowerSeries.X * ((PowerSeries.X + sSeries) * q1Series)) * rSeries := by
            rw [hq]
      _ = ((PowerSeries.X + sSeries) * ((1 + PowerSeries.X ^ 2) - PowerSeries.X * (PowerSeries.X + sSeries))) *
            q1Series ^ 2 * rSeries := by ring
  rw [h1, h2, h3]
  have hnum : (1 + PowerSeries.X ^ 2) * sSeries + PowerSeries.C 2 * PowerSeries.X * (1 + PowerSeries.X ^ 2) +
        (-PowerSeries.C 2 * PowerSeries.X * (PowerSeries.X + sSeries) * sSeries) =
      (PowerSeries.X + sSeries) * ((1 + PowerSeries.X ^ 2) - PowerSeries.X * (PowerSeries.X + sSeries)) := by
    have hs2 : sSeries ^ 2 = 1 + (1 + 1) * PowerSeries.X ^ 2 := by rw [hsq, hc2]
    rw [hc2]
    linear_combination -PowerSeries.X * hs2
  linear_combination (q1Series ^ 2 * rSeries) * hnum

private lemma fSeries_ode (m : ℕ) :
    derivPS (fSeries m + PowerSeries.X * fSeries (m + 1)) =
      PowerSeries.C ((m + 1 : ℕ) : ℚ) * (fSeries (m + 1) - PowerSeries.X * fSeries (m + 2)) := by
  rw [fSeries_add_X_succ m, derivPS_pow, derivPS_wSeries]
  simp only [Nat.add_sub_cancel]
  unfold fSeries
  rw [pow_succ wSeries m, pow_succ wSeries (m + 1)]
  ring

private lemma coeff_zero_rSeries : PowerSeries.coeff 0 rSeries = 1 := by
  unfold rSeries
  have := coeff_substX2_even invSqrt1p2u 0
  simpa [coeff_zero_invSqrt1p2u] using this

private lemma coeff_one_rSeries : PowerSeries.coeff 1 rSeries = 0 := by
  unfold rSeries
  exact coeff_substX2_odd invSqrt1p2u 0

private lemma coeff_zero_sSeries : PowerSeries.coeff 0 sSeries = 1 := by
  unfold sSeries
  rw [add_mul, one_mul, map_add, sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc,
    PowerSeries.coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero, coeff_zero_rSeries]

private lemma coeff_one_sSeries : PowerSeries.coeff 1 sSeries = 0 := by
  unfold sSeries
  rw [add_mul, one_mul, map_add, sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc,
    PowerSeries.coeff_C_mul, coeff_X_mul_succ, coeff_X_mul_zero, mul_zero, add_zero, coeff_one_rSeries]

private lemma coeff_zero_q1Series : PowerSeries.coeff 0 q1Series = 1 := by
  unfold q1Series q1u
  have := coeff_substX2_even (invUnit1 (1 + PowerSeries.X)) 0
  simpa [coeff_zero_invUnit1] using this

private lemma coeff_one_q1Series : PowerSeries.coeff 1 q1Series = 0 := by
  unfold q1Series
  exact coeff_substX2_odd q1u 0

private lemma coeff_zero_wSeries : PowerSeries.coeff 0 wSeries = 1 := by
  unfold wSeries
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff,
    map_add, PowerSeries.coeff_X, if_neg (by decide : 0 ≠ 1), zero_add,
    coeff_zero_sSeries, coeff_zero_q1Series, mul_one]

private lemma coeff_one_wSeries : PowerSeries.coeff 1 wSeries = 1 := by
  unfold wSeries
  rw [coeff_mul_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, Nat.sub_self, map_add, PowerSeries.coeff_X, if_neg (by decide : 0 ≠ 1),
    ite_true, coeff_zero_sSeries, coeff_one_sSeries, coeff_zero_q1Series, coeff_one_q1Series]
  ring

private lemma coeff_zero_fSeries (m : ℕ) : PowerSeries.coeff 0 (fSeries m) = 1 := by
  unfold fSeries
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_wSeries, coeff_zero_rSeries, one_pow, mul_one]

private lemma coeff_one_fSeries (m : ℕ) : PowerSeries.coeff 1 (fSeries m) = (m : ℚ) := by
  unfold fSeries
  have hw1 : PowerSeries.coeff 1 (wSeries ^ m) = (m : ℚ) := by
    induction m with
    | zero => simp [PowerSeries.coeff_one]
    | succ m ih =>
      rw [pow_succ, coeff_mul_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_one]
      have hw0 : PowerSeries.coeff 0 (wSeries ^ m) = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_wSeries, one_pow]
      simp only [Nat.sub_zero, Nat.sub_self, hw0, coeff_zero_wSeries, coeff_one_wSeries, ih]
      push_cast; ring
  rw [coeff_mul_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_one]
  have hw0 : PowerSeries.coeff 0 (wSeries ^ m) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_wSeries, one_pow]
  simp only [Nat.sub_zero, Nat.sub_self, hw0, hw1, coeff_zero_rSeries, coeff_one_rSeries]
  ring

private lemma dSeq_eq_factorial_coeff (k : ℕ) :
    ∀ m : ℕ, (dSeq m k : ℚ) = (k.factorial : ℚ) * PowerSeries.coeff k (fSeries m) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro m
    match k with
    | 0 =>
      simp [dSeq, coeff_zero_fSeries]
    | 1 =>
      simp [dSeq, coeff_one_fSeries]
    | k + 2 =>
      have hc := congr_arg (PowerSeries.coeff (k + 1)) (fSeries_ode m)
      simp only [derivPS, PowerSeries.coeff_mk, map_add, map_sub, PowerSeries.coeff_C_mul] at hc
      rw [coeff_X_mul_succ, coeff_X_mul_succ] at hc
      have ih1 := ih (k + 1) (by omega) (m + 1)
      have ih2 := ih k (by omega) (m + 2)
      simp only [dSeq, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one]
      have hfac2 : ((k + 2).factorial : ℚ) = ((k + 2 : ℕ) : ℚ) * ((k + 1).factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hfac1 : ((k + 1).factorial : ℚ) = ((k + 1 : ℕ) : ℚ) * (k.factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [ih1, ih2, hfac2, hfac1]
      push_cast at hc ⊢
      linear_combination -((k.factorial : ℚ) * ((k : ℚ) + 1)) * hc

/-! ### Part 5: Splitting `fSeries 3` into its even and odd parts -/

private noncomputable def hEvenU : PowerSeries ℚ :=
  (1 + PowerSeries.C 5 * PowerSeries.X) * q1u ^ 3

private noncomputable def hOddU : PowerSeries ℚ :=
  (PowerSeries.C 3 + PowerSeries.C 7 * PowerSeries.X) * q1u ^ 3 * invSqrt1p2u

private lemma fSeries_three_split :
    fSeries 3 = substX2 hEvenU + PowerSeries.X * substX2 hOddU := by
  unfold fSeries wSeries hEvenU hOddU
  rw [substX2_mul, substX2_add, substX2_one, substX2_C_mul, substX2_X, substX2_pow,
    substX2_mul, substX2_mul, substX2_add, substX2_C_mul, substX2_X, substX2_pow]
  have hC3 : substX2 (PowerSeries.C (3 : ℚ)) = PowerSeries.C (3 : ℚ) := by
    have h := substX2_C_mul 3 1
    simpa [substX2_one] using h
  rw [hC3]
  change ((PowerSeries.X + sSeries) * q1Series) ^ 3 * rSeries =
    (1 + PowerSeries.C 5 * PowerSeries.X ^ 2) * q1Series ^ 3 +
      PowerSeries.X * ((PowerSeries.C 3 + PowerSeries.C 7 * PowerSeries.X ^ 2) * q1Series ^ 3 * rSeries)
  have hsq := sSeries_sq
  have hsr := sSeries_mul_rSeries
  have hc2 : PowerSeries.C (2 : ℚ) = 1 + 1 := by rw [← map_one PowerSeries.C, ← map_add]; norm_num
  have hc3 : PowerSeries.C (3 : ℚ) = 1 + 1 + 1 := by rw [← map_one PowerSeries.C, ← map_add, ← map_add]; norm_num
  have hc5 : PowerSeries.C (5 : ℚ) = 1 + 1 + 1 + 1 + 1 := by
    rw [← map_one PowerSeries.C, ← map_add, ← map_add, ← map_add, ← map_add]; norm_num
  have hc7 : PowerSeries.C (7 : ℚ) = 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
    rw [← map_one PowerSeries.C, ← map_add, ← map_add, ← map_add, ← map_add, ← map_add, ← map_add]; norm_num
  have hcube : (PowerSeries.X + sSeries) ^ 3 * rSeries =
      (1 + PowerSeries.C 5 * PowerSeries.X ^ 2) +
        PowerSeries.X * (PowerSeries.C 3 + PowerSeries.C 7 * PowerSeries.X ^ 2) * rSeries := by
    calc
      (PowerSeries.X + sSeries) ^ 3 * rSeries
        = (PowerSeries.X ^ 3 + 3 * PowerSeries.X * sSeries ^ 2) * rSeries +
            (3 * PowerSeries.X ^ 2 + sSeries ^ 2) * (sSeries * rSeries) := by ring
      _ = (PowerSeries.X ^ 3 + 3 * PowerSeries.X * (1 + PowerSeries.C 2 * PowerSeries.X ^ 2)) * rSeries +
            (3 * PowerSeries.X ^ 2 + (1 + PowerSeries.C 2 * PowerSeries.X ^ 2)) * 1 := by
            rw [hsq, hsr]
      _ = (1 + PowerSeries.C 5 * PowerSeries.X ^ 2) +
            PowerSeries.X * (PowerSeries.C 3 + PowerSeries.C 7 * PowerSeries.X ^ 2) * rSeries := by
            rw [hc2, hc3, hc5, hc7]; ring
  calc
    ((PowerSeries.X + sSeries) * q1Series) ^ 3 * rSeries
      = ((PowerSeries.X + sSeries) ^ 3 * rSeries) * q1Series ^ 3 := by ring
    _ = ((1 + PowerSeries.C 5 * PowerSeries.X ^ 2) +
          PowerSeries.X * (PowerSeries.C 3 + PowerSeries.C 7 * PowerSeries.X ^ 2) * rSeries) *
            q1Series ^ 3 := by rw [hcube]
    _ = (1 + PowerSeries.C 5 * PowerSeries.X ^ 2) * q1Series ^ 3 +
          PowerSeries.X * ((PowerSeries.C 3 + PowerSeries.C 7 * PowerSeries.X ^ 2) * q1Series ^ 3 * rSeries) := by
          ring

/-! ### Part 6: Conjecture 1 (even terms) -/

private lemma coeff_hEvenU (n : ℕ) :
    PowerSeries.coeff n hEvenU = (-1 : ℚ) ^ (n + 1) * ((n + 1 : ℕ) : ℚ) * (2 * (n : ℚ) - 1) := by
  let g : PowerSeries ℚ :=
    PowerSeries.mk (fun k => (-1 : ℚ) ^ (k + 1) * ((k + 1 : ℕ) : ℚ) * (2 * (k : ℚ) - 1))
  have hmul : (1 + PowerSeries.X) ^ 3 * g = 1 + PowerSeries.C 5 * PowerSeries.X := by
    have hexp : (1 + PowerSeries.X : PowerSeries ℚ) ^ 3 =
        1 + PowerSeries.C 3 * PowerSeries.X + PowerSeries.C 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by
      have hc3 : PowerSeries.C (3 : ℚ) = 1 + 1 + 1 := by
        rw [← map_one PowerSeries.C, ← map_add, ← map_add]; norm_num
      rw [hc3]; ring
    rw [hexp]
    ext k
    rw [add_mul, add_mul, add_mul, one_mul, map_add, map_add, map_add, map_add]
    have hX1 : ∀ m, PowerSeries.coeff (m + 1) (PowerSeries.C 3 * PowerSeries.X * g) =
        3 * PowerSeries.coeff m g := by
      intro m; rw [mul_assoc, PowerSeries.coeff_C_mul, coeff_X_mul_succ]
    have hX2 : ∀ m, PowerSeries.coeff (m + 2) (PowerSeries.C 3 * PowerSeries.X ^ 2 * g) =
        3 * PowerSeries.coeff m g := by
      intro m; rw [sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
        coeff_X_mul_succ, coeff_X_mul_succ]
    have hX3 : ∀ m, PowerSeries.coeff (m + 3) (PowerSeries.X ^ 3 * g) =
        PowerSeries.coeff m g := by
      intro m
      rw [show (PowerSeries.X : PowerSeries ℚ) ^ 3 = PowerSeries.X * (PowerSeries.X * PowerSeries.X) by ring,
        mul_assoc, mul_assoc, coeff_X_mul_succ, coeff_X_mul_succ, coeff_X_mul_succ]
    match k with
    | 0 =>
      rw [mul_assoc, PowerSeries.coeff_C_mul, coeff_X_mul_zero, mul_zero,
        sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
        coeff_X_mul_zero, mul_zero,
        show (PowerSeries.X : PowerSeries ℚ) ^ 3 = PowerSeries.X * PowerSeries.X ^ 2 by ring,
        mul_assoc, coeff_X_mul_zero, PowerSeries.coeff_one, if_pos rfl,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X, if_neg (by decide : 0 ≠ 1), mul_zero]
      simp [g]
    | 1 =>
      rw [hX1 0, sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
        coeff_X_mul_succ, coeff_X_mul_zero, mul_zero,
        show (PowerSeries.X : PowerSeries ℚ) ^ 3 = PowerSeries.X * (PowerSeries.X * PowerSeries.X) by ring,
        mul_assoc, mul_assoc, coeff_X_mul_succ, coeff_X_mul_zero, PowerSeries.coeff_one,
        if_neg (by decide : 1 ≠ 0), PowerSeries.coeff_C_mul, PowerSeries.coeff_X, if_pos rfl]
      simp [g]; norm_num
    | 2 =>
      rw [hX1 1, hX2 0,
        show (PowerSeries.X : PowerSeries ℚ) ^ 3 = PowerSeries.X * (PowerSeries.X * PowerSeries.X) by ring,
        mul_assoc, mul_assoc, coeff_X_mul_succ, coeff_X_mul_succ, coeff_X_mul_zero,
        PowerSeries.coeff_one, if_neg (by decide : 2 ≠ 0),
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X, if_neg (by decide : 2 ≠ 1)]
      simp [g]; norm_num
    | m + 3 =>
      rw [hX1 (m + 2), hX2 (m + 1), hX3 m, PowerSeries.coeff_one, if_neg (by omega),
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X, if_neg (by omega), mul_zero, add_zero]
      simp only [g, PowerSeries.coeff_mk]
      have hp1 : (-1 : ℚ) ^ (m + 1 + 1) = -((-1 : ℚ) ^ (m + 1)) := by rw [pow_succ]; ring
      have hp2 : (-1 : ℚ) ^ (m + 2 + 1) = (-1 : ℚ) ^ (m + 1) := by rw [pow_succ, hp1]; ring
      have hp3 : (-1 : ℚ) ^ (m + 3 + 1) = -((-1 : ℚ) ^ (m + 1)) := by rw [pow_succ, hp2]; ring
      rw [hp1, hp2, hp3]
      push_cast; ring
  have heq : hEvenU = g := by
    unfold hEvenU
    have hq3 : (1 + PowerSeries.X) ^ 3 * q1u ^ 3 = 1 := by
      rw [← mul_pow, mul_q1u, one_pow]
    calc
      (1 + PowerSeries.C 5 * PowerSeries.X) * q1u ^ 3
        = ((1 + PowerSeries.X) ^ 3 * g) * q1u ^ 3 := by rw [hmul]
      _ = ((1 + PowerSeries.X) ^ 3 * q1u ^ 3) * g := by ring
      _ = 1 * g := by rw [hq3]
      _ = g := one_mul _
  rw [heq]
  simp [g]

private lemma a127068_even (n : ℕ) :
    a127068 (2 * n) =
      (-1 : ℤ) ^ (n + 1) * ((n + 1 : ℕ) : ℤ) * (2 * (n : ℤ) - 1) * (((2 * n).factorial : ℕ) : ℤ) := by
  have hq : (a127068 (2 * n) : ℚ) =
      ((-1 : ℤ) ^ (n + 1) * ((n + 1 : ℕ) : ℤ) * (2 * (n : ℤ) - 1) * (((2 * n).factorial : ℕ) : ℤ) : ℚ) := by
    unfold a127068
    rw [dSeq_eq_factorial_coeff (2 * n) 3, fSeries_three_split, map_add, coeff_substX2_even,
      coeff_hEvenU]
    have hodd0 : PowerSeries.coeff (2 * n) (PowerSeries.X * substX2 hOddU) = 0 := by
      cases n with
      | zero => exact coeff_X_mul_zero _
      | succ n' =>
        rw [show 2 * (n' + 1) = (2 * n' + 1) + 1 by omega, coeff_X_mul_succ, coeff_substX2_odd]
    rw [hodd0, add_zero]
    push_cast; ring
  exact_mod_cast hq

/-! ### Part 7: Conjecture 2 (odd terms via exact 2nd-order ODE on `hOddU`) -/

private lemma ode_hOddU :
    PowerSeries.C 2 * PowerSeries.X * (1 + PowerSeries.X) * (1 + PowerSeries.C 2 * PowerSeries.X) *
        derivPS (derivPS hOddU) +
      (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) *
        derivPS hOddU +
      (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * hOddU = 0 := by
  let P : PowerSeries ℚ := PowerSeries.C 3 + PowerSeries.C 7 * PowerSeries.X
  let U1 : PowerSeries ℚ := 1 + PowerSeries.X
  let U2 : PowerSeries ℚ := 1 + PowerSeries.C 2 * PowerSeries.X
  have hP' : derivPS P = PowerSeries.C 7 := by
    change derivPS (PowerSeries.C 3 + PowerSeries.C 7 * PowerSeries.X) = PowerSeries.C 7
    rw [derivPS_add, derivPS_C_mul, derivPS_X]
    have hc3 : derivPS (PowerSeries.C (3 : ℚ)) = 0 := by
      rw [← mul_one (PowerSeries.C (3 : ℚ)), derivPS_C_mul, derivPS_one, mul_zero]
    rw [hc3, zero_add, mul_one]
  have hq3' : derivPS (q1u ^ 3) = -PowerSeries.C 3 * q1u ^ 4 := by
    rw [derivPS_pow, derivPS_q1u]
    simp only [Nat.cast_ofNat]
    ring
  have hq4' : derivPS (q1u ^ 4) = -PowerSeries.C 4 * q1u ^ 5 := by
    rw [derivPS_pow, derivPS_q1u]
    simp only [Nat.cast_ofNat]
    ring
  have hR' : U2 * derivPS invSqrt1p2u = -invSqrt1p2u := by
    have h := ode_invSqrt1p2u
    linear_combination h
  have hR'' : U2 ^ 2 * derivPS (derivPS invSqrt1p2u) = PowerSeries.C 3 * invSqrt1p2u := by
    have hd := congr_arg derivPS hR'
    rw [derivPS_mul, derivPS_neg] at hd
    have hU2' : derivPS U2 = PowerSeries.C 2 := by
      change derivPS (1 + PowerSeries.C 2 * PowerSeries.X) = PowerSeries.C 2
      rw [derivPS_add, derivPS_one, derivPS_C_mul, derivPS_X, zero_add, mul_one]
    rw [hU2'] at hd
    have h3 : PowerSeries.C (2 : ℚ) + 1 = PowerSeries.C (3 : ℚ) := by
      rw [← map_one PowerSeries.C, ← map_add]; norm_num
    linear_combination U2 * hd - (PowerSeries.C 2 + 1) * hR' + invSqrt1p2u * h3
  -- General product-rule helper: for any Q, U1 * U2 * derivPS (Q * q1u^3 * R) = (derivPS Q * U1 * U2 - 3 * Q * U2 - Q * U1) * q1u^3 * R
  have hprod_deriv : ∀ Q : PowerSeries ℚ,
      U1 * U2 * derivPS (Q * q1u ^ 3 * invSqrt1p2u) =
        (derivPS Q * U1 * U2 - PowerSeries.C 3 * Q * U2 - Q * U1) * q1u ^ 3 * invSqrt1p2u := by
    intro Q
    rw [derivPS_mul, derivPS_mul, hq3']
    have hUq : U1 * q1u = 1 := mul_q1u
    have hA : U1 * U2 * (derivPS Q * q1u ^ 3 * invSqrt1p2u) =
        (derivPS Q * U1 * U2) * q1u ^ 3 * invSqrt1p2u := by ring
    have hB : U1 * U2 * (Q * (-PowerSeries.C 3 * q1u ^ 4) * invSqrt1p2u) =
        (-PowerSeries.C 3 * Q * U2) * q1u ^ 3 * invSqrt1p2u := by
      calc
        U1 * U2 * (Q * (-PowerSeries.C 3 * q1u ^ 4) * invSqrt1p2u)
          = (-PowerSeries.C 3 * Q * U2) * (U1 * q1u) * q1u ^ 3 * invSqrt1p2u := by ring
        _ = (-PowerSeries.C 3 * Q * U2) * 1 * q1u ^ 3 * invSqrt1p2u := by rw [hUq]
        _ = (-PowerSeries.C 3 * Q * U2) * q1u ^ 3 * invSqrt1p2u := by ring
    have hC : U1 * U2 * (Q * q1u ^ 3 * derivPS invSqrt1p2u) =
        (-Q * U1) * q1u ^ 3 * invSqrt1p2u := by
      calc
        U1 * U2 * (Q * q1u ^ 3 * derivPS invSqrt1p2u)
          = Q * U1 * q1u ^ 3 * (U2 * derivPS invSqrt1p2u) := by ring
        _ = Q * U1 * q1u ^ 3 * (-invSqrt1p2u) := by rw [hR']
        _ = (-Q * U1) * q1u ^ 3 * invSqrt1p2u := by ring
    linear_combination hA + hB + hC
  let A : PowerSeries ℚ :=
    -PowerSeries.C 5 - PowerSeries.C 28 * PowerSeries.X - PowerSeries.C 35 * PowerSeries.X ^ 2
  have h1 : U1 * U2 * derivPS hOddU = A * q1u ^ 3 * invSqrt1p2u := by
    have h0 := hprod_deriv P
    change U1 * U2 * derivPS hOddU = _ at h0
    rw [h0, hP']
    congr 2
    change PowerSeries.C 7 * (1 + PowerSeries.X) * (1 + PowerSeries.C 2 * PowerSeries.X) -
        PowerSeries.C 3 * (PowerSeries.C 3 + PowerSeries.C 7 * PowerSeries.X) *
          (1 + PowerSeries.C 2 * PowerSeries.X) -
        (PowerSeries.C 3 + PowerSeries.C 7 * PowerSeries.X) * (1 + PowerSeries.X) =
      -PowerSeries.C 5 - PowerSeries.C 28 * PowerSeries.X - PowerSeries.C 35 * PowerSeries.X ^ 2
    have h2 : PowerSeries.C (2 : ℚ) = 2 := map_ofNat PowerSeries.C 2
    have h3 : PowerSeries.C (3 : ℚ) = 3 := map_ofNat PowerSeries.C 3
    have h5 : PowerSeries.C (5 : ℚ) = 5 := map_ofNat PowerSeries.C 5
    have h7 : PowerSeries.C (7 : ℚ) = 7 := map_ofNat PowerSeries.C 7
    have h28 : PowerSeries.C (28 : ℚ) = 28 := map_ofNat PowerSeries.C 28
    have h35 : PowerSeries.C (35 : ℚ) = 35 := map_ofNat PowerSeries.C 35
    rw [h2, h3, h5, h7, h28, h35]; ring
  have hA' : derivPS A = -PowerSeries.C 28 - PowerSeries.C 70 * PowerSeries.X := by
    change derivPS (-PowerSeries.C 5 - PowerSeries.C 28 * PowerSeries.X - PowerSeries.C 35 * PowerSeries.X ^ 2) = _
    rw [derivPS_sub, derivPS_sub, derivPS_neg, derivPS_C_mul, derivPS_X, derivPS_C_mul, derivPS_pow, derivPS_X]
    have hc5 : derivPS (PowerSeries.C (5 : ℚ)) = 0 := by
      rw [← mul_one (PowerSeries.C (5 : ℚ)), derivPS_C_mul, derivPS_one, mul_zero]
    rw [hc5, show (2 : ℕ) - 1 = 1 by rfl, pow_one]
    simp only [neg_zero, zero_sub, mul_one, Nat.cast_ofNat]
    have h2 : PowerSeries.C (2 : ℚ) = 2 := map_ofNat PowerSeries.C 2
    have h28 : PowerSeries.C (28 : ℚ) = 28 := map_ofNat PowerSeries.C 28
    have h35 : PowerSeries.C (35 : ℚ) = 35 := map_ofNat PowerSeries.C 35
    have h70 : PowerSeries.C (70 : ℚ) = 70 := map_ofNat PowerSeries.C 70
    rw [h2, h28, h35, h70]; ring
  have hU12' : derivPS (U1 * U2) = PowerSeries.C 3 + PowerSeries.C 4 * PowerSeries.X := by
    change derivPS ((1 + PowerSeries.X) * (1 + PowerSeries.C 2 * PowerSeries.X)) = _
    rw [derivPS_mul, derivPS_add, derivPS_one, derivPS_X, derivPS_add, derivPS_one, derivPS_C_mul, derivPS_X]
    simp only [zero_add, one_mul, mul_one]
    have h2 : PowerSeries.C (2 : ℚ) = 2 := map_ofNat PowerSeries.C 2
    have h3 : PowerSeries.C (3 : ℚ) = 3 := map_ofNat PowerSeries.C 3
    have h4 : PowerSeries.C (4 : ℚ) = 4 := map_ofNat PowerSeries.C 4
    rw [h2, h3, h4]; ring
  have h2 : U1 * U2 * (U1 * U2 * derivPS (derivPS hOddU)) =
      (derivPS A * U1 * U2 - PowerSeries.C 3 * A * U2 - A * U1 - derivPS (U1 * U2) * A) *
        q1u ^ 3 * invSqrt1p2u := by
    have hd1 := congr_arg derivPS h1
    rw [derivPS_mul] at hd1
    have hd2 := hprod_deriv A
    calc
      U1 * U2 * (U1 * U2 * derivPS (derivPS hOddU))
        = U1 * U2 * (derivPS (A * q1u ^ 3 * invSqrt1p2u) - derivPS (U1 * U2) * derivPS hOddU) := by
            congr 1; linear_combination hd1
      _ = U1 * U2 * derivPS (A * q1u ^ 3 * invSqrt1p2u) - derivPS (U1 * U2) * (U1 * U2 * derivPS hOddU) := by
            ring
      _ = (derivPS A * U1 * U2 - PowerSeries.C 3 * A * U2 - A * U1) * q1u ^ 3 * invSqrt1p2u -
            derivPS (U1 * U2) * (A * q1u ^ 3 * invSqrt1p2u) := by rw [hd2, h1]
      _ = (derivPS A * U1 * U2 - PowerSeries.C 3 * A * U2 - A * U1 - derivPS (U1 * U2) * A) *
            q1u ^ 3 * invSqrt1p2u := by ring
  -- Multiply the ODE LHS by U1 * U2 and reduce to a pure polynomial identity!
  have hmul_ode : U1 * U2 *
      (PowerSeries.C 2 * PowerSeries.X * U1 * U2 * derivPS (derivPS hOddU) +
        (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) *
          derivPS hOddU +
        (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * hOddU) = 0 := by
    have hcomb : U1 * U2 *
        (PowerSeries.C 2 * PowerSeries.X * U1 * U2 * derivPS (derivPS hOddU) +
          (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) *
            derivPS hOddU +
          (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * hOddU) =
        (PowerSeries.C 2 * PowerSeries.X *
            (derivPS A * U1 * U2 - PowerSeries.C 3 * A * U2 - A * U1 - derivPS (U1 * U2) * A) +
          (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) * A +
          (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * P * U1 * U2) *
          q1u ^ 3 * invSqrt1p2u := by
      have hh : U1 * U2 * hOddU = P * U1 * U2 * q1u ^ 3 * invSqrt1p2u := by
        change U1 * U2 * (P * q1u ^ 3 * invSqrt1p2u) = _; ring
      calc
        U1 * U2 *
            (PowerSeries.C 2 * PowerSeries.X * U1 * U2 * derivPS (derivPS hOddU) +
              (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) *
                derivPS hOddU +
              (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * hOddU)
          = PowerSeries.C 2 * PowerSeries.X * (U1 * U2 * (U1 * U2 * derivPS (derivPS hOddU))) +
              (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) *
                (U1 * U2 * derivPS hOddU) +
              (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * (U1 * U2 * hOddU) := by ring
        _ = PowerSeries.C 2 * PowerSeries.X *
              ((derivPS A * U1 * U2 - PowerSeries.C 3 * A * U2 - A * U1 - derivPS (U1 * U2) * A) *
                q1u ^ 3 * invSqrt1p2u) +
            (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) *
              (A * q1u ^ 3 * invSqrt1p2u) +
            (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) *
              (P * U1 * U2 * q1u ^ 3 * invSqrt1p2u) := by rw [h2, h1, hh]
        _ = (PowerSeries.C 2 * PowerSeries.X *
              (derivPS A * U1 * U2 - PowerSeries.C 3 * A * U2 - A * U1 - derivPS (U1 * U2) * A) +
            (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) * A +
            (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * P * U1 * U2) *
            q1u ^ 3 * invSqrt1p2u := by ring
    rw [hcomb, hA', hU12']
    have hpoly_zero : PowerSeries.C 2 * PowerSeries.X *
          ((-PowerSeries.C 28 - PowerSeries.C 70 * PowerSeries.X) * U1 * U2 -
            PowerSeries.C 3 * A * U2 - A * U1 -
            (PowerSeries.C 3 + PowerSeries.C 4 * PowerSeries.X) * A) +
        (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) * A +
        (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * P * U1 * U2 = 0 := by
      dsimp only [A, P, U1, U2]
      simp only [map_ofNat]
      ring
    rw [hpoly_zero, zero_mul, zero_mul]
  -- Cancel unit U1 * U2 using q1u * invSqrt1p2u ^ 2
  have hinv : (U1 * U2) * (q1u * invSqrt1p2u ^ 2) = 1 := by
    calc
      (U1 * U2) * (q1u * invSqrt1p2u ^ 2)
        = (U1 * q1u) * (U2 * invSqrt1p2u ^ 2) := by ring
      _ = 1 * 1 := by rw [mul_q1u, sq_invSqrt1p2u]
      _ = 1 := mul_one _
  calc
    PowerSeries.C 2 * PowerSeries.X * U1 * U2 * derivPS (derivPS hOddU) +
        (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) *
          derivPS hOddU +
        (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * hOddU
      = (q1u * invSqrt1p2u ^ 2) * (U1 * U2 *
          (PowerSeries.C 2 * PowerSeries.X * U1 * U2 * derivPS (derivPS hOddU) +
            (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) *
              derivPS hOddU +
            (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * hOddU)) := by
          calc
            _ = 1 * _ := (one_mul _).symm
            _ = ((U1 * U2) * (q1u * invSqrt1p2u ^ 2)) * _ := by rw [hinv]
            _ = _ := by ring
    _ = (q1u * invSqrt1p2u ^ 2) * 0 := by rw [hmul_ode]
    _ = 0 := mul_zero _

private lemma coeff_hOddU_rec (m : ℕ) :
    ((m + 2 : ℕ) : ℚ) * (2 * ((m + 2 : ℕ) : ℚ) + 1) * PowerSeries.coeff (m + 2) hOddU +
      (2 * ((m + 2 : ℕ) : ℚ) + 3) * (3 * ((m + 2 : ℕ) : ℚ) - 2) * PowerSeries.coeff (m + 1) hOddU +
      (2 * ((m + 2 : ℕ) : ℚ) + 1) * (2 * ((m + 2 : ℕ) : ℚ) + 3) * PowerSeries.coeff m hOddU = 0 := by
  have hode :
      (PowerSeries.C 2 * PowerSeries.X + PowerSeries.C 6 * PowerSeries.X ^ 2 + PowerSeries.C 4 * PowerSeries.X ^ 3) *
          derivPS (derivPS hOddU) +
        (PowerSeries.C 3 + PowerSeries.C 23 * PowerSeries.X + PowerSeries.C 28 * PowerSeries.X ^ 2) *
          derivPS hOddU +
        (PowerSeries.C 5 + PowerSeries.C 35 * PowerSeries.X) * hOddU = 0 := by
    have hexp : (PowerSeries.C (2 : ℚ) * PowerSeries.X * (1 + PowerSeries.X) * (1 + PowerSeries.C (2 : ℚ) * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.C (2 : ℚ) * PowerSeries.X + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]; ring
    linear_combination ode_hOddU - derivPS (derivPS hOddU) * hexp
  have hc := congr_arg (PowerSeries.coeff (m + 1)) hode
  rw [map_zero] at hc
  simp only [add_mul, map_add] at hc
  have hx1 : ∀ (a : ℚ) (f : PowerSeries ℚ) (k : ℕ),
      PowerSeries.coeff (k + 1) (PowerSeries.C a * PowerSeries.X * f) = a * PowerSeries.coeff k f := by
    intro a f k; rw [mul_assoc, PowerSeries.coeff_C_mul, coeff_X_mul_succ]
  have hx2 : ∀ (a : ℚ) (f : PowerSeries ℚ) (k : ℕ),
      PowerSeries.coeff (k + 2) (PowerSeries.C a * PowerSeries.X ^ 2 * f) = a * PowerSeries.coeff k f := by
    intro a f k
    rw [sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
      coeff_X_mul_succ, coeff_X_mul_succ]
  have hx3 : ∀ (a : ℚ) (f : PowerSeries ℚ) (k : ℕ),
      PowerSeries.coeff (k + 3) (PowerSeries.C a * PowerSeries.X ^ 3 * f) = a * PowerSeries.coeff k f := by
    intro a f k
    rw [show (PowerSeries.X : PowerSeries ℚ) ^ 3 = PowerSeries.X * (PowerSeries.X * PowerSeries.X) by ring,
      mul_assoc, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
      coeff_X_mul_succ, coeff_X_mul_succ, coeff_X_mul_succ]
  have hx2_zero : ∀ (a : ℚ) (f : PowerSeries ℚ),
      PowerSeries.coeff 1 (PowerSeries.C a * PowerSeries.X ^ 2 * f) = 0 := by
    intro a f
    rw [sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
      coeff_X_mul_succ, coeff_X_mul_zero, mul_zero]
  have hx3_zero : ∀ (a : ℚ) (f : PowerSeries ℚ),
      PowerSeries.coeff 1 (PowerSeries.C a * PowerSeries.X ^ 3 * f) = 0 := by
    intro a f
    rw [show (PowerSeries.X : PowerSeries ℚ) ^ 3 = PowerSeries.X * (PowerSeries.X * PowerSeries.X) by ring,
      mul_assoc, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, coeff_X_mul_succ, coeff_X_mul_zero, mul_zero]
  have hx3_one : ∀ (a : ℚ) (f : PowerSeries ℚ),
      PowerSeries.coeff 2 (PowerSeries.C a * PowerSeries.X ^ 3 * f) = 0 := by
    intro a f
    rw [show (PowerSeries.X : PowerSeries ℚ) ^ 3 = PowerSeries.X * (PowerSeries.X * PowerSeries.X) by ring,
      mul_assoc, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
      coeff_X_mul_succ, coeff_X_mul_succ, coeff_X_mul_zero, mul_zero]
  rw [hx1 2 _ m, hx1 23 _ m, hx1 35 _ m, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hc
  cases m with
  | zero =>
    rw [hx2_zero 6, hx3_zero 4, hx2_zero 28] at hc
    simp only [derivPS, PowerSeries.coeff_mk] at hc
    push_cast at hc ⊢
    linarith
  | succ m' =>
    cases m' with
    | zero =>
      rw [hx2 6 _ 0, hx3_one 4, hx2 28 _ 0] at hc
      simp only [derivPS, PowerSeries.coeff_mk] at hc
      push_cast at hc ⊢
      linarith
    | succ r =>
      rw [hx2 6 _ (r + 1), hx3 4 _ r, hx2 28 _ (r + 1)] at hc
      simp only [derivPS, PowerSeries.coeff_mk] at hc
      push_cast at hc ⊢
      linarith

private lemma a127068_odd_coeff (n : ℕ) :
    (a127068 (2 * n + 1) : ℚ) = ((2 * n + 1).factorial : ℚ) * PowerSeries.coeff n hOddU := by
  unfold a127068
  rw [dSeq_eq_factorial_coeff (2 * n + 1) 3, fSeries_three_split, map_add, coeff_substX2_odd,
    zero_add, coeff_X_mul_succ, coeff_substX2_even]

private lemma a127068_odd_rec (n : ℕ) (hn : 2 ≤ n) :
    a127068 (2 * n + 1) =
      -2 * (2 * (n : ℤ) + 3) * (3 * (n : ℤ) - 2) * a127068 (2 * n - 1) -
        4 * ((n : ℤ) - 1) * (2 * (n : ℤ) + 3) * (4 * (n : ℤ) ^ 2 - 1) * a127068 (2 * n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hrec := coeff_hOddU_rec m
  have ha2 := a127068_odd_coeff (m + 2)
  have ha1 := a127068_odd_coeff (m + 1)
  have ha0 := a127068_odd_coeff m
  have hsub1 : 2 * (m + 2) - 1 = 2 * (m + 1) + 1 := by omega
  have hsub3 : 2 * (m + 2) - 3 = 2 * m + 1 := by omega
  have hq : (a127068 (2 * (m + 2) + 1) : ℚ) =
      (-2 * (2 * ((m + 2 : ℕ) : ℤ) + 3) * (3 * ((m + 2 : ℕ) : ℤ) - 2) * a127068 (2 * (m + 2) - 1) -
        4 * (((m + 2 : ℕ) : ℤ) - 1) * (2 * ((m + 2 : ℕ) : ℤ) + 3) *
          (4 * ((m + 2 : ℕ) : ℤ) ^ 2 - 1) * a127068 (2 * (m + 2) - 3) : ℚ) := by
    rw [hsub1, hsub3]
    push_cast
    rw [ha2, ha1, ha0]
    have hf1 : ((2 * (m + 1) + 1).factorial : ℚ) =
        ((2 * m + 3 : ℕ) : ℚ) * (((2 * m + 2 : ℕ) : ℚ) * ((2 * m + 1).factorial : ℚ)) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hf2 : ((2 * (m + 2) + 1).factorial : ℚ) =
        ((2 * m + 5 : ℕ) : ℚ) * (((2 * m + 4 : ℕ) : ℚ) * ((2 * (m + 1) + 1).factorial : ℚ)) := by
      rw [show 2 * (m + 2) + 1 = (2 * m + 4) + 1 by omega, Nat.factorial_succ,
        show 2 * m + 4 = (2 * m + 3) + 1 by omega, Nat.factorial_succ,
        show 2 * (m + 1) + 1 = 2 * m + 3 by omega]
      push_cast; ring
    rw [hf2, hf1]
    push_cast at hrec ⊢
    linear_combination 2 * ((2 * m + 1).factorial : ℚ) * ((2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 3)) * hrec
  exact_mod_cast hq

theorem solution :
    (∀ n : ℕ,
      a127068 (2 * n) =
        (-1 : ℤ) ^ (n + 1) * ((n + 1 : ℕ) : ℤ) * (2 * (n : ℤ) - 1) * (((2 * n).factorial : ℕ) : ℤ)) ∧
    a127068 1 = 3 ∧
    a127068 3 = -30 ∧
    (∀ n : ℕ, 2 ≤ n →
      a127068 (2 * n + 1) =
        -2 * (2 * (n : ℤ) + 3) * (3 * (n : ℤ) - 2) * a127068 (2 * n - 1) -
          4 * ((n : ℤ) - 1) * (2 * (n : ℤ) + 3) * (4 * (n : ℤ) ^ 2 - 1) * a127068 (2 * n - 3)) :=
  ⟨a127068_even, rfl, rfl, a127068_odd_rec⟩

end OMA.P_oeis_a127068

theorem OMA.solution : type_of% @OMA.S_oeis_a127068.main :=
  OMA.P_oeis_a127068.solution
