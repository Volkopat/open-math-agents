import FormalConjectures.OptimizationConstants.«7a»

/-! The two-sided coefficient bound permits index selection even when the
integer obtained from the first linear form vanishes. The argument uses
the same rate margin as Hata's lemma in Bai, arXiv:2609.11276v2, §5.1. -/

namespace OMA.R_Constant7a_c7a_upper_bound_R1

open Filter
open scoped Topology

private noncomputable def rationalIntegrand (n : ℕ) (t : ℂ) : ℂ :=
  5 * t ^ (3714 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (3714 * n) /
    (25 - t ^ 2) ^ (5570 * n + 1)

/-- The real part of Bai's contour integral, parameterized by the imaginary
coordinate. Multiplying the vertical tangent by the outer `i` gives `-1`. -/
private noncomputable def contour (n : ℕ) : ℝ :=
  -(∫ y in (-2 : ℝ)..2, (rationalIntegrand n (-1 + (y : ℂ) * Complex.I)).re)

/-- Expands the shared contour in the arithmetic and decay hypotheses. -/
theorem contour_eq (n : ℕ) :
    contour n = -(∫ y in (-2 : ℝ)..2,
      let t := (-1 : ℂ) + (y : ℂ) * Complex.I
      (5 * t ^ (3714 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (3714 * n) /
        (25 - t ^ 2) ^ (5570 * n + 1)).re) := rfl

private theorem not_liouville_of_forms {θ k p : ℝ} (hk : 0 ≤ k) (hp : k + 1 < p)
    {A B D R : ℝ} (hA : 1 ≤ A) (hB : 0 < B) (hR : 1 < R)
    (hRD : R ≤ D) (hAB : A * R ≤ B * D) (hAk : A ≤ R ^ k)
    {U V : ℕ → ℤ} {n₀ : ℕ}
    (bounds : ∀ n ≥ n₀, B ^ n ≤ |(V n : ℝ)| ∧ |(V n : ℝ)| ≤ A ^ n ∧
      |(U n : ℝ) + (V n : ℝ) * θ| ≤ 1 / D ^ n) :
    ¬ LiouvilleWith p θ := by
  intro hl
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  have hR₀ : 0 < R := zero_lt_one.trans hR
  have hD₀ : 0 < D := hR₀.trans_le hRD
  let K : ℝ := 4 * A
  let E : ℝ := (R * K) ^ k
  let s : ℝ := (k + 1 + p) / 2
  let e : ℝ := s - (k + 1)
  have he : 0 < e := by dsimp [e, s]; linarith
  have hs : s < p := by dsimp [s]; linarith
  have qLarge : ∀ᶠ q : ℕ in atTop, R ^ n₀ / K ≤ (q : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have qPower : ∀ᶠ q : ℕ in atTop, 4 * E < (q : ℝ) ^ e :=
    ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop _)
  obtain ⟨q, ⟨⟨hq, hqLarge⟩, hqPower⟩, m, hne, hsmall⟩ :=
    ((((eventually_ge_atTop (1 : ℕ)).and qLarge).and qPower).and_frequently
      (hl.frequently_lt_rpow_neg hs)).exists
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  let δ : ℝ := θ - (m : ℝ) / (q : ℝ)
  let f (n : ℕ) : ℝ := (U n : ℝ) + (V n : ℝ) * θ
  let z (n : ℕ) : ℤ := (q : ℤ) * U n + m * V n
  have δpos : 0 < |δ| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have form (n : ℕ) : (z n : ℝ) = (q : ℝ) * f n - q * ((V n : ℝ) * δ) := by
    dsimp [z, f, δ]
    push_cast
    field_simp
    ring
  have hK : 0 < K := by dsimp [K]; positivity
  have growth : Tendsto (fun n : ℕ ↦ R ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hR
  have existsN : ∃ n : ℕ, K * q < R ^ n :=
    (growth.eventually (eventually_gt_atTop (K * q))).exists
  let N := Nat.find existsN
  have hN : K * q < R ^ N := Nat.find_spec existsN
  have hn₀ : R ^ n₀ ≤ K * q := by
    linear_combination (div_le_iff₀ hK).mp hqLarge
  have Nlarge : n₀ < N := by
    by_contra! h
    exact (not_lt_of_ge ((pow_le_pow_right₀ hR.le h).trans hn₀)) hN
  have Nupper : R ^ N ≤ R * (K * q) := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
    have hmin : ¬ K * (q : ℝ) < R ^ j := Nat.find_min existsN (by omega)
    rw [hj, pow_succ]
    exact (mul_le_mul_of_nonneg_right (le_of_not_gt hmin) hR₀.le).trans_eq (mul_comm _ _)
  have scale (n : ℕ) (hn : N ≤ n) : K * q < R ^ n :=
    hN.trans_le (pow_le_pow_right₀ hR.le hn)
  have formSmall (n : ℕ) (hn : N ≤ n) : |(q : ℝ) * f n| < 1 / 4 := by
    have hb := (bounds n (by omega)).2.2
    have hd := pow_le_pow_left₀ hR₀.le hRD n
    have ht : 4 * (q : ℝ) < D ^ n := by
      calc 4 * (q : ℝ) ≤ K * q := by dsimp [K]; nlinarith
        _ < R ^ n := scale n hn
        _ ≤ D ^ n := hd
    rw [abs_mul, abs_of_pos hq₀]
    calc (q : ℝ) * |f n| ≤ q * (1 / D ^ n) := mul_le_mul_of_nonneg_left hb hq₀.le
      _ < 1 / 4 := by rw [mul_one_div, div_lt_iff₀ (pow_pos hD₀ n)]; linarith
  have zeroOfSmall (n : ℕ) (hn : N ≤ n)
      (hv : |(q : ℝ) * ((V n : ℝ) * δ)| < 1 / 4) : z n = 0 := by
    have hz : |(z n : ℝ)| < 1 := by
      rw [form]
      exact (abs_sub_le _ 0 _).trans_lt (by
        rw [sub_zero, zero_sub, abs_neg]
        linarith [formSmall n hn])
    have hz' : |z n| < 1 := by exact_mod_cast hz
    exact Int.abs_lt_one_iff.mp hz'
  have initial : z N = 0 := by
    apply zeroOfSmall N le_rfl
    rw [abs_mul, abs_mul, abs_of_pos hq₀]
    have vupper : |(V N : ℝ)| ≤ E * (q : ℝ) ^ k := by
      calc |(V N : ℝ)| ≤ A ^ N := (bounds N (by omega)).2.1
        _ ≤ (R ^ k) ^ N := pow_le_pow_left₀ hA₀.le hAk _
        _ = (R ^ N) ^ k := by rw [← Real.rpow_mul_natCast hR₀.le,
          ← Real.rpow_natCast_mul hR₀.le, mul_comm k]
        _ ≤ (R * (K * q)) ^ k := Real.rpow_le_rpow (by positivity) Nupper hk
        _ = E * (q : ℝ) ^ k := by rw [← mul_assoc, Real.mul_rpow (by positivity) hq₀.le]
    have hpw : (q : ℝ) ^ e > 0 := Real.rpow_pos_of_pos hq₀ _
    calc (q : ℝ) * (|(V N : ℝ)| * |δ|) ≤ q * ((E * (q : ℝ) ^ k) * |δ|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right vupper (abs_nonneg _)) hq₀.le
      _ < q * ((E * (q : ℝ) ^ k) * (q : ℝ) ^ (-s)) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hsmall
          (mul_pos (Real.rpow_pos_of_pos (mul_pos hR₀ hK) _) (Real.rpow_pos_of_pos hq₀ _))) hq₀
      _ = E / (q : ℝ) ^ e := by
        calc (q : ℝ) * ((E * (q : ℝ) ^ k) * (q : ℝ) ^ (-s)) =
            E * (((q : ℝ) ^ (1 : ℝ) * (q : ℝ) ^ k) * (q : ℝ) ^ (-s)) := by
              rw [Real.rpow_one]; ring
          _ = E / (q : ℝ) ^ e := by
            rw [← Real.rpow_add hq₀, ← Real.rpow_add hq₀,
              show 1 + k + -s = -e by dsimp [e]; ring, Real.rpow_neg hq₀.le, div_eq_mul_inv]
      _ < 1 / 4 := by rw [div_lt_iff₀ hpw]; linarith
  have absZero (n : ℕ) (hn : N ≤ n) (hz : z n = 0) :
      |δ| ≤ 1 / (B * D) ^ n := by
    have eq := form n
    rw [hz, Int.cast_zero] at eq
    have eq' : f n = (V n : ℝ) * δ := mul_left_cancel₀ hq₀.ne' (sub_eq_zero.mp eq.symm)
    have h₁ := (bounds n (by omega)).1
    have h₂ := (bounds n (by omega)).2.2
    rw [show |f n| = |(V n : ℝ)| * |δ| by rw [eq', abs_mul]] at h₂
    apply (le_div_iff₀ (pow_pos (mul_pos hB hD₀) n)).2
    calc |δ| * (B * D) ^ n = (B ^ n * |δ|) * D ^ n := by rw [mul_pow]; ring
      _ ≤ (|(V n : ℝ)| * |δ|) * D ^ n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₁ (abs_nonneg _)) (by positivity)
      _ ≤ 1 := (le_div_iff₀ (pow_pos hD₀ n)).1 h₂
  have next (n : ℕ) (hn : N ≤ n) (hz : z n = 0) : z (n + 1) = 0 := by
    apply zeroOfSmall _ (by omega)
    rw [abs_mul, abs_mul, abs_of_pos hq₀]
    have bpos : 0 < (B * D) ^ n := by positivity
    have rate : A ^ n * R ^ n ≤ (B * D) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hAB n
    have stepBound : A ^ (n + 1) * (1 / (B * D) ^ n) ≤ A / R ^ n := by
      rw [mul_one_div, div_le_div_iff₀ bpos (pow_pos hR₀ n), pow_succ]
      calc A ^ n * A * R ^ n = A * (A ^ n * R ^ n) := by ring
        _ ≤ A * (B * D) ^ n := mul_le_mul_of_nonneg_left rate hA₀.le
    calc (q : ℝ) * (|(V (n + 1) : ℝ)| * |δ|) ≤ q * (A ^ (n + 1) * (1 / (B * D) ^ n)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (bounds (n + 1) (by omega)).2.1 (absZero n hn hz)
              (abs_nonneg _) (by positivity)) hq₀.le
      _ ≤ q * (A / R ^ n) := mul_le_mul_of_nonneg_left stepBound hq₀.le
      _ < 1 / 4 := by
        rw [← mul_div_assoc, div_lt_iff₀ (pow_pos hR₀ n)]
        have h := scale n hn
        dsimp [K] at h
        nlinarith
  have allZero (n : ℕ) (hn : N ≤ n) : z n = 0 := by
    induction n, hn using Nat.le_induction with
    | base => exact initial
    | succ n hn ih => exact next n hn ih
  obtain ⟨n, hn, hr⟩ := ((eventually_ge_atTop N).and
    (growth.eventually (eventually_gt_atTop (1 / |δ|)))).exists
  have hbase : R ≤ B * D := (by nlinarith : R ≤ A * R).trans hAB
  have hlarge := hr.trans_le (pow_le_pow_left₀ hR₀.le hbase n)
  have hsmall' := (le_div_iff₀ (pow_pos (mul_pos hB hD₀) n)).1
    (absZero n hn (allZero n hn))
  have hbig := (div_lt_iff₀ δpos).1 hlarge
  linarith [mul_comm |δ| ((B * D) ^ n)]

/-- Arithmetic normalization and the coefficient bounds from the real saddle. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ (M : ℝ) (U V : ℤ),
    0 < M ∧ M ≤ Real.exp ((5570 * 0.539995 : ℝ) * n) ∧
    M * contour n = (U : ℝ) + (V : ℝ) * Real.pi ∧
    Real.exp ((5570 * 3.87192 : ℝ) * n) ≤ |(V : ℝ)| ∧
    |(V : ℝ)| ≤ Real.exp ((5570 * 3.87195 : ℝ) * n)

/-- The decay estimate on the unnormalized integral. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, |contour n| ≤ 1 / Real.exp ((5570 * 1.174535 : ℝ) * n)

theorem main : H1 → H2 → type_of% @Constant7a.c7a_upper_bound := by
  intro arithmetic decay
  rw [H1, eventually_atTop] at arithmetic
  rw [H2, eventually_atTop] at decay
  obtain ⟨n₁, har⟩ := arithmetic
  obtain ⟨n₂, hdec⟩ := decay
  let n₀ := max n₁ n₂
  have pointwise (n : ℕ) : ∃ U V : ℤ, n₀ ≤ n →
      Real.exp ((5570 * 3.87192 : ℝ) * n) ≤ |(V : ℝ)| ∧
      |(V : ℝ)| ≤ Real.exp ((5570 * 3.87195 : ℝ) * n) ∧
      |(U : ℝ) + (V : ℝ) * Real.pi| ≤ 1 / Real.exp ((5570 * 0.63454 : ℝ) * n) := by
    by_cases hn : n₀ ≤ n
    · obtain ⟨M, U, V, hpos, hm, heq, hv₁, hv₂⟩ :=
        har n ((le_max_left n₁ n₂).trans hn)
      refine ⟨U, V, fun _ ↦ ⟨hv₁, hv₂, ?_⟩⟩
      calc |(U : ℝ) + (V : ℝ) * Real.pi| = M * |contour n| := by
            rw [← heq, abs_mul, abs_of_pos hpos]
        _ ≤ Real.exp ((5570 * 0.539995 : ℝ) * n) *
            (1 / Real.exp ((5570 * 1.174535 : ℝ) * n)) :=
          mul_le_mul hm (hdec n ((le_max_right n₁ n₂).trans hn)) (abs_nonneg _)
            (Real.exp_pos _).le
        _ = 1 / Real.exp ((5570 * 0.63454 : ℝ) * n) := by
          rw [mul_one_div, ← Real.exp_sub, one_div, ← Real.exp_neg]
          congr 1
          ring
    · exact ⟨0, 0, fun h ↦ (hn h).elim⟩
  choose U V bounds using pointwise
  let A := Real.exp (5570 * 3.87195)
  let B := Real.exp (5570 * 3.87192)
  let D := Real.exp (5570 * 0.63454)
  let R := Real.exp (5570 * 0.63450)
  have hA : 1 ≤ A := by
    dsimp [A]
    rw [← Real.exp_zero, Real.exp_le_exp]
    norm_num
  have hB : 0 < B := Real.exp_pos _
  have hR : 1 < R := by
    dsimp [R]
    rw [← Real.exp_zero, Real.exp_lt_exp]
    norm_num
  have hRD : R ≤ D := by
    dsimp [R, D]
    rw [Real.exp_le_exp]
    norm_num
  have hAB : A * R ≤ B * D := by
    dsimp [A, B, R, D]
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    norm_num
  have hAk : A ≤ R ^ (6.103 : ℝ) := by
    dsimp [A, R]
    rw [← Real.exp_mul, Real.exp_le_exp]
    norm_num
  have forms : ∀ n ≥ n₀, B ^ n ≤ |(V n : ℝ)| ∧ |(V n : ℝ)| ≤ A ^ n ∧
      |(U n : ℝ) + (V n : ℝ) * Real.pi| ≤ 1 / D ^ n := by
    intro n hn
    have expPow (r : ℝ) : Real.exp (r * (n : ℝ)) = Real.exp r ^ n := by
      rw [Real.exp_mul, Real.rpow_natCast]
    simpa only [expPow] using bounds n hn

  have h : Constant7a.C7a ≤ ((7.103 : NNReal) : ENNReal) := by
    unfold Constant7a.C7a Constant7a.irrationalityExponent
    rw [sSup_le_iff]
    rintro _ ⟨p, hp, rfl⟩
    by_contra! hgt
    have hp' : (6.103 : ℝ) + 1 < (p : ℝ) := by
      have hnn : (7.103 : NNReal) < p := ENNReal.coe_lt_coe.mp hgt
      have hreal : ((7.103 : NNReal) : ℝ) < (p : ℝ) := hnn
      norm_num at hreal ⊢
      linarith
    exact not_liouville_of_forms (by norm_num) hp' hA hB hR hRD hAB hAk forms hp
  apply h.trans_lt
  change ((7.103 : NNReal) : ENNReal) < ((7.103205334138 : NNReal) : ENNReal)
  exact ENNReal.coe_lt_coe.mpr (by norm_num)

end OMA.R_Constant7a_c7a_upper_bound_R1
