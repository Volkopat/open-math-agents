import OMAStatements.S_oeis_a326097
import Mathlib

namespace OMA.S_oeis_a326097

private noncomputable def egf (f : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (f n : ℚ) / (Nat.factorial n : ℚ))

private def hmul (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f k * g (n - k)

private lemma egf_mul (f g : ℕ → ℤ) : egf f * egf g = egf (hmul f g) := by
  ext n
  simp only [egf, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j =>
      ((f i : ℚ) / (Nat.factorial i : ℚ)) * ((g j : ℚ) / (Nat.factorial j : ℚ))) n]
  simp only [hmul, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hch : (Nat.choose n k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ) =
      (Nat.factorial n : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hfnk : (Nat.factorial (n - k) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hfk, hfnk, hfn]
  rw [← hch]; ring

private lemma egf_sub (f g : ℕ → ℤ) : egf f - egf g = egf (fun n => f n - g n) := by
  ext n
  simp only [egf, map_sub, PowerSeries.coeff_mk, Int.cast_sub, sub_div]

private lemma egf_deriv (f : ℕ → ℤ) :
    PowerSeries.derivative ℚ (egf f) = egf (fun n => f (n + 1)) := by
  ext n
  simp only [egf, PowerSeries.coeff_derivative, PowerSeries.coeff_mk, Nat.factorial_succ,
    Nat.cast_mul]
  have h1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have h2 : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [h1, h2]
  push_cast; ring

private lemma egf_one_add_X_pow (n : ℕ) :
    (1 + PowerSeries.X : PowerSeries ℚ) ^ n =
    egf (fun k => (Nat.factorial k * Nat.choose n k : ℤ)) := by
  ext k
  have hpoly : ((1 + PowerSeries.X : PowerSeries ℚ) ^ n) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ n : Polynomial ℚ) : PowerSeries ℚ) := by
    simp
  rw [hpoly, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  simp only [egf, PowerSeries.coeff_mk]
  have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  push_cast
  field_simp [hfk]

private def hdivpow (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 0
  | m + 1, n + 1 =>
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) * hdivpow f m (n - k)

private lemma egf_hdivpow (f : ℕ → ℤ) (hf0 : f 0 = 0) :
    ∀ m : ℕ, (1 / (Nat.factorial m : ℚ)) • (egf f) ^ m = egf (hdivpow f m) := by
  intro m
  induction m with
  | zero =>
    ext n
    simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_smul, egf,
      PowerSeries.coeff_one, PowerSeries.coeff_mk, hdivpow]
    split_ifs with h <;> simp [h]
  | succ m ih =>
    ext n
    cases n with
    | zero =>
      simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_zero_eq_constantCoeff,
        map_pow, egf, PowerSeries.constantCoeff_mk, hf0, Int.cast_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, zero_pow (Nat.succ_ne_zero m), mul_zero, hdivpow]
    | succ n =>
      have hderiv : PowerSeries.derivative ℚ ((1 / (Nat.factorial (m + 1) : ℚ)) • (egf f) ^ (m + 1)) =
          egf (hmul (fun k => f (k + 1)) (hdivpow f m)) := by
        have hsmul : ∀ (c : ℚ) (F : PowerSeries ℚ),
            PowerSeries.derivative ℚ (c • F) = c • PowerSeries.derivative ℚ F := by
          intro c F; ext k
          simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_smul, smul_eq_mul]; ring
        rw [hsmul, PowerSeries.derivative_pow, Nat.add_sub_cancel, ← smul_mul_assoc]
        have hsc : (1 / (Nat.factorial (m + 1) : ℚ)) • (((m + 1 : ℕ) : PowerSeries ℚ) * (egf f) ^ m) =
            (1 / (Nat.factorial m : ℚ)) • (egf f) ^ m := by
          ext k
          rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, ← nsmul_eq_mul, map_nsmul]
          simp only [smul_eq_mul, nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul]
          have h1 : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
          have h2 : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
          field_simp [h1, h2]
        rw [hsc, ih, egf_deriv, egf_mul,
          show hmul (hdivpow f m) (fun k => f (k + 1)) = hmul (fun k => f (k + 1)) (hdivpow f m) from by
            funext r
            have := congr_arg (PowerSeries.coeff r) (mul_comm (egf (hdivpow f m)) (egf (fun k => f (k + 1))))
            rw [egf_mul, egf_mul] at this
            simp only [egf, PowerSeries.coeff_mk] at this
            have hfr : (Nat.factorial r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
            have hq : (hmul (hdivpow f m) (fun k => f (k + 1)) r : ℚ) =
                (hmul (fun k => f (k + 1)) (hdivpow f m) r : ℚ) := by
              exact (div_left_inj' hfr).mp this
            exact_mod_cast hq]
      have hc := congr_arg (PowerSeries.coeff n) hderiv
      rw [PowerSeries.coeff_derivative] at hc
      simp only [egf, PowerSeries.coeff_mk, hmul] at hc
      simp only [egf, PowerSeries.coeff_mk, hdivpow]
      rw [Nat.factorial_succ n, Nat.cast_mul]
      have h1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      have h2 : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hcast : ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [hcast] at hc
      have hc' : PowerSeries.coeff (n + 1) ((1 / (Nat.factorial (m + 1) : ℚ)) •
            (PowerSeries.mk fun n => (f n : ℚ) / (Nat.factorial n : ℚ)) ^ (m + 1)) =
          ((∑ x ∈ Finset.range (n + 1), (Nat.choose n x : ℤ) * f (x + 1) * hdivpow f m (n - x) : ℤ) : ℚ) /
            (((n + 1 : ℕ) : ℚ) * (Nat.factorial n : ℚ)) := by
        rw [eq_div_iff (mul_ne_zero h1 h2), ← mul_assoc, hc, div_mul_cancel₀ _ h2]
      exact hc'

private lemma hdivpow_eq_zero_of_lt (f : ℕ → ℤ) : ∀ m n : ℕ, n < m → hdivpow f m n = 0 := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ n =>
      simp only [hdivpow]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [ih (n - k) (by omega), mul_zero]

private lemma hdivpow_one (f : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) : hdivpow f 1 n = f n := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [hdivpow]
    rw [Finset.sum_eq_single n]
    · simp
    · intro k hk hkne
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have : n - k ≠ 0 := by omega
      simp [this]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h

private lemma hdivpow_congr_mod2 {f1 f2 : ℕ → ℤ} (h : ∀ k, f1 k % 2 = f2 k % 2) :
    ∀ m n : ℕ, hdivpow f1 m n % 2 = hdivpow f2 m n % 2 := by
  intro m
  induction m with
  | zero => intro n; simp [hdivpow]
  | succ m ih =>
    intro n
    cases n with
    | zero => simp [hdivpow]
    | succ n =>
      simp only [hdivpow]
      rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ), h (k + 1), ih (n - k)]
      conv_rhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ)]

private lemma hdivpow_depends_below {f1 f2 : ℕ → ℤ} :
    ∀ m n : ℕ, 2 ≤ m → (∀ j < n, f1 j % 2 = f2 j % 2) →
      hdivpow f1 m n % 2 = hdivpow f2 m n % 2 := by
  intro m
  induction m with
  | zero => intro n hm; omega
  | succ m ih =>
    intro n hm hbelow
    cases n with
    | zero => simp [hdivpow]
    | succ n =>
      simp only [hdivpow]
      rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hkn_eq : k = n
      · subst hkn_eq
        have h0 : hdivpow f1 m 0 = 0 := by cases m <;> [omega; rfl]
        have h0' : hdivpow f2 m 0 = 0 := by cases m <;> [omega; rfl]
        simp [h0, h0']
      · have h1 : f1 (k + 1) % 2 = f2 (k + 1) % 2 := hbelow (k + 1) (by omega)
        have h2 : hdivpow f1 m (n - k) % 2 = hdivpow f2 m (n - k) % 2 := by
          by_cases hm1 : m = 1
          · subst hm1
            rw [hdivpow_one f1 (n - k) (by omega), hdivpow_one f2 (n - k) (by omega)]
            exact hbelow (n - k) (by omega)
          · exact ih (n - k) (by omega) (fun j hj => hbelow j (by omega))
        conv_lhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ), h1, h2]
        conv_rhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ)]

private def hcosh (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), if Even m then hdivpow f m n else 0

private def hsinh (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), if Odd m then hdivpow f m n else 0

private lemma hcosh_zero (f : ℕ → ℤ) : hcosh f 0 = 1 := by
  simp [hcosh, hdivpow]

private lemma hsinh_zero (f : ℕ → ℤ) : hsinh f 0 = 0 := by
  simp [hsinh]

private lemma hcosh_succ (f : ℕ → ℤ) (n : ℕ) :
    hcosh f (n + 1) = hmul (fun k => f (k + 1)) (hsinh f) n := by
  simp only [hcosh, hmul, hsinh]
  rw [Finset.sum_range_succ']
  simp only [hdivpow, Nat.succ_ne_zero, ↓reduceIte, ite_self, add_zero]
  have hswap :
      (∑ m ∈ Finset.range (n + 1),
        if Even (m + 1) then
          ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) * hdivpow f m (n - k)
        else 0) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) *
        ∑ m ∈ Finset.range (n + 1), if Odd m then hdivpow f m (n - k) else 0 := by
    have h1 : ∀ m, (if Even (m + 1) then
          ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) * hdivpow f m (n - k)
        else 0) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℤ) * f (k + 1) * (if Odd m then hdivpow f m (n - k) else 0) := by
      intro m
      have hev : Even (m + 1) ↔ Odd m := Nat.even_add_one.trans (by simp [Nat.not_even_iff_odd])
      by_cases ho : Odd m
      · simp [hev.mpr ho, ho]
      · simp [mt hev.mp ho, ho]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  congr 1
  symm
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => ?_
  simp only [Finset.mem_range, not_lt] at hm
  split_ifs
  · exact hdivpow_eq_zero_of_lt f m (n - k) (by omega)
  · rfl

private lemma hsinh_succ (f : ℕ → ℤ) (n : ℕ) :
    hsinh f (n + 1) = hmul (fun k => f (k + 1)) (hcosh f) n := by
  simp only [hsinh, hmul, hcosh]
  rw [Finset.sum_range_succ']
  simp only [Nat.not_odd_zero, ↓reduceIte, add_zero, hdivpow]
  have hswap :
      (∑ m ∈ Finset.range (n + 1),
        if Odd (m + 1) then
          ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) * hdivpow f m (n - k)
        else 0) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) *
        ∑ m ∈ Finset.range (n + 1), if Even m then hdivpow f m (n - k) else 0 := by
    have h1 : ∀ m, (if Odd (m + 1) then
          ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) * hdivpow f m (n - k)
        else 0) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℤ) * f (k + 1) * (if Even m then hdivpow f m (n - k) else 0) := by
      intro m
      have hod : Odd (m + 1) ↔ Even m := by
        rw [Nat.odd_add_one, Nat.not_odd_iff_even]
      by_cases he : Even m
      · simp [hod.mpr he, he]
      · simp [mt hod.mp he, he]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  congr 1
  symm
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => ?_
  simp only [Finset.mem_range, not_lt] at hm
  split_ifs
  · exact hdivpow_eq_zero_of_lt f m (n - k) (by omega)
  · rfl

-- Mod 4 binomial sum vanishing for n >= 4
private lemma sum_choose_mod4_even :
    ∀ n : ℕ, 4 ≤ n → ∀ r : ℕ,
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 4 = r), (Nat.choose n k : ℤ)) % 2 = 0 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    intro r
    by_cases hn4 : n < 4
    · have hneq : n = 3 := by omega
      subst hneq
      rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | rfl | rfl | hr
      · decide
      · decide
      · decide
      · decide
      · have hemp : (Finset.range 5).filter (fun k => k % 4 = r) = ∅ := by
          ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
          omega
        simp [hemp]
    · have hge4 : 4 ≤ n := by omega
      by_cases hr4 : 4 ≤ r
      · have hemp : (Finset.range (n + 2)).filter (fun k => k % 4 = r) = ∅ := by
          ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
          omega
        simp [hemp]
      · have hsplit :
            (∑ k ∈ (Finset.range (n + 2)).filter (fun k => k % 4 = r), (Nat.choose (n + 1) k : ℤ)) =
            (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 4 = r), (Nat.choose n k : ℤ)) +
            (∑ j ∈ (Finset.range (n + 1)).filter (fun j => j % 4 = (r + 3) % 4), (Nat.choose n j : ℤ)) := by
          clear ih
          have hL : (∑ k ∈ Finset.range (n + 2),
                if k % 4 = r then (Nat.choose (n + 1) k : ℤ) else 0) =
              (if 0 % 4 = r then (1 : ℤ) else 0) +
              ∑ j ∈ Finset.range (n + 1),
                if (j + 1) % 4 = r then ((Nat.choose n j : ℤ) + (Nat.choose n (j + 1) : ℤ)) else 0 := by
            rw [Finset.sum_range_succ', add_comm]
            simp only [Nat.choose_zero_right, Nat.cast_one]
            congr 1
          have hR1 : (∑ k ∈ Finset.range (n + 1), if k % 4 = r then (Nat.choose n k : ℤ) else 0) =
              (if 0 % 4 = r then (1 : ℤ) else 0) +
              ∑ j ∈ Finset.range (n + 1),
                if (j + 1) % 4 = r then (Nat.choose n (j + 1) : ℤ) else 0 := by
            rw [Finset.sum_range_succ' (n := n), add_comm]
            simp only [Nat.choose_zero_right, Nat.cast_one]
            congr 1
            rw [Finset.sum_range_succ]; simp
          have hR2 : (∑ j ∈ Finset.range (n + 1),
                if j % 4 = (r + 3) % 4 then (Nat.choose n j : ℤ) else 0) =
              ∑ j ∈ Finset.range (n + 1),
                if (j + 1) % 4 = r then (Nat.choose n j : ℤ) else 0 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have : (j % 4 = (r + 3) % 4) ↔ ((j + 1) % 4 = r) := by omega
            simp [this]
          simp only [Finset.sum_filter]
          rw [hL, hR1, hR2]
          have hadd : (∑ j ∈ Finset.range (n + 1),
                if (j + 1) % 4 = r then ((Nat.choose n j : ℤ) + (Nat.choose n (j + 1) : ℤ)) else 0) =
              (∑ j ∈ Finset.range (n + 1),
                if (j + 1) % 4 = r then (Nat.choose n j : ℤ) else 0) +
              (∑ j ∈ Finset.range (n + 1),
                if (j + 1) % 4 = r then (Nat.choose n (j + 1) : ℤ) else 0) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
          rw [hadd]; ring
        rw [hsplit, Int.add_emod, ih hge4 r, ih hge4 ((r + 3) % 4)]
        norm_num

private def ind4 (r : ℕ) (k : ℕ) : ℤ := if k % 4 = r then 1 else 0
private def delta (c : ℕ) (k : ℕ) : ℤ := if k = c then 1 else 0

private lemma hmul_ind4_ind4_even (r s : ℕ) (_hr : r < 4) (hs : s < 4) (n : ℕ) (hn : 4 ≤ n) :
    hmul (ind4 r) (ind4 s) n % 2 = 0 := by
  simp only [hmul, ind4]
  by_cases hmod : (r + s) % 4 = n % 4
  · have heq : (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℤ) * (if k % 4 = r then 1 else 0) * (if (n - k) % 4 = s then 1 else 0)) =
        ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 4 = r), (Nat.choose n k : ℤ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hkr : k % 4 = r
      · have hnk : (n - k) % 4 = s := by omega
        simp [hkr, hnk]
      · simp [hkr]
    rw [heq]
    exact sum_choose_mod4_even n hn r
  · have hzero : (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℤ) * (if k % 4 = r then 1 else 0) * (if (n - k) % 4 = s then 1 else 0)) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hkr : k % 4 = r
      · have hnk : (n - k) % 4 ≠ s := by omega
        simp [hkr, hnk]
      · simp [hkr]
    rw [hzero]; norm_num

private lemma hmul_delta_left (c : ℕ) (f : ℕ → ℤ) (n : ℕ) (hcn : c ≤ n) :
    hmul (delta c) f n = (Nat.choose n c : ℤ) * f (n - c) := by
  simp only [hmul, delta]
  rw [Finset.sum_eq_single c]
  · simp
  · intro k _ hkc; simp [hkc]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma hmul_delta_right (f : ℕ → ℤ) (c : ℕ) (n : ℕ) (hcn : c ≤ n) :
    hmul f (delta c) n = (Nat.choose n c : ℤ) * f (n - c) := by
  simp only [hmul, delta]
  rw [Finset.sum_eq_single (n - c)]
  · simp only [show n - (n - c) = c by omega, ↓reduceIte, mul_one]
    rw [Nat.choose_symm hcn]
  · intro k hk hkne
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : n - k ≠ c := by omega
    simp [this]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma hmul_add_left (f1 f2 g : ℕ → ℤ) (n : ℕ) :
    hmul (fun k => f1 k + f2 k) g n = hmul f1 g n + hmul f2 g n := by
  simp only [hmul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma hmul_add_right (f g1 g2 : ℕ → ℤ) (n : ℕ) :
    hmul f (fun k => g1 k + g2 k) n = hmul f g1 n + hmul f g2 n := by
  simp only [hmul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma hmul_congr_mod2 {f1 f2 g1 g2 : ℕ → ℤ} (hf : ∀ k, f1 k % 2 = f2 k % 2)
    (hg : ∀ k, g1 k % 2 = g2 k % 2) (n : ℕ) :
    hmul f1 g1 n % 2 = hmul f2 g2 n % 2 := by
  simp only [hmul]
  rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_lhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ), hf k, hg (n - k)]
  conv_rhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ)]

private lemma choose_two_mod2 (n : ℕ) :
    (Nat.choose n 2 : ℤ) % 2 = if n % 4 = 2 ∨ n % 4 = 3 then 1 else 0 := by
  rw [Nat.choose_two_right]
  have h : n * (n - 1) / 2 % 2 = if n % 4 = 2 ∨ n % 4 = 3 then 1 else 0 := by
    have hq : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
    set q := n / 4
    set r := n % 4
    have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr with hr0 | hr1 | hr2 | hr3
    · have hn0 : n = 4 * q := by omega
      rw [hn0, hr0]
      cases q with
      | zero => decide
      | succ q =>
        have h1 : 4 * (q + 1) - 1 = 4 * q + 3 := by omega
        have h2 : 4 * (q + 1) * (4 * q + 3) = 2 * (2 * ((q + 1) * (4 * q + 3))) := by ring
        rw [h1, h2, Nat.mul_div_cancel_left _ (by omega)]; simp
    · have hn1 : n = 4 * q + 1 := by omega
      rw [hn1, hr1]
      have h1 : 4 * q + 1 - 1 = 4 * q := by omega
      have h2 : (4 * q + 1) * (4 * q) = 2 * (2 * ((4 * q + 1) * q)) := by ring
      rw [h1, h2, Nat.mul_div_cancel_left _ (by omega)]; simp
    · have hn2 : n = 4 * q + 2 := by omega
      rw [hn2, hr2]
      have h1 : 4 * q + 2 - 1 = 4 * q + 1 := by omega
      have h2 : (4 * q + 2) * (4 * q + 1) = 2 * (2 * (4 * q * q + 3 * q) + 1) := by ring
      rw [h1, h2, Nat.mul_div_cancel_left _ (by omega)]; simp
    · have hn3 : n = 4 * q + 3 := by omega
      rw [hn3, hr3]
      have h1 : 4 * q + 3 - 1 = 4 * q + 2 := by omega
      have h2 : (4 * q + 3) * (4 * q + 2) = 2 * (2 * (4 * q * q + 5 * q + 1) + 1) := by ring
      rw [h1, h2, Nat.mul_div_cancel_left _ (by omega)]; simp
  have hcast : ((n * (n - 1) / 2 : ℕ) : ℤ) % 2 = ((n * (n - 1) / 2 % 2 : ℕ) : ℤ) := by omega
  rw [hcast, h]
  split_ifs <;> rfl

-- Explicit mod 2 solution g0, g0x, cg0, sg0, cg0x, sg0x
private def g0 (n : ℕ) : ℤ := if n = 1 ∨ n = 3 ∨ n % 4 = 2 then 1 else 0
private def g0x (n : ℕ) : ℤ := if n = 3 ∨ n % 4 = 2 then 1 else 0
private def cg0 (n : ℕ) : ℤ := if n = 0 ∨ n = 2 ∨ n % 4 = 3 then 1 else 0
private def sg0 (n : ℕ) : ℤ := if n = 1 ∨ n % 4 = 2 then 1 else 0
private def cg0x (n : ℕ) : ℤ := if n % 4 = 0 then 1 else 0
private def sg0x (n : ℕ) : ℤ := if n = 2 ∨ n % 4 = 3 then 1 else 0

private lemma hmul_delta_delta (a b n : ℕ) (h : a + b < n) :
    hmul (delta a) (delta b) n = 0 := by
  rw [hmul_delta_left a (delta b) n (by omega)]
  simp [delta, show n - a ≠ b by omega]

private lemma hmul_delta2_delta2_even (n : ℕ) (hn : 4 ≤ n) :
    hmul (delta 2) (delta 2) n % 2 = 0 := by
  rw [hmul_delta_left 2 (delta 2) n (by omega)]
  by_cases hn4 : n = 4
  · subst hn4; decide
  · simp [delta, show n - 2 ≠ 2 by omega]

private lemma hmul_g0_sg0 (n : ℕ) :
    hmul (fun k => g0 (k + 1)) sg0 n % 2 = cg0 (n + 1) % 2 := by
  by_cases hn4 : n < 4
  · interval_cases n <;> decide
  · have hge4 : 4 ≤ n := by omega
    have hf : ∀ k, g0 (k + 1) % 2 = (ind4 1 k + delta 0 k + delta 2 k) % 2 := by
      intro k; simp only [g0, ind4, delta]; split_ifs <;> omega
    have hg : ∀ k, sg0 k % 2 = (ind4 2 k + delta 1 k) % 2 := by
      intro k; simp only [sg0, ind4, delta]; split_ifs <;> omega
    rw [hmul_congr_mod2 hf hg n]
    simp only [hmul_add_left, hmul_add_right]
    rw [hmul_delta_delta 0 1 n (by omega), hmul_delta_delta 2 1 n (by omega),
      hmul_delta_left 0 _ n (by omega), hmul_delta_left 2 _ n (by omega),
      hmul_delta_right _ 1 n (by omega)]
    have h12 := hmul_ind4_ind4_even 1 2 (by omega) (by omega) n hge4
    have hc2 := choose_two_mod2 n
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.choose_one_right, Nat.sub_zero,
      add_zero, ind4, cg0]
    have hmod_c2 : ((Nat.choose n 2 : ℤ) * (if (n - 2) % 4 = 2 then 1 else 0)) % 2 =
        if (n % 4 = 2 ∨ n % 4 = 3) ∧ (n - 2) % 4 = 2 then 1 else 0 := by
      rw [Int.mul_emod, hc2]; split_ifs <;> omega
    have hmod_n : ((n : ℤ) * (if (n - 1) % 4 = 1 then 1 else 0)) % 2 =
        if n % 2 = 1 ∧ (n - 1) % 4 = 1 then 1 else 0 := by
      rw [Int.mul_emod]; split_ifs <;> omega
    have hsum_mod : ∀ a b c d : ℤ, ((a + b + c) + d) % 2 =
        ((a % 2 + b % 2) + (c % 2 + d % 2)) % 2 := fun _ _ _ _ => by omega
    rw [hsum_mod, h12, hmod_c2, hmod_n]
    have hmod_ite : ∀ p : Prop, [Decidable p] → (if p then (1 : ℤ) else 0) % 2 = if p then 1 else 0 :=
      fun p _ => by split_ifs <;> norm_num
    rw [hmod_ite, hmod_ite]
    obtain ⟨q, rfl | rfl | rfl | rfl⟩ :
        ∃ q, n = 4 * q ∨ n = 4 * q + 1 ∨ n = 4 * q + 2 ∨ n = 4 * q + 3 := ⟨n / 4, by omega⟩
    · have h1 : (4 * q) % 4 = 0 := by omega
      have h2 : (4 * q + 1) % 4 = 1 := by omega
      have h3 : (4 * q) % 2 = 0 := by omega
      have h4 : 4 * q + 1 ≠ 0 ∧ 4 * q + 1 ≠ 2 := by omega
      simp [h1, h2, h3, h4]
    · have h1 : (4 * q + 1) % 4 = 1 := by omega
      have h2 : (4 * q + 1 + 1) % 4 = 2 := by omega
      have h4 : 4 * q + 1 + 1 ≠ 0 ∧ 4 * q + 1 + 1 ≠ 2 := by omega
      simp [h1, h2, h4]
    · have h1 : (4 * q + 2) % 4 = 2 := by omega
      have h3 : (4 * q + 2) % 2 = 0 := by omega
      have h4 : (4 * q + 2 + 1) % 4 = 3 := by omega
      simp [h1, h3, h4]
    · have h1 : (4 * q + 3) % 4 = 3 := by omega
      have h4 : (4 * q + 3 + 1) % 4 = 0 := by omega
      have h5 : 4 * q + 3 + 1 ≠ 0 ∧ 4 * q + 3 + 1 ≠ 2 := by omega
      simp [h1, h4, h5]

private lemma hmul_g0_cg0 (n : ℕ) :
    hmul (fun k => g0 (k + 1)) cg0 n % 2 = sg0 (n + 1) % 2 := by
  by_cases hn4 : n < 4
  · interval_cases n <;> decide
  · have hge4 : 4 ≤ n := by omega
    have hf : ∀ k, g0 (k + 1) % 2 = (ind4 1 k + delta 0 k + delta 2 k) % 2 := by
      intro k; simp only [g0, ind4, delta]; split_ifs <;> omega
    have hg : ∀ k, cg0 k % 2 = (ind4 3 k + delta 0 k + delta 2 k) % 2 := by
      intro k; simp only [cg0, ind4, delta]; split_ifs <;> omega
    rw [hmul_congr_mod2 hf hg n]
    simp only [hmul_add_left, hmul_add_right]
    rw [hmul_delta_delta 0 0 n (by omega), hmul_delta_delta 2 0 n (by omega),
      hmul_delta_delta 0 2 n (by omega),
      hmul_delta_left 0 _ n (by omega), hmul_delta_left 2 _ n (by omega),
      hmul_delta_right _ 0 n (by omega), hmul_delta_right _ 2 n (by omega)]
    have h13 := hmul_ind4_ind4_even 1 3 (by omega) (by omega) n hge4
    have h22 := hmul_delta2_delta2_even n hge4
    have hc2 := choose_two_mod2 n
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, add_zero, ind4, sg0]
    have hmod_c2a : ((Nat.choose n 2 : ℤ) * (if (n - 2) % 4 = 3 then 1 else 0)) % 2 =
        if (n % 4 = 2 ∨ n % 4 = 3) ∧ (n - 2) % 4 = 3 then 1 else 0 := by
      rw [Int.mul_emod, hc2]; split_ifs <;> omega
    have hmod_c2b : ((Nat.choose n 2 : ℤ) * (if (n - 2) % 4 = 1 then 1 else 0)) % 2 =
        if (n % 4 = 2 ∨ n % 4 = 3) ∧ (n - 2) % 4 = 1 then 1 else 0 := by
      rw [Int.mul_emod, hc2]; split_ifs <;> omega
    have hsum_mod : ∀ a b c d e f : ℤ, ((a + b + c) + d + (e + f)) % 2 =
        ((a % 2 + b % 2) + (c % 2 + d % 2) + (e % 2 + f % 2)) % 2 := fun _ _ _ _ _ _ => by omega
    rw [hsum_mod, h13, h22, hmod_c2a, hmod_c2b]
    have hmod_ite : ∀ p : Prop, [Decidable p] → (if p then (1 : ℤ) else 0) % 2 = if p then 1 else 0 :=
      fun p _ => by split_ifs <;> norm_num
    rw [hmod_ite, hmod_ite, hmod_ite]
    split_ifs <;> omega

private lemma hmul_g0x_sg0x (n : ℕ) :
    hmul (fun k => g0x (k + 1)) sg0x n % 2 = cg0x (n + 1) % 2 := by
  by_cases hn4 : n < 4
  · interval_cases n <;> decide
  · have hge4 : 4 ≤ n := by omega
    have hf : ∀ k, g0x (k + 1) % 2 = (ind4 1 k + delta 2 k) % 2 := by
      intro k; simp only [g0x, ind4, delta]; split_ifs <;> omega
    have hg : ∀ k, sg0x k % 2 = (ind4 3 k + delta 2 k) % 2 := by
      intro k; simp only [sg0x, ind4, delta]; split_ifs <;> omega
    rw [hmul_congr_mod2 hf hg n]
    simp only [hmul_add_left, hmul_add_right]
    rw [hmul_delta_left 2 _ n (by omega), hmul_delta_right _ 2 n (by omega)]
    have h13 := hmul_ind4_ind4_even 1 3 (by omega) (by omega) n hge4
    have h22 := hmul_delta2_delta2_even n hge4
    have hc2 := choose_two_mod2 n
    simp only [ind4, cg0x]
    have hmod_c2a : ((Nat.choose n 2 : ℤ) * (if (n - 2) % 4 = 3 then 1 else 0)) % 2 =
        if (n % 4 = 2 ∨ n % 4 = 3) ∧ (n - 2) % 4 = 3 then 1 else 0 := by
      rw [Int.mul_emod, hc2]; split_ifs <;> omega
    have hmod_c2b : ((Nat.choose n 2 : ℤ) * (if (n - 2) % 4 = 1 then 1 else 0)) % 2 =
        if (n % 4 = 2 ∨ n % 4 = 3) ∧ (n - 2) % 4 = 1 then 1 else 0 := by
      rw [Int.mul_emod, hc2]; split_ifs <;> omega
    have hsum_mod : ∀ a b c d : ℤ, ((a + b) + (c + d)) % 2 =
        ((a % 2 + b % 2) + (c % 2 + d % 2)) % 2 := fun _ _ _ _ => by omega
    rw [hsum_mod, h13, h22, hmod_c2a, hmod_c2b]
    have hmod_ite : ∀ p : Prop, [Decidable p] → (if p then (1 : ℤ) else 0) % 2 = if p then 1 else 0 :=
      fun p _ => by split_ifs <;> norm_num
    rw [hmod_ite]
    split_ifs <;> omega

private lemma hmul_g0x_cg0x (n : ℕ) :
    hmul (fun k => g0x (k + 1)) cg0x n % 2 = sg0x (n + 1) % 2 := by
  by_cases hn4 : n < 4
  · interval_cases n <;> decide
  · have hge4 : 4 ≤ n := by omega
    have hf : ∀ k, g0x (k + 1) % 2 = (ind4 1 k + delta 2 k) % 2 := by
      intro k; simp only [g0x, ind4, delta]; split_ifs <;> omega
    have hg : ∀ k, cg0x k % 2 = ind4 0 k % 2 := by
      intro k; simp only [cg0x, ind4]
    rw [hmul_congr_mod2 hf hg n]
    simp only [hmul_add_left]
    rw [hmul_delta_left 2 _ n (by omega)]
    have h10 := hmul_ind4_ind4_even 1 0 (by omega) (by omega) n hge4
    have hc2 := choose_two_mod2 n
    simp only [ind4, sg0x]
    have hmod_c2 : ((Nat.choose n 2 : ℤ) * (if (n - 2) % 4 = 0 then 1 else 0)) % 2 =
        if (n % 4 = 2 ∨ n % 4 = 3) ∧ (n - 2) % 4 = 0 then 1 else 0 := by
      rw [Int.mul_emod, hc2]; split_ifs <;> omega
    rw [Int.add_emod, h10, hmod_c2]
    split_ifs <;> omega

private lemma hmul_congr_mod2_le {f1 f2 g1 g2 : ℕ → ℤ} (n : ℕ)
    (hf : ∀ k ≤ n, f1 k % 2 = f2 k % 2) (hg : ∀ k ≤ n, g1 k % 2 = g2 k % 2) :
    hmul f1 g1 n % 2 = hmul f2 g2 n % 2 := by
  simp only [hmul]
  rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  conv_lhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ), hf k hkn, hg (n - k) (by omega)]
  conv_rhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ)]

private lemma hcosh_hsinh_g0 :
    ∀ n : ℕ, hcosh g0 n % 2 = cg0 n % 2 ∧ hsinh g0 n % 2 = sg0 n % 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [hcosh_zero, hsinh_zero, cg0, sg0]
    | succ n =>
      constructor
      · rw [hcosh_succ,
          hmul_congr_mod2_le n (fun _ _ => rfl) (fun k hk => (ih k (by omega)).2)]
        exact hmul_g0_sg0 n
      · rw [hsinh_succ,
          hmul_congr_mod2_le n (fun _ _ => rfl) (fun k hk => (ih k (by omega)).1)]
        exact hmul_g0_cg0 n

private lemma hcosh_hsinh_g0x :
    ∀ n : ℕ, hcosh g0x n % 2 = cg0x n % 2 ∧ hsinh g0x n % 2 = sg0x n % 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [hcosh_zero, hsinh_zero, cg0x, sg0x]
    | succ n =>
      constructor
      · rw [hcosh_succ,
          hmul_congr_mod2_le n (fun _ _ => rfl) (fun k hk => (ih k (by omega)).2)]
        exact hmul_g0x_sg0x n
      · rw [hsinh_succ,
          hmul_congr_mod2_le n (fun _ _ => rfl) (fun k hk => (ih k (by omega)).1)]
        exact hmul_g0x_cg0x n

private lemma g0_eq_mod2 (k : ℕ) :
    (hcosh g0 k + hsinh g0x k) % 2 = (if k = 0 then 1 else 0) := by
  rw [Int.add_emod, (hcosh_hsinh_g0 k).1, (hcosh_hsinh_g0x k).2]
  simp only [cg0, sg0x]
  split_ifs <;> omega

private theorem main_proved :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      (∀ k : ℕ,
        let A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ))
        ∑ n ∈ Finset.range (k + 1),
          (1 / (Nat.factorial n : ℚ)) *
            PowerSeries.coeff k (((1 + PowerSeries.X) ^ n - A) ^ n) =
        if k = 0 then 1 else 0) →
      ∀ k : ℕ, 3 < k → (a k % 2 = 1 ↔ k % 4 = 2) := by
  intro a ha0 heq
  let g : ℕ → ℤ := fun k => if k = 0 then 0 else a k
  let gx : ℕ → ℤ := fun k => if k = 0 then 0 else if k = 1 then a 1 + 1 else a k
  have hsum_int : ∀ k : ℕ,
      (∑ n ∈ Finset.range (k + 1),
        hdivpow (fun j => (Nat.factorial j * Nat.choose n j : ℤ) - a j) n k) =
      if k = 0 then 1 else 0 := by
    intro k
    have hk := heq k
    have hterm : ∀ n : ℕ,
        (1 / (Nat.factorial n : ℚ)) *
          PowerSeries.coeff k (((1 + PowerSeries.X) ^ n - egf a) ^ n) =
        (hdivpow (fun j => (Nat.factorial j * Nat.choose n j : ℤ) - a j) n k : ℚ) /
          (Nat.factorial k : ℚ) := by
      intro n
      have hsub : (1 + PowerSeries.X : PowerSeries ℚ) ^ n - egf a =
          egf (fun j => (Nat.factorial j * Nat.choose n j : ℤ) - a j) := by
        rw [egf_one_add_X_pow, egf_sub]
      have h0 : ((Nat.factorial 0 * Nat.choose n 0 : ℤ) - a 0) = 0 := by
        simp [ha0]
      have hdp := congr_arg (PowerSeries.coeff k)
        (egf_hdivpow (fun j => (Nat.factorial j * Nat.choose n j : ℤ) - a j) h0 n)
      simp only [PowerSeries.coeff_smul, smul_eq_mul, egf, PowerSeries.coeff_mk] at hdp
      rw [hsub]
      exact hdp
    have hk' : (∑ n ∈ Finset.range (k + 1),
          (hdivpow (fun j => (Nat.factorial j * Nat.choose n j : ℤ) - a j) n k : ℚ)) /
        (Nat.factorial k : ℚ) = if k = 0 then 1 else 0 := by
      rw [Finset.sum_div]
      dsimp only [egf] at hterm
      simpa only [hterm] using hk
    have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hq : ((∑ n ∈ Finset.range (k + 1),
          hdivpow (fun j => (Nat.factorial j * Nat.choose n j : ℤ) - a j) n k : ℤ) : ℚ) =
        ((if k = 0 then (1 : ℤ) else 0 : ℤ) : ℚ) := by
      rw [Int.cast_sum]
      split_ifs at hk' ⊢ with hkz
      · subst hkz
        simp only [Nat.factorial_zero, Nat.cast_one, div_one] at hk'
        simpa using hk'
      · exact (div_eq_zero_iff.mp hk').resolve_right hfk
    exact_mod_cast hq
  have hmod2_eq : ∀ k : ℕ, (hcosh g k + hsinh gx k) % 2 = if k = 0 then 1 else 0 := by
    intro k
    have hsum := hsum_int k
    have hmod_term : ∀ n : ℕ,
        hdivpow (fun j => (Nat.factorial j * Nat.choose n j : ℤ) - a j) n k % 2 =
        (if Even n then hdivpow g n k else hdivpow gx n k) % 2 := by
      intro n
      by_cases hev : Even n
      · simp only [hev, ↓reduceIte]
        refine hdivpow_congr_mod2 (fun j => ?_) n k
        rcases j with _ | _ | j
        · simp [g, ha0]
        · obtain ⟨m, rfl⟩ := hev
          change ((Nat.factorial 1 * Nat.choose (m + m) 1 : ℤ) - a 1) % 2 = g 1 % 2
          simp only [g, Nat.factorial_one, Nat.choose_one_right,
            Nat.cast_one, one_mul, Nat.cast_add]
          omega
        · simp only [g, Nat.succ_ne_zero, ↓reduceIte]
          have h2dvd : 2 ∣ Nat.factorial (j + 2) :=
            Nat.dvd_factorial (by omega) (by omega)
          obtain ⟨q, hq⟩ := h2dvd
          have h2eq : ((Nat.factorial (j + 2) * Nat.choose n (j + 2) : ℤ)) =
              2 * ((q * Nat.choose n (j + 2) : ℕ) : ℤ) := by
            push_cast [hq]; ring
          rw [h2eq]; omega
      · simp only [hev, ↓reduceIte]
        have hodd : Odd n := Nat.not_even_iff_odd.mp hev
        refine hdivpow_congr_mod2 (fun j => ?_) n k
        rcases j with _ | _ | j
        · simp [gx, ha0]
        · obtain ⟨m, rfl⟩ := hodd
          change ((Nat.factorial 1 * Nat.choose (2 * m + 1) 1 : ℤ) - a 1) % 2 = gx 1 % 2
          simp only [gx, ↓reduceIte, Nat.factorial_one, Nat.choose_one_right,
            Nat.cast_one, one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          omega
        · simp only [gx, Nat.succ_ne_zero, show j + 2 ≠ 1 by omega, ↓reduceIte]
          have h2dvd : 2 ∣ Nat.factorial (j + 2) :=
            Nat.dvd_factorial (by omega) (by omega)
          obtain ⟨q, hq⟩ := h2dvd
          have h2eq : ((Nat.factorial (j + 2) * Nat.choose n (j + 2) : ℤ)) =
              2 * ((q * Nat.choose n (j + 2) : ℕ) : ℤ) := by
            push_cast [hq]; ring
          rw [h2eq]; omega
    have hcs : hcosh g k + hsinh gx k =
        ∑ n ∈ Finset.range (k + 1), if Even n then hdivpow g n k else hdivpow gx n k := by
      simp only [hcosh, hsinh, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hev : Even n
      · simp [hev, Nat.not_odd_iff_even.mpr hev]
      · simp [hev, Nat.not_even_iff_odd.mp hev]
    rw [hcs, Finset.sum_int_mod]
    have hcongr : (∑ n ∈ Finset.range (k + 1),
          (if Even n then hdivpow g n k else hdivpow gx n k) % 2) =
        ∑ n ∈ Finset.range (k + 1),
          hdivpow (fun j => (Nat.factorial j * Nat.choose n j : ℤ) - a j) n k % 2 := by
      refine Finset.sum_congr rfl fun n _ => (hmod_term n).symm
    rw [hcongr, ← Finset.sum_int_mod, hsum]
    split_ifs <;> norm_num
  have hg_eq : ∀ k : ℕ, g k % 2 = g0 k % 2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => simp [g, g0]
      | succ k =>
        have h1 := hmod2_eq (k + 1)
        have h2 := g0_eq_mod2 (k + 1)
        simp only [Nat.succ_ne_zero, ↓reduceIte] at h1 h2
        have hgx_below : ∀ j < k + 1, gx j % 2 = g0x j % 2 := by
          intro j hj
          have hgj := ih j hj
          by_cases hj0 : j = 0
          · subst hj0; simp [gx, g0x]
          · by_cases hj1 : j = 1
            · subst hj1; simp [g, gx, g0, g0x] at hgj ⊢; omega
            · simp only [g, gx, g0, g0x, hj0, hj1, ↓reduceIte] at hgj ⊢
              have : (j = 1 ∨ j = 3 ∨ j % 4 = 2) ↔ (j = 3 ∨ j % 4 = 2) := by omega
              simpa [this] using hgj
        have hcosh_eq : hcosh g (k + 1) % 2 = hcosh g0 (k + 1) % 2 := by
          simp only [hcosh]
          rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
          congr 1
          refine Finset.sum_congr rfl fun m _ => ?_
          by_cases hev : Even m
          · simp only [hev, ↓reduceIte]
            by_cases hm0 : m = 0
            · subst hm0; simp [hdivpow]
            · exact hdivpow_depends_below m (k + 1) (by
                obtain ⟨r, rfl⟩ := hev; omega) ih
          · simp [hev]
        have hsinh_split : ∀ f : ℕ → ℤ,
            hsinh f (k + 1) = f (k + 1) +
              ∑ m ∈ (Finset.range (k + 2)).filter (fun m => Odd m ∧ 3 ≤ m), hdivpow f m (k + 1) := by
          intro f
          simp only [hsinh]
          have h1_mem : 1 ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
          rw [← Finset.add_sum_erase _ _ h1_mem]
          simp only [odd_one, ↓reduceIte, hdivpow_one f (k + 1) (by omega)]
          congr 1
          rw [Finset.sum_filter]
          refine Finset.sum_bij_ne_zero (fun m _ _ => m) ?_ ?_ ?_ ?_
          · intro m hm _; exact Finset.mem_of_mem_erase hm
          · intro _ _ _ _ _ _ h; exact h
          · intro m hm hne
            have hm1 : m ≠ 1 := by
              intro h; subst h; simp at hne
            exact ⟨m, Finset.mem_erase.mpr ⟨hm1, hm⟩, by
              simp only [ite_ne_right_iff] at hne
              simp [hne.1.1, hne.2], rfl⟩
          · intro m hm hne
            have hm1 : m ≠ 1 := (Finset.mem_erase.mp hm).1
            by_cases ho : Odd m
            · have hm3 : 3 ≤ m := by obtain ⟨r, rfl⟩ := ho; omega
              simp [ho, hm3]
            · simp [ho] at hne
        have htail_eq :
            (∑ m ∈ (Finset.range (k + 2)).filter (fun m => Odd m ∧ 3 ≤ m), hdivpow gx m (k + 1)) % 2 =
            (∑ m ∈ (Finset.range (k + 2)).filter (fun m => Odd m ∧ 3 ≤ m), hdivpow g0x m (k + 1)) % 2 := by
          rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
          congr 1
          refine Finset.sum_congr rfl fun m hm => ?_
          have hm3 : 3 ≤ m := (Finset.mem_filter.mp hm).2.2
          exact hdivpow_depends_below m (k + 1) (by omega) hgx_below
        rw [hsinh_split gx] at h1
        rw [hsinh_split g0x] at h2
        have hgx_eq : gx (k + 1) % 2 = g0x (k + 1) % 2 := by
          have h3 : ∀ x y z : ℤ, (x + (y + z)) % 2 = (x % 2 + y % 2 + z % 2) % 2 :=
            fun _ _ _ => by omega
          rw [h3] at h1 h2
          rw [hcosh_eq, htail_eq] at h1
          omega
        by_cases hk0 : k = 0
        · subst hk0
          simp [g, gx, g0, g0x] at hgx_eq ⊢
          omega
        · simp only [g, gx, g0, g0x, Nat.succ_ne_zero, ↓reduceIte] at hgx_eq ⊢
          have hk1 : k + 1 ≠ 1 := by omega
          simp only [hk1, ↓reduceIte, false_or] at hgx_eq ⊢
          exact hgx_eq
  intro k hk
  have hgk := hg_eq k
  simp only [g, g0, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 3 by omega,
    ↓reduceIte, false_or] at hgk
  split_ifs at hgk with hmod
  · simp [hgk, hmod]
  · simp [hgk, hmod]

end OMA.S_oeis_a326097

theorem OMA.solution : type_of% @OMA.S_oeis_a326097.main :=
  OMA.S_oeis_a326097.main_proved
