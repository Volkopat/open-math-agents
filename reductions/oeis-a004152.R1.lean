import OMAStatements.S_oeis_a004152

namespace OMA.R_oeis_a004152_R1

open Filter Asymptotics Real
open OMA.S_oeis_a004152 (a c₁)

private theorem digit_length_bounds {b m : ℕ} (hb : 1 < b) (hm : 0 < m) :
    log (m : ℝ) / log (b : ℝ) ≤ ((Nat.digits b m).length : ℝ) ∧
    ((Nat.digits b m).length : ℝ) ≤ log (m : ℝ) / log (b : ℝ) + 1 := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hbLog : 0 < log (b : ℝ) := log_pos hbR
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hPow₁ : (b : ℝ) ^ Nat.log b m ≤ (m : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self b hm.ne'
  have hPow₂ : (m : ℝ) ≤ (b : ℝ) ^ (Nat.log b m + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self hb m).le
  have h₁ := Real.log_le_log (pow_pos (zero_lt_one.trans hbR) _) hPow₁
  have h₂ := Real.log_le_log hmR hPow₂
  rw [Real.log_pow] at h₁ h₂
  rw [Nat.length_digits b m hb hm.ne', Nat.cast_add, Nat.cast_one]
  constructor
  · exact (div_le_iff₀ hbLog).mpr (by simpa only [Nat.cast_add, Nat.cast_one] using h₂)
  · have h := (le_div_iff₀ hbLog).mpr h₁
    linarith only [h]

private theorem stirling_error {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ log (n.factorial : ℝ) - ((n : ℝ) * log (n : ℝ) - n) ∧
    log (n.factorial : ℝ) - ((n : ℝ) * log (n : ℝ) - n) ≤ 1 + log (n : ℝ) / 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := (zero_lt_one.trans_le hnR).ne'
  have hLog := Real.log_nonneg hnR
  have hFormula := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0,
    Real.log_div hn0 (Real.exp_ne_zero _), Real.log_exp, mul_sub, mul_one] at hFormula
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hLower := Stirling.log_stirlingSeq_bounded_by_constant k
  have hUpper := Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
  change log (Stirling.stirlingSeq (k + 1)) ≤ log (Stirling.stirlingSeq 1) at hUpper
  rw [Stirling.stirlingSeq_one, Real.log_div (Real.exp_ne_zero _) (by positivity),
    Real.log_exp, Real.log_sqrt (by norm_num)] at hUpper
  norm_num at hLower
  constructor <;> linarith only [hFormula, hLower, hUpper, hLog]

/-- The deterministic center obtained from the decimal length and the number
of trailing zeros differs from the conjectured center by at most a logarithm. -/
private theorem center_error {n : ℕ} (hn : 2 ≤ n) :
    let D : ℝ := 9 / 2 * (((Nat.digits 10 n.factorial).length : ℝ) - padicValNat 5 n.factorial) -
      (c₁ * n * log n - (c₁ + 9 / 8) * n)
    0 ≤ D ∧ D ≤ ((9 + c₁) / log 2 + c₁ / 2 + 9 / 2 / log 5) * log (n : ℝ) := by
  have hn₁ : 1 ≤ n := by omega
  have hn₀ : 0 < n := by omega
  let s := (Nat.digits 5 n).sum
  have hsn : s ≤ n := by
    simpa only [s, Nat.ofDigits_digits] using
      (Nat.sum_le_ofDigits (Nat.digits 5 n) (by decide : 1 ≤ 5))
  have hz : (padicValNat 5 n.factorial : ℝ) = ((n : ℝ) - (s : ℝ)) / 4 := by
    have hp : Fact (Nat.Prime 5) := ⟨by decide⟩
    have h := sub_one_mul_padicValNat_factorial (p := 5) (hp := hp) n
    change 4 * padicValNat 5 n.factorial = n - s at h
    have he : 4 * padicValNat 5 n.factorial + s = n := by omega
    have heR : 4 * (padicValNat 5 n.factorial : ℝ) + (s : ℝ) = (n : ℝ) := by exact_mod_cast he
    linarith only [heR]
  have hs₀ : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hsUpper : (s : ℝ) ≤ (log (n : ℝ) / log 5 + 1) * 4 := by
    have sum_bound (digits : List ℕ) (h : ∀ d ∈ digits, d ≤ 4) :
        digits.sum ≤ digits.length * 4 := by
      induction digits with
      | nil => simp
      | cons d rest ih =>
        have hd := h d List.mem_cons_self
        have hrest := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
        simp only [List.sum_cons, List.length_cons]
        omega
    have hsum : s ≤ (Nat.digits 5 n).length * 4 :=
      sum_bound (Nat.digits 5 n)
        (fun d hd => Nat.le_of_lt_succ (Nat.digits_lt_base (by decide : 1 < 5) hd))
    have hsumR : (s : ℝ) ≤ ((Nat.digits 5 n).length : ℝ) * 4 := by exact_mod_cast hsum
    exact hsumR.trans (mul_le_mul_of_nonneg_right
      (digit_length_bounds (by decide : 1 < 5) hn₀).2 (by norm_num))
  have hDigits := digit_length_bounds (by decide : 1 < 10) (Nat.factorial_pos n)
  have hErr := stirling_error hn₁
  have hc₀ : 0 ≤ c₁ := by
    unfold c₁
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) (log_pos (by norm_num)).le)
  have hc₉ : 0 ≤ (9 : ℝ) + c₁ := add_nonneg (by norm_num) hc₀
  have hc : c₁ = (9 : ℝ) / 2 / log 10 := by simp only [c₁, div_div]
  intro D
  have hD : D =
      9 / 2 * (((Nat.digits 10 n.factorial).length : ℝ) - log (n.factorial : ℝ) / log 10) +
      c₁ * (log (n.factorial : ℝ) - ((n : ℝ) * log (n : ℝ) - n)) + 9 / 8 * (s : ℝ) := by
    dsimp only [D]
    rw [hz, hc]
    ring
  have hlog₂ : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogn : log (2 : ℝ) ≤ log (n : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hOne : (1 : ℝ) ≤ log (n : ℝ) / log 2 :=
    (le_div_iff₀ hlog₂).mpr (by simpa only [one_mul] using hlogn)
  constructor
  · rw [hD]
    exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hDigits.1))
      (mul_nonneg hc₀ hErr.1)) (mul_nonneg (by norm_num) hs₀)
  · rw [hD]
    calc
      _ ≤ 9 / 2 * 1 + c₁ * (1 + log (n : ℝ) / 2) +
          9 / 8 * ((log (n : ℝ) / log 5 + 1) * 4) := by
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (by linarith only [hDigits.2]) (by norm_num))
          (mul_le_mul_of_nonneg_left hErr.2 hc₀)) (mul_le_mul_of_nonneg_left hsUpper (by norm_num))
      _ = (9 + c₁) * 1 + (c₁ / 2 + 9 / 2 / log 5) * log (n : ℝ) := by ring
      _ ≤ (9 + c₁) * (log (n : ℝ) / log 2) + (c₁ / 2 + 9 / 2 / log 5) * log (n : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hOne hc₉) le_rfl
      _ = _ := by ring

/-- Upper discrepancy from the center determined by the significant digit count. -/
def H1 : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    (a n : ℝ) - 9 / 2 * (((Nat.digits 10 n.factorial).length : ℝ) - padicValNat 5 n.factorial) ≤
      C * log (n : ℝ)

/-- Lower discrepancy from the center determined by the significant digit count. -/
def H2 : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    9 / 2 * (((Nat.digits 10 n.factorial).length : ℝ) - padicValNat 5 n.factorial) - (a n : ℝ) ≤
      C * log (n : ℝ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a004152.main := by
  intro hAbove hBelow
  obtain ⟨U, hAbove⟩ := hAbove
  obtain ⟨V, hBelow⟩ := hBelow
  let K : ℝ := (9 + c₁) / log 2 + c₁ / 2 + 9 / 2 / log 5
  refine IsBigO.of_bound (max U V + K) ?_
  filter_upwards [hAbove, hBelow, eventually_ge_atTop (2 : ℕ)] with n hU hV hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog := Real.log_nonneg hnR
  have hU' := hU.trans (mul_le_mul_of_nonneg_right (le_max_left U V) hlog)
  have hV' := hV.trans (mul_le_mul_of_nonneg_right (le_max_right U V) hlog)
  have hCenter := center_error hn
  dsimp only at hCenter
  have hCenter₀ := hCenter.1
  have hCenter₁ := hCenter.2
  change _ ≤ K * log (n : ℝ) at hCenter₁
  have hK := hCenter₀.trans hCenter₁
  change ‖(a n : ℝ) - (c₁ * n * log n - (c₁ + 9 / 8) * n)‖ ≤ (max U V + K) * ‖log (n : ℝ)‖
  rw [Real.norm_of_nonneg hlog, Real.norm_eq_abs, add_mul (max U V) K (log (n : ℝ))]
  exact abs_le.mpr ⟨by linarith only [hV', hCenter₀, hK], by linarith only [hU', hCenter₁]⟩

end OMA.R_oeis_a004152_R1
