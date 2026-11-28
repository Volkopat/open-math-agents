import FormalConjectures.Wikipedia.SkewesNumber
import Mathlib.NumberTheory.Chebyshev

/-! Transfer weighted prime-power oscillations to integer prime-counting sign changes. -/

namespace OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R2

open ArithmeticFunction Real
open scoped Interval

private theorem weighted_count_decomp (x : ℝ) :
    (∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, vonMangoldt k / Real.log (k : ℝ)) = (Nat.primeCounting ⌊x⌋₊ : ℝ) + (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬n.Prime, vonMangoldt n / Real.log (n : ℝ)) := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc 0 ⌊x⌋₊)
    (p := Nat.Prime) (f := fun n => vonMangoldt n / Real.log (n : ℝ))]
  have hp : (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime = Nat.primesLE ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
    exact ⟨fun ⟨⟨_, hb⟩, hn⟩ => ⟨hb, hn⟩, fun ⟨hb, hn⟩ => ⟨⟨hn.pos, hb⟩, hn⟩⟩
  rw [hp, Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) ?_,
    Finset.sum_const, nsmul_eq_mul, mul_one, Nat.primesLE_card_eq_primeCounting]
  intro n hn
  have hprime := (Nat.mem_primesLE.mp hn).2
  rw [vonMangoldt_apply_prime hprime, div_self (Real.log_pos (by exact_mod_cast hprime.one_lt)).ne']

private theorem weighted_count_ge (x : ℝ) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, vonMangoldt k / Real.log (k : ℝ)) := by
  rw [weighted_count_decomp]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ =>
    div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg _))

private theorem low_weight (n : ℕ) :
    vonMangoldt n / Real.log (n : ℝ) ≤ vonMangoldt n / Real.log 2 := by
  rcases n with _ | _ | n
  · simp
  · simp
  · refine div_le_div_of_nonneg_left vonMangoldt_nonneg (Real.log_pos one_lt_two) ?_
    exact Real.log_le_log (by norm_num) (by exact_mod_cast Nat.le_add_left 2 n)

private theorem log_interval {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    0 ≤ Real.logIntegral b - Real.logIntegral a ∧
      Real.logIntegral b - Real.logIntegral a ≤ (b - a) / Real.log 2 := by
  have hi {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
      IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le huv]
    apply continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
    · intro t ht
      exact (by linarith [ht.1] : t ≠ 0)
    · intro t ht
      exact (Real.log_pos (by linarith [ht.1])).ne'
  have hdiff : Real.logIntegral b - Real.logIntegral a =
      ∫ t in a..b, 1 / Real.log t := by
    unfold Real.logIntegral
    have heq := intervalIntegral.integral_add_adjacent_intervals (hi le_rfl ha) (hi ha hab)
    linarith
  rw [hdiff]
  constructor
  · exact intervalIntegral.integral_nonneg hab fun t ht =>
      one_div_nonneg.mpr (Real.log_nonneg (by linarith [ht.1]))
  · have hmono := intervalIntegral.integral_mono_on hab (hi ha hab)
      (intervalIntegrable_const (c := (Real.log 2)⁻¹)) (fun t ht => by
        rw [one_div]
        exact inv_anti₀ (Real.log_pos one_lt_two)
          (Real.log_le_log (by norm_num) (ha.trans ht.1)))
    simpa [intervalIntegral.integral_const, div_eq_mul_inv, smul_eq_mul] using hmono

private theorem weighted_count_le :
    ∃ B : ℝ, ∀ x ≥ 2, (∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, vonMangoldt k / Real.log (k : ℝ)) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) +
      B * (Real.sqrt x / Real.log x) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := max 0 C
  have hD (y : ℝ) : Chebyshev.psi y - Chebyshev.theta y ≤ D * Real.sqrt y :=
    (hC y).trans (mul_le_mul_of_nonneg_right (le_max_right 0 C) (Real.sqrt_nonneg y))
  refine ⟨4 * D / Real.log 2 + 2 * D, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h2log : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  let s := (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬ n.Prime)
  let a := s.filter (fun n => n ≤ ⌊Real.sqrt x⌋₊)
  let b := s.filter (fun n => ¬n ≤ ⌊Real.sqrt x⌋₊)
  have ha : a = (Finset.Ioc 0 ⌊Real.sqrt x⌋₊).filter (fun n : ℕ => ¬n.Prime) := by
    have hf : ⌊Real.sqrt x⌋₊ ≤ ⌊x⌋₊ :=
      Nat.floor_mono (Real.sqrt_le_iff.mpr ⟨hx0, by nlinarith⟩)
    ext n
    simp only [a, s, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨fun ⟨⟨hp, hn⟩, hb⟩ => ⟨⟨hp.1, hb⟩, hn⟩,
      fun ⟨⟨hp, hb⟩, hn⟩ => ⟨⟨⟨hp, hb.trans hf⟩, hn⟩, hb⟩⟩
  have hlow : ∑ n ∈ a, vonMangoldt n / Real.log (n : ℝ) ≤ D * Real.sqrt (Real.sqrt x) /
      Real.log 2 := by
    calc
      _ ≤ ∑ n ∈ a, vonMangoldt n / Real.log 2 :=
        Finset.sum_le_sum fun n _ => low_weight n
      _ = (Chebyshev.psi (Real.sqrt x) - Chebyshev.theta (Real.sqrt x)) / Real.log 2 := by
        rw [← Finset.sum_div, ha, ← Chebyshev.psi_sub_theta_eq_sum_not_prime]
      _ ≤ _ := div_le_div_of_nonneg_right (hD _) h2log.le
  have hhigh : ∑ n ∈ b, vonMangoldt n / Real.log (n : ℝ) ≤
      D * Real.sqrt x / (Real.log x / 2) := by
    calc
      _ ≤ ∑ n ∈ b, vonMangoldt n / (Real.log x / 2) := by
        apply Finset.sum_le_sum
        intro n hn
        have hlt : Real.sqrt x < (n : ℝ) := by
          apply (Nat.floor_lt (Real.sqrt_nonneg x)).mp
          exact Nat.lt_of_not_ge (Finset.mem_filter.mp hn).2
        apply div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity)
        calc
          Real.log x / 2 = Real.log (Real.sqrt x) := (Real.log_sqrt hx0).symm
          _ ≤ Real.log (n : ℝ) := Real.log_le_log hsqrt hlt.le
      _ ≤ ∑ n ∈ s, vonMangoldt n / (Real.log x / 2) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => div_nonneg vonMangoldt_nonneg (by positivity))
      _ = (Chebyshev.psi x - Chebyshev.theta x) / (Real.log x / 2) := by
        rw [← Finset.sum_div, Chebyshev.psi_sub_theta_eq_sum_not_prime]
      _ ≤ _ := div_le_div_of_nonneg_right (hD _) (by positivity)
  have hs : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
    congr 1
    norm_num
  have hproduct : Real.sqrt (Real.sqrt x) * (Real.sqrt (Real.sqrt x)) = Real.sqrt x := by
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg x)]
  have hsize : Real.sqrt (Real.sqrt x) * Real.log x ≤ 4 * Real.sqrt x := by
    have hlog := Real.log_le_rpow_div (x := x) (ε := 1 / 4) hx0 (by norm_num)
    rw [← hs] at hlog
    have hm := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg (Real.sqrt x))
    calc
      _ ≤ Real.sqrt (Real.sqrt x) * (Real.sqrt (Real.sqrt x) / (1 / 4)) := hm
      _ = _ := by linear_combination 4 * hproduct
  have hsmall : D * Real.sqrt (Real.sqrt x) / Real.log 2 ≤
      (4 * D / Real.log 2) * (Real.sqrt x / Real.log x) := by
    have hD0 : 0 ≤ D := le_max_left _ _
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsize hD0]
  rw [weighted_count_decomp]
  change (Nat.primeCounting ⌊x⌋₊ : ℝ) + (∑ n ∈ s, vonMangoldt n / Real.log (n : ℝ)) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not (p := fun n => n ≤ ⌊Real.sqrt x⌋₊)]
  change (Nat.primeCounting ⌊x⌋₊ : ℝ) +
    ((∑ n ∈ a, vonMangoldt n / Real.log (n : ℝ)) +
      (∑ n ∈ b, vonMangoldt n / Real.log (n : ℝ))) ≤ _
  rw [add_mul]
  have hh : D * Real.sqrt x / (Real.log x / 2) = 2 * D * (Real.sqrt x / Real.log x) := by ring
  linarith [hlow.trans hsmall, hhigh.trans_eq hh]

-- The weighted prime-power count has positive and negative oscillations of
-- unbounded size on the sqrt(x)/log(x) scale.  Only a constant margin is
-- needed on the negative side.
def H1 : Prop :=
  ∀ B X : ℝ, ∃ x ≥ max 2 X,
    Real.logIntegral x + B * (Real.sqrt x / Real.log x) <
      (∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, vonMangoldt k / Real.log (k : ℝ))

def H2 : Prop :=
  ∀ X : ℝ, ∃ x ≥ max 2 X,
    (∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, vonMangoldt k / Real.log (k : ℝ)) + (Real.log 2)⁻¹ <
      Real.logIntegral x

theorem main : H1 → H2 → type_of% @SkewesNumber.littlewood_pi_minus_li_infinite_sign_changes := by
  intro habove hbelow
  constructor
  · obtain ⟨B, hB⟩ := weighted_count_le
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨x, hx, hs⟩ := habove B (N + 1 : ℕ)
    have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
    have hn2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx2
    have hn : N + 1 ≤ ⌊x⌋₊ := Nat.le_floor ((le_max_right _ _).trans hx)
    have hr := log_interval (by exact_mod_cast hn2) (Nat.floor_le (by linarith [hx2]))
    have hb := hB x hx2
    exact ⟨⌊x⌋₊, ⟨hn2, by linarith [hr.1]⟩, by omega⟩
  · apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨x, hx, hs⟩ := hbelow (N + 1 : ℕ)
    have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
    have hn2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx2
    have hn : N + 1 ≤ ⌊x⌋₊ := Nat.le_floor ((le_max_right _ _).trans hx)
    have hr := log_interval (by exact_mod_cast hn2) (Nat.floor_le (by linarith [hx2]))
    have hshort : (x - (⌊x⌋₊ : ℝ)) / Real.log 2 ≤ (Real.log 2)⁻¹ := by
      rw [← one_div]
      exact div_le_div_of_nonneg_right (by linarith [Nat.lt_floor_add_one x])
        (Real.log_pos one_lt_two).le
    have hp := weighted_count_ge x
    exact ⟨⌊x⌋₊, ⟨hn2, by linarith [hr.2.trans hshort]⟩, by omega⟩

end OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R2
