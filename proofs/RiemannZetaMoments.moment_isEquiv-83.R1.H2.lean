import OMAReductions.R_RiemannZetaMoments_moment_isEquiv_83_R1
import Mathlib

/-!
# Proof of `RiemannZetaMoments.moment_isEquiv-83.R1.H2`

We prove off-diagonal and oscillatory cross-term cancellation for the balanced
approximate functional equation model of `ζ(1/2 + it)²`:
`(∫₀ᵀ ‖M t‖² - 2 ∫₀ᵀ ∑_{1 ≤ n ≤ ⌊t/(2π)⌋₊} d(n)² / n) =o[atTop] (T * (log T)⁴)`.
-/

namespace ZetaMomentsH2Proof

open Complex Filter Real Asymptotics MeasureTheory ArithmeticFunction Finset Set
open scoped BigOperators Topology ComplexConjugate

/- ### Section 1: Elementary Harmonic, Square-Root, and Divisor Bounds -/

private abbrev divFn (n : ℕ) : ℝ := ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ)

private lemma divFn_nonneg (n : ℕ) : 0 ≤ divFn n := Nat.cast_nonneg _

private lemma divFn_eq_card_divisors (n : ℕ) : divFn n = (n.divisors.card : ℝ) := by
  simp [divFn, ArithmeticFunction.sigma_apply]

private lemma harmonic_Icc_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ≤ Real.log (M : ℝ) + 1 := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      have hexp : (m : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.exp (-(1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
        have h1 := Real.add_one_le_exp (-(1 : ℝ) / ((m + 1 : ℕ) : ℝ))
        have heq : -(1 : ℝ) / ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
          push_cast; field_simp; ring
        linarith
      have hlog := Real.log_le_log (div_pos hm_pos hm1_pos) hexp
      rw [Real.log_div hm_pos.ne' hm1_pos.ne', Real.log_exp, neg_div] at hlog
      linarith
    linarith

private lemma harmonic_Icc_le_max (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ≤ Real.log (max (M : ℝ) 1) + 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · have hmax : max (M : ℝ) 1 = (M : ℝ) := max_eq_left (by exact_mod_cast hM)
    rw [hmax]
    exact harmonic_Icc_le M hM

private lemma inv_sq_sum_le_two (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / ((k : ℝ) ^ 2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · suffices h : ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / ((k : ℝ) ^ 2) ≤ 2 - 1 / (N : ℝ) by
      have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      linarith
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
        rw [div_sub_div _ _ hm_pos.ne' hm1_pos.ne', div_le_div_iff₀ (sq_pos_of_pos hm1_pos)
          (mul_pos hm_pos hm1_pos)]
        push_cast
        nlinarith
      linarith

private lemma inv_sqrt_sum_le (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (k : ℝ) ≤ 2 * Real.sqrt (M : ℝ) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hm1_pos : (0 : ℝ) < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hsum_pos : (0 : ℝ) < Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ) := by positivity
    have hsq : (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) *
        (Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ)) = 1 := by
      have h1 : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 = ((m + 1 : ℕ) : ℝ) :=
        Real.sq_sqrt (by positivity)
      have h2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
      push_cast at h1 ⊢
      nlinarith
    have hle_sqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ m)
    have hstep : (1 : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((m + 1 : ℕ) : ℝ) - 2 * Real.sqrt (m : ℝ) := by
      rw [div_le_iff₀ hm1_pos]
      have h2 : (2 * Real.sqrt ((m + 1 : ℕ) : ℝ) - 2 * Real.sqrt (m : ℝ)) *
          (Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ)) = 2 := by linarith
      have h3 : Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ) ≤
          2 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by linarith
      have hdiff_nn : 0 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ) := sub_nonneg.mpr hle_sqrt
      nlinarith
    linarith

private lemma sum_divFn_eq_double_sum {N : ℕ} (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, divFn n * f n =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), f (a * b) := by
  have h1 : ∀ n ∈ Finset.Icc 1 N,
      divFn n * f n = ∑ a ∈ n.divisors, f n := by
    intro n _
    rw [divFn_eq_card_divisors, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij (fun p => ⟨p.2, p.1 / p.2⟩) ?_ ?_ ?_ ?_
  · intro ⟨n, a⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp ⊢
    rcases hp with ⟨⟨hn1, hnN⟩, ⟨ha_dvd, hn0⟩⟩
    have ha1 : 1 ≤ a := Nat.pos_of_dvd_of_pos ha_dvd (by omega)
    have haN : a ≤ N := le_trans (Nat.le_of_dvd (by omega) ha_dvd) hnN
    have hb1 : 1 ≤ n / a := Nat.div_pos (Nat.le_of_dvd (by omega) ha_dvd) ha1
    have hbN : n / a ≤ N / a := Nat.div_le_div_right hnN
    exact ⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩
  · intro ⟨n₁, a₁⟩ hp₁ ⟨n₂, a₂⟩ hp₂ heq
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp₁ hp₂
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
    rcases heq with ⟨ha, hdiv⟩
    subst ha
    have hmul₁ : a₁ * (n₁ / a₁) = n₁ := Nat.mul_div_cancel' hp₁.2.1
    have hmul₂ : a₁ * (n₂ / a₁) = n₂ := Nat.mul_div_cancel' hp₂.2.1
    have hn : n₁ = n₂ := by rw [← hmul₁, ← hmul₂, hdiv]
    subst hn
    rfl
  · intro ⟨a, b⟩ hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc] at hp
    rcases hp with ⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩
    have hab1 : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
    have habN : a * b ≤ N := by
      calc a * b ≤ a * (N / a) := Nat.mul_le_mul_left a hbN
        _ ≤ N := Nat.mul_div_le N a
    refine ⟨⟨a * b, a⟩, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
      exact ⟨⟨hab1, habN⟩, ⟨dvd_mul_right a b, by omega⟩⟩
    · simp [Nat.mul_div_cancel_left b (by omega : 0 < a)]
  · intro ⟨n, a⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    dsimp only
    rw [Nat.mul_div_cancel' hp.2.1]

private lemma sum_divFn_div_sqrt_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ) ≤
      2 * Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1) := by
  have hrw : ∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ) =
      ∑ n ∈ Finset.Icc 1 N, divFn n * ((Real.sqrt (n : ℝ))⁻¹) := by
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [hrw, sum_divFn_eq_double_sum]
  calc ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), (Real.sqrt ((a * b : ℕ) : ℝ))⁻¹
      = ∑ a ∈ Finset.Icc 1 N, (1 / Real.sqrt (a : ℝ)) *
          ∑ b ∈ Finset.Icc 1 (N / a), (1 : ℝ) / Real.sqrt (b : ℝ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg a)]
        ring
    _ ≤ ∑ a ∈ Finset.Icc 1 N, (1 / Real.sqrt (a : ℝ)) * (2 * Real.sqrt ((N / a : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left (inv_sqrt_sum_le (N / a)) (by positivity)
    _ ≤ ∑ a ∈ Finset.Icc 1 N, (1 / Real.sqrt (a : ℝ)) * (2 * Real.sqrt ((N : ℝ) / (a : ℝ))) := by
        refine Finset.sum_le_sum fun a _ => ?_
        gcongr
        exact Nat.cast_div_le
    _ = 2 * Real.sqrt (N : ℝ) * ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / (a : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a ha => ?_
        have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (by exact (Finset.mem_Icc.mp ha).1)
        rw [Real.sqrt_div (Nat.cast_nonneg N)]
        have hsq : Real.sqrt (a : ℝ) ^ 2 = (a : ℝ) := Real.sq_sqrt ha_pos.le
        have hne : Real.sqrt (a : ℝ) ≠ 0 := (Real.sqrt_pos.mpr ha_pos).ne'
        field_simp [hne, ha_pos.ne']
        exact hsq.symm
    _ ≤ 2 * Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left (harmonic_Icc_le N hN) (by positivity)

private lemma sum_divFn_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 1 M, divFn n ≤ (M : ℝ) * (Real.log (M : ℝ) + 1) := by
  have hrw : ∑ n ∈ Finset.Icc 1 M, divFn n = ∑ n ∈ Finset.Icc 1 M, divFn n * 1 := by simp
  rw [hrw, sum_divFn_eq_double_sum]
  calc ∑ a ∈ Finset.Icc 1 M, ∑ _b ∈ Finset.Icc 1 (M / a), (1 : ℝ)
      = ∑ a ∈ Finset.Icc 1 M, ((M / a : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun a _ => by simp
    _ ≤ ∑ a ∈ Finset.Icc 1 M, (M : ℝ) / (a : ℝ) :=
        Finset.sum_le_sum fun a _ => Nat.cast_div_le
    _ = (M : ℝ) * ∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by ring
    _ ≤ (M : ℝ) * (Real.log (M : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (harmonic_Icc_le M hM) (Nat.cast_nonneg M)

private lemma divFn_le_two_mul_small_divisors {x R : ℕ} (hx : 1 ≤ x) (hR : Nat.sqrt x ≤ R) :
    divFn x ≤ 2 * ∑ a ∈ Finset.Icc 1 R, if a ∣ x then (1 : ℝ) else 0 := by
  rw [divFn_eq_card_divisors]
  set sLo := x.divisors.filter (fun a => a ≤ Nat.sqrt x)
  set sHi := x.divisors.filter (fun a => ¬ (a ≤ Nat.sqrt x))
  have hcard_add : x.divisors.card = sLo.card + sHi.card := by
    rw [← Finset.card_filter_add_card_filter_not (p := fun a => a ≤ Nat.sqrt x)]
  have hhi_le : sHi.card ≤ sLo.card := by
    refine Finset.card_le_card_of_injOn (fun a => x / a) ?_ ?_
    · intro a ha
      simp only [Finset.mem_coe, sHi, sLo, Finset.mem_filter, Nat.mem_divisors] at ha ⊢
      rcases ha with ⟨⟨ha_dvd, hx0⟩, hgt⟩
      have hgt' : Nat.sqrt x < a := Nat.lt_of_not_ge hgt
      have hdiv_dvd : x / a ∣ x := Nat.div_dvd_of_dvd ha_dvd
      refine ⟨⟨hdiv_dvd, hx0⟩, ?_⟩
      by_contra hle
      have hgt2 : Nat.sqrt x < x / a := Nat.lt_of_not_ge hle
      have hprod : (Nat.sqrt x + 1) * (Nat.sqrt x + 1) ≤ a * (x / a) :=
        Nat.mul_le_mul hgt' hgt2
      rw [Nat.mul_div_cancel' ha_dvd] at hprod
      have hlt := Nat.lt_succ_sqrt x
      rw [Nat.succ_eq_add_one] at hlt
      omega
    · intro a₁ ha₁ a₂ ha₂ heq
      dsimp only at heq
      simp only [Finset.mem_coe, sHi, Finset.mem_filter, Nat.mem_divisors] at ha₁ ha₂
      have h1 : a₁ * (x / a₁) = x := Nat.mul_div_cancel' ha₁.1.1
      have h2 : a₂ * (x / a₂) = x := Nat.mul_div_cancel' ha₂.1.1
      have hpos : 0 < x / a₁ := Nat.div_pos (Nat.le_of_dvd (by omega) ha₁.1.1)
        (Nat.pos_of_dvd_of_pos ha₁.1.1 (by omega))
      rw [heq] at h1
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < x / a₂) (h1.trans h2.symm)
  have hlo_sub : sLo ⊆ (Finset.Icc 1 R).filter (fun a => a ∣ x) := by
    intro a ha
    simp only [sLo, Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at ha ⊢
    exact ⟨⟨Nat.pos_of_dvd_of_pos ha.1.1 (by omega), ha.2.trans hR⟩, ha.1.1⟩
  have hcard_le : x.divisors.card ≤ 2 * ((Finset.Icc 1 R).filter (fun a => a ∣ x)).card := by
    have hsub := Finset.card_le_card hlo_sub
    omega
  have hrw : (((Finset.Icc 1 R).filter (fun a => a ∣ x)).card : ℝ) =
      ∑ a ∈ Finset.Icc 1 R, if a ∣ x then (1 : ℝ) else 0 := by
    simp [Finset.sum_boole]
  rw [← hrw]
  exact_mod_cast hcard_le

private lemma divFn_le_two_sqrt {x : ℕ} (hx : 1 ≤ x) :
    divFn x ≤ 2 * Real.sqrt (x : ℝ) := by
  have h1 := divFn_le_two_mul_small_divisors hx le_rfl
  have h2 : (∑ a ∈ Finset.Icc 1 (Nat.sqrt x), if a ∣ x then (1 : ℝ) else 0) ≤
      (Nat.sqrt x : ℝ) := by
    calc (∑ a ∈ Finset.Icc 1 (Nat.sqrt x), if a ∣ x then (1 : ℝ) else 0)
        ≤ ∑ _a ∈ Finset.Icc 1 (Nat.sqrt x), (1 : ℝ) := by
          refine Finset.sum_le_sum fun a _ => ?_
          split_ifs <;> norm_num
      _ = (Nat.sqrt x : ℝ) := by simp
  have h3 : (Nat.sqrt x : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _), sq]
    exact_mod_cast Nat.sqrt_le x
  linarith

private lemma card_shifted_congruence_le {N k a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (((Finset.Icc 1 N).filter (fun m => a ∣ m ∧ b ∣ m + k)).card : ℝ) ≤
      if Nat.gcd a b ∣ k then (N : ℝ) * (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) + 1 else 0 := by
  set S := (Finset.Icc 1 N).filter (fun m => a ∣ m ∧ b ∣ m + k)
  by_cases hg : Nat.gcd a b ∣ k
  · rw [if_pos hg]
    by_cases hS : S.Nonempty
    · set m₀ := S.min' hS
      have hm₀ : m₀ ∈ S := Finset.min'_mem S hS
      simp only [S, Finset.mem_filter, Finset.mem_Icc] at hm₀
      set L := Nat.lcm a b
      have hL_pos : 0 < L := Nat.lcm_pos (by omega) (by omega)
      have hcard : S.card ≤ N / L + 1 := by
        have hcard_range : (Finset.range (N / L + 1)).card = N / L + 1 := Finset.card_range _
        rw [← hcard_range]
        refine Finset.card_le_card_of_injOn (fun m => (m - m₀) / L) ?_ ?_
        · intro m hm
          have hm' := hm
          simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_Icc] at hm'
          have hle : m₀ ≤ m := Finset.min'_le S m (Finset.mem_coe.mp hm)
          simp only [Finset.mem_coe, Finset.mem_range]
          have hsub_le : m - m₀ ≤ N := by omega
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hsub_le)
        · intro m₁ hm₁ m₂ hm₂ heq
          have h1 := hm₁; have h2 := hm₂
          simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_Icc] at h1 h2
          have hle₁ : m₀ ≤ m₁ := Finset.min'_le S m₁ (Finset.mem_coe.mp hm₁)
          have hle₂ : m₀ ≤ m₂ := Finset.min'_le S m₂ (Finset.mem_coe.mp hm₂)
          have hdvd₁ : L ∣ m₁ - m₀ := by
            refine Nat.lcm_dvd (Nat.dvd_sub h1.2.1 hm₀.2.1) ?_
            have hsub : m₁ + k - (m₀ + k) = m₁ - m₀ := by omega
            rw [← hsub]
            exact Nat.dvd_sub h1.2.2 hm₀.2.2
          have hdvd₂ : L ∣ m₂ - m₀ := by
            refine Nat.lcm_dvd (Nat.dvd_sub h2.2.1 hm₀.2.1) ?_
            have hsub : m₂ + k - (m₀ + k) = m₂ - m₀ := by omega
            rw [← hsub]
            exact Nat.dvd_sub h2.2.2 hm₀.2.2
          have hmul₁ : L * ((m₁ - m₀) / L) = m₁ - m₀ := Nat.mul_div_cancel' hdvd₁
          have hmul₂ : L * ((m₂ - m₀) / L) = m₂ - m₀ := Nat.mul_div_cancel' hdvd₂
          dsimp only at heq
          have hdiff : m₁ - m₀ = m₂ - m₀ := by rw [← hmul₁, ← hmul₂, heq]
          omega
      have hgl : (Nat.gcd a b : ℝ) * (L : ℝ) = (a : ℝ) * (b : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm a b
      have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (by omega)
      have hb_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr (by omega)
      have hL_posR : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL_pos
      have hdiv_le : ((N / L : ℕ) : ℝ) ≤ (N : ℝ) * (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) := by
        calc ((N / L : ℕ) : ℝ) ≤ (N : ℝ) / (L : ℝ) := Nat.cast_div_le
          _ = (N : ℝ) * (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) := by
              rw [← hgl]
              field_simp [hL_posR.ne', (Nat.cast_pos.mpr (Nat.gcd_pos_of_pos_left b (by omega))).ne']
      have hcast : (S.card : ℝ) ≤ ((N / L : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp
      positivity
  · rw [if_neg hg]
    have hempty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      simp only [S, Finset.mem_filter, Finset.mem_Icc] at hm
      have h1 : Nat.gcd a b ∣ m := dvd_trans (Nat.gcd_dvd_left a b) hm.2.1
      have h2 : Nat.gcd a b ∣ m + k := dvd_trans (Nat.gcd_dvd_right a b) hm.2.2
      exact hg ((Nat.dvd_add_right h1).mp h2)
    rw [hempty]
    simp

private lemma sum_le_sum_of_injOn {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : Finset β} {f : α → ℝ} {g : β → ℝ} (e : α → β)
    (he_maps : ∀ a ∈ s, f a ≠ 0 → e a ∈ t)
    (he_inj : ∀ a₁ ∈ s, f a₁ ≠ 0 → ∀ a₂ ∈ s, f a₂ ≠ 0 → e a₁ = e a₂ → a₁ = a₂)
    (hg_nn : ∀ b ∈ t, 0 ≤ g b)
    (hfg : ∀ a ∈ s, f a ≠ 0 → f a ≤ g (e a)) :
    ∑ a ∈ s, f a ≤ ∑ b ∈ t, g b := by
  classical
  set s' := s.filter (fun a => f a ≠ 0)
  have h1 : ∑ a ∈ s, f a = ∑ a ∈ s', f a :=
    (Finset.sum_filter_of_ne (fun _ _ h => h)).symm
  rw [h1]
  have h2 : ∑ a ∈ s', f a ≤ ∑ a ∈ s', g (e a) :=
    Finset.sum_le_sum fun a ha => hfg a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
  have h3 : ∑ a ∈ s', g (e a) = ∑ b ∈ s'.image e, g b := by
    rw [Finset.sum_image]
    intro a₁ ha₁ a₂ ha₂ heq
    exact he_inj a₁ (Finset.mem_filter.mp ha₁).1 (Finset.mem_filter.mp ha₁).2
      a₂ (Finset.mem_filter.mp ha₂).1 (Finset.mem_filter.mp ha₂).2 heq
  have hsub : s'.image e ⊆ t := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    exact he_maps a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
  exact h2.trans (h3.le.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun b hb _ => hg_nn b hb))

private lemma shifted_divFn_fixed_k_le {N k : ℕ} (hN : 1 ≤ N) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, divFn m * divFn (m + k) ≤
      8 * (N : ℝ) + 4 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 2 *
        ∑ g ∈ k.divisors, (1 : ℝ) / (g : ℝ) := by
  set R := Nat.sqrt (2 * N)
  have h1 : ∑ m ∈ Finset.Icc 1 N, divFn m * divFn (m + k) ≤
      ∑ m ∈ Finset.Icc 1 N,
        (2 * ∑ a ∈ Finset.Icc 1 R, if a ∣ m then (1 : ℝ) else 0) *
        (2 * ∑ b ∈ Finset.Icc 1 R, if b ∣ m + k then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
    refine mul_le_mul ?_ ?_ (divFn_nonneg _) (by positivity)
    · exact divFn_le_two_mul_small_divisors hm1 (Nat.sqrt_le_sqrt (by omega))
    · exact divFn_le_two_mul_small_divisors (by omega) (Nat.sqrt_le_sqrt (by omega))
  have h2 : ∑ m ∈ Finset.Icc 1 N,
        (2 * ∑ a ∈ Finset.Icc 1 R, if a ∣ m then (1 : ℝ) else 0) *
        (2 * ∑ b ∈ Finset.Icc 1 R, if b ∣ m + k then (1 : ℝ) else 0) =
      4 * ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
        (((Finset.Icc 1 N).filter (fun m => a ∣ m ∧ b ∣ m + k)).card : ℝ) := by
    have hre : ∀ m ∈ Finset.Icc 1 N,
        (2 * ∑ a ∈ Finset.Icc 1 R, if a ∣ m then (1 : ℝ) else 0) *
        (2 * ∑ b ∈ Finset.Icc 1 R, if b ∣ m + k then (1 : ℝ) else 0) =
        4 * ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
          if a ∣ m ∧ b ∣ m + k then (1 : ℝ) else 0 := by
      intro m _
      rw [show (2 * ∑ a ∈ Finset.Icc 1 R, if a ∣ m then (1 : ℝ) else 0) *
          (2 * ∑ b ∈ Finset.Icc 1 R, if b ∣ m + k then (1 : ℝ) else 0) =
          4 * ((∑ a ∈ Finset.Icc 1 R, if a ∣ m then (1 : ℝ) else 0) *
            (∑ b ∈ Finset.Icc 1 R, if b ∣ m + k then (1 : ℝ) else 0)) by ring]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases ha : a ∣ m <;> by_cases hb : b ∣ m + k <;> simp [ha, hb]
    rw [Finset.sum_congr rfl hre, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [Finset.sum_boole]
  have h3 : ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
        (((Finset.Icc 1 N).filter (fun m => a ∣ m ∧ b ∣ m + k)).card : ℝ) ≤
      2 * (N : ℝ) + (N : ℝ) * ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
        if Nat.gcd a b ∣ k then (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) else 0 := by
    calc ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
            (((Finset.Icc 1 N).filter (fun m => a ∣ m ∧ b ∣ m + k)).card : ℝ)
        ≤ ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
            (if Nat.gcd a b ∣ k then (N : ℝ) * (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) + 1 else 0) := by
          refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ?_
          exact card_shifted_congruence_le (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1
      _ ≤ ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
            ((1 : ℝ) + (N : ℝ) * (if Nat.gcd a b ∣ k then (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) else 0)) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          split_ifs
          · ring_nf; exact le_rfl
          · norm_num
      _ = (R : ℝ) ^ 2 + (N : ℝ) * ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
            if Nat.gcd a b ∣ k then (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) else 0 := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc]
          simp [sq]
      _ ≤ 2 * (N : ℝ) + (N : ℝ) * ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
            if Nat.gcd a b ∣ k then (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) else 0 := by
          gcongr
          have hRsq : R * R ≤ 2 * N := Nat.sqrt_le (2 * N)
          have hRsq' : (R : ℝ) ^ 2 ≤ 2 * (N : ℝ) := by
            rw [sq]; exact_mod_cast hRsq
          exact hRsq'
  have h4 : ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
        (if Nat.gcd a b ∣ k then (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) else 0) ≤
      (Real.log (2 * (N : ℝ)) + 1) ^ 2 * ∑ g ∈ k.divisors, (1 : ℝ) / (g : ℝ) := by
    set P := ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)).filter (fun p => Nat.gcd p.1 p.2 ∣ k)
    set Q := k.divisors ×ˢ ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R))
    have hLHS : ∑ a ∈ Finset.Icc 1 R, ∑ b ∈ Finset.Icc 1 R,
          (if Nat.gcd a b ∣ k then (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) else 0) =
        ∑ p ∈ P, (Nat.gcd p.1 p.2 : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ)) := by
      rw [← Finset.sum_product', Finset.sum_filter]
    have hRHS : ∑ q ∈ Q, ((1 : ℝ) / (q.1 : ℝ)) * ((1 : ℝ) / (q.2.1 : ℝ)) * ((1 : ℝ) / (q.2.2 : ℝ)) =
        (∑ a' ∈ Finset.Icc 1 R, (1 : ℝ) / (a' : ℝ)) ^ 2 *
          ∑ g ∈ k.divisors, (1 : ℝ) / (g : ℝ) := by
      rw [Finset.sum_product]
      simp_rw [Finset.sum_product, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    have hinj : ∑ p ∈ P, (Nat.gcd p.1 p.2 : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ)) ≤
        ∑ q ∈ Q, ((1 : ℝ) / (q.1 : ℝ)) * ((1 : ℝ) / (q.2.1 : ℝ)) * ((1 : ℝ) / (q.2.2 : ℝ)) := by
      refine sum_le_sum_of_injOn (fun p => (Nat.gcd p.1 p.2, (p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2))) ?_ ?_ ?_ ?_
      · intro p hp _
        simp only [P, Q, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Nat.mem_divisors] at hp ⊢
        rcases hp with ⟨⟨⟨ha1, haR⟩, ⟨hb1, hbR⟩⟩, hgk⟩
        have hg_pos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 (by omega)
        have ha_div1 : 1 ≤ p.1 / Nat.gcd p.1 p.2 :=
          Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left p.1 p.2)) hg_pos
        have hb_div1 : 1 ≤ p.2 / Nat.gcd p.1 p.2 :=
          Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right p.1 p.2)) hg_pos
        exact ⟨⟨hgk, by omega⟩, ⟨⟨ha_div1, Nat.div_le_self p.1 _ |>.trans haR⟩,
          ⟨hb_div1, Nat.div_le_self p.2 _ |>.trans hbR⟩⟩⟩
      · intro p₁ hp₁ _ p₂ hp₂ _ heq
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨hg, ha', hb'⟩
        have h1a : Nat.gcd p₁.1 p₁.2 * (p₁.1 / Nat.gcd p₁.1 p₁.2) = p₁.1 :=
          Nat.mul_div_cancel' (Nat.gcd_dvd_left p₁.1 p₁.2)
        have h2a : Nat.gcd p₂.1 p₂.2 * (p₂.1 / Nat.gcd p₂.1 p₂.2) = p₂.1 :=
          Nat.mul_div_cancel' (Nat.gcd_dvd_left p₂.1 p₂.2)
        have h1b : Nat.gcd p₁.1 p₁.2 * (p₁.2 / Nat.gcd p₁.1 p₁.2) = p₁.2 :=
          Nat.mul_div_cancel' (Nat.gcd_dvd_right p₁.1 p₁.2)
        have h2b : Nat.gcd p₂.1 p₂.2 * (p₂.2 / Nat.gcd p₂.1 p₂.2) = p₂.2 :=
          Nat.mul_div_cancel' (Nat.gcd_dvd_right p₂.1 p₂.2)
        ext
        · rw [← h1a, ← h2a, ha', hg]
        · rw [← h1b, ← h2b, hb', hg]
      · intro q _
        positivity
      · intro p hp _
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        have hg_pos : (0 : ℝ) < (Nat.gcd p.1 p.2 : ℝ) :=
          Nat.cast_pos.mpr (Nat.gcd_pos_of_pos_left p.2 (by omega))
        have ha_eq : (p.1 : ℝ) = (Nat.gcd p.1 p.2 : ℝ) * ((p.1 / Nat.gcd p.1 p.2 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)).symm
        have hb_eq : (p.2 : ℝ) = (Nat.gcd p.1 p.2 : ℝ) * ((p.2 / Nat.gcd p.1 p.2 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)).symm
        have ha'_ne : ((p.1 / Nat.gcd p.1 p.2 : ℕ) : ℝ) ≠ 0 := by
          have : 0 < p.1 / Nat.gcd p.1 p.2 :=
            Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left p.1 p.2))
              (Nat.gcd_pos_of_pos_left p.2 (by omega))
          positivity
        have hb'_ne : ((p.2 / Nat.gcd p.1 p.2 : ℕ) : ℝ) ≠ 0 := by
          have : 0 < p.2 / Nat.gcd p.1 p.2 :=
            Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right p.1 p.2))
              (Nat.gcd_pos_of_pos_left p.2 (by omega))
          positivity
        dsimp only
        rw [ha_eq, hb_eq]
        field_simp [hg_pos.ne', ha'_ne, hb'_ne]
        exact le_rfl
    rw [hLHS]
    refine hinj.trans ?_
    rw [hRHS]
    have hH_le : ∑ a' ∈ Finset.Icc 1 R, (1 : ℝ) / (a' : ℝ) ≤ Real.log (2 * (N : ℝ)) + 1 := by
      refine (harmonic_Icc_le_max R).trans ?_
      have hR_le : max (R : ℝ) 1 ≤ 2 * (N : ℝ) := by
        apply max_le
        · exact_mod_cast Nat.sqrt_le_self (2 * N)
        · have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
      have hmax_pos : (0 : ℝ) < max (R : ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      linarith [Real.log_le_log hmax_pos hR_le]
    have hH_nn : 0 ≤ ∑ a' ∈ Finset.Icc 1 R, (1 : ℝ) / (a' : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hg_nn : 0 ≤ ∑ g ∈ k.divisors, (1 : ℝ) / (g : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH_nn hH_le 2) hg_nn
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

private lemma sum_inv_divisors_weighted_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) * ∑ g ∈ k.divisors, (1 : ℝ) / (g : ℝ) ≤
      2 * (Real.log (N : ℝ) + 1) := by
  have h1 : ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) * ∑ g ∈ k.divisors, (1 : ℝ) / (g : ℝ) =
      ∑ g ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 (N / g),
        ((1 : ℝ) / ((g * r : ℕ) : ℝ)) * ((1 : ℝ) / (g : ℝ)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij (fun p => ⟨p.2, p.1 / p.2⟩) ?_ ?_ ?_ ?_
    · intro ⟨k, g⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp ⊢
      rcases hp with ⟨⟨hk1, hkN⟩, ⟨hg_dvd, hk0⟩⟩
      have hg1 : 1 ≤ g := Nat.pos_of_dvd_of_pos hg_dvd (by omega)
      have hgN : g ≤ N := le_trans (Nat.le_of_dvd (by omega) hg_dvd) hkN
      exact ⟨⟨hg1, hgN⟩, ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hg_dvd) hg1, Nat.div_le_div_right hkN⟩⟩
    · intro ⟨k₁, g₁⟩ hp₁ ⟨k₂, g₂⟩ hp₂ heq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp₁ hp₂
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      rcases heq with ⟨hg, hdiv⟩
      subst hg
      have hk : k₁ = k₂ := by
        rw [← Nat.mul_div_cancel' hp₁.2.1, ← Nat.mul_div_cancel' hp₂.2.1, hdiv]
      subst hk
      rfl
    · intro ⟨g, r⟩ hp
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc] at hp
      rcases hp with ⟨⟨hg1, hgN⟩, ⟨hr1, hrN⟩⟩
      have hgr1 : 1 ≤ g * r := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
      have hgrN : g * r ≤ N := (Nat.mul_le_mul_left g hrN).trans (Nat.mul_div_le N g)
      refine ⟨⟨g * r, g⟩, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
        exact ⟨⟨hgr1, hgrN⟩, ⟨dvd_mul_right g r, by omega⟩⟩
      · simp [Nat.mul_div_cancel_left r (by omega : 0 < g)]
    · intro ⟨k, g⟩ hp
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
      dsimp only
      rw [Nat.mul_div_cancel' hp.2.1]
  rw [h1]
  calc ∑ g ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 (N / g),
          ((1 : ℝ) / ((g * r : ℕ) : ℝ)) * ((1 : ℝ) / (g : ℝ))
      = ∑ g ∈ Finset.Icc 1 N, ((1 : ℝ) / (g : ℝ) ^ 2) *
          ∑ r ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (r : ℝ) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Nat.cast_mul]; ring
    _ ≤ ∑ g ∈ Finset.Icc 1 N, ((1 : ℝ) / (g : ℝ) ^ 2) * (Real.log (N : ℝ) + 1) := by
        refine Finset.sum_le_sum fun g hg => ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (harmonic_Icc_le_max (N / g)).trans ?_
        have hle : max ((N / g : ℕ) : ℝ) 1 ≤ (N : ℝ) := by
          apply max_le
          · exact_mod_cast Nat.div_le_self N g
          · exact_mod_cast hN
        have hpos : (0 : ℝ) < max ((N / g : ℕ) : ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
        linarith [Real.log_le_log hpos hle]
    _ = (∑ g ∈ Finset.Icc 1 N, (1 : ℝ) / (g : ℝ) ^ 2) * (Real.log (N : ℝ) + 1) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * (Real.log (N : ℝ) + 1) := by
        have hlog_nn : 0 ≤ Real.log (N : ℝ) + 1 := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN)
          linarith
        exact mul_le_mul_of_nonneg_right (inv_sq_sum_le_two N) hlog_nn

private lemma shifted_divFn_sum_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) * ∑ m ∈ Finset.Icc 1 N, divFn m * divFn (m + k) ≤
      16 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 3 := by
  have hlog_ge1 : 1 ≤ Real.log (2 * (N : ℝ)) + 1 := by
    have : (1 : ℝ) ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    linarith [Real.log_nonneg this]
  have hlogN_le : Real.log (N : ℝ) + 1 ≤ Real.log (2 * (N : ℝ)) + 1 := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    linarith [Real.log_le_log hN_pos (show (N : ℝ) ≤ 2 * (N : ℝ) by linarith)]
  calc ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) * ∑ m ∈ Finset.Icc 1 N, divFn m * divFn (m + k)
      ≤ ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) *
          (8 * (N : ℝ) + 4 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 2 *
            ∑ g ∈ k.divisors, (1 : ℝ) / (g : ℝ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Finset.mem_Icc.mp hk
        exact mul_le_mul_of_nonneg_left (shifted_divFn_fixed_k_le hN hk'.1 hk'.2) (by positivity)
    _ = 8 * (N : ℝ) * (∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ)) +
        4 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 2 *
          (∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) * ∑ g ∈ k.divisors, (1 : ℝ) / (g : ℝ)) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 8 * (N : ℝ) * (Real.log (N : ℝ) + 1) +
        4 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 2 * (2 * (Real.log (N : ℝ) + 1)) := by
        gcongr
        · exact harmonic_Icc_le N hN
        · exact sum_inv_divisors_weighted_le hN
    _ ≤ 16 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 3 := by
        have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        set L := Real.log (2 * (N : ℝ)) + 1
        have hL_ge1 : 1 ≤ L := hlog_ge1
        have hL_sq : 1 ≤ L ^ 2 := by nlinarith
        have hL_le3 : L ≤ L ^ 3 := by nlinarith
        have hA : 8 * (N : ℝ) * (Real.log (N : ℝ) + 1) ≤ 8 * (N : ℝ) * L ^ 3 := by
          have h1 : Real.log (N : ℝ) + 1 ≤ L ^ 3 := hlogN_le.trans hL_le3
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        have hB : 4 * (N : ℝ) * L ^ 2 * (2 * (Real.log (N : ℝ) + 1)) ≤ 8 * (N : ℝ) * L ^ 3 := by
          have h1 : 8 * (N : ℝ) * L ^ 2 * (Real.log (N : ℝ) + 1) ≤ 8 * (N : ℝ) * L ^ 2 * L :=
            mul_le_mul_of_nonneg_left hlogN_le (by positivity)
          linarith [show 4 * (N : ℝ) * L ^ 2 * (2 * (Real.log (N : ℝ) + 1)) =
            8 * (N : ℝ) * L ^ 2 * (Real.log (N : ℝ) + 1) by ring,
            show 8 * (N : ℝ) * L ^ 2 * L = 8 * (N : ℝ) * L ^ 3 by ring]
        linarith

/- ### Section 2: Model Definitions, Unimodularity, and Indicator Integrals -/

private noncomputable def chi2 (t : ℝ) : ℂ :=
  (Complex.Gammaℝ (1 / 2 - Complex.I * (t : ℂ)) /
    Complex.Gammaℝ (1 / 2 + Complex.I * (t : ℂ))) ^ 2

private noncomputable def dirTerm (n : ℕ) (t : ℝ) : ℂ :=
  ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))

private noncomputable def dirPoly (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊t / (2 * Real.pi)⌋₊, dirTerm n t

private noncomputable def modelM (t : ℝ) : ℂ :=
  dirPoly t + chi2 t * star (dirPoly t)

private noncomputable def diagSum (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊t / (2 * Real.pi)⌋₊, divFn n ^ 2 / (n : ℝ)

private lemma cpow_ofReal_pos_conj {r : ℝ} (hr : 0 < r) (z : ℂ) :
    star ((r : ℂ) ^ z) = (r : ℂ) ^ (star z) := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hr0,
    Complex.star_def, ← Complex.exp_conj, map_mul, ← Complex.ofReal_log hr.le,
    Complex.conj_ofReal]

private lemma Gammaℝ_conj (s : ℂ) :
    star (Complex.Gammaℝ s) = Complex.Gammaℝ (star s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, star_mul',
    cpow_ofReal_pos_conj Real.pi_pos, Complex.star_def, ← Complex.Gamma_conj]
  simp only [map_div₀, map_neg, map_ofNat]

private lemma Gammaℝ_half_add_I_ne_zero (t : ℝ) :
    Complex.Gammaℝ (1 / 2 + Complex.I * (t : ℂ)) ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  simp

private lemma Gammaℝ_half_sub_I_ne_zero (t : ℝ) :
    Complex.Gammaℝ (1 / 2 - Complex.I * (t : ℂ)) ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  simp

private lemma Gammaℝ_half_sub_eq_star (t : ℝ) :
    Complex.Gammaℝ (1 / 2 - Complex.I * (t : ℂ)) =
      star (Complex.Gammaℝ (1 / 2 + Complex.I * (t : ℂ))) := by
  rw [Gammaℝ_conj]
  congr 1
  simp [sub_eq_add_neg]

private lemma norm_chi2 (t : ℝ) : ‖chi2 t‖ = 1 := by
  unfold chi2
  rw [norm_pow, norm_div, Gammaℝ_half_sub_eq_star, norm_star,
    div_self (norm_ne_zero_iff.mpr (Gammaℝ_half_add_I_ne_zero t)), one_pow]

private lemma star_chi2 (t : ℝ) :
    star (chi2 t) =
      (Complex.Gammaℝ (1 / 2 + Complex.I * (t : ℂ)) /
        Complex.Gammaℝ (1 / 2 - Complex.I * (t : ℂ))) ^ 2 := by
  unfold chi2
  rw [star_pow, star_div₀, Gammaℝ_half_sub_eq_star, star_star]

private lemma continuous_Gammaℝ_half_add_I :
    Continuous (fun t : ℝ => Complex.Gammaℝ (1 / 2 + Complex.I * (t : ℂ))) := by
  have h1 : Continuous (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
  unfold Complex.Gammaℝ
  refine Continuous.mul ?_ ?_
  · refine Continuous.const_cpow ?_ (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    fun_prop
  · rw [continuous_iff_continuousAt]
    intro t
    have hre : (0 : ℝ) < (((1 / 2 : ℂ) + Complex.I * (t : ℂ)) / 2).re := by
      simp
    have hne : ∀ m : ℕ, ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) / 2 ≠ -m := by
      intro m heq
      have := congrArg Complex.re heq
      simp at this
      linarith
    exact ContinuousAt.comp (g := Complex.Gamma) (Complex.continuousAt_Gamma _ hne)
      (by fun_prop : ContinuousAt (fun u : ℝ => ((1 / 2 : ℂ) + Complex.I * (u : ℂ)) / 2) t)

private lemma continuous_chi2 : Continuous chi2 := by
  have hadd := continuous_Gammaℝ_half_add_I
  have hsub : Continuous (fun t : ℝ => Complex.Gammaℝ (1 / 2 - Complex.I * (t : ℂ))) := by
    have : (fun t : ℝ => Complex.Gammaℝ (1 / 2 - Complex.I * (t : ℂ))) =
        fun t : ℝ => star (Complex.Gammaℝ (1 / 2 + Complex.I * (t : ℂ))) :=
      funext Gammaℝ_half_sub_eq_star
    rw [this]
    exact continuous_star.comp hadd
  unfold chi2
  exact (hsub.div hadd Gammaℝ_half_add_I_ne_zero).pow 2

private lemma norm_sq_modelM (t : ℝ) :
    ‖modelM t‖ ^ 2 = 2 * ‖dirPoly t‖ ^ 2 + 2 * (star (chi2 t) * dirPoly t ^ 2).re := by
  unfold modelM
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_mul,
    show star (dirPoly t) = (starRingEnd ℂ) (dirPoly t) from rfl, Complex.normSq_conj,
    Complex.normSq_eq_norm_sq (chi2 t), norm_chi2, one_pow, one_mul,
    Complex.normSq_eq_norm_sq (dirPoly t)]
  have hcross : dirPoly t * (starRingEnd ℂ) (chi2 t * (starRingEnd ℂ) (dirPoly t)) =
      star (chi2 t) * dirPoly t ^ 2 := by
    simp only [map_mul, Complex.star_def, starRingEnd_self_apply]
    ring
  rw [hcross]
  ring

private lemma dirTerm_eq_exp {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    dirTerm n t = ((divFn n / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      Complex.exp (-Complex.I * ((Real.log (n : ℝ) * t : ℝ) : ℂ)) := by
  unfold dirTerm
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlogn : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn_pos.le]
  rw [Complex.cpow_def_of_ne_zero hn_ne, hlogn]
  have hexp_arg : ((Real.log (n : ℝ) : ℝ) : ℂ) * (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) =
      (((-(1 / 2 : ℝ) * Real.log (n : ℝ) : ℝ) : ℂ) +
        (-Complex.I * ((Real.log (n : ℝ) * t : ℝ) : ℂ))) := by
    push_cast; ring
  rw [hexp_arg, Complex.exp_add, ← Complex.ofReal_exp]
  have hsqrt : Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn_pos, ← Real.exp_neg]
    congr 1; ring
  rw [hsqrt]
  push_cast
  ring

private lemma continuous_dirTerm {n : ℕ} (hn : 1 ≤ n) : Continuous (dirTerm n) := by
  have heq : dirTerm n = fun t : ℝ => ((divFn n / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      Complex.exp (-Complex.I * ((Real.log (n : ℝ) * t : ℝ) : ℂ)) :=
    funext (dirTerm_eq_exp hn)
  rw [heq]
  fun_prop

private lemma dirTerm_mul_star {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (t : ℝ) :
    dirTerm m t * star (dirTerm n t) =
      ((divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((Real.log (n : ℝ) - Real.log (m : ℝ)) * t : ℝ) : ℂ)) := by
  rw [dirTerm_eq_exp hm, dirTerm_eq_exp hn, star_mul', Complex.star_def, Complex.conj_ofReal,
    ← Complex.exp_conj]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg]
  have hexp : Complex.exp (-Complex.I * ((Real.log (m : ℝ) * t : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((Real.log (n : ℝ) * t : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (((Real.log (n : ℝ) - Real.log (m : ℝ)) * t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  rw [show ((divFn m / Real.sqrt (m : ℝ) : ℝ) : ℂ) *
      Complex.exp (-Complex.I * ((Real.log (m : ℝ) * t : ℝ) : ℂ)) *
      (((divFn n / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((Real.log (n : ℝ) * t : ℝ) : ℂ))) =
      (((divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ)) : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * ((Real.log (m : ℝ) * t : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((Real.log (n : ℝ) * t : ℝ) : ℂ))) by push_cast; ring]
  rw [hexp, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]
  congr 1; push_cast; ring

private lemma dirTerm_mul_dirTerm {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (t : ℝ) :
    dirTerm m t * dirTerm n t =
      ((divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((Real.log ((m * n : ℕ) : ℝ) * t : ℝ) : ℂ)) := by
  rw [dirTerm_eq_exp hm, dirTerm_eq_exp hn]
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hexp : Complex.exp (-Complex.I * ((Real.log (m : ℝ) * t : ℝ) : ℂ)) *
      Complex.exp (-Complex.I * ((Real.log (n : ℝ) * t : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * ((Real.log ((m * n : ℕ) : ℝ) * t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, Nat.cast_mul, Real.log_mul hm_pos.ne' hn_pos.ne']
    congr 1; push_cast; ring
  rw [show ((divFn m / Real.sqrt (m : ℝ) : ℝ) : ℂ) *
      Complex.exp (-Complex.I * ((Real.log (m : ℝ) * t : ℝ) : ℂ)) *
      (((divFn n / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((Real.log (n : ℝ) * t : ℝ) : ℂ))) =
      (((divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ)) : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * ((Real.log (m : ℝ) * t : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ((Real.log (n : ℝ) * t : ℝ) : ℂ))) by push_cast; ring]
  rw [hexp, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]
  congr 1; push_cast; ring

private lemma dirTerm_diag_re {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (dirTerm n t * star (dirTerm n t)).re = divFn n ^ 2 / (n : ℝ) := by
  rw [dirTerm_mul_star hn hn t]
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [sub_self, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    Complex.ofReal_re]
  rw [Nat.cast_mul, Real.sqrt_mul_self hn_nn, sq]

private lemma intervalIntegrable_indicator_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Continuous f) (a c T : ℝ) (hcT : c ≤ T) :
    IntervalIntegrable (Set.indicator (Set.Ici a) f) volume c T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcT]
  exact (hf.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    measurableSet_Ici

private lemma intervalIntegrable_finsetSum' {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (f : ι → ℝ → E) {a b : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun t => ∑ i ∈ s, f i t) volume a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [intervalIntegrable_const]
  | insert i s hi ih =>
    have hsum_eq : (fun t => ∑ j ∈ insert i s, f j t) = fun t => f i t + ∑ j ∈ s, f j t := by
      ext t; exact Finset.sum_insert hi
    rw [hsum_eq]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private lemma intervalIntegral_indicator_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (_hf : Continuous f) {a c T : ℝ} (hcT : c ≤ T) (haT : a ≤ T) :
    ∫ t in c..T, Set.indicator (Set.Ici a) f t = ∫ t in (max c a)..T, f t := by
  have hmax : max c a ≤ T := max_le hcT haT
  rw [intervalIntegral.integral_of_le hcT, intervalIntegral.integral_of_le hmax,
    MeasureTheory.setIntegral_indicator measurableSet_Ici]
  refine MeasureTheory.setIntegral_congr_set ?_
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ a := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne] with t ht
  rw [eq_iff_iff]
  change t ∈ Set.Ioc c T ∩ Set.Ici a ↔ t ∈ Set.Ioc (max c a) T
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, max_lt_iff]
  constructor
  · rintro ⟨⟨hct, htT⟩, hat⟩
    exact ⟨⟨hct, lt_of_le_of_ne hat ht.symm⟩, htT⟩
  · rintro ⟨⟨hct, hat⟩, htT⟩
    exact ⟨⟨hct, htT⟩, hat.le⟩

private lemma dirPoly_eq_sum_indicator {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    dirPoly t = ∑ n ∈ Finset.Icc 1 ⌊T / (2 * Real.pi)⌋₊,
      Set.indicator (Set.Ici (2 * Real.pi * (n : ℝ))) (dirTerm n) t := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsub : Finset.Icc 1 ⌊t / (2 * Real.pi)⌋₊ ⊆ Finset.Icc 1 ⌊T / (2 * Real.pi)⌋₊ := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.floor_mono (div_le_div_of_nonneg_right htT h2pi.le))⟩
  unfold dirPoly
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : n ≤ ⌊t / (2 * Real.pi)⌋₊ := (Finset.mem_Icc.mp hn).2
    have hle : (n : ℝ) ≤ t / (2 * Real.pi) := (Nat.le_floor_iff (div_nonneg ht0 h2pi.le)).mp hn2
    have hmem : t ∈ Set.Ici (2 * Real.pi * (n : ℝ)) := by
      rw [Set.mem_Ici]
      have := (le_div_iff₀ h2pi).mp hle
      linarith
    rw [Set.indicator_of_mem hmem]
  · intro n _ hnot
    have hgt : ⌊t / (2 * Real.pi)⌋₊ < n := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
      rcases hnot with h1 | h2
      · exfalso; have := (Finset.mem_Icc.mp ‹_›).1; omega
      · exact h2
    have hnotmem : t ∉ Set.Ici (2 * Real.pi * (n : ℝ)) := by
      rw [Set.mem_Ici, not_le]
      have hlt : t / (2 * Real.pi) < (n : ℝ) :=
        lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast hgt)
      have := (div_lt_iff₀ h2pi).mp hlt
      linarith
    rw [Set.indicator_of_notMem hnotmem]

private lemma diagSum_eq_sum_indicator {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    diagSum t = ∑ n ∈ Finset.Icc 1 ⌊T / (2 * Real.pi)⌋₊,
      Set.indicator (Set.Ici (2 * Real.pi * (n : ℝ))) (fun _ => divFn n ^ 2 / (n : ℝ)) t := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsub : Finset.Icc 1 ⌊t / (2 * Real.pi)⌋₊ ⊆ Finset.Icc 1 ⌊T / (2 * Real.pi)⌋₊ := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.floor_mono (div_le_div_of_nonneg_right htT h2pi.le))⟩
  unfold diagSum
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : n ≤ ⌊t / (2 * Real.pi)⌋₊ := (Finset.mem_Icc.mp hn).2
    have hle : (n : ℝ) ≤ t / (2 * Real.pi) := (Nat.le_floor_iff (div_nonneg ht0 h2pi.le)).mp hn2
    have hmem : t ∈ Set.Ici (2 * Real.pi * (n : ℝ)) := by
      rw [Set.mem_Ici]
      have := (le_div_iff₀ h2pi).mp hle
      linarith
    rw [Set.indicator_of_mem hmem]
  · intro n _ hnot
    have hgt : ⌊t / (2 * Real.pi)⌋₊ < n := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
      rcases hnot with h1 | h2
      · exfalso; have := (Finset.mem_Icc.mp ‹_›).1; omega
      · exact h2
    have hnotmem : t ∉ Set.Ici (2 * Real.pi * (n : ℝ)) := by
      rw [Set.mem_Ici, not_le]
      have hlt : t / (2 * Real.pi) < (n : ℝ) :=
        lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast hgt)
      have := (div_lt_iff₀ h2pi).mp hlt
      linarith
    rw [Set.indicator_of_notMem hnotmem]

private lemma indicator_Ici_mul_indicator_Ici {a b : ℝ} (f g : ℝ → ℂ) (t : ℝ) :
    Set.indicator (Set.Ici a) f t * Set.indicator (Set.Ici b) g t =
      Set.indicator (Set.Ici (max a b)) (fun u => f u * g u) t := by
  by_cases ha : a ≤ t <;> by_cases hb : b ≤ t
  · have hmax : max a b ≤ t := max_le ha hb
    simp [Set.indicator, Set.mem_Ici, ha, hb, hmax]
  · have hmax : ¬ (max a b ≤ t) := fun h => hb ((le_max_right a b).trans h)
    simp [Set.indicator, Set.mem_Ici, ha, hb, hmax]
  · have hmax : ¬ (max a b ≤ t) := fun h => ha ((le_max_left a b).trans h)
    simp [Set.indicator, Set.mem_Ici, ha, hb, hmax]
  · have hmax : ¬ (max a b ≤ t) := fun h => ha ((le_max_left a b).trans h)
    simp [Set.indicator, Set.mem_Ici, ha, hb, hmax]

private lemma intervalIntegrable_dirPoly {c T : ℝ} (hc0 : 0 ≤ c) (hcT : c ≤ T) :
    IntervalIntegrable dirPoly volume c T := by
  set N := ⌊T / (2 * Real.pi)⌋₊
  have hsum : IntervalIntegrable
      (fun t => ∑ n ∈ Finset.Icc 1 N, Set.indicator (Set.Ici (2 * Real.pi * (n : ℝ))) (dirTerm n) t)
      volume c T := by
    refine intervalIntegrable_finsetSum' (Finset.Icc 1 N) _ fun n hn => ?_
    exact intervalIntegrable_indicator_Ici (continuous_dirTerm (Finset.mem_Icc.mp hn).1) _ c T hcT
  refine hsum.congr_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_)
  rw [Set.uIoc_of_le hcT] at ht
  exact (dirPoly_eq_sum_indicator (hc0.trans ht.1.le) ht.2).symm

private lemma norm_sq_eq_mul_star_re (z : ℂ) : ‖z‖ ^ 2 = (z * star z).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re]
  simp

private lemma intervalIntegrable_norm_sq_dirPoly {c T : ℝ} (hc0 : 0 ≤ c) (hcT : c ≤ T) :
    IntervalIntegrable (fun t => ‖dirPoly t‖ ^ 2) volume c T := by
  set N := ⌊T / (2 * Real.pi)⌋₊
  have hsum : IntervalIntegrable
      (fun t => ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        Set.indicator (Set.Ici (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))
          (fun u => (dirTerm m u * star (dirTerm n u)).re) t) volume c T := by
    refine intervalIntegrable_finsetSum' (Finset.Icc 1 N) _ fun m hm =>
      intervalIntegrable_finsetSum' (Finset.Icc 1 N) _ fun n hn => ?_
    have hcont : Continuous (fun u => (dirTerm m u * star (dirTerm n u)).re) :=
      Complex.continuous_re.comp ((continuous_dirTerm (Finset.mem_Icc.mp hm).1).mul
        (continuous_star.comp (continuous_dirTerm (Finset.mem_Icc.mp hn).1)))
    exact intervalIntegrable_indicator_Ici hcont _ c T hcT
  refine hsum.congr_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_)
  rw [Set.uIoc_of_le hcT] at ht
  dsimp only
  have hD := dirPoly_eq_sum_indicator (hc0.trans ht.1.le) ht.2
  rw [norm_sq_eq_mul_star_re, hD, star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  have hstar : star (Set.indicator (Set.Ici (2 * Real.pi * (n : ℝ))) (dirTerm n) t) =
      Set.indicator (Set.Ici (2 * Real.pi * (n : ℝ))) (fun u => star (dirTerm n u)) t := by
    by_cases h : t ∈ Set.Ici (2 * Real.pi * (n : ℝ)) <;> simp [Set.indicator, h]
  rw [hstar, indicator_Ici_mul_indicator_Ici]
  by_cases h : t ∈ Set.Ici (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))) <;>
    simp [Set.indicator, h]

private lemma intervalIntegrable_cross {c T : ℝ} (hc0 : 0 ≤ c) (hcT : c ≤ T) :
    IntervalIntegrable (fun t => (star (chi2 t) * dirPoly t ^ 2).re) volume c T := by
  set N := ⌊T / (2 * Real.pi)⌋₊
  have hsum : IntervalIntegrable
      (fun t => ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        Set.indicator (Set.Ici (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))
          (fun u => (star (chi2 u) * (dirTerm m u * dirTerm n u)).re) t) volume c T := by
    refine intervalIntegrable_finsetSum' (Finset.Icc 1 N) _ fun m hm =>
      intervalIntegrable_finsetSum' (Finset.Icc 1 N) _ fun n hn => ?_
    have hcont : Continuous (fun u => (star (chi2 u) * (dirTerm m u * dirTerm n u)).re) :=
      Complex.continuous_re.comp ((continuous_star.comp continuous_chi2).mul
        ((continuous_dirTerm (Finset.mem_Icc.mp hm).1).mul
          (continuous_dirTerm (Finset.mem_Icc.mp hn).1)))
    exact intervalIntegrable_indicator_Ici hcont _ c T hcT
  refine hsum.congr_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_)
  rw [Set.uIoc_of_le hcT] at ht
  dsimp only
  have hD := dirPoly_eq_sum_indicator (hc0.trans ht.1.le) ht.2
  rw [hD, sq, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [indicator_Ici_mul_indicator_Ici]
  by_cases h : t ∈ Set.Ici (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))) <;>
    simp [Set.indicator, h]

private lemma intervalIntegrable_diagSum {c T : ℝ} (hc0 : 0 ≤ c) (hcT : c ≤ T) :
    IntervalIntegrable diagSum volume c T := by
  set N := ⌊T / (2 * Real.pi)⌋₊
  have hsum : IntervalIntegrable
      (fun t => ∑ n ∈ Finset.Icc 1 N,
        Set.indicator (Set.Ici (2 * Real.pi * (n : ℝ))) (fun _ => divFn n ^ 2 / (n : ℝ)) t)
      volume c T := by
    refine intervalIntegrable_finsetSum' (Finset.Icc 1 N) _ fun n _ => ?_
    exact intervalIntegrable_indicator_Ici continuous_const _ c T hcT
  refine hsum.congr_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_)
  rw [Set.uIoc_of_le hcT] at ht
  exact (diagSum_eq_sum_indicator (hc0.trans ht.1.le) ht.2).symm

private lemma main_identity_decomp {T₀ T : ℝ} (hT₀ : 0 ≤ T₀) (hT : T₀ ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖modelM t‖ ^ 2) - 2 * (∫ t in (0 : ℝ)..T, diagSum t) =
      2 * (∑ m ∈ Finset.Icc 1 ⌊T / (2 * Real.pi)⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T / (2 * Real.pi)⌋₊,
        if m ≠ n then
          ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
            (dirTerm m t * star (dirTerm n t)).re
        else 0) +
      2 * (∫ t in (0 : ℝ)..T₀, (star (chi2 t) * dirPoly t ^ 2).re) +
      2 * (∑ m ∈ Finset.Icc 1 ⌊T / (2 * Real.pi)⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T / (2 * Real.pi)⌋₊,
        ∫ t in (max T₀ (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
          (star (chi2 t) * (dirTerm m t * dirTerm n t)).re) := by
  have hT_nn : 0 ≤ T := hT₀.trans hT
  set N := ⌊T / (2 * Real.pi)⌋₊
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hM_eq : (fun t => ‖modelM t‖ ^ 2) = fun t =>
      2 * ‖dirPoly t‖ ^ 2 + 2 * (star (chi2 t) * dirPoly t ^ 2).re :=
    funext norm_sq_modelM
  have hint_D := intervalIntegrable_norm_sq_dirPoly le_rfl hT_nn
  have hint_C := intervalIntegrable_cross le_rfl hT_nn
  have hint_diag := intervalIntegrable_diagSum le_rfl hT_nn
  rw [hM_eq, intervalIntegral.integral_add (hint_D.const_mul 2) (hint_C.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- Split cross term at T₀
  have hC_split : (∫ t in (0 : ℝ)..T, (star (chi2 t) * dirPoly t ^ 2).re) =
      (∫ t in (0 : ℝ)..T₀, (star (chi2 t) * dirPoly t ^ 2).re) +
      (∫ t in T₀..T, (star (chi2 t) * dirPoly t ^ 2).re) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cross le_rfl hT₀) (intervalIntegrable_cross hT₀ hT)).symm
  -- Rewrite off-diagonal: ∫_0^T ‖dirPoly‖^2 - ∫_0^T diagSum
  have hOff : (∫ t in (0 : ℝ)..T, ‖dirPoly t‖ ^ 2) - (∫ t in (0 : ℝ)..T, diagSum t) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        if m ≠ n then
          ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
            (dirTerm m t * star (dirTerm n t)).re
        else 0 := by
    rw [← intervalIntegral.integral_sub hint_D hint_diag]
    have hcongr : ∫ t in (0 : ℝ)..T, (‖dirPoly t‖ ^ 2 - diagSum t) =
        ∫ t in (0 : ℝ)..T, ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if m ≠ n then
            Set.indicator (Set.Ici (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))
              (fun u => (dirTerm m u * star (dirTerm n u)).re) t
          else 0 := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Set.uIoc_of_le hT_nn] at ht
      have hD := dirPoly_eq_sum_indicator ht.1.le ht.2
      have hdiag := diagSum_eq_sum_indicator ht.1.le ht.2
      rw [norm_sq_eq_mul_star_re, hD, star_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum, Complex.re_sum]
      rw [hdiag, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hsplit_n : (∑ n ∈ Finset.Icc 1 N,
            (Set.indicator (Set.Ici (2 * Real.pi * (m : ℝ))) (dirTerm m) t *
              star (Set.indicator (Set.Ici (2 * Real.pi * (n : ℝ))) (dirTerm n) t)).re) -
          Set.indicator (Set.Ici (2 * Real.pi * (m : ℝ))) (fun _ => divFn m ^ 2 / (m : ℝ)) t =
          ∑ n ∈ Finset.Icc 1 N, if m ≠ n then
            Set.indicator (Set.Ici (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))
              (fun u => (dirTerm m u * star (dirTerm n u)).re) t
          else 0 := by
        rw [← Finset.add_sum_erase _ _ hm]
        have hdiag_term :
            (Set.indicator (Set.Ici (2 * Real.pi * (m : ℝ))) (dirTerm m) t *
              star (Set.indicator (Set.Ici (2 * Real.pi * (m : ℝ))) (dirTerm m) t)).re =
            Set.indicator (Set.Ici (2 * Real.pi * (m : ℝ))) (fun _ => divFn m ^ 2 / (m : ℝ)) t := by
          by_cases hmem : t ∈ Set.Ici (2 * Real.pi * (m : ℝ))
          · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
            exact dirTerm_diag_re (Finset.mem_Icc.mp hm).1 t
          · simp [Set.indicator, hmem]
        rw [hdiag_term, add_sub_cancel_left]
        rw [← Finset.add_sum_erase _ _ hm]
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hne : m ≠ n := (Finset.mem_erase.mp hn).1.symm
        rw [if_pos hne]
        have hstar : star (Set.indicator (Set.Ici (2 * Real.pi * (n : ℝ))) (dirTerm n) t) =
            Set.indicator (Set.Ici (2 * Real.pi * (n : ℝ))) (fun u => star (dirTerm n u)) t := by
          by_cases h : t ∈ Set.Ici (2 * Real.pi * (n : ℝ)) <;> simp [Set.indicator, h]
        rw [hstar, indicator_Ici_mul_indicator_Ici]
        by_cases h : t ∈ Set.Ici (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))) <;>
          simp [Set.indicator, h]
      exact hsplit_n
    rw [hcongr]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun n hn => ?_
        by_cases hmn : m ≠ n
        · simp only [if_pos hmn]
          have hcont : Continuous (fun u => (dirTerm m u * star (dirTerm n u)).re) :=
            Complex.continuous_re.comp ((continuous_dirTerm (Finset.mem_Icc.mp hm).1).mul
              (continuous_star.comp (continuous_dirTerm (Finset.mem_Icc.mp hn).1)))
          have hmT : 2 * Real.pi * (m : ℝ) ≤ T := by
            have h1 : (m : ℝ) ≤ T / (2 * Real.pi) :=
              (Nat.le_floor_iff (div_nonneg hT_nn h2pi.le)).mp (Finset.mem_Icc.mp hm).2
            linarith [(le_div_iff₀ h2pi).mp h1]
          have hnT : 2 * Real.pi * (n : ℝ) ≤ T := by
            have h1 : (n : ℝ) ≤ T / (2 * Real.pi) :=
              (Nat.le_floor_iff (div_nonneg hT_nn h2pi.le)).mp (Finset.mem_Icc.mp hn).2
            linarith [(le_div_iff₀ h2pi).mp h1]
          rw [intervalIntegral_indicator_Ici hcont hT_nn (max_le hmT hnT)]
          have hmax0 : max (0 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))) =
              max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)) :=
            max_eq_right (le_trans (by positivity) (le_max_left _ _))
          rw [hmax0]
        · simp [hmn]
      · intro n hn
        by_cases hmn : m ≠ n
        · simp only [if_pos hmn]
          have hcont : Continuous (fun u => (dirTerm m u * star (dirTerm n u)).re) :=
            Complex.continuous_re.comp ((continuous_dirTerm (Finset.mem_Icc.mp hm).1).mul
              (continuous_star.comp (continuous_dirTerm (Finset.mem_Icc.mp hn).1)))
          exact intervalIntegrable_indicator_Ici hcont _ 0 T hT_nn
        · simp [hmn]
    · intro m hm
      refine intervalIntegrable_finsetSum' (Finset.Icc 1 N) _ fun n hn => ?_
      by_cases hmn : m ≠ n
      · simp only [if_pos hmn]
        have hcont : Continuous (fun u => (dirTerm m u * star (dirTerm n u)).re) :=
          Complex.continuous_re.comp ((continuous_dirTerm (Finset.mem_Icc.mp hm).1).mul
            (continuous_star.comp (continuous_dirTerm (Finset.mem_Icc.mp hn).1)))
        exact intervalIntegrable_indicator_Ici hcont _ 0 T hT_nn
      · simp [hmn]
  -- Rewrite cross term on [T₀, T]
  have hCross : (∫ t in T₀..T, (star (chi2 t) * dirPoly t ^ 2).re) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ∫ t in (max T₀ (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
          (star (chi2 t) * (dirTerm m t * dirTerm n t)).re := by
    have hcongr : ∫ t in T₀..T, (star (chi2 t) * dirPoly t ^ 2).re =
        ∫ t in T₀..T, ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          Set.indicator (Set.Ici (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))
            (fun u => (star (chi2 u) * (dirTerm m u * dirTerm n u)).re) t := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Set.uIoc_of_le hT] at ht
      have hD := dirPoly_eq_sum_indicator (hT₀.trans ht.1.le) ht.2
      rw [hD, sq, Finset.sum_mul, Finset.mul_sum]
      simp_rw [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      rw [indicator_Ici_mul_indicator_Ici]
      by_cases h : t ∈ Set.Ici (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))) <;>
        simp [Set.indicator, h]
    rw [hcongr]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun n hn => ?_
        have hcont : Continuous (fun u => (star (chi2 u) * (dirTerm m u * dirTerm n u)).re) :=
          Complex.continuous_re.comp ((continuous_star.comp continuous_chi2).mul
            ((continuous_dirTerm (Finset.mem_Icc.mp hm).1).mul
              (continuous_dirTerm (Finset.mem_Icc.mp hn).1)))
        have hmT : 2 * Real.pi * (m : ℝ) ≤ T := by
          have h1 : (m : ℝ) ≤ T / (2 * Real.pi) :=
            (Nat.le_floor_iff (div_nonneg hT_nn h2pi.le)).mp (Finset.mem_Icc.mp hm).2
          linarith [(le_div_iff₀ h2pi).mp h1]
        have hnT : 2 * Real.pi * (n : ℝ) ≤ T := by
          have h1 : (n : ℝ) ≤ T / (2 * Real.pi) :=
            (Nat.le_floor_iff (div_nonneg hT_nn h2pi.le)).mp (Finset.mem_Icc.mp hn).2
          linarith [(le_div_iff₀ h2pi).mp h1]
        exact intervalIntegral_indicator_Ici hcont hT (max_le hmT hnT)
      · intro n hn
        have hcont : Continuous (fun u => (star (chi2 u) * (dirTerm m u * dirTerm n u)).re) :=
          Complex.continuous_re.comp ((continuous_star.comp continuous_chi2).mul
            ((continuous_dirTerm (Finset.mem_Icc.mp hm).1).mul
              (continuous_dirTerm (Finset.mem_Icc.mp hn).1)))
        exact intervalIntegrable_indicator_Ici hcont _ T₀ T hT
    · intro m hm
      refine intervalIntegrable_finsetSum' (Finset.Icc 1 N) _ fun n hn => ?_
      have hcont : Continuous (fun u => (star (chi2 u) * (dirTerm m u * dirTerm n u)).re) :=
        Complex.continuous_re.comp ((continuous_star.comp continuous_chi2).mul
          ((continuous_dirTerm (Finset.mem_Icc.mp hm).1).mul
            (continuous_dirTerm (Finset.mem_Icc.mp hn).1)))
      exact intervalIntegrable_indicator_Ici hcont _ T₀ T hT
  rw [hC_split, hCross]
  linarith [hOff]

/- ### Section 3: Analytic Bounds for `digamma(1/4 + i t/2)` via Euler Limit Formula -/

private def halfPlane : Set ℂ := {s : ℂ | 0 < s.re}

private lemma isOpen_halfPlane : IsOpen halfPlane :=
  Complex.continuous_re.isOpen_preimage _ isOpen_Ioi

private lemma GammaSeq_eq_indicator_integral {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    Complex.GammaSeq s n =
      ∫ x in Set.Ioi (0 : ℝ),
        Set.indicator (Set.Ioc 0 (n : ℝ))
          (fun x : ℝ => (((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) x := by
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hs hn,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (Nat.cast_nonneg n),
    Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self]

private lemma GammaSeq_integrand_integrableOn {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn
      (Set.indicator (Set.Ioc 0 (n : ℝ))
        (fun x : ℝ => (((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)))
      (Set.Ioi (0 : ℝ)) volume := by
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
    Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self, ← IntegrableOn,
    ← intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)]
  apply IntervalIntegrable.continuousOn_mul
  · refine intervalIntegral.intervalIntegrable_cpow' ?_
    simp [hs]
  · fun_prop

private lemma Gamma_sub_GammaSeq_norm_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {s : ℂ} (hsa : a ≤ s.re) (hsb : s.re ≤ b) {n : ℕ} (hn : n ≠ 0) :
    ‖Complex.Gamma s - Complex.GammaSeq s n‖ ≤
      (Complex.Gamma (a : ℂ) - Complex.GammaSeq (a : ℂ) n).re +
      (Complex.Gamma (b : ℂ) - Complex.GammaSeq (b : ℂ) n).re := by
  have hs : 0 < s.re := lt_of_lt_of_le ha hsa
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let gn : ℝ → ℝ := fun x =>
    Real.exp (-x) - Set.indicator (Set.Ioc 0 (n : ℝ)) (fun u => (1 - u / (n : ℝ)) ^ n) x
  have hgn_nn : ∀ x : ℝ, 0 < x → 0 ≤ gn x := by
    intro x hx
    dsimp [gn]
    by_cases hxn : x ≤ (n : ℝ)
    · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hxn⟩)]
      linarith [Real.one_sub_div_pow_le_exp_neg hxn]
    · rw [Set.indicator_of_notMem (fun h => hxn h.2), sub_zero]
      exact (Real.exp_pos _).le
  have hsub_eq : ∀ {z : ℂ} (hz : 0 < z.re),
      Complex.Gamma z - Complex.GammaSeq z n =
        ∫ x in Set.Ioi (0 : ℝ), (gn x : ℂ) * (x : ℂ) ^ (z - 1) := by
    intro z hz
    rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, GammaSeq_eq_indicator_integral hz hn,
      ← MeasureTheory.integral_sub (Complex.GammaIntegral_convergent hz)
        (GammaSeq_integrand_integrableOn hz n)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    dsimp [gn]
    by_cases hxn : x ≤ (n : ℝ)
    · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hxn⟩),
        Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hxn⟩)]
      push_cast; ring
    · rw [Set.indicator_of_notMem (fun h => hxn h.2),
        Set.indicator_of_notMem (fun h => hxn h.2)]
      simp
  have hreal_int : ∀ {r : ℝ} (hr : 0 < r),
      IntegrableOn (fun x : ℝ => gn x * x ^ (r - 1)) (Set.Ioi (0 : ℝ)) volume ∧
      (Complex.Gamma (r : ℂ) - Complex.GammaSeq (r : ℂ) n).re =
        ∫ x in Set.Ioi (0 : ℝ), gn x * x ^ (r - 1) := by
    intro r hr
    have hrC : 0 < (r : ℂ).re := by simpa using hr
    have hEq := hsub_eq hrC
    have hintC : IntegrableOn (fun x : ℝ => (gn x : ℂ) * (x : ℂ) ^ ((r : ℂ) - 1))
        (Set.Ioi (0 : ℝ)) volume := by
      refine ((Complex.GammaIntegral_convergent hrC).sub
        (GammaSeq_integrand_integrableOn hrC n)).congr_fun ?_ measurableSet_Ioi
      intro x hx
      dsimp [gn]
      by_cases hxn : x ≤ (n : ℝ)
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hxn⟩),
          Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hxn⟩)]
        push_cast; ring
      · rw [Set.indicator_of_notMem (fun h => hxn h.2),
          Set.indicator_of_notMem (fun h => hxn h.2)]
        simp
    have hfun : Set.EqOn (fun x : ℝ => (gn x : ℂ) * (x : ℂ) ^ ((r : ℂ) - 1))
        (fun x : ℝ => ((gn x * x ^ (r - 1) : ℝ) : ℂ)) (Set.Ioi (0 : ℝ)) := by
      intro x hx
      dsimp only
      rw [show (r : ℂ) - 1 = ((r - 1 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_cpow (Set.mem_Ioi.mp hx).le, Complex.ofReal_mul]
    have hintC' : IntegrableOn (fun x : ℝ => ((gn x * x ^ (r - 1) : ℝ) : ℂ))
        (Set.Ioi (0 : ℝ)) volume :=
      hintC.congr_fun hfun measurableSet_Ioi
    have hintR : IntegrableOn (fun x : ℝ => gn x * x ^ (r - 1)) (Set.Ioi (0 : ℝ)) volume := by
      change Integrable (fun x : ℝ => gn x * x ^ (r - 1)) (volume.restrict (Set.Ioi (0 : ℝ)))
      simpa only [RCLike.re_to_complex, Complex.ofReal_re] using hintC'.re
    refine ⟨hintR, ?_⟩
    rw [hEq, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hfun]
    have hre_comm := Complex.reCLM.integral_comp_comm hintC'
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using hre_comm.symm
  obtain ⟨hIntA, hReA⟩ := hreal_int ha
  obtain ⟨hIntB, hReB⟩ := hreal_int hb
  rw [hsub_eq hs, hReA, hReB, ← MeasureTheory.integral_add hIntA hIntB]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hint_norm : IntegrableOn (fun x : ℝ => ‖(gn x : ℂ) * (x : ℂ) ^ (s - 1)‖)
      (Set.Ioi (0 : ℝ)) volume := by
    have hC : IntegrableOn (fun x : ℝ => (gn x : ℂ) * (x : ℂ) ^ (s - 1))
        (Set.Ioi (0 : ℝ)) volume := by
      refine ((Complex.GammaIntegral_convergent hs).sub
        (GammaSeq_integrand_integrableOn hs n)).congr_fun ?_ measurableSet_Ioi
      intro x hx
      dsimp [gn]
      by_cases hxn : x ≤ (n : ℝ)
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hxn⟩),
          Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hxn⟩)]
        push_cast; ring
      · rw [Set.indicator_of_notMem (fun h => hxn h.2),
          Set.indicator_of_notMem (fun h => hxn h.2)]
        simp
    exact hC.norm
  refine MeasureTheory.setIntegral_mono_on hint_norm (hIntA.add hIntB) measurableSet_Ioi fun x hx => ?_
  have hx_pos : 0 < x := Set.mem_Ioi.mp hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgn_nn x hx_pos),
    Complex.norm_cpow_eq_rpow_re_of_pos hx_pos, Complex.sub_re, Complex.one_re, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hgn_nn x hx_pos)
  rcases le_or_gt x 1 with hx1 | hx1
  · have hle : x ^ (s.re - 1) ≤ x ^ (a - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx_pos hx1 (by linarith)
    linarith [Real.rpow_nonneg hx_pos.le (b - 1)]
  · have hle : x ^ (s.re - 1) ≤ x ^ (b - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith [Real.rpow_nonneg hx_pos.le (a - 1)]

private lemma tendstoLocallyUniformlyOn_GammaSeq :
    TendstoLocallyUniformlyOn (fun n s => Complex.GammaSeq s n) Complex.Gamma atTop halfPlane := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_halfPlane]
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp [TendstoUniformlyOn]
  obtain ⟨sMin, hsMinK, hsMin⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  obtain ⟨sMax, hsMaxK, hsMax⟩ := hK.exists_isMaxOn hKne Complex.continuous_re.continuousOn
  set a := sMin.re
  set b := sMax.re
  have ha : 0 < a := hKU hsMinK
  have hab : a ≤ b := hsMin hsMaxK
  have htendA : Tendsto (fun n => (Complex.Gamma (a : ℂ) - Complex.GammaSeq (a : ℂ) n).re)
      atTop (𝓝 0) := by
    have h1 := (Complex.GammaSeq_tendsto_Gamma (a : ℂ)).const_sub (Complex.Gamma (a : ℂ))
    rw [sub_self] at h1
    simpa only [Function.comp_def, Complex.zero_re] using (Complex.continuous_re.tendsto 0).comp h1
  have htendB : Tendsto (fun n => (Complex.Gamma (b : ℂ) - Complex.GammaSeq (b : ℂ) n).re)
      atTop (𝓝 0) := by
    have h1 := (Complex.GammaSeq_tendsto_Gamma (b : ℂ)).const_sub (Complex.Gamma (b : ℂ))
    rw [sub_self] at h1
    simpa only [Function.comp_def, Complex.zero_re] using (Complex.continuous_re.tendsto 0).comp h1
  have htendSum : Tendsto
      (fun n => (Complex.Gamma (a : ℂ) - Complex.GammaSeq (a : ℂ) n).re +
        (Complex.Gamma (b : ℂ) - Complex.GammaSeq (b : ℂ) n).re) atTop (𝓝 0) := by
    simpa using htendA.add htendB
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev := htendSum.eventually (Iio_mem_nhds hε)
  filter_upwards [hev, eventually_ne_atTop 0] with n hn_lt hn0 s hsK
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (Gamma_sub_GammaSeq_norm_le ha hab (hsMin hsK) (hsMax hsK) hn0) hn_lt

private noncomputable def psiSeq (n : ℕ) (s : ℂ) : ℂ :=
  ((Real.log (n : ℝ) : ℝ) : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹

private lemma differentiableOn_GammaSeq {n : ℕ} (hn : n ≠ 0) :
    DifferentiableOn ℂ (fun s => Complex.GammaSeq s n) halfPlane := by
  intro s hs
  unfold Complex.GammaSeq
  have hprod_ne : (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j _ h0
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
    have : (0 : ℝ) < s.re := hs
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hnum : DifferentiableAt ℂ (fun z : ℂ => (n : ℂ) ^ z * (Nat.factorial n : ℂ)) s := by
    refine (DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (Nat.cast_ne_zero.mpr hn))).mul (differentiableAt_const _)
  have hden : DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ Finset.range (n + 1), (z + (j : ℂ))) s := by
    induction (n + 1) with
    | zero => simp [differentiableAt_const]
    | succ k ih =>
      simp_rw [Finset.prod_range_succ]
      exact ih.mul (differentiableAt_id.add (differentiableAt_const _))
  exact (hnum.div hden hprod_ne).differentiableWithinAt

private lemma logDeriv_GammaSeq {n : ℕ} (hn : n ≠ 0) {s : ℂ} (hs : s ∈ halfPlane) :
    logDeriv (fun z => Complex.GammaSeq z n) s = psiSeq n s := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfacC : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hpow_ne : (n : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnC]
    exact Complex.exp_ne_zero _
  have hfac_ne : ∀ j ∈ Finset.range (n + 1), s + (j : ℂ) ≠ 0 := by
    intro j _ h0
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
    have : (0 : ℝ) < s.re := hs
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hprod_ne : (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac_ne
  have hpow_diff : DifferentiableAt ℂ (fun z : ℂ => (n : ℂ) ^ z) s :=
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl hnC)
  have hprod_diff : DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ Finset.range (n + 1), (z + (j : ℂ))) s := by
    induction (n + 1) with
    | zero => simp [differentiableAt_const]
    | succ k ih =>
      simp_rw [Finset.prod_range_succ]
      exact ih.mul (differentiableAt_id.add (differentiableAt_const _))
  have hnum_diff : DifferentiableAt ℂ (fun z : ℂ => (n : ℂ) ^ z * (Nat.factorial n : ℂ)) s :=
    hpow_diff.mul (differentiableAt_const _)
  have hdiv := logDeriv_div
    (f := fun z : ℂ => (n : ℂ) ^ z * (Nat.factorial n : ℂ))
    (g := fun z : ℂ => ∏ j ∈ Finset.range (n + 1), (z + (j : ℂ)))
    s (mul_ne_zero hpow_ne hfacC) hprod_ne hnum_diff hprod_diff
  change logDeriv (fun z => (n : ℂ) ^ z * (Nat.factorial n : ℂ) /
    ∏ j ∈ Finset.range (n + 1), (z + (j : ℂ))) s = psiSeq n s
  rw [hdiv, logDeriv_mul_const (f := fun z : ℂ => (n : ℂ) ^ z) s (Nat.factorial n : ℂ) hfacC,
    logDeriv_prod hfac_ne (fun j _ => differentiableAt_id.add (differentiableAt_const _))]
  have hpow_ld : logDeriv (fun z : ℂ => (n : ℂ) ^ z) s = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun z : ℂ => (n : ℂ) ^ z) ((n : ℂ) ^ s * Complex.log (n : ℂ)) s := by
      simpa using (hasDerivAt_id s).const_cpow (Or.inl hnC)
    rw [hd.deriv, mul_div_cancel_left₀ _ hpow_ne, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log (Nat.cast_nonneg n)]
  have hterm : ∀ j ∈ Finset.range (n + 1),
      logDeriv (fun z : ℂ => z + (j : ℂ)) s = (s + (j : ℂ))⁻¹ := by
    intro j _
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun z : ℂ => z + (j : ℂ)) 1 s := by
      simpa using (hasDerivAt_id s).add_const (j : ℂ)
    rw [hd.deriv, one_div]
  rw [hpow_ld, Finset.sum_congr rfl hterm]
  rfl

private lemma tendstoLocallyUniformlyOn_psiSeq :
    TendstoLocallyUniformlyOn psiSeq Complex.digamma atTop halfPlane := by
  have hF := tendstoLocallyUniformlyOn_GammaSeq
  have hF_diff : ∀ᶠ n in atTop, DifferentiableOn ℂ (fun s => Complex.GammaSeq s n) halfPlane := by
    filter_upwards [eventually_ne_atTop 0] with n hn using differentiableOn_GammaSeq hn
  have hF' : TendstoLocallyUniformlyOn (fun n s => deriv (fun z => Complex.GammaSeq z n) s)
      (deriv Complex.Gamma) atTop halfPlane :=
    hF.deriv hF_diff isOpen_halfPlane
  have hG_diff : DifferentiableOn ℂ Complex.Gamma halfPlane :=
    hF.differentiableOn hF_diff isOpen_halfPlane
  have hG'_cont : ContinuousOn (deriv Complex.Gamma) halfPlane :=
    hF'.continuousOn (Filter.Eventually.frequently (by
      filter_upwards [hF_diff] with n hn
      exact (hn.deriv isOpen_halfPlane).continuousOn))
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_halfPlane] at hF hF' ⊢
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp [TendstoUniformlyOn]
  have hG_contK : ContinuousOn Complex.Gamma K := hG_diff.continuousOn.mono hKU
  have hG'_contK : ContinuousOn (deriv Complex.Gamma) K := hG'_cont.mono hKU
  obtain ⟨s0, hs0K, hs0Min⟩ := hK.exists_isMinOn hKne (continuous_norm.comp_continuousOn hG_contK)
  obtain ⟨s1, hs1K, hs1Max⟩ := hK.exists_isMaxOn hKne (continuous_norm.comp_continuousOn hG'_contK)
  set δ := ‖Complex.Gamma s0‖
  have hδ : 0 < δ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (hKU hs0K))
  set M := max ‖deriv Complex.Gamma s1‖ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFK := hF K hKU hK
  have hF'K := hF' K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hFK hF'K ⊢
  intro ε hε
  have h1 := hFK (min (δ / 2) (ε * δ ^ 2 / (4 * M))) (lt_min (by positivity) (by positivity))
  have h2 := hF'K (ε * δ / 4) (by positivity)
  filter_upwards [h1, h2, eventually_ne_atTop 0] with n hn1 hn2 hn0 s hsK
  rw [dist_eq_norm, ← logDeriv_GammaSeq hn0 (hKU hsK), Complex.digamma_def,
    logDeriv_apply, logDeriv_apply]
  have hGs_ge : δ ≤ ‖Complex.Gamma s‖ := hs0Min hsK
  have hGs'_le : ‖deriv Complex.Gamma s‖ ≤ M := le_trans (hs1Max hsK) (le_max_left _ _)
  have hdiff_F : ‖Complex.Gamma s - Complex.GammaSeq s n‖ < min (δ / 2) (ε * δ ^ 2 / (4 * M)) := by
    simpa [dist_eq_norm] using hn1 s hsK
  have hdiff_F' : ‖deriv Complex.Gamma s - deriv (fun z => Complex.GammaSeq z n) s‖ < ε * δ / 4 := by
    simpa [dist_eq_norm] using hn2 s hsK
  have hF_ge : δ / 2 ≤ ‖Complex.GammaSeq s n‖ := by
    have htri := norm_sub_norm_le (Complex.Gamma s) (Complex.GammaSeq s n)
    have hlt1 : ‖Complex.Gamma s - Complex.GammaSeq s n‖ < δ / 2 :=
      lt_of_lt_of_le hdiff_F (min_le_left _ _)
    linarith
  have hGs_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (hKU hsK)
  have hFn_ne : Complex.GammaSeq s n ≠ 0 := norm_pos_iff.mp (by linarith)
  have hsub_frac : deriv Complex.Gamma s / Complex.Gamma s -
      deriv (fun z => Complex.GammaSeq z n) s / Complex.GammaSeq s n =
      ((deriv Complex.Gamma s - deriv (fun z => Complex.GammaSeq z n) s) * Complex.Gamma s +
        deriv Complex.Gamma s * (Complex.GammaSeq s n - Complex.Gamma s)) /
      (Complex.Gamma s * Complex.GammaSeq s n) := by
    field_simp [hGs_ne, hFn_ne]
    ring
  rw [hsub_frac, norm_div, norm_mul]
  have hnum_le : ‖(deriv Complex.Gamma s - deriv (fun z => Complex.GammaSeq z n) s) * Complex.Gamma s +
      deriv Complex.Gamma s * (Complex.GammaSeq s n - Complex.Gamma s)‖ ≤
      ‖deriv Complex.Gamma s - deriv (fun z => Complex.GammaSeq z n) s‖ * ‖Complex.Gamma s‖ +
      ‖deriv Complex.Gamma s‖ * ‖Complex.Gamma s - Complex.GammaSeq s n‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_sub_rev (Complex.GammaSeq s n) (Complex.Gamma s)]
  have hden_pos : 0 < ‖Complex.Gamma s‖ * ‖Complex.GammaSeq s n‖ := by
    exact mul_pos (lt_of_lt_of_le hδ hGs_ge) (by linarith)
  have hbound1 : ‖deriv Complex.Gamma s - deriv (fun z => Complex.GammaSeq z n) s‖ * ‖Complex.Gamma s‖ /
      (‖Complex.Gamma s‖ * ‖Complex.GammaSeq s n‖) < ε / 2 := by
    have hGs_pos : 0 < ‖Complex.Gamma s‖ := lt_of_lt_of_le hδ hGs_ge
    rw [mul_comm _ ‖Complex.Gamma s‖, mul_div_mul_left _ _ hGs_pos.ne',
      div_lt_iff₀ (by linarith : 0 < ‖Complex.GammaSeq s n‖)]
    nlinarith
  have hbound2 : ‖deriv Complex.Gamma s‖ * ‖Complex.Gamma s - Complex.GammaSeq s n‖ /
      (‖Complex.Gamma s‖ * ‖Complex.GammaSeq s n‖) < ε / 2 := by
    rw [div_lt_iff₀ hden_pos]
    have hlt2 : ‖Complex.Gamma s - Complex.GammaSeq s n‖ < ε * δ ^ 2 / (4 * M) :=
      lt_of_lt_of_le hdiff_F (min_le_right _ _)
    have hprod_ge : δ * (δ / 2) ≤ ‖Complex.Gamma s‖ * ‖Complex.GammaSeq s n‖ :=
      mul_le_mul hGs_ge hF_ge (by positivity) (by linarith)
    have h1' : M * ‖Complex.Gamma s - Complex.GammaSeq s n‖ < M * (ε * δ ^ 2 / (4 * M)) :=
      mul_lt_mul_of_pos_left hlt2 hM
    have h2' : M * (ε * δ ^ 2 / (4 * M)) = (ε / 2) * (δ * (δ / 2)) := by
      field_simp [hM.ne']; ring
    have h3' : ‖deriv Complex.Gamma s‖ * ‖Complex.Gamma s - Complex.GammaSeq s n‖ ≤
        M * ‖Complex.Gamma s - Complex.GammaSeq s n‖ :=
      mul_le_mul_of_nonneg_right hGs'_le (norm_nonneg _)
    nlinarith
  have hsplit_div : (‖deriv Complex.Gamma s - deriv (fun z => Complex.GammaSeq z n) s‖ * ‖Complex.Gamma s‖ +
      ‖deriv Complex.Gamma s‖ * ‖Complex.Gamma s - Complex.GammaSeq s n‖) /
      (‖Complex.Gamma s‖ * ‖Complex.GammaSeq s n‖) < ε := by
    rw [add_div]
    linarith
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hnum_le hden_pos.le) hsplit_div

private lemma differentiableOn_psiSeq (n : ℕ) : DifferentiableOn ℂ (psiSeq n) halfPlane := by
  intro s hs
  unfold psiSeq
  refine (differentiableAt_const _).sub ?_ |>.differentiableWithinAt
  refine DifferentiableAt.fun_sum fun j _ => ?_
  have hne : s + (j : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
    have : (0 : ℝ) < s.re := hs
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  exact (differentiableAt_id.add (differentiableAt_const _)).inv hne

private lemma deriv_psiSeq (n : ℕ) {s : ℂ} (hs : s ∈ halfPlane) :
    deriv (psiSeq n) s = ∑ j ∈ Finset.range (n + 1), ((s + (j : ℂ)) ^ 2)⁻¹ := by
  have hd : HasDerivAt (psiSeq n) (∑ j ∈ Finset.range (n + 1), ((s + (j : ℂ)) ^ 2)⁻¹) s := by
    have hsum : HasDerivAt (fun z : ℂ => ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹)
        (∑ j ∈ Finset.range (n + 1), -((s + (j : ℂ)) ^ 2)⁻¹) s := by
      refine HasDerivAt.fun_sum fun j _ => ?_
      have hne : s + (j : ℂ) ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
        have : (0 : ℝ) < s.re := hs
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have h1 : HasDerivAt (fun z : ℂ => (z + (j : ℂ))⁻¹) (-1 / (s + (j : ℂ)) ^ 2) s :=
        ((hasDerivAt_id s).add_const (j : ℂ)).inv hne
      exact h1.congr_deriv (by rw [neg_div, one_div])
    have h2 : HasDerivAt (psiSeq n) (0 - ∑ j ∈ Finset.range (n + 1), -((s + (j : ℂ)) ^ 2)⁻¹) s :=
      (hasDerivAt_const s (((Real.log (n : ℝ) : ℝ) : ℂ))).sub hsum
    exact h2.congr_deriv (by simp [Finset.sum_neg_distrib])
  exact hd.deriv

private lemma differentiableOn_digamma : DifferentiableOn ℂ Complex.digamma halfPlane :=
  tendstoLocallyUniformlyOn_psiSeq.differentiableOn
    (Eventually.of_forall differentiableOn_psiSeq) isOpen_halfPlane

private lemma continuousOn_deriv_digamma : ContinuousOn (deriv Complex.digamma) halfPlane :=
  (differentiableOn_digamma.deriv isOpen_halfPlane).continuousOn

private lemma tendsto_deriv_digamma {s : ℂ} (hs : s ∈ halfPlane) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), ((s + (j : ℂ)) ^ 2)⁻¹)
      atTop (𝓝 (deriv Complex.digamma s)) := by
  have h := (tendstoLocallyUniformlyOn_psiSeq.deriv
    (Eventually.of_forall differentiableOn_psiSeq) isOpen_halfPlane).tendsto_at hs
  refine h.congr fun n => ?_
  exact deriv_psiSeq n hs

private lemma digamma_conj {s : ℂ} (hs : s ∈ halfPlane) :
    Complex.digamma (star s) = star (Complex.digamma s) := by
  have hs' : star s ∈ halfPlane := by simpa [halfPlane, Complex.star_def] using hs
  have h1 := tendstoLocallyUniformlyOn_psiSeq.tendsto_at hs'
  have h2 := (continuous_star.tendsto (Complex.digamma s)).comp
    (tendstoLocallyUniformlyOn_psiSeq.tendsto_at hs)
  have heq : (fun n => psiSeq n (star s)) = (fun n => star (psiSeq n s)) := by
    ext n
    simp only [psiSeq, Complex.star_def, map_sub, map_sum, map_inv₀, map_add,
      Complex.conj_ofReal, map_natCast]
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

private noncomputable def psiRe (t : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + Complex.I * ((t / 2 : ℝ) : ℂ))).re

private noncomputable def psiReDeriv (t : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * (deriv Complex.digamma (1 / 4 + Complex.I * ((t / 2 : ℝ) : ℂ))).im

private lemma halfPlane_quarter (t : ℝ) :
    ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) ∈ halfPlane := by
  simp [halfPlane]

private lemma hasDerivAt_psiRe (t : ℝ) : HasDerivAt psiRe (psiReDeriv t) t := by
  have hmem := halfPlane_quarter t
  have hdg : HasDerivAt Complex.digamma (deriv Complex.digamma (1 / 4 + Complex.I * ((t / 2 : ℝ) : ℂ)))
      (1 / 4 + Complex.I * ((t / 2 : ℝ) : ℂ)) :=
    (differentiableOn_digamma.differentiableAt (isOpen_halfPlane.mem_nhds hmem)).hasDerivAt
  have hlin : HasDerivAt (fun u : ℝ => (1 / 4 : ℂ) + Complex.I * ((u / 2 : ℝ) : ℂ))
      (Complex.I / 2) t := by
    have h1 : HasDerivAt (fun u : ℝ => ((u / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).div_const (2 : ℝ)).ofReal_comp
    exact ((h1.const_mul Complex.I).const_add (1 / 4 : ℂ)).congr_deriv (by push_cast; ring)
  have hcomp : HasDerivAt (fun u : ℝ => Complex.digamma (1 / 4 + Complex.I * ((u / 2 : ℝ) : ℂ)))
      (deriv Complex.digamma (1 / 4 + Complex.I * ((t / 2 : ℝ) : ℂ)) * (Complex.I / 2)) t := by
    have h := (hdg.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hlin
    exact h.congr_deriv (by
      change (Complex.I / 2) • deriv Complex.digamma (1 / 4 + Complex.I * ((t / 2 : ℝ) : ℂ)) = _
      rw [smul_eq_mul, mul_comm])
  have hre : HasDerivAt psiRe
      ((deriv Complex.digamma (1 / 4 + Complex.I * ((t / 2 : ℝ) : ℂ)) * (Complex.I / 2)).re) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
  exact hre.congr_deriv (by
    unfold psiReDeriv
    simp [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im]
    ring)

private lemma continuous_psiReDeriv : Continuous psiReDeriv := by
  have hlin : Continuous (fun t : ℝ => (1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) := by fun_prop
  have hcomp : Continuous (fun t : ℝ => deriv Complex.digamma (1 / 4 + Complex.I * ((t / 2 : ℝ) : ℂ))) :=
    continuousOn_deriv_digamma.comp_continuous hlin halfPlane_quarter
  unfold psiReDeriv
  exact continuous_const.mul (Complex.continuous_im.comp hcomp)

private lemma tendsto_psiReDeriv_partial {t : ℝ} :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
      ((j : ℝ) + 1 / 4) * (t / 2) / (((j : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2) ^ 2)
      atTop (𝓝 (psiReDeriv t)) := by
  have htend := tendsto_deriv_digamma (halfPlane_quarter t)
  have him : Tendsto
      (fun n : ℕ => -(1 / 2 : ℝ) *
        (∑ j ∈ Finset.range (n + 1), ((1 / 4 + Complex.I * ((t / 2 : ℝ) : ℂ) + (j : ℂ)) ^ 2)⁻¹).im)
      atTop (𝓝 (psiReDeriv t)) :=
    ((Complex.continuous_im.tendsto _).comp htend).const_mul (-(1 / 2 : ℝ))
  refine him.congr fun n => ?_
  rw [Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set a : ℝ := (j : ℝ) + 1 / 4
  set b : ℝ := t / 2
  have hz : (1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) + (j : ℂ) = (a : ℂ) + Complex.I * (b : ℂ) := by
    dsimp [a, b]; push_cast; ring
  rw [hz]
  have hsq : ((a : ℂ) + Complex.I * (b : ℂ)) ^ 2 =
      ((a ^ 2 - b ^ 2 : ℝ) : ℂ) + Complex.I * ((2 * a * b : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [hsq, Complex.inv_im]
  have hnsq : Complex.normSq (((a ^ 2 - b ^ 2 : ℝ) : ℂ) + Complex.I * ((2 * a * b : ℝ) : ℂ)) =
      (a ^ 2 + b ^ 2) ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, one_mul, zero_add]
    ring
  rw [hnsq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, zero_mul,
    Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
  ring

private lemma psiReDeriv_ge_inv_five_t {t : ℝ} (ht : 4 ≤ t) :
    1 / (5 * t) ≤ psiReDeriv t := by
  set b : ℝ := t / 2
  have hb : 2 ≤ b := by dsimp [b]; linarith
  have hb_pos : 0 < b := by linarith
  let f : ℝ → ℝ := fun x => x * b / (x ^ 2 + b ^ 2) ^ 2
  have hf_nn : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x := fun x hx => by dsimp [f]; positivity
  have hf_anti : ∀ {x y : ℝ}, b ≤ x → x ≤ y → f y ≤ f x := by
    intro x y hbx hxy
    dsimp [f]
    have hden1 : 0 < (x ^ 2 + b ^ 2) ^ 2 := by positivity
    have hden2 : 0 < (y ^ 2 + b ^ 2) ^ 2 := by positivity
    rw [div_le_div_iff₀ hden2 hden1]
    have hnum : 0 ≤ (y - x) * (x * y * (x ^ 2 + x * y + y ^ 2) + 2 * x * y * b ^ 2 - b ^ 4) := by
      refine mul_nonneg (by linarith) ?_
      have hxy_b : b ^ 2 ≤ x * y := by nlinarith
      have hsum_b : 3 * b ^ 2 ≤ x ^ 2 + x * y + y ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have hf_int : ∀ {u v : ℝ}, u ≤ v →
      ∫ x in u..v, f x = b / (2 * (u ^ 2 + b ^ 2)) - b / (2 * (v ^ 2 + b ^ 2)) := by
    intro u v _
    let F : ℝ → ℝ := fun x => -b / (2 * (x ^ 2 + b ^ 2))
    have hF : ∀ x ∈ Set.uIcc u v, HasDerivAt F (f x) x := by
      intro x _
      have hden_ne : (2 * (x ^ 2 + b ^ 2)) ≠ 0 := by positivity
      have h1 : HasDerivAt (fun z : ℝ => 2 * (z ^ 2 + b ^ 2)) (2 * (2 * x)) x := by
        simpa using (((hasDerivAt_pow 2 x).add_const (b ^ 2)).const_mul 2)
      have h2 := (hasDerivAt_const x (-b)).div h1 hden_ne
      refine h2.congr_deriv ?_
      dsimp [f]; field_simp [hden_ne]; ring
    have hcont : ContinuousOn f (Set.uIcc u v) := by
      refine Continuous.continuousOn ?_
      refine (continuous_id.mul continuous_const).div ?_ (fun x => by positivity)
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable)]
    dsimp [F]; ring
  set m : ℕ := ⌈b⌉₊
  have hm_ge : b ≤ (m : ℝ) := Nat.le_ceil b
  have hm_le : (m : ℝ) < b + 1 := Nat.ceil_lt_add_one hb_pos.le
  have hpartial : ∀ n : ℕ, m ≤ n →
      b / (2 * (((m : ℝ) + 1 / 4) ^ 2 + b ^ 2)) -
        b / (2 * (((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + 2 * b ^ 2) ≤
      ∑ j ∈ Finset.range (n + 1), f ((j : ℝ) + 1 / 4) := by
    intro n hmn
    have hsub : Finset.Ico m (n + 1) ⊆ Finset.range (n + 1) := by
      intro j hj
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
    have h1 : ∑ j ∈ Finset.Ico m (n + 1), f ((j : ℝ) + 1 / 4) ≤
        ∑ j ∈ Finset.range (n + 1), f ((j : ℝ) + 1 / 4) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hf_nn _ (by positivity)
    have h2 : ∑ j ∈ Finset.Ico m (n + 1), ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), f x ≤
        ∑ j ∈ Finset.Ico m (n + 1), f ((j : ℝ) + 1 / 4) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjm : b ≤ (j : ℝ) + 1 / 4 := by
        have : (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hj).1
        linarith
      have hcont : Continuous f :=
        (continuous_id.mul continuous_const).div (by fun_prop) (fun x => by positivity)
      calc ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), f x
          ≤ ∫ _x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), f ((j : ℝ) + 1 / 4) := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hcont.intervalIntegrable _ _) intervalIntegrable_const fun x hx => ?_
            exact hf_anti hjm hx.1
        _ = f ((j : ℝ) + 1 / 4) := by simp; ring
    have htele : ∑ j ∈ Finset.Ico m (n + 1), ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), f x =
        b / (2 * (((m : ℝ) + 1 / 4) ^ 2 + b ^ 2)) -
        b / (2 * ((((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + b ^ 2)) := by
      have hterm : ∀ j ∈ Finset.Ico m (n + 1),
          ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), f x =
          b / (2 * (((j : ℝ) + 1 / 4) ^ 2 + b ^ 2)) -
          b / (2 * ((((j + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + b ^ 2)) := by
        intro j _
        rw [hf_int (by linarith)]
        congr 3; push_cast; ring
      rw [Finset.sum_congr rfl hterm]
      have htel := Finset.sum_Ico_sub (f := fun j : ℕ => b / (2 * (((j : ℝ) + 1 / 4) ^ 2 + b ^ 2)))
        (by omega : m ≤ n + 1)
      have hneg : ∀ j : ℕ, b / (2 * (((j : ℝ) + 1 / 4) ^ 2 + b ^ 2)) -
            b / (2 * ((((j + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + b ^ 2)) =
          -(b / (2 * ((((j + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + b ^ 2)) -
            b / (2 * (((j : ℝ) + 1 / 4) ^ 2 + b ^ 2))) := fun _ => by ring
      simp_rw [hneg, Finset.sum_neg_distrib, htel]
      ring
    have heq2 : 2 * ((((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + b ^ 2) =
        2 * (((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + 2 * b ^ 2 := by ring
    rw [heq2] at htele
    linarith
  have htend_rhs : Tendsto (fun n : ℕ =>
      b / (2 * (((m : ℝ) + 1 / 4) ^ 2 + b ^ 2)) -
        b / (2 * (((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + 2 * b ^ 2))
      atTop (𝓝 (b / (2 * (((m : ℝ) + 1 / 4) ^ 2 + b ^ 2)))) := by
    have hden_top : Tendsto (fun n : ℕ => 2 * (((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + 2 * b ^ 2)
        atTop atTop := by
      refine Filter.tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast; nlinarith
    have h0 := tendsto_const_nhds.div_atTop hden_top (a := b)
    simpa using tendsto_const_nhds.sub h0
  have hlim : b / (2 * (((m : ℝ) + 1 / 4) ^ 2 + b ^ 2)) ≤ psiReDeriv t := by
    refine le_of_tendsto_of_tendsto htend_rhs tendsto_psiReDeriv_partial ?_
    filter_upwards [eventually_ge_atTop m] with n hn using hpartial n hn
  have hm_bound : (m : ℝ) + 1 / 4 ≤ 2 * b := by linarith
  have hden_le : 2 * (((m : ℝ) + 1 / 4) ^ 2 + b ^ 2) ≤ 10 * b ^ 2 := by
    have : ((m : ℝ) + 1 / 4) ^ 2 ≤ (2 * b) ^ 2 := by nlinarith
    nlinarith
  have hfrac : 1 / (5 * t) ≤ b / (2 * (((m : ℝ) + 1 / 4) ^ 2 + b ^ 2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    dsimp [b] at hden_le ⊢
    nlinarith
  linarith

private lemma psiRe_approx {t : ℝ} (ht : 4 ≤ t) :
    |psiRe t - Real.log (t / 2)| ≤ 4 / t := by
  set b : ℝ := t / 2
  have hb : 2 ≤ b := by dsimp [b]; linarith
  have hb_pos : 0 < b := by linarith
  let g : ℝ → ℝ := fun x => x / (x ^ 2 + b ^ 2)
  have hg_cont : Continuous g :=
    continuous_id.div (by fun_prop) (fun x => by positivity)
  have hg_bounds : ∀ x : ℝ, 0 ≤ x → 0 ≤ g x ∧ g x ≤ 1 / (2 * b) := by
    intro x hx
    dsimp [g]
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x - b)]
  have hg_mono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → y ≤ b → g x ≤ g y := by
    intro x y hx hxy hyb
    dsimp [g]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hxy_b : x * y ≤ b ^ 2 := by nlinarith
    nlinarith
  have hg_anti : ∀ {x y : ℝ}, b ≤ x → x ≤ y → g y ≤ g x := by
    intro x y hbx hxy
    dsimp [g]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hxy_b : b ^ 2 ≤ x * y := by nlinarith
    nlinarith
  have hg_int : ∀ {u v : ℝ},
      ∫ x in u..v, g x = (1 / 2) * Real.log (v ^ 2 + b ^ 2) - (1 / 2) * Real.log (u ^ 2 + b ^ 2) := by
    intro u v
    let G : ℝ → ℝ := fun x => (1 / 2) * Real.log (x ^ 2 + b ^ 2)
    have hG : ∀ x ∈ Set.uIcc u v, HasDerivAt G (g x) x := by
      intro x _
      have hpos : x ^ 2 + b ^ 2 ≠ 0 := by positivity
      have h1 : HasDerivAt (fun z : ℝ => z ^ 2 + b ^ 2) (2 * x) x := by
        simpa using (hasDerivAt_pow 2 x).add_const (b ^ 2)
      have h2 := (h1.log hpos).const_mul (1 / 2 : ℝ)
      refine h2.congr_deriv ?_
      dsimp [g]; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG (hg_cont.intervalIntegrable u v)]
  -- Compare finite sum of g(j + 1/4) with ∫_{1/4}^{n + 5/4} g
  set m : ℕ := ⌊b - 1 / 4⌋₊
  have hm_le : (m : ℝ) + 1 / 4 ≤ b := by
    have := Nat.floor_le (show 0 ≤ b - 1 / 4 by linarith)
    linarith
  have hm_lt : b < (m : ℝ) + 5 / 4 := by
    have := Nat.lt_floor_add_one (b - 1 / 4)
    linarith
  let E : ℕ → ℝ := fun j => g ((j : ℝ) + 1 / 4) - ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g x
  have hE_sum : ∀ n : ℕ,
      ∑ j ∈ Finset.range (n + 1), E j =
        (∑ j ∈ Finset.range (n + 1), g ((j : ℝ) + 1 / 4)) -
        ((1 / 2) * Real.log ((((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + b ^ 2) -
          (1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2)) := by
    intro n
    dsimp [E]
    rw [Finset.sum_sub_distrib]
    congr 1
    have hterm : ∀ j ∈ Finset.range (n + 1),
        ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g x =
        (1 / 2) * Real.log ((((j + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + b ^ 2) -
        (1 / 2) * Real.log (((j : ℝ) + 1 / 4) ^ 2 + b ^ 2) := by
      intro j _
      rw [hg_int]
      congr 3; push_cast; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun j : ℕ =>
      (1 / 2) * Real.log (((j : ℝ) + 1 / 4) ^ 2 + b ^ 2))]
    simp
  have hE_bound : ∀ n : ℕ, m + 1 ≤ n → |∑ j ∈ Finset.range (n + 1), E j| ≤ 3 / (2 * b) := by
    intro n hmn
    have hsplit1 : ∑ j ∈ Finset.range (n + 1), E j =
        (∑ j ∈ Finset.range m, E j) + E m + ∑ j ∈ Finset.Ico (m + 1) (n + 1), E j := by
      have h1 := Finset.sum_range_add_sum_Ico E (show m + 1 ≤ n + 1 by omega)
      rw [Finset.sum_range_succ] at h1
      linarith
    -- Part 1: j < m
    have hpart1_lo : g (1 / 4) - g ((m : ℝ) + 1 / 4) ≤ ∑ j ∈ Finset.range m, E j := by
      calc g (1 / 4) - g ((m : ℝ) + 1 / 4)
          = ∑ j ∈ Finset.range m, (g ((j : ℝ) + 1 / 4) - g ((((j + 1 : ℕ) : ℝ) + 1 / 4))) := by
            have htel := Finset.sum_range_sub (fun j : ℕ => g ((j : ℝ) + 1 / 4)) m
            have hneg : ∀ j : ℕ, g ((j : ℝ) + 1 / 4) - g ((((j + 1 : ℕ) : ℝ) + 1 / 4)) =
                -(g ((((j + 1 : ℕ) : ℝ) + 1 / 4)) - g ((j : ℝ) + 1 / 4)) := fun _ => by ring
            simp_rw [hneg, Finset.sum_neg_distrib, htel]
            simp only [Nat.cast_zero, zero_add]
            ring
        _ ≤ ∑ j ∈ Finset.range m, E j := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjm : j + 1 ≤ m := Finset.mem_range.mp hj
            have hj_le_b : (j : ℝ) + 5 / 4 ≤ b := by
              have : ((j + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
              push_cast at this; linarith
            have hint_le : ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g x ≤
                g (((j + 1 : ℕ) : ℝ) + 1 / 4) := by
              have heq : ((j + 1 : ℕ) : ℝ) + 1 / 4 = (j : ℝ) + 5 / 4 := by push_cast; ring
              rw [heq]
              calc ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g x
                  ≤ ∫ _x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g ((j : ℝ) + 5 / 4) :=
                    intervalIntegral.integral_mono_on (by linarith) (hg_cont.intervalIntegrable _ _)
                      intervalIntegrable_const fun x hx =>
                        hg_mono (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) j]) hx.2 hj_le_b
                _ = g ((j : ℝ) + 5 / 4) := by simp; ring
            dsimp [E]; linarith
    have hpart1_hi : ∑ j ∈ Finset.range m, E j ≤ 0 := by
      refine Finset.sum_nonpos fun j hj => ?_
      have hjm : j + 1 ≤ m := Finset.mem_range.mp hj
      have hj_le_b : (j : ℝ) + 5 / 4 ≤ b := by
        have : ((j + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
        push_cast at this; linarith
      have hint_ge : g ((j : ℝ) + 1 / 4) ≤ ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g x := by
        calc g ((j : ℝ) + 1 / 4)
            = ∫ _x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g ((j : ℝ) + 1 / 4) := by simp; ring
          _ ≤ ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g x :=
            intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
              (hg_cont.intervalIntegrable _ _) fun x hx =>
                hg_mono (by positivity) hx.1 (hx.2.trans hj_le_b)
      dsimp [E]; linarith
    have habs1 : |∑ j ∈ Finset.range m, E j| ≤ 1 / (2 * b) := by
      rw [abs_le]
      have h1 := hg_bounds (1 / 4) (by norm_num)
      have h2 := hg_bounds ((m : ℝ) + 1 / 4) (by positivity)
      exact ⟨by linarith, by linarith⟩
    -- Part 2: j = m
    have habs2 : |E m| ≤ 1 / (2 * b) := by
      have hgm := hg_bounds ((m : ℝ) + 1 / 4) (by positivity)
      have hint_lo : 0 ≤ ∫ x in ((m : ℝ) + 1 / 4)..((m : ℝ) + 5 / 4), g x :=
        intervalIntegral.integral_nonneg (by linarith) fun x hx =>
          (hg_bounds x (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) m])).1
      have hint_hi : ∫ x in ((m : ℝ) + 1 / 4)..((m : ℝ) + 5 / 4), g x ≤ 1 / (2 * b) := by
        calc ∫ x in ((m : ℝ) + 1 / 4)..((m : ℝ) + 5 / 4), g x
            ≤ ∫ _x in ((m : ℝ) + 1 / 4)..((m : ℝ) + 5 / 4), (1 / (2 * b)) :=
              intervalIntegral.integral_mono_on (by linarith) (hg_cont.intervalIntegrable _ _)
                intervalIntegrable_const fun x hx =>
                  (hg_bounds x (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) m])).2
          _ = 1 / (2 * b) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      dsimp [E]; rw [abs_le]; exact ⟨by linarith, by linarith⟩
    -- Part 3: m + 1 ≤ j ≤ n
    have hpart3_lo : 0 ≤ ∑ j ∈ Finset.Ico (m + 1) (n + 1), E j := by
      refine Finset.sum_nonneg fun j hj => ?_
      have hjb : b ≤ (j : ℝ) + 1 / 4 := by
        have : ((m + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hj).1
        push_cast at this; linarith
      have hint_le : ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g x ≤ g ((j : ℝ) + 1 / 4) := by
        calc ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g x
            ≤ ∫ _x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g ((j : ℝ) + 1 / 4) :=
              intervalIntegral.integral_mono_on (by linarith) (hg_cont.intervalIntegrable _ _)
                intervalIntegrable_const fun x hx => hg_anti hjb hx.1
          _ = g ((j : ℝ) + 1 / 4) := by simp; ring
      dsimp [E]; linarith
    have hpart3_hi : ∑ j ∈ Finset.Ico (m + 1) (n + 1), E j ≤
        g (((m + 1 : ℕ) : ℝ) + 1 / 4) - g (((n + 1 : ℕ) : ℝ) + 1 / 4) := by
      calc ∑ j ∈ Finset.Ico (m + 1) (n + 1), E j
          ≤ ∑ j ∈ Finset.Ico (m + 1) (n + 1), (g ((j : ℝ) + 1 / 4) - g ((((j + 1 : ℕ) : ℝ) + 1 / 4))) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjb : b ≤ (j : ℝ) + 1 / 4 := by
              have : ((m + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hj).1
              push_cast at this; linarith
            have hint_ge : g (((j + 1 : ℕ) : ℝ) + 1 / 4) ≤
                ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g x := by
              have heq : ((j + 1 : ℕ) : ℝ) + 1 / 4 = (j : ℝ) + 5 / 4 := by push_cast; ring
              rw [heq]
              calc g ((j : ℝ) + 5 / 4)
                  = ∫ _x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g ((j : ℝ) + 5 / 4) := by simp; ring
                _ ≤ ∫ x in ((j : ℝ) + 1 / 4)..((j : ℝ) + 5 / 4), g x :=
                  intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
                    (hg_cont.intervalIntegrable _ _) fun x hx => hg_anti (hjb.trans hx.1) hx.2
            dsimp [E]; linarith
        _ = g (((m + 1 : ℕ) : ℝ) + 1 / 4) - g (((n + 1 : ℕ) : ℝ) + 1 / 4) := by
            have htel := Finset.sum_Ico_sub (f := fun j : ℕ => g ((j : ℝ) + 1 / 4))
              (show m + 1 ≤ n + 1 by omega)
            have hneg : ∀ j : ℕ, g ((j : ℝ) + 1 / 4) - g ((((j + 1 : ℕ) : ℝ) + 1 / 4)) =
                -(g ((((j + 1 : ℕ) : ℝ) + 1 / 4)) - g ((j : ℝ) + 1 / 4)) := fun _ => by ring
            simp_rw [hneg, Finset.sum_neg_distrib, htel]; ring
    have habs3 : |∑ j ∈ Finset.Ico (m + 1) (n + 1), E j| ≤ 1 / (2 * b) := by
      rw [abs_le]
      have h1 := hg_bounds (((m + 1 : ℕ) : ℝ) + 1 / 4) (by positivity)
      have h2 := hg_bounds (((n + 1 : ℕ) : ℝ) + 1 / 4) (by positivity)
      exact ⟨by linarith, by linarith⟩
    rw [hsplit1]
    have htri : |(∑ j ∈ Finset.range m, E j) + E m + ∑ j ∈ Finset.Ico (m + 1) (n + 1), E j| ≤
        |∑ j ∈ Finset.range m, E j| + |E m| + |∑ j ∈ Finset.Ico (m + 1) (n + 1), E j| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    linarith [show 1 / (2 * b) + 1 / (2 * b) + 1 / (2 * b) = 3 / (2 * b) by ring]
  -- Now take n → ∞ using psiSeq n (1/4 + I*b) → digamma (1/4 + I*b)
  have htend_psi : Tendsto (fun n : ℕ => Real.log (n : ℝ) - ∑ j ∈ Finset.range (n + 1), g ((j : ℝ) + 1 / 4))
      atTop (𝓝 (psiRe t)) := by
    have h := (Complex.continuous_re.tendsto _).comp
      (tendstoLocallyUniformlyOn_psiSeq.tendsto_at (halfPlane_quarter t))
    refine h.congr fun n => ?_
    dsimp [Function.comp_def, psiSeq, g]
    rw [Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.inv_re]
    have hre : ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) + (j : ℂ)).re = (j : ℝ) + 1 / 4 := by
      simp; ring
    have him : ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) + (j : ℂ)).im = b := by
      simp [b]
    rw [Complex.normSq_apply, hre, him, sq, sq]
  have htend_int : Tendsto (fun n : ℕ =>
      Real.log (n : ℝ) - ((1 / 2) * Real.log ((((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + b ^ 2) -
        (1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2)))
      atTop (𝓝 ((1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2))) := by
    have hratio : Tendsto (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 / (n : ℝ) ^ 2 + b ^ 2 / (n : ℝ) ^ 2)
        atTop (𝓝 (1 + 0)) := by
      have h1 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) + 1 / 4) / (n : ℝ)) atTop (𝓝 1) := by
        have hlin : Tendsto (fun n : ℕ => (1 : ℝ) + (5 / 4 : ℝ) / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
        rw [add_zero] at hlin
        refine hlin.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with n hn
        have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast; field_simp [hnR]; ring
      have h1sq : Tendsto (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) + 1 / 4) / (n : ℝ)) ^ 2) atTop (𝓝 (1 ^ 2)) :=
        h1.pow 2
      simp only [one_pow, div_pow] at h1sq
      have h2 : Tendsto (fun n : ℕ => b ^ 2 / (n : ℝ) ^ 2) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
      exact h1sq.add h2
    rw [add_zero] at hratio
    have hlog0 : Tendsto (fun n : ℕ =>
        -(1 / 2 : ℝ) * Real.log (((((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + b ^ 2) / (n : ℝ) ^ 2) +
          (1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2))
        atTop (𝓝 ((1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2))) := by
      have h := ((Real.continuousAt_log one_ne_zero).tendsto.comp hratio).const_mul (-(1 / 2 : ℝ))
      have h' := h.add (tendsto_const_nhds (x := (1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2)))
      rw [Real.log_one, mul_zero, zero_add] at h'
      refine h'.congr fun n => ?_
      dsimp [Function.comp_def]
      rw [← add_div]
    refine hlog0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
    ring
  have hlim_diff : |psiRe t - (1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2)| ≤ 3 / (2 * b) := by
    have hdiff := (htend_psi.sub htend_int).abs
    refine le_of_tendsto hdiff ?_
    filter_upwards [eventually_ge_atTop (m + 1)] with n hn
    have heq : (Real.log (n : ℝ) - ∑ j ∈ Finset.range (n + 1), g ((j : ℝ) + 1 / 4)) -
        (Real.log (n : ℝ) - ((1 / 2) * Real.log ((((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + b ^ 2) -
          (1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2))) =
        -(∑ j ∈ Finset.range (n + 1), E j) := by
      rw [hE_sum n]; ring
    rw [heq, abs_neg]
    exact hE_bound n hn
  have hlog_shift : |(1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2) - Real.log b| ≤ 1 / (2 * b) := by
    have heq : (1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2) - Real.log b =
        (1 / 2) * Real.log (1 + 1 / (16 * b ^ 2)) := by
      have hfac : (1 / 4 : ℝ) ^ 2 + b ^ 2 = b ^ 2 * (1 + 1 / (16 * b ^ 2)) := by
        field_simp [hb_pos.ne']; ring
      rw [hfac, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      ring
    rw [heq, abs_of_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ 1 / (16 * b ^ 2) by positivity])))]
    have hlog_le : Real.log (1 + 1 / (16 * b ^ 2)) ≤ 1 / (16 * b ^ 2) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (16 * b ^ 2) by positivity)
      linarith
    have h1 : (1 / 2) * (1 / (16 * b ^ 2)) ≤ 1 / (2 * b) := by
      rw [show (1 / 2 : ℝ) * (1 / (16 * b ^ 2)) = 1 / (32 * b ^ 2) by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have htri : |psiRe t - Real.log b| ≤
      |psiRe t - (1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2)| +
      |(1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2) - Real.log b| := by
    have heq : (psiRe t - (1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2)) +
        ((1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + b ^ 2) - Real.log b) = psiRe t - Real.log b := by ring
    rw [← heq]
    exact abs_add_le _ _
  have h2b : 3 / (2 * b) + 1 / (2 * b) = 4 / t := by
    dsimp [b]; field_simp [hb_pos.ne']; ring
  linarith

/- ### Section 4: First-Derivative Van der Corput and Oscillatory Bounds -/

private lemma norm_integral_cexp_linear_le {a b ω : ℝ} (hω : ω ≠ 0) :
    ‖∫ t in a..b, Complex.exp (Complex.I * ((ω * t : ℝ) : ℂ))‖ ≤ 2 / |ω| := by
  let F : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((ω * t : ℝ) : ℂ)) / (Complex.I * (ω : ℂ))
  have hIω : Complex.I * (ω : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hω)
  have hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (Complex.exp (Complex.I * ((ω * t : ℝ) : ℂ))) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => Complex.I * ((ω * u : ℝ) : ℂ)) (Complex.I * (ω : ℂ)) t := by
      have hmul : HasDerivAt (fun u : ℝ => ((ω * u : ℝ) : ℂ)) (ω : ℂ) t := by
        simpa using ((hasDerivAt_id t).const_mul ω).ofReal_comp
      exact hmul.const_mul Complex.I
    have h2 := h1.cexp.div_const (Complex.I * (ω : ℂ))
    refine h2.congr_deriv ?_
    rw [mul_div_cancel_right₀ _ hIω]
  have hcont : Continuous (fun t : ℝ => Complex.exp (Complex.I * ((ω * t : ℝ) : ℂ))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable a b)]
  dsimp [F]
  rw [← sub_div, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg ω)
  have hnorm1 : ∀ r : ℝ, ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
    intro r
    rw [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    simp
  calc ‖Complex.exp (Complex.I * ((ω * b : ℝ) : ℂ)) - Complex.exp (Complex.I * ((ω * a : ℝ) : ℂ))‖
      ≤ ‖Complex.exp (Complex.I * ((ω * b : ℝ) : ℂ))‖ +
        ‖Complex.exp (Complex.I * ((ω * a : ℝ) : ℂ))‖ := norm_sub_le _ _
    _ = 2 := by rw [hnorm1, hnorm1]; norm_num

private lemma van_der_corput_first_deriv {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    {u : ℝ → ℂ} {φ φ' : ℝ → ℝ}
    (hu_norm : ∀ t ∈ Set.uIcc a b, ‖u t‖ = 1)
    (hu_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt u (Complex.I * (φ t : ℂ) * u t) t)
    (hφ_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (φ' t) t)
    (hφ'_cont : ContinuousOn φ' (Set.uIcc a b))
    (hφ'_nn : ∀ t ∈ Set.uIcc a b, 0 ≤ φ' t)
    (hφ_lo : lam ≤ φ a) :
    ‖∫ t in a..b, u t‖ ≤ 2 / lam := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hφ_mono : MonotoneOn φ (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · exact fun t ht => (hφ_deriv t (huIcc ▸ ht)).continuousAt.continuousWithinAt
    · exact fun t ht => (hφ_deriv t (huIcc ▸ interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hφ_deriv t (huIcc ▸ interior_subset ht)).deriv]
      exact hφ'_nn t (huIcc ▸ interior_subset ht)
  have hφ_ge : ∀ t ∈ Set.uIcc a b, lam ≤ φ t := fun t ht =>
    hφ_lo.trans (hφ_mono (Set.left_mem_Icc.mpr hab) (huIcc ▸ ht) (huIcc ▸ ht).1)
  have hφ_pos : ∀ t ∈ Set.uIcc a b, 0 < φ t := fun t ht => lt_of_lt_of_le hlam (hφ_ge t ht)
  have hu_cont : ContinuousOn u (Set.uIcc a b) :=
    fun t ht => (hu_deriv t ht).continuousAt.continuousWithinAt
  have hφ_cont : ContinuousOn φ (Set.uIcc a b) :=
    fun t ht => (hφ_deriv t ht).continuousAt.continuousWithinAt
  let F : ℝ → ℂ := fun t => u t / (Complex.I * (φ t : ℂ))
  let R : ℝ → ℂ := fun t => Complex.I * ((φ' t / φ t ^ 2 : ℝ) : ℂ) * u t
  have hF_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt F (u t + R t) t := by
    intro t ht
    have hφne : (φ t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ_pos t ht).ne'
    have hIφne : Complex.I * (φ t : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hφne
    have hden : HasDerivAt (fun x : ℝ => Complex.I * (φ x : ℂ)) (Complex.I * (φ' t : ℂ)) t :=
      (hφ_deriv t ht).ofReal_comp.const_mul Complex.I
    have hq := (hu_deriv t ht).div hden hIφne
    refine hq.congr_deriv ?_
    dsimp [R]
    push_cast
    field_simp [hIφne, hφne]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hR_cont : ContinuousOn R (Set.uIcc a b) := by
    refine ContinuousOn.mul ?_ hu_cont
    refine continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_)
    exact hφ'_cont.div (hφ_cont.pow 2) fun t ht => (sq_pos_of_pos (hφ_pos t ht)).ne'
  have hF'_int : IntervalIntegrable (fun t => u t + R t) volume a b :=
    (hu_cont.add hR_cont).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv hF'_int
  rw [intervalIntegral.integral_add hu_cont.intervalIntegrable hR_cont.intervalIntegrable] at hFTC
  have hu_eq : (∫ t in a..b, u t) = (F b - F a) - ∫ t in a..b, R t := by
    exact eq_sub_of_add_eq hFTC
  rw [hu_eq]
  have hFb : ‖F b‖ = 1 / φ b := by
    dsimp [F]
    rw [norm_div, hu_norm b (Set.right_mem_uIcc), norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hφ_pos b Set.right_mem_uIcc)]
  have hFa : ‖F a‖ = 1 / φ a := by
    dsimp [F]
    rw [norm_div, hu_norm a (Set.left_mem_uIcc), norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hφ_pos a Set.left_mem_uIcc)]
  have hR_bound : ‖∫ t in a..b, R t‖ ≤ 1 / φ a - 1 / φ b := by
    have hnorm_R : ∀ t ∈ Set.uIcc a b, ‖R t‖ = φ' t / φ t ^ 2 := by
      intro t ht
      dsimp [R]
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        hu_norm t ht, mul_one, abs_of_nonneg (div_nonneg (hφ'_nn t ht) (sq_nonneg _))]
    have h1 : ‖∫ t in a..b, R t‖ ≤ ∫ t in a..b, ‖R t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    have h2 : ∫ t in a..b, ‖R t‖ = ∫ t in a..b, φ' t / φ t ^ 2 :=
      intervalIntegral.integral_congr hnorm_R
    have h3 : ∫ t in a..b, φ' t / φ t ^ 2 = (-(φ b)⁻¹) - (-(φ a)⁻¹) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -(φ t)⁻¹) ?_ ?_
      · intro t ht
        have hinv := (hφ_deriv t ht).inv (hφ_pos t ht).ne'
        exact hinv.neg.congr_deriv (by ring)
      · exact (hφ'_cont.div (hφ_cont.pow 2) fun t ht => (sq_pos_of_pos (hφ_pos t ht)).ne').intervalIntegrable
    rw [h2, h3] at h1
    linarith [show (-(φ b)⁻¹) - (-(φ a)⁻¹) = 1 / φ a - 1 / φ b by simp [one_div]; ring]
  calc ‖(F b - F a) - ∫ t in a..b, R t‖
      ≤ ‖F b - F a‖ + ‖∫ t in a..b, R t‖ := norm_sub_le _ _
    _ ≤ (‖F b‖ + ‖F a‖) + (1 / φ a - 1 / φ b) := add_le_add (norm_sub_le _ _) hR_bound
    _ = 2 / φ a := by rw [hFb, hFa]; ring
    _ ≤ 2 / lam := div_le_div_of_nonneg_left (by norm_num) hlam hφ_lo

private noncomputable def oscPhase (k : ℕ) (t : ℝ) : ℝ :=
  2 * psiRe t - 2 * Real.log Real.pi - Real.log (k : ℝ)

private noncomputable def oscUnit (k : ℕ) (t : ℝ) : ℂ :=
  star (chi2 t) * Complex.exp (-Complex.I * ((Real.log (k : ℝ) * t : ℝ) : ℂ))

private lemma norm_oscUnit (k : ℕ) (t : ℝ) : ‖oscUnit k t‖ = 1 := by
  unfold oscUnit
  rw [norm_mul, norm_star, norm_chi2, one_mul, Complex.norm_exp]
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_self, neg_zero, Real.exp_zero]

private lemma hasDerivAt_oscUnit {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    HasDerivAt (oscUnit k) (Complex.I * (oscPhase k t : ℂ) * oscUnit k t) t := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Express oscUnit k t explicitly in terms of exp and Gamma
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  let sPlus : ℝ → ℂ := fun u => (1 / 4 : ℂ) + Complex.I * ((u / 2 : ℝ) : ℂ)
  let sMinus : ℝ → ℂ := fun u => (1 / 4 : ℂ) - Complex.I * ((u / 2 : ℝ) : ℂ)
  have hosc_eq : oscUnit k = fun u : ℝ =>
      Complex.exp (-Complex.I * (((2 * Real.log Real.pi + Real.log (k : ℝ)) * u : ℝ) : ℂ)) *
        (Complex.Gamma (sPlus u) / Complex.Gamma (sMinus u)) ^ 2 := by
    ext u
    unfold oscUnit
    rw [star_chi2, Complex.Gammaℝ_def, Complex.Gammaℝ_def]
    have harg1 : -((1 / 2 : ℂ) + Complex.I * (u : ℂ)) / 2 = -(1 / 4 : ℂ) - Complex.I * ((u / 2 : ℝ) : ℂ) := by
      push_cast; ring
    have harg2 : -((1 / 2 : ℂ) - Complex.I * (u : ℂ)) / 2 = -(1 / 4 : ℂ) + Complex.I * ((u / 2 : ℝ) : ℂ) := by
      push_cast; ring
    have harg3 : ((1 / 2 : ℂ) + Complex.I * (u : ℂ)) / 2 = sPlus u := by
      dsimp [sPlus]; push_cast; ring
    have harg4 : ((1 / 2 : ℂ) - Complex.I * (u : ℂ)) / 2 = sMinus u := by
      dsimp [sMinus]; push_cast; ring
    rw [harg1, harg2, harg3, harg4, mul_div_mul_comm, mul_pow, ← Complex.cpow_sub _ _ hpi_ne]
    have hexp_pi : ((Real.pi : ℂ) ^ (-(1 / 4 : ℂ) - Complex.I * ((u / 2 : ℝ) : ℂ) -
        (-(1 / 4 : ℂ) + Complex.I * ((u / 2 : ℝ) : ℂ)))) ^ 2 =
        Complex.exp (-Complex.I * ((2 * Real.log Real.pi * u : ℝ) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero hpi_ne, ← Complex.ofReal_log Real.pi_pos.le,
        ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    rw [hexp_pi, mul_right_comm, ← Complex.exp_add]
    congr 2; push_cast; ring
  rw [hosc_eq]
  have hsP_mem : sPlus t ∈ halfPlane := halfPlane_quarter t
  have hsM_mem : sMinus t ∈ halfPlane := by simp [sMinus, halfPlane]
  have hGP_ne : Complex.Gamma (sPlus t) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hsP_mem
  have hGM_ne : Complex.Gamma (sMinus t) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hsM_mem
  have hGP_diff : HasDerivAt Complex.Gamma (deriv Complex.Gamma (sPlus t)) (sPlus t) :=
    (Complex.differentiableAt_Gamma _ fun m h => by
      have := congrArg Complex.re h
      simp only [sPlus, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
        Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero,
        Complex.neg_re, Complex.natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) m]).hasDerivAt
  have hGM_diff : HasDerivAt Complex.Gamma (deriv Complex.Gamma (sMinus t)) (sMinus t) :=
    (Complex.differentiableAt_Gamma _ fun m h => by
      have := congrArg Complex.re h
      simp only [sMinus, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
        Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, sub_zero,
        Complex.neg_re, Complex.natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) m]).hasDerivAt
  have hsP_deriv : HasDerivAt sPlus (Complex.I / 2) t := by
    have h1 : HasDerivAt (fun u : ℝ => ((u / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).div_const (2 : ℝ)).ofReal_comp
    exact ((h1.const_mul Complex.I).const_add (1 / 4 : ℂ)).congr_deriv (by push_cast; ring)
  have hsM_deriv : HasDerivAt sMinus (-(Complex.I / 2)) t := by
    have h1 : HasDerivAt (fun u : ℝ => ((u / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).div_const (2 : ℝ)).ofReal_comp
    exact ((hasDerivAt_const t (1 / 4 : ℂ)).sub (h1.const_mul Complex.I)).congr_deriv (by push_cast; ring)
  have hGP_comp : HasDerivAt (fun u => Complex.Gamma (sPlus u))
      (Complex.digamma (sPlus t) * Complex.Gamma (sPlus t) * (Complex.I / 2)) t := by
    have h := (hGP_diff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hsP_deriv
    refine h.congr_deriv ?_
    change (Complex.I / 2) • deriv Complex.Gamma (sPlus t) = _
    rw [smul_eq_mul, Complex.digamma_def, logDeriv_apply, div_mul_cancel₀ _ hGP_ne, mul_comm]
  have hGM_comp : HasDerivAt (fun u => Complex.Gamma (sMinus u))
      (Complex.digamma (sMinus t) * Complex.Gamma (sMinus t) * (-(Complex.I / 2))) t := by
    have h := (hGM_diff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hsM_deriv
    refine h.congr_deriv ?_
    change (-(Complex.I / 2)) • deriv Complex.Gamma (sMinus t) = _
    rw [smul_eq_mul, Complex.digamma_def, logDeriv_apply, div_mul_cancel₀ _ hGM_ne, mul_comm]
  have hQ_deriv : HasDerivAt (fun u => (Complex.Gamma (sPlus u) / Complex.Gamma (sMinus u)) ^ 2)
      (2 * (Complex.Gamma (sPlus t) / Complex.Gamma (sMinus t)) ^ 1 *
        ((Complex.digamma (sPlus t) * Complex.Gamma (sPlus t) * (Complex.I / 2) * Complex.Gamma (sMinus t) -
          Complex.Gamma (sPlus t) * (Complex.digamma (sMinus t) * Complex.Gamma (sMinus t) * (-(Complex.I / 2)))) /
          Complex.Gamma (sMinus t) ^ 2)) t :=
    (hGP_comp.div hGM_comp hGM_ne).pow 2
  have hE_deriv' : HasDerivAt
      (fun u : ℝ => Complex.exp (-Complex.I * (((2 * Real.log Real.pi + Real.log (k : ℝ)) * u : ℝ) : ℂ)))
      (Complex.exp (-Complex.I * (((2 * Real.log Real.pi + Real.log (k : ℝ)) * t : ℝ) : ℂ)) *
        (-Complex.I * ((2 * Real.log Real.pi + Real.log (k : ℝ) : ℝ) : ℂ))) t := by
    have h1 : HasDerivAt (fun u : ℝ => (((2 * Real.log Real.pi + Real.log (k : ℝ)) * u : ℝ) : ℂ))
        ((2 * Real.log Real.pi + Real.log (k : ℝ) : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * Real.log Real.pi + Real.log (k : ℝ))).ofReal_comp
    exact (h1.const_mul (-Complex.I)).cexp
  have hmul := hE_deriv'.mul hQ_deriv
  refine hmul.congr_deriv ?_
  have hconj_s : sMinus t = star (sPlus t) := by
    simp [sMinus, sPlus, sub_eq_add_neg]
  have hdig_sum : Complex.digamma (sPlus t) + Complex.digamma (sMinus t) =
      ((2 * psiRe t : ℝ) : ℂ) := by
    rw [hconj_s, digamma_conj hsP_mem, Complex.star_def, Complex.add_conj]
    simp [psiRe, sPlus]
  unfold oscPhase
  have hkey : ((2 * psiRe t : ℝ) : ℂ) = Complex.digamma (sPlus t) + Complex.digamma (sMinus t) :=
    hdig_sum.symm
  have hphase_cast : ((2 * psiRe t - 2 * Real.log Real.pi - Real.log (k : ℝ) : ℝ) : ℂ) =
      (Complex.digamma (sPlus t) + Complex.digamma (sMinus t)) -
        ((2 * Real.log Real.pi + Real.log (k : ℝ) : ℝ) : ℂ) := by
    rw [← hkey]
    push_cast
    ring
  rw [hphase_cast]
  field_simp [hGM_ne]
  ring

private lemma oscPhase_approx {k : ℕ} (_hk : 1 ≤ k) {t : ℝ} (ht : 4 ≤ t) :
    |oscPhase k t - (2 * Real.log (t / (2 * Real.pi)) - Real.log (k : ℝ))| ≤ 8 / t := by
  have ht_pos : 0 < t := by linarith
  have hlog : 2 * Real.log (t / 2) - 2 * Real.log Real.pi = 2 * Real.log (t / (2 * Real.pi)) := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
    ring
  have hdiff : oscPhase k t - (2 * Real.log (t / (2 * Real.pi)) - Real.log (k : ℝ)) =
      2 * (psiRe t - Real.log (t / 2)) := by
    unfold oscPhase
    linarith [hlog]
  rw [hdiff, abs_mul, abs_of_pos two_pos]
  have hpsi := psiRe_approx ht
  linarith [show 2 * (4 / t) = 8 / t by ring]

private lemma oscUnit_integral_bound {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    {T : ℝ} (hT : 10000 ≤ T) (hnT : 2 * Real.pi * (n : ℝ) ≤ T) :
    let a := max (10000 : ℝ) (2 * Real.pi * (n : ℝ))
    (2 * m ≤ n → ‖∫ t in a..T, oscUnit (m * n) t‖ ≤ 8) ∧
    (m + 4 ≤ n → n < 2 * m → ‖∫ t in a..T, oscUnit (m * n) t‖ ≤ 12 * (m : ℝ) / ((n - m : ℕ) : ℝ)) ∧
    (n < m + 4 → ‖∫ t in a..T, oscUnit (m * n) t‖ ≤ 4200 * Real.sqrt (m : ℝ)) := by
  intro a
  have ha_ge : 10000 ≤ a := le_max_left _ _
  have ha_ge2 : 2 * Real.pi * (n : ℝ) ≤ a := le_max_right _ _
  have haT : a ≤ T := max_le hT hnT
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmn1 : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  have hφ_deriv : ∀ t : ℝ, HasDerivAt (oscPhase (m * n)) (2 * psiReDeriv t) t := by
    intro t
    unfold oscPhase
    exact (((hasDerivAt_psiRe t).const_mul 2).sub_const (2 * Real.log Real.pi)).sub_const
      (Real.log ((m * n : ℕ) : ℝ))
  have hφ'_cont : Continuous (fun t => 2 * psiReDeriv t) := continuous_const.mul continuous_psiReDeriv
  have hφ'_ge : ∀ t : ℝ, 4 ≤ t → 2 / (5 * t) ≤ 2 * psiReDeriv t := fun t ht => by
    have h := psiReDeriv_ge_inv_five_t ht
    linarith [show 2 * (1 / (5 * t)) = 2 / (5 * t) by ring]
  have hφ_a_lb : Real.log ((n : ℝ) / (m : ℝ)) - 8 / a ≤ oscPhase (m * n) a := by
    have h1 := oscPhase_approx hmn1 (show 4 ≤ a by linarith)
    rw [abs_le] at h1
    have hlog_ge : Real.log ((n : ℝ) / (m : ℝ)) ≤ 2 * Real.log (a / (2 * Real.pi)) - Real.log ((m * n : ℕ) : ℝ) := by
      have hna : (n : ℝ) ≤ a / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
        linarith
      have hln := Real.log_le_log hn_pos hna
      rw [Nat.cast_mul, Real.log_mul hm_pos.ne' hn_pos.ne', Real.log_div hn_pos.ne' hm_pos.ne']
      linarith
    linarith
  have hvdc : ∀ {c d lam : ℝ}, 4 ≤ c → c ≤ d → 0 < lam → lam ≤ oscPhase (m * n) c →
      ‖∫ t in c..d, oscUnit (m * n) t‖ ≤ 2 / lam := by
    intro c d lam hc4 hcd hlam hlo
    refine van_der_corput_first_deriv hcd hlam
      (fun t _ => norm_oscUnit (m * n) t)
      (fun t _ => hasDerivAt_oscUnit hmn1 t)
      (fun t _ => hφ_deriv t)
      hφ'_cont.continuousOn
      (fun t ht => ?_)
      hlo
    rw [Set.uIcc_of_le hcd] at ht
    have ht4 : 4 ≤ t := hc4.trans ht.1
    have := hφ'_ge t ht4
    have ht_pos : 0 < t := by linarith
    have : 0 ≤ 2 / (5 * t) := by positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- Case A: 2 * m ≤ n
    intro h2m
    have hratio : (2 : ℝ) ≤ (n : ℝ) / (m : ℝ) := by
      rw [le_div_iff₀ hm_pos]
      exact_mod_cast h2m
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log ((n : ℝ) / (m : ℝ)) := by
      have h1 := Real.log_le_log two_pos hratio
      have h2 := Real.log_two_gt_d9
      linarith
    have h8a : 8 / a ≤ 1 / 4 := by
      rw [div_le_iff₀ (by linarith : 0 < a)]; linarith
    have hlo : (1 / 4 : ℝ) ≤ oscPhase (m * n) a := by linarith
    have hb := hvdc (by linarith) haT (by norm_num) hlo
    linarith [show (2 : ℝ) / (1 / 4 : ℝ) = 8 by norm_num]
  · -- Case B: m + 4 ≤ n < 2 * m
    intro hge4 hlt2m
    set k : ℕ := n - m
    have hk4 : 4 ≤ k := by omega
    have hkm : k < m := by omega
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn_eq : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
      have : n = m + k := by omega
      exact_mod_cast this
    have hlog_lb : (k : ℝ) / (2 * (m : ℝ)) ≤ Real.log ((n : ℝ) / (m : ℝ)) := by
      have h1 : (n : ℝ) / (m : ℝ) = 1 + (k : ℝ) / (m : ℝ) := by
        rw [hn_eq, add_div, div_self hm_pos.ne']
      rw [h1]
      set x : ℝ := (k : ℝ) / (m : ℝ)
      have hx_nn : 0 ≤ x := by positivity
      have hx_le1 : x ≤ 1 := by
        dsimp [x]; rw [div_le_one hm_pos]; exact_mod_cast hkm.le
      have hexp : 1 / (1 + x) ≤ Real.exp (-(x / (1 + x))) := by
        have h := Real.add_one_le_exp (-(x / (1 + x)))
        have heq : -(x / (1 + x)) + 1 = 1 / (1 + x) := by
          field_simp [show (1 + x) ≠ 0 by linarith]; ring
        linarith
      have hlog := Real.log_le_log (by positivity : 0 < 1 / (1 + x)) hexp
      rw [Real.log_div one_ne_zero (by linarith : 1 + x ≠ 0), Real.log_one, zero_sub,
        Real.log_exp] at hlog
      have h2 : x / 2 ≤ x / (1 + x) := by
        rw [div_le_div_iff₀ two_pos (by linarith : 0 < 1 + x)]
        nlinarith
      dsimp [x] at h2 ⊢
      linarith [show (k : ℝ) / (m : ℝ) / 2 = (k : ℝ) / (2 * (m : ℝ)) by ring]
    have ha_6m : 6 * (m : ℝ) ≤ a := by
      have hpi : 3 < Real.pi := Real.pi_gt_three
      have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      nlinarith
    have h8a : 8 / a ≤ 4 / (3 * (m : ℝ)) := by
      rw [div_le_div_iff₀ (by linarith : 0 < a) (by positivity)]
      nlinarith
    have hlo : (k : ℝ) / (6 * (m : ℝ)) ≤ oscPhase (m * n) a := by
      have hk4R : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
      have hdiff : (k : ℝ) / (6 * (m : ℝ)) ≤ (k : ℝ) / (2 * (m : ℝ)) - 4 / (3 * (m : ℝ)) := by
        rw [show (k : ℝ) / (2 * (m : ℝ)) - 4 / (3 * (m : ℝ)) = (3 * (k : ℝ) - 8) / (6 * (m : ℝ)) by
          field_simp [hm_pos.ne']; ring]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
    have hb := hvdc (by linarith) haT (by positivity) hlo
    calc ‖∫ t in a..T, oscUnit (m * n) t‖
        ≤ 2 / ((k : ℝ) / (6 * (m : ℝ))) := hb
      _ = 12 * (m : ℝ) / (k : ℝ) := by field_simp [hk_pos.ne', hm_pos.ne']; ring
  · -- Case C: m ≤ n < m + 4
    intro hlt4
    set δ : ℝ := 40 * Real.sqrt a
    have hsqrt_a_ge : 100 ≤ Real.sqrt a := by
      rw [show (100 : ℝ) = Real.sqrt 10000 by norm_num]
      exact Real.sqrt_le_sqrt ha_ge
    have hsqrt_a_pos : 0 < Real.sqrt a := by linarith
    have hδ_pos : 0 < δ := by positivity
    have hδ_le_a : δ ≤ a := by
      have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt (by linarith)
      dsimp [δ]; nlinarith
    have hu_cont : Continuous (oscUnit (m * n)) :=
      continuous_iff_continuousAt.mpr fun u => (hasDerivAt_oscUnit hmn1 u).continuousAt
    have htriv : ∀ {c d : ℝ}, c ≤ d → ‖∫ t in c..d, oscUnit (m * n) t‖ ≤ d - c := by
      intro c d hcd
      calc ‖∫ t in c..d, oscUnit (m * n) t‖
          ≤ ∫ t in c..d, ‖oscUnit (m * n) t‖ := intervalIntegral.norm_integral_le_integral_norm hcd
        _ = ∫ _t in c..d, (1 : ℝ) := intervalIntegral.integral_congr fun t _ => norm_oscUnit (m * n) t
        _ = d - c := by simp
    have hbound_a : ‖∫ t in a..T, oscUnit (m * n) t‖ ≤ 42 * Real.sqrt a := by
      rcases le_or_gt T (a + δ) with hshort | hlong
      · have := htriv haT
        dsimp [δ] at hshort
        linarith
      · have hsplit : (∫ t in a..T, oscUnit (m * n) t) =
            (∫ t in a..(a + δ), oscUnit (m * n) t) + (∫ t in (a + δ)..T, oscUnit (m * n) t) :=
          (intervalIntegral.integral_add_adjacent_intervals
            (hu_cont.intervalIntegrable _ _) (hu_cont.intervalIntegrable _ _)).symm
        have hpart1 : ‖∫ t in a..(a + δ), oscUnit (m * n) t‖ ≤ 40 * Real.sqrt a := by
          have := htriv (show a ≤ a + δ by linarith)
          dsimp [δ] at this ⊢; linarith
        -- Lower bound oscPhase at a + δ
        have hinc : 8 / Real.sqrt a ≤ oscPhase (m * n) (a + δ) - oscPhase (m * n) a := by
          have hftc : oscPhase (m * n) (a + δ) - oscPhase (m * n) a =
              ∫ t in a..(a + δ), 2 * psiReDeriv t :=
            (intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun t _ => hφ_deriv t) (hφ'_cont.intervalIntegrable a (a + δ))).symm
          rw [hftc]
          have hlb : ∀ t ∈ Set.Icc a (a + δ), 1 / (5 * a) ≤ 2 * psiReDeriv t := by
            intro t ht
            have ht4 : 4 ≤ t := by linarith [ht.1]
            have ht_le : t ≤ 2 * a := by linarith [ht.2]
            have h1 := hφ'_ge t ht4
            have h2 : 1 / (5 * a) ≤ 2 / (5 * t) := by
              rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
            linarith
          calc 8 / Real.sqrt a
              = (a + δ - a) * (1 / (5 * a)) := by
                have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
                dsimp [δ]
                rw [add_sub_cancel_left]
                field_simp [hsqrt_a_pos.ne', (show a ≠ 0 by linarith)]
                nlinarith
            _ = ∫ _t in a..(a + δ), (1 / (5 * a)) := by simp; ring
            _ ≤ ∫ t in a..(a + δ), 2 * psiReDeriv t :=
                intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
                  (hφ'_cont.intervalIntegrable a (a + δ)) hlb
        have hφ_a_neg : -(1 / Real.sqrt a) ≤ oscPhase (m * n) a := by
          have hlog_nn : 0 ≤ Real.log ((n : ℝ) / (m : ℝ)) :=
            Real.log_nonneg ((one_le_div hm_pos).mpr (by exact_mod_cast hmn))
          have h8a : 8 / a ≤ 1 / Real.sqrt a := by
            rw [div_le_div_iff₀ (by linarith) hsqrt_a_pos]
            have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt (by linarith)
            nlinarith
          linarith
        have hlo : 1 / Real.sqrt a ≤ oscPhase (m * n) (a + δ) := by
          have hpos : (0 : ℝ) < 1 / Real.sqrt a := by positivity
          have heq : 8 / Real.sqrt a - 1 / Real.sqrt a = 7 * (1 / Real.sqrt a) := by ring
          linarith
        have hpart2 : ‖∫ t in (a + δ)..T, oscUnit (m * n) t‖ ≤ 2 * Real.sqrt a := by
          have hb := hvdc (by linarith) hlong.le (by positivity) hlo
          simpa [div_div_eq_mul_div] using hb
        rw [hsplit]
        exact (norm_add_le _ _).trans (by linarith)
    have hsqrt_le : Real.sqrt a ≤ 100 * Real.sqrt (m : ℝ) := by
      have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have ha_le_m : a ≤ 10000 * (m : ℝ) := by
        dsimp [a]
        apply max_le
        · nlinarith
        · have hn_le : (n : ℝ) ≤ 5 * (m : ℝ) := by
            have : n ≤ 5 * m := by omega
            exact_mod_cast this
          have hpi_lt : Real.pi < 4 := Real.pi_lt_four
          nlinarith
      calc Real.sqrt a ≤ Real.sqrt (10000 * (m : ℝ)) := Real.sqrt_le_sqrt ha_le_m
        _ = Real.sqrt 10000 * Real.sqrt (m : ℝ) := Real.sqrt_mul (by norm_num) (m : ℝ)
        _ = 100 * Real.sqrt (m : ℝ) := by norm_num
    linarith

/- ### Section 5: Total Off-Diagonal and Cross-Term Bounds and Final Assembly -/

private lemma offDiag_sum_bound {T : ℝ} (hT : 2 * Real.pi ≤ T) :
    let N := ⌊T / (2 * Real.pi)⌋₊
    |∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      if m ≠ n then
        ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
          (dirTerm m t * star (dirTerm n t)).re
      else 0| ≤
      200 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 3 := by
  intro N
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by
    intro h0
    have := Nat.floor_eq_zero.mp h0
    have : (1 : ℝ) ≤ T / (2 * Real.pi) := (one_le_div h2pi).mpr hT
    linarith)
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- Symmetry: bound by 2 * ∑_{1 ≤ m < n ≤ N} |∫|
  have hsym : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      |∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
        (dirTerm m t * star (dirTerm n t)).re| =
      |∫ t in (max (2 * Real.pi * (n : ℝ)) (2 * Real.pi * (m : ℝ)))..T,
        (dirTerm n t * star (dirTerm m t)).re| := by
    intro m n _ _
    rw [max_comm]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hconj : (dirTerm m t * star (dirTerm n t)).re =
        (star (dirTerm m t * star (dirTerm n t))).re := by
      simp
    rw [hconj, star_mul', star_star, mul_comm]
  have htri : |∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      if m ≠ n then
        ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
          (dirTerm m t * star (dirTerm n t)).re
      else 0| ≤
      2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        if m < n then
          |∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
            (dirTerm m t * star (dirTerm n t)).re|
        else 0 := by
    have h1 : |∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if m ≠ n then
            ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
              (dirTerm m t * star (dirTerm n t)).re
          else 0| ≤
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          |if m ≠ n then
            ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
              (dirTerm m t * star (dirTerm n t)).re
          else 0| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _)
    have hsplit : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          |if m ≠ n then
            ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
              (dirTerm m t * star (dirTerm n t)).re
          else 0| =
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if m < n then
            |∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
              (dirTerm m t * star (dirTerm n t)).re|
          else 0) +
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if n < m then
            |∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
              (dirTerm m t * star (dirTerm n t)).re|
          else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rcases lt_trichotomy m n with hlt | rfl | hgt
      · simp [hlt, hlt.ne, hlt.not_gt]
      · simp
      · simp [hgt, hgt.ne', hgt.not_gt]
    have hswap : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if n < m then
            |∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
              (dirTerm m t * star (dirTerm n t)).re|
          else 0) =
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if m < n then
            |∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
              (dirTerm m t * star (dirTerm n t)).re|
          else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
      by_cases h : m < n
      · simp only [if_pos h]
        exact hsym n m (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1
      · simp [h]
    linarith
  -- Bound each term m < n
  have hpair : ∀ m ∈ Finset.Icc 1 N, ∀ n ∈ Finset.Icc 1 N, m < n →
      |∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
        (dirTerm m t * star (dirTerm n t)).re| ≤
      (if 2 * m ≤ n then 4 * (divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ)) else 0) +
      (if n < 2 * m then 4 * divFn m * divFn n / ((n - m : ℕ) : ℝ) else 0) := by
    intro m hm n hn hlt
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlog_pos : 0 < Real.log (n : ℝ) - Real.log (m : ℝ) :=
      sub_pos.mpr (Real.log_lt_log hm_pos (by exact_mod_cast hlt))
    have hre_le : |∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
        (dirTerm m t * star (dirTerm n t)).re| ≤
        (divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ)) *
          (2 / (Real.log (n : ℝ) - Real.log (m : ℝ))) := by
      set a := max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))
      have hC : ∫ t in a..T, (dirTerm m t * star (dirTerm n t)).re =
          (∫ t in a..T, dirTerm m t * star (dirTerm n t)).re := by
        have hcont : Continuous (fun t => dirTerm m t * star (dirTerm n t)) :=
          (continuous_dirTerm hm1).mul (continuous_star.comp (continuous_dirTerm hn1))
        exact Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable a T)
      rw [hC]
      refine (Complex.abs_re_le_norm _).trans ?_
      have heq : (fun t => dirTerm m t * star (dirTerm n t)) =
          fun t => ((divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (((Real.log (n : ℝ) - Real.log (m : ℝ)) * t : ℝ) : ℂ)) :=
        funext (dirTerm_mul_star hm1 hn1)
      rw [heq, intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hb := norm_integral_cexp_linear_le (a := a) (b := T) hlog_pos.ne'
      rwa [abs_of_pos hlog_pos] at hb
    refine hre_le.trans ?_
    by_cases h2m : 2 * m ≤ n
    · simp only [if_pos h2m, if_neg (by omega : ¬ n < 2 * m), add_zero]
      have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
        rw [← Real.log_div hn_pos.ne' hm_pos.ne']
        have h1 : (2 : ℝ) ≤ (n : ℝ) / (m : ℝ) := by
          rw [le_div_iff₀ hm_pos]; exact_mod_cast h2m
        linarith [Real.log_le_log two_pos h1, Real.log_two_gt_d9]
      have hfrac : 2 / (Real.log (n : ℝ) - Real.log (m : ℝ)) ≤ 4 := by
        rw [div_le_iff₀ hlog_pos]; linarith
      rw [Nat.cast_mul, Real.sqrt_mul hm_pos.le]
      calc (divFn m * divFn n / (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ))) *
            (2 / (Real.log (n : ℝ) - Real.log (m : ℝ)))
          ≤ (divFn m * divFn n / (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ))) * 4 :=
            mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = 4 * (divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ)) := by ring
    · have hlt2m : n < 2 * m := by omega
      simp only [if_neg h2m, if_pos hlt2m, zero_add]
      set k : ℕ := n - m
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
      have hkm : k < m := by omega
      have hn_eq : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
        have : n = m + k := by omega
        exact_mod_cast this
      have hlog_ge : (k : ℝ) / (2 * (m : ℝ)) ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
        rw [← Real.log_div hn_pos.ne' hm_pos.ne', hn_eq, add_div, div_self hm_pos.ne']
        set x : ℝ := (k : ℝ) / (m : ℝ)
        have hx_le1 : x ≤ 1 := by dsimp [x]; rw [div_le_one hm_pos]; exact_mod_cast hkm.le
        have hx_nn : 0 ≤ x := by positivity
        have hexp : 1 / (1 + x) ≤ Real.exp (-(x / (1 + x))) := by
          have h := Real.add_one_le_exp (-(x / (1 + x)))
          have heq : -(x / (1 + x)) + 1 = 1 / (1 + x) := by
            field_simp [show (1 + x) ≠ 0 by linarith]; ring
          linarith
        have hlog := Real.log_le_log (by positivity : 0 < 1 / (1 + x)) hexp
        rw [Real.log_div one_ne_zero (by linarith : 1 + x ≠ 0), Real.log_one, zero_sub,
          Real.log_exp] at hlog
        have h2 : x / 2 ≤ x / (1 + x) := by
          rw [div_le_div_iff₀ two_pos (by linarith : 0 < 1 + x)]; nlinarith
        dsimp [x] at h2 ⊢
        linarith [show (k : ℝ) / (m : ℝ) / 2 = (k : ℝ) / (2 * (m : ℝ)) by ring]
      have hfrac : 2 / (Real.log (n : ℝ) - Real.log (m : ℝ)) ≤ 4 * (m : ℝ) / (k : ℝ) := by
        calc 2 / (Real.log (n : ℝ) - Real.log (m : ℝ))
            ≤ 2 / ((k : ℝ) / (2 * (m : ℝ))) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) hlog_ge
          _ = 4 * (m : ℝ) / (k : ℝ) := by field_simp [hk_pos.ne', hm_pos.ne']; ring
      have hsqrt_ge : (m : ℝ) ≤ Real.sqrt ((m * n : ℕ) : ℝ) := by
        rw [Real.le_sqrt hm_pos.le (by positivity)]
        have : m * m ≤ m * n := Nat.mul_le_mul_left m hlt.le
        rw [sq]; exact_mod_cast this
      calc (divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ)) *
            (2 / (Real.log (n : ℝ) - Real.log (m : ℝ)))
          ≤ (divFn m * divFn n / (m : ℝ)) * (4 * (m : ℝ) / (k : ℝ)) := by
            refine mul_le_mul ?_ hfrac (by positivity) (by positivity)
            exact div_le_div_of_nonneg_left (mul_nonneg (divFn_nonneg m) (divFn_nonneg n))
              hm_pos hsqrt_ge
        _ = 4 * divFn m * divFn n / (k : ℝ) := by field_simp [hm_pos.ne', hk_pos.ne']
  -- Sum the two regimes
  have hsum_le : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if m < n then
          |∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
            (dirTerm m t * star (dirTerm n t)).re|
        else 0) ≤
      (4 * (∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ)) ^ 2) +
      (4 * ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) * ∑ m ∈ Finset.Icc 1 N, divFn m * divFn (m + k)) := by
    have hstep1 : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if m < n then
            |∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
              (dirTerm m t * star (dirTerm n t)).re|
          else 0) ≤
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          4 * (divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ))) +
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if m < n ∧ n < 2 * m then 4 * divFn m * divFn n / ((n - m : ℕ) : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun m hm => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n hn => ?_
      by_cases hlt : m < n
      · rw [if_pos hlt]
        refine (hpair m hm n hn hlt).trans ?_
        apply add_le_add
        · split_ifs
          · exact le_rfl
          · positivity
        · by_cases h2 : n < 2 * m
          · simp [hlt, h2]
          · simp [hlt, h2]
      · rw [if_neg hlt]
        have hnot : ¬ (m < n ∧ n < 2 * m) := fun h => hlt h.1
        rw [if_neg hnot, add_zero]
        positivity
    refine hstep1.trans (add_le_add ?_ ?_)
    · have heq : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          4 * (divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ)) =
          4 * (∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ)) ^ 2 := by
        simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
      exact le_of_eq heq
    · -- Reindex (m, n) with m < n < 2m to (k, m) with k = n - m ∈ Icc 1 N
      rw [← Finset.sum_product']
      have hRHS : 4 * ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) *
            ∑ m ∈ Finset.Icc 1 N, divFn m * divFn (m + k) =
          ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
            4 * divFn p.2 * divFn (p.2 + p.1) / (p.1 : ℝ) := by
        rw [Finset.sum_product, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => by ring
      rw [hRHS]
      refine sum_le_sum_of_injOn (fun p => (p.2 - p.1, p.1)) ?_ ?_ ?_ ?_
      · intro p hp hne
        simp only [Finset.mem_product, Finset.mem_Icc] at hp ⊢
        have hcond : p.1 < p.2 ∧ p.2 < 2 * p.1 := by
          by_contra hc; simp [hc] at hne
        exact ⟨⟨by omega, by omega⟩, hp.1⟩
      · intro p₁ _ hne₁ p₂ _ hne₂ heq
        have hc₁ : p₁.1 < p₁.2 ∧ p₁.2 < 2 * p₁.1 := by
          by_contra hc; simp [hc] at hne₁
        have hc₂ : p₂.1 < p₂.2 ∧ p₂.2 < 2 * p₂.1 := by
          by_contra hc; simp [hc] at hne₂
        simp only [Prod.mk.injEq] at heq
        ext <;> omega
      · intro p _
        positivity
      · intro p _ hne
        have hc : p.1 < p.2 ∧ p.2 < 2 * p.1 := by
          by_contra hc; simp [hc] at hne
        rw [if_pos hc]
        dsimp only
        rw [Nat.add_sub_of_le hc.1.le]
  have hlog_ge1 : 1 ≤ Real.log (2 * (N : ℝ)) + 1 := by
    have : (1 : ℝ) ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      linarith
    linarith [Real.log_nonneg this]
  have hlogN_le : Real.log (N : ℝ) + 1 ≤ Real.log (2 * (N : ℝ)) + 1 := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    linarith [Real.log_le_log hN_pos (show (N : ℝ) ≤ 2 * (N : ℝ) by linarith)]
  have hb1 : (∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ)) ^ 2 ≤
      4 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 2 := by
    have h1 := sum_divFn_div_sqrt_le hN1
    have hnn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have h2 : ∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ) ≤
        2 * Real.sqrt (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) := by
      refine h1.trans (mul_le_mul_of_nonneg_left hlogN_le (by positivity))
    calc (∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ)) ^ 2
        ≤ (2 * Real.sqrt (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1)) ^ 2 :=
          pow_le_pow_left₀ hnn h2 2
      _ = 4 * (Real.sqrt (N : ℝ) ^ 2) * (Real.log (2 * (N : ℝ)) + 1) ^ 2 := by ring
      _ = 4 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 2 := by rw [Real.sq_sqrt hN_nn]
  have hb2 := shifted_divFn_sum_le hN1
  nlinarith

private lemma cross_sum_bound {T : ℝ} (hT : 10000 ≤ T) :
    let N := ⌊T / (2 * Real.pi)⌋₊
    |∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      ∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
        (star (chi2 t) * (dirTerm m t * dirTerm n t)).re| ≤
      200000 * ((N : ℝ) + 4) * (Real.log (2 * ((N : ℝ) + 4)) + 1) ^ 3 := by
  intro N
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by
    intro h0
    have := Nat.floor_eq_zero.mp h0
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have : (1 : ℝ) ≤ T / (2 * Real.pi) := (one_le_div h2pi).mpr (by linarith)
    linarith)
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- Symmetry: bound by 2 * ∑_{1 ≤ m ≤ n ≤ N} |∫|
  have hsym : ∀ m n : ℕ,
      |∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
        (star (chi2 t) * (dirTerm m t * dirTerm n t)).re| =
      |∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (n : ℝ)) (2 * Real.pi * (m : ℝ))))..T,
        (star (chi2 t) * (dirTerm n t * dirTerm m t)).re| := by
    intro m n
    rw [max_comm (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mul_comm (dirTerm m t) (dirTerm n t)]
  have htri : |∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      ∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
        (star (chi2 t) * (dirTerm m t * dirTerm n t)).re| ≤
      2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        if m ≤ n then
          |∫ t in (max (10000 : ℝ) (2 * Real.pi * (n : ℝ)))..T,
            (star (chi2 t) * (dirTerm m t * dirTerm n t)).re|
        else 0 := by
    have h1 : |∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
            (star (chi2 t) * (dirTerm m t * dirTerm n t)).re| ≤
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          |∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
            (star (chi2 t) * (dirTerm m t * dirTerm n t)).re| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _)
    have hsplit : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          |∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
            (star (chi2 t) * (dirTerm m t * dirTerm n t)).re| ≤
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if m ≤ n then
            |∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
              (star (chi2 t) * (dirTerm m t * dirTerm n t)).re|
          else 0) +
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if n ≤ m then
            |∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
              (star (chi2 t) * (dirTerm m t * dirTerm n t)).re|
          else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun m _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n _ => ?_
      rcases le_total m n with hle | hge
      · rw [if_pos hle]
        split_ifs <;> linarith [abs_nonneg (∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
          (star (chi2 t) * (dirTerm m t * dirTerm n t)).re)]
      · rw [if_pos hge]
        split_ifs <;> linarith [abs_nonneg (∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
          (star (chi2 t) * (dirTerm m t * dirTerm n t)).re)]
    have hswap : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if n ≤ m then
            |∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
              (star (chi2 t) * (dirTerm m t * dirTerm n t)).re|
          else 0) =
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if m ≤ n then
            |∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
              (star (chi2 t) * (dirTerm m t * dirTerm n t)).re|
          else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      by_cases h : m ≤ n
      · simp only [if_pos h]; exact hsym n m
      · simp [h]
    have hsimp_max : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if m ≤ n then
            |∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
              (star (chi2 t) * (dirTerm m t * dirTerm n t)).re|
          else 0) =
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if m ≤ n then
            |∫ t in (max (10000 : ℝ) (2 * Real.pi * (n : ℝ)))..T,
              (star (chi2 t) * (dirTerm m t * dirTerm n t)).re|
          else 0) := by
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      by_cases h : m ≤ n
      · simp only [if_pos h]
        have hmax : max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)) = 2 * Real.pi * (n : ℝ) :=
          max_eq_right (mul_le_mul_of_nonneg_left (by exact_mod_cast h) h2pi.le)
        rw [hmax]
      · simp [h]
    linarith
  -- Pairwise bound for 1 ≤ m ≤ n ≤ N
  have hpair : ∀ m ∈ Finset.Icc 1 N, ∀ n ∈ Finset.Icc 1 N, m ≤ n →
      |∫ t in (max (10000 : ℝ) (2 * Real.pi * (n : ℝ)))..T,
        (star (chi2 t) * (dirTerm m t * dirTerm n t)).re| ≤
      8 * (divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ)) +
      (if m + 4 ≤ n ∧ n < 2 * m then 12 * divFn m * divFn n / ((n - m : ℕ) : ℝ) else 0) +
      (if n < m + 4 then 8400 * divFn n else 0) := by
    intro m hm n hn hmn
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hnT : 2 * Real.pi * (n : ℝ) ≤ T := by
      have h1 : (n : ℝ) ≤ T / (2 * Real.pi) :=
        (Nat.le_floor_iff (div_nonneg (by linarith) h2pi.le)).mp (Finset.mem_Icc.mp hn).2
      linarith [(le_div_iff₀ h2pi).mp h1]
    set a := max (10000 : ℝ) (2 * Real.pi * (n : ℝ))
    have hre_le : |∫ t in a..T, (star (chi2 t) * (dirTerm m t * dirTerm n t)).re| ≤
        (divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ)) * ‖∫ t in a..T, oscUnit (m * n) t‖ := by
      have hcont : Continuous (fun t => star (chi2 t) * (dirTerm m t * dirTerm n t)) :=
        (continuous_star.comp continuous_chi2).mul
          ((continuous_dirTerm hm1).mul (continuous_dirTerm hn1))
      have hC : ∫ t in a..T, (star (chi2 t) * (dirTerm m t * dirTerm n t)).re =
          (∫ t in a..T, star (chi2 t) * (dirTerm m t * dirTerm n t)).re :=
        Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable a T)
      rw [hC]
      refine (Complex.abs_re_le_norm _).trans ?_
      have heq : (fun t => star (chi2 t) * (dirTerm m t * dirTerm n t)) =
          fun t => ((divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ) : ℝ) : ℂ) * oscUnit (m * n) t := by
        ext t
        rw [dirTerm_mul_dirTerm hm1 hn1 t]
        unfold oscUnit
        ring
      rw [heq, intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    obtain ⟨hA, hB, hC⟩ := oscUnit_integral_bound hm1 hmn hT hnT
    have hsqrt_ge : (m : ℝ) ≤ Real.sqrt ((m * n : ℕ) : ℝ) := by
      rw [Real.le_sqrt hm_pos.le (by positivity)]
      have : m * m ≤ m * n := Nat.mul_le_mul_left m hmn
      rw [sq]; exact_mod_cast this
    by_cases h2m : 2 * m ≤ n
    · have h1 := hre_le.trans (mul_le_mul_of_nonneg_left (hA h2m) (by positivity))
      have h2 : (divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ)) * 8 =
          8 * (divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ)) := by
        rw [Nat.cast_mul, Real.sqrt_mul hm_pos.le]; ring
      have hnn1 : 0 ≤ (if m + 4 ≤ n ∧ n < 2 * m then 12 * divFn m * divFn n / ((n - m : ℕ) : ℝ) else 0) := by
        split_ifs <;> positivity
      have hnn2 : 0 ≤ (if n < m + 4 then 8400 * divFn n else 0) := by
        split_ifs <;> positivity
      linarith
    · by_cases hge4 : m + 4 ≤ n
      · have hlt2m : n < 2 * m := by omega
        have h1 := hre_le.trans (mul_le_mul_of_nonneg_left (hB hge4 hlt2m) (by positivity))
        have h2 : (divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ)) * (12 * (m : ℝ) / ((n - m : ℕ) : ℝ)) ≤
            12 * divFn m * divFn n / ((n - m : ℕ) : ℝ) := by
          have hk_pos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
          calc (divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ)) * (12 * (m : ℝ) / ((n - m : ℕ) : ℝ))
              ≤ (divFn m * divFn n / (m : ℝ)) * (12 * (m : ℝ) / ((n - m : ℕ) : ℝ)) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                exact div_le_div_of_nonneg_left (mul_nonneg (divFn_nonneg m) (divFn_nonneg n))
                  hm_pos hsqrt_ge
            _ = 12 * divFn m * divFn n / ((n - m : ℕ) : ℝ) := by field_simp [hm_pos.ne', hk_pos.ne']
        rw [if_pos ⟨hge4, hlt2m⟩]
        have hnn0 : 0 ≤ 8 * (divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ)) := by positivity
        have hnn2 : 0 ≤ (if n < m + 4 then 8400 * divFn n else 0) := by split_ifs <;> positivity
        linarith
      · have hlt4 : n < m + 4 := by omega
        have h1 := hre_le.trans (mul_le_mul_of_nonneg_left (hC hlt4) (by positivity))
        have hdm : divFn m ≤ 2 * Real.sqrt (m : ℝ) := divFn_le_two_sqrt hm1
        have h2 : (divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ)) * (4200 * Real.sqrt (m : ℝ)) ≤
            8400 * divFn n := by
          have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm_pos.le
          calc (divFn m * divFn n / Real.sqrt ((m * n : ℕ) : ℝ)) * (4200 * Real.sqrt (m : ℝ))
              ≤ (divFn m * divFn n / (m : ℝ)) * (4200 * Real.sqrt (m : ℝ)) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                exact div_le_div_of_nonneg_left (mul_nonneg (divFn_nonneg m) (divFn_nonneg n))
                  hm_pos hsqrt_ge
            _ ≤ ((2 * Real.sqrt (m : ℝ)) * divFn n / (m : ℝ)) * (4200 * Real.sqrt (m : ℝ)) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hdm (divFn_nonneg n)) hm_pos.le
            _ = 8400 * divFn n := by
                field_simp [hm_pos.ne']
                rw [hsq]
                ring
        rw [if_pos hlt4]
        have hnn0 : 0 ≤ 8 * (divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ)) := by positivity
        have hnn1 : 0 ≤ (if m + 4 ≤ n ∧ n < 2 * m then 12 * divFn m * divFn n / ((n - m : ℕ) : ℝ) else 0) := by
          split_ifs <;> positivity
        linarith
  -- Sum the three pieces over 1 ≤ m ≤ n ≤ N
  have hsum_split : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if m ≤ n then
          |∫ t in (max (10000 : ℝ) (2 * Real.pi * (n : ℝ)))..T,
            (star (chi2 t) * (dirTerm m t * dirTerm n t)).re|
        else 0) ≤
      (8 * (∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ)) ^ 2) +
      (12 * ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) * ∑ m ∈ Finset.Icc 1 N, divFn m * divFn (m + k)) +
      (33600 * ∑ x ∈ Finset.Icc 1 (N + 4), divFn x) := by
    have hstep1 : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if m ≤ n then
            |∫ t in (max (10000 : ℝ) (2 * Real.pi * (n : ℝ)))..T,
              (star (chi2 t) * (dirTerm m t * dirTerm n t)).re|
          else 0) ≤
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          8 * (divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ))) +
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if m + 4 ≤ n ∧ n < 2 * m then 12 * divFn m * divFn n / ((n - m : ℕ) : ℝ) else 0) +
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if m ≤ n ∧ n < m + 4 then 8400 * divFn n else 0) := by
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => ?_
      by_cases hmn : m ≤ n
      · rw [if_pos hmn]
        refine (hpair m hm n hn hmn).trans ?_
        have hiff : (m ≤ n ∧ n < m + 4) ↔ n < m + 4 := and_iff_right hmn
        simp only [hiff, le_rfl]
      · rw [if_neg hmn]
        have hnot1 : ¬ (m + 4 ≤ n ∧ n < 2 * m) := fun h => hmn (by omega)
        have hnot2 : ¬ (m ≤ n ∧ n < m + 4) := fun h => hmn h.1
        rw [if_neg hnot1, if_neg hnot2, add_zero, add_zero]
        positivity
    refine hstep1.trans (add_le_add (add_le_add ?_ ?_) ?_)
    · have heq : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          8 * (divFn m / Real.sqrt (m : ℝ)) * (divFn n / Real.sqrt (n : ℝ)) =
          8 * (∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ)) ^ 2 := by
        simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
      exact le_of_eq heq
    · rw [← Finset.sum_product']
      have hRHS : 12 * ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) *
            ∑ m ∈ Finset.Icc 1 N, divFn m * divFn (m + k) =
          ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
            12 * divFn p.2 * divFn (p.2 + p.1) / (p.1 : ℝ) := by
        rw [Finset.sum_product, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => by ring
      rw [hRHS]
      refine sum_le_sum_of_injOn (fun p => (p.2 - p.1, p.1)) ?_ ?_ ?_ ?_
      · intro p hp hne
        simp only [Finset.mem_product, Finset.mem_Icc] at hp ⊢
        have hc : p.1 + 4 ≤ p.2 ∧ p.2 < 2 * p.1 := by
          by_contra hc; simp [hc] at hne
        exact ⟨⟨by omega, by omega⟩, hp.1⟩
      · intro p₁ _ hne₁ p₂ _ hne₂ heq
        have hc₁ : p₁.1 + 4 ≤ p₁.2 ∧ p₁.2 < 2 * p₁.1 := by by_contra hc; simp [hc] at hne₁
        have hc₂ : p₂.1 + 4 ≤ p₂.2 ∧ p₂.2 < 2 * p₂.1 := by by_contra hc; simp [hc] at hne₂
        simp only [Prod.mk.injEq] at heq
        ext <;> omega
      · intro p _
        positivity
      · intro p _ hne
        have hc : p.1 + 4 ≤ p.2 ∧ p.2 < 2 * p.1 := by by_contra hc; simp [hc] at hne
        rw [if_pos hc]
        dsimp only
        rw [Nat.add_sub_of_le (by omega : p.1 ≤ p.2)]
    · -- Near-diagonal sum: m ≤ n < m + 4 → map (m, n) to (n - m, n) ∈ range 4 × Icc 1 (N + 4)
      rw [← Finset.sum_product']
      have hRHS : 33600 * ∑ x ∈ Finset.Icc 1 (N + 4), divFn x =
          ∑ q ∈ (Finset.range 4) ×ˢ (Finset.Icc 1 (N + 4)), 8400 * divFn q.2 := by
        rw [Finset.sum_product]
        dsimp only
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
        ring
      rw [hRHS]
      refine sum_le_sum_of_injOn (fun p => (p.2 - p.1, p.2)) ?_ ?_ ?_ ?_
      · intro p hp hne
        simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hp ⊢
        have hc : p.1 ≤ p.2 ∧ p.2 < p.1 + 4 := by by_contra hc; simp [hc] at hne
        exact ⟨by omega, ⟨by omega, by omega⟩⟩
      · intro p₁ _ hne₁ p₂ _ hne₂ heq
        have hc₁ : p₁.1 ≤ p₁.2 ∧ p₁.2 < p₁.1 + 4 := by by_contra hc; simp [hc] at hne₁
        have hc₂ : p₂.1 ≤ p₂.2 ∧ p₂.2 < p₂.1 + 4 := by by_contra hc; simp [hc] at hne₂
        simp only [Prod.mk.injEq] at heq
        ext <;> omega
      · intro q _
        have := divFn_nonneg q.2; positivity
      · intro p _ hne
        have hc : p.1 ≤ p.2 ∧ p.2 < p.1 + 4 := by by_contra hc; simp [hc] at hne
        rw [if_pos hc]
  -- Combine all three elementary bounds
  set L := Real.log (2 * ((N : ℝ) + 4)) + 1
  have hL_ge1 : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 * ((N : ℝ) + 4) by linarith)]
  have hlogN_le : Real.log (N : ℝ) + 1 ≤ L := by
    dsimp [L]
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    linarith [Real.log_le_log hN_pos (show (N : ℝ) ≤ 2 * ((N : ℝ) + 4) by linarith)]
  have hlog2N_le : Real.log (2 * (N : ℝ)) + 1 ≤ L := by
    dsimp [L]
    have h2N_pos : (0 : ℝ) < 2 * (N : ℝ) := by positivity
    linarith [Real.log_le_log h2N_pos (show 2 * (N : ℝ) ≤ 2 * ((N : ℝ) + 4) by linarith)]
  have hlogN4_le : Real.log ((N : ℝ) + 4) + 1 ≤ L := by
    dsimp [L]
    have hpos : (0 : ℝ) < (N : ℝ) + 4 := by positivity
    linarith [Real.log_le_log hpos (show (N : ℝ) + 4 ≤ 2 * ((N : ℝ) + 4) by linarith)]
  have hb1 : (∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ)) ^ 2 ≤ 4 * (N : ℝ) * L ^ 2 := by
    have h1 := (sum_divFn_div_sqrt_le hN1).trans (mul_le_mul_of_nonneg_left hlogN_le (by positivity))
    have hnn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    calc (∑ n ∈ Finset.Icc 1 N, divFn n / Real.sqrt (n : ℝ)) ^ 2
        ≤ (2 * Real.sqrt (N : ℝ) * L) ^ 2 := pow_le_pow_left₀ hnn h1 2
      _ = 4 * Real.sqrt (N : ℝ) ^ 2 * L ^ 2 := by ring
      _ = 4 * (N : ℝ) * L ^ 2 := by rw [Real.sq_sqrt hN_nn]
  have hb2 : ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (k : ℝ)) * ∑ m ∈ Finset.Icc 1 N, divFn m * divFn (m + k) ≤
      16 * (N : ℝ) * L ^ 3 := by
    have hnn : 0 ≤ Real.log (2 * (N : ℝ)) + 1 := by
      have : (1 : ℝ) ≤ 2 * (N : ℝ) := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
        linarith
      linarith [Real.log_nonneg this]
    refine (shifted_divFn_sum_le hN1).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hlog2N_le 3) (by positivity)
  have hb3 : ∑ x ∈ Finset.Icc 1 (N + 4), divFn x ≤ ((N : ℝ) + 4) * L := by
    have h := sum_divFn_le (show 1 ≤ N + 4 by omega)
    push_cast at h
    exact h.trans (mul_le_mul_of_nonneg_left hlogN4_le (by positivity))
  have hL_sq : L ≤ L ^ 3 := by nlinarith
  have hL2_le : L ^ 2 ≤ L ^ 3 := by nlinarith
  have hN_le : (N : ℝ) ≤ (N : ℝ) + 4 := by linarith
  nlinarith

private lemma H2_proof : OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1.H2 := by
  unfold OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1.H2
  change (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, ‖modelM t‖ ^ 2) - 2 * ∫ t in (0 : ℝ)..T, diagSum t)
    =o[atTop] fun T : ℝ => T * Real.log T ^ 4
  set C₀ : ℝ := 2 * |∫ t in (0 : ℝ)..(10000 : ℝ), (star (chi2 t) * dirPoly t ^ 2).re|
  have hC₀_nn : 0 ≤ C₀ := by positivity
  -- Show the difference is O(C₀ + T * (log T)^3), hence o(T * (log T)^4)
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖(∫ t in (0 : ℝ)..T, ‖modelM t‖ ^ 2) - 2 * ∫ t in (0 : ℝ)..T, diagSum t‖ ≤
        C₀ + 40000000 * T * Real.log T ^ 3 := by
    filter_upwards [eventually_ge_atTop (10000 : ℝ)] with T hT
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have h2pi_ge : 6 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hdecomp := main_identity_decomp (T₀ := 10000) (by norm_num) hT
    rw [Real.norm_eq_abs, hdecomp]
    set N := ⌊T / (2 * Real.pi)⌋₊
    have hN_le_T : (N : ℝ) ≤ T / 6 := by
      have h1 : (N : ℝ) ≤ T / (2 * Real.pi) := Nat.floor_le (by positivity)
      have h2 : T / (2 * Real.pi) ≤ T / 6 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) h2pi_ge
      linarith
    have hN4_le : (N : ℝ) + 4 ≤ T := by linarith
    have hlogT_ge : 2 ≤ Real.log T := by
      have hexp2 : Real.exp 2 ≤ 10000 := by
        have h1 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1]
      have hle : Real.exp 2 ≤ T := hexp2.trans hT
      have h := Real.log_le_log (Real.exp_pos 2) hle
      rwa [Real.log_exp] at h
    have hlog_bound : Real.log (2 * ((N : ℝ) + 4)) + 1 ≤ 2 * Real.log T := by
      have h1 : 2 * ((N : ℝ) + 4) ≤ T := by linarith
      have h2 : Real.log (2 * ((N : ℝ) + 4)) ≤ Real.log T :=
        Real.log_le_log (by positivity) h1
      linarith
    have hlog2N_bound : Real.log (2 * (N : ℝ)) + 1 ≤ 2 * Real.log T := by
      have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by
        intro h0
        have := Nat.floor_eq_zero.mp h0
        have hpi : Real.pi < 4 := Real.pi_lt_four
        have : (1 : ℝ) ≤ T / (2 * Real.pi) := (one_le_div h2pi).mpr (by linarith)
        linarith)
      have h1 : 2 * (N : ℝ) ≤ 2 * ((N : ℝ) + 4) := by linarith
      have h2 : Real.log (2 * (N : ℝ)) ≤ Real.log (2 * ((N : ℝ) + 4)) :=
        Real.log_le_log (by positivity) h1
      linarith
    have hoff := offDiag_sum_bound (show 2 * Real.pi ≤ T by linarith [Real.pi_lt_four])
    have hcross := cross_sum_bound hT
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hlog2N_nn : 0 ≤ Real.log (2 * (N : ℝ)) + 1 := by
      have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by
        intro h0
        have := Nat.floor_eq_zero.mp h0
        have hpi : Real.pi < 4 := Real.pi_lt_four
        have : (1 : ℝ) ≤ T / (2 * Real.pi) := (one_le_div h2pi).mpr (by linarith)
        linarith)
      have : (1 : ℝ) ≤ 2 * (N : ℝ) := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
        linarith
      linarith [Real.log_nonneg this]
    have hlogN4_nn : 0 ≤ Real.log (2 * ((N : ℝ) + 4)) + 1 := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 * ((N : ℝ) + 4) by linarith)]
    have hcube1 : (Real.log (2 * (N : ℝ)) + 1) ^ 3 ≤ 8 * Real.log T ^ 3 := by
      have := pow_le_pow_left₀ hlog2N_nn hlog2N_bound 3
      linarith [show (2 * Real.log T) ^ 3 = 8 * Real.log T ^ 3 by ring]
    have hcube2 : (Real.log (2 * ((N : ℝ) + 4)) + 1) ^ 3 ≤ 8 * Real.log T ^ 3 := by
      have := pow_le_pow_left₀ hlogN4_nn hlog_bound 3
      linarith [show (2 * Real.log T) ^ 3 = 8 * Real.log T ^ 3 by ring]
    have htri : |2 * (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if m ≠ n then
            ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
              (dirTerm m t * star (dirTerm n t)).re
          else 0) +
        2 * (∫ t in (0 : ℝ)..(10000 : ℝ), (star (chi2 t) * dirPoly t ^ 2).re) +
        2 * (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
            (star (chi2 t) * (dirTerm m t * dirTerm n t)).re)| ≤
        2 * |∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if m ≠ n then
            ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
              (dirTerm m t * star (dirTerm n t)).re
          else 0| + C₀ +
        2 * |∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
            (star (chi2 t) * (dirTerm m t * dirTerm n t)).re| := by
      set A : ℝ := ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        if m ≠ n then
          ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
            (dirTerm m t * star (dirTerm n t)).re
        else 0
      set B : ℝ := ∫ t in (0 : ℝ)..(10000 : ℝ), (star (chi2 t) * dirPoly t ^ 2).re
      set C : ℝ := ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
          (star (chi2 t) * (dirTerm m t * dirTerm n t)).re
      have h1 : |(2 * A + 2 * B) + 2 * C| ≤ |2 * A + 2 * B| + |2 * C| := abs_add_le _ _
      have h2 : |2 * A + 2 * B| ≤ |2 * A| + |2 * B| := abs_add_le _ _
      simp only [abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)] at h1 h2
      have hC₀_eq : C₀ = 2 * |B| := rfl
      linarith
    have hN_le_T' : (N : ℝ) ≤ T := by linarith
    have hlog3_nn : 0 ≤ Real.log T ^ 3 := by positivity
    have hb_off : 200 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 3 ≤ 1600 * T * Real.log T ^ 3 := by
      have h1 : 200 * (N : ℝ) * (Real.log (2 * (N : ℝ)) + 1) ^ 3 ≤ 200 * T * (8 * Real.log T ^ 3) :=
        mul_le_mul (by linarith) hcube1 (by positivity) (by positivity)
      linarith
    have hb_cross : 200000 * ((N : ℝ) + 4) * (Real.log (2 * ((N : ℝ) + 4)) + 1) ^ 3 ≤
        1600000 * T * Real.log T ^ 3 := by
      have h1 : 200000 * ((N : ℝ) + 4) * (Real.log (2 * ((N : ℝ) + 4)) + 1) ^ 3 ≤
          200000 * T * (8 * Real.log T ^ 3) :=
        mul_le_mul (by linarith) hcube2 (by positivity) (by positivity)
      linarith
    have hoff' : |∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        if m ≠ n then
          ∫ t in (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ)))..T,
            (dirTerm m t * star (dirTerm n t)).re
        else 0| ≤ 1600 * T * Real.log T ^ 3 := hoff.trans hb_off
    have hcross' : |∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ∫ t in (max (10000 : ℝ) (max (2 * Real.pi * (m : ℝ)) (2 * Real.pi * (n : ℝ))))..T,
          (star (chi2 t) * (dirTerm m t * dirTerm n t)).re| ≤ 1600000 * T * Real.log T ^ 3 :=
      hcross.trans hb_cross
    have hTlog_nn : 0 ≤ T * Real.log T ^ 3 := by positivity
    linarith
  -- Conclude =o[atTop] (T * (log T)^4)
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h1 : Tendsto (fun T : ℝ => C₀ / (T * Real.log T ^ 4)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    have hlog4 : Tendsto (fun T : ℝ => Real.log T ^ 4) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 4 ≠ 0)).comp Real.tendsto_log_atTop
    exact Filter.Tendsto.atTop_mul_atTop₀ tendsto_id hlog4
  have h2 : Tendsto (fun T : ℝ => (40000000 : ℝ) / Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hev1 : ∀ᶠ T : ℝ in atTop, C₀ / (T * Real.log T ^ 4) < c / 2 :=
    h1.eventually (Iio_mem_nhds (by positivity))
  have hev2 : ∀ᶠ T : ℝ in atTop, (40000000 : ℝ) / Real.log T < c / 2 :=
    h2.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hbound, hev1, hev2, eventually_gt_atTop (2 : ℝ)] with T hT hT1 hT2 hTgt2
  have hTpos : 0 < T := by linarith
  have hlog_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hden_pos : 0 < T * Real.log T ^ 4 := by positivity
  rw [Real.norm_eq_abs (T * Real.log T ^ 4), abs_of_pos hden_pos]
  have hC1 : C₀ < (c / 2) * (T * Real.log T ^ 4) := (div_lt_iff₀ hden_pos).mp hT1
  have hC2 : 40000000 * T * Real.log T ^ 3 < (c / 2) * (T * Real.log T ^ 4) := by
    have hlt := (div_lt_iff₀ hlog_pos).mp hT2
    have hmul := mul_lt_mul_of_pos_right hlt (show 0 < T * Real.log T ^ 3 by positivity)
    linarith [show (c / 2) * Real.log T * (T * Real.log T ^ 3) = (c / 2) * (T * Real.log T ^ 4) by ring,
      show (40000000 : ℝ) * (T * Real.log T ^ 3) = 40000000 * T * Real.log T ^ 3 by ring]
  linarith

end ZetaMomentsH2Proof

theorem OMA.solution : OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1.H2 := by
  exact ZetaMomentsH2Proof.H2_proof
