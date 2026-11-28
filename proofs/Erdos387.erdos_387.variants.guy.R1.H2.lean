import OMAReductions.R_Erdos387_erdos_387_variants_guy_R1

/-!
Proof of Erdos387.erdos_387.variants.guy.R1.H2 via the Rosser-Iwaniec beta-sieve
(fundamental lemma of the combinatorial sieve) for k linear forms on a covered progression.
-/

namespace Erdos387GuyH2

open Finset Filter Real
open scoped Classical

/- ### Section 1: Elementary Mertens Upper Bound from Chebyshev's theta bound -/

lemma theta_diff_nat (n : ℕ) (hn : 1 ≤ n) :
    Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n - 1 : ℕ) : ℝ) =
      if n.Prime then Real.log (n : ℝ) else 0 := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have hsub : n.primesLE = (if n.Prime then {n} else ∅) ∪ (n - 1).primesLE := by
    ext p
    split_ifs with hp
    · simp only [Nat.mem_primesLE, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hpn, hpp⟩
        rcases eq_or_lt_of_le hpn with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨by omega, hpp⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨le_rfl, hp⟩
        · exact ⟨by omega, h2⟩
    · simp only [Nat.mem_primesLE, Finset.mem_union, Finset.notMem_empty, false_or]
      constructor
      · rintro ⟨hpn, hpp⟩
        have hne : p ≠ n := fun h => hp (h ▸ hpp)
        exact ⟨by omega, hpp⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
  rw [hsub]
  split_ifs with hp
  · have hnot : n ∉ (n - 1).primesLE := by
      simp only [Nat.mem_primesLE]; omega
    rw [Finset.singleton_union, Finset.sum_insert hnot]
    ring
  · simp

lemma sum_by_parts_Ioc (f g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, (f n - f (n - 1)) * g n =
      f b * g b - f a * g a +
        ∑ n ∈ Finset.Ico a b, f n * (g n - g (n + 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ioc_succ_top hm, ih, Finset.sum_Ico_succ_top hm]
    have hsub : m + 1 - 1 = m := Nat.add_sub_cancel m 1
    rw [hsub]
    ring

lemma sum_Ico_telescope (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f (n + 1) - f n) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm, ih]
    ring

lemma sum_Ico_telescope_rev (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm, ih]
    ring

lemma log_log_step (n : ℕ) (hn : 2 ≤ n) :
    1 / (((n : ℝ) + 1) * Real.log (n : ℝ)) ≤
      2 * (Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log (n : ℝ))) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogn1 : 0 < Real.log ((n : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))
  have hstep1 : 1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
    rw [← Real.log_div hn1_pos.ne' hn_pos.ne']
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hn1_pos hn_pos)
    have heq : 1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹ = 1 / ((n : ℝ) + 1) := by field_simp; ring
    linarith
  have hstep2 : (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) / Real.log ((n : ℝ) + 1) ≤
      Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log (n : ℝ)) := by
    rw [← Real.log_div hlogn1.ne' hlogn.ne']
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hlogn1 hlogn)
    have heq : 1 - (Real.log ((n : ℝ) + 1) / Real.log (n : ℝ))⁻¹ =
        (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) / Real.log ((n : ℝ) + 1) := by
      field_simp
    linarith
  have hlog_le : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
    have hsq : ((n : ℝ) + 1) ≤ (n : ℝ) ^ 2 := by
      have : n + 1 ≤ n * n := by nlinarith
      exact_mod_cast (by simpa [sq] using this)
    calc Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hn1_pos hsq
      _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
  have h1 : 1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) ≤
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) / Real.log ((n : ℝ) + 1) := by
    rw [← div_div, div_le_div_iff_of_pos_right hlogn1]
    exact hstep1
  have h2 : 1 / (((n : ℝ) + 1) * Real.log (n : ℝ)) ≤
      2 * (1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

lemma sum_inv_prime_Ioc_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, (1 / (p : ℝ)) ≤
      3 * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + 3 / Real.log (a : ℝ) := by
  have ha_pos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hb_pos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < a))
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  have hsum_eq : ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, (1 / (p : ℝ)) =
      ∑ n ∈ Finset.Ioc a b,
        (Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n - 1 : ℕ) : ℝ)) *
          (1 / ((n : ℝ) * Real.log (n : ℝ))) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
    have hlogn : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
    rw [theta_diff_nat n (by omega)]
    split_ifs with hp
    · field_simp
    · simp
  rw [hsum_eq, sum_by_parts_Ioc (fun n => Chebyshev.theta (n : ℝ))
    (fun n => 1 / ((n : ℝ) * Real.log (n : ℝ))) a b hab]
  have hlog4 : Real.log 4 < 3 / 2 := by
    have h2 : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hta_nonneg : 0 ≤ Chebyshev.theta (a : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    exact Finset.sum_nonneg fun p hp => Real.log_natCast_nonneg p
  have htb : Chebyshev.theta (b : ℝ) * (1 / ((b : ℝ) * Real.log (b : ℝ))) ≤
      Real.log 4 / Real.log (a : ℝ) := by
    have h1 := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ b by positivity)
    have h2 : Chebyshev.theta (b : ℝ) * (1 / ((b : ℝ) * Real.log (b : ℝ))) ≤
        (Real.log 4 * b) * (1 / ((b : ℝ) * Real.log (b : ℝ))) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (Real.log 4 * b) * (1 / ((b : ℝ) * Real.log (b : ℝ))) = Real.log 4 / Real.log (b : ℝ) := by
      field_simp
    have h4 : Real.log 4 / Real.log (b : ℝ) ≤ Real.log 4 / Real.log (a : ℝ) :=
      div_le_div_of_nonneg_left hlog4_pos.le hloga (Real.log_le_log ha_pos (by exact_mod_cast hab))
    linarith
  have hta : 0 ≤ Chebyshev.theta (a : ℝ) * (1 / ((a : ℝ) * Real.log (a : ℝ))) := by positivity
  have hmid : ∑ n ∈ Finset.Ico a b,
      Chebyshev.theta (n : ℝ) * (1 / ((n : ℝ) * Real.log (n : ℝ)) -
        1 / (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ))) ≤
      Real.log 4 * (2 * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + 1 / Real.log (a : ℝ)) := by
    have hterm : ∀ n ∈ Finset.Ico a b,
        Chebyshev.theta (n : ℝ) * (1 / ((n : ℝ) * Real.log (n : ℝ)) -
          1 / (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ))) ≤
        Real.log 4 * (2 * (Real.log (Real.log (((n + 1 : ℕ) : ℝ))) - Real.log (Real.log (n : ℝ))) +
          (1 / Real.log (n : ℝ) - 1 / Real.log (((n + 1 : ℕ) : ℝ)))) := by
      intro n hn
      have hn2 : 2 ≤ n := by have := (Finset.mem_Ico.mp hn).1; omega
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hlogn1 : 0 < Real.log ((n : ℝ) + 1) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))
      have hdiff_nonneg : 0 ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) -
          1 / (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
        push_cast
        have hle : (n : ℝ) * Real.log (n : ℝ) ≤ ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) :=
          mul_le_mul (by linarith) (Real.log_le_log hn_pos (by linarith)) hlogn.le (by positivity)
        exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) hle)
      have hth := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ n by positivity)
      have h1 := mul_le_mul_of_nonneg_right hth hdiff_nonneg
      have hsplit : (n : ℝ) * (1 / ((n : ℝ) * Real.log (n : ℝ)) -
          1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))) ≤
          1 / (((n : ℝ) + 1) * Real.log (n : ℝ)) +
            (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) := by
        have hid : (n : ℝ) * (1 / ((n : ℝ) * Real.log (n : ℝ)) -
            1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))) =
            1 / (((n : ℝ) + 1) * Real.log (n : ℝ)) +
              ((n : ℝ) / ((n : ℝ) + 1)) * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) := by
          field_simp; ring
        rw [hid]
        have hsub_nn : 0 ≤ 1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1) :=
          sub_nonneg.mpr (one_div_le_one_div_of_le hlogn (Real.log_le_log hn_pos (by linarith)))
        have hfrac : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
        nlinarith
      have hll := log_log_step n hn2
      push_cast at h1 ⊢
      nlinarith
    calc ∑ n ∈ Finset.Ico a b,
          Chebyshev.theta (n : ℝ) * (1 / ((n : ℝ) * Real.log (n : ℝ)) -
            1 / (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)))
        ≤ ∑ n ∈ Finset.Ico a b,
          Real.log 4 * (2 * (Real.log (Real.log (((n + 1 : ℕ) : ℝ))) - Real.log (Real.log (n : ℝ))) +
            (1 / Real.log (n : ℝ) - 1 / Real.log (((n + 1 : ℕ) : ℝ)))) :=
          Finset.sum_le_sum hterm
      _ = Real.log 4 * (2 * ∑ n ∈ Finset.Ico a b,
              (Real.log (Real.log (((n + 1 : ℕ) : ℝ))) - Real.log (Real.log (n : ℝ))) +
            ∑ n ∈ Finset.Ico a b, (1 / Real.log (n : ℝ) - 1 / Real.log (((n + 1 : ℕ) : ℝ)))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = Real.log 4 * (2 * (Real.log (Real.log (b : ℝ)) - Real.log (Real.log (a : ℝ))) +
            (1 / Real.log (a : ℝ) - 1 / Real.log (b : ℝ))) := by
          rw [sum_Ico_telescope (fun n => Real.log (Real.log (n : ℝ))) a b hab,
            sum_Ico_telescope_rev (fun n => 1 / Real.log (n : ℝ)) a b hab]
      _ ≤ Real.log 4 * (2 * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + 1 / Real.log (a : ℝ)) := by
          rw [Real.log_div hlogb.ne' hloga.ne']
          have hinvb : 0 ≤ 1 / Real.log (b : ℝ) := by positivity
          nlinarith
  have hratio_nn : 0 ≤ Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) :=
    Real.log_nonneg ((one_le_div hloga).mpr (Real.log_le_log ha_pos (by exact_mod_cast hab)))
  have hinva_nn : 0 ≤ 1 / Real.log (a : ℝ) := by positivity
  have htb' : Chebyshev.theta (b : ℝ) * (1 / ((b : ℝ) * Real.log (b : ℝ))) ≤
      (3 / 2 : ℝ) / Real.log (a : ℝ) :=
    htb.trans (div_le_div_of_nonneg_right hlog4.le hloga.le)
  have hmid' : ∑ n ∈ Finset.Ico a b,
      Chebyshev.theta (n : ℝ) * (1 / ((n : ℝ) * Real.log (n : ℝ)) -
        1 / (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ))) ≤
      (3 / 2 : ℝ) * (2 * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + 1 / Real.log (a : ℝ)) :=
    hmid.trans (mul_le_mul_of_nonneg_right hlog4.le (by positivity))
  have hdiv3 : (3 / 2 : ℝ) / Real.log (a : ℝ) + (3 / 2 : ℝ) * (1 / Real.log (a : ℝ)) =
      3 / Real.log (a : ℝ) := by ring
  linarith

lemma inv_one_sub_le_exp_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (1 - t)⁻¹ ≤ Real.exp (2 * t) := by
  have h1t : 0 < 1 - t := by linarith
  rw [inv_le_iff_one_le_mul₀' h1t]
  have hexp := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * t by linarith) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one] at hexp
  norm_num at hexp
  nlinarith

lemma prod_inv_one_sub_le (k a b : ℕ) (hk : 1 ≤ k) (ha : 2 * k < a) (hab : a ≤ b)
    (hlog : (1000 : ℝ) * k ≤ Real.log (a : ℝ))
    (S : Finset ℕ) (hS : S ⊆ (Finset.Ioc a b).filter Nat.Prime) :
    ∏ p ∈ S, (1 - (k : ℝ) / (p : ℝ))⁻¹ ≤
      (101 / 100 : ℝ) * (Real.log (b : ℝ) / Real.log (a : ℝ)) ^ (6 * k) := by
  have ha2 : 2 ≤ a := by omega
  have hloga : 0 < Real.log (a : ℝ) := by
    have : (0 : ℝ) < 1000 * k := by positivity
    linarith
  have hlogb : 0 < Real.log (b : ℝ) :=
    lt_of_lt_of_le hloga (Real.log_le_log (by exact_mod_cast (by omega : 0 < a)) (by exact_mod_cast hab))
  have hkp_le : ∀ p ∈ S, (k : ℝ) / (p : ℝ) ≤ 1 / 2 := by
    intro p hp
    have hpa : a < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hS hp)).1).1
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    rw [div_le_div_iff₀ hp_pos (by norm_num)]
    exact_mod_cast (show k * 2 ≤ 1 * p by omega)
  have h1 : ∏ p ∈ S, (1 - (k : ℝ) / (p : ℝ))⁻¹ ≤
      ∏ p ∈ S, Real.exp (2 * ((k : ℝ) / (p : ℝ))) := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have hkp := hkp_le p hp
      have hpos : 0 < 1 - (k : ℝ) / (p : ℝ) := by linarith
      exact inv_nonneg.mpr hpos.le
    · exact inv_one_sub_le_exp_two_mul (by positivity) (hkp_le p hp)
  have h2 : ∏ p ∈ S, Real.exp (2 * ((k : ℝ) / (p : ℝ))) =
      Real.exp (2 * (k : ℝ) * ∑ p ∈ S, (1 / (p : ℝ))) := by
    rw [← Real.exp_sum, Finset.mul_sum]
    exact congrArg Real.exp (Finset.sum_congr rfl fun p _ => by ring)
  have h3 : ∑ p ∈ S, (1 / (p : ℝ)) ≤
      ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, (1 / (p : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun p _ _ => by positivity)
  have h4 := sum_inv_prime_Ioc_le a b ha2 hab
  have h5 : 2 * (k : ℝ) * (3 * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + 3 / Real.log (a : ℝ)) ≤
      (6 * k : ℕ) * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + (6 / 1000 : ℝ) := by
    have hdiv : 6 * (k : ℝ) / Real.log (a : ℝ) ≤ 6 / 1000 := by
      rw [div_le_div_iff₀ hloga (by norm_num)]
      linarith
    have hmul : 2 * (k : ℝ) * (3 * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + 3 / Real.log (a : ℝ)) =
        (6 * k : ℕ) * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + 6 * (k : ℝ) / Real.log (a : ℝ) := by
      push_cast; ring
    linarith
  have hexp6 : Real.exp (6 / 1000 : ℝ) ≤ 101 / 100 := by
    have h := Real.exp_bound (show |(6 / 1000 : ℝ)| ≤ 1 by norm_num) (show 0 < 2 by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one] at h
    norm_num [abs_le] at h
    linarith
  calc ∏ p ∈ S, (1 - (k : ℝ) / (p : ℝ))⁻¹
      ≤ Real.exp (2 * (k : ℝ) * ∑ p ∈ S, (1 / (p : ℝ))) := h1.trans_eq h2
    _ ≤ Real.exp ((6 * k : ℕ) * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + (6 / 1000 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have : 2 * (k : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) ≤
            2 * (k : ℝ) * (3 * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + 3 / Real.log (a : ℝ)) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
        linarith
    _ = Real.exp (6 / 1000 : ℝ) * (Real.log (b : ℝ) / Real.log (a : ℝ)) ^ (6 * k) := by
        rw [Real.exp_add, mul_comm, Real.exp_nat_mul, Real.exp_log (div_pos hlogb hloga)]
    _ ≤ (101 / 100 : ℝ) * (Real.log (b : ℝ) / Real.log (a : ℝ)) ^ (6 * k) :=
        mul_le_mul_of_nonneg_right hexp6 (by positivity)

/- ### Section 2: Beta-Sieve Functional, Pointwise Inequality & Buchstab Identities -/

noncomputable def sieveSum (sign : Bool) (β : ℝ) (D : ℝ) : List ℕ → (ℕ → ℝ) → ℝ
  | [], f => f 1
  | p :: ps, f =>
    match sign with
    | false =>
      sieveSum false β D ps f - sieveSum true β (D / (p : ℝ)) ps (fun d => f (p * d))
    | true =>
      if (p : ℝ) ^ (β + 2) ≤ D then
        sieveSum true β D ps f - sieveSum false β (D / (p : ℝ)) ps (fun d => f (p * d))
      else
        sieveSum true β D ps f

noncomputable def sieveAbs (sign : Bool) (β : ℝ) (D : ℝ) : List ℕ → (ℕ → ℝ) → ℝ
  | [], f => f 1
  | p :: ps, f =>
    match sign with
    | false =>
      sieveAbs false β D ps f + sieveAbs true β (D / (p : ℝ)) ps (fun d => f (p * d))
    | true =>
      if (p : ℝ) ^ (β + 2) ≤ D then
        sieveAbs true β D ps f + sieveAbs false β (D / (p : ℝ)) ps (fun d => f (p * d))
      else
        sieveAbs true β D ps f

lemma sieveSum_add (sign : Bool) (β D : ℝ) (ps : List ℕ) (f g : ℕ → ℝ) :
    sieveSum sign β D ps (fun d => f d + g d) =
      sieveSum sign β D ps f + sieveSum sign β D ps g := by
  induction ps generalizing sign D f g with
  | nil => simp [sieveSum]
  | cons p ps ih =>
    cases sign <;> simp only [sieveSum]
    · rw [ih, ih]; ring
    · split_ifs
      · rw [ih, ih]; ring
      · exact ih true D f g

lemma sieveSum_smul (sign : Bool) (β D c : ℝ) (ps : List ℕ) (f : ℕ → ℝ) :
    sieveSum sign β D ps (fun d => c * f d) = c * sieveSum sign β D ps f := by
  induction ps generalizing sign D f with
  | nil => simp [sieveSum]
  | cons p ps ih =>
    cases sign <;> simp only [sieveSum]
    · rw [ih, ih]; ring
    · split_ifs
      · rw [ih, ih]; ring
      · exact ih true D f

lemma sieveSum_zero (sign : Bool) (β D : ℝ) (ps : List ℕ) :
    sieveSum sign β D ps (fun _ => 0) = 0 := by
  have := sieveSum_smul sign β D 0 ps (fun _ => 0)
  simpa using this

lemma abs_sieveSum_le (sign : Bool) (β D : ℝ) (ps : List ℕ) (f : ℕ → ℝ) :
    |sieveSum sign β D ps f| ≤ sieveAbs sign β D ps (fun d => |f d|) := by
  induction ps generalizing sign D f with
  | nil => simp [sieveSum, sieveAbs]
  | cons p ps ih =>
    cases sign <;> simp only [sieveSum, sieveAbs]
    · exact (abs_sub _ _).trans (add_le_add (ih false D f) (ih true (D / p) (fun d => f (p * d))))
    · split_ifs
      · exact (abs_sub _ _).trans (add_le_add (ih true D f) (ih false (D / p) (fun d => f (p * d))))
      · exact ih true D f

lemma sieveSum_indicator (β : ℝ) (ps : List ℕ) (bad : ℕ → Prop) :
    let ind : ℕ → ℝ := fun d => if ∀ q ∈ d.primeFactors, bad q then 1 else 0
    (∀ p ∈ ps, p.Prime) → ps.Nodup →
    (∀ D : ℝ, (if ∀ p ∈ ps, ¬ bad p then (1 : ℝ) else 0) ≤ sieveSum true β D ps ind) ∧
    (∀ D : ℝ, sieveSum false β D ps ind ≤ (if ∀ p ∈ ps, ¬ bad p then (1 : ℝ) else 0)) := by
  intro ind hprime hnodup
  induction ps with
  | nil =>
    constructor <;> intro D <;>
      simp only [sieveSum, ind, Nat.primeFactors_one, Finset.notMem_empty,
        List.not_mem_nil, IsEmpty.forall_iff, forall_const, ↓reduceIte, le_refl]
  | cons p ps ih =>
    have hp : p.Prime := hprime p (List.mem_cons_self ..)
    have hps_prime : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    have ⟨hp_not_mem, hps_nodup⟩ := List.nodup_cons.mp hnodup
    obtain ⟨ih_pos, ih_neg⟩ := ih hps_prime hps_nodup
    have hshift : ∀ (sign : Bool) (D : ℝ),
        sieveSum sign β D ps (fun d => ind (p * d)) =
          if bad p then sieveSum sign β D ps ind else 0 := by
      intro sign D
      have hcongr : ∀ (sign' : Bool) (D' : ℝ) (qs : List ℕ) (f₁ f₂ : ℕ → ℝ),
          (∀ d, (∀ q ∈ d.primeFactors, q ∈ qs) → d ≠ 0 → f₁ d = f₂ d) →
          (∀ q ∈ qs, q.Prime) →
          sieveSum sign' β D' qs f₁ = sieveSum sign' β D' qs f₂ := by
        intro sign' D' qs
        induction qs generalizing sign' D' with
        | nil =>
          intro f₁ f₂ h _
          simp only [sieveSum]
          exact h 1 (by simp) one_ne_zero
        | cons q qs ihq =>
          intro f₁ f₂ h hq
          have hq_prime : q.Prime := hq q (List.mem_cons_self ..)
          have hqs_prime : ∀ r ∈ qs, r.Prime := fun r hr => hq r (List.mem_cons_of_mem q hr)
          have h1 : ∀ d, (∀ r ∈ d.primeFactors, r ∈ qs) → d ≠ 0 → f₁ d = f₂ d :=
            fun d hd hd0 => h d (fun r hr => List.mem_cons_of_mem q (hd r hr)) hd0
          have h2 : ∀ d, (∀ r ∈ d.primeFactors, r ∈ qs) → d ≠ 0 → f₁ (q * d) = f₂ (q * d) := by
            intro d hd hd0
            apply h (q * d) _ (mul_ne_zero hq_prime.ne_zero hd0)
            intro r hr
            rw [Nat.primeFactors_mul hq_prime.ne_zero hd0, Finset.mem_union] at hr
            rcases hr with hr | hr
            · have : r = q := by
                have := Nat.mem_primeFactors.mp hr
                exact (Nat.prime_dvd_prime_iff_eq this.1 hq_prime).mp this.2.1
              subst this; exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem q (hd r hr)
          cases sign' <;> simp only [sieveSum]
          · rw [ihq false D' f₁ f₂ h1 hqs_prime, ihq true (D' / q) _ _ h2 hqs_prime]
          · split_ifs
            · rw [ihq true D' f₁ f₂ h1 hqs_prime, ihq false (D' / q) _ _ h2 hqs_prime]
            · exact ihq true D' f₁ f₂ h1 hqs_prime
      split_ifs with hbp
      · apply hcongr sign D ps _ _ _ hps_prime
        intro d _ hd0
        simp only [ind, Nat.primeFactors_mul hp.ne_zero hd0, Finset.mem_union]
        have hiff : (∀ q, q ∈ p.primeFactors ∨ q ∈ d.primeFactors → bad q) ↔
            (∀ q ∈ d.primeFactors, bad q) := by
          constructor
          · intro h q hq; exact h q (Or.inr hq)
          · rintro h q (hq | hq)
            · have : q = p := by
                have := Nat.mem_primeFactors.mp hq
                exact (Nat.prime_dvd_prime_iff_eq this.1 hp).mp this.2.1
              subst this; exact hbp
            · exact h q hq
        rw [if_congr hiff rfl rfl]
      · rw [← sieveSum_zero sign β D ps]
        apply hcongr sign D ps _ _ _ hps_prime
        intro d _ hd0
        simp only [ind]
        rw [if_neg]
        intro h
        exact hbp (h p (Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_right p d, mul_ne_zero hp.ne_zero hd0⟩))
    constructor
    · intro D
      simp only [sieveSum, hshift]
      by_cases hbp : bad p
      · have hlhs : (if ∀ q ∈ p :: ps, ¬ bad q then (1 : ℝ) else 0) = 0 := by
          rw [if_neg]; intro h; exact h p (List.mem_cons_self ..) hbp
        rw [hlhs, if_pos hbp]
        split_ifs
        · linarith [ih_pos D, ih_neg (D / p)]
        · have hnn : (0 : ℝ) ≤ if ∀ q ∈ ps, ¬ bad q then 1 else 0 := by split_ifs <;> norm_num
          linarith [ih_pos D]
      · have heq : (∀ q ∈ p :: ps, ¬ bad q) ↔ (∀ q ∈ ps, ¬ bad q) := by
          simp [hbp]
        rw [if_neg hbp, if_congr heq rfl rfl]
        by_cases hc : (p : ℝ) ^ (β + 2) ≤ D
        · rw [if_pos hc, sub_zero]; exact ih_pos D
        · rw [if_neg hc]; exact ih_pos D
    · intro D
      simp only [sieveSum, hshift]
      by_cases hbp : bad p
      · have hrhs : (if ∀ q ∈ p :: ps, ¬ bad q then (1 : ℝ) else 0) = 0 := by
          rw [if_neg]; intro h; exact h p (List.mem_cons_self ..) hbp
        rw [hrhs, if_pos hbp]
        linarith [ih_neg D, ih_pos (D / p)]
      · have heq : (∀ q ∈ p :: ps, ¬ bad q) ↔ (∀ q ∈ ps, ¬ bad q) := by
          simp [hbp]
        rw [if_neg hbp, sub_zero, if_congr heq rfl rfl]
        exact ih_neg D

/- ### Section 3: Beta-Sieve Main Term Exponential Error Bound -/

noncomputable def prodV (k : ℕ) (ps : List ℕ) : ℝ :=
  (ps.map (fun p => 1 - (k : ℝ) / (p : ℝ))).prod

noncomputable def multG (k : ℕ) (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, (k : ℝ) / (p : ℝ)

lemma prodV_nil (k : ℕ) : prodV k [] = 1 := rfl

lemma prodV_cons (k p : ℕ) (ps : List ℕ) :
    prodV k (p :: ps) = (1 - (k : ℝ) / (p : ℝ)) * prodV k ps := rfl

lemma prodV_append (k : ℕ) (l₁ l₂ : List ℕ) :
    prodV k (l₁ ++ l₂) = prodV k l₁ * prodV k l₂ := by
  simp [prodV]

lemma prodV_pos (k : ℕ) (ps : List ℕ) (h : ∀ p ∈ ps, 2 * k < p) : 0 < prodV k ps := by
  induction ps with
  | nil => simp [prodV]
  | cons p ps ih =>
    rw [prodV_cons]
    have hp : 2 * k < p := h p (List.mem_cons_self ..)
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have h1 : 0 < 1 - (k : ℝ) / (p : ℝ) := by
      rw [sub_pos, div_lt_one hp_pos]
      exact_mod_cast (by omega : k < p)
    exact mul_pos h1 (ih fun q hq => h q (List.mem_cons_of_mem p hq))

lemma prodV_eq_finset_prod (k : ℕ) (ps : List ℕ) (hnd : ps.Nodup) :
    prodV k ps = ∏ p ∈ ps.toFinset, (1 - (k : ℝ) / (p : ℝ)) := by
  induction ps with
  | nil => simp [prodV]
  | cons p ps ih =>
    obtain ⟨hp, hps⟩ := List.nodup_cons.mp hnd
    rw [prodV_cons, List.toFinset_cons, Finset.prod_insert (by simpa using hp), ih hps]

lemma sieveSum_congr_primes (sign : Bool) (β D : ℝ) (qs : List ℕ) (f₁ f₂ : ℕ → ℝ)
    (h : ∀ d, (∀ q ∈ d.primeFactors, q ∈ qs) → d ≠ 0 → f₁ d = f₂ d)
    (hq : ∀ q ∈ qs, q.Prime) :
    sieveSum sign β D qs f₁ = sieveSum sign β D qs f₂ := by
  induction qs generalizing sign D f₁ f₂ with
  | nil =>
    simp only [sieveSum]
    exact h 1 (by simp) one_ne_zero
  | cons q qs ih =>
    have hq_prime : q.Prime := hq q (List.mem_cons_self ..)
    have hqs_prime : ∀ r ∈ qs, r.Prime := fun r hr => hq r (List.mem_cons_of_mem q hr)
    have h1 : ∀ d, (∀ r ∈ d.primeFactors, r ∈ qs) → d ≠ 0 → f₁ d = f₂ d :=
      fun d hd hd0 => h d (fun r hr => List.mem_cons_of_mem q (hd r hr)) hd0
    have h2 : ∀ d, (∀ r ∈ d.primeFactors, r ∈ qs) → d ≠ 0 → f₁ (q * d) = f₂ (q * d) := by
      intro d hd hd0
      apply h (q * d) _ (mul_ne_zero hq_prime.ne_zero hd0)
      intro r hr
      rw [Nat.primeFactors_mul hq_prime.ne_zero hd0, Finset.mem_union] at hr
      rcases hr with hr | hr
      · have : r = q := by
          have := Nat.mem_primeFactors.mp hr
          exact (Nat.prime_dvd_prime_iff_eq this.1 hq_prime).mp this.2.1
        subst this; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem q (hd r hr)
    cases sign <;> simp only [sieveSum]
    · rw [ih false D f₁ f₂ h1 hqs_prime, ih true (D / q) _ _ h2 hqs_prime]
    · split_ifs
      · rw [ih true D f₁ f₂ h1 hqs_prime, ih false (D / q) _ _ h2 hqs_prime]
      · exact ih true D f₁ f₂ h1 hqs_prime

lemma sieveSum_multG_shift (k : ℕ) (sign : Bool) (β D : ℝ) (p : ℕ) (ps : List ℕ)
    (hp : p.Prime) (hps : ∀ q ∈ ps, q.Prime) (hnot : p ∉ ps) :
    sieveSum sign β D ps (fun d => multG k (p * d)) =
      ((k : ℝ) / (p : ℝ)) * sieveSum sign β D ps (multG k) := by
  rw [← sieveSum_smul]
  apply sieveSum_congr_primes sign β D ps _ _ _ hps
  intro d hd hd0
  simp only [multG]
  rw [Nat.primeFactors_mul hp.ne_zero hd0, hp.primeFactors]
  have hp_not_d : p ∉ d.primeFactors := fun h => hnot (hd p h)
  rw [Finset.singleton_union, Finset.prod_insert hp_not_d]

lemma sieveSum_multG_sign_bound (k : ℕ) (β : ℝ) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hnd : ps.Nodup) (hgt : ∀ p ∈ ps, 2 * k < p) :
    (∀ D : ℝ, prodV k ps ≤ sieveSum true β D ps (multG k)) ∧
    (∀ D : ℝ, sieveSum false β D ps (multG k) ≤ prodV k ps) := by
  induction ps with
  | nil =>
    constructor <;> intro D <;> simp [sieveSum, prodV, multG]
  | cons p ps ih =>
    have hp : p.Prime := hprime p (List.mem_cons_self ..)
    have hps_prime : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    obtain ⟨hp_not, hps_nd⟩ := List.nodup_cons.mp hnd
    have hps_gt : ∀ q ∈ ps, 2 * k < q := fun q hq => hgt q (List.mem_cons_of_mem p hq)
    obtain ⟨ih_pos, ih_neg⟩ := ih hps_prime hps_nd hps_gt
    have hkp_nn : 0 ≤ (k : ℝ) / (p : ℝ) := by positivity
    have hV_pos : 0 < prodV k ps := prodV_pos k ps hps_gt
    constructor
    · intro D
      simp only [sieveSum, prodV_cons]
      rw [sieveSum_multG_shift k false β (D / p) p ps hp hps_prime hp_not]
      split_ifs
      · nlinarith [ih_pos D, ih_neg (D / p)]
      · nlinarith [ih_pos D]
    · intro D
      simp only [sieveSum, prodV_cons]
      rw [sieveSum_multG_shift k true β (D / p) p ps hp hps_prime hp_not]
      nlinarith [ih_neg D, ih_pos (D / p)]

noncomputable def sumTail (k : ℕ) : List ℕ → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | p :: qs, F => sumTail k qs F + ((k : ℝ) / (p : ℝ)) * prodV k qs * F p

lemma sumTail_append_le (k : ℕ) (hi lo : List ℕ) (F : ℕ → ℝ) (M : ℝ)
    (hgt : ∀ p ∈ hi ++ lo, 2 * k < p) (hF : ∀ p ∈ hi, F p ≤ M) :
    sumTail k (hi ++ lo) F ≤ sumTail k lo F + (prodV k lo - prodV k (hi ++ lo)) * M := by
  induction hi with
  | nil => simp
  | cons p qs ih =>
    have hqs : ∀ q ∈ qs ++ lo, 2 * k < q := fun q hq => hgt q (List.mem_cons_of_mem p hq)
    have hF' : ∀ q ∈ qs, F q ≤ M := fun q hq => hF q (List.mem_cons_of_mem p hq)
    have hih := ih hqs hF'
    have hFp : F p ≤ M := hF p (List.mem_cons_self ..)
    have hV_pos : 0 < prodV k (qs ++ lo) := prodV_pos k (qs ++ lo) hqs
    have hkp_nn : 0 ≤ (k : ℝ) / (p : ℝ) := by positivity
    have hstep : prodV k (qs ++ lo) - prodV k (p :: (qs ++ lo)) =
        ((k : ℝ) / (p : ℝ)) * prodV k (qs ++ lo) := by
      rw [prodV_cons]; ring
    have hmul : ((k : ℝ) / (p : ℝ)) * prodV k (qs ++ lo) * F p ≤
        (prodV k (qs ++ lo) - prodV k (p :: (qs ++ lo))) * M := by
      rw [hstep]
      exact mul_le_mul_of_nonneg_left hFp (mul_nonneg hkp_nn hV_pos.le)
    simp only [List.cons_append, sumTail]
    linarith

lemma buchstab_pos_le (k : ℕ) (β D : ℝ) (ps : List ℕ) (F : ℕ → ℝ)
    (hprime : ∀ p ∈ ps, p.Prime) (hnd : ps.Nodup)
    (hstep : ∀ (hi : List ℕ) (p : ℕ) (qs : List ℕ), ps = hi ++ p :: qs →
      (if (p : ℝ) ^ (β + 2) ≤ D then prodV k qs - sieveSum false β (D / (p : ℝ)) qs (multG k)
        else prodV k qs) ≤ prodV k qs * F p) :
    sieveSum true β D ps (multG k) - prodV k ps ≤ sumTail k ps F := by
  induction ps with
  | nil => simp [sieveSum, prodV, multG, sumTail]
  | cons p qs ih =>
    have hp : p.Prime := hprime p (List.mem_cons_self ..)
    have hqs_prime : ∀ q ∈ qs, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    obtain ⟨hp_not, hqs_nd⟩ := List.nodup_cons.mp hnd
    have hih := ih hqs_prime hqs_nd (fun hi r rs heq => hstep (p :: hi) r rs (by simp [heq]))
    have hp_step := hstep [] p qs rfl
    simp only [sieveSum, prodV_cons, sumTail]
    rw [sieveSum_multG_shift k false β (D / (p : ℝ)) p qs hp hqs_prime hp_not]
    have hkp_nn : 0 ≤ (k : ℝ) / (p : ℝ) := by positivity
    split_ifs at hp_step ⊢
    · nlinarith
    · nlinarith

lemma buchstab_neg_le (k : ℕ) (β D : ℝ) (ps : List ℕ) (F : ℕ → ℝ)
    (hprime : ∀ p ∈ ps, p.Prime) (hnd : ps.Nodup)
    (hstep : ∀ (hi : List ℕ) (p : ℕ) (qs : List ℕ), ps = hi ++ p :: qs →
      sieveSum true β (D / (p : ℝ)) qs (multG k) - prodV k qs ≤ prodV k qs * F p) :
    prodV k ps - sieveSum false β D ps (multG k) ≤ sumTail k ps F := by
  induction ps with
  | nil => simp [sieveSum, prodV, multG, sumTail]
  | cons p qs ih =>
    have hp : p.Prime := hprime p (List.mem_cons_self ..)
    have hqs_prime : ∀ q ∈ qs, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    obtain ⟨hp_not, hqs_nd⟩ := List.nodup_cons.mp hnd
    have hih := ih hqs_prime hqs_nd (fun hi r rs heq => hstep (p :: hi) r rs (by simp [heq]))
    have hp_step := hstep [] p qs rfl
    simp only [sieveSum, prodV_cons, sumTail]
    rw [sieveSum_multG_shift k true β (D / (p : ℝ)) p qs hp hqs_prime hp_not]
    have hkp_nn : 0 ≤ (k : ℝ) / (p : ℝ) := by positivity
    nlinarith

lemma list_split_desc (ps : List ℕ) (hdesc : ps.Pairwise (· > ·)) (y : ℝ) :
    ps = ps.filter (fun p : ℕ => decide (y < (p : ℝ))) ++
      ps.filter (fun p : ℕ => decide (¬ (y < (p : ℝ)))) := by
  induction ps with
  | nil => simp
  | cons p qs ih =>
    obtain ⟨hp_gt, hqs_desc⟩ := List.pairwise_cons.mp hdesc
    by_cases hy : y < (p : ℝ)
    · simp only [List.filter_cons, decide_eq_true hy, ↓reduceIte, decide_eq_false (not_not.mpr hy),
        List.cons_append]
      exact congrArg (List.cons p) (ih hqs_desc)
    · have hhi : qs.filter (fun q : ℕ => decide (y < (q : ℝ))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro q hq
        have hqp : (q : ℝ) < (p : ℝ) := by exact_mod_cast hp_gt q hq
        simp only [decide_eq_true_eq, not_lt]
        linarith
      have hlo : qs.filter (fun q : ℕ => decide (¬ (y < (q : ℝ)))) = qs := by
        rw [List.filter_eq_self]
        intro q hq
        have hqp : (q : ℝ) < (p : ℝ) := by exact_mod_cast hp_gt q hq
        simp only [decide_eq_true_eq, not_lt]
        linarith
      simp only [List.filter_cons, decide_eq_false hy, decide_eq_true hy, Bool.false_eq_true,
        ↓reduceIte, hhi, hlo, List.nil_append]

lemma pairwise_gt_nodup {ps : List ℕ} (h : ps.Pairwise (· > ·)) : ps.Nodup :=
  h.imp fun hab => ne_of_gt hab

lemma prodV_ratio_le_real (k w : ℕ) (hk : 1 ≤ k) (hw : 2 * k < w)
    (hlogw : (1000 : ℝ) * k ≤ Real.log (w : ℝ))
    (hi lo : List ℕ) (hnd : hi.Nodup)
    (a b : ℝ) (hwa : (w : ℝ) ≤ a) (hab : a ≤ b)
    (hhi : ∀ p ∈ hi, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b)
    (hlo : ∀ p ∈ lo, 2 * k < p) :
    prodV k lo ≤ (102 / 100 : ℝ) * (Real.log b / Real.log a) ^ (6 * k) * prodV k (hi ++ lo) := by
  have hwa_nat : w ≤ ⌊a⌋₊ := Nat.le_floor hwa
  have ha_nat : 2 * k < ⌊a⌋₊ := by omega
  have hb_nat : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hlog_fa : (1000 : ℝ) * k ≤ Real.log (⌊a⌋₊ : ℝ) :=
    hlogw.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < w)) (by exact_mod_cast hwa_nat))
  have hsub : hi.toFinset ⊆ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    intro p hp
    have hp' := List.mem_toFinset.mp hp
    obtain ⟨hpr, hpa, hpb⟩ := hhi p hp'
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hpr⟩
    · exact (Nat.floor_lt' hpr.ne_zero).mpr hpa
    · exact Nat.le_floor hpb
  have hprod := prod_inv_one_sub_le k ⌊a⌋₊ ⌊b⌋₊ hk ha_nat hb_nat hlog_fa hi.toFinset hsub
  have hfa_pos : (0 : ℝ) < ⌊a⌋₊ := by exact_mod_cast (by omega : 0 < ⌊a⌋₊)
  have ha_pos : (0 : ℝ) < a := lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < w)) hwa
  have hb_pos : (0 : ℝ) < b := lt_of_lt_of_le ha_pos hab
  have hlog_fa_pos : 0 < Real.log (⌊a⌋₊ : ℝ) := by
    have : (0 : ℝ) < 1000 * k := by positivity
    linarith
  have hlog_a_pos : 0 < Real.log a :=
    lt_of_lt_of_le hlog_fa_pos (Real.log_le_log hfa_pos (Nat.floor_le ha_pos.le))
  have hlog_fb_le : Real.log (⌊b⌋₊ : ℝ) ≤ Real.log b :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊b⌋₊)) (Nat.floor_le hb_pos.le)
  -- Bound log a / log ⌊a⌋₊ ≤ 1 + 1 / (1000 * k)
  have hratio_floor : Real.log a / Real.log (⌊a⌋₊ : ℝ) ≤ 1 + 1 / ((1000 : ℝ) * k) := by
    have hdiff : Real.log a - Real.log (⌊a⌋₊ : ℝ) ≤ 1 := by
      rw [← Real.log_div ha_pos.ne' hfa_pos.ne']
      have hlt : a / (⌊a⌋₊ : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hfa_pos]
        have hfl : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
        have h1 : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 ≤ ⌊a⌋₊)
        linarith
      have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      exact (Real.log_le_log (div_pos ha_pos hfa_pos) hlt).trans hlog2
    rw [div_le_iff₀ hlog_fa_pos]
    have h1 : (1 : ℝ) ≤ Real.log (⌊a⌋₊ : ℝ) / ((1000 : ℝ) * k) :=
      (one_le_div (by positivity)).mpr hlog_fa
    have h2 : Real.log (⌊a⌋₊ : ℝ) * (1 + 1 / ((1000 : ℝ) * k)) =
        Real.log (⌊a⌋₊ : ℝ) + Real.log (⌊a⌋₊ : ℝ) / ((1000 : ℝ) * k) := by ring
    linarith
  have hpow_floor : (Real.log a / Real.log (⌊a⌋₊ : ℝ)) ^ (6 * k) ≤ 102 / 101 := by
    have h1 : Real.log a / Real.log (⌊a⌋₊ : ℝ) ≤ Real.exp (1 / ((1000 : ℝ) * k)) :=
      hratio_floor.trans (by linarith [Real.add_one_le_exp (1 / ((1000 : ℝ) * k))])
    have h2 : (Real.log a / Real.log (⌊a⌋₊ : ℝ)) ^ (6 * k) ≤
        (Real.exp (1 / ((1000 : ℝ) * k))) ^ (6 * k) :=
      pow_le_pow_left₀ (by positivity) h1 (6 * k)
    have h3 : (Real.exp (1 / ((1000 : ℝ) * k))) ^ (6 * k) = Real.exp (6 / 1000 : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      push_cast; field_simp
    have h4 : Real.exp (6 / 1000 : ℝ) ≤ 102 / 101 := by
      have h := Real.exp_bound (show |(6 / 1000 : ℝ)| ≤ 1 by norm_num) (show 0 < 2 by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one] at h
      norm_num [abs_le] at h
      linarith
    linarith
  have hlog_ratio : (Real.log (⌊b⌋₊ : ℝ) / Real.log (⌊a⌋₊ : ℝ)) ^ (6 * k) ≤
      (102 / 101 : ℝ) * (Real.log b / Real.log a) ^ (6 * k) := by
    have hsplit : Real.log (⌊b⌋₊ : ℝ) / Real.log (⌊a⌋₊ : ℝ) ≤
        (Real.log a / Real.log (⌊a⌋₊ : ℝ)) * (Real.log b / Real.log a) := by
      have heq : (Real.log a / Real.log (⌊a⌋₊ : ℝ)) * (Real.log b / Real.log a) =
          Real.log b / Real.log (⌊a⌋₊ : ℝ) := by field_simp
      rw [heq]
      exact div_le_div_of_nonneg_right hlog_fb_le hlog_fa_pos.le
    calc (Real.log (⌊b⌋₊ : ℝ) / Real.log (⌊a⌋₊ : ℝ)) ^ (6 * k)
        ≤ ((Real.log a / Real.log (⌊a⌋₊ : ℝ)) * (Real.log b / Real.log a)) ^ (6 * k) :=
          pow_le_pow_left₀ (div_nonneg (Real.log_natCast_nonneg _) hlog_fa_pos.le) hsplit (6 * k)
      _ = (Real.log a / Real.log (⌊a⌋₊ : ℝ)) ^ (6 * k) * (Real.log b / Real.log a) ^ (6 * k) :=
          mul_pow _ _ _
      _ ≤ (102 / 101 : ℝ) * (Real.log b / Real.log a) ^ (6 * k) := by
          have hlog_b_pos : 0 < Real.log b := lt_of_lt_of_le hlog_a_pos (Real.log_le_log ha_pos hab)
          exact mul_le_mul_of_nonneg_right hpow_floor (by positivity)
  have hhi_gt : ∀ p ∈ hi, 2 * k < p := by
    intro p hp
    have hlt : (w : ℝ) < p := lt_of_le_of_lt hwa (hhi p hp).2.1
    have hlt' : w < p := by exact_mod_cast hlt
    omega
  have hVhi_pos : 0 < prodV k hi := prodV_pos k hi hhi_gt
  have hVlo_pos : 0 < prodV k lo := prodV_pos k lo hlo
  have hinv : (prodV k hi)⁻¹ = ∏ p ∈ hi.toFinset, (1 - (k : ℝ) / (p : ℝ))⁻¹ := by
    rw [prodV_eq_finset_prod k hi hnd, Finset.prod_inv_distrib]
  have hinv_le : (prodV k hi)⁻¹ ≤ (102 / 100 : ℝ) * (Real.log b / Real.log a) ^ (6 * k) := by
    rw [hinv]
    calc ∏ p ∈ hi.toFinset, (1 - (k : ℝ) / (p : ℝ))⁻¹
        ≤ (101 / 100 : ℝ) * (Real.log (⌊b⌋₊ : ℝ) / Real.log (⌊a⌋₊ : ℝ)) ^ (6 * k) := hprod
      _ ≤ (101 / 100 : ℝ) * ((102 / 101 : ℝ) * (Real.log b / Real.log a) ^ (6 * k)) :=
          mul_le_mul_of_nonneg_left hlog_ratio (by norm_num)
      _ = (102 / 100 : ℝ) * (Real.log b / Real.log a) ^ (6 * k) := by ring
  rw [prodV_append]
  have hmul := mul_le_mul_of_nonneg_right hinv_le (mul_pos hVhi_pos hVlo_pos).le
  have hlhs : (prodV k hi)⁻¹ * (prodV k hi * prodV k lo) = prodV k lo := by
    rw [← mul_assoc, inv_mul_cancel₀ hVhi_pos.ne', one_mul]
  linarith

noncomputable def phiSieve (β s : ℝ) : ℝ :=
  Real.exp ((β + 2 - s) / 2)

lemma phiSieve_anti (β : ℝ) {s₁ s₂ : ℝ} (h : s₁ ≤ s₂) :
    phiSieve β s₂ ≤ phiSieve β s₁ :=
  Real.exp_le_exp.mpr (by linarith)

lemma sumTail_dyadic_le (k w : ℕ) (hk : 12 ≤ k) (hw : 2 * k < w)
    (hlogw : (1000 : ℝ) * k ≤ Real.log (w : ℝ))
    (z D : ℝ) (hz : (w : ℝ) < z)
    (hs : (400 : ℝ) * (k : ℝ) ^ 2 ≤ Real.log D / Real.log z)
    (fuel j : ℕ) (hj : 1 ≤ j)
    (hfuel : Real.log z * (1 / 2 : ℝ) ^ (j + fuel) ≤ Real.log (w : ℝ))
    (qs : List ℕ) (hdesc : qs.Pairwise (· > ·))
    (hqs : ∀ q ∈ qs, q.Prime ∧ w < q ∧ (q : ℝ) ≤ z ^ ((1 / 2 : ℝ) ^ j)) :
    let β : ℝ := (400 : ℝ) * (k : ℝ) ^ 2
    let s : ℝ := Real.log D / Real.log z
    sumTail k qs (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) ≤
      prodV k qs * (1 / 10 : ℝ) * phiSieve β s * Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4))) := by
  intro β s
  have hlogw_pos : 0 < Real.log (w : ℝ) := by
    have : (0 : ℝ) < 1000 * k := by positivity
    linarith
  have hw_pos : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hz_pos : (0 : ℝ) < z := lt_trans hw_pos hz
  have hlogz_pos : 0 < Real.log z := lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hz.le)
  have hD_pos : 0 < Real.log D := by
    have hs_pos : 0 < s := lt_of_lt_of_le (by positivity) hs
    exact (div_pos_iff_of_pos_right hlogz_pos).mp hs_pos
  induction fuel generalizing j qs with
  | zero =>
    have hnil : qs = [] := by
      cases qs with
      | nil => rfl
      | cons q rs =>
        exfalso
        obtain ⟨_, hqw, hqz⟩ := hqs q (List.mem_cons_self ..)
        have h1 : Real.log (w : ℝ) < Real.log (q : ℝ) :=
          Real.log_lt_log hw_pos (by exact_mod_cast hqw)
        have h2 : Real.log (q : ℝ) ≤ Real.log (z ^ ((1 / 2 : ℝ) ^ j)) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < q)) hqz
        rw [Real.log_rpow hz_pos] at h2
        simp only [Nat.add_zero] at hfuel
        linarith
    subst hnil
    simp only [sumTail, prodV_nil, one_mul]
    dsimp only [phiSieve]; positivity
  | succ f ih =>
    let y : ℝ := z ^ ((1 / 2 : ℝ) ^ (j + 1))
    let hi : List ℕ := qs.filter (fun p : ℕ => decide (y < (p : ℝ)))
    let lo : List ℕ := qs.filter (fun p : ℕ => decide (¬ (y < (p : ℝ))))
    have hsplit : qs = hi ++ lo := list_split_desc qs hdesc y
    have hhi_nd : hi.Nodup := (pairwise_gt_nodup hdesc).filter _
    have hlo_desc : lo.Pairwise (· > ·) := hdesc.filter _
    have hlo_props : ∀ q ∈ lo, q.Prime ∧ w < q ∧ (q : ℝ) ≤ z ^ ((1 / 2 : ℝ) ^ (j + 1)) := by
      intro q hq
      obtain ⟨hqm, hqf⟩ := List.mem_filter.mp hq
      obtain ⟨hpr, hqw, _⟩ := hqs q hqm
      simp only [decide_eq_true_eq, not_lt] at hqf
      exact ⟨hpr, hqw, hqf⟩
    have hih := ih (j + 1) (by omega) (by simpa [Nat.add_assoc, Nat.add_comm 1 f] using hfuel)
      lo hlo_desc hlo_props
    have hqs_gt : ∀ q ∈ qs, 2 * k < q := fun q hq => by have := (hqs q hq).2.1; omega
    have hlo_gt : ∀ q ∈ lo, 2 * k < q := fun q hq => by have := (hlo_props q hq).2.1; omega
    have hF_hi : ∀ p ∈ hi,
        phiSieve β (Real.log D / Real.log (p : ℝ) - 1) ≤ phiSieve β ((2 : ℝ) ^ j * s - 1) := by
      intro p hp
      obtain ⟨hpm, _⟩ := List.mem_filter.mp hp
      obtain ⟨_, hpw, hpz⟩ := hqs p hpm
      have hlogp_pos : 0 < Real.log (p : ℝ) :=
        lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos (by exact_mod_cast hpw.le))
      have hlogp_le : Real.log (p : ℝ) ≤ (1 / 2 : ℝ) ^ j * Real.log z := by
        calc Real.log (p : ℝ) ≤ Real.log (z ^ ((1 / 2 : ℝ) ^ j)) :=
              Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) hpz
          _ = (1 / 2 : ℝ) ^ j * Real.log z := Real.log_rpow hz_pos _
      apply phiSieve_anti
      have hdiv : (2 : ℝ) ^ j * s ≤ Real.log D / Real.log (p : ℝ) := by
        dsimp only [s]
        rw [le_div_iff₀ hlogp_pos]
        have hmul : (2 : ℝ) ^ j * (Real.log D / Real.log z) * ((1 / 2 : ℝ) ^ j * Real.log z) =
            Real.log D := by
          have h2 : (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
          calc (2 : ℝ) ^ j * (Real.log D / Real.log z) * ((1 / 2 : ℝ) ^ j * Real.log z)
              = ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j) * ((Real.log D / Real.log z) * Real.log z) := by ring
            _ = 1 * Real.log D := by rw [h2, div_mul_cancel₀ _ hlogz_pos.ne']
            _ = Real.log D := one_mul _
        calc (2 : ℝ) ^ j * (Real.log D / Real.log z) * Real.log (p : ℝ)
            ≤ (2 : ℝ) ^ j * (Real.log D / Real.log z) * ((1 / 2 : ℝ) ^ j * Real.log z) :=
              mul_le_mul_of_nonneg_left hlogp_le (by positivity)
          _ = Real.log D := hmul
      linarith
    have htail : sumTail k qs (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) ≤
        sumTail k lo (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) +
          (prodV k lo - prodV k qs) * phiSieve β ((2 : ℝ) ^ j * s - 1) := by
      conv_lhs => rw [hsplit]
      conv_rhs => rw [hsplit]
      exact sumTail_append_le k hi lo _ _ (hsplit ▸ hqs_gt) hF_hi
    have hratio_lo : prodV k lo ≤ (2 : ℝ) * (2 : ℝ) ^ (6 * k) * prodV k qs := by
      by_cases hhi_nil : hi = []
      · have hqlo : qs = lo := by rw [hsplit, hhi_nil, List.nil_append]
        rw [hqlo]
        have hVpos : 0 < prodV k lo := prodV_pos k lo hlo_gt
        have h1 : (1 : ℝ) ≤ (2 : ℝ) * (2 : ℝ) ^ (6 * k) := by
          have : (1 : ℝ) ≤ (2 : ℝ) ^ (6 * k) := one_le_pow₀ (by norm_num)
          linarith
        nlinarith
      · have htop_gt_w : (w : ℝ) < z ^ ((1 / 2 : ℝ) ^ j) := by
          obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil hi hhi_nil
          obtain ⟨hpm, _⟩ := List.mem_filter.mp hp
          obtain ⟨_, hpw, hpz⟩ := hqs p hpm
          exact lt_of_lt_of_le (by exact_mod_cast hpw) hpz
        let a : ℝ := max (w : ℝ) y
        let b : ℝ := z ^ ((1 / 2 : ℝ) ^ j)
        have hwa : (w : ℝ) ≤ a := le_max_left _ _
        have hab : a ≤ b := by
          apply max_le htop_gt_w.le
          apply Real.rpow_le_rpow_of_exponent_le (le_trans (by exact_mod_cast (by omega : 1 ≤ w)) hz.le)
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ j)
        have hhi_in : ∀ p ∈ hi, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
          intro p hp
          obtain ⟨hpm, hpf⟩ := List.mem_filter.mp hp
          obtain ⟨hpr, hpw, hpz⟩ := hqs p hpm
          simp only [decide_eq_true_eq] at hpf
          exact ⟨hpr, max_lt (by exact_mod_cast hpw) hpf, hpz⟩
        have hrat := prodV_ratio_le_real k w (by omega) hw hlogw hi lo hhi_nd a b hwa hab hhi_in hlo_gt
        rw [← hsplit] at hrat
        have hlog_rat : Real.log b / Real.log a ≤ 2 := by
          have hloga_pos : 0 < Real.log a :=
            lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hwa)
          rw [div_le_iff₀ hloga_pos]
          have hlog_y_le : Real.log y ≤ Real.log a :=
            Real.log_le_log (Real.rpow_pos_of_pos hz_pos _) (le_max_right _ _)
          have hlog_b : Real.log b = (1 / 2 : ℝ) ^ j * Real.log z := Real.log_rpow hz_pos _
          have hlog_y : Real.log y = (1 / 2 : ℝ) ^ (j + 1) * Real.log z := Real.log_rpow hz_pos _
          rw [hlog_b]
          have h2y : (1 / 2 : ℝ) ^ j * Real.log z = 2 * ((1 / 2 : ℝ) ^ (j + 1) * Real.log z) := by
            rw [pow_succ]; ring
          linarith
        have hpow_le : (Real.log b / Real.log a) ^ (6 * k) ≤ (2 : ℝ) ^ (6 * k) :=
          pow_le_pow_left₀ (div_nonneg (Real.log_nonneg (le_trans (by exact_mod_cast (by omega : 1 ≤ w)) htop_gt_w.le))
            (lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hwa)).le) hlog_rat (6 * k)
        have hVqs_pos : 0 < prodV k qs := prodV_pos k qs hqs_gt
        have h102 : (102 / 100 : ℝ) * (Real.log b / Real.log a) ^ (6 * k) ≤
            (2 : ℝ) * (2 : ℝ) ^ (6 * k) := by
          have : (0 : ℝ) ≤ (2 : ℝ) ^ (6 * k) := by positivity
          nlinarith
        exact hrat.trans (mul_le_mul_of_nonneg_right h102 hVqs_pos.le)
    have h2j : (2 : ℝ) ≤ (2 : ℝ) ^ j := by
      have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj
      simpa using this
    have hexp_bound1 : (2 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp (-((2 : ℝ) ^ j * (s / 4))) ≤ 1 / 2 := by
      have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      have harg : Real.log ((2 : ℝ) * (2 : ℝ) ^ (6 * k)) - (2 : ℝ) ^ j * (s / 4) ≤ -1 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        have hk12 : (12 : ℝ) ≤ k := by exact_mod_cast hk
        have hs1 : (400 : ℝ) * (k : ℝ) ^ 2 ≤ s := hs
        push_cast
        nlinarith
      have hrew : (2 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp (-((2 : ℝ) ^ j * (s / 4))) =
          Real.exp (Real.log ((2 : ℝ) * (2 : ℝ) ^ (6 * k)) - (2 : ℝ) ^ j * (s / 4)) := by
        rw [Real.exp_sub, Real.exp_log (by positivity), Real.exp_neg, ← div_eq_mul_inv]
      rw [hrew]
      have he1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      exact (Real.exp_le_exp.mpr harg).trans he1
    have hexp_bound2 : (20 : ℝ) * (2 : ℝ) ^ (6 * k) *
        Real.exp (1 / 2 - ((2 : ℝ) ^ j - 1) * (s / 4)) ≤ 1 / 2 := by
      have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      have hlog20 : Real.log 20 < 4 := by
        have : (20 : ℝ) < (2 : ℝ) ^ 5 := by norm_num
        have h5 : Real.log ((2 : ℝ) ^ 5) = 5 * Real.log 2 := by rw [Real.log_pow]; norm_num
        have h2 : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
        linarith [Real.log_lt_log (by norm_num) this]
      have harg : Real.log ((20 : ℝ) * (2 : ℝ) ^ (6 * k)) + (1 / 2 - ((2 : ℝ) ^ j - 1) * (s / 4)) ≤ -1 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        have hk12 : (12 : ℝ) ≤ k := by exact_mod_cast hk
        have hs1 : (400 : ℝ) * (k : ℝ) ^ 2 ≤ s := hs
        push_cast
        nlinarith
      have hrew : (20 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp (1 / 2 - ((2 : ℝ) ^ j - 1) * (s / 4)) =
          Real.exp (Real.log ((20 : ℝ) * (2 : ℝ) ^ (6 * k)) + (1 / 2 - ((2 : ℝ) ^ j - 1) * (s / 4))) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
      rw [hrew]
      have he1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      exact (Real.exp_le_exp.mpr harg).trans he1
    have hterm1 : sumTail k lo (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) ≤
        (1 / 2 : ℝ) * (prodV k qs * (1 / 10 : ℝ) * phiSieve β s *
          Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4)))) := by
      have hpow_split : Real.exp (-(((2 : ℝ) ^ (j + 1) - 1) * (s / 4))) =
          Real.exp (-((2 : ℝ) ^ j * (s / 4))) * Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4))) := by
        rw [← Real.exp_add, pow_succ]; congr 1; ring
      have h1 : prodV k lo * (1 / 10 : ℝ) * phiSieve β s *
          Real.exp (-(((2 : ℝ) ^ (j + 1) - 1) * (s / 4))) ≤
          ((2 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp (-((2 : ℝ) ^ j * (s / 4)))) *
            (prodV k qs * (1 / 10 : ℝ) * phiSieve β s * Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4)))) := by
        have heq : ((2 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp (-((2 : ℝ) ^ j * (s / 4)))) *
            (prodV k qs * (1 / 10 : ℝ) * phiSieve β s * Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4)))) =
            ((2 : ℝ) * (2 : ℝ) ^ (6 * k) * prodV k qs) * (1 / 10 : ℝ) * phiSieve β s *
              (Real.exp (-((2 : ℝ) ^ j * (s / 4))) * Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4)))) := by ring
        rw [hpow_split, heq]
        have hnn : 0 ≤ (1 / 10 : ℝ) * phiSieve β s *
            (Real.exp (-((2 : ℝ) ^ j * (s / 4))) * Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4)))) := by
          dsimp only [phiSieve]; positivity
        have hmul := mul_le_mul_of_nonneg_right hratio_lo hnn
        linarith
      have hVqs_pos : 0 < prodV k qs := prodV_pos k qs hqs_gt
      have hbase_nn : 0 ≤ prodV k qs * (1 / 10 : ℝ) * phiSieve β s *
          Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4))) := by
        dsimp only [phiSieve]; positivity
      exact hih.trans (h1.trans (mul_le_mul_of_nonneg_right hexp_bound1 hbase_nn))
    have hterm2 : (prodV k lo - prodV k qs) * phiSieve β ((2 : ℝ) ^ j * s - 1) ≤
        (1 / 2 : ℝ) * (prodV k qs * (1 / 10 : ℝ) * phiSieve β s *
          Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4)))) := by
      have hVqs_pos : 0 < prodV k qs := prodV_pos k qs hqs_gt
      have hphi_split : phiSieve β ((2 : ℝ) ^ j * s - 1) =
          phiSieve β s * Real.exp (1 / 2 - ((2 : ℝ) ^ j - 1) * (s / 4)) *
            Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4))) := by
        dsimp only [phiSieve]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1; ring
      have h1 : (prodV k lo - prodV k qs) * phiSieve β ((2 : ℝ) ^ j * s - 1) ≤
          prodV k lo * phiSieve β ((2 : ℝ) ^ j * s - 1) := by
        have hphi_nn : 0 ≤ phiSieve β ((2 : ℝ) ^ j * s - 1) := by dsimp only [phiSieve]; positivity
        nlinarith
      have h2 : prodV k lo * phiSieve β ((2 : ℝ) ^ j * s - 1) ≤
          ((20 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp (1 / 2 - ((2 : ℝ) ^ j - 1) * (s / 4))) *
            (prodV k qs * (1 / 10 : ℝ) * phiSieve β s * Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4)))) := by
        rw [hphi_split]
        have heq : ((20 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp (1 / 2 - ((2 : ℝ) ^ j - 1) * (s / 4))) *
            (prodV k qs * (1 / 10 : ℝ) * phiSieve β s * Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4)))) =
            ((2 : ℝ) * (2 : ℝ) ^ (6 * k) * prodV k qs) *
              (phiSieve β s * Real.exp (1 / 2 - ((2 : ℝ) ^ j - 1) * (s / 4)) *
                Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4)))) := by ring
        rw [heq]
        have hnn : 0 ≤ phiSieve β s * Real.exp (1 / 2 - ((2 : ℝ) ^ j - 1) * (s / 4)) *
            Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4))) := by
          dsimp only [phiSieve]; positivity
        exact mul_le_mul_of_nonneg_right hratio_lo hnn
      have hbase_nn : 0 ≤ prodV k qs * (1 / 10 : ℝ) * phiSieve β s *
          Real.exp (-(((2 : ℝ) ^ j - 1) * (s / 4))) := by
        dsimp only [phiSieve]; positivity
      exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right hexp_bound2 hbase_nn))
    linarith

set_option maxHeartbeats 400000 in
lemma sumTail_full_le (k w : ℕ) (hk : 12 ≤ k) (hw : 2 * k < w)
    (hlogw : (1000 : ℝ) * k ≤ Real.log (w : ℝ))
    (z D : ℝ) (hz : (w : ℝ) < z)
    (hs : (400 : ℝ) * (k : ℝ) ^ 2 ≤ Real.log D / Real.log z)
    (ps : List ℕ) (hdesc : ps.Pairwise (· > ·))
    (hps : ∀ p ∈ ps, p.Prime ∧ w < p ∧ (p : ℝ) ≤ z) :
    let β : ℝ := (400 : ℝ) * (k : ℝ) ^ 2
    let s : ℝ := Real.log D / Real.log z
    sumTail k ps (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) ≤
      prodV k ps * phiSieve β s := by
  intro β s
  have hlogw_pos : 0 < Real.log (w : ℝ) := by
    have : (0 : ℝ) < 1000 * k := by positivity
    linarith
  have hw_pos : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hz_pos : (0 : ℝ) < z := lt_trans hw_pos hz
  have hz1 : (1 : ℝ) ≤ z := le_trans (by exact_mod_cast (by omega : 1 ≤ w)) hz.le
  have hlogz_pos : 0 < Real.log z := lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hz.le)
  have hD_pos : 0 < Real.log D := by
    have hs_pos : 0 < s := lt_of_lt_of_le (by positivity) hs
    exact (div_pos_iff_of_pos_right hlogz_pos).mp hs_pos
  have hps_gt : ∀ p ∈ ps, 2 * k < p := fun p hp => by have := (hps p hp).2.1; omega
  have hVps_pos : 0 < prodV k ps := prodV_pos k ps hps_gt
  have hphi_pos : 0 < phiSieve β s := Real.exp_pos _
  -- Split ps at y0 = z^(1 - δ) with δ = 1/(40*k), and lo0 at y1 = z^(1/2)
  let δ : ℝ := 1 / ((40 : ℝ) * k)
  let y0 : ℝ := z ^ (1 - δ)
  let y1 : ℝ := z ^ (1 / 2 : ℝ)
  let hi0 : List ℕ := ps.filter (fun p : ℕ => decide (y0 < (p : ℝ)))
  let lo0 : List ℕ := ps.filter (fun p : ℕ => decide (¬ (y0 < (p : ℝ))))
  have hsplit0 : ps = hi0 ++ lo0 := list_split_desc ps hdesc y0
  have hlo0_desc : lo0.Pairwise (· > ·) := hdesc.filter _
  let hi1 : List ℕ := lo0.filter (fun p : ℕ => decide (y1 < (p : ℝ)))
  let lo1 : List ℕ := lo0.filter (fun p : ℕ => decide (¬ (y1 < (p : ℝ))))
  have hsplit1 : lo0 = hi1 ++ lo1 := list_split_desc lo0 hlo0_desc y1
  have hlo0_gt : ∀ p ∈ lo0, 2 * k < p := fun p hp => hps_gt p (List.mem_filter.mp hp).1
  have hlo1_gt : ∀ p ∈ lo1, 2 * k < p := fun p hp => hlo0_gt p (List.mem_filter.mp hp).1
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt : δ < 1 / 2 := by
    dsimp only [δ]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have hk12 : (12 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  -- Step 1: Bound hi0 contribution ≤ (1/2) * prodV k ps * phiSieve β s
  have hF_hi0 : ∀ p ∈ hi0,
      phiSieve β (Real.log D / Real.log (p : ℝ) - 1) ≤ phiSieve β (s - 1) := by
    intro p hp
    obtain ⟨_, hpw, hpz⟩ := hps p (List.mem_filter.mp hp).1
    have hlogp_pos : 0 < Real.log (p : ℝ) :=
      lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos (by exact_mod_cast hpw.le))
    have hlogp_le : Real.log (p : ℝ) ≤ Real.log z :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) hpz
    apply phiSieve_anti
    have : s ≤ Real.log D / Real.log (p : ℝ) :=
      div_le_div_of_nonneg_left hD_pos.le hlogp_pos hlogp_le
    linarith
  have htail0 : sumTail k ps (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) ≤
      sumTail k lo0 (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) +
        (prodV k lo0 - prodV k ps) * phiSieve β (s - 1) := by
    conv_lhs => rw [hsplit0]
    conv_rhs => rw [hsplit0]
    exact sumTail_append_le k hi0 lo0 _ _ (hsplit0 ▸ hps_gt) hF_hi0
  have hratio0 : prodV k lo0 ≤ (12 / 10 : ℝ) * prodV k ps := by
    let a0 : ℝ := max (w : ℝ) y0
    have hwa0 : (w : ℝ) ≤ a0 := le_max_left _ _
    have ha0z : a0 ≤ z := by
      apply max_le hz.le
      calc y0 = z ^ (1 - δ) := rfl
        _ ≤ z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
        _ = z := Real.rpow_one z
    have hhi0_in : ∀ p ∈ hi0, p.Prime ∧ a0 < (p : ℝ) ∧ (p : ℝ) ≤ z := by
      intro p hp
      obtain ⟨hpm, hpf⟩ := List.mem_filter.mp hp
      obtain ⟨hpr, hpw, hpz⟩ := hps p hpm
      simp only [decide_eq_true_eq] at hpf
      exact ⟨hpr, max_lt (by exact_mod_cast hpw) hpf, hpz⟩
    have hrat := prodV_ratio_le_real k w (by omega) hw hlogw hi0 lo0
      ((pairwise_gt_nodup hdesc).filter _) a0 z hwa0 ha0z hhi0_in hlo0_gt
    rw [← hsplit0] at hrat
    have hlog_rat : Real.log z / Real.log a0 ≤ (1 - δ)⁻¹ := by
      have hloga0 : 0 < Real.log a0 := lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hwa0)
      rw [div_le_iff₀ hloga0]
      have hy0_le : Real.log y0 ≤ Real.log a0 :=
        Real.log_le_log (Real.rpow_pos_of_pos hz_pos _) (le_max_right _ _)
      have hlogy0 : Real.log y0 = (1 - δ) * Real.log z := Real.log_rpow hz_pos _
      have h1d_pos : 0 < 1 - δ := by linarith
      have : (1 - δ)⁻¹ * ((1 - δ) * Real.log z) = Real.log z := by
        rw [← mul_assoc, inv_mul_cancel₀ h1d_pos.ne', one_mul]
      have hmul := mul_le_mul_of_nonneg_left (hlogy0 ▸ hy0_le) (inv_nonneg.mpr h1d_pos.le)
      linarith
    have hpow0 : (Real.log z / Real.log a0) ^ (6 * k) ≤ 117 / 100 := by
      have hinv1 : (1 - δ)⁻¹ ≤ Real.exp (2 * δ) := inv_one_sub_le_exp_two_mul hδ_pos.le hδ_lt.le
      have h1 : (Real.log z / Real.log a0) ^ (6 * k) ≤ (Real.exp (2 * δ)) ^ (6 * k) :=
        pow_le_pow_left₀ (div_nonneg hlogz_pos.le
          (lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hwa0)).le) (hlog_rat.trans hinv1) (6 * k)
      have h2 : (Real.exp (2 * δ)) ^ (6 * k) = Real.exp (3 / 10 : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp only [δ]
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        push_cast; field_simp; ring
      -- Wait: exp(3/10) ≈ 1.3498 > 1.17! Let's bound (1 - δ)⁻¹ ≤ 1 + 2 * δ? No, exp(3/10) = 1.3498!
      -- Actually (1 - 1/(40k))⁻¹ = 1 + 1/(40k - 1) ≤ exp(1/(39k)), so ^ (6k) ≤ exp(6/39) = exp(2/13) ≈ 1.1663!
      have hinv_tight : (1 - δ)⁻¹ ≤ Real.exp (1 / ((39 : ℝ) * k)) := by
        have h1d : 0 < 1 - δ := by linarith
        have hle : (1 - δ)⁻¹ ≤ 1 + 1 / ((39 : ℝ) * k) := by
          rw [inv_le_iff_one_le_mul₀' h1d]
          dsimp only [δ]
          have hk12 : (12 : ℝ) ≤ k := by exact_mod_cast hk
          have hmul : (1 - 1 / ((40 : ℝ) * k)) * (1 + 1 / ((39 : ℝ) * k)) =
              1 + (k - 1) / ((1560 : ℝ) * k ^ 2) := by
            have hk0 : (k : ℝ) ≠ 0 := by positivity
            field_simp; ring
          rw [hmul]
          have : (0 : ℝ) ≤ (k - 1) / ((1560 : ℝ) * k ^ 2) := div_nonneg (by linarith) (by positivity)
          linarith
        exact hle.trans (by linarith [Real.add_one_le_exp (1 / ((39 : ℝ) * k))])
      have h1' : (Real.log z / Real.log a0) ^ (6 * k) ≤ (Real.exp (1 / ((39 : ℝ) * k))) ^ (6 * k) :=
        pow_le_pow_left₀ (div_nonneg hlogz_pos.le
          (lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hwa0)).le) (hlog_rat.trans hinv_tight) (6 * k)
      have h2' : (Real.exp (1 / ((39 : ℝ) * k))) ^ (6 * k) = Real.exp (2 / 13 : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        push_cast; field_simp; ring
      have h3' : Real.exp (2 / 13 : ℝ) ≤ 117 / 100 := by
        have h := Real.exp_bound (show |(2 / 13 : ℝ)| ≤ 1 by norm_num) (show 0 < 3 by norm_num)
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one] at h
        norm_num [abs_le] at h
        linarith
      linarith
    have h12 : (102 / 100 : ℝ) * (Real.log z / Real.log a0) ^ (6 * k) ≤ 12 / 10 := by linarith
    exact hrat.trans (mul_le_mul_of_nonneg_right h12 hVps_pos.le)
  have hterm0 : (prodV k lo0 - prodV k ps) * phiSieve β (s - 1) ≤ (1 / 2 : ℝ) * (prodV k ps * phiSieve β s) := by
    have hphi_step : phiSieve β (s - 1) = phiSieve β s * Real.exp (1 / 2 : ℝ) := by
      dsimp only [phiSieve]; rw [← Real.exp_add]; congr 1; ring
    have hexp_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have h := Real.exp_bound (show |(1 / 2 : ℝ)| ≤ 1 by norm_num) (show 0 < 3 by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one] at h
      norm_num [abs_le] at h
      linarith
    rw [hphi_step]
    have h1 : (prodV k lo0 - prodV k ps) * (phiSieve β s * Real.exp (1 / 2 : ℝ)) ≤
        (2 / 10 * prodV k ps) * (phiSieve β s * Real.exp (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (2 / 10 * prodV k ps) * (phiSieve β s * Real.exp (1 / 2 : ℝ)) ≤
        (2 / 10 * prodV k ps) * (phiSieve β s * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_half hphi_pos.le) (by positivity)
    have h3 : 0 ≤ prodV k ps * phiSieve β s := by positivity
    linarith
  -- Step 2: Bound hi1 contribution ≤ (1/4) * prodV k ps * phiSieve β s
  have hF_hi1 : ∀ p ∈ hi1,
      phiSieve β (Real.log D / Real.log (p : ℝ) - 1) ≤ phiSieve β (s * (1 + δ) - 1) := by
    intro p hp
    have hlo0_m : p ∈ lo0 := (List.mem_filter.mp hp).1
    obtain ⟨hpm, hpf0⟩ := List.mem_filter.mp hlo0_m
    obtain ⟨_, hpw, _⟩ := hps p hpm
    simp only [decide_eq_true_eq, not_lt] at hpf0
    have hlogp_pos : 0 < Real.log (p : ℝ) :=
      lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos (by exact_mod_cast hpw.le))
    have hlogp_le : Real.log (p : ℝ) ≤ (1 - δ) * Real.log z := by
      calc Real.log (p : ℝ) ≤ Real.log y0 := Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) hpf0
        _ = (1 - δ) * Real.log z := Real.log_rpow hz_pos _
    apply phiSieve_anti
    have hdiv : s * (1 + δ) ≤ Real.log D / Real.log (p : ℝ) := by
      dsimp only [s]
      rw [le_div_iff₀ hlogp_pos]
      have hprod_le : (1 + δ) * (1 - δ) ≤ 1 := by nlinarith
      calc Real.log D / Real.log z * (1 + δ) * Real.log (p : ℝ)
          ≤ Real.log D / Real.log z * (1 + δ) * ((1 - δ) * Real.log z) :=
            mul_le_mul_of_nonneg_left hlogp_le (by positivity)
        _ = ((1 + δ) * (1 - δ)) * ((Real.log D / Real.log z) * Real.log z) := by ring
        _ = ((1 + δ) * (1 - δ)) * Real.log D := by rw [div_mul_cancel₀ _ hlogz_pos.ne']
        _ ≤ 1 * Real.log D := mul_le_mul_of_nonneg_right hprod_le hD_pos.le
        _ = Real.log D := one_mul _
    linarith
  have htail1 : sumTail k lo0 (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) ≤
      sumTail k lo1 (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) +
        (prodV k lo1 - prodV k lo0) * phiSieve β (s * (1 + δ) - 1) := by
    conv_lhs => rw [hsplit1]
    conv_rhs => rw [hsplit1]
    exact sumTail_append_le k hi1 lo1 _ _ (hsplit1 ▸ hlo0_gt) hF_hi1
  have hratio_lo1 : prodV k lo1 ≤ (2 : ℝ) * (2 : ℝ) ^ (6 * k) * prodV k ps := by
    have hsplit_all : ps = (hi0 ++ hi1) ++ lo1 := by rw [hsplit0, hsplit1, List.append_assoc]
    have hnd_all : (hi0 ++ hi1).Nodup := by
      have hnd := pairwise_gt_nodup hdesc
      rw [hsplit_all] at hnd
      exact (List.nodup_append.mp hnd).1
    let a1 : ℝ := max (w : ℝ) y1
    have hwa1 : (w : ℝ) ≤ a1 := le_max_left _ _
    have ha1z : a1 ≤ z := by
      apply max_le hz.le
      calc y1 = z ^ (1 / 2 : ℝ) := rfl
        _ ≤ z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
        _ = z := Real.rpow_one z
    have hhi_in : ∀ p ∈ hi0 ++ hi1, p.Prime ∧ a1 < (p : ℝ) ∧ (p : ℝ) ≤ z := by
      intro p hp
      rcases List.mem_append.mp hp with hp0 | hp1
      · obtain ⟨hpm, hpf0⟩ := List.mem_filter.mp hp0
        obtain ⟨hpr, hpw, hpz⟩ := hps p hpm
        simp only [decide_eq_true_eq] at hpf0
        have hy1_le_y0 : y1 ≤ y0 :=
          Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
        exact ⟨hpr, max_lt (by exact_mod_cast hpw) (lt_of_le_of_lt hy1_le_y0 hpf0), hpz⟩
      · obtain ⟨hlo0m, hpf1⟩ := List.mem_filter.mp hp1
        obtain ⟨hpm, _⟩ := List.mem_filter.mp hlo0m
        obtain ⟨hpr, hpw, hpz⟩ := hps p hpm
        simp only [decide_eq_true_eq] at hpf1
        exact ⟨hpr, max_lt (by exact_mod_cast hpw) hpf1, hpz⟩
    have hrat := prodV_ratio_le_real k w (by omega) hw hlogw (hi0 ++ hi1) lo1 hnd_all
      a1 z hwa1 ha1z hhi_in hlo1_gt
    rw [← hsplit_all] at hrat
    have hlog_rat : Real.log z / Real.log a1 ≤ 2 := by
      have hloga1 : 0 < Real.log a1 := lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hwa1)
      rw [div_le_iff₀ hloga1]
      have hy1_le : Real.log y1 ≤ Real.log a1 :=
        Real.log_le_log (Real.rpow_pos_of_pos hz_pos _) (le_max_right _ _)
      have hlogy1 : Real.log y1 = (1 / 2 : ℝ) * Real.log z := Real.log_rpow hz_pos _
      linarith
    have hpow1 : (Real.log z / Real.log a1) ^ (6 * k) ≤ (2 : ℝ) ^ (6 * k) :=
      pow_le_pow_left₀ (div_nonneg hlogz_pos.le
        (lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hwa1)).le) hlog_rat (6 * k)
    have h102 : (102 / 100 : ℝ) * (Real.log z / Real.log a1) ^ (6 * k) ≤ (2 : ℝ) * (2 : ℝ) ^ (6 * k) := by
      have : (0 : ℝ) ≤ (2 : ℝ) ^ (6 * k) := by positivity
      nlinarith
    exact hrat.trans (mul_le_mul_of_nonneg_right h102 hVps_pos.le)
  have hterm1 : (prodV k lo1 - prodV k lo0) * phiSieve β (s * (1 + δ) - 1) ≤
      (1 / 4 : ℝ) * (prodV k ps * phiSieve β s) := by
    have hphi_split : phiSieve β (s * (1 + δ) - 1) = phiSieve β s * Real.exp ((1 - s * δ) / 2) := by
      dsimp only [phiSieve]; rw [← Real.exp_add]; congr 1; ring
    have hVlo0_pos : 0 < prodV k lo0 := prodV_pos k lo0 hlo0_gt
    have hphi1_nn : 0 ≤ phiSieve β (s * (1 + δ) - 1) := (Real.exp_pos _).le
    have hbound : (2 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp ((1 - s * δ) / 2) ≤ 1 / 4 := by
      have hlog2 : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
      have hsδ : (10 : ℝ) * k ≤ s * δ := by
        dsimp only [δ]
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        have heq : (400 : ℝ) * (k : ℝ) ^ 2 * (1 / ((40 : ℝ) * k)) = (10 : ℝ) * k := by
          field_simp; ring
        have hmul := mul_le_mul_of_nonneg_right hs hδ_pos.le
        linarith
      have harg : Real.log ((2 : ℝ) * (2 : ℝ) ^ (6 * k)) + (1 - s * δ) / 2 ≤ -2 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        have hk12 : (12 : ℝ) ≤ k := by exact_mod_cast hk
        push_cast
        nlinarith
      have hrew : (2 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp ((1 - s * δ) / 2) =
          Real.exp (Real.log ((2 : ℝ) * (2 : ℝ) ^ (6 * k)) + (1 - s * δ) / 2) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
      rw [hrew]
      have he2 : Real.exp (-2 : ℝ) ≤ 1 / 4 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
        have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_gt_d9]
      exact (Real.exp_le_exp.mpr harg).trans he2
    have h1 : (prodV k lo1 - prodV k lo0) * phiSieve β (s * (1 + δ) - 1) ≤
        prodV k lo1 * phiSieve β (s * (1 + δ) - 1) := by nlinarith
    have h2 : prodV k lo1 * phiSieve β (s * (1 + δ) - 1) ≤
        ((2 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp ((1 - s * δ) / 2)) * (prodV k ps * phiSieve β s) := by
      rw [hphi_split]
      have heq : ((2 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp ((1 - s * δ) / 2)) * (prodV k ps * phiSieve β s) =
          ((2 : ℝ) * (2 : ℝ) ^ (6 * k) * prodV k ps) * (phiSieve β s * Real.exp ((1 - s * δ) / 2)) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hratio_lo1 (by positivity)
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right hbound (by positivity)))
  -- Step 3: Bound lo1 contribution ≤ (1/4) * prodV k ps * phiSieve β s via sumTail_dyadic_le
  have hlo1_props : ∀ q ∈ lo1, q.Prime ∧ w < q ∧ (q : ℝ) ≤ z ^ ((1 / 2 : ℝ) ^ 1) := by
    intro q hq
    obtain ⟨hlo0m, hqf1⟩ := List.mem_filter.mp hq
    obtain ⟨hpm, _⟩ := List.mem_filter.mp hlo0m
    obtain ⟨hpr, hqw, _⟩ := hps q hpm
    simp only [decide_eq_true_eq, not_lt] at hqf1
    dsimp only [y1] at hqf1
    exact ⟨hpr, hqw, by simpa only [pow_one] using hqf1⟩
  obtain ⟨fuel, hfuel⟩ : ∃ fuel : ℕ, Real.log z * (1 / 2 : ℝ) ^ (1 + fuel) ≤ Real.log (w : ℝ) := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hlogw_pos hlogz_pos) (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨N, ?_⟩
    have h1 : (1 / 2 : ℝ) ^ (1 + N) ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left N 1)
    have h2 : (1 / 2 : ℝ) ^ N * Real.log z < Real.log (w : ℝ) := (lt_div_iff₀ hlogz_pos).mp hN
    nlinarith
  have hdyadic := sumTail_dyadic_le k w hk hw hlogw z D hz hs fuel 1 le_rfl hfuel
    lo1 (hlo0_desc.filter _) hlo1_props
  have hterm2 : sumTail k lo1 (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) ≤
      (1 / 4 : ℝ) * (prodV k ps * phiSieve β s) := by
    have hbound : (2 : ℝ) * (2 : ℝ) ^ (6 * k) * (1 / 10 : ℝ) * Real.exp (-(((2 : ℝ) ^ 1 - 1) * (s / 4))) ≤ 1 / 4 := by
      have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      have harg : Real.log ((2 : ℝ) * (2 : ℝ) ^ (6 * k)) - s / 4 ≤ -1 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        have hk12 : (12 : ℝ) ≤ k := by exact_mod_cast hk
        have hs1 : (400 : ℝ) * (k : ℝ) ^ 2 ≤ s := hs
        have hk2 : (12 : ℝ) * (k : ℝ) ≤ (k : ℝ) ^ 2 := by
          have : 0 ≤ ((k : ℝ) - 12) * (k : ℝ) := by positivity
          linarith
        have h6k : (6 * k : ℕ) * Real.log 2 ≤ (6 * k : ℝ) := by
          have hnn : (0 : ℝ) ≤ (6 * k : ℕ) := by positivity
          have := mul_le_mul_of_nonneg_left hlog2.le hnn
          push_cast at this ⊢
          linarith
        linarith
      have hrew : (2 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp (-(((2 : ℝ) ^ 1 - 1) * (s / 4))) =
          Real.exp (Real.log ((2 : ℝ) * (2 : ℝ) ^ (6 * k)) - s / 4) := by
        have hsimp : -(((2 : ℝ) ^ 1 - 1) * (s / 4)) = -(s / 4) := by ring
        rw [hsimp, Real.exp_sub, Real.exp_log (by positivity), Real.exp_neg, ← div_eq_mul_inv]
      have he1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      have hle : (2 : ℝ) * (2 : ℝ) ^ (6 * k) * Real.exp (-(((2 : ℝ) ^ 1 - 1) * (s / 4))) ≤ 1 / 2 := by
        rw [hrew]; exact (Real.exp_le_exp.mpr harg).trans he1
      linarith
    have h1 : prodV k lo1 * (1 / 10 : ℝ) * phiSieve β s * Real.exp (-(((2 : ℝ) ^ 1 - 1) * (s / 4))) ≤
        ((2 : ℝ) * (2 : ℝ) ^ (6 * k) * (1 / 10 : ℝ) * Real.exp (-(((2 : ℝ) ^ 1 - 1) * (s / 4)))) *
          (prodV k ps * phiSieve β s) := by
      have heq : ((2 : ℝ) * (2 : ℝ) ^ (6 * k) * (1 / 10 : ℝ) * Real.exp (-(((2 : ℝ) ^ 1 - 1) * (s / 4)))) *
          (prodV k ps * phiSieve β s) =
          ((2 : ℝ) * (2 : ℝ) ^ (6 * k) * prodV k ps) * ((1 / 10 : ℝ) * phiSieve β s *
            Real.exp (-(((2 : ℝ) ^ 1 - 1) * (s / 4)))) := by ring
      rw [heq, mul_assoc (prodV k lo1), mul_assoc (prodV k lo1)]
      exact mul_le_mul_of_nonneg_right hratio_lo1 (by positivity)
    exact hdyadic.trans (h1.trans (mul_le_mul_of_nonneg_right hbound (by positivity)))
  linarith

lemma sieve_main_bound (k w : ℕ) (hk : 12 ≤ k) (hw : 2 * k < w)
    (hlogw : (1000 : ℝ) * k ≤ Real.log (w : ℝ)) :
    let β : ℝ := (400 : ℝ) * (k : ℝ) ^ 2
    ∀ (N : ℕ) (ps : List ℕ), ps.length ≤ N → ps.Pairwise (· > ·) →
      (∀ p ∈ ps, p.Prime ∧ w < p) →
      ∀ (z D : ℝ), 0 < D → (w : ℝ) < z → (∀ p ∈ ps, (p : ℝ) ≤ z) →
        ((β ≤ Real.log D / Real.log z →
          sieveSum true β D ps (multG k) - prodV k ps ≤ prodV k ps * phiSieve β (Real.log D / Real.log z)) ∧
         (β + 1 ≤ Real.log D / Real.log z →
          prodV k ps - sieveSum false β D ps (multG k) ≤ prodV k ps * phiSieve β (Real.log D / Real.log z))) := by
  intro β N
  have hlogw_pos : 0 < Real.log (w : ℝ) := by
    have : (0 : ℝ) < 1000 * k := by positivity
    linarith
  have hw_pos : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  induction N with
  | zero =>
    intro ps hlen _ _ z D _ _ _
    have hnil : ps = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hnil
    constructor <;> intro _ <;> simp only [sieveSum, prodV_nil, multG, Nat.primeFactors_one,
      Finset.prod_empty, sub_self, one_mul] <;> exact (Real.exp_pos _).le
  | succ N ih =>
    intro ps hlen hdesc hps z D hD_pos hz hpz
    have hprime : ∀ p ∈ ps, p.Prime := fun p hp => (hps p hp).1
    have hnd : ps.Nodup := pairwise_gt_nodup hdesc
    have hz_pos : (0 : ℝ) < z := lt_trans hw_pos hz
    have hlogz_pos : 0 < Real.log z := lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hz.le)
    have htail_props : ∀ (hi : List ℕ) (p : ℕ) (qs : List ℕ), ps = hi ++ p :: qs →
        qs.length ≤ N ∧ qs.Pairwise (· > ·) ∧ (∀ q ∈ qs, q.Prime ∧ w < q) ∧
        (w : ℝ) < (p : ℝ) ∧ (∀ q ∈ qs, (q : ℝ) ≤ (p : ℝ)) ∧ (p : ℝ) ≤ z := by
      intro hi p qs heq
      have hlen_qs : qs.length ≤ N := by
        have := congrArg List.length heq
        simp only [List.length_append, List.length_cons] at this
        omega
      have hdesc' : (p :: qs).Pairwise (· > ·) := (List.pairwise_append.mp (heq ▸ hdesc)).2.1
      obtain ⟨hp_gt, hqs_desc⟩ := List.pairwise_cons.mp hdesc'
      have hp_mem : p ∈ ps := heq ▸ List.mem_append_right hi (List.mem_cons_self ..)
      have hqs_mem : ∀ q ∈ qs, q ∈ ps := fun q hq =>
        heq ▸ List.mem_append_right hi (List.mem_cons_of_mem p hq)
      exact ⟨hlen_qs, hqs_desc, fun q hq => hps q (hqs_mem q hq),
        by exact_mod_cast (hps p hp_mem).2, fun q hq => by exact_mod_cast (hp_gt q hq).le, hpz p hp_mem⟩
    constructor
    · intro hs
      apply (buchstab_pos_le k β D ps (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) hprime hnd _).trans
      · exact sumTail_full_le k w hk hw hlogw z D hz hs ps hdesc (fun p hp => ⟨(hps p hp).1, (hps p hp).2, hpz p hp⟩)
      · intro hi p qs heq
        obtain ⟨hlen_qs, hqs_desc, hqs_p, hwp, hqp, hpz_p⟩ := htail_props hi p qs heq
        have hp_pos : (0 : ℝ) < p := lt_trans hw_pos hwp
        have hlogp_pos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hwp.le)
        have hlog_div : Real.log (D / (p : ℝ)) / Real.log (p : ℝ) = Real.log D / Real.log (p : ℝ) - 1 := by
          rw [Real.log_div hD_pos.ne' hp_pos.ne', sub_div, div_self hlogp_pos.ne']
        split_ifs with hcut
        · have hs' : β + 1 ≤ Real.log (D / (p : ℝ)) / Real.log (p : ℝ) := by
            rw [hlog_div]
            have hlog_cut : (β + 2) * Real.log (p : ℝ) ≤ Real.log D := by
              calc (β + 2) * Real.log (p : ℝ) = Real.log ((p : ℝ) ^ (β + 2)) := (Real.log_rpow hp_pos _).symm
                _ ≤ Real.log D := Real.log_le_log (Real.rpow_pos_of_pos hp_pos _) hcut
            have : β + 2 ≤ Real.log D / Real.log (p : ℝ) := (le_div_iff₀ hlogp_pos).mpr hlog_cut
            linarith
          have hsub := (ih qs hlen_qs hqs_desc hqs_p (p : ℝ) (D / (p : ℝ)) (div_pos hD_pos hp_pos) hwp hqp).2 hs'
          rwa [hlog_div] at hsub
        · push Not at hcut
          have hlog_lt : Real.log D < (β + 2) * Real.log (p : ℝ) := by
            calc Real.log D < Real.log ((p : ℝ) ^ (β + 2)) := Real.log_lt_log hD_pos hcut
              _ = (β + 2) * Real.log (p : ℝ) := Real.log_rpow hp_pos _
          have hrat_lt : Real.log D / Real.log (p : ℝ) < β + 2 := (div_lt_iff₀ hlogp_pos).mpr hlog_lt
          have h1_le : 1 ≤ phiSieve β (Real.log D / Real.log (p : ℝ) - 1) := by
            dsimp only [phiSieve]
            exact Real.one_le_exp (by linarith)
          have hVqs_pos : 0 < prodV k qs := prodV_pos k qs (fun q hq => by have := (hqs_p q hq).2; omega)
          nlinarith
    · intro hs
      apply (buchstab_neg_le k β D ps (fun p => phiSieve β (Real.log D / Real.log (p : ℝ) - 1)) hprime hnd _).trans
      · exact sumTail_full_le k w hk hw hlogw z D hz (by linarith) ps hdesc
          (fun p hp => ⟨(hps p hp).1, (hps p hp).2, hpz p hp⟩)
      · intro hi p qs heq
        obtain ⟨hlen_qs, hqs_desc, hqs_p, hwp, hqp, hpz_p⟩ := htail_props hi p qs heq
        have hp_pos : (0 : ℝ) < p := lt_trans hw_pos hwp
        have hlogp_pos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le hlogw_pos (Real.log_le_log hw_pos hwp.le)
        have hlog_div : Real.log (D / (p : ℝ)) / Real.log (p : ℝ) = Real.log D / Real.log (p : ℝ) - 1 := by
          rw [Real.log_div hD_pos.ne' hp_pos.ne', sub_div, div_self hlogp_pos.ne']
        have hlogD_pos : 0 < Real.log D := by
          have hβ_pos : 0 < β := by positivity
          have : 0 < Real.log D / Real.log z := by linarith
          exact (div_pos_iff_of_pos_right hlogz_pos).mp this
        have hs' : β ≤ Real.log (D / (p : ℝ)) / Real.log (p : ℝ) := by
          rw [hlog_div]
          have h1 : Real.log D / Real.log z ≤ Real.log D / Real.log (p : ℝ) :=
            div_le_div_of_nonneg_left hlogD_pos.le hlogp_pos (Real.log_le_log hp_pos hpz_p)
          linarith
        have hsub := (ih qs hlen_qs hqs_desc hqs_p (p : ℝ) (D / (p : ℝ)) (div_pos hD_pos hp_pos) hwp hqp).1 hs'
        rwa [hlog_div] at hsub

/- ### Section 4: Sieve Support, Remainder Bound, and CRT Counting -/

noncomputable def sieveSupp (sign : Bool) (β D : ℝ) : List ℕ → Finset ℕ
  | [] => {1}
  | p :: ps =>
    match sign with
    | false => sieveSupp false β D ps ∪ (sieveSupp true β (D / (p : ℝ)) ps).image (p * ·)
    | true =>
      if (p : ℝ) ^ (β + 2) ≤ D then
        sieveSupp true β D ps ∪ (sieveSupp false β (D / (p : ℝ)) ps).image (p * ·)
      else
        sieveSupp true β D ps

lemma mem_sieveSupp_props (sign : Bool) (β D : ℝ) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    ∀ d ∈ sieveSupp sign β D ps, 0 < d ∧ ∀ q ∈ d.primeFactors, q ∈ ps := by
  induction ps generalizing sign D with
  | nil =>
    intro d hd
    simp only [sieveSupp, Finset.mem_singleton] at hd
    subst hd
    simp
  | cons p ps ih =>
    have hp : p.Prime := hprime p (List.mem_cons_self ..)
    have hps : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    intro d hd
    have hbranch : ∀ (s1 s2 : Bool),
        d ∈ sieveSupp s1 β D ps ∪ (sieveSupp s2 β (D / (p : ℝ)) ps).image (p * ·) →
        0 < d ∧ ∀ q ∈ d.primeFactors, q ∈ p :: ps := by
      intro s1 s2 hm
      rcases Finset.mem_union.mp hm with hm | hm
      · obtain ⟨hd0, hpf⟩ := ih s1 D hps d hm
        exact ⟨hd0, fun q hq => List.mem_cons_of_mem p (hpf q hq)⟩
      · rcases Finset.mem_image.mp hm with ⟨d', hd', rfl⟩
        obtain ⟨hd'0, hpf⟩ := ih s2 (D / (p : ℝ)) hps d' hd'
        refine ⟨Nat.mul_pos hp.pos hd'0, fun q hq => ?_⟩
        rw [Nat.primeFactors_mul hp.ne_zero hd'0.ne', Finset.mem_union] at hq
        rcases hq with hq | hq
        · have hqp := Nat.mem_primeFactors.mp hq
          have : q = p := (Nat.prime_dvd_prime_iff_eq hqp.1 hp).mp hqp.2.1
          subst this; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem p (hpf q hq)
    cases sign
    · exact hbranch false true hd
    · simp only [sieveSupp] at hd
      split_ifs at hd
      · exact hbranch true false hd
      · obtain ⟨hd0, hpf⟩ := ih true D hps d hd
        exact ⟨hd0, fun q hq => List.mem_cons_of_mem p (hpf q hq)⟩

lemma sieveAbs_eq_sum_sieveSupp (sign : Bool) (β D : ℝ) (ps : List ℕ) (f : ℕ → ℝ)
    (hprime : ∀ p ∈ ps, p.Prime) (hnd : ps.Nodup) :
    sieveAbs sign β D ps f = ∑ d ∈ sieveSupp sign β D ps, f d := by
  induction ps generalizing sign D f with
  | nil => simp [sieveAbs, sieveSupp]
  | cons p ps ih =>
    have hp : p.Prime := hprime p (List.mem_cons_self ..)
    have hps : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    obtain ⟨hp_not, hps_nd⟩ := List.nodup_cons.mp hnd
    have hdisj : ∀ (s1 s2 : Bool),
        Disjoint (sieveSupp s1 β D ps) ((sieveSupp s2 β (D / (p : ℝ)) ps).image (p * ·)) := by
      intro s1 s2
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      rcases Finset.mem_image.mp hd2 with ⟨d', hd', rfl⟩
      obtain ⟨hd1_pos, hpf1⟩ := mem_sieveSupp_props s1 β D ps hps (p * d') hd1
      have hp_mem : p ∈ (p * d').primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_right p d', hd1_pos.ne'⟩
      exact hp_not (hpf1 p hp_mem)
    have hinj : Function.Injective (p * ·) := fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h
    cases sign
    · simp only [sieveAbs, sieveSupp]
      rw [Finset.sum_union (hdisj false true), Finset.sum_image (fun _ _ _ _ h => hinj h),
        ih false D f hps hps_nd, ih true (D / (p : ℝ)) (fun d => f (p * d)) hps hps_nd]
    · simp only [sieveAbs, sieveSupp]
      split_ifs
      · rw [Finset.sum_union (hdisj true false), Finset.sum_image (fun _ _ _ _ h => hinj h),
          ih true D f hps hps_nd, ih false (D / (p : ℝ)) (fun d => f (p * d)) hps hps_nd]
      · exact ih true D f hps hps_nd

lemma mem_sieveSupp_le_D (sign : Bool) (β D : ℝ) (ps : List ℕ)
    (hβ : 0 ≤ β) (hprime : ∀ p ∈ ps, p.Prime) (hdesc : ps.Pairwise (· > ·))
    (hD : 1 ≤ D) (hfalse : sign = false → ∀ p ∈ ps, (p : ℝ) ≤ D) :
    ∀ d ∈ sieveSupp sign β D ps, 1 ≤ d ∧ (d : ℝ) ≤ D := by
  induction ps generalizing sign D with
  | nil =>
    intro d hd
    simp only [sieveSupp, Finset.mem_singleton] at hd
    subst hd
    exact ⟨le_rfl, by simpa using hD⟩
  | cons p ps ih =>
    have hp : p.Prime := hprime p (List.mem_cons_self ..)
    have hps : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    obtain ⟨hp_gt, hps_desc⟩ := List.pairwise_cons.mp hdesc
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp_ge2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    intro d hd
    cases sign
    · simp only [sieveSupp, Finset.mem_union] at hd
      rcases hd with hd | hd
      · exact ih false D hps hps_desc hD (fun _ q hq => hfalse rfl q (List.mem_cons_of_mem p hq)) d hd
      · rcases Finset.mem_image.mp hd with ⟨d', hd', rfl⟩
        have hpD : (p : ℝ) ≤ D := hfalse rfl p (List.mem_cons_self ..)
        have hDp : 1 ≤ D / (p : ℝ) := (one_le_div hp_pos).mpr hpD
        obtain ⟨hd'1, hd'D⟩ := ih true (D / (p : ℝ)) hps hps_desc hDp (fun h => by cases h) d' hd'
        refine ⟨Nat.mul_pos hp.pos hd'1, ?_⟩
        push_cast
        calc (p : ℝ) * (d' : ℝ) ≤ (p : ℝ) * (D / (p : ℝ)) := mul_le_mul_of_nonneg_left hd'D hp_pos.le
          _ = D := mul_div_cancel₀ D hp_pos.ne'
    · simp only [sieveSupp] at hd
      split_ifs at hd with hcut
      · rcases Finset.mem_union.mp hd with hd | hd
        · exact ih true D hps hps_desc hD (fun h => by cases h) d hd
        · rcases Finset.mem_image.mp hd with ⟨d', hd', rfl⟩
          have hp2_le : (p : ℝ) ^ (2 : ℝ) ≤ (p : ℝ) ^ (β + 2) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          have hp_sq : (p : ℝ) * (p : ℝ) ≤ D := by
            have hsq : (p : ℝ) ^ (2 : ℝ) = (p : ℝ) * (p : ℝ) := by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq]
            calc (p : ℝ) * (p : ℝ) = (p : ℝ) ^ (2 : ℝ) := hsq.symm
              _ ≤ (p : ℝ) ^ (β + 2) := hp2_le
              _ ≤ D := hcut
          have hp_le_Dp : (p : ℝ) ≤ D / (p : ℝ) := (le_div_iff₀ hp_pos).mpr hp_sq
          have hDp : 1 ≤ D / (p : ℝ) := by linarith
          have hq_le : ∀ q ∈ ps, (q : ℝ) ≤ D / (p : ℝ) := fun q hq => by
            have hqp : (q : ℝ) < (p : ℝ) := by exact_mod_cast hp_gt q hq
            linarith
          obtain ⟨hd'1, hd'D⟩ := ih false (D / (p : ℝ)) hps hps_desc hDp (fun _ => hq_le) d' hd'
          refine ⟨Nat.mul_pos hp.pos hd'1, ?_⟩
          push_cast
          calc (p : ℝ) * (d' : ℝ) ≤ (p : ℝ) * (D / (p : ℝ)) := mul_le_mul_of_nonneg_left hd'D hp_pos.le
            _ = D := mul_div_cancel₀ D hp_pos.ne'
      · exact ih true D hps hps_desc hD (fun h => by cases h) d hd

lemma pow_omega_le (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (k : ℝ) ^ d.primeFactors.card ≤ (k : ℝ) ^ (k ^ 4) * (d : ℝ) ^ (1 / 4 : ℝ) := by
  let S1 := d.primeFactors.filter (· ≤ k ^ 4)
  let S2 := d.primeFactors.filter (fun p => ¬ p ≤ k ^ 4)
  have hcard : d.primeFactors.card = S1.card + S2.card := by
    dsimp only [S1, S2]
    exact (Finset.card_filter_add_card_filter_not (s := d.primeFactors) (p := (· ≤ k ^ 4))).symm
  have hS1 : S1.card ≤ k ^ 4 := by
    have hsub : S1 ⊆ Finset.Icc 1 (k ^ 4) := by
      intro p hp
      obtain ⟨hpm, hple⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Nat.mem_primeFactors.mp hpm).1.pos, hple⟩
    calc S1.card ≤ (Finset.Icc 1 (k ^ 4)).card := Finset.card_le_card hsub
      _ = k ^ 4 := by simp
  have hS1_pow : (k : ℝ) ^ S1.card ≤ (k : ℝ) ^ (k ^ 4) :=
    pow_le_pow_right₀ (by exact_mod_cast hk) hS1
  have hS2_pow : (k : ℝ) ^ S2.card ≤ (d : ℝ) ^ (1 / 4 : ℝ) := by
    have hprod_dvd : (∏ p ∈ S2, p) ∣ d := by
      have h1 : (∏ p ∈ S2, p) ∣ (∏ p ∈ d.primeFactors, p) :=
        Finset.prod_dvd_prod_of_subset S2 d.primeFactors id (Finset.filter_subset _ _)
      exact h1.trans (Nat.prod_primeFactors_dvd d)
    have hprod_le : (∏ p ∈ S2, (p : ℝ)) ≤ (d : ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (by omega) hprod_dvd
    have hk4_le : ((k : ℝ) ^ S2.card) ^ (4 : ℕ) ≤ (d : ℝ) := by
      calc ((k : ℝ) ^ S2.card) ^ (4 : ℕ)
          = ((k : ℝ) ^ (4 : ℕ)) ^ S2.card := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = ∏ _p ∈ S2, (k : ℝ) ^ (4 : ℕ) := by rw [Finset.prod_const]
        _ ≤ ∏ p ∈ S2, (p : ℝ) := by
            apply Finset.prod_le_prod (fun _ _ => by positivity)
            intro p hp
            have hgt : k ^ 4 < p := not_le.mp (Finset.mem_filter.mp hp).2
            exact_mod_cast hgt.le
        _ ≤ (d : ℝ) := hprod_le
    have hnn : 0 ≤ (k : ℝ) ^ S2.card := by positivity
    calc (k : ℝ) ^ S2.card
        = (((k : ℝ) ^ S2.card) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_mul hnn]; norm_num
      _ = (((k : ℝ) ^ S2.card) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
            rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ ≤ (d : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hk4_le (by norm_num)
  rw [hcard, pow_add]
  exact mul_le_mul hS1_pow hS2_pow (by positivity) (by positivity)

lemma sieveAbs_pow_omega_le (k : ℕ) (hk : 1 ≤ k) (β D : ℝ) (hβ : 0 ≤ β) (hD : 1 ≤ D)
    (ps : List ℕ) (hprime : ∀ p ∈ ps, p.Prime) (hdesc : ps.Pairwise (· > ·))
    (hpsD : ∀ p ∈ ps, (p : ℝ) ≤ D) :
    sieveAbs false β D ps (fun d => (k : ℝ) ^ d.primeFactors.card) ≤
      (k : ℝ) ^ (k ^ 4) * D * D ^ (1 / 4 : ℝ) := by
  rw [sieveAbs_eq_sum_sieveSupp false β D ps _ hprime (pairwise_gt_nodup hdesc)]
  have hsub : sieveSupp false β D ps ⊆ Finset.Icc 1 ⌊D⌋₊ := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := mem_sieveSupp_le_D false β D ps hβ hprime hdesc hD (fun _ => hpsD) d hd
    exact Finset.mem_Icc.mpr ⟨hd1, Nat.le_floor hdD⟩
  have hcard : ((sieveSupp false β D ps).card : ℝ) ≤ D := by
    have h1 : (sieveSupp false β D ps).card ≤ ⌊D⌋₊ := by
      calc (sieveSupp false β D ps).card ≤ (Finset.Icc 1 ⌊D⌋₊).card := Finset.card_le_card hsub
        _ = ⌊D⌋₊ := by simp
    exact (by exact_mod_cast h1 : ((sieveSupp false β D ps).card : ℝ) ≤ (⌊D⌋₊ : ℝ)).trans
      (Nat.floor_le (by linarith))
  calc ∑ d ∈ sieveSupp false β D ps, (k : ℝ) ^ d.primeFactors.card
      ≤ ∑ _d ∈ sieveSupp false β D ps, ((k : ℝ) ^ (k ^ 4) * D ^ (1 / 4 : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hd1, hdD⟩ := mem_sieveSupp_le_D false β D ps hβ hprime hdesc hD (fun _ => hpsD) d hd
        exact (pow_omega_le k d hk hd1).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hdD (by norm_num)) (by positivity))
    _ = ((sieveSupp false β D ps).card : ℝ) * ((k : ℝ) ^ (k ^ 4) * D ^ (1 / 4 : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ D * ((k : ℝ) ^ (k ^ 4) * D ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (k : ℝ) ^ (k ^ 4) * D * D ^ (1 / 4 : ℝ) := by ring

lemma count_Ico_modEq (M r : ℕ) (hM : 0 < M) (hr : r < M) :
    ∀ N : ℕ, ((Finset.Ico 0 N).filter (fun n => n % M = r)).card = (N + M - 1 - r) / M := by
  intro N
  induction N with
  | zero =>
    simp only [Finset.Ico_self, Finset.filter_empty, Finset.card_empty]
    symm
    exact Nat.div_eq_of_lt (by omega)
  | succ N ih =>
    have hsplit : Finset.Ico 0 (N + 1) = insert N (Finset.Ico 0 N) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hsplit, Finset.filter_insert]
    have hnot : N ∉ (Finset.Ico 0 N).filter (fun n => n % M = r) := by
      simp
    have ha : N + 1 + M - 1 - r = (N + M - 1 - r) + 1 := by omega
    rw [ha]
    have hNdiv := Nat.div_add_mod N M
    split_ifs with hmod
    · rw [Finset.card_insert_of_notMem hnot, ih]
      have hsucc : (N + M - 1 - r) + 1 = M * (N / M + 1) := by
        rw [Nat.mul_add, mul_one]; omega
      have hpred : N + M - 1 - r = M * (N / M) + (M - 1) := by omega
      rw [hsucc, Nat.mul_div_right _ hM, hpred, Nat.mul_add_div hM,
        Nat.div_eq_of_lt (by omega : M - 1 < M), add_zero]
    · rw [ih]
      have hlt : N % M < M := Nat.mod_lt N hM
      by_cases hcmp : N % M < r
      · have hsucc : (N + M - 1 - r) + 1 = M * (N / M) + (N % M + M - r) := by omega
        have hpred : N + M - 1 - r = M * (N / M) + (N % M + M - 1 - r) := by omega
        rw [hsucc, hpred, Nat.mul_add_div hM, Nat.mul_add_div hM,
          Nat.div_eq_of_lt (by omega : N % M + M - r < M),
          Nat.div_eq_of_lt (by omega : N % M + M - 1 - r < M)]
      · have hgt : r < N % M := by omega
        have hsucc : (N + M - 1 - r) + 1 = M * (N / M + 1) + (N % M - r) := by
          rw [Nat.mul_add, mul_one]; omega
        have hpred : N + M - 1 - r = M * (N / M + 1) + (N % M - 1 - r) := by
          rw [Nat.mul_add, mul_one]; omega
        rw [hsucc, hpred, Nat.mul_add_div hM, Nat.mul_add_div hM,
          Nat.div_eq_of_lt (by omega : N % M - r < M),
          Nat.div_eq_of_lt (by omega : N % M - 1 - r < M)]

lemma card_Ioc_modEq_approx (x M r : ℕ) (hM : 0 < M) :
    |(((Finset.Ioc x (2 * x)).filter (fun n => n ≡ r [MOD M])).card : ℝ) - (x : ℝ) / (M : ℝ)| ≤ 1 := by
  let r' := r % M
  have hr' : r' < M := Nat.mod_lt r hM
  have hfilt : (Finset.Ioc x (2 * x)).filter (fun n => n ≡ r [MOD M]) =
      (Finset.Ico 0 (2 * x + 1)).filter (fun n => n % M = r') \
        (Finset.Ico 0 (x + 1)).filter (fun n => n % M = r') := by
    ext n
    rw [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_Ico, Finset.mem_Ico]
    dsimp only [Nat.ModEq, r']
    constructor
    · rintro ⟨⟨h1, h2⟩, hmod⟩
      exact ⟨⟨⟨Nat.zero_le n, by omega⟩, hmod⟩, fun ⟨⟨_, h3⟩, _⟩ => by omega⟩
    · rintro ⟨⟨⟨_, h2⟩, hmod⟩, hnot⟩
      refine ⟨⟨?_, by omega⟩, hmod⟩
      by_contra hle
      exact hnot ⟨⟨Nat.zero_le n, by omega⟩, hmod⟩
  have hsub : (Finset.Ico 0 (x + 1)).filter (fun n => n % M = r') ⊆
      (Finset.Ico 0 (2 * x + 1)).filter (fun n => n % M = r') := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
    omega
  rw [hfilt, Finset.card_sdiff_of_subset hsub, count_Ico_modEq M r' hM hr' (2 * x + 1),
    count_Ico_modEq M r' hM hr' (x + 1)]
  let u := x + M - r'
  have hu1 : x + 1 + M - 1 - r' = u := by omega
  have hu2 : 2 * x + 1 + M - 1 - r' = u + x := by omega
  rw [hu1, hu2]
  have hle : u / M ≤ (u + x) / M := Nat.div_le_div_right (Nat.le_add_right u x)
  rw [Nat.cast_sub hle]
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : ((u + x) / M : ℕ) * M + (u + x) % M = u + x := by
    linarith [Nat.div_add_mod (u + x) M]
  have h2 : (u / M : ℕ) * M + u % M = u := by
    linarith [Nat.div_add_mod u M]
  have h1r : (((u + x) / M : ℕ) : ℝ) * (M : ℝ) + (((u + x) % M : ℕ) : ℝ) = (u : ℝ) + (x : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h1
    simpa only [Nat.cast_add, Nat.cast_mul] using this
  have h2r : ((u / M : ℕ) : ℝ) * (M : ℝ) + ((u % M : ℕ) : ℝ) = (u : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h2
    simpa only [Nat.cast_add, Nat.cast_mul] using this
  have hdiff : ((((u + x) / M : ℕ) : ℝ) - ((u / M : ℕ) : ℝ) - (x : ℝ) / (M : ℝ)) * (M : ℝ) =
      ((u % M : ℕ) : ℝ) - (((u + x) % M : ℕ) : ℝ) := by
    field_simp
    linarith
  have hrem1 : (0 : ℝ) ≤ ((u % M : ℕ) : ℝ) ∧ ((u % M : ℕ) : ℝ) < (M : ℝ) :=
    ⟨by positivity, by exact_mod_cast Nat.mod_lt u hM⟩
  have hrem2 : (0 : ℝ) ≤ (((u + x) % M : ℕ) : ℝ) ∧ (((u + x) % M : ℕ) : ℝ) < (M : ℝ) :=
    ⟨by positivity, by exact_mod_cast Nat.mod_lt (u + x) hM⟩
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

lemma crt_count_Ioc_list (x Q' γ' k : ℕ) (hQ' : 0 < Q') (hk : 1 ≤ k) (qs : List ℕ)
    (hnd : qs.Nodup) (hq : ∀ p ∈ qs, p.Prime ∧ 2 * k < p ∧ Nat.Coprime Q' p) :
    |(((Finset.Ioc x (2 * x)).filter (fun n => n ≡ γ' [MOD Q'] ∧ ∀ p ∈ qs, n % p < k)).card : ℝ) -
      ((x : ℝ) / (Q' : ℝ)) * (∏ p ∈ qs.toFinset, (k : ℝ) / (p : ℝ))| ≤ (k : ℝ) ^ qs.length := by
  induction qs generalizing Q' γ' with
  | nil =>
    simp only [List.not_mem_nil, IsEmpty.forall_iff, forall_const, and_true, List.toFinset_nil,
      Finset.prod_empty, mul_one, List.length_nil, pow_zero]
    exact card_Ioc_modEq_approx x Q' γ' hQ'
  | cons p rs ih =>
    obtain ⟨hp_not, hrs_nd⟩ := List.nodup_cons.mp hnd
    obtain ⟨hp_prime, hpk, hQ'p⟩ := hq p (List.mem_cons_self ..)
    have hsplit : (Finset.Ioc x (2 * x)).filter (fun n => n ≡ γ' [MOD Q'] ∧ ∀ q ∈ p :: rs, n % q < k) =
        (Finset.range k).biUnion (fun r =>
          (Finset.Ioc x (2 * x)).filter
            (fun n => n ≡ (Nat.chineseRemainder hQ'p γ' r).val [MOD Q' * p] ∧ ∀ q ∈ rs, n % q < k)) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, List.mem_cons,
        forall_eq_or_imp]
      constructor
      · rintro ⟨hnI, hnQ, hnp, hnrs⟩
        refine ⟨n % p, hnp, hnI, ?_, hnrs⟩
        have hcr := (Nat.chineseRemainder hQ'p γ' (n % p)).property
        rw [← Nat.modEq_and_modEq_iff_modEq_mul hQ'p]
        exact ⟨hnQ.trans hcr.1.symm, (Nat.mod_modEq n p).symm.trans hcr.2.symm⟩
      · rintro ⟨r, hrk, hnI, hnQp, hnrs⟩
        have hcr := (Nat.chineseRemainder hQ'p γ' r).property
        rw [← Nat.modEq_and_modEq_iff_modEq_mul hQ'p] at hnQp
        refine ⟨hnI, hnQp.1.trans hcr.1, ?_, hnrs⟩
        have hnp_eq : n % p = r % p := hnQp.2.trans hcr.2
        rw [hnp_eq, Nat.mod_eq_of_lt (by omega : r < p)]
        exact hrk
    have hdisj : Set.PairwiseDisjoint (↑(Finset.range k) : Set ℕ) (fun r =>
        (Finset.Ioc x (2 * x)).filter
          (fun n => n ≡ (Nat.chineseRemainder hQ'p γ' r).val [MOD Q' * p] ∧ ∀ q ∈ rs, n % q < k)) := by
      intro r1 hr1 r2 hr2 hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      have h1 := (Finset.mem_filter.mp hn1).2.1
      have h2 := (Finset.mem_filter.mp hn2).2.1
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hQ'p] at h1 h2
      have hc1 := (Nat.chineseRemainder hQ'p γ' r1).property.2
      have hc2 := (Nat.chineseRemainder hQ'p γ' r2).property.2
      have heq : r1 % p = r2 % p := ((h1.2.trans hc1).symm.trans (h2.2.trans hc2))
      have hr1k : r1 < k := Finset.mem_range.mp hr1
      have hr2k : r2 < k := Finset.mem_range.mp hr2
      rw [Nat.mod_eq_of_lt (by omega : r1 < p), Nat.mod_eq_of_lt (by omega : r2 < p)] at heq
      exact hne heq
    rw [hsplit, Finset.card_biUnion hdisj, Nat.cast_sum]
    have hprod : ∏ q ∈ (p :: rs).toFinset, (k : ℝ) / (q : ℝ) =
        ((k : ℝ) / (p : ℝ)) * ∏ q ∈ rs.toFinset, (k : ℝ) / (q : ℝ) := by
      rw [List.toFinset_cons, Finset.prod_insert (by simpa using hp_not)]
    rw [hprod]
    have hmain : ((x : ℝ) / (Q' : ℝ)) * (((k : ℝ) / (p : ℝ)) * ∏ q ∈ rs.toFinset, (k : ℝ) / (q : ℝ)) =
        ∑ _r ∈ Finset.range k, (((x : ℝ) / ((Q' * p : ℕ) : ℝ)) * ∏ q ∈ rs.toFinset, (k : ℝ) / (q : ℝ)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      have hQ'0 : (Q' : ℝ) ≠ 0 := by positivity
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp_prime.ne_zero
      field_simp
    rw [hmain, ← Finset.sum_sub_distrib]
    calc |∑ r ∈ Finset.range k,
            ((((Finset.Ioc x (2 * x)).filter
              (fun n => n ≡ (Nat.chineseRemainder hQ'p γ' r).val [MOD Q' * p] ∧ ∀ q ∈ rs, n % q < k)).card : ℝ) -
             ((x : ℝ) / ((Q' * p : ℕ) : ℝ)) * ∏ q ∈ rs.toFinset, (k : ℝ) / (q : ℝ))|
        ≤ ∑ r ∈ Finset.range k,
            |(((Finset.Ioc x (2 * x)).filter
              (fun n => n ≡ (Nat.chineseRemainder hQ'p γ' r).val [MOD Q' * p] ∧ ∀ q ∈ rs, n % q < k)).card : ℝ) -
             ((x : ℝ) / ((Q' * p : ℕ) : ℝ)) * ∏ q ∈ rs.toFinset, (k : ℝ) / (q : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Finset.range k, (k : ℝ) ^ rs.length := by
          apply Finset.sum_le_sum
          intro r _
          apply ih (Q' * p) (Nat.chineseRemainder hQ'p γ' r).val (Nat.mul_pos hQ' hp_prime.pos) hrs_nd
          intro q hqrs
          obtain ⟨hq_prime, hqk, hQ'q⟩ := hq q (List.mem_cons_of_mem p hqrs)
          refine ⟨hq_prime, hqk, hQ'q.mul_left ?_⟩
          have hne : p ≠ q := fun heq => hp_not (heq ▸ hqrs)
          exact (Nat.coprime_primes hp_prime hq_prime).mpr hne
      _ = (k : ℝ) ^ (p :: rs).length := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, List.length_cons, pow_succ']

lemma crt_count_Ioc (x Q' γ' k d : ℕ) (hQ' : 0 < Q') (hk : 1 ≤ k)
    (hd : ∀ p ∈ d.primeFactors, p.Prime ∧ 2 * k < p ∧ Nat.Coprime Q' p) :
    |(((Finset.Ioc x (2 * x)).filter (fun n => n ≡ γ' [MOD Q'] ∧ ∀ p ∈ d.primeFactors, n % p < k)).card : ℝ) -
      ((x : ℝ) / (Q' : ℝ)) * multG k d| ≤ (k : ℝ) ^ d.primeFactors.card := by
  let qs := d.primeFactors.toList
  have hnd : qs.Nodup := Finset.nodup_toList _
  have hmem : ∀ p, p ∈ qs ↔ p ∈ d.primeFactors := fun p => Finset.mem_toList
  have hlen : qs.length = d.primeFactors.card := Finset.length_toList _
  have htoF : qs.toFinset = d.primeFactors := by
    ext p; simp [qs]
  have hfilt : (Finset.Ioc x (2 * x)).filter (fun n => n ≡ γ' [MOD Q'] ∧ ∀ p ∈ d.primeFactors, n % p < k) =
      (Finset.Ioc x (2 * x)).filter (fun n => n ≡ γ' [MOD Q'] ∧ ∀ p ∈ qs, n % p < k) := by
    ext n; simp [hmem]
  rw [hfilt, ← hlen, show multG k d = ∏ p ∈ qs.toFinset, (k : ℝ) / (p : ℝ) by rw [htoF]; rfl]
  exact crt_count_Ioc_list x Q' γ' k hQ' hk qs hnd (fun p hp => hd p ((hmem p).mp hp))

/- ### Section 5: Final Assembly -/

lemma sieveSum_finset_sum {α : Type*} (s : Finset α) (sign : Bool) (β D : ℝ) (ps : List ℕ)
    (f : α → ℕ → ℝ) :
    sieveSum sign β D ps (fun d => ∑ a ∈ s, f a d) = ∑ a ∈ s, sieveSum sign β D ps (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact sieveSum_zero sign β D ps
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [sieveSum_add, ih]

lemma pairwise_ge_nodup_gt {ps : List ℕ} (hge : ps.Pairwise (· ≥ ·)) (hnd : ps.Nodup) :
    ps.Pairwise (· > ·) := by
  induction ps with
  | nil => exact List.Pairwise.nil
  | cons p qs ih =>
    obtain ⟨hp_ge, hqs_ge⟩ := List.pairwise_cons.mp hge
    obtain ⟨hp_not, hqs_nd⟩ := List.nodup_cons.mp hnd
    refine List.pairwise_cons.mpr ⟨fun q hq => ?_, ih hqs_ge hqs_nd⟩
    have hne : p ≠ q := fun heq => hp_not (heq ▸ hq)
    have h1 := hp_ge q hq
    omega

lemma prime_dvd_choose_imp_mod_lt {n k p : ℕ} (hkn : k < n) (hp : p.Prime) (hpk : 2 * k < p)
    (hpdvd : p ∣ n.choose k) : n % p < k := by
  have hdvd : p ∣ ∏ i ∈ Finset.range k, (n - i) := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right hpdvd _
  obtain ⟨i, hi, hpi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdvd
  have hik : i < k := Finset.mem_range.mp hi
  have hmod : n % p = i % p := by
    have : n = (n - i) + i := by omega
    conv_lhs => rw [this]
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpi, zero_add, Nat.mod_mod]
  rw [hmod, Nat.mod_eq_of_lt (by omega : i < p)]
  exact hik

lemma three_pow_ge_quad (k : ℕ) (hk : 12 ≤ k) : 800 * k ^ 2 + 20 ≤ 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : 800 * (m + 1) ^ 2 + 20 ≤ 3 * (800 * m ^ 2 + 20) := by nlinarith
    calc 800 * (m + 1) ^ 2 + 20 ≤ 3 * (800 * m ^ 2 + 20) := h1
      _ ≤ 3 * 3 ^ m := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (m + 1) := by ring

lemma log_pow_le_rpow (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 1 ≤ x) :
    (Real.log x) ^ (6 * k) ≤ ((24 * k : ℝ) ^ (6 * k)) * x ^ (1 / 4 : ℝ) := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  let c : ℝ := 24 * (k : ℝ)
  have hc_pos : 0 < c := by positivity
  let t : ℝ := x ^ (1 / c)
  have ht_pos : 0 < t := Real.rpow_pos_of_pos hx_pos _
  have hlogx_le : Real.log x ≤ c * t := by
    have hlogt : Real.log t = (1 / c) * Real.log x := Real.log_rpow hx_pos _
    have hle : Real.log t ≤ t := by linarith [Real.log_le_sub_one_of_pos ht_pos]
    have : Real.log x = c * Real.log t := by
      rw [hlogt]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hle hc_pos.le
  calc (Real.log x) ^ (6 * k) ≤ (c * t) ^ (6 * k) := pow_le_pow_left₀ hlogx_nn hlogx_le _
    _ = c ^ (6 * k) * t ^ (6 * k) := mul_pow c t (6 * k)
    _ = ((24 * k : ℝ) ^ (6 * k)) * x ^ (1 / 4 : ℝ) := by
      congr 1
      dsimp only [t]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
      congr 1
      dsimp only [c]
      push_cast
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      field_simp
      ring

end Erdos387GuyH2

theorem OMA.solution : OMA.R_Erdos387_erdos_387_variants_guy_R1.H2 := by
  classical
  rw [OMA.R_Erdos387_erdos_387_variants_guy_R1.H2]
  refine Filter.eventually_atTop.mpr ⟨12, ?_⟩
  intro k hk γ g ⟨_, _, hcover⟩
  have hk1 : 1 ≤ k := by omega
  let Q : ℕ := ∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1)
  have hQ_pos : 0 < Q := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Nat.mem_primesLE.mp hp).2.pos _
  have hQ_cop : ∀ q : ℕ, q.Prime → 2 * k < q → Nat.Coprime Q q := by
    intro q hq hqk
    apply Nat.Coprime.prod_left
    intro p hp
    obtain ⟨hple, hp_prime⟩ := Nat.mem_primesLE.mp hp
    have hne : p ≠ q := by omega
    exact ((Nat.coprime_primes hp_prime hq).mpr hne).pow_left _
  let w : ℕ := ⌈Real.exp ((1000 : ℝ) * k)⌉₊ + 2 * k + 1
  have hw_gt : 2 * k < w := by omega
  have hlogw : (1000 : ℝ) * k ≤ Real.log (w : ℝ) := by
    have hexp_le : Real.exp ((1000 : ℝ) * k) ≤ (w : ℝ) := by
      have h1 : Real.exp ((1000 : ℝ) * k) ≤ (⌈Real.exp ((1000 : ℝ) * k)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈Real.exp ((1000 : ℝ) * k)⌉₊ : ℝ) ≤ (w : ℝ) := by exact_mod_cast (by omega : ⌈Real.exp ((1000 : ℝ) * k)⌉₊ ≤ w)
      linarith
    calc (1000 : ℝ) * k = Real.log (Real.exp ((1000 : ℝ) * k)) := (Real.log_exp _).symm
      _ ≤ Real.log (w : ℝ) := Real.log_le_log (Real.exp_pos _) hexp_le
  let smallPrimes : Finset ℕ := (Finset.Ioc (2 * k) w).filter Nat.Prime
  let Psmall : ℕ := ∏ p ∈ smallPrimes, p
  have hPsmall_pos : 0 < Psmall :=
    Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
  have hQP_cop : Nat.Coprime Q Psmall := by
    apply Nat.Coprime.prod_right
    intro p hp
    obtain ⟨hI, hp_prime⟩ := Finset.mem_filter.mp hp
    exact hQ_cop p hp_prime (Finset.mem_Ioc.mp hI).1
  let Q' : ℕ := Q * Psmall
  have hQ'_pos : 0 < Q' := Nat.mul_pos hQ_pos hPsmall_pos
  let γ' : ℕ := (Nat.chineseRemainder hQP_cop γ k).val
  have hγ'_Q : γ' ≡ γ [MOD Q] := (Nat.chineseRemainder hQP_cop γ k).property.1
  have hγ'_P : γ' ≡ k [MOD Psmall] := (Nat.chineseRemainder hQP_cop γ k).property.2
  have hQ'_cop : ∀ q : ℕ, q.Prime → w < q → Nat.Coprime Q' q := by
    intro q hq hqw
    apply Nat.Coprime.mul_left
    · exact hQ_cop q hq (by omega)
    · apply Nat.Coprime.prod_left
      intro p hp
      obtain ⟨hI, hp_prime⟩ := Finset.mem_filter.mp hp
      have hple : p ≤ w := (Finset.mem_Ioc.mp hI).2
      exact (Nat.coprime_primes hp_prime hq).mpr (by omega)
  let C_rem : ℝ := 4 * (Q' : ℝ) * (k : ℝ) ^ (k ^ 4) * ((24 * k : ℝ) ^ (6 * k))
  let x0 : ℕ := max (k + 1)
    (max (⌈((w : ℝ) + 1) ^ ((3 : ℝ) ^ k)⌉₊ + 1) (⌈(C_rem + 1) ^ (8 : ℕ)⌉₊ + 2))
  apply Filter.Eventually.frequently
  refine Filter.eventually_atTop.mpr ⟨x0, ?_⟩
  intro x hx
  have hkx : k < x := by
    have : k + 1 ≤ x0 := le_max_left _ _
    omega
  have hx2 : 2 ≤ x := by
    have : ⌈(C_rem + 1) ^ (8 : ℕ)⌉₊ + 2 ≤ x0 := le_trans (le_max_right _ _) (le_max_right _ _)
    omega
  have hx_pos : (0 : ℝ) < x := by positivity
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  let β : ℝ := (400 : ℝ) * (k : ℝ) ^ 2
  let z : ℝ := (x : ℝ) ^ ((3 : ℝ) ^ k)⁻¹
  let D : ℝ := Real.sqrt (x : ℝ)
  have hD_pos : 0 < D := Real.sqrt_pos.mpr hx_pos
  have hD1 : 1 ≤ D := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hz_gt_w : (w : ℝ) < z := by
    have h1 : ((w : ℝ) + 1) ^ ((3 : ℝ) ^ k) ≤ (x : ℝ) := by
      have hle : ⌈((w : ℝ) + 1) ^ ((3 : ℝ) ^ k)⌉₊ ≤ x := by
        have : ⌈((w : ℝ) + 1) ^ ((3 : ℝ) ^ k)⌉₊ + 1 ≤ x0 :=
          le_trans (le_max_left _ _) (le_max_right _ _)
        omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast hle)
    have h3k_pos : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    have h2 : (w : ℝ) + 1 ≤ z := by
      calc (w : ℝ) + 1 = (((w : ℝ) + 1) ^ ((3 : ℝ) ^ k)) ^ ((3 : ℝ) ^ k)⁻¹ := by
            rw [← Real.rpow_mul (by positivity), mul_inv_cancel₀ h3k_pos.ne', Real.rpow_one]
        _ ≤ z := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    linarith
  have hz_le_D : z ≤ D := by
    rw [show D = (x : ℝ) ^ (1 / 2 : ℝ) by dsimp only [D]; rw [Real.sqrt_eq_rpow]]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    have h3k : (2 : ℝ) ≤ (3 : ℝ) ^ k := by
      have : 2 ≤ 3 ^ k := by
        calc 2 ≤ 3 ^ 1 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
      exact_mod_cast this
    rw [one_div]
    exact inv_anti₀ (by norm_num) h3k
  have hz_pos : 0 < z := Real.rpow_pos_of_pos hx_pos _
  have hlogz_eq : Real.log z = ((3 : ℝ) ^ k)⁻¹ * Real.log (x : ℝ) := Real.log_rpow hx_pos _
  have hlogD_eq : Real.log D = (1 / 2 : ℝ) * Real.log (x : ℝ) := by
    rw [show D = (x : ℝ) ^ (1 / 2 : ℝ) by dsimp only [D]; rw [Real.sqrt_eq_rpow], Real.log_rpow hx_pos _]
  have hs_eq : Real.log D / Real.log z = (3 : ℝ) ^ k / 2 := by
    rw [hlogD_eq, hlogz_eq]
    have h3k0 : (3 : ℝ) ^ k ≠ 0 := by positivity
    field_simp [hlogx_pos.ne']
  have hs_ge : β + 10 ≤ Real.log D / Real.log z := by
    rw [hs_eq]
    have hq := Erdos387GuyH2.three_pow_ge_quad k hk
    have hqr : (800 : ℝ) * (k : ℝ) ^ 2 + 20 ≤ (3 : ℝ) ^ k := by exact_mod_cast hq
    dsimp only [β]
    linarith
  let Pfin : Finset ℕ := (Finset.Ico (w + 1) ⌈z⌉₊).filter Nat.Prime
  let ps : List ℕ := Pfin.sort (· ≥ ·)
  have hps_mem : ∀ p, p ∈ ps ↔ p ∈ Pfin := fun p => Finset.mem_sort (· ≥ ·)
  have hps_nd : ps.Nodup := Pfin.sort_nodup (· ≥ ·)
  have hps_desc : ps.Pairwise (· > ·) :=
    Erdos387GuyH2.pairwise_ge_nodup_gt (Finset.pairwise_sort Pfin (· ≥ ·)) hps_nd
  have hps_props : ∀ p ∈ ps, p.Prime ∧ w < p ∧ (p : ℝ) < z := by
    intro p hp
    obtain ⟨hI, hpr⟩ := Finset.mem_filter.mp ((hps_mem p).mp hp)
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hI
    exact ⟨hpr, by omega, Nat.lt_ceil.mp hhi⟩
  have hps_prime : ∀ p ∈ ps, p.Prime := fun p hp => (hps_props p hp).1
  have hps_le_z : ∀ p ∈ ps, (p : ℝ) ≤ z := fun p hp => (hps_props p hp).2.2.le
  have hps_le_D : ∀ p ∈ ps, (p : ℝ) ≤ D := fun p hp => (hps_le_z p hp).trans hz_le_D
  -- Apply Beta-sieve main term lower bound
  have hmain_err := (Erdos387GuyH2.sieve_main_bound k w hk hw_gt hlogw ps.length ps le_rfl hps_desc
    (fun p hp => ⟨(hps_props p hp).1, (hps_props p hp).2.1⟩) z D hD_pos hz_gt_w hps_le_z).2 (by linarith)
  have hphi_le_half : Erdos387GuyH2.phiSieve β (Real.log D / Real.log z) ≤ 1 / 2 := by
    dsimp only [Erdos387GuyH2.phiSieve]
    have hexp_le : Real.exp ((β + 2 - Real.log D / Real.log z) / 2) ≤ Real.exp (-1 : ℝ) :=
      Real.exp_le_exp.mpr (by linarith)
    have he1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith [Real.exp_one_gt_d9]
    exact hexp_le.trans he1
  have hVps_pos : 0 < Erdos387GuyH2.prodV k ps :=
    Erdos387GuyH2.prodV_pos k ps (fun p hp => by have := (hps_props p hp).2.1; omega)
  have hVneg_ge : (1 / 2 : ℝ) * Erdos387GuyH2.prodV k ps ≤
      Erdos387GuyH2.sieveSum false β D ps (Erdos387GuyH2.multG k) := by
    have : Erdos387GuyH2.prodV k ps * Erdos387GuyH2.phiSieve β (Real.log D / Real.log z) ≤
        (1 / 2 : ℝ) * Erdos387GuyH2.prodV k ps := by nlinarith
    linarith
  -- Lower bound on prodV k ps via prodV_ratio_le_real
  have hVps_lb : 1 / (2 * (Real.log (x : ℝ)) ^ (6 * k)) ≤ Erdos387GuyH2.prodV k ps := by
    have hrat := Erdos387GuyH2.prodV_ratio_le_real k w hk1 hw_gt hlogw ps [] hps_nd
      (w : ℝ) z le_rfl hz_gt_w.le
      (fun p hp => ⟨(hps_props p hp).1, by exact_mod_cast (hps_props p hp).2.1, hps_le_z p hp⟩)
      (fun _ h => by cases h)
    simp only [List.append_nil, Erdos387GuyH2.prodV_nil] at hrat
    have hlogw_ge1 : (1 : ℝ) ≤ Real.log (w : ℝ) := by
      have : (12 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hlogz_le_logx : Real.log z ≤ Real.log (x : ℝ) := by
      rw [hlogz_eq]
      have hinv_le : ((3 : ℝ) ^ k)⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        exact_mod_cast Nat.one_le_pow k 3 (by norm_num)
      nlinarith
    have hfrac_le : Real.log z / Real.log (w : ℝ) ≤ Real.log (x : ℝ) := by
      calc Real.log z / Real.log (w : ℝ) ≤ Real.log z / 1 :=
            div_le_div_of_nonneg_left (by rw [hlogz_eq]; positivity) zero_lt_one hlogw_ge1
        _ = Real.log z := div_one _
        _ ≤ Real.log (x : ℝ) := hlogz_le_logx
    have hpow_le : (Real.log z / Real.log (w : ℝ)) ^ (6 * k) ≤ (Real.log (x : ℝ)) ^ (6 * k) :=
      pow_le_pow_left₀ (by rw [hlogz_eq]; positivity) hfrac_le _
    have h1 : (1 : ℝ) ≤ 2 * (Real.log (x : ℝ)) ^ (6 * k) * Erdos387GuyH2.prodV k ps := by
      have h2 : (102 / 100 : ℝ) * (Real.log z / Real.log (w : ℝ)) ^ (6 * k) ≤
          2 * (Real.log (x : ℝ)) ^ (6 * k) := by
        have : 0 ≤ (Real.log (x : ℝ)) ^ (6 * k) := by positivity
        nlinarith
      exact hrat.trans (mul_le_mul_of_nonneg_right h2 hVps_pos.le)
    rw [div_le_iff₀ (by positivity)]
    linarith
  -- Connect sieveSum to sifted count on A'
  let A' : Finset ℕ := (Finset.Ioc x (2 * x)).filter (fun n => n ≡ γ' [MOD Q'])
  let S' : Finset ℕ := A'.filter (fun n => ∀ p ∈ ps, ¬ (n % p < k))
  let ind : ℕ → ℕ → ℝ := fun n d => if ∀ q ∈ d.primeFactors, n % q < k then 1 else 0
  let f : ℕ → ℝ := fun d => ∑ n ∈ A', ind n d
  let R : ℕ → ℝ := fun d => f d - ((x : ℝ) / (Q' : ℝ)) * Erdos387GuyH2.multG k d
  have hS'_ge : Erdos387GuyH2.sieveSum false β D ps f ≤ (S'.card : ℝ) := by
    have hsum_eq : Erdos387GuyH2.sieveSum false β D ps f =
        ∑ n ∈ A', Erdos387GuyH2.sieveSum false β D ps (ind n) :=
      Erdos387GuyH2.sieveSum_finset_sum A' false β D ps ind
    rw [hsum_eq]
    calc ∑ n ∈ A', Erdos387GuyH2.sieveSum false β D ps (ind n)
        ≤ ∑ n ∈ A', (if ∀ p ∈ ps, ¬ (n % p < k) then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro n _
          have hind := (Erdos387GuyH2.sieveSum_indicator β ps (fun q => n % q < k) hps_prime hps_nd).2 D
          calc Erdos387GuyH2.sieveSum false β D ps (ind n)
              = _ := by congr 1; funext d; dsimp only [ind]; split_ifs <;> rfl
            _ ≤ _ := hind
            _ = (if ∀ p ∈ ps, ¬ (n % p < k) then (1 : ℝ) else 0) := by split_ifs <;> rfl
      _ = (S'.card : ℝ) := by
          simp [S', Finset.sum_boole]
  have hf_decomp : f = fun d => ((x : ℝ) / (Q' : ℝ)) * Erdos387GuyH2.multG k d + R d := by
    ext d; dsimp only [R]; ring
  have hdecomp : Erdos387GuyH2.sieveSum false β D ps f =
      ((x : ℝ) / (Q' : ℝ)) * Erdos387GuyH2.sieveSum false β D ps (Erdos387GuyH2.multG k) +
      Erdos387GuyH2.sieveSum false β D ps R := by
    rw [hf_decomp, Erdos387GuyH2.sieveSum_add, Erdos387GuyH2.sieveSum_smul]
  have hR_bound : |Erdos387GuyH2.sieveSum false β D ps R| ≤
      (k : ℝ) ^ (k ^ 4) * D * D ^ (1 / 4 : ℝ) := by
    have h1 := Erdos387GuyH2.abs_sieveSum_le false β D ps R
    rw [Erdos387GuyH2.sieveAbs_eq_sum_sieveSupp false β D ps _ hps_prime hps_nd] at h1
    have h2 : ∑ d ∈ Erdos387GuyH2.sieveSupp false β D ps, |R d| ≤
        ∑ d ∈ Erdos387GuyH2.sieveSupp false β D ps, (k : ℝ) ^ d.primeFactors.card := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨_, hd_pf⟩ := Erdos387GuyH2.mem_sieveSupp_props false β D ps hps_prime d hd
      have hf_eq : f d = (((Finset.Ioc x (2 * x)).filter
          (fun n => n ≡ γ' [MOD Q'] ∧ ∀ p ∈ d.primeFactors, n % p < k)).card : ℝ) := by
        dsimp only [f, ind, A']
        rw [Finset.sum_boole, Finset.filter_filter]
      dsimp only [R]
      rw [hf_eq]
      apply Erdos387GuyH2.crt_count_Ioc x Q' γ' k d hQ'_pos hk1
      intro p hp
      obtain ⟨hp_prime, hpw, _⟩ := hps_props p (hd_pf p hp)
      exact ⟨hp_prime, by omega, hQ'_cop p hp_prime hpw⟩
    rw [← Erdos387GuyH2.sieveAbs_eq_sum_sieveSupp false β D ps
        (fun d => (k : ℝ) ^ d.primeFactors.card) hps_prime hps_nd] at h2
    exact (h1.trans h2).trans
      (Erdos387GuyH2.sieveAbs_pow_omega_le k hk1 β D (by positivity) hD1 ps hps_prime hps_desc hps_le_D)
  -- Show main term > remainder term
  have hmain_gt_rem : (k : ℝ) ^ (k ^ 4) * D * D ^ (1 / 4 : ℝ) <
      ((x : ℝ) / (Q' : ℝ)) * ((1 / 2 : ℝ) * (1 / (2 * (Real.log (x : ℝ)) ^ (6 * k)))) := by
    have hD_rpow : D * D ^ (1 / 4 : ℝ) = (x : ℝ) ^ (5 / 8 : ℝ) := by
      rw [show D = (x : ℝ) ^ (1 / 2 : ℝ) by dsimp only [D]; rw [Real.sqrt_eq_rpow],
        ← Real.rpow_mul hx_pos.le, ← Real.rpow_add hx_pos]
      congr 1; norm_num
    rw [mul_assoc, hD_rpow]
    have hC_lt : C_rem < (x : ℝ) ^ (1 / 8 : ℝ) := by
      have hle : ⌈(C_rem + 1) ^ (8 : ℕ)⌉₊ ≤ x := by
        have : ⌈(C_rem + 1) ^ (8 : ℕ)⌉₊ + 2 ≤ x0 := le_trans (le_max_right _ _) (le_max_right _ _)
        omega
      have hpow : (C_rem + 1) ^ (8 : ℕ) ≤ (x : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hle)
      have hC_nn : 0 ≤ C_rem := by positivity
      have h1 : C_rem + 1 ≤ (x : ℝ) ^ (1 / 8 : ℝ) := by
        calc C_rem + 1 = ((C_rem + 1) ^ (8 : ℝ)) ^ (1 / 8 : ℝ) := by
              rw [← Real.rpow_mul (by linarith)]; norm_num
          _ = ((C_rem + 1) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) := by
              rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          _ ≤ (x : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (by positivity) hpow (by norm_num)
      linarith
    have hlog_bd := Erdos387GuyH2.log_pow_le_rpow k hk1 (x : ℝ) hx1
    have hprod_lt : 4 * (Q' : ℝ) * (k : ℝ) ^ (k ^ 4) * (Real.log (x : ℝ)) ^ (6 * k) * (x : ℝ) ^ (5 / 8 : ℝ) <
        (x : ℝ) := by
      have h1 : 4 * (Q' : ℝ) * (k : ℝ) ^ (k ^ 4) * (Real.log (x : ℝ)) ^ (6 * k) * (x : ℝ) ^ (5 / 8 : ℝ) ≤
          C_rem * (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (5 / 8 : ℝ) := by
        have hrew : C_rem * (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (5 / 8 : ℝ) =
            (4 * (Q' : ℝ) * (k : ℝ) ^ (k ^ 4)) * (((24 * k : ℝ) ^ (6 * k)) * (x : ℝ) ^ (1 / 4 : ℝ)) *
              (x : ℝ) ^ (5 / 8 : ℝ) := by dsimp only [C_rem]; ring
        rw [hrew]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_bd (by positivity)) (by positivity)
      have h2 : C_rem * (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (5 / 8 : ℝ) <
          (x : ℝ) ^ (1 / 8 : ℝ) * (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (5 / 8 : ℝ) := by
        apply mul_lt_mul_of_pos_right
        apply mul_lt_mul_of_pos_right hC_lt (by positivity)
        positivity
      have h3 : (x : ℝ) ^ (1 / 8 : ℝ) * (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (5 / 8 : ℝ) = (x : ℝ) := by
        rw [← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos]
        norm_num
      linarith
    have hden_pos : 0 < 4 * (Q' : ℝ) * (Real.log (x : ℝ)) ^ (6 * k) := by positivity
    rw [show ((x : ℝ) / (Q' : ℝ)) * ((1 / 2 : ℝ) * (1 / (2 * (Real.log (x : ℝ)) ^ (6 * k)))) =
        (x : ℝ) / (4 * (Q' : ℝ) * (Real.log (x : ℝ)) ^ (6 * k)) by ring]
    rw [lt_div_iff₀ hden_pos]
    linarith
  have hS'_pos : (0 : ℝ) < (S'.card : ℝ) := by
    have hmain_lb : ((x : ℝ) / (Q' : ℝ)) * ((1 / 2 : ℝ) * (1 / (2 * (Real.log (x : ℝ)) ^ (6 * k)))) ≤
        ((x : ℝ) / (Q' : ℝ)) * Erdos387GuyH2.sieveSum false β D ps (Erdos387GuyH2.multG k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (mul_le_mul_of_nonneg_left hVps_lb (by norm_num)).trans hVneg_ge
    have hR_neg : -((k : ℝ) ^ (k ^ 4) * D * D ^ (1 / 4 : ℝ)) ≤ Erdos387GuyH2.sieveSum false β D ps R :=
      (abs_le.mp hR_bound).1
    linarith
  have hS'_ne : S'.Nonempty := Finset.card_pos.mp (by exact_mod_cast hS'_pos)
  obtain ⟨n, hn⟩ := hS'_ne
  obtain ⟨hnA', hnps⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnI, hnQ'⟩ := Finset.mem_filter.mp hnA'
  refine ⟨n, Finset.mem_filter.mpr ⟨hnI, ?_, ?_⟩⟩
  · have hQQ' : Q ∣ Q' := dvd_mul_right Q Psmall
    exact (hnQ'.of_dvd hQQ').trans hγ'_Q
  · intro p hp hpdvd
    have hkn : k < n := lt_trans hkx (Finset.mem_Ioc.mp hnI).1
    have hnQ : n ≡ γ [MOD Q] := (hnQ'.of_dvd (dvd_mul_right Q Psmall)).trans hγ'_Q
    by_contra hlt
    push Not at hlt
    by_cases hp2k : p ≤ 2 * k
    · exact (hcover n hkn hnQ).2 p hp hp2k hpdvd
    · have hmod_lt : n % p < k := Erdos387GuyH2.prime_dvd_choose_imp_mod_lt hkn hp (by omega) hpdvd
      by_cases hpw : p ≤ w
      · have hp_small : p ∈ smallPrimes :=
          Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hpw⟩, hp⟩
        have hp_dvd_P : p ∣ Psmall := Finset.dvd_prod_of_mem _ hp_small
        have hp_dvd_Q' : p ∣ Q' := dvd_mul_of_dvd_right hp_dvd_P Q
        have hnp : n ≡ k [MOD p] := (hnQ'.of_dvd hp_dvd_Q').trans (hγ'_P.of_dvd hp_dvd_P)
        have hnp_eq : n % p = k := by
          change n % p = k % p at hnp
          rw [hnp, Nat.mod_eq_of_lt (by omega : k < p)]
        omega
      · have hp_mem : p ∈ ps := by
          rw [hps_mem]
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, Nat.lt_ceil.mpr hlt⟩, hp⟩
        exact hnps p hp_mem hmod_lt
