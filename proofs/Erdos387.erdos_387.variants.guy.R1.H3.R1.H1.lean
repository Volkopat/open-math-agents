import OMAReductions.R_Erdos387_erdos_387_variants_guy_R1_H3_R1


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


/-!
Elementary Selberg upper-bound sieve for `R`-rough integers in `(A, B]`:
  `#{b ∈ (A, B] : ∀ p prime, p ≤ R → ¬ p ∣ b} ≤ (B - A) / log(R + 1) + R ^ 4`.
Also includes the rough-integer reciprocal-sum bound via Euler product.
-/

namespace E387Selberg

open Finset Real
open scoped Classical

/-- Radical of a positive integer: product of its distinct prime factors. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma harmonic_ge_log (R : ℕ) :
    Real.log ((R : ℝ) + 1) ≤ ∑ n ∈ Finset.Icc 1 R, (1 : ℝ) / (n : ℝ) := by
  induction R with
  | zero => simp
  | succ R ih =>
    have hIcc : Finset.Icc 1 (R + 1) = insert (R + 1) (Finset.Icc 1 R) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    have hR1 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
    have hR2 : (0 : ℝ) < (R : ℝ) + 2 := by positivity
    have hstep : Real.log ((R : ℝ) + 2) - Real.log ((R : ℝ) + 1) ≤ 1 / ((R : ℝ) + 1) := by
      rw [← Real.log_div hR2.ne' hR1.ne']
      have h := Real.log_le_sub_one_of_pos (div_pos hR2 hR1)
      have heq : ((R : ℝ) + 2) / ((R : ℝ) + 1) - 1 = 1 / ((R : ℝ) + 1) := by field_simp; ring
      linarith
    push_cast
    rw [show (R : ℝ) + 1 + 1 = (R : ℝ) + 2 by ring]
    linarith

lemma prod_primes_squarefree {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) :=
      Nat.Coprime.prod_right fun q hq =>
        (Nat.coprime_primes hp (hs' q hq)).mpr (fun heq => hps (heq ▸ hq))
    exact Nat.squarefree_mul_iff.mpr ⟨hcop, hp.squarefree, ih hs'⟩

lemma rad_squarefree (n : ℕ) : Squarefree (rad n) :=
  prod_primes_squarefree fun _p hp => Nat.prime_of_mem_primeFactors hp

lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _p hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma rad_le (n : ℕ) (hn : 1 ≤ n) : rad n ≤ n :=
  Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)

lemma totient_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps, Finset.prod_insert hps]
    have hp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) :=
      Nat.Coprime.prod_right fun q hq =>
        (Nat.coprime_primes hp (hs' q hq)).mpr (fun heq => hps (heq ▸ hq))
    rw [Nat.totient_mul hcop, Nat.totient_prime hp, ih hs']

lemma primeFactors_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).primeFactors = s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hprod_ne : ∏ q ∈ s, q ≠ 0 := (Finset.prod_pos fun q hq => (hs' q hq).pos).ne'
    rw [Nat.primeFactors_mul hp.ne_zero hprod_ne, hp.primeFactors, ih hs', Finset.singleton_union]

lemma totient_of_squarefree {m : ℕ} (hm : Squarefree m) (_hm0 : 0 < m) :
    (Nat.totient m : ℝ) = ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
  have heq : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hm
  conv_lhs => rw [← heq]
  rw [totient_prod_primes (fun _p hp => Nat.prime_of_mem_primeFactors hp), Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  rw [Nat.cast_sub (by omega), Nat.cast_one]

lemma geom_sum_inv_prime_le (p R : ℕ) (hp : p.Prime) :
    ∑ e ∈ Finset.Icc 1 R, (1 : ℝ) / ((p : ℝ) ^ e) ≤ (1 : ℝ) / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h2 : ∑ e ∈ Finset.Icc 1 R, (1 : ℝ) / ((p : ℝ) ^ e) =
      (1 / (p : ℝ)) * ∑ j ∈ Finset.range R, ((1 : ℝ) / (p : ℝ)) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun e _ => e - 1) ?_ ?_ ?_ ?_
    · intro e he; simp only [Finset.mem_Icc] at he; simp only [Finset.mem_range]; omega
    · intro e1 he1 e2 he2 h; simp only [Finset.mem_Icc] at he1 he2; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      exact ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro e he; simp only [Finset.mem_Icc] at he
      rw [one_div_pow, one_div_mul_one_div, ← pow_succ', show e - 1 + 1 = e by omega]
  rw [h2, geom_sum_eq (ne_of_lt h1)]
  have hpow_nn : (0 : ℝ) ≤ ((1 : ℝ) / (p : ℝ)) ^ R := by positivity
  have hden_pos : (0 : ℝ) < 1 - 1 / (p : ℝ) := by linarith
  have hnum : ((1 : ℝ) / (p : ℝ)) ^ R - 1 ≤ 0 := by
    have : ((1 : ℝ) / (p : ℝ)) ^ R ≤ 1 ^ R := pow_le_pow_left₀ (by positivity) h1.le R
    simpa using this
  have hle : (((1 : ℝ) / (p : ℝ)) ^ R - 1) / ((1 : ℝ) / (p : ℝ) - 1) ≤ 1 / (1 - 1 / (p : ℝ)) := by
    rw [show (((1 : ℝ) / (p : ℝ)) ^ R - 1) / ((1 : ℝ) / (p : ℝ) - 1) =
        (1 - ((1 : ℝ) / (p : ℝ)) ^ R) / (1 - 1 / (p : ℝ)) by rw [← neg_div_neg_eq, neg_sub, neg_sub]]
    exact div_le_div_of_nonneg_right (by linarith) hden_pos.le
  calc (1 / (p : ℝ)) * ((((1 : ℝ) / (p : ℝ)) ^ R - 1) / ((1 : ℝ) / (p : ℝ) - 1))
      ≤ (1 / (p : ℝ)) * (1 / (1 - 1 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 / ((p : ℝ) - 1) := by field_simp

lemma sum_inv_primeFactors_eq_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (R : ℕ) :
    ∑ n ∈ (Finset.Icc 1 R).filter (fun n => n.primeFactors = P), (1 : ℝ) / (n : ℝ) ≤
      ∏ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := by
  classical
  induction P using Finset.induction_on generalizing R with
  | empty =>
    rw [Finset.prod_empty]
    have hsub : (Finset.Icc 1 R).filter (fun n => n.primeFactors = ∅) ⊆ {1} := by
      intro n hn
      obtain ⟨hnI, hpf⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hnI
      rw [Finset.mem_singleton]
      by_contra hne
      have hgt1 : 1 < n := by omega
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
      rw [hpf] at hmem
      exact Finset.notMem_empty p hmem
    calc ∑ n ∈ (Finset.Icc 1 R).filter (fun n => n.primeFactors = ∅), (1 : ℝ) / (n : ℝ)
        ≤ ∑ n ∈ ({1} : Finset ℕ), (1 : ℝ) / (n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | @insert p s hps ih =>
    have hp : p.Prime := hP p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps]
    set A := (Finset.Icc 1 R).filter (fun n => n.primeFactors = insert p s)
    set B := (Finset.Icc 1 R).filter (fun n => n.primeFactors = s)
    set img := (Finset.Icc 1 R ×ˢ B).image (fun pair : ℕ × ℕ => p ^ pair.1 * pair.2)
    have hA_sub : A ⊆ img := by
      intro n hn
      obtain ⟨hnI, hpf⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnR⟩ := Finset.mem_Icc.mp hnI
      set e := n.factorization p
      have hp_mem : p ∈ n.primeFactors := by rw [hpf]; exact Finset.mem_insert_self p s
      have he_pos : 1 ≤ e := by
        have := Nat.Prime.dvd_iff_one_le_factorization hp (by omega : n ≠ 0)
        exact this.mp (Nat.dvd_of_mem_primeFactors hp_mem)
      have hpe_dvd : p ^ e ∣ n := Nat.ordProj_dvd n p
      set m := n / p ^ e
      have hmul : p ^ e * m = n := Nat.mul_div_cancel' hpe_dvd
      have hpe_le : p ^ e ≤ n := Nat.le_of_dvd (by omega) hpe_dvd
      have he_le : e ≤ R := by
        have hlt : e < 2 ^ e := Nat.lt_two_pow_self
        have h2p : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
        omega
      have hm_pos : 1 ≤ m := Nat.div_pos hpe_le (pow_pos hp.pos e)
      have hm_le : m ≤ R := by
        have : m ≤ p ^ e * m := Nat.le_mul_of_pos_left m (pow_pos hp.pos e)
        omega
      have hcop : ¬ p ∣ m := by
        intro hpm
        have h1 : p ^ (e + 1) ∣ n := by
          rw [← hmul, pow_succ]
          exact mul_dvd_mul_left (p ^ e) hpm
        have h2 := (hp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mp h1
        omega
      have hm_pf : m.primeFactors = s := by
        ext q
        constructor
        · intro hq
          have hqn : q ∈ n.primeFactors := by
            rw [← hmul, Nat.primeFactors_mul (pow_pos hp.pos e).ne' (by omega)]
            exact Finset.mem_union_right _ hq
          rw [hpf, Finset.mem_insert] at hqn
          rcases hqn with rfl | hqs
          · exact absurd (Nat.dvd_of_mem_primeFactors hq) hcop
          · exact hqs
        · intro hqs
          have hq_ne : q ≠ p := fun heq => hps (heq ▸ hqs)
          have hqn : q ∈ n.primeFactors := by rw [hpf]; exact Finset.mem_insert_of_mem hqs
          have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqn
          have hqdvd : q ∣ p ^ e * m := hmul.symm ▸ Nat.dvd_of_mem_primeFactors hqn
          have hq_not_pe : ¬ q ∣ p ^ e := fun h =>
            hq_ne ((Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow h))
          have hqm : q ∣ m := (hqp.dvd_mul.mp hqdvd).resolve_left hq_not_pe
          exact Nat.mem_primeFactors.mpr ⟨hqp, hqm, by omega⟩
      exact Finset.mem_image.mpr ⟨(e, m),
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨he_pos, he_le⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩, hm_pf⟩⟩,
        hmul⟩
    calc ∑ n ∈ A, (1 : ℝ) / (n : ℝ)
        ≤ ∑ n ∈ img, (1 : ℝ) / (n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hA_sub (fun _ _ _ => by positivity)
      _ ≤ ∑ pair ∈ Finset.Icc 1 R ×ˢ B, (1 : ℝ) / ((p ^ pair.1 * pair.2 : ℕ) : ℝ) :=
          Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
      _ = (∑ e ∈ Finset.Icc 1 R, (1 : ℝ) / ((p : ℝ) ^ e)) * (∑ m ∈ B, (1 : ℝ) / (m : ℝ)) := by
          rw [Finset.sum_product, Finset.sum_mul]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          push_cast; ring
      _ ≤ ((1 : ℝ) / ((p : ℝ) - 1)) * ∏ q ∈ s, (1 : ℝ) / ((q : ℝ) - 1) :=
          mul_le_mul (geom_sum_inv_prime_le p R hp) (ih hs R)
            (Finset.sum_nonneg fun _ _ => by positivity)
            (by
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
              have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              positivity)

lemma selberg_G_ge_log (R : ℕ) :
    Real.log ((R : ℝ) + 1) ≤
      ∑ m ∈ (Finset.Icc 1 R).filter Squarefree, (1 : ℝ) / (Nat.totient m : ℝ) := by
  classical
  have hmaps : ∀ n ∈ Finset.Icc 1 R, rad n ∈ (Finset.Icc 1 R).filter Squarefree := fun n hn => by
    obtain ⟨hn1, hnR⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨rad_pos n, (rad_le n hn1).trans hnR⟩,
      rad_squarefree n⟩
  have hpart : ∑ n ∈ Finset.Icc 1 R, (1 : ℝ) / (n : ℝ) =
      ∑ m ∈ (Finset.Icc 1 R).filter Squarefree,
        ∑ n ∈ (Finset.Icc 1 R).filter (fun n => rad n = m), (1 : ℝ) / (n : ℝ) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  refine (harmonic_ge_log R).trans (hpart.le.trans (Finset.sum_le_sum fun m hm => ?_))
  obtain ⟨hmI, hmsf⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hmI
  have hfib : (Finset.Icc 1 R).filter (fun n => rad n = m) =
      (Finset.Icc 1 R).filter (fun n => n.primeFactors = m.primeFactors) := by
    ext n
    simp only [Finset.mem_filter]
    refine and_congr_right fun hnI => ?_
    constructor
    · intro hrad
      rw [← hrad]
      exact (primeFactors_prod_primes fun p hp => Nat.prime_of_mem_primeFactors hp).symm
    · intro hpf
      unfold rad
      rw [hpf, Nat.prod_primeFactors_of_squarefree hmsf]
  rw [hfib, totient_of_squarefree hmsf (by omega), one_div, ← Finset.prod_inv_distrib]
  simpa only [one_div] using sum_inv_primeFactors_eq_le m.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) R

lemma card_Ioc_dvd_approx (A B L : ℕ) (hAB : A ≤ B) (hL : 0 < L) :
    |(((Finset.Ioc A B).filter (fun b => L ∣ b)).card : ℝ) - ((B - A : ℕ) : ℝ) / (L : ℝ)| ≤ 1 := by
  have hcard : ((Finset.Ioc A B).filter (fun b => L ∣ b)).card = B / L - A / L := by
    have h1 : ∀ N : ℕ, ((Finset.Icc 1 N).filter (fun b => L ∣ b)).card = N / L := by
      intro N
      have heq : (Finset.Icc 1 N).filter (fun b => L ∣ b) =
          (Finset.Icc 1 (N / L)).image (fun k => L * k) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hb1, hbN⟩, k, rfl⟩
          refine ⟨k, ⟨?_, ?_⟩, rfl⟩
          · by_contra h0
            have hk0 : k = 0 := by omega
            subst hk0
            omega
          · exact (Nat.le_div_iff_mul_le hL).mpr (by rw [mul_comm]; exact hbN)
        · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
          refine ⟨⟨Nat.mul_pos hL hk1, ?_⟩, k, rfl⟩
          calc L * k ≤ L * (N / L) := Nat.mul_le_mul_left L hkN
            _ ≤ N := Nat.mul_div_le N L
      rw [heq, Finset.card_image_of_injective _ (fun x y h => Nat.eq_of_mul_eq_mul_left hL h),
        Nat.card_Icc]
      simp
    have hsdiff : (Finset.Ioc A B).filter (fun b => L ∣ b) =
        (Finset.Icc 1 B).filter (fun b => L ∣ b) \ (Finset.Icc 1 A).filter (fun b => L ∣ b) := by
      ext b; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc]; omega
    have hsub : (Finset.Icc 1 A).filter (fun b => L ∣ b) ⊆
        (Finset.Icc 1 B).filter (fun b => L ∣ b) := by
      intro b hb; simp only [Finset.mem_filter, Finset.mem_Icc] at hb ⊢; omega
    rw [hsdiff, Finset.card_sdiff_of_subset hsub, h1 B, h1 A]
  rw [hcard, Nat.cast_sub (Nat.div_le_div_right hAB)]
  have hB := Nat.div_add_mod B L
  have hA := Nat.div_add_mod A L
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hBr : ((L : ℝ) * ((B / L : ℕ) : ℝ)) + ((B % L : ℕ) : ℝ) = (B : ℝ) := by exact_mod_cast hB
  have hAr : ((L : ℝ) * ((A / L : ℕ) : ℝ)) + ((A % L : ℕ) : ℝ) = (A : ℝ) := by exact_mod_cast hA
  have hBA : ((B - A : ℕ) : ℝ) = (B : ℝ) - (A : ℝ) := Nat.cast_sub hAB
  have hdiff : ((((B / L : ℕ) : ℝ) - ((A / L : ℕ) : ℝ)) - ((B - A : ℕ) : ℝ) / (L : ℝ)) * (L : ℝ) =
      ((A % L : ℕ) : ℝ) - ((B % L : ℕ) : ℝ) := by
    rw [hBA]; field_simp; linarith
  have hrA : (0 : ℝ) ≤ ((A % L : ℕ) : ℝ) ∧ ((A % L : ℕ) : ℝ) < (L : ℝ) :=
    ⟨by positivity, by exact_mod_cast Nat.mod_lt A hL⟩
  have hrB : (0 : ℝ) ≤ ((B % L : ℕ) : ℝ) ∧ ((B % L : ℕ) : ℝ) < (L : ℝ) :=
    ⟨by positivity, by exact_mod_cast Nat.mod_lt B hL⟩
  rw [abs_le]; constructor <;> nlinarith

/-- Elementary Selberg upper-bound sieve: the count of `R`-rough integers in `(A, B]`
is at most `(B - A) / log(R + 1) + R ^ 4`. -/
theorem selberg_rough_Ioc_le (A B R : ℕ) (hAB : A ≤ B) (hR : 1 ≤ R) :
    (((Finset.Ioc A B).filter (fun b => ∀ p : ℕ, p.Prime → p ≤ R → ¬ p ∣ b)).card : ℝ) ≤
      ((B - A : ℕ) : ℝ) / Real.log ((R : ℝ) + 1) + (R : ℝ) ^ 4 := by
  classical
  set S := (Finset.Icc 1 R).filter Squarefree
  set G : ℝ := ∑ m ∈ S, (1 : ℝ) / (Nat.totient m : ℝ)
  have h1S : 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hR⟩, squarefree_one⟩
  have hG_ge_log : Real.log ((R : ℝ) + 1) ≤ G := selberg_G_ge_log R
  have hlog_pos : 0 < Real.log ((R : ℝ) + 1) :=
    Real.log_pos (by
      have : (1 : ℝ) ≤ R := by exact_mod_cast hR
      linarith)
  have hG_pos : 0 < G := lt_of_lt_of_le hlog_pos hG_ge_log
  let y : ℕ → ℝ := fun m => (ArithmeticFunction.moebius m : ℝ) / ((Nat.totient m : ℝ) * G)
  let c : ℕ → ℝ := fun d =>
    (d : ℝ) * ∑ m ∈ S.filter (fun m => d ∣ m), (ArithmeticFunction.moebius (m / d) : ℝ) * y m
  -- Core Möbius inversion: for every r ∈ S, ∑_{d ∈ S, r ∣ d} c d / d = y r
  have hinv : ∀ r ∈ S, ∑ d ∈ S.filter (fun d => r ∣ d), c d / (d : ℝ) = y r := by
    intro r hr
    have hstep1 : ∑ d ∈ S.filter (fun d => r ∣ d), c d / (d : ℝ) =
        ∑ d ∈ S.filter (fun d => r ∣ d),
          ∑ m ∈ S.filter (fun m => d ∣ m), (ArithmeticFunction.moebius (m / d) : ℝ) * y m := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd0 : (d : ℝ) ≠ 0 := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1).1
        positivity
      dsimp only [c]; field_simp
    rw [hstep1]
    have hswap :
        ∑ d ∈ S.filter (fun d => r ∣ d),
          ∑ m ∈ S.filter (fun m => d ∣ m), (ArithmeticFunction.moebius (m / d) : ℝ) * y m =
        ∑ m ∈ S.filter (fun m => r ∣ m),
          y m * ∑ d ∈ S.filter (fun d => r ∣ d ∧ d ∣ m),
            (ArithmeticFunction.moebius (m / d) : ℝ) := by
      calc ∑ d ∈ S.filter (fun d => r ∣ d),
            ∑ m ∈ S.filter (fun m => d ∣ m), (ArithmeticFunction.moebius (m / d) : ℝ) * y m
          = ∑ d ∈ S.filter (fun d => r ∣ d), ∑ m ∈ S,
              if d ∣ m then (ArithmeticFunction.moebius (m / d) : ℝ) * y m else 0 := by
            refine Finset.sum_congr rfl fun d _ => ?_; rw [Finset.sum_filter]
        _ = ∑ m ∈ S, ∑ d ∈ S.filter (fun d => r ∣ d),
              if d ∣ m then (ArithmeticFunction.moebius (m / d) : ℝ) * y m else 0 :=
            Finset.sum_comm
        _ = ∑ m ∈ S, if r ∣ m then
              y m * ∑ d ∈ S.filter (fun d => r ∣ d ∧ d ∣ m),
                (ArithmeticFunction.moebius (m / d) : ℝ) else 0 := by
            refine Finset.sum_congr rfl fun m _ => ?_
            by_cases hrm : r ∣ m
            · rw [if_pos hrm, Finset.mul_sum, ← Finset.sum_filter]
              have heq : (S.filter (fun d => r ∣ d)).filter (fun d => d ∣ m) =
                  S.filter (fun d => r ∣ d ∧ d ∣ m) := by
                ext d; simp only [Finset.mem_filter]; tauto
              rw [heq]
              refine Finset.sum_congr rfl fun d _ => mul_comm _ _
            · rw [if_neg hrm]
              refine Finset.sum_eq_zero fun d hd => ?_
              have hrd := (Finset.mem_filter.mp hd).2
              exact if_neg (fun hdm => hrm (hrd.trans hdm))
        _ = _ := by rw [← Finset.sum_filter]
    rw [hswap]
    have hinner : ∀ m ∈ S.filter (fun m => r ∣ m),
        ∑ d ∈ S.filter (fun d => r ∣ d ∧ d ∣ m), (ArithmeticFunction.moebius (m / d) : ℝ) =
          if m = r then 1 else 0 := by
      intro m hm
      obtain ⟨hmS, hrm⟩ := Finset.mem_filter.mp hm
      obtain ⟨hmI, hmsf⟩ := Finset.mem_filter.mp hmS
      have hm1 := (Finset.mem_Icc.mp hmI).1
      have hmR := (Finset.mem_Icc.mp hmI).2
      have hr1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
      have hbij : ∑ d ∈ S.filter (fun d => r ∣ d ∧ d ∣ m), (ArithmeticFunction.moebius (m / d) : ℝ) =
          ∑ k ∈ (m / r).divisors, (ArithmeticFunction.moebius k : ℝ) := by
        refine Finset.sum_bij (fun d _ => m / d) ?_ ?_ ?_ ?_
        · intro d hd
          obtain ⟨_, hrd, hdm⟩ := Finset.mem_filter.mp hd
          refine Nat.mem_divisors.mpr ⟨?_, (Nat.div_pos (Nat.le_of_dvd (by omega) hrm) (by omega)).ne'⟩
          obtain ⟨a, rfl⟩ := hrd
          obtain ⟨b, hb⟩ := hdm
          have hrapos : 0 < r * a := by
            by_contra h0
            have hza : r * a = 0 := by omega
            rw [hza, zero_mul] at hb
            omega
          have hdiv1 : m / (r * a) = b := by rw [hb, Nat.mul_div_cancel_left b hrapos]
          have hdiv2 : m / r = a * b := by
            rw [hb, mul_assoc, Nat.mul_div_cancel_left (a * b) (by omega : 0 < r)]
          rw [hdiv1, hdiv2]
          exact dvd_mul_left b a
        · intro d1 hd1 d2 hd2 heq
          have hd1m := (Finset.mem_filter.mp hd1).2.2
          have hd2m := (Finset.mem_filter.mp hd2).2.2
          have h1 := Nat.mul_div_cancel' hd1m
          have h2 := Nat.mul_div_cancel' hd2m
          have hqpos : 0 < m / d1 := Nat.div_pos (Nat.le_of_dvd (by omega) hd1m)
            (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd1).1).1).1
          rw [← heq] at h2
          exact Nat.eq_of_mul_eq_mul_right hqpos (h1.trans h2.symm)
        · intro k hk
          obtain ⟨hkdvd, _⟩ := Nat.mem_divisors.mp hk
          have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hkdvd
            (Nat.div_pos (Nat.le_of_dvd (by omega) hrm) (by omega))
          have hkm : k ∣ m := hkdvd.trans (Nat.div_dvd_of_dvd hrm)
          refine ⟨m / k, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
          · exact Nat.div_pos (Nat.le_of_dvd (by omega) hkm) hkpos
          · exact (Nat.div_le_self m k).trans hmR
          · exact hmsf.squarefree_of_dvd (Nat.div_dvd_of_dvd hkm)
          · obtain ⟨q, hq⟩ := hkdvd
            have hmq : m = r * (k * q) := by
              have := Nat.mul_div_cancel' hrm; rw [hq] at this; exact this.symm
            rw [hmq, show r * (k * q) = k * (r * q) by ring, Nat.mul_div_cancel_left _ hkpos]
            exact dvd_mul_right r q
          · exact Nat.div_dvd_of_dvd hkm
          · exact Nat.div_div_self hkm (by omega)
        · intro _ _; rfl
      rw [hbij]
      have hmoeb : (∑ k ∈ (m / r).divisors, ArithmeticFunction.moebius k : ℤ) =
          if m / r = 1 then 1 else 0 := by
        have h := ArithmeticFunction.moebius_mul_coe_zeta
        have hval := congrArg (fun f => f (m / r)) h
        simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply,
          ArithmeticFunction.zeta_apply, ArithmeticFunction.one_apply] at hval
        have hpos : m / r ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hrm) (by omega)).ne'
        have hsum : ∑ x ∈ (m / r).divisorsAntidiagonal,
            ArithmeticFunction.moebius x.1 * ((if x.2 = 0 then (0 : ℕ) else 1 : ℕ) : ℤ) =
            ∑ k ∈ (m / r).divisors, ArithmeticFunction.moebius k := by
          rw [Nat.sum_divisorsAntidiagonal (f := fun a b => ArithmeticFunction.moebius a * ((if b = 0 then (0 : ℕ) else 1 : ℕ) : ℤ))]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkd := (Nat.mem_divisors.mp hk).1
          have hqne : m / r / k ≠ 0 :=
            (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hkd)
              (Nat.pos_of_dvd_of_pos hkd (Nat.pos_of_ne_zero hpos))).ne'
          rw [if_neg hqne]; simp
        rw [← hsum]
        exact hval
      have hmr1 : m / r = 1 ↔ m = r := by
        constructor
        · intro h1; have := Nat.mul_div_cancel' hrm; rw [h1, mul_one] at this; exact this.symm
        · intro heq; subst heq; exact Nat.div_self (by omega)
      have hcast : ∑ k ∈ (m / r).divisors, (ArithmeticFunction.moebius k : ℝ) =
          ((∑ k ∈ (m / r).divisors, ArithmeticFunction.moebius k : ℤ) : ℝ) := by push_cast; rfl
      rw [hcast, hmoeb]
      by_cases heq : m = r
      · rw [if_pos (hmr1.mpr heq), if_pos heq]; simp
      · rw [if_neg (fun h => heq (hmr1.mp h)), if_neg heq]; simp
    rw [Finset.sum_congr rfl fun m hm => by rw [hinner m hm]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_filter.mpr ⟨hr, dvd_refl r⟩)]
  -- Verify c 1 = 1
  have hc1 : c 1 = 1 := by
    dsimp only [c, y]
    rw [Nat.cast_one, one_mul]
    have hfilt1 : S.filter (fun m => 1 ∣ m) = S := by ext m; simp
    rw [hfilt1]
    have hterm : ∀ m ∈ S, (ArithmeticFunction.moebius (m / 1) : ℝ) *
        ((ArithmeticFunction.moebius m : ℝ) / ((Nat.totient m : ℝ) * G)) =
        (1 : ℝ) / (Nat.totient m : ℝ) / G := by
      intro m hm
      rw [Nat.div_one]
      have hmsf := (Finset.mem_filter.mp hm).2
      have hm_sq : (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius m : ℝ) = 1 := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hmsf]
        push_cast
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      calc (ArithmeticFunction.moebius m : ℝ) * ((ArithmeticFunction.moebius m : ℝ) / ((Nat.totient m : ℝ) * G))
          = ((ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius m : ℝ)) / ((Nat.totient m : ℝ) * G) := by ring
        _ = 1 / ((Nat.totient m : ℝ) * G) := by rw [hm_sq]
        _ = (1 : ℝ) / (Nat.totient m : ℝ) / G := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    exact div_self hG_pos.ne'
  -- Bound |c d| ≤ d
  have hc_abs : ∀ d ∈ S, |c d| ≤ (d : ℝ) := by
    intro d hd
    dsimp only [c, y]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
    have hsum_le : |∑ m ∈ S.filter (fun m => d ∣ m),
        (ArithmeticFunction.moebius (m / d) : ℝ) *
          ((ArithmeticFunction.moebius m : ℝ) / ((Nat.totient m : ℝ) * G))| ≤ 1 := by
      calc |∑ m ∈ S.filter (fun m => d ∣ m),
              (ArithmeticFunction.moebius (m / d) : ℝ) *
                ((ArithmeticFunction.moebius m : ℝ) / ((Nat.totient m : ℝ) * G))|
          ≤ ∑ m ∈ S.filter (fun m => d ∣ m),
              |(ArithmeticFunction.moebius (m / d) : ℝ) *
                ((ArithmeticFunction.moebius m : ℝ) / ((Nat.totient m : ℝ) * G))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ S.filter (fun m => d ∣ m), (1 : ℝ) / (Nat.totient m : ℝ) / G := by
            refine Finset.sum_le_sum fun m hm => ?_
            have htot_nn : (0 : ℝ) ≤ (Nat.totient m : ℝ) * G := by positivity
            have hmsf : Squarefree m := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
            have hdm : d ∣ m := (Finset.mem_filter.mp hm).2
            have hμ1 : |(ArithmeticFunction.moebius (m / d) : ℝ)| ≤ 1 := by
              rw [ArithmeticFunction.moebius_apply_of_squarefree (hmsf.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm))]; simp
            have hμ2 : |(ArithmeticFunction.moebius m : ℝ)| ≤ 1 := by
              rw [ArithmeticFunction.moebius_apply_of_squarefree hmsf]; simp
            rw [abs_mul, abs_div, abs_of_nonneg htot_nn,
              show (1 : ℝ) / (Nat.totient m : ℝ) / G = 1 * (1 / ((Nat.totient m : ℝ) * G)) by ring]
            exact mul_le_mul hμ1 (div_le_div_of_nonneg_right hμ2 htot_nn)
              (by positivity) zero_le_one
        _ ≤ ∑ m ∈ S, (1 : ℝ) / (Nat.totient m : ℝ) / G :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity)
        _ = G / G := by rw [← Finset.sum_div]
        _ = 1 := div_self hG_pos.ne'
    calc (d : ℝ) * |∑ m ∈ S.filter (fun m => d ∣ m), _|
        ≤ (d : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum_le (Nat.cast_nonneg d)
      _ = (d : ℝ) := mul_one _
  -- Diagonalize the quadratic form: ∑ d1, d2 ∈ S, c d1 * c d2 / lcm(d1, d2) = 1 / G
  have hquad : ∑ d1 ∈ S, ∑ d2 ∈ S, c d1 * c d2 / (Nat.lcm d1 d2 : ℝ) = 1 / G := by
    have hterm : ∀ d1 ∈ S, ∀ d2 ∈ S,
        c d1 * c d2 / (Nat.lcm d1 d2 : ℝ) =
          ∑ r ∈ S, if r ∣ d1 ∧ r ∣ d2 then
            (Nat.totient r : ℝ) * (c d1 / (d1 : ℝ)) * (c d2 / (d2 : ℝ)) else 0 := by
      intro d1 hd1 d2 hd2
      have hd1_pos : 0 < d1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1).1
      have hd2_pos : 0 < d2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd2).1).1
      have hd1_R : d1 ≤ R := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1).2
      have hd1_sf : Squarefree d1 := (Finset.mem_filter.mp hd1).2
      have hgl : Nat.gcd d1 d2 * Nat.lcm d1 d2 = d1 * d2 := Nat.gcd_mul_lcm d1 d2
      have hlcm_pos : (0 : ℝ) < Nat.lcm d1 d2 := by
        exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd1_pos.ne' hd2_pos.ne')
      have hd1r : (0 : ℝ) < d1 := by exact_mod_cast hd1_pos
      have hd2r : (0 : ℝ) < d2 := by exact_mod_cast hd2_pos
      have hdiv_eq : S.filter (fun r => r ∣ d1 ∧ r ∣ d2) = (Nat.gcd d1 d2).divisors := by
        ext r
        simp only [S, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨⟨_, _⟩, _⟩, hr1, hr2⟩
          exact ⟨Nat.dvd_gcd hr1 hr2, (Nat.gcd_pos_of_pos_left d2 hd1_pos).ne'⟩
        · rintro ⟨hrg, _⟩
          have hr1 : r ∣ d1 := hrg.trans (Nat.gcd_dvd_left d1 d2)
          have hr2 : r ∣ d2 := hrg.trans (Nat.gcd_dvd_right d1 d2)
          exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hr1 hd1_pos, (Nat.le_of_dvd hd1_pos hr1).trans hd1_R⟩,
            hd1_sf.squarefree_of_dvd hr1⟩, hr1, hr2⟩
      rw [← Finset.sum_filter, hdiv_eq, ← Finset.sum_mul, ← Finset.sum_mul]
      have htot_sum : ∑ r ∈ (Nat.gcd d1 d2).divisors, (Nat.totient r : ℝ) = (Nat.gcd d1 d2 : ℝ) := by
        exact_mod_cast Nat.sum_totient (Nat.gcd d1 d2)
      rw [htot_sum]
      have hglr : (Nat.gcd d1 d2 : ℝ) * (Nat.lcm d1 d2 : ℝ) = (d1 : ℝ) * (d2 : ℝ) := by
        exact_mod_cast hgl
      field_simp
      calc c d1 * c d2 * (d1 : ℝ) * (d2 : ℝ)
          = c d1 * c d2 * ((d1 : ℝ) * (d2 : ℝ)) := by ring
        _ = c d1 * c d2 * ((Nat.gcd d1 d2 : ℝ) * (Nat.lcm d1 d2 : ℝ)) := by rw [← hglr]
        _ = c d1 * c d2 * (Nat.lcm d1 d2 : ℝ) * (Nat.gcd d1 d2 : ℝ) := by ring
    calc ∑ d1 ∈ S, ∑ d2 ∈ S, c d1 * c d2 / (Nat.lcm d1 d2 : ℝ)
        = ∑ d1 ∈ S, ∑ d2 ∈ S, ∑ r ∈ S,
            if r ∣ d1 ∧ r ∣ d2 then
              (Nat.totient r : ℝ) * (c d1 / (d1 : ℝ)) * (c d2 / (d2 : ℝ)) else 0 := by
          refine Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 =>
            hterm d1 hd1 d2 hd2
      _ = ∑ r ∈ S, ∑ d1 ∈ S, ∑ d2 ∈ S,
            if r ∣ d1 ∧ r ∣ d2 then
              (Nat.totient r : ℝ) * (c d1 / (d1 : ℝ)) * (c d2 / (d2 : ℝ)) else 0 := by
          have h1 : ∀ d1 ∈ S, ∑ d2 ∈ S, ∑ r ∈ S,
              (if r ∣ d1 ∧ r ∣ d2 then (Nat.totient r : ℝ) * (c d1 / (d1 : ℝ)) * (c d2 / (d2 : ℝ)) else 0) =
              ∑ r ∈ S, ∑ d2 ∈ S,
              (if r ∣ d1 ∧ r ∣ d2 then (Nat.totient r : ℝ) * (c d1 / (d1 : ℝ)) * (c d2 / (d2 : ℝ)) else 0) :=
            fun _ _ => Finset.sum_comm
          rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      _ = ∑ r ∈ S, (Nat.totient r : ℝ) * (y r) ^ 2 := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [← hinv r hr, sq, Finset.sum_mul, Finset.mul_sum]
          simp_rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d1 _ => ?_
          split_ifs with h1
          · refine Finset.sum_congr rfl fun d2 _ => ?_
            by_cases h2 : r ∣ d2
            · rw [if_pos ⟨h1, h2⟩, if_pos h2]; ring
            · rw [if_neg (fun h => h2 h.2), if_neg h2]; ring
          · refine Finset.sum_eq_zero fun d2 _ => ?_
            rw [if_neg (fun h => h1 h.1)]
      _ = ∑ r ∈ S, (1 : ℝ) / (Nat.totient r : ℝ) / G ^ 2 := by
          refine Finset.sum_congr rfl fun r hr => ?_
          have hrsf : Squarefree r := (Finset.mem_filter.mp hr).2
          have hr_pos : 0 < r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
          have htot_pos : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr_pos
          have hμ_sq : (ArithmeticFunction.moebius r : ℝ) ^ 2 = 1 := by
            rw [ArithmeticFunction.moebius_apply_of_squarefree hrsf]
            push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
          dsimp only [y]
          rw [div_pow, hμ_sq]
          field_simp
      _ = G / G ^ 2 := by rw [← Finset.sum_div]
      _ = 1 / G := by field_simp
  -- Upper bound the count of R-rough integers in (A, B]
  set U := (Finset.Ioc A B).filter (fun b => ∀ p : ℕ, p.Prime → p ≤ R → ¬ p ∣ b)
  have hpoint : ∀ b ∈ U, (1 : ℝ) = (∑ d ∈ S.filter (fun d => d ∣ b), c d) ^ 2 := by
    intro b hb
    have hrough := (Finset.mem_filter.mp hb).2
    have honly : S.filter (fun d => d ∣ b) = {1} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hdS, hdb⟩
        obtain ⟨hdI, _⟩ := Finset.mem_filter.mp hdS
        obtain ⟨hd1, hdR⟩ := Finset.mem_Icc.mp hdI
        by_contra hne
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
        exact hrough p hp ((Nat.le_of_dvd (by omega) hpd).trans hdR) (hpd.trans hdb)
      · rintro rfl; exact ⟨h1S, one_dvd b⟩
    rw [honly, Finset.sum_singleton, hc1, one_pow]
  have hU_le : (U.card : ℝ) ≤ ∑ b ∈ Finset.Ioc A B, (∑ d ∈ S.filter (fun d => d ∣ b), c d) ^ 2 := by
    calc (U.card : ℝ) = ∑ _b ∈ U, (1 : ℝ) := by simp
      _ = ∑ b ∈ U, (∑ d ∈ S.filter (fun d => d ∣ b), c d) ^ 2 :=
          Finset.sum_congr rfl fun b hb => hpoint b hb
      _ ≤ ∑ b ∈ Finset.Ioc A B, (∑ d ∈ S.filter (fun d => d ∣ b), c d) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => sq_nonneg _)
  have hexpand : ∑ b ∈ Finset.Ioc A B, (∑ d ∈ S.filter (fun d => d ∣ b), c d) ^ 2 =
      ∑ d1 ∈ S, ∑ d2 ∈ S, c d1 * c d2 *
        (((Finset.Ioc A B).filter (fun b => Nat.lcm d1 d2 ∣ b)).card : ℝ) := by
    have hsq : ∀ b : ℕ, (∑ d ∈ S.filter (fun d => d ∣ b), c d) ^ 2 =
        ∑ d1 ∈ S, ∑ d2 ∈ S, if Nat.lcm d1 d2 ∣ b then c d1 * c d2 else 0 := by
      intro b
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d1 _ => ?_
      split_ifs with h1
      · refine Finset.sum_congr rfl fun d2 _ => ?_
        by_cases h2 : d2 ∣ b
        · rw [if_pos h2, if_pos (Nat.lcm_dvd h1 h2)]
        · rw [if_neg h2, if_neg (fun hl => h2 ((Nat.dvd_lcm_right d1 d2).trans hl))]
      · symm
        refine Finset.sum_eq_zero fun d2 _ => ?_
        exact if_neg (fun hl => h1 ((Nat.dvd_lcm_left d1 d2).trans hl))
    simp_rw [hsq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsum_abs_le : ∑ d ∈ S, |c d| ≤ (R : ℝ) ^ 2 := by
    calc ∑ d ∈ S, |c d| ≤ ∑ d ∈ S, (d : ℝ) := Finset.sum_le_sum fun d hd => hc_abs d hd
      _ ≤ ∑ d ∈ Finset.Icc 1 R, (d : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ _d ∈ Finset.Icc 1 R, (R : ℝ) :=
          Finset.sum_le_sum fun d hd => by exact_mod_cast (Finset.mem_Icc.mp hd).2
      _ = (R : ℝ) ^ 2 := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have hfinal : ∑ d1 ∈ S, ∑ d2 ∈ S, c d1 * c d2 *
      (((Finset.Ioc A B).filter (fun b => Nat.lcm d1 d2 ∣ b)).card : ℝ) ≤
      ((B - A : ℕ) : ℝ) / G + (R : ℝ) ^ 4 := by
    have hsplit : ∑ d1 ∈ S, ∑ d2 ∈ S, c d1 * c d2 *
        (((Finset.Ioc A B).filter (fun b => Nat.lcm d1 d2 ∣ b)).card : ℝ) =
        ((B - A : ℕ) : ℝ) * (∑ d1 ∈ S, ∑ d2 ∈ S, c d1 * c d2 / (Nat.lcm d1 d2 : ℝ)) +
        ∑ d1 ∈ S, ∑ d2 ∈ S, c d1 * c d2 *
          ((((Finset.Ioc A B).filter (fun b => Nat.lcm d1 d2 ∣ b)).card : ℝ) -
            ((B - A : ℕ) : ℝ) / (Nat.lcm d1 d2 : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d1 _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d2 _ => by ring
    rw [hsplit, hquad, mul_one_div]
    have herr : ∑ d1 ∈ S, ∑ d2 ∈ S, c d1 * c d2 *
        ((((Finset.Ioc A B).filter (fun b => Nat.lcm d1 d2 ∣ b)).card : ℝ) -
          ((B - A : ℕ) : ℝ) / (Nat.lcm d1 d2 : ℝ)) ≤ (R : ℝ) ^ 4 := by
      calc ∑ d1 ∈ S, ∑ d2 ∈ S, c d1 * c d2 *
            ((((Finset.Ioc A B).filter (fun b => Nat.lcm d1 d2 ∣ b)).card : ℝ) -
              ((B - A : ℕ) : ℝ) / (Nat.lcm d1 d2 : ℝ))
          ≤ ∑ d1 ∈ S, ∑ d2 ∈ S, |c d1| * |c d2| := by
            refine Finset.sum_le_sum fun d1 hd1 => Finset.sum_le_sum fun d2 hd2 => ?_
            have hd1p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1).1
            have hd2p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd2).1).1
            have hlpos : 0 < Nat.lcm d1 d2 :=
              Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
            have hap := card_Ioc_dvd_approx A B (Nat.lcm d1 d2) hAB hlpos
            calc c d1 * c d2 * _ ≤ |c d1 * c d2 * _| := le_abs_self _
              _ = |c d1| * |c d2| * |_| := by rw [abs_mul, abs_mul]
              _ ≤ |c d1| * |c d2| * 1 := mul_le_mul_of_nonneg_left hap (by positivity)
              _ = |c d1| * |c d2| := mul_one _
        _ = (∑ d ∈ S, |c d|) ^ 2 := by
            rw [sq, Finset.sum_mul]; refine Finset.sum_congr rfl fun d1 _ => by rw [← Finset.mul_sum]
        _ ≤ ((R : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hsum_abs_le 2
        _ = (R : ℝ) ^ 4 := by ring
    linarith
  have hmain_le : ((B - A : ℕ) : ℝ) / G ≤ ((B - A : ℕ) : ℝ) / Real.log ((R : ℝ) + 1) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlog_pos hG_ge_log
  linarith

/-- Finite Euler product upper bound for sums of `1 / d` over `P`-smooth integers `d ∈ [1, M]`. -/
lemma sum_inv_primeFactors_subset_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (M : ℕ) :
    ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d.primeFactors ⊆ P), (1 : ℝ) / (d : ℝ) ≤
      ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
  classical
  induction P using Finset.induction_on generalizing M with
  | empty =>
    rw [Finset.prod_empty]
    have hsub : (Finset.Icc 1 M).filter (fun d => d.primeFactors ⊆ ∅) ⊆ {1} := by
      intro d hd
      obtain ⟨hdI, hpf⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hdI
      rw [Finset.mem_singleton]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
      exact Finset.notMem_empty p (hpf (Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩))
    calc ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d.primeFactors ⊆ ∅), (1 : ℝ) / (d : ℝ)
        ≤ ∑ d ∈ ({1} : Finset ℕ), (1 : ℝ) / (d : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | @insert p s hps ih =>
    have hp : p.Prime := hP p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps]
    set A := (Finset.Icc 1 M).filter (fun d => d.primeFactors ⊆ insert p s)
    set B := (Finset.Icc 1 M).filter (fun d => d.primeFactors ⊆ s)
    set img := (Finset.range (M + 1) ×ˢ B).image (fun pair : ℕ × ℕ => p ^ pair.1 * pair.2)
    have hA_sub : A ⊆ img := by
      intro d hd
      obtain ⟨hdI, hpf⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hdI
      set e := d.factorization p
      have hpe_dvd : p ^ e ∣ d := Nat.ordProj_dvd d p
      set m := d / p ^ e
      have hmul : p ^ e * m = d := Nat.mul_div_cancel' hpe_dvd
      have hpe_le : p ^ e ≤ d := Nat.le_of_dvd (by omega) hpe_dvd
      have he_lt : e < M + 1 := by
        have hlt : e < 2 ^ e := Nat.lt_two_pow_self
        have h2p : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
        omega
      have hm_pos : 1 ≤ m := Nat.div_pos hpe_le (pow_pos hp.pos e)
      have hm_le : m ≤ M := by
        have : m ≤ p ^ e * m := Nat.le_mul_of_pos_left m (pow_pos hp.pos e)
        omega
      have hcop : ¬ p ∣ m := by
        intro hpm
        have h1 : p ^ (e + 1) ∣ d := by
          rw [← hmul, pow_succ]; exact mul_dvd_mul_left (p ^ e) hpm
        have h2 := (hp.pow_dvd_iff_le_factorization (by omega : d ≠ 0)).mp h1
        omega
      have hm_pf : m.primeFactors ⊆ s := by
        intro q hq
        have hqd : q ∈ d.primeFactors := by
          rw [← hmul, Nat.primeFactors_mul (pow_pos hp.pos e).ne' (by omega)]
          exact Finset.mem_union_right _ hq
        rcases Finset.mem_insert.mp (hpf hqd) with rfl | hqs
        · exact absurd (Nat.dvd_of_mem_primeFactors hq) hcop
        · exact hqs
      exact Finset.mem_image.mpr ⟨(e, m),
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr he_lt,
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩, hm_pf⟩⟩,
        hmul⟩
    have hgeom : ∑ e ∈ Finset.range (M + 1), (1 : ℝ) / ((p : ℝ) ^ e) ≤ (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have h1 : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
      have hrew : ∑ e ∈ Finset.range (M + 1), (1 : ℝ) / ((p : ℝ) ^ e) =
          ∑ e ∈ Finset.range (M + 1), ((1 : ℝ) / (p : ℝ)) ^ e :=
        Finset.sum_congr rfl fun e _ => by rw [one_div_pow]
      rw [hrew, geom_sum_eq (ne_of_lt h1)]
      have hden_pos : (0 : ℝ) < 1 - 1 / (p : ℝ) := by linarith
      have hpow_nn : (0 : ℝ) ≤ ((1 : ℝ) / (p : ℝ)) ^ (M + 1) := by positivity
      rw [show (((1 : ℝ) / (p : ℝ)) ^ (M + 1) - 1) / ((1 : ℝ) / (p : ℝ) - 1) =
          (1 - ((1 : ℝ) / (p : ℝ)) ^ (M + 1)) / (1 - 1 / (p : ℝ)) by rw [← neg_div_neg_eq, neg_sub, neg_sub], inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith) hden_pos.le
    have hden_pos : (0 : ℝ) < 1 - (1 : ℝ) / (p : ℝ) := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    calc ∑ d ∈ A, (1 : ℝ) / (d : ℝ)
        ≤ ∑ d ∈ img, (1 : ℝ) / (d : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hA_sub (fun _ _ _ => by positivity)
      _ ≤ ∑ pair ∈ Finset.range (M + 1) ×ˢ B, (1 : ℝ) / ((p ^ pair.1 * pair.2 : ℕ) : ℝ) :=
          Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
      _ = (∑ e ∈ Finset.range (M + 1), (1 : ℝ) / ((p : ℝ) ^ e)) * (∑ m ∈ B, (1 : ℝ) / (m : ℝ)) := by
          rw [Finset.sum_product, Finset.sum_mul]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          push_cast; ring
      _ ≤ (1 - (1 : ℝ) / (p : ℝ))⁻¹ * ∏ q ∈ s, (1 - (1 : ℝ) / (q : ℝ))⁻¹ :=
          mul_le_mul hgeom (ih hs M) (Finset.sum_nonneg fun _ _ => by positivity)
            (inv_nonneg.mpr hden_pos.le)

/-- Pairwise-coprime `k`-tuples with product `D` inject into `D.primeFactors → Fin k`. -/
lemma card_coprime_tuples_prod_eq_le (k D : ℕ) (hD : 1 ≤ D) :
    ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
      (fun (f : Fin k → ℕ) => (∏ j : Fin k, f j) = D ∧
        Pairwise (fun j1 j2 : Fin k => Nat.Coprime (f j1) (f j2)))).card ≤
      k ^ D.primeFactors.card := by
  classical
  set F := (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
    (fun (f : Fin k → ℕ) => (∏ j : Fin k, f j) = D ∧
      Pairwise (fun j1 j2 : Fin k => Nat.Coprime (f j1) (f j2)))
  have hex : ∀ f ∈ F, ∀ p : D.primeFactors, ∃ j : Fin k, p.val ∣ f j := by
    intro f hf p
    obtain ⟨_, hprod, _⟩ := Finset.mem_filter.mp hf
    have hp_prime := Nat.prime_of_mem_primeFactors p.property
    have hp_dvd : p.val ∣ ∏ j : Fin k, f j := hprod.symm ▸ Nat.dvd_of_mem_primeFactors p.property
    obtain ⟨j, _, hj⟩ := (Prime.dvd_finsetProd_iff hp_prime.prime _).mp hp_dvd
    exact ⟨j, hj⟩
  by_cases hFne : F.Nonempty
  · by_cases hk0 : k = 0
    · subst hk0
      have hcard_le : F.card ≤ 1 := by
        calc F.card ≤ (Fintype.piFinset (fun _ : Fin 0 => Finset.Icc 1 D)).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = 1 := by simp
      obtain ⟨f0, hf0⟩ := hFne
      have hD1 : D = 1 := by
        have := (Finset.mem_filter.mp hf0).2.1
        simp at this; exact this.symm
      subst hD1
      simpa using hcard_le
    · have hkpos : 0 < k := by omega
      let ψ : (Fin k → ℕ) → (D.primeFactors → Fin k) := fun f p =>
        if hf : f ∈ F then Classical.choose (hex f hf p) else ⟨0, hkpos⟩
      have hinj : Set.InjOn ψ (F : Set (Fin k → ℕ)) := by
        intro f1 hf1 f2 hf2 heq
        rw [Finset.mem_coe] at hf1 hf2
        obtain ⟨hf1_pi, hprod1, hcop1⟩ := Finset.mem_filter.mp hf1
        obtain ⟨hf2_pi, hprod2, hcop2⟩ := Finset.mem_filter.mp hf2
        have hf1_pos : ∀ j : Fin k, f1 j ≠ 0 := fun j => by
          have := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hf1_pi j)).1; omega
        have hf2_pos : ∀ j : Fin k, f2 j ≠ 0 := fun j => by
          have := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hf2_pi j)).1; omega
        funext j
        apply Nat.eq_of_factorization_eq (hf1_pos j) (hf2_pos j)
        intro p
        by_cases hp : p ∈ D.primeFactors
        · have hp_prime := Nat.prime_of_mem_primeFactors hp
          let p' : D.primeFactors := ⟨p, hp⟩
          have h1_dvd : p ∣ f1 (ψ f1 p') := by
            dsimp only [ψ]; rw [dif_pos hf1]; exact Classical.choose_spec (hex f1 hf1 p')
          have h2_dvd : p ∣ f2 (ψ f2 p') := by
            dsimp only [ψ]; rw [dif_pos hf2]; exact Classical.choose_spec (hex f2 hf2 p')
          have hj_eq : ψ f1 p' = ψ f2 p' := congrFun heq p'
          rw [← hj_eq] at h2_dvd
          set j0 := ψ f1 p'
          by_cases hjj : j = j0
          · rw [hjj]
            have hfac1 : D.factorization p = (f1 j0).factorization p := by
              rw [← hprod1, Nat.factorization_prod (fun i _ => hf1_pos i), Finsupp.finsetSum_apply]
              rw [Finset.sum_eq_single j0]
              · intro i _ hij
                have hni : ¬ p ∣ f1 i := fun hpi =>
                  hp_prime.not_dvd_one ((hcop1 hij).gcd_eq_one ▸ Nat.dvd_gcd hpi h1_dvd)
                exact Nat.factorization_eq_zero_of_not_dvd hni
              · intro h; exact absurd (Finset.mem_univ j0) h
            have hfac2 : D.factorization p = (f2 j0).factorization p := by
              rw [← hprod2, Nat.factorization_prod (fun i _ => hf2_pos i), Finsupp.finsetSum_apply]
              rw [Finset.sum_eq_single j0]
              · intro i _ hij
                have hni : ¬ p ∣ f2 i := fun hpi =>
                  hp_prime.not_dvd_one ((hcop2 hij).gcd_eq_one ▸ Nat.dvd_gcd hpi h2_dvd)
                exact Nat.factorization_eq_zero_of_not_dvd hni
              · intro h; exact absurd (Finset.mem_univ j0) h
            omega
          · have hn1 : ¬ p ∣ f1 j := fun hpj =>
              hp_prime.not_dvd_one ((hcop1 hjj).gcd_eq_one ▸ Nat.dvd_gcd hpj h1_dvd)
            have hn2 : ¬ p ∣ f2 j := fun hpj =>
              hp_prime.not_dvd_one ((hcop2 hjj).gcd_eq_one ▸ Nat.dvd_gcd hpj h2_dvd)
            rw [Nat.factorization_eq_zero_of_not_dvd hn1, Nat.factorization_eq_zero_of_not_dvd hn2]
        · by_cases hpp : p.Prime
          · have hndvdD : ¬ p ∣ D := fun h => hp (Nat.mem_primeFactors.mpr ⟨hpp, h, by omega⟩)
            have hn1 : ¬ p ∣ f1 j := fun h =>
              hndvdD (h.trans (hprod1 ▸ Finset.dvd_prod_of_mem f1 (Finset.mem_univ j)))
            have hn2 : ¬ p ∣ f2 j := fun h =>
              hndvdD (h.trans (hprod2 ▸ Finset.dvd_prod_of_mem f2 (Finset.mem_univ j)))
            rw [Nat.factorization_eq_zero_of_not_dvd hn1, Nat.factorization_eq_zero_of_not_dvd hn2]
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp,
              Nat.factorization_eq_zero_of_not_prime _ hpp]
      calc F.card = (F.image ψ).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (D.primeFactors → Fin k)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card (D.primeFactors → Fin k) := Finset.card_univ
        _ = k ^ D.primeFactors.card := by simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hFne, Finset.card_empty]
    exact Nat.zero_le _

/-- If every prime factor of `D ≥ 1` is `≥ z > 1` and `D ≤ z ^ K`, then `ω(D) ≤ K`. -/
lemma primeFactors_card_le_of_rough (D K : ℕ) (z : ℝ) (hD : 1 ≤ D) (hz : 1 < z)
    (hrough : ∀ p ∈ D.primeFactors, z ≤ (p : ℝ)) (hDK : (D : ℝ) ≤ z ^ K) :
    D.primeFactors.card ≤ K := by
  have h1 : z ^ D.primeFactors.card ≤ (D : ℝ) := by
    calc z ^ D.primeFactors.card = ∏ _p ∈ D.primeFactors, z := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ D.primeFactors, (p : ℝ) :=
          Finset.prod_le_prod (fun _ _ => by linarith) (fun p hp => hrough p hp)
      _ = ((∏ p ∈ D.primeFactors, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
      _ ≤ (D : ℝ) := by exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd D)
  have h2 : z ^ D.primeFactors.card ≤ z ^ K := h1.trans hDK
  by_contra hgt
  push Not at hgt
  have hlt : z ^ K < z ^ D.primeFactors.card := pow_lt_pow_right₀ hz hgt
  linarith

/-- Chinese Remainder Theorem over a finite set of pairwise-coprime moduli. -/
lemma crt_finset_exists {ι : Type*} [DecidableEq ι] (s : Finset ι) (m r : ι → ℕ)
    (hcop : Set.Pairwise (s : Set ι) (fun a b => Nat.Coprime (m a) (m b))) :
    ∃ γ : ℕ, ∀ n : ℕ, (∀ a ∈ s, n ≡ r a [MOD m a]) → n ≡ γ [MOD ∏ a ∈ s, m a] := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ _ => by simp [Nat.ModEq, Nat.mod_one]⟩
  | @insert a s has ih =>
    have hcop_s : Set.Pairwise (s : Set ι) (fun x y => Nat.Coprime (m x) (m y)) :=
      fun x hx y hy hxy => hcop (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) hxy
    obtain ⟨γs, hγs⟩ := ih hcop_s
    have hcop_a : Nat.Coprime (m a) (∏ b ∈ s, m b) :=
      Nat.Coprime.prod_right fun b hb =>
        hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb) (fun h => has (h ▸ hb))
    let cr := Nat.chineseRemainder hcop_a (r a) γs
    refine ⟨cr.val, fun n hn => ?_⟩
    rw [Finset.prod_insert has, ← Nat.modEq_and_modEq_iff_modEq_mul hcop_a]
    exact ⟨(hn a (Finset.mem_insert_self a s)).trans cr.property.1.symm,
      (hγs n fun b hb => hn b (Finset.mem_insert_of_mem hb)).trans cr.property.2.symm⟩

end E387Selberg

namespace E387Switch

open Finset Real E387Selberg
open scoped Classical

/-- Converse of `prime_dvd_choose_imp_mod_lt`: if `p > k` is prime and `n % p < k < n`, then `p ∣ n.choose k`. -/
lemma mod_lt_imp_prime_dvd_choose {n k p : ℕ} (hkn : k < n) (hp : p.Prime) (hpk : k < p)
    (hmod : n % p < k) : p ∣ n.choose k := by
  set j := n % p
  have hjn : j ≤ n := le_trans (le_of_lt hmod) (le_of_lt hkn)
  have hp_sub : p ∣ n - j := by
    have h1 := Nat.div_add_mod n p
    have h2 : n - j = p * (n / p) := by omega
    rw [h2]
    exact dvd_mul_right p (n / p)
  have hp_prod : p ∣ ∏ i ∈ Finset.range k, (n - i) :=
    hp_sub.trans (Finset.dvd_prod_of_mem (fun i => n - i) (Finset.mem_range.mpr hmod))
  have hdesc : ∏ i ∈ Finset.range k, (n - i) = k.factorial * n.choose k := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
  rw [hdesc] at hp_prod
  have hnot_fac : ¬ p ∣ k.factorial := by
    rw [hp.dvd_factorial]; omega
  exact (hp.dvd_mul.mp hp_prod).resolve_left hnot_fac

/-- Product of reduced numerator factors equals `n.choose k`. -/
lemma prod_div_g_eq_choose {n k : ℕ} {g : ℕ → ℕ}
    (hfact : (∏ i ∈ Finset.range k, g i) = k.factorial)
    (hdvd : ∀ i < k, g i ∣ n - i) :
    (∏ i ∈ Finset.range k, (n - i) / g i) = n.choose k := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k)
  rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
    ← hfact, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i hi => Nat.mul_div_cancel' (hdvd i (Finset.mem_range.mp hi))

/-- Elementary bound `log u ≤ 4 * u ^ (1 / 4)` for `u > 0`. -/
lemma log_le_four_rpow_quarter (u : ℝ) (hu : 0 < u) :
    Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := by
  have h1 : Real.log (u ^ (1 / 4 : ℝ)) ≤ u ^ (1 / 4 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu _)
  rw [Real.log_rpow hu] at h1
  linarith

/-- Uniform reciprocal-sum bound for `z`-rough integers `b` in `[D / (2 * gi), 2 * D / gi]`. -/
lemma sum_inv_rough_b_le (D gi : ℕ) (z : ℝ) (hgi : 1 ≤ gi) (hz16 : (16 : ℝ) ^ 16 ≤ z)
    (hDz : z ≤ (D : ℝ)) (hgi_le : 2 * (gi : ℝ) ≤ z ^ (1 / 2 : ℝ)) :
    ∑ b ∈ (Finset.Icc (D / (2 * gi)) (2 * D / gi)).filter
        (fun b => 1 ≤ b ∧ ∀ p : ℕ, p ∈ b.primeFactors → z ≤ (p : ℝ)), (1 : ℝ) / (b : ℝ) ≤
      200 / Real.log z := by
  set Bset := (Finset.Icc (D / (2 * gi)) (2 * D / gi)).filter
    (fun b => 1 ≤ b ∧ ∀ p : ℕ, p ∈ b.primeFactors → z ≤ (p : ℝ))
  have hz_pos : (0 : ℝ) < z := by linarith [show (16 : ℝ) ^ 16 > 0 by norm_num]
  have hz_gt1 : (1 : ℝ) < z := by linarith [show (16 : ℝ) ^ 16 > 1 by norm_num]
  have hlogz_pos : 0 < Real.log z := Real.log_pos hz_gt1
  have hgi_pos : (0 : ℝ) < gi := by exact_mod_cast (by omega : 0 < gi)
  have hD_pos : (0 : ℝ) < D := lt_of_lt_of_le hz_pos hDz
  have hz_sqrt_le : z ^ (1 / 2 : ℝ) ≤ z := by
    have h1 : z ^ (1 / 2 : ℝ) ≤ z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz_gt1.le (by norm_num)
    simpa using h1
  have h2gi_le_D : 2 * gi ≤ D := by
    have : (2 * gi : ℝ) ≤ (D : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hlo_pos : 1 ≤ D / (2 * gi) := Nat.div_pos h2gi_le_D (by omega)
  set A := D / (2 * gi) - 1
  set B := 2 * D / gi
  have hAB : A ≤ B := by
    have h1 : D / (2 * gi) ≤ D / gi := Nat.div_le_div_left (by omega) (by omega)
    have h2 : D / gi ≤ 2 * D / gi := Nat.div_le_div_right (by omega)
    omega
  set R := Nat.floor (z ^ (1 / 16 : ℝ))
  have hz16_rpow : (16 : ℝ) ≤ z ^ (1 / 16 : ℝ) := by
    calc (16 : ℝ) = ((16 : ℝ) ^ (16 : ℝ)) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ = ((16 : ℝ) ^ (16 : ℕ)) ^ (1 / 16 : ℝ) := by
          rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ ≤ z ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by positivity) hz16 (by norm_num)
  have hR_ge1 : 1 ≤ R := by
    have : ((1 : ℕ) : ℝ) ≤ z ^ (1 / 16 : ℝ) := by linarith
    exact Nat.le_floor this
  have hR_le_z16 : (R : ℝ) ≤ z ^ (1 / 16 : ℝ) := Nat.floor_le (Real.rpow_nonneg hz_pos.le _)
  have hR_lt_z : (R : ℝ) < z := by
    have hlt : z ^ (1 / 16 : ℝ) < z ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hz_gt1 (by norm_num)
    simp only [Real.rpow_one] at hlt
    linarith
  have hBset_sub : Bset ⊆ (Finset.Ioc A B).filter (fun b => ∀ p : ℕ, p.Prime → p ≤ R → ¬ p ∣ b) := by
    intro b hb
    obtain ⟨hbI, hb1, hrough⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbl, hbu⟩ := Finset.mem_Icc.mp hbI
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hbu⟩, fun p hp hpR hpb => ?_⟩
    have hpz := hrough p (Nat.mem_primeFactors.mpr ⟨hp, hpb, by omega⟩)
    have hpR' : (p : ℝ) ≤ (R : ℝ) := by exact_mod_cast hpR
    linarith
  have hBset_card : (Bset.card : ℝ) ≤ ((B - A : ℕ) : ℝ) / Real.log ((R : ℝ) + 1) + (R : ℝ) ^ 4 := by
    calc (Bset.card : ℝ)
        ≤ (((Finset.Ioc A B).filter (fun b => ∀ p : ℕ, p.Prime → p ≤ R → ¬ p ∣ b)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hBset_sub
      _ ≤ ((B - A : ℕ) : ℝ) / Real.log ((R : ℝ) + 1) + (R : ℝ) ^ 4 :=
          selberg_rough_Ioc_le A B R hAB hR_ge1
  have hBA_le : ((B - A : ℕ) : ℝ) ≤ 3 * (D : ℝ) / (gi : ℝ) := by
    have h1 : B - A ≤ 2 * D / gi + 1 := by omega
    have h2 : ((2 * D / gi : ℕ) : ℝ) ≤ 2 * (D : ℝ) / (gi : ℝ) := by
      rw [le_div_iff₀ hgi_pos]
      have : (2 * D / gi) * gi ≤ 2 * D := Nat.div_mul_le_self (2 * D) gi
      exact_mod_cast this
    have h3 : (1 : ℝ) ≤ (D : ℝ) / (gi : ℝ) := by
      rw [le_div_iff₀ hgi_pos, one_mul]
      have : gi ≤ D := by omega
      exact_mod_cast this
    have h1r : ((B - A : ℕ) : ℝ) ≤ ((2 * D / gi : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    have h23 : 2 * (D : ℝ) / (gi : ℝ) + (D : ℝ) / (gi : ℝ) = 3 * (D : ℝ) / (gi : ℝ) := by ring
    linarith
  have hlogR_ge : (1 / 16 : ℝ) * Real.log z ≤ Real.log ((R : ℝ) + 1) := by
    have hlt : z ^ (1 / 16 : ℝ) < (R : ℝ) + 1 := Nat.lt_floor_add_one _
    calc (1 / 16 : ℝ) * Real.log z = Real.log (z ^ (1 / 16 : ℝ)) := (Real.log_rpow hz_pos _).symm
      _ ≤ Real.log ((R : ℝ) + 1) := Real.log_le_log (Real.rpow_pos_of_pos hz_pos _) hlt.le
  have hR4_le : (R : ℝ) ^ 4 ≤ z ^ (1 / 4 : ℝ) := by
    calc (R : ℝ) ^ 4 ≤ (z ^ (1 / 16 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg R) hR_le_z16 4
      _ = (z ^ (1 / 16 : ℝ)) ^ (4 : ℝ) := by rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ = z ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hz_pos.le]; congr 1; norm_num
  have hinv_b : ∀ b ∈ Bset, (1 : ℝ) / (b : ℝ) ≤ 4 * (gi : ℝ) / (D : ℝ) := by
    intro b hb
    obtain ⟨hbI, hb1, _⟩ := Finset.mem_filter.mp hb
    have hbl := (Finset.mem_Icc.mp hbI).1
    have hD_le : D ≤ 4 * gi * b := by
      have hdiv := Nat.div_add_mod D (2 * gi)
      have hmod : D % (2 * gi) < 2 * gi := Nat.mod_lt D (by omega)
      have hmul : 2 * gi * (D / (2 * gi)) ≤ 2 * gi * b := Nat.mul_le_mul_left (2 * gi) hbl
      nlinarith
    have hb_pos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    rw [div_le_div_iff₀ hb_pos hD_pos, one_mul]
    exact_mod_cast (show D ≤ 4 * gi * b from hD_le)
  have hsum_le : ∑ b ∈ Bset, (1 : ℝ) / (b : ℝ) ≤ (Bset.card : ℝ) * (4 * (gi : ℝ) / (D : ℝ)) := by
    calc ∑ b ∈ Bset, (1 : ℝ) / (b : ℝ)
        ≤ ∑ _b ∈ Bset, (4 * (gi : ℝ) / (D : ℝ)) := Finset.sum_le_sum hinv_b
      _ = (Bset.card : ℝ) * (4 * (gi : ℝ) / (D : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmain_part : ((B - A : ℕ) : ℝ) / Real.log ((R : ℝ) + 1) ≤
      (48 * (D : ℝ) / (gi : ℝ)) / Real.log z := by
    have hlogR_pos : 0 < Real.log ((R : ℝ) + 1) := by linarith
    have h1 : ((B - A : ℕ) : ℝ) / Real.log ((R : ℝ) + 1) ≤
        (3 * (D : ℝ) / (gi : ℝ)) / ((1 / 16 : ℝ) * Real.log z) := by
      calc ((B - A : ℕ) : ℝ) / Real.log ((R : ℝ) + 1)
          ≤ (3 * (D : ℝ) / (gi : ℝ)) / Real.log ((R : ℝ) + 1) :=
            div_le_div_of_nonneg_right hBA_le hlogR_pos.le
        _ ≤ (3 * (D : ℝ) / (gi : ℝ)) / ((1 / 16 : ℝ) * Real.log z) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hlogR_ge
    have heq : (3 * (D : ℝ) / (gi : ℝ)) / ((1 / 16 : ℝ) * Real.log z) =
        (48 * (D : ℝ) / (gi : ℝ)) / Real.log z := by ring
    linarith
  have herr_part : z ^ (1 / 4 : ℝ) * (4 * (gi : ℝ) / (D : ℝ)) ≤ 8 / Real.log z := by
    have h1 : (4 * (gi : ℝ) / (D : ℝ)) ≤ 2 / z ^ (1 / 2 : ℝ) := by
      rw [div_le_div_iff₀ hD_pos (Real.rpow_pos_of_pos hz_pos _)]
      have hsq : z ^ (1 / 2 : ℝ) * z ^ (1 / 2 : ℝ) = z := by
        rw [← Real.rpow_add hz_pos]; norm_num
      nlinarith
    have h2 : z ^ (1 / 4 : ℝ) * (4 * (gi : ℝ) / (D : ℝ)) ≤ 2 / z ^ (1 / 4 : ℝ) := by
      calc z ^ (1 / 4 : ℝ) * (4 * (gi : ℝ) / (D : ℝ))
          ≤ z ^ (1 / 4 : ℝ) * (2 / z ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hz_pos.le _)
        _ = 2 / z ^ (1 / 4 : ℝ) := by
            have hq : z ^ (1 / 4 : ℝ) * z ^ (1 / 4 : ℝ) = z ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_add hz_pos]; congr 1; norm_num
            have hpos4 : (0 : ℝ) < z ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hz_pos _
            have hpos2 : (0 : ℝ) < z ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hz_pos _
            field_simp
            nlinarith
    have h3 : 2 / z ^ (1 / 4 : ℝ) ≤ 8 / Real.log z := by
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hz_pos _) hlogz_pos]
      linarith [log_le_four_rpow_quarter z hz_pos]
    linarith
  have hprod1 : ((48 * (D : ℝ) / (gi : ℝ)) / Real.log z) * (4 * (gi : ℝ) / (D : ℝ)) =
      192 / Real.log z := by
    field_simp; ring
  have hcard_mul : (Bset.card : ℝ) * (4 * (gi : ℝ) / (D : ℝ)) ≤
      (((48 * (D : ℝ) / (gi : ℝ)) / Real.log z) + z ^ (1 / 4 : ℝ)) * (4 * (gi : ℝ) / (D : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [add_mul, hprod1] at hcard_mul
  have h192 : (192 : ℝ) / Real.log z + 8 / Real.log z = 200 / Real.log z := by ring
  linarith

/-- Sum of `∏ f j` over pairwise-coprime `z`-rough `k`-tuples with product in `[1, M]`. -/
lemma sum_prod_coprime_rough_tuples_le (k M K : ℕ) (hk : 1 ≤ k) (z : ℝ) (hz : 1 < z)
    (hMK : (M : ℝ) ≤ z ^ K) :
    ∑ f ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 M)).filter
        (fun (f : Fin k → ℕ) => (∏ j : Fin k, f j) ≤ M ∧
          Pairwise (fun j1 j2 : Fin k => Nat.Coprime (f j1) (f j2)) ∧
          ∀ j : Fin k, ∀ p ∈ (f j).primeFactors, z ≤ (p : ℝ)),
      ((∏ j : Fin k, f j : ℕ) : ℝ) ≤ (k : ℝ) ^ K * (M : ℝ) ^ 2 := by
  set T := (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 M)).filter
    (fun (f : Fin k → ℕ) => (∏ j : Fin k, f j) ≤ M ∧
      Pairwise (fun j1 j2 : Fin k => Nat.Coprime (f j1) (f j2)) ∧
      ∀ j : Fin k, ∀ p ∈ (f j).primeFactors, z ≤ (p : ℝ))
  have hmaps : ∀ f ∈ T, (∏ j : Fin k, f j) ∈ Finset.Icc 1 M := fun f hf => by
    obtain ⟨hfpi, hle, _, _⟩ := Finset.mem_filter.mp hf
    have hpos : 1 ≤ ∏ j : Fin k, f j :=
      Finset.one_le_prod' fun j _ => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hfpi j)).1
    exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ D ∈ Finset.Icc 1 M, ∑ f ∈ T.filter (fun f => (∏ j : Fin k, f j) = D), ((∏ j : Fin k, f j : ℕ) : ℝ)
      ≤ ∑ D ∈ Finset.Icc 1 M, (k : ℝ) ^ K * (M : ℝ) := by
        refine Finset.sum_le_sum fun D hD => ?_
        obtain ⟨hD1, hDM⟩ := Finset.mem_Icc.mp hD
        have hconst : ∑ f ∈ T.filter (fun f => (∏ j : Fin k, f j) = D), ((∏ j : Fin k, f j : ℕ) : ℝ) =
            ((T.filter (fun f => (∏ j : Fin k, f j) = D)).card : ℝ) * (D : ℝ) := by
          rw [Finset.sum_congr rfl (fun f hf => by rw [(Finset.mem_filter.mp hf).2]),
            Finset.sum_const, nsmul_eq_mul]
        rw [hconst]
        by_cases hfib : (T.filter (fun f => (∏ j : Fin k, f j) = D)).Nonempty
        · obtain ⟨f0, hf0⟩ := hfib
          obtain ⟨hf0T, hf0D⟩ := Finset.mem_filter.mp hf0
          have hD_rough : ∀ p ∈ D.primeFactors, z ≤ (p : ℝ) := by
            intro p hp
            have hp_prime := Nat.prime_of_mem_primeFactors hp
            have hp_dvd : p ∣ ∏ j : Fin k, f0 j := hf0D.symm ▸ Nat.dvd_of_mem_primeFactors hp
            obtain ⟨j, _, hj⟩ := (Prime.dvd_finsetProd_iff hp_prime.prime _).mp hp_dvd
            have hfj_pos : f0 j ≠ 0 := by
              have := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf0T).1 j)).1
              omega
            exact (Finset.mem_filter.mp hf0T).2.2.2 j p (Nat.mem_primeFactors.mpr ⟨hp_prime, hj, hfj_pos⟩)
          have homega : D.primeFactors.card ≤ K :=
            primeFactors_card_le_of_rough D K z hD1 hz hD_rough
              ((Nat.cast_le.mpr hDM).trans hMK)
          have hsub : T.filter (fun f => (∏ j : Fin k, f j) = D) ⊆
              (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
                (fun (f : Fin k → ℕ) => (∏ j : Fin k, f j) = D ∧
                  Pairwise (fun j1 j2 : Fin k => Nat.Coprime (f j1) (f j2))) := by
            intro f hf
            obtain ⟨hfT, hfD⟩ := Finset.mem_filter.mp hf
            obtain ⟨hfpi, _, hcop, _⟩ := Finset.mem_filter.mp hfT
            refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, hfD, hcop⟩
            have h1 := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hfpi j)).1
            have h2 : f j ≤ D := Nat.le_of_dvd (by omega)
              (hfD ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ j))
            exact Finset.mem_Icc.mpr ⟨h1, h2⟩
          have hcard_nat : (T.filter (fun f => (∏ j : Fin k, f j) = D)).card ≤ k ^ K := by
            calc (T.filter (fun f => (∏ j : Fin k, f j) = D)).card
                ≤ _ := Finset.card_le_card hsub
              _ ≤ k ^ D.primeFactors.card := card_coprime_tuples_prod_eq_le k D hD1
              _ ≤ k ^ K := Nat.pow_le_pow_right hk homega
          have hcard_r : ((T.filter (fun f => (∏ j : Fin k, f j) = D)).card : ℝ) ≤ (k : ℝ) ^ K := by
            exact_mod_cast hcard_nat
          exact mul_le_mul hcard_r (Nat.cast_le.mpr hDM) (Nat.cast_nonneg D) (by positivity)
        · rw [Finset.not_nonempty_iff_eq_empty.mp hfib, Finset.card_empty, Nat.cast_zero, zero_mul]
          positivity
    _ = (M : ℝ) * ((k : ℝ) ^ K * (M : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ = (k : ℝ) ^ K * (M : ℝ) ^ 2 := by ring

/-- Divisor-switching upper bound for `E1` given any black-box upper-bound sieve on progressions. -/
theorem E1_card_le_from_sieve (k x Q γ K : ℕ) (g : ℕ → ℕ) (ps : List ℕ) (z V E_err : ℝ)
    (hk : 1 ≤ k) (hQ : 0 < Q) (hx : 2 * k < x)
    (hz16 : (16 : ℝ) ^ 16 ≤ z) (hz2k : 2 * (k : ℝ) < z)
    (hg2 : ∀ i < k, 2 ≤ g i)
    (hfact : (∏ i ∈ Finset.range k, g i) = k.factorial)
    (hg_le_z : ∀ i < k, 2 * (g i : ℝ) ≤ z ^ (1 / 2 : ℝ))
    (hQ_primes : ∀ p ∈ Q.primeFactors, p ≤ 2 * k)
    (hps : ∀ p ∈ ps, p.Prime ∧ 2 * k < p ∧ (p : ℝ) < z)
    (hcov_div : ∀ n ∈ Finset.Ioc x (2 * x), n ≡ γ [MOD Q] → ∀ i < k, g i ∣ n - i)
    (hV_nn : 0 ≤ V) (hE_nn : 0 ≤ E_err)
    (hMDK : ((⌈2 * (x : ℝ) ^ (49 / 100 : ℝ)⌉₊ : ℕ) : ℝ) ≤ z ^ K)
    (hsieve : ∀ (Q' γ' : ℕ), 0 < Q' → (∀ p ∈ ps, Nat.Coprime Q' p) →
      (((Finset.Ioc x (2 * x)).filter
        (fun n => n ≡ γ' [MOD Q'] ∧ ∀ p ∈ ps, ¬ (n % p < k))).card : ℝ) ≤
      (2 * (x : ℝ) / (Q' : ℝ)) * V + E_err) :
    let M_D := ⌈2 * (x : ℝ) ^ (49 / 100 : ℝ)⌉₊
    let Rough := (Finset.Icc 1 M_D).filter (fun d => ∀ p : ℕ, p ∈ d.primeFactors → z ≤ (p : ℝ))
    let S := (Finset.Ioc x (2 * x)).filter (fun n =>
      n ≡ γ [MOD Q] ∧ ∀ p : ℕ, p.Prime → p ∣ n.choose k → z ≤ (p : ℝ))
    let E1 := S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
      (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
      n < 2 * (∏ i ∈ Finset.range k, f i) ∧ (∏ i ∈ Finset.range k, f i) ≤ n ∧
      (∃ i < k, (x : ℝ) ^ (51 / 100 : ℝ) ≤ (f i : ℝ)))
    (E1.card : ℝ) ≤
      (2 * (x : ℝ) / (Q : ℝ)) * V * (k : ℝ) * (200 / Real.log z) *
        (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1) +
      2 * (k : ℝ) * ((k : ℝ) ^ K * (M_D : ℝ) ^ 2) * E_err := by
  intro M_D Rough S E1
  have hz_pos : (0 : ℝ) < z := by linarith [show (16 : ℝ) ^ 16 > 0 by norm_num]
  have hz_gt1 : (1 : ℝ) < z := by linarith [show (16 : ℝ) ^ 16 > 1 by norm_num]
  have hlogz_pos : 0 < Real.log z := Real.log_pos hz_gt1
  have hx_pos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast hQ
  -- Define for each i : Fin k the finite set of candidate tuples f' : Fin k → ℕ
  let GoodTuples (i : Fin k) : Finset (Fin k → ℕ) :=
    (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 M_D)).filter
      (fun (f' : Fin k → ℕ) => f' i = 1 ∧
        z ≤ ((∏ j : Fin k, f' j : ℕ) : ℝ) ∧
        (∏ j : Fin k, f' j) ≤ M_D ∧
        Pairwise (fun j1 j2 : Fin k => Nat.Coprime (f' j1) (f' j2)) ∧
        ∀ j : Fin k, ∀ p ∈ (f' j).primeFactors, z ≤ (p : ℝ))
  let GoodB (i : Fin k) (D : ℕ) : Finset ℕ :=
    (Finset.Icc (D / (2 * g i.val)) (2 * D / g i.val)).filter
      (fun b => 1 ≤ b ∧ Nat.Coprime b D ∧ ∀ p ∈ b.primeFactors, z ≤ (p : ℝ))
  let Cell (i : Fin k) (f' : Fin k → ℕ) (b : ℕ) : Finset ℕ :=
    (Finset.Ioc x (2 * x)).filter (fun n =>
      n ≡ γ [MOD Q] ∧ n ≡ i.val [MOD b] ∧ (∀ j : Fin k, n ≡ j.val [MOD f' j]) ∧
      ∀ p ∈ ps, ¬ (n % p < k))
  -- Step 1: Cover E1 by ⋃ i, ⋃ f' ∈ GoodTuples i, ⋃ b ∈ GoodB i (∏ f'), Cell i f' b
  have hcover : E1 ⊆ Finset.univ.biUnion (fun i : Fin k =>
      (GoodTuples i).biUnion (fun f' =>
        (GoodB i (∏ j : Fin k, f' j)).biUnion (fun b => Cell i f' b))) := by
    intro n hn
    obtain ⟨hnS, f, hfdvd, ⟨i1, hi1, i2, hi2, hne12, hf1, hf2⟩, hfhi, hflo, ⟨i0, hi0, hfbig⟩⟩ :=
      Finset.mem_filter.mp hn
    obtain ⟨hnI, hnQ, hn_rough⟩ := Finset.mem_filter.mp hnS
    obtain ⟨hxn, hn2x⟩ := Finset.mem_Ioc.mp hnI
    have hkn : k < n := by omega
    have hg_dvd : ∀ j < k, g j ∣ n - j := hcov_div n hnI hnQ
    have hchoose_eq : (∏ j ∈ Finset.range k, (n - j) / g j) = n.choose k :=
      prod_div_g_eq_choose hfact hg_dvd
    have hchoose_pos : 0 < n.choose k := Nat.choose_pos (le_of_lt hkn)
    have hfi_pos : 0 < f i0 := by
      have : (0 : ℝ) < (x : ℝ) ^ (51 / 100 : ℝ) := Real.rpow_pos_of_pos hx_pos _
      have : (0 : ℝ) < (f i0 : ℝ) := lt_of_lt_of_le this hfbig
      exact_mod_cast this
    have hdiv_pos : ∀ j < k, 0 < (n - j) / g j := fun j hj =>
      Nat.div_pos (Nat.le_of_dvd (by omega) (hg_dvd j hj)) (by have := hg2 j hj; omega)
    have hfj_pos : ∀ j < k, 0 < f j := fun j hj => Nat.pos_of_dvd_of_pos (hfdvd j hj) (hdiv_pos j hj)
    have hfj_dvd_choose : ∀ j < k, f j ∣ n.choose k := fun j hj =>
      (hfdvd j hj).trans (hchoose_eq ▸ Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj))
    let i : Fin k := ⟨i0, hi0⟩
    let f' : Fin k → ℕ := fun j => if j = i then 1 else f j.val
    let D : ℕ := ∏ j : Fin k, f' j
    have hD_mul : D * f i0 = ∏ j ∈ Finset.range k, f j := by
      have hfin : (∏ j ∈ Finset.range k, f j) = ∏ j : Fin k, f j.val :=
        Finset.prod_range f
      rw [hfin]
      have hsplit1 : ∏ j : Fin k, f j.val = f i.val * ∏ j ∈ Finset.univ.erase i, f j.val :=
        (Finset.mul_prod_erase Finset.univ (fun j : Fin k => f j.val) (Finset.mem_univ i)).symm
      have hsplit2 : D = f' i * ∏ j ∈ Finset.univ.erase i, f' j :=
        (Finset.mul_prod_erase Finset.univ f' (Finset.mem_univ i)).symm
      have hrest : ∏ j ∈ Finset.univ.erase i, f' j = ∏ j ∈ Finset.univ.erase i, f j.val :=
        Finset.prod_congr rfl fun j hj => if_neg (Finset.mem_erase.mp hj).1
      rw [hsplit1, hsplit2, hrest]
      simp [f', i, mul_comm]
    have hD_le_MD : D ≤ M_D := by
      have h1 : (D : ℝ) * (x : ℝ) ^ (51 / 100 : ℝ) ≤ 2 * (x : ℝ) := by
        calc (D : ℝ) * (x : ℝ) ^ (51 / 100 : ℝ)
            ≤ (D : ℝ) * (f i0 : ℝ) := mul_le_mul_of_nonneg_left hfbig (Nat.cast_nonneg D)
          _ = ((∏ j ∈ Finset.range k, f j : ℕ) : ℝ) := by exact_mod_cast hD_mul
          _ ≤ (n : ℝ) := by exact_mod_cast hflo
          _ ≤ 2 * (x : ℝ) := by exact_mod_cast hn2x
      have h2 : (D : ℝ) ≤ 2 * (x : ℝ) ^ (49 / 100 : ℝ) := by
        have hx51 : (0 : ℝ) < (x : ℝ) ^ (51 / 100 : ℝ) := Real.rpow_pos_of_pos hx_pos _
        rw [← mul_le_mul_iff_left₀ hx51]
        have hrpow : 2 * (x : ℝ) ^ (49 / 100 : ℝ) * (x : ℝ) ^ (51 / 100 : ℝ) = 2 * (x : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hx_pos]; norm_num
        linarith
      exact Nat.le_ceil _ |> fun h => by exact_mod_cast h2.trans h
    have hf'_rough : ∀ j : Fin k, ∀ p ∈ (f' j).primeFactors, z ≤ (p : ℝ) := by
      intro j p hp
      by_cases hji : j = i
      · simp [f', hji] at hp
      · simp only [f', if_neg hji] at hp
        exact hn_rough p (Nat.prime_of_mem_primeFactors hp)
          ((Nat.dvd_of_mem_primeFactors hp).trans (hfj_dvd_choose j.val j.isLt))
    have hD_gt1 : 1 < D := by
      have hexj : ∃ j : Fin k, j ≠ i ∧ 1 < f j.val := by
        by_cases h1 : i1 = i0
        · exact ⟨⟨i2, hi2⟩, fun h => hne12 (h1.trans (congrArg Fin.val h).symm), hf2⟩
        · exact ⟨⟨i1, hi1⟩, fun h => h1 (congrArg Fin.val h), hf1⟩
      obtain ⟨j, hji, hfj1⟩ := hexj
      have hdvd : f' j ∣ D := Finset.dvd_prod_of_mem f' (Finset.mem_univ j)
      have hDpos : 0 < D := Finset.prod_pos fun m _ => by
        dsimp only [f']; split_ifs; exact Nat.one_pos; exact hfj_pos m.val m.isLt
      have hle : f' j ≤ D := Nat.le_of_dvd hDpos hdvd
      simp only [f', if_neg hji] at hle
      omega
    have hD_ge_z : z ≤ (D : ℝ) := by
      obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd (by omega : D ≠ 1)
      obtain ⟨j, _, hpj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpD
      have hfj_ne : f' j ≠ 0 := by
        dsimp only [f']; split_ifs; norm_num; exact (hfj_pos j.val j.isLt).ne'
      have hpz := hf'_rough j p (Nat.mem_primeFactors.mpr ⟨hp, hpj, hfj_ne⟩)
      have hp_le_D : (p : ℝ) ≤ (D : ℝ) := by exact_mod_cast Nat.le_of_dvd (by omega) hpD
      linarith
    have hf'_dvd_sub : ∀ j : Fin k, f' j ∣ n - j.val := by
      intro j
      dsimp only [f']
      split_ifs with hji
      · exact one_dvd _
      · exact (hfdvd j.val j.isLt).trans (Nat.div_dvd_of_dvd (hg_dvd j.val j.isLt))
    have hf'_cop : Pairwise (fun j1 j2 : Fin k => Nat.Coprime (f' j1) (f' j2)) := by
      intro j1 j2 hne
      apply Nat.coprime_of_dvd
      intro p hp hp1 hp2
      have hp_sub1 : p ∣ n - j1.val := hp1.trans (hf'_dvd_sub j1)
      have hp_sub2 : p ∣ n - j2.val := hp2.trans (hf'_dvd_sub j2)
      have hfj1_ne : f' j1 ≠ 0 := by
        dsimp only [f']; split_ifs; norm_num; exact (hfj_pos j1.val j1.isLt).ne'
      have hpz : z ≤ (p : ℝ) := hf'_rough j1 p (Nat.mem_primeFactors.mpr ⟨hp, hp1, hfj1_ne⟩)
      have hp_lt_k : p < k := by
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
        · have hdiff : (n - j1.val) - (n - j2.val) = j2.val - j1.val := by omega
          have hpd : p ∣ j2.val - j1.val := hdiff ▸ Nat.dvd_sub hp_sub1 hp_sub2
          have hle := Nat.le_of_dvd (by omega) hpd
          omega
        · have hdiff : (n - j2.val) - (n - j1.val) = j1.val - j2.val := by omega
          have hpd : p ∣ j1.val - j2.val := hdiff ▸ Nat.dvd_sub hp_sub2 hp_sub1
          have hle := Nat.le_of_dvd (by omega) hpd
          omega
      have hp_r : (p : ℝ) < (k : ℝ) := by exact_mod_cast hp_lt_k
      linarith
    have hf'_mem : f' ∈ GoodTuples i := by
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => Finset.mem_Icc.mpr ⟨?_, ?_⟩,
        by simp [f'], hD_ge_z, hD_le_MD, hf'_cop, hf'_rough⟩
      · dsimp only [f']; split_ifs; exact le_rfl; exact hfj_pos j.val j.isLt
      · have hle : f' j ≤ D := Nat.le_of_dvd (by omega) (Finset.dvd_prod_of_mem f' (Finset.mem_univ j))
        exact hle.trans hD_le_MD
    -- Define switched divisor b = ((n - i0) / g i0) / f i0
    let b : ℕ := ((n - i0) / g i0) / f i0
    have hmul_b : g i0 * f i0 * b = n - i0 := by
      have h1 : f i0 * b = (n - i0) / g i0 := Nat.mul_div_cancel' (hfdvd i0 hi0)
      rw [mul_assoc, h1, Nat.mul_div_cancel' (hg_dvd i0 hi0)]
    have hb_dvd_choose : b ∣ n.choose k :=
      (Nat.div_dvd_of_dvd (hfdvd i0 hi0)).trans
        (hchoose_eq ▸ Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi0))
    have hb_pos : 1 ≤ b := Nat.pos_of_dvd_of_pos hb_dvd_choose hchoose_pos
    have hb_dvd_sub : b ∣ n - i0 := by
      rw [← hmul_b]; exact dvd_mul_left b (g i0 * f i0)
    have hb_rough : ∀ p ∈ b.primeFactors, z ≤ (p : ℝ) := fun p hp =>
      hn_rough p (Nat.prime_of_mem_primeFactors hp)
        ((Nat.dvd_of_mem_primeFactors hp).trans hb_dvd_choose)
    have hD_le_2gb : D ≤ 2 * g i0 * b := by
      have h1 : D * f i0 ≤ 2 * (n - i0) := by
        have h2 : D * f i0 ≤ n := hD_mul.symm ▸ hflo
        omega
      have h2 : D * f i0 ≤ (2 * g i0 * b) * f i0 := by
        have heq : (2 * g i0 * b) * f i0 = 2 * (g i0 * f i0 * b) := by ring
        rw [heq, hmul_b]; exact h1
      exact Nat.le_of_mul_le_mul_right h2 hfi_pos
    have hgb_lt_2D : g i0 * b < 2 * D := by
      have h1 : g i0 * b * f i0 < (2 * D) * f i0 := by
        have heq1 : g i0 * b * f i0 = n - i0 := by rw [← hmul_b]; ring
        have heq2 : (2 * D) * f i0 = 2 * (D * f i0) := by ring
        rw [heq1, heq2, hD_mul]
        omega
      exact Nat.lt_of_mul_lt_mul_right h1
    have hb_Icc : b ∈ Finset.Icc (D / (2 * g i0)) (2 * D / g i0) := by
      have hgi_pos : 0 < g i0 := by have := hg2 i0 hi0; omega
      refine Finset.mem_Icc.mpr ⟨(Nat.div_le_iff_le_mul_add_pred (by omega)).mpr ?_,
        (Nat.le_div_iff_mul_le hgi_pos).mpr ?_⟩
      · have : 2 * g i0 * b = b * (2 * g i0) := by ring
        omega
      · have : b * g i0 = g i0 * b := mul_comm b (g i0)
        omega
    have hb_cop_D : Nat.Coprime b D := by
      apply Nat.coprime_of_dvd
      intro p hp hpb hpD
      obtain ⟨j, _, hpj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpD
      have hji : j ≠ i := by
        intro h; rw [h] at hpj; simp [f'] at hpj; exact hp.ne_one hpj
      have hp_sub1 : p ∣ n - i0 := hpb.trans hb_dvd_sub
      have hp_sub2 : p ∣ n - j.val := hpj.trans (hf'_dvd_sub j)
      have hpz := hb_rough p (Nat.mem_primeFactors.mpr ⟨hp, hpb, by omega⟩)
      have hjlt : j.val < k := j.isLt
      have hj_ne : i0 ≠ j.val := fun h => hji (Fin.ext h.symm)
      have hp_lt_k : p < k := by
        rcases lt_or_gt_of_ne hj_ne with hlt | hgt
        · have hdiff : (n - i0) - (n - j.val) = j.val - i0 := by omega
          have hpd : p ∣ j.val - i0 := hdiff ▸ Nat.dvd_sub hp_sub1 hp_sub2
          have hle := Nat.le_of_dvd (by omega) hpd
          omega
        · have hdiff : (n - j.val) - (n - i0) = i0 - j.val := by omega
          have hpd : p ∣ i0 - j.val := hdiff ▸ Nat.dvd_sub hp_sub2 hp_sub1
          have hle := Nat.le_of_dvd (by omega) hpd
          omega
      have hp_r : (p : ℝ) < (k : ℝ) := by exact_mod_cast hp_lt_k
      linarith
    have hb_mem : b ∈ GoodB i D := Finset.mem_filter.mpr ⟨hb_Icc, hb_pos, hb_cop_D, hb_rough⟩
    have hn_cell : n ∈ Cell i f' b := by
      refine Finset.mem_filter.mpr ⟨hnI, hnQ, ?_, ?_, ?_⟩
      · have hmod := Nat.modEq_iff_dvd' (show i0 ≤ n by omega) |>.mpr hb_dvd_sub
        exact hmod.symm
      · intro j
        have hmod := Nat.modEq_iff_dvd' (show j.val ≤ n by omega) |>.mpr (hf'_dvd_sub j)
        exact hmod.symm
      · intro p hp hmod
        obtain ⟨hp_prime, hp2k, hpz⟩ := hps p hp
        have hpdvd := mod_lt_imp_prime_dvd_choose hkn hp_prime (by omega) hmod
        linarith [hn_rough p hp_prime hpdvd]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_biUnion.mpr ⟨f', hf'_mem,
        Finset.mem_biUnion.mpr ⟨b, hb_mem, hn_cell⟩⟩⟩
  -- Step 2: Bound each Cell i f' b using CRT + hsieve
  have hcell_bound : ∀ i : Fin k, ∀ f' ∈ GoodTuples i, ∀ b ∈ GoodB i (∏ j : Fin k, f' j),
      ((Cell i f' b).card : ℝ) ≤
        (2 * (x : ℝ) / ((Q * b * (∏ j : Fin k, f' j) : ℕ) : ℝ)) * V + E_err := by
    intro i f' hf' b hb
    set D := ∏ j : Fin k, f' j
    obtain ⟨hf'pi, _, hDz, _, hf'cop, hf'rough⟩ := Finset.mem_filter.mp hf'
    obtain ⟨_, hb1, hbcopD, hbrough⟩ := Finset.mem_filter.mp hb
    have hD_pos : 0 < D := Finset.prod_pos fun j _ =>
      (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hf'pi j)).1
    have hQ_cop_rough : ∀ m : ℕ, 0 < m → (∀ p ∈ m.primeFactors, z ≤ (p : ℝ)) → Nat.Coprime Q m := by
      intro m hm hrm
      apply Nat.coprime_of_dvd
      intro p hp hpQ hpm
      have hp2k := hQ_primes p (Nat.mem_primeFactors.mpr ⟨hp, hpQ, hQ.ne'⟩)
      have hpz := hrm p (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.ne'⟩)
      have hpr : (p : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hp2k
      linarith
    have hD_rough : ∀ p ∈ D.primeFactors, z ≤ (p : ℝ) := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      obtain ⟨j, _, hpj⟩ := (Prime.dvd_finsetProd_iff hp_prime.prime _).mp (Nat.dvd_of_mem_primeFactors hp)
      have hfj_pos := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hf'pi j)).1
      exact hf'rough j p (Nat.mem_primeFactors.mpr ⟨hp_prime, hpj, by omega⟩)
    have hQb_cop : Nat.Coprime Q b := hQ_cop_rough b (by omega) hbrough
    have hQD_cop : Nat.Coprime Q D := hQ_cop_rough D hD_pos hD_rough
    obtain ⟨γD, hγD⟩ := crt_finset_exists Finset.univ f' (fun j => j.val)
      (fun j1 _ j2 _ hne => hf'cop hne)
    let cr1 := Nat.chineseRemainder hQb_cop γ i.val
    have hQb_cop_D : Nat.Coprime (Q * b) D := hQD_cop.mul_left hbcopD
    let cr2 := Nat.chineseRemainder hQb_cop_D cr1.val γD
    have hsub_cell : Cell i f' b ⊆ (Finset.Ioc x (2 * x)).filter
        (fun n => n ≡ cr2.val [MOD Q * b * D] ∧ ∀ p ∈ ps, ¬ (n % p < k)) := by
      intro n hn
      obtain ⟨hnI, hnQ, hnb, hnf', hnps⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨hnI, ?_, hnps⟩
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hQb_cop_D]
      refine ⟨?_, (hγD n (fun j _ => hnf' j)).trans cr2.property.2.symm⟩
      have hnQb : n ≡ cr1.val [MOD Q * b] := by
        rw [← Nat.modEq_and_modEq_iff_modEq_mul hQb_cop]
        exact ⟨hnQ.trans cr1.property.1.symm, hnb.trans cr1.property.2.symm⟩
      exact hnQb.trans cr2.property.1.symm
    have hQ'_pos : 0 < Q * b * D := Nat.mul_pos (Nat.mul_pos hQ (by omega)) hD_pos
    have hQ'_cop_ps : ∀ p ∈ ps, Nat.Coprime (Q * b * D) p := by
      intro p hp
      obtain ⟨hp_prime, hp2k, hpz⟩ := hps p hp
      have hQp : Nat.Coprime Q p := hp_prime.coprime_iff_not_dvd.mpr (fun hd => by
        have := hQ_primes p (Nat.mem_primeFactors.mpr ⟨hp_prime, hd, hQ.ne'⟩); omega) |>.symm
      have hbp : Nat.Coprime b p := hp_prime.coprime_iff_not_dvd.mpr (fun hd => by
        have := hbrough p (Nat.mem_primeFactors.mpr ⟨hp_prime, hd, by omega⟩); linarith) |>.symm
      have hDp : Nat.Coprime D p := hp_prime.coprime_iff_not_dvd.mpr (fun hd => by
        have := hD_rough p (Nat.mem_primeFactors.mpr ⟨hp_prime, hd, hD_pos.ne'⟩); linarith) |>.symm
      exact (hQp.mul_left hbp).mul_left hDp
    calc ((Cell i f' b).card : ℝ)
        ≤ (((Finset.Ioc x (2 * x)).filter
            (fun n => n ≡ cr2.val [MOD Q * b * D] ∧ ∀ p ∈ ps, ¬ (n % p < k))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub_cell
      _ ≤ (2 * (x : ℝ) / ((Q * b * D : ℕ) : ℝ)) * V + E_err := hsieve (Q * b * D) cr2.val hQ'_pos hQ'_cop_ps
  -- Step 3: Union bound and separate main term + error term
  have hunion : (E1.card : ℝ) ≤ ∑ i : Fin k, ∑ f' ∈ GoodTuples i, ∑ b ∈ GoodB i (∏ j : Fin k, f' j),
      ((Cell i f' b).card : ℝ) := by
    have h1 : E1.card ≤ ∑ i : Fin k, ∑ f' ∈ GoodTuples i, ∑ b ∈ GoodB i (∏ j : Fin k, f' j),
        (Cell i f' b).card := by
      calc E1.card ≤ _ := Finset.card_le_card hcover
        _ ≤ ∑ i : Fin k, ((GoodTuples i).biUnion (fun f' =>
              (GoodB i (∏ j : Fin k, f' j)).biUnion (fun b => Cell i f' b))).card := Finset.card_biUnion_le
        _ ≤ ∑ i : Fin k, ∑ f' ∈ GoodTuples i,
              ((GoodB i (∏ j : Fin k, f' j)).biUnion (fun b => Cell i f' b)).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
        _ ≤ ∑ i : Fin k, ∑ f' ∈ GoodTuples i, ∑ b ∈ GoodB i (∏ j : Fin k, f' j), (Cell i f' b).card :=
            Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
    exact_mod_cast h1
  have hsum_split : ∑ i : Fin k, ∑ f' ∈ GoodTuples i, ∑ b ∈ GoodB i (∏ j : Fin k, f' j),
      ((Cell i f' b).card : ℝ) ≤
      (2 * (x : ℝ) / (Q : ℝ)) * V *
        (∑ i : Fin k, ∑ f' ∈ GoodTuples i,
          ((1 : ℝ) / ((∏ j : Fin k, f' j : ℕ) : ℝ)) *
            ∑ b ∈ GoodB i (∏ j : Fin k, f' j), (1 : ℝ) / (b : ℝ)) +
      (∑ i : Fin k, ∑ f' ∈ GoodTuples i, ((GoodB i (∏ j : Fin k, f' j)).card : ℝ)) * E_err := by
    calc ∑ i : Fin k, ∑ f' ∈ GoodTuples i, ∑ b ∈ GoodB i (∏ j : Fin k, f' j), ((Cell i f' b).card : ℝ)
        ≤ ∑ i : Fin k, ∑ f' ∈ GoodTuples i, ∑ b ∈ GoodB i (∏ j : Fin k, f' j),
            ((2 * (x : ℝ) / ((Q * b * (∏ j : Fin k, f' j) : ℕ) : ℝ)) * V + E_err) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun f' hf' => Finset.sum_le_sum fun b hb =>
            hcell_bound i f' hf' b hb
      _ = _ := by
          simp_rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun f' _ => ?_
            rw [← mul_assoc, Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            push_cast; ring
          · rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun f' _ => ?_
            rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 4: Bound main sum for each i : Fin k
  have hmain_i : ∀ i : Fin k,
      ∑ f' ∈ GoodTuples i, ((1 : ℝ) / ((∏ j : Fin k, f' j : ℕ) : ℝ)) *
        ∑ b ∈ GoodB i (∏ j : Fin k, f' j), (1 : ℝ) / (b : ℝ) ≤
      (200 / Real.log z) * (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1) := by
    intro i
    have hb_each : ∀ f' ∈ GoodTuples i,
        ∑ b ∈ GoodB i (∏ j : Fin k, f' j), (1 : ℝ) / (b : ℝ) ≤ 200 / Real.log z := by
      intro f' hf'
      set D := ∏ j : Fin k, f' j
      have hDz := (Finset.mem_filter.mp hf').2.2.1
      have hsubB : GoodB i D ⊆ (Finset.Icc (D / (2 * g i.val)) (2 * D / g i.val)).filter
          (fun b => 1 ≤ b ∧ ∀ p : ℕ, p ∈ b.primeFactors → z ≤ (p : ℝ)) := fun b hb => by
        obtain ⟨h1, h2, _, h4⟩ := Finset.mem_filter.mp hb
        exact Finset.mem_filter.mpr ⟨h1, h2, h4⟩
      calc ∑ b ∈ GoodB i D, (1 : ℝ) / (b : ℝ)
          ≤ ∑ b ∈ (Finset.Icc (D / (2 * g i.val)) (2 * D / g i.val)).filter
              (fun b => 1 ≤ b ∧ ∀ p : ℕ, p ∈ b.primeFactors → z ≤ (p : ℝ)), (1 : ℝ) / (b : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubB (fun _ _ _ => by positivity)
        _ ≤ 200 / Real.log z :=
            sum_inv_rough_b_le D (g i.val) z (by have := hg2 i.val i.isLt; omega) hz16 hDz
              (hg_le_z i.val i.isLt)
    have hgt_sub : GoodTuples i ⊆ Fintype.piFinset (fun j : Fin k => if j = i then {1} else Rough) := by
      intro f' hf'
      obtain ⟨hf'pi, hf'i, _, _, _, hf'r⟩ := Finset.mem_filter.mp hf'
      refine Fintype.mem_piFinset.mpr fun j => ?_
      split_ifs with hji
      · rw [Finset.mem_singleton, hji]; exact hf'i
      · exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hf'pi j, hf'r j⟩
    have hprod_sum : ∑ f' ∈ Fintype.piFinset (fun j : Fin k => if j = i then {1} else Rough),
        (1 : ℝ) / ((∏ j : Fin k, f' j : ℕ) : ℝ) =
        (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1) := by
      have hrew : ∀ f' : Fin k → ℕ, (1 : ℝ) / ((∏ j : Fin k, f' j : ℕ) : ℝ) =
          ∏ j : Fin k, (1 : ℝ) / (f' j : ℝ) := fun f' => by
        rw [Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]; simp only [one_div]
      simp_rw [hrew]
      rw [← Finset.prod_univ_sum (t := fun j : Fin k => if j = i then {1} else Rough)
        (f := fun _ d => (1 : ℝ) / (d : ℝ))]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      have hi1 : ∑ d ∈ (if i = i then ({1} : Finset ℕ) else Rough), (1 : ℝ) / (d : ℝ) = 1 := by simp
      rw [hi1, one_mul]
      have hrest : ∏ j ∈ Finset.univ.erase i,
          ∑ d ∈ (if j = i then ({1} : Finset ℕ) else Rough), (1 : ℝ) / (d : ℝ) =
          ∏ _j ∈ Finset.univ.erase i, ∑ d ∈ Rough, (1 : ℝ) / (d : ℝ) :=
        Finset.prod_congr rfl fun j hj => by rw [if_neg (Finset.mem_erase.mp hj).1]
      rw [hrest, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    calc ∑ f' ∈ GoodTuples i, ((1 : ℝ) / ((∏ j : Fin k, f' j : ℕ) : ℝ)) *
            ∑ b ∈ GoodB i (∏ j : Fin k, f' j), (1 : ℝ) / (b : ℝ)
        ≤ ∑ f' ∈ GoodTuples i, ((1 : ℝ) / ((∏ j : Fin k, f' j : ℕ) : ℝ)) * (200 / Real.log z) :=
          Finset.sum_le_sum fun f' hf' =>
            mul_le_mul_of_nonneg_left (hb_each f' hf') (by positivity)
      _ = (200 / Real.log z) * ∑ f' ∈ GoodTuples i, (1 : ℝ) / ((∏ j : Fin k, f' j : ℕ) : ℝ) := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ (200 / Real.log z) * ∑ f' ∈ Fintype.piFinset (fun j : Fin k => if j = i then {1} else Rough),
            (1 : ℝ) / ((∏ j : Fin k, f' j : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hgt_sub (fun _ _ _ => by positivity))
            (by positivity)
      _ = (200 / Real.log z) * (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1) := by rw [hprod_sum]
  -- Step 5: Bound error sum for each i : Fin k
  have herr_i : ∀ i : Fin k,
      ∑ f' ∈ GoodTuples i, ((GoodB i (∏ j : Fin k, f' j)).card : ℝ) ≤
        2 * ((k : ℝ) ^ K * (M_D : ℝ) ^ 2) := by
    intro i
    have hBcard : ∀ f' ∈ GoodTuples i,
        ((GoodB i (∏ j : Fin k, f' j)).card : ℝ) ≤ 2 * ((∏ j : Fin k, f' j : ℕ) : ℝ) := by
      intro f' hf'
      set D := ∏ j : Fin k, f' j
      have hD_pos : 1 ≤ D := Finset.one_le_prod' fun j _ =>
        (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf').1 j)).1
      have hgi2 : 2 ≤ g i.val := hg2 i.val i.isLt
      have hdiv_le : 2 * D / g i.val ≤ D :=
        (Nat.div_le_iff_le_mul_add_pred (by omega)).mpr (by nlinarith)
      have hle : (GoodB i D).card ≤ 2 * D := by
        calc (GoodB i D).card ≤ (Finset.Icc (D / (2 * g i.val)) (2 * D / g i.val)).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = 2 * D / g i.val + 1 - D / (2 * g i.val) := Nat.card_Icc _ _
          _ ≤ 2 * D / g i.val + 1 := Nat.sub_le _ _
          _ ≤ D + 1 := Nat.add_le_add_right hdiv_le 1
          _ ≤ 2 * D := by omega
      exact_mod_cast hle
    have hsubT : GoodTuples i ⊆ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 M_D)).filter
        (fun (f' : Fin k → ℕ) => (∏ j : Fin k, f' j) ≤ M_D ∧
          Pairwise (fun j1 j2 : Fin k => Nat.Coprime (f' j1) (f' j2)) ∧
          ∀ j : Fin k, ∀ p ∈ (f' j).primeFactors, z ≤ (p : ℝ)) := fun f' hf' => by
      obtain ⟨h1, _, _, h4, h5, h6⟩ := Finset.mem_filter.mp hf'
      exact Finset.mem_filter.mpr ⟨h1, h4, h5, h6⟩
    calc ∑ f' ∈ GoodTuples i, ((GoodB i (∏ j : Fin k, f' j)).card : ℝ)
        ≤ ∑ f' ∈ GoodTuples i, 2 * ((∏ j : Fin k, f' j : ℕ) : ℝ) := Finset.sum_le_sum hBcard
      _ = 2 * ∑ f' ∈ GoodTuples i, ((∏ j : Fin k, f' j : ℕ) : ℝ) := (Finset.mul_sum ..).symm
      _ ≤ 2 * ∑ f' ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 M_D)).filter
            (fun (f' : Fin k → ℕ) => (∏ j : Fin k, f' j) ≤ M_D ∧
              Pairwise (fun j1 j2 : Fin k => Nat.Coprime (f' j1) (f' j2)) ∧
              ∀ j : Fin k, ∀ p ∈ (f' j).primeFactors, z ≤ (p : ℝ)),
            ((∏ j : Fin k, f' j : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsubT (fun _ _ _ => by positivity))
            (by norm_num)
      _ ≤ 2 * ((k : ℝ) ^ K * (M_D : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_prod_coprime_rough_tuples_le k M_D K hk z hz_gt1 hMDK)
            (by norm_num)
  -- Step 6: Combine main + error across i : Fin k
  have hmain_total : ∑ i : Fin k, ∑ f' ∈ GoodTuples i,
      ((1 : ℝ) / ((∏ j : Fin k, f' j : ℕ) : ℝ)) *
        ∑ b ∈ GoodB i (∏ j : Fin k, f' j), (1 : ℝ) / (b : ℝ) ≤
      (k : ℝ) * (200 / Real.log z) * (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1) := by
    calc ∑ i : Fin k, _ ≤ ∑ _i : Fin k, ((200 / Real.log z) * (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1)) :=
          Finset.sum_le_sum fun i _ => hmain_i i
      _ = (k : ℝ) * (200 / Real.log z) * (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have herr_total : ∑ i : Fin k, ∑ f' ∈ GoodTuples i, ((GoodB i (∏ j : Fin k, f' j)).card : ℝ) ≤
      2 * (k : ℝ) * ((k : ℝ) ^ K * (M_D : ℝ) ^ 2) := by
    calc ∑ i : Fin k, _ ≤ ∑ _i : Fin k, (2 * ((k : ℝ) ^ K * (M_D : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun i _ => herr_i i
      _ = 2 * (k : ℝ) * ((k : ℝ) ^ K * (M_D : ℝ) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hcomb1 : (2 * (x : ℝ) / (Q : ℝ)) * V *
      (∑ i : Fin k, ∑ f' ∈ GoodTuples i,
        ((1 : ℝ) / ((∏ j : Fin k, f' j : ℕ) : ℝ)) *
          ∑ b ∈ GoodB i (∏ j : Fin k, f' j), (1 : ℝ) / (b : ℝ)) ≤
      (2 * (x : ℝ) / (Q : ℝ)) * V * (k : ℝ) * (200 / Real.log z) *
        (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hmain_total (by positivity : 0 ≤ (2 * (x : ℝ) / (Q : ℝ)) * V)
    linarith
  have hcomb2 : (∑ i : Fin k, ∑ f' ∈ GoodTuples i, ((GoodB i (∏ j : Fin k, f' j)).card : ℝ)) * E_err ≤
      2 * (k : ℝ) * ((k : ℝ) ^ K * (M_D : ℝ) ^ 2) * E_err :=
    mul_le_mul_of_nonneg_right herr_total hE_nn
  linarith

end E387Switch


namespace E387Final

open Finset Filter Real
open scoped Classical

lemma three_pow_ge_200_quad (k : ℕ) (hk : 16 ≤ k) :
    200 * (400 * k ^ 2 + 10) ≤ 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hpow : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
    nlinarith

lemma log_pow_le_rpow_small (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 1 ≤ x) :
    (Real.log x) ^ (6 * k) ≤ ((960 * k : ℝ) ^ (6 * k)) * x ^ (1 / 160 : ℝ) := by
  have hx_pos : 0 < x := by linarith
  have h1 : Real.log (x ^ ((1 : ℝ) / (960 * (k : ℝ)))) ≤ x ^ ((1 : ℝ) / (960 * (k : ℝ))) := by
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx_pos ((1 : ℝ) / (960 * (k : ℝ))))
    linarith
  rw [Real.log_rpow hx_pos] at h1
  have h960_pos : (0 : ℝ) < 960 * (k : ℝ) := by positivity
  have h2 : Real.log x ≤ (960 * (k : ℝ)) * x ^ ((1 : ℝ) / (960 * (k : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_left h1 h960_pos.le
    have hlhs : (960 * (k : ℝ)) * ((1 : ℝ) / (960 * (k : ℝ)) * Real.log x) = Real.log x := by
      field_simp
    linarith
  have hpow := pow_le_pow_left₀ (Real.log_nonneg hx) h2 (6 * k)
  rw [mul_pow] at hpow
  have hrpow : (x ^ ((1 : ℝ) / (960 * (k : ℝ)))) ^ (6 * k) = x ^ (1 / 160 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
    congr 1
    push_cast
    field_simp
    ring
  rwa [hrpow] at hpow

lemma sieveAbs_true_pow_omega_le (k : ℕ) (hk : 1 ≤ k) (β D : ℝ) (hβ : 0 ≤ β) (hD : 1 ≤ D)
    (ps : List ℕ) (hprime : ∀ p ∈ ps, p.Prime) (hdesc : ps.Pairwise (· > ·))
    (hpsD : ∀ p ∈ ps, (p : ℝ) ≤ D) :
    Erdos387GuyH2.sieveAbs true β D ps (fun d => (k : ℝ) ^ d.primeFactors.card) ≤
      (k : ℝ) ^ (k ^ 4) * D * D ^ (1 / 4 : ℝ) := by
  rw [Erdos387GuyH2.sieveAbs_eq_sum_sieveSupp true β D ps _ hprime (Erdos387GuyH2.pairwise_gt_nodup hdesc)]
  have hsub : Erdos387GuyH2.sieveSupp true β D ps ⊆ Finset.Icc 1 ⌊D⌋₊ := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Erdos387GuyH2.mem_sieveSupp_le_D true β D ps hβ hprime hdesc hD (fun _ => hpsD) d hd
    exact Finset.mem_Icc.mpr ⟨hd1, Nat.le_floor hdD⟩
  have hcard : ((Erdos387GuyH2.sieveSupp true β D ps).card : ℝ) ≤ D := by
    have h1 : (Erdos387GuyH2.sieveSupp true β D ps).card ≤ ⌊D⌋₊ := by
      calc (Erdos387GuyH2.sieveSupp true β D ps).card ≤ (Finset.Icc 1 ⌊D⌋₊).card := Finset.card_le_card hsub
        _ = ⌊D⌋₊ := by simp
    exact (by exact_mod_cast h1 : ((Erdos387GuyH2.sieveSupp true β D ps).card : ℝ) ≤ (⌊D⌋₊ : ℝ)).trans
      (Nat.floor_le (by linarith))
  calc ∑ d ∈ Erdos387GuyH2.sieveSupp true β D ps, (k : ℝ) ^ d.primeFactors.card
      ≤ ∑ _d ∈ Erdos387GuyH2.sieveSupp true β D ps, ((k : ℝ) ^ (k ^ 4) * D ^ (1 / 4 : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hd1, hdD⟩ := Erdos387GuyH2.mem_sieveSupp_le_D true β D ps hβ hprime hdesc hD (fun _ => hpsD) d hd
        exact (Erdos387GuyH2.pow_omega_le k d hk hd1).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hdD (by norm_num)) (by positivity))
    _ = ((Erdos387GuyH2.sieveSupp true β D ps).card : ℝ) * ((k : ℝ) ^ (k ^ 4) * D ^ (1 / 4 : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ D * ((k : ℝ) ^ (k ^ 4) * D ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (k : ℝ) ^ (k ^ 4) * D * D ^ (1 / 4 : ℝ) := by ring

end E387Final

set_option maxHeartbeats 1600000 in
theorem OMA.solution : OMA.R_Erdos387_erdos_387_variants_guy_R1_H3_R1.H1 := by
  classical
  rw [OMA.R_Erdos387_erdos_387_variants_guy_R1_H3_R1.H1]
  refine Filter.eventually_atTop.mpr ⟨16, ?_⟩
  intro k hk16 γ g ⟨hg2, hfact, hcover⟩
  have hk : 12 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  let Q : ℕ := ∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1)
  have hQ_pos : 0 < Q := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Nat.mem_primesLE.mp hp).2.pos _
  have hQ_primes : ∀ p ∈ Q.primeFactors, p ≤ 2 * k := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hpdvd
    obtain ⟨hqle, hqp⟩ := Nat.mem_primesLE.mp hq
    have heq := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp (hpp.dvd_of_dvd_pow hpq)
    omega
  have hQ_cop : ∀ q : ℕ, q.Prime → 2 * k < q → Nat.Coprime Q q := by
    intro q hq hqk
    apply Nat.Coprime.prod_left
    intro p hp
    obtain ⟨hple, hp_prime⟩ := Nat.mem_primesLE.mp hp
    exact ((Nat.coprime_primes hp_prime hq).mpr (by omega)).pow_left _
  let w : ℕ := ⌈Real.exp ((1000 : ℝ) * k)⌉₊ + 2 * k + 1
  have hw_gt : 2 * k < w := by omega
  have hlogw : (1000 : ℝ) * k ≤ Real.log (w : ℝ) := by
    have hexp_le : Real.exp ((1000 : ℝ) * k) ≤ (w : ℝ) := by
      have h1 : Real.exp ((1000 : ℝ) * k) ≤ (⌈Real.exp ((1000 : ℝ) * k)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈Real.exp ((1000 : ℝ) * k)⌉₊ : ℝ) ≤ (w : ℝ) := by
        exact_mod_cast (by omega : ⌈Real.exp ((1000 : ℝ) * k)⌉₊ ≤ w)
      linarith
    calc (1000 : ℝ) * k = Real.log (Real.exp ((1000 : ℝ) * k)) := (Real.log_exp _).symm
      _ ≤ Real.log (w : ℝ) := Real.log_le_log (Real.exp_pos _) hexp_le
  let smallPrimes : Finset ℕ := (Finset.Ioc (2 * k) w).filter Nat.Prime
  let Psmall : ℕ := ∏ p ∈ smallPrimes, p
  have hPsmall_pos : 0 < Psmall :=
    Finset.prod_pos (fun _ hp => (Finset.mem_filter.mp hp).2.pos)
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
  have hgi_le_fac : ∀ i < k, g i ≤ k.factorial := fun i hi =>
    Nat.le_of_dvd (Nat.factorial_pos k) (hfact ▸ Finset.dvd_prod_of_mem g (Finset.mem_range.mpr hi))
  let C_rem : ℝ := 8 * (Q' : ℝ) * (k : ℝ) ^ (k ^ 4) * ((24 * k : ℝ) ^ (6 * k))
  let C_rough : ℝ := 2 * (2 * (3 : ℝ) ^ k) ^ 6
  let C_main : ℝ := 64000 * (Psmall : ℝ) * (k : ℝ) * ((3 : ℝ) ^ k) * C_rough ^ (k - 1)
  let C_err : ℝ := 5760 * (Q' : ℝ) * (k : ℝ) * ((k : ℝ) ^ (3 ^ k)) * ((k : ℝ) ^ (k ^ 4)) * ((960 * k : ℝ) ^ (6 * k))
  let z_floor_need : ℝ := max ((w : ℝ) + 2) (max ((16 : ℝ) ^ 16) ((2 * (k.factorial : ℝ)) ^ 2 + 2))
  let x0 : ℕ := max (2 * k + 100)
    (max (⌈z_floor_need ^ ((3 : ℝ) ^ k)⌉₊ + 2)
      (max (⌈(C_rem + 1) ^ (8 : ℕ)⌉₊ + 2)
        (max (⌈Real.exp (C_main + 1)⌉₊ + 2)
          (max (⌈(C_err + 1) ^ (200 : ℕ)⌉₊ + 2) (10 ^ 10)))))
  refine Filter.eventually_atTop.mpr ⟨x0, ?_⟩
  intro x hx
  intro S
  have h2kx : 2 * k < x := by
    have : 2 * k + 100 ≤ x0 := le_max_left _ _
    omega
  have hkx : k < x := by omega
  have hx10 : 10 ^ 10 ≤ x := by
    have : 10 ^ 10 ≤ x0 := le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
    omega
  have hx_pos : (0 : ℝ) < x := by positivity
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  let β : ℝ := (400 : ℝ) * (k : ℝ) ^ 2
  let z : ℝ := (x : ℝ) ^ ((3 : ℝ) ^ k)⁻¹
  have hz_pos : 0 < z := Real.rpow_pos_of_pos hx_pos _
  have hz_ge_need : z_floor_need ≤ z := by
    have h1 : z_floor_need ^ ((3 : ℝ) ^ k) ≤ (x : ℝ) := by
      have hle : ⌈z_floor_need ^ ((3 : ℝ) ^ k)⌉₊ ≤ x := by
        have : ⌈z_floor_need ^ ((3 : ℝ) ^ k)⌉₊ + 2 ≤ x0 :=
          le_trans (le_max_left _ _) (le_max_right _ _)
        omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast hle)
    have hnn : 0 ≤ z_floor_need := le_trans (by positivity : (0 : ℝ) ≤ (w : ℝ) + 2) (le_max_left _ _)
    have h3k_pos : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    calc z_floor_need = (z_floor_need ^ ((3 : ℝ) ^ k)) ^ ((3 : ℝ) ^ k)⁻¹ := by
          rw [← Real.rpow_mul hnn, mul_inv_cancel₀ h3k_pos.ne', Real.rpow_one]
      _ ≤ z := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) h1 (by positivity)
  have hz_gt_w2 : (w : ℝ) + 2 ≤ z := le_trans (le_max_left _ _) hz_ge_need
  have hz_gt_w : (w : ℝ) < z := by linarith
  have hz16 : (16 : ℝ) ^ 16 ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hz_ge_need
  have hz_fac : (2 * (k.factorial : ℝ)) ^ 2 + 2 ≤ z :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hz_ge_need
  have hz2k : 2 * (k : ℝ) < z := by
    have : 2 * (k : ℝ) < (w : ℝ) := by exact_mod_cast hw_gt
    linarith
  have hgi_le_z : ∀ i < k, 2 * (g i : ℝ) ≤ z ^ (1 / 2 : ℝ) := by
    intro i hi
    have h1 : 2 * (g i : ℝ) ≤ 2 * (k.factorial : ℝ) := by
      have := hgi_le_fac i hi; exact_mod_cast (by omega : 2 * g i ≤ 2 * k.factorial)
    have h2 : (2 * (k.factorial : ℝ)) ^ 2 ≤ z := by linarith
    have h3 : 2 * (k.factorial : ℝ) ≤ z ^ (1 / 2 : ℝ) := by
      calc 2 * (k.factorial : ℝ) = ((2 * (k.factorial : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_mul (by positivity)]; norm_num
        _ = ((2 * (k.factorial : ℝ)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        _ ≤ z ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    linarith
  have hlogz_eq : Real.log z = ((3 : ℝ) ^ k)⁻¹ * Real.log (x : ℝ) := Real.log_rpow hx_pos _
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
  let V : ℝ := Erdos387GuyH2.prodV k ps
  have hV_pos : 0 < V := Erdos387GuyH2.prodV_pos k ps (fun p hp => by have := (hps_props p hp).2.1; omega)
  -- Step A: Lower bound on S.card ≥ (x / (4 * Q')) * V, and V ≥ 1 / (2 * (log x)^(6 * k))
  let D_S : ℝ := Real.sqrt (x : ℝ)
  have hDS_pos : 0 < D_S := Real.sqrt_pos.mpr hx_pos
  have hDS1 : 1 ≤ D_S := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx1
  have hz_le_DS : z ≤ D_S := by
    rw [show D_S = (x : ℝ) ^ (1 / 2 : ℝ) by dsimp only [D_S]; rw [Real.sqrt_eq_rpow]]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    have h3k : (2 : ℝ) ≤ (3 : ℝ) ^ k := by
      exact_mod_cast (show 2 ≤ 3 ^ k from le_trans (by norm_num : 2 ≤ 3 ^ 1) (Nat.pow_le_pow_right (by norm_num) hk1))
    rw [one_div]; exact inv_anti₀ (by norm_num) h3k
  have hsDS_eq : Real.log D_S / Real.log z = (3 : ℝ) ^ k / 2 := by
    have hlogDS : Real.log D_S = (1 / 2 : ℝ) * Real.log (x : ℝ) := by
      rw [show D_S = (x : ℝ) ^ (1 / 2 : ℝ) by dsimp only [D_S]; rw [Real.sqrt_eq_rpow], Real.log_rpow hx_pos _]
    rw [hlogDS, hlogz_eq]
    have h3k0 : (3 : ℝ) ^ k ≠ 0 := by positivity
    field_simp [hlogx_pos.ne']
  have hsDS_ge : β + 10 ≤ Real.log D_S / Real.log z := by
    rw [hsDS_eq]
    have hqr : (800 : ℝ) * (k : ℝ) ^ 2 + 20 ≤ (3 : ℝ) ^ k := by exact_mod_cast Erdos387GuyH2.three_pow_ge_quad k hk
    dsimp only [β]; linarith
  have hV_lb : 1 / (2 * (Real.log (x : ℝ)) ^ (6 * k)) ≤ V := by
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
      have hinv_le : ((3 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_pow k 3 (by norm_num))
      nlinarith
    have hfrac_le : Real.log z / Real.log (w : ℝ) ≤ Real.log (x : ℝ) :=
      (div_le_div_of_nonneg_left (by rw [hlogz_eq]; positivity) zero_lt_one hlogw_ge1).trans
        (by rw [div_one]; exact hlogz_le_logx)
    have hpow_le : (Real.log z / Real.log (w : ℝ)) ^ (6 * k) ≤ (Real.log (x : ℝ)) ^ (6 * k) :=
      pow_le_pow_left₀ (by rw [hlogz_eq]; positivity) hfrac_le _
    have h1 : (1 : ℝ) ≤ 2 * (Real.log (x : ℝ)) ^ (6 * k) * V := by
      have h2 : (102 / 100 : ℝ) * (Real.log z / Real.log (w : ℝ)) ^ (6 * k) ≤
          2 * (Real.log (x : ℝ)) ^ (6 * k) := by
        have : 0 ≤ (Real.log (x : ℝ)) ^ (6 * k) := by positivity
        nlinarith
      exact hrat.trans (mul_le_mul_of_nonneg_right h2 hV_pos.le)
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hS_lb : ((x : ℝ) / (4 * (Q' : ℝ))) * V ≤ (S.card : ℝ) := by
    have hmain_err := (Erdos387GuyH2.sieve_main_bound k w hk hw_gt hlogw ps.length ps le_rfl hps_desc
      (fun p hp => ⟨(hps_props p hp).1, (hps_props p hp).2.1⟩) z D_S hDS_pos hz_gt_w hps_le_z).2 (by linarith)
    have hphi_le_half : Erdos387GuyH2.phiSieve β (Real.log D_S / Real.log z) ≤ 1 / 2 := by
      dsimp only [Erdos387GuyH2.phiSieve]
      have hexp_le : Real.exp ((β + 2 - Real.log D_S / Real.log z) / 2) ≤ Real.exp (-1 : ℝ) :=
        Real.exp_le_exp.mpr (by linarith)
      have he1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      exact hexp_le.trans he1
    have hVneg_ge : (1 / 2 : ℝ) * V ≤ Erdos387GuyH2.sieveSum false β D_S ps (Erdos387GuyH2.multG k) := by
      have : V * Erdos387GuyH2.phiSieve β (Real.log D_S / Real.log z) ≤ (1 / 2 : ℝ) * V := by nlinarith
      linarith
    let A' : Finset ℕ := (Finset.Ioc x (2 * x)).filter (fun n => n ≡ γ' [MOD Q'])
    let S' : Finset ℕ := A'.filter (fun n => ∀ p ∈ ps, ¬ (n % p < k))
    have hS'_sub : S' ⊆ S := by
      intro n hn
      obtain ⟨hnA', hnps⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnI, hnQ'⟩ := Finset.mem_filter.mp hnA'
      refine Finset.mem_filter.mpr ⟨hnI, (hnQ'.of_dvd (dvd_mul_right Q Psmall)).trans hγ'_Q, ?_⟩
      intro p hp hpdvd
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
    let ind : ℕ → ℕ → ℝ := fun n d => if ∀ q ∈ d.primeFactors, n % q < k then 1 else 0
    let f : ℕ → ℝ := fun d => ∑ n ∈ A', ind n d
    let R : ℕ → ℝ := fun d => f d - ((x : ℝ) / (Q' : ℝ)) * Erdos387GuyH2.multG k d
    have hS'_ge : Erdos387GuyH2.sieveSum false β D_S ps f ≤ (S'.card : ℝ) := by
      rw [show Erdos387GuyH2.sieveSum false β D_S ps f = ∑ n ∈ A', Erdos387GuyH2.sieveSum false β D_S ps (ind n) from
        Erdos387GuyH2.sieveSum_finset_sum A' false β D_S ps ind]
      calc ∑ n ∈ A', Erdos387GuyH2.sieveSum false β D_S ps (ind n)
          ≤ ∑ n ∈ A', (if ∀ p ∈ ps, ¬ (n % p < k) then (1 : ℝ) else 0) :=
            Finset.sum_le_sum fun n _ => by
              have hind := (Erdos387GuyH2.sieveSum_indicator β ps (fun q => n % q < k) hps_prime hps_nd).2 D_S
              calc Erdos387GuyH2.sieveSum false β D_S ps (ind n)
                  = _ := by congr 1; funext d; dsimp only [ind]; split_ifs <;> rfl
                _ ≤ _ := hind
                _ = (if ∀ p ∈ ps, ¬ (n % p < k) then (1 : ℝ) else 0) := by split_ifs <;> rfl
        _ = (S'.card : ℝ) := by simp [S', Finset.sum_boole]
    have hdecomp : Erdos387GuyH2.sieveSum false β D_S ps f =
        ((x : ℝ) / (Q' : ℝ)) * Erdos387GuyH2.sieveSum false β D_S ps (Erdos387GuyH2.multG k) +
        Erdos387GuyH2.sieveSum false β D_S ps R := by
      have hf_eq : f = fun d => ((x : ℝ) / (Q' : ℝ)) * Erdos387GuyH2.multG k d + R d := by
        ext d; dsimp only [R]; ring
      rw [hf_eq, Erdos387GuyH2.sieveSum_add, Erdos387GuyH2.sieveSum_smul]
    have hR_bound : |Erdos387GuyH2.sieveSum false β D_S ps R| ≤ (k : ℝ) ^ (k ^ 4) * D_S * D_S ^ (1 / 4 : ℝ) := by
      have h1 := Erdos387GuyH2.abs_sieveSum_le false β D_S ps R
      rw [Erdos387GuyH2.sieveAbs_eq_sum_sieveSupp false β D_S ps _ hps_prime hps_nd] at h1
      have h2 : ∑ d ∈ Erdos387GuyH2.sieveSupp false β D_S ps, |R d| ≤
          ∑ d ∈ Erdos387GuyH2.sieveSupp false β D_S ps, (k : ℝ) ^ d.primeFactors.card := by
        refine Finset.sum_le_sum fun d hd => ?_
        obtain ⟨_, hd_pf⟩ := Erdos387GuyH2.mem_sieveSupp_props false β D_S ps hps_prime d hd
        have hf_eq : f d = (((Finset.Ioc x (2 * x)).filter
            (fun n => n ≡ γ' [MOD Q'] ∧ ∀ p ∈ d.primeFactors, n % p < k)).card : ℝ) := by
          dsimp only [f, ind, A']; rw [Finset.sum_boole, Finset.filter_filter]
        dsimp only [R]; rw [hf_eq]
        exact Erdos387GuyH2.crt_count_Ioc x Q' γ' k d hQ'_pos hk1 fun p hp => by
          obtain ⟨hp_prime, hpw, _⟩ := hps_props p (hd_pf p hp)
          exact ⟨hp_prime, by omega, hQ'_cop p hp_prime hpw⟩
      rw [← Erdos387GuyH2.sieveAbs_eq_sum_sieveSupp false β D_S ps
          (fun d => (k : ℝ) ^ d.primeFactors.card) hps_prime hps_nd] at h2
      exact (h1.trans h2).trans
        (Erdos387GuyH2.sieveAbs_pow_omega_le k hk1 β D_S (by positivity) hDS1 ps hps_prime hps_desc
          (fun p hp => (hps_le_z p hp).trans hz_le_DS))
    have hrem_small : (k : ℝ) ^ (k ^ 4) * D_S * D_S ^ (1 / 4 : ℝ) ≤ ((x : ℝ) / (4 * (Q' : ℝ))) * V := by
      have hD_rpow : D_S * D_S ^ (1 / 4 : ℝ) = (x : ℝ) ^ (5 / 8 : ℝ) := by
        rw [show D_S = (x : ℝ) ^ (1 / 2 : ℝ) by dsimp only [D_S]; rw [Real.sqrt_eq_rpow],
          ← Real.rpow_mul hx_pos.le, ← Real.rpow_add hx_pos]
        congr 1; norm_num
      rw [mul_assoc, hD_rpow]
      have hC_lt : C_rem < (x : ℝ) ^ (1 / 8 : ℝ) := by
        have hle : ⌈(C_rem + 1) ^ (8 : ℕ)⌉₊ ≤ x := by
          have : ⌈(C_rem + 1) ^ (8 : ℕ)⌉₊ + 2 ≤ x0 :=
            le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
          omega
        have hpow : (C_rem + 1) ^ (8 : ℕ) ≤ (x : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hle)
        have h1 : C_rem + 1 ≤ (x : ℝ) ^ (1 / 8 : ℝ) := by
          calc C_rem + 1 = ((C_rem + 1) ^ (8 : ℝ)) ^ (1 / 8 : ℝ) := by
                rw [← Real.rpow_mul (by positivity)]; norm_num
            _ = ((C_rem + 1) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) := by
                rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            _ ≤ (x : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (by positivity) hpow (by norm_num)
        linarith
      have hlog_bd := Erdos387GuyH2.log_pow_le_rpow k hk1 (x : ℝ) hx1
      have hprod_lt : 8 * (Q' : ℝ) * (k : ℝ) ^ (k ^ 4) * (Real.log (x : ℝ)) ^ (6 * k) * (x : ℝ) ^ (5 / 8 : ℝ) < (x : ℝ) := by
        have h1 : 8 * (Q' : ℝ) * (k : ℝ) ^ (k ^ 4) * (Real.log (x : ℝ)) ^ (6 * k) * (x : ℝ) ^ (5 / 8 : ℝ) ≤
            C_rem * (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (5 / 8 : ℝ) := by
          have hrew : C_rem * (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (5 / 8 : ℝ) =
              (8 * (Q' : ℝ) * (k : ℝ) ^ (k ^ 4)) * (((24 * k : ℝ) ^ (6 * k)) * (x : ℝ) ^ (1 / 4 : ℝ)) *
                (x : ℝ) ^ (5 / 8 : ℝ) := by dsimp only [C_rem]; ring
          rw [hrew]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_bd (by positivity)) (by positivity)
        have h2 : C_rem * (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (5 / 8 : ℝ) <
            (x : ℝ) ^ (1 / 8 : ℝ) * (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (5 / 8 : ℝ) :=
          mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hC_lt (by positivity)) (by positivity)
        have h3 : (x : ℝ) ^ (1 / 8 : ℝ) * (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (5 / 8 : ℝ) = (x : ℝ) := by
          rw [← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos]; norm_num
        linarith
      have hmid : (k : ℝ) ^ (k ^ 4) * (x : ℝ) ^ (5 / 8 : ℝ) ≤
          ((x : ℝ) / (4 * (Q' : ℝ))) * (1 / (2 * (Real.log (x : ℝ)) ^ (6 * k))) := by
        rw [show ((x : ℝ) / (4 * (Q' : ℝ))) * (1 / (2 * (Real.log (x : ℝ)) ^ (6 * k))) =
            (x : ℝ) / (8 * (Q' : ℝ) * (Real.log (x : ℝ)) ^ (6 * k)) by ring,
          le_div_iff₀ (by positivity)]
        linarith
      exact hmid.trans (mul_le_mul_of_nonneg_left hV_lb (by positivity))
    have hcard_le : (S'.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hS'_sub
    have hmain_lb : ((x : ℝ) / (2 * (Q' : ℝ))) * V ≤
        ((x : ℝ) / (Q' : ℝ)) * Erdos387GuyH2.sieveSum false β D_S ps (Erdos387GuyH2.multG k) := by
      have : ((x : ℝ) / (2 * (Q' : ℝ))) * V = ((x : ℝ) / (Q' : ℝ)) * ((1 / 2 : ℝ) * V) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hVneg_ge (by positivity)
    have hR_neg : -((k : ℝ) ^ (k ^ 4) * D_S * D_S ^ (1 / 4 : ℝ)) ≤ Erdos387GuyH2.sieveSum false β D_S ps R :=
      (abs_le.mp hR_bound).1
    have hhalf : ((x : ℝ) / (2 * (Q' : ℝ))) * V - ((x : ℝ) / (4 * (Q' : ℝ))) * V =
        ((x : ℝ) / (4 * (Q' : ℝ))) * V := by ring
    linarith
  -- Step B: Upper-bound sieve for arbitrary progression (Q1, γ1) with D_E = x^(1/200)
  let D_E : ℝ := (x : ℝ) ^ (1 / 200 : ℝ)
  have hDE_pos : 0 < D_E := Real.rpow_pos_of_pos hx_pos _
  have hDE1 : 1 ≤ D_E := Real.one_le_rpow hx1 (by norm_num)
  have hz_le_DE : z ≤ D_E := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    have h3k : (200 : ℝ) ≤ (3 : ℝ) ^ k := by
      have := E387Final.three_pow_ge_200_quad k hk16
      exact_mod_cast (show 200 ≤ 3 ^ k by nlinarith)
    rw [one_div]; exact inv_anti₀ (by norm_num) h3k
  have hsDE_eq : Real.log D_E / Real.log z = (3 : ℝ) ^ k / 200 := by
    rw [Real.log_rpow hx_pos _, hlogz_eq]
    have h3k0 : (3 : ℝ) ^ k ≠ 0 := by positivity
    field_simp [hlogx_pos.ne']
  have hsDE_ge : β + 10 ≤ Real.log D_E / Real.log z := by
    rw [hsDE_eq]
    have hqr : 200 * (400 * (k : ℝ) ^ 2 + 10) ≤ (3 : ℝ) ^ k := by
      exact_mod_cast E387Final.three_pow_ge_200_quad k hk16
    dsimp only [β]; linarith
  have hVpos_le : Erdos387GuyH2.sieveSum true β D_E ps (Erdos387GuyH2.multG k) ≤ 2 * V := by
    have hmain_err := (Erdos387GuyH2.sieve_main_bound k w hk hw_gt hlogw ps.length ps le_rfl hps_desc
      (fun p hp => ⟨(hps_props p hp).1, (hps_props p hp).2.1⟩) z D_E hDE_pos hz_gt_w hps_le_z).1 (by linarith)
    have hphi_le1 : Erdos387GuyH2.phiSieve β (Real.log D_E / Real.log z) ≤ 1 := by
      dsimp only [Erdos387GuyH2.phiSieve]
      exact Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  have hDE_rpow : D_E * D_E ^ (1 / 4 : ℝ) = (x : ℝ) ^ (1 / 160 : ℝ) := by
    dsimp only [D_E]
    rw [← Real.rpow_mul hx_pos.le, ← Real.rpow_add hx_pos]
    congr 1; norm_num
  have hsieve_upper : ∀ (Q1 γ1 : ℕ), 0 < Q1 → (∀ p ∈ ps, Nat.Coprime Q1 p) →
      (((Finset.Ioc x (2 * x)).filter
        (fun n => n ≡ γ1 [MOD Q1] ∧ ∀ p ∈ ps, ¬ (n % p < k))).card : ℝ) ≤
      (2 * (x : ℝ) / (Q1 : ℝ)) * V + (k : ℝ) ^ (k ^ 4) * (x : ℝ) ^ (1 / 160 : ℝ) := by
    intro Q1 γ1 hQ1 hQ1_cop
    let A1 : Finset ℕ := (Finset.Ioc x (2 * x)).filter (fun n => n ≡ γ1 [MOD Q1])
    let ind : ℕ → ℕ → ℝ := fun n d => if ∀ q ∈ d.primeFactors, n % q < k then 1 else 0
    let f1 : ℕ → ℝ := fun d => ∑ n ∈ A1, ind n d
    let R1 : ℕ → ℝ := fun d => f1 d - ((x : ℝ) / (Q1 : ℝ)) * Erdos387GuyH2.multG k d
    have hfilt_eq : (Finset.Ioc x (2 * x)).filter (fun n => n ≡ γ1 [MOD Q1] ∧ ∀ p ∈ ps, ¬ (n % p < k)) =
        A1.filter (fun n => ∀ p ∈ ps, ¬ (n % p < k)) := by
      simp [A1, Finset.filter_filter]
    rw [hfilt_eq]
    have hle_sieve : ((A1.filter (fun n => ∀ p ∈ ps, ¬ (n % p < k))).card : ℝ) ≤
        Erdos387GuyH2.sieveSum true β D_E ps f1 := by
      rw [show Erdos387GuyH2.sieveSum true β D_E ps f1 = ∑ n ∈ A1, Erdos387GuyH2.sieveSum true β D_E ps (ind n) from
        Erdos387GuyH2.sieveSum_finset_sum A1 true β D_E ps ind]
      calc ((A1.filter (fun n => ∀ p ∈ ps, ¬ (n % p < k))).card : ℝ)
          = ∑ n ∈ A1, (if ∀ p ∈ ps, ¬ (n % p < k) then (1 : ℝ) else 0) := by simp [Finset.sum_boole]
        _ ≤ ∑ n ∈ A1, Erdos387GuyH2.sieveSum true β D_E ps (ind n) :=
            Finset.sum_le_sum fun n _ => by
              convert (Erdos387GuyH2.sieveSum_indicator β ps (fun q => n % q < k) hps_prime hps_nd).1 D_E
              rfl
    have hdecomp1 : Erdos387GuyH2.sieveSum true β D_E ps f1 =
        ((x : ℝ) / (Q1 : ℝ)) * Erdos387GuyH2.sieveSum true β D_E ps (Erdos387GuyH2.multG k) +
        Erdos387GuyH2.sieveSum true β D_E ps R1 := by
      have hf1 : f1 = fun d => ((x : ℝ) / (Q1 : ℝ)) * Erdos387GuyH2.multG k d + R1 d := by
        ext d; dsimp only [R1]; ring
      rw [hf1, Erdos387GuyH2.sieveSum_add, Erdos387GuyH2.sieveSum_smul]
    have hR1_bound : |Erdos387GuyH2.sieveSum true β D_E ps R1| ≤ (k : ℝ) ^ (k ^ 4) * (x : ℝ) ^ (1 / 160 : ℝ) := by
      have h1 := Erdos387GuyH2.abs_sieveSum_le true β D_E ps R1
      rw [Erdos387GuyH2.sieveAbs_eq_sum_sieveSupp true β D_E ps _ hps_prime hps_nd] at h1
      have h2 : ∑ d ∈ Erdos387GuyH2.sieveSupp true β D_E ps, |R1 d| ≤
          ∑ d ∈ Erdos387GuyH2.sieveSupp true β D_E ps, (k : ℝ) ^ d.primeFactors.card := by
        refine Finset.sum_le_sum fun d hd => ?_
        obtain ⟨_, hd_pf⟩ := Erdos387GuyH2.mem_sieveSupp_props true β D_E ps hps_prime d hd
        have hf_eq : f1 d = (((Finset.Ioc x (2 * x)).filter
            (fun n => n ≡ γ1 [MOD Q1] ∧ ∀ p ∈ d.primeFactors, n % p < k)).card : ℝ) := by
          dsimp only [f1, ind, A1]; rw [Finset.sum_boole, Finset.filter_filter]
        dsimp only [R1]; rw [hf_eq]
        exact Erdos387GuyH2.crt_count_Ioc x Q1 γ1 k d hQ1 hk1 fun p hp => by
          obtain ⟨hp_prime, hpw, _⟩ := hps_props p (hd_pf p hp)
          exact ⟨hp_prime, by omega, hQ1_cop p (hd_pf p hp)⟩
      rw [← Erdos387GuyH2.sieveAbs_eq_sum_sieveSupp true β D_E ps
          (fun d => (k : ℝ) ^ d.primeFactors.card) hps_prime hps_nd] at h2
      have h3 := (h1.trans h2).trans
        (E387Final.sieveAbs_true_pow_omega_le k hk1 β D_E (by positivity) hDE1 ps hps_prime hps_desc
          (fun p hp => (hps_le_z p hp).trans hz_le_DE))
      rwa [mul_assoc, hDE_rpow] at h3
    have hmain1 : ((x : ℝ) / (Q1 : ℝ)) * Erdos387GuyH2.sieveSum true β D_E ps (Erdos387GuyH2.multG k) ≤
        (2 * (x : ℝ) / (Q1 : ℝ)) * V := by
      have : (2 * (x : ℝ) / (Q1 : ℝ)) * V = ((x : ℝ) / (Q1 : ℝ)) * (2 * V) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hVpos_le (by positivity)
    have hR1_pos := (abs_le.mp hR1_bound).2
    linarith
  -- Step C: Apply E1_card_le_from_sieve with K = 3 ^ k
  let M_D : ℕ := ⌈2 * (x : ℝ) ^ (49 / 100 : ℝ)⌉₊
  have hMD_le_3 : (M_D : ℝ) ≤ 3 * (x : ℝ) ^ (49 / 100 : ℝ) := by
    have h1 : (M_D : ℝ) < 2 * (x : ℝ) ^ (49 / 100 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ (x : ℝ) ^ (49 / 100 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    linarith
  have hMD_le_x : (M_D : ℝ) ≤ (x : ℝ) := by
    have h1 : (3 : ℝ) ≤ (x : ℝ) ^ (51 / 100 : ℝ) := by
      have hx_big : (10 ^ 10 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx10
      calc (3 : ℝ) ≤ (10 ^ 10 : ℝ) ^ (51 / 100 : ℝ) := by
            have : (3 : ℝ) ^ (100 : ℕ) ≤ (10 ^ 10 : ℝ) ^ (51 : ℕ) := by norm_num
            calc (3 : ℝ) = ((3 : ℝ) ^ (100 : ℝ)) ^ (1 / 100 : ℝ) := by
                  rw [← Real.rpow_mul (by norm_num)]; norm_num
              _ = ((3 : ℝ) ^ (100 : ℕ)) ^ (1 / 100 : ℝ) := by
                  rw [show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
              _ ≤ ((10 ^ 10 : ℝ) ^ (51 : ℕ)) ^ (1 / 100 : ℝ) :=
                  Real.rpow_le_rpow (by positivity) this (by norm_num)
              _ = (10 ^ 10 : ℝ) ^ (51 / 100 : ℝ) := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ (x : ℝ) ^ (51 / 100 : ℝ) := Real.rpow_le_rpow (by positivity) hx_big (by norm_num)
    calc (M_D : ℝ) ≤ 3 * (x : ℝ) ^ (49 / 100 : ℝ) := hMD_le_3
      _ ≤ (x : ℝ) ^ (51 / 100 : ℝ) * (x : ℝ) ^ (49 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (x : ℝ) := by rw [← Real.rpow_add hx_pos]; norm_num
  have hMDK : (M_D : ℝ) ≤ z ^ (3 ^ k) := by
    have hzpow : z ^ (3 ^ k) = (x : ℝ) := by
      dsimp only [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
      have h3k0 : (3 : ℝ) ^ k ≠ 0 := by positivity
      have hcast : ((3 ^ k : ℕ) : ℝ) = (3 : ℝ) ^ k := by push_cast; rfl
      rw [hcast, inv_mul_cancel₀ h3k0, Real.rpow_one]
    rw [hzpow]; exact hMD_le_x
  have hE1_bd := E387Switch.E1_card_le_from_sieve k x Q γ (3 ^ k) g ps z V
    ((k : ℝ) ^ (k ^ 4) * (x : ℝ) ^ (1 / 160 : ℝ)) hk1 hQ_pos h2kx hz16 hz2k hg2 hfact hgi_le_z
    hQ_primes (fun p hp => ⟨(hps_props p hp).1, by have := (hps_props p hp).2.1; omega, (hps_props p hp).2.2⟩)
    (fun n hnI hnQ => (hcover n (lt_trans hkx (Finset.mem_Ioc.mp hnI).1) hnQ).1)
    hV_pos.le (by positivity) hMDK hsieve_upper
  -- Step D: Bound Rough sum ≤ C_rough
  let Rough := (Finset.Icc 1 M_D).filter (fun d => ∀ p : ℕ, p ∈ d.primeFactors → z ≤ (p : ℝ))
  have hRough_le : ∑ d ∈ Rough, (1 : ℝ) / (d : ℝ) ≤ C_rough := by
    let a_lo : ℕ := Nat.floor z - 1
    have ha_ge_w : w ≤ a_lo := by
      have : w + 2 ≤ Nat.floor z := Nat.le_floor (by exact_mod_cast hz_gt_w2)
      omega
    have ha_gt2 : 2 * 1 < a_lo := by omega
    have hloga : (1000 : ℝ) * (1 : ℕ) ≤ Real.log (a_lo : ℝ) := by
      have hw_le_a : (w : ℝ) ≤ (a_lo : ℝ) := by exact_mod_cast ha_ge_w
      have h1 : (1000 : ℝ) * (1 : ℕ) ≤ (1000 : ℝ) * (k : ℝ) := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        push_cast; nlinarith
      exact h1.trans (hlogw.trans (Real.log_le_log (by positivity) hw_le_a))
    by_cases ha_le_MD : a_lo ≤ M_D
    · let Pbig : Finset ℕ := (Finset.Ioc a_lo M_D).filter Nat.Prime
      have hRough_sub : Rough ⊆ (Finset.Icc 1 M_D).filter (fun d => d.primeFactors ⊆ Pbig) := by
        intro d hd
        obtain ⟨hdI, hrough⟩ := Finset.mem_filter.mp hd
        refine Finset.mem_filter.mpr ⟨hdI, fun p hp => ?_⟩
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hp_le_MD : p ≤ M_D := (Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hdI).1; omega)
          (Nat.dvd_of_mem_primeFactors hp)).trans (Finset.mem_Icc.mp hdI).2
        have hp_gt_a : a_lo < p := by
          have hpz := hrough p hp
          have hfl : (Nat.floor z : ℝ) ≤ z := Nat.floor_le hz_pos.le
          have hp_ge_fl : Nat.floor z ≤ p := Nat.floor_le_of_le hpz
          have hfl2 : 2 ≤ Nat.floor z := by omega
          omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp_gt_a, hp_le_MD⟩, hpp⟩
      have h1 := (Finset.sum_le_sum_of_subset_of_nonneg hRough_sub (fun _ _ _ => by positivity)).trans
        (E387Selberg.sum_inv_primeFactors_subset_le Pbig (fun _ hp => (Finset.mem_filter.mp hp).2) M_D)
      have h2 := Erdos387GuyH2.prod_inv_one_sub_le 1 a_lo M_D le_rfl ha_gt2 ha_le_MD hloga Pbig Finset.Subset.rfl
      simp only [Nat.cast_one, mul_one] at h2
      have hza : z / 2 ≤ (a_lo : ℝ) := by
        have hfl : z - 1 < (Nat.floor z : ℝ) := Nat.sub_one_lt_floor z
        have hfl2 : 2 ≤ Nat.floor z := by omega
        have hcast : (a_lo : ℝ) = (Nat.floor z : ℝ) - 1 := by
          dsimp only [a_lo]; rw [Nat.cast_sub (by omega), Nat.cast_one]
        have hz4 : (4 : ℝ) ≤ z := by linarith [show (4 : ℝ) ≤ (16 : ℝ) ^ 16 by norm_num]
        linarith
      have hlog_ratio : Real.log (M_D : ℝ) / Real.log (a_lo : ℝ) ≤ 2 * (3 : ℝ) ^ k := by
        have hloga_pos : 0 < Real.log (a_lo : ℝ) := by push_cast at hloga; linarith
        have hlogMD_le : Real.log (M_D : ℝ) ≤ Real.log (x : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < M_D)) hMD_le_x
        have hloga_ge : Real.log z / 2 ≤ Real.log (a_lo : ℝ) := by
          have hz_ge4 : (4 : ℝ) ≤ z := by linarith [show (4 : ℝ) ≤ (16 : ℝ) ^ 16 by norm_num]
          have hsqrt_le : z ^ (1 / 2 : ℝ) ≤ z / 2 := by
            have hsq : (z ^ (1 / 2 : ℝ)) ^ 2 = z := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hz_pos.le]; norm_num
            nlinarith [Real.rpow_nonneg hz_pos.le (1 / 2 : ℝ)]
          have hlog_sqrt : Real.log (z ^ (1 / 2 : ℝ)) = Real.log z / 2 := by
            rw [Real.log_rpow hz_pos]; ring
          rw [← hlog_sqrt]
          exact Real.log_le_log (Real.rpow_pos_of_pos hz_pos _) (hsqrt_le.trans hza)
        have h1' : Real.log (M_D : ℝ) / Real.log (a_lo : ℝ) ≤ Real.log (x : ℝ) / (Real.log z / 2) := by
          calc Real.log (M_D : ℝ) / Real.log (a_lo : ℝ)
              ≤ Real.log (x : ℝ) / Real.log (a_lo : ℝ) := div_le_div_of_nonneg_right hlogMD_le hloga_pos.le
            _ ≤ Real.log (x : ℝ) / (Real.log z / 2) :=
                div_le_div_of_nonneg_left hlogx_pos.le (by rw [hlogz_eq]; positivity) hloga_ge
        have heq : Real.log (x : ℝ) / (Real.log z / 2) = 2 * (3 : ℝ) ^ k := by
          rw [hlogz_eq]
          have h3k0 : (3 : ℝ) ^ k ≠ 0 := by positivity
          field_simp [hlogx_pos.ne']
        linarith
      have hpow6 : (Real.log (M_D : ℝ) / Real.log (a_lo : ℝ)) ^ 6 ≤ (2 * (3 : ℝ) ^ k) ^ 6 :=
        pow_le_pow_left₀ (div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M_D))) (by linarith))
          hlog_ratio 6
      have h3 : (101 / 100 : ℝ) * (Real.log (M_D : ℝ) / Real.log (a_lo : ℝ)) ^ 6 ≤ C_rough := by
        dsimp only [C_rough]
        have : 0 ≤ (2 * (3 : ℝ) ^ k) ^ 6 := by positivity
        nlinarith
      exact h1.trans (h2.trans h3)
    · -- M_D < a_lo, so Rough ⊆ {1}
      have hsub1 : Rough ⊆ {1} := by
        intro d hd
        obtain ⟨hdI, hrough⟩ := Finset.mem_filter.mp hd
        obtain ⟨hd1, hdMD⟩ := Finset.mem_Icc.mp hdI
        rw [Finset.mem_singleton]
        by_contra hne
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
        have hpz := hrough p (Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩)
        have hp_le : p ≤ M_D := (Nat.le_of_dvd (by omega) hpd).trans hdMD
        have hfl : Nat.floor z ≤ p := Nat.floor_le_of_le hpz
        omega
      have hsum1 : ∑ d ∈ Rough, (1 : ℝ) / (d : ℝ) ≤ 1 := by
        calc ∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)
            ≤ ∑ d ∈ ({1} : Finset ℕ), (1 : ℝ) / (d : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun _ _ _ => by positivity)
          _ = 1 := by simp
      have hC_ge1 : (1 : ℝ) ≤ C_rough := by
        dsimp only [C_rough]
        have : (1 : ℝ) ≤ 2 * (3 : ℝ) ^ k := by
          have : (1 : ℝ) ≤ (3 : ℝ) ^ k := by exact_mod_cast Nat.one_le_pow k 3 (by norm_num)
          linarith
        have : (1 : ℝ) ≤ (2 * (3 : ℝ) ^ k) ^ 6 := one_le_pow₀ this
        linarith
      linarith
  -- Step E: Show 40 * E1_main ≤ S.card and 40 * E1_err ≤ S.card
  have h40_main : 40 * ((2 * (x : ℝ) / (Q : ℝ)) * V * (k : ℝ) * (200 / Real.log z) *
      (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1)) ≤ (S.card : ℝ) := by
    have hlogx_ge : C_main ≤ Real.log (x : ℝ) := by
      have hle : ⌈Real.exp (C_main + 1)⌉₊ ≤ x := by
        have : ⌈Real.exp (C_main + 1)⌉₊ + 2 ≤ x0 :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _)))
        omega
      have hexp : Real.exp (C_main + 1) ≤ (x : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hle)
      have h1 : C_main + 1 ≤ Real.log (x : ℝ) := by
        calc C_main + 1 = Real.log (Real.exp (C_main + 1)) := (Real.log_exp _).symm
          _ ≤ Real.log (x : ℝ) := Real.log_le_log (Real.exp_pos _) hexp
      linarith
    have hpow_rough : (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1) ≤ C_rough ^ (k - 1) :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hRough_le (k - 1)
    have h1 : 40 * ((2 * (x : ℝ) / (Q : ℝ)) * V * (k : ℝ) * (200 / Real.log z) *
        (∑ d ∈ Rough, (1 : ℝ) / (d : ℝ)) ^ (k - 1)) ≤
        ((x : ℝ) / (4 * (Q' : ℝ))) * V * (C_main / Real.log (x : ℝ)) := by
      have hrew : 40 * ((2 * (x : ℝ) / (Q : ℝ)) * V * (k : ℝ) * (200 / Real.log z) * C_rough ^ (k - 1)) =
          ((x : ℝ) / (4 * (Q' : ℝ))) * V * (C_main / Real.log (x : ℝ)) := by
        rw [hlogz_eq]
        dsimp only [C_main, Q']
        push_cast
        have hQ0 : (Q : ℝ) ≠ 0 := by positivity
        have hP0 : (Psmall : ℝ) ≠ 0 := by positivity
        have h3k0 : (3 : ℝ) ^ k ≠ 0 := by positivity
        field_simp [hlogx_pos.ne']
        ring
      rw [← hrew]
      have hmul_eq : ∀ u : ℝ, 40 * ((2 * (x : ℝ) / (Q : ℝ)) * V * (k : ℝ) * (200 / Real.log z) * u) =
          (40 * ((2 * (x : ℝ) / (Q : ℝ)) * V * (k : ℝ) * (200 / Real.log z))) * u := fun u => by ring
      rw [hmul_eq, hmul_eq]
      exact mul_le_mul_of_nonneg_left hpow_rough (by rw [hlogz_eq]; positivity)
    have hdiv_le1 : C_main / Real.log (x : ℝ) ≤ 1 := (div_le_one hlogx_pos).mpr hlogx_ge
    have h2 : ((x : ℝ) / (4 * (Q' : ℝ))) * V * (C_main / Real.log (x : ℝ)) ≤ ((x : ℝ) / (4 * (Q' : ℝ))) * V := by
      calc ((x : ℝ) / (4 * (Q' : ℝ))) * V * (C_main / Real.log (x : ℝ))
          ≤ ((x : ℝ) / (4 * (Q' : ℝ))) * V * 1 := mul_le_mul_of_nonneg_left hdiv_le1 (by positivity)
        _ = ((x : ℝ) / (4 * (Q' : ℝ))) * V := mul_one _
    exact h1.trans (h2.trans hS_lb)
  have h40_err : 40 * (2 * (k : ℝ) * ((k : ℝ) ^ (3 ^ k) * (M_D : ℝ) ^ 2) *
      ((k : ℝ) ^ (k ^ 4) * (x : ℝ) ^ (1 / 160 : ℝ))) ≤ (S.card : ℝ) := by
    have hMD2 : (M_D : ℝ) ^ 2 ≤ 9 * (x : ℝ) ^ (98 / 100 : ℝ) := by
      calc (M_D : ℝ) ^ 2 ≤ (3 * (x : ℝ) ^ (49 / 100 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hMD_le_3 2
        _ = 9 * ((x : ℝ) ^ (49 / 100 : ℝ)) ^ (2 : ℝ) := by
            rw [mul_pow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
        _ = 9 * (x : ℝ) ^ (98 / 100 : ℝ) := by
            rw [← Real.rpow_mul hx_pos.le]; congr 2; norm_num
    have hC_err_lt : C_err < (x : ℝ) ^ (1 / 200 : ℝ) := by
      have hle : ⌈(C_err + 1) ^ (200 : ℕ)⌉₊ ≤ x := by
        have : ⌈(C_err + 1) ^ (200 : ℕ)⌉₊ + 2 ≤ x0 :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
        omega
      have hpow : (C_err + 1) ^ (200 : ℕ) ≤ (x : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hle)
      have h1 : C_err + 1 ≤ (x : ℝ) ^ (1 / 200 : ℝ) := by
        calc C_err + 1 = ((C_err + 1) ^ (200 : ℝ)) ^ (1 / 200 : ℝ) := by
              rw [← Real.rpow_mul (by positivity)]; norm_num
          _ = ((C_err + 1) ^ (200 : ℕ)) ^ (1 / 200 : ℝ) := by
              rw [show (200 : ℝ) = ((200 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          _ ≤ (x : ℝ) ^ (1 / 200 : ℝ) := Real.rpow_le_rpow (by positivity) hpow (by norm_num)
      linarith
    have hlog_sm := E387Final.log_pow_le_rpow_small k hk1 (x : ℝ) hx1
    have hprod_le : 40 * (2 * (k : ℝ) * ((k : ℝ) ^ (3 ^ k) * (M_D : ℝ) ^ 2) *
        ((k : ℝ) ^ (k ^ 4) * (x : ℝ) ^ (1 / 160 : ℝ))) * (8 * (Q' : ℝ) * (Real.log (x : ℝ)) ^ (6 * k)) ≤ (x : ℝ) := by
      have h1 : 40 * (2 * (k : ℝ) * ((k : ℝ) ^ (3 ^ k) * (M_D : ℝ) ^ 2) *
          ((k : ℝ) ^ (k ^ 4) * (x : ℝ) ^ (1 / 160 : ℝ))) * (8 * (Q' : ℝ) * (Real.log (x : ℝ)) ^ (6 * k)) ≤
          C_err * (x : ℝ) ^ (98 / 100 : ℝ) * (x : ℝ) ^ (1 / 160 : ℝ) * (x : ℝ) ^ (1 / 160 : ℝ) := by
        have hrew : C_err * (x : ℝ) ^ (98 / 100 : ℝ) * (x : ℝ) ^ (1 / 160 : ℝ) * (x : ℝ) ^ (1 / 160 : ℝ) =
            (40 * (2 * (k : ℝ) * ((k : ℝ) ^ (3 ^ k) * (9 * (x : ℝ) ^ (98 / 100 : ℝ))) *
              ((k : ℝ) ^ (k ^ 4) * (x : ℝ) ^ (1 / 160 : ℝ)))) *
            (8 * (Q' : ℝ) * (((960 * k : ℝ) ^ (6 * k)) * (x : ℝ) ^ (1 / 160 : ℝ))) := by
          dsimp only [C_err]; ring
        rw [hrew]
        refine mul_le_mul ?_ (mul_le_mul_of_nonneg_left hlog_sm (by positivity)) (by positivity) (by positivity)
        have hmul1 : (k : ℝ) ^ (3 ^ k) * (M_D : ℝ) ^ 2 ≤ (k : ℝ) ^ (3 ^ k) * (9 * (x : ℝ) ^ (98 / 100 : ℝ)) :=
          mul_le_mul_of_nonneg_left hMD2 (by positivity)
        have hmul2 : 2 * (k : ℝ) * ((k : ℝ) ^ (3 ^ k) * (M_D : ℝ) ^ 2) ≤
            2 * (k : ℝ) * ((k : ℝ) ^ (3 ^ k) * (9 * (x : ℝ) ^ (98 / 100 : ℝ))) :=
          mul_le_mul_of_nonneg_left hmul1 (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmul2 (by positivity)) (by norm_num)
      have h2 : C_err * (x : ℝ) ^ (98 / 100 : ℝ) * (x : ℝ) ^ (1 / 160 : ℝ) * (x : ℝ) ^ (1 / 160 : ℝ) ≤
          (x : ℝ) ^ (1 / 200 : ℝ) * (x : ℝ) ^ (98 / 100 : ℝ) * (x : ℝ) ^ (1 / 160 : ℝ) * (x : ℝ) ^ (1 / 160 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC_err_lt.le (by positivity)) (by positivity)) (by positivity)
      have h3 : (x : ℝ) ^ (1 / 200 : ℝ) * (x : ℝ) ^ (98 / 100 : ℝ) * (x : ℝ) ^ (1 / 160 : ℝ) * (x : ℝ) ^ (1 / 160 : ℝ) ≤
          (x : ℝ) := by
        rw [← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos]
        have : (x : ℝ) ^ (1 / 200 + 98 / 100 + 1 / 160 + 1 / 160 : ℝ) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        simpa using this
      exact h1.trans (h2.trans h3)
    have hmid : 40 * (2 * (k : ℝ) * ((k : ℝ) ^ (3 ^ k) * (M_D : ℝ) ^ 2) *
        ((k : ℝ) ^ (k ^ 4) * (x : ℝ) ^ (1 / 160 : ℝ))) ≤
        ((x : ℝ) / (4 * (Q' : ℝ))) * (1 / (2 * (Real.log (x : ℝ)) ^ (6 * k))) := by
      rw [show ((x : ℝ) / (4 * (Q' : ℝ))) * (1 / (2 * (Real.log (x : ℝ)) ^ (6 * k))) =
          (x : ℝ) / (8 * (Q' : ℝ) * (Real.log (x : ℝ)) ^ (6 * k)) by ring,
        le_div_iff₀ (by positivity)]
      exact hprod_le
    exact (hmid.trans (mul_le_mul_of_nonneg_left hV_lb (by positivity))).trans hS_lb
  -- Combine: 40 * E1.card ≤ 2 * S.card ≤ 9 * S.card
  set E1 := S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
      (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
      n < 2 * (∏ i ∈ Finset.range k, f i) ∧ (∏ i ∈ Finset.range k, f i) ≤ n ∧
      (∃ i < k, (x : ℝ) ^ (51 / 100 : ℝ) ≤ (f i : ℝ)))
  have hreal : (40 : ℝ) * (E1.card : ℝ) ≤ 9 * (S.card : ℝ) := by
    have hS_nn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have h40 := mul_le_mul_of_nonneg_left hE1_bd (by norm_num : (0 : ℝ) ≤ 40)
    rw [mul_add] at h40
    linarith
  have hcast : ((40 * E1.card : ℕ) : ℝ) ≤ ((9 * S.card : ℕ) : ℝ) := by
    push_cast; exact hreal
  exact Nat.cast_le.mp hcast
