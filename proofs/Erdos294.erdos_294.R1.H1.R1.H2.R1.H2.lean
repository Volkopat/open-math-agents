import OMAReductions.R_Erdos294_erdos_294_R1_H1_R1_H2_R1
import Mathlib

/-!
# Proof of `Erdos294.erdos_294.R1.H1.R1.H2.R1.H2`

Proves the far-frequency exponential-sum bound for smooth divisors in `[N/16, N]`
following the minor-arc divisibility method of Liu and Sawhney (arXiv:2404.07113,
Proposition 3.2 and Lemma 4.1). Restricting the nonnegative phase sum to smooth
integers with at most 5 distinct prime factors removes all `log log N` losses from
prime-factor multiplicity, allowing `c = 1` with purely elementary Chebyshev bounds.

Credits for upstream reductions and sibling proofs of `Erdos294.erdos_294`:
- `@steveDOTdigital` (PRs #5730, #6217, #6261, #6598, #6840)
- `@mattdorman` (PR #8765)
- `@vkascheev` (PR #833)
-/

open Finset Filter Real

namespace Erdos294StepH2

/- ## Section 1: Elementary Chebyshev prime-counting bounds -/

section PrimeCounting

private lemma log_le_four_sqrt_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have h1 : Real.log x / 4 + 1 ≤ Real.exp (Real.log x / 4) := Real.add_one_le_exp _
  have h2 : Real.exp (Real.log x / 4) = Real.sqrt (Real.sqrt x) := by
    have hs1 : Real.exp (Real.log x / 2) = Real.sqrt x := by
      rw [← Real.sqrt_sq (Real.exp_pos _).le, sq, ← Real.exp_add, add_halves, Real.exp_log hx]
    rw [← hs1, ← Real.sqrt_sq (Real.exp_pos _).le, sq, ← Real.exp_add]
    congr 2; ring
  linarith

private lemma sqrt_sqrt_le_mul_of_le {a x : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (Real.sqrt (a * x)) = Real.sqrt (Real.sqrt a) * Real.sqrt (Real.sqrt x) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul (Real.sqrt_nonneg a)]

private lemma theta_sub_eq_sum_Ioc {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log b, Chebyshev.theta_eq_sum_primesLE_log a]
  have hsub : Nat.primesLE a ⊆ Nat.primesLE b := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hab, hp.2⟩
  have hsdiff : Nat.primesLE b \ Nat.primesLE a = (Ioc a b).filter Nat.Prime := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hpb, hp⟩, hna⟩
      refine ⟨⟨?_, hpb⟩, hp⟩
      by_contra hle
      exact hna ⟨le_of_not_gt hle, hp⟩
    · rintro ⟨⟨hap, hpb⟩, hp⟩
      exact ⟨⟨hpb, hp⟩, fun ⟨hpa, _⟩ => by omega⟩
  rw [← hsdiff, Finset.sum_sdiff_eq_sub hsub]

private lemma theta_ge_half {n : ℕ} (hn : 10 ^ 10 ≤ n) :
    (n : ℝ) / 2 ≤ Chebyshev.theta (n : ℝ) := by
  have hge := Chebyshev.theta_ge n
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn_big : (10 ^ 10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hq : (100 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by
    have h1 : (10000 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hn_pos.le]
      nlinarith
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]
    nlinarith
  have hsqn : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt (n : ℝ) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hsq2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
  have hlogn : Real.log (n : ℝ) ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) :=
    log_le_four_sqrt_sqrt hn_pos
  have hlogn1 : Real.log ((n : ℝ) + 1) ≤ 4 * Real.sqrt (Real.sqrt (2 * (n : ℝ))) := by
    have hle : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    exact (Real.log_le_log (by positivity) hle).trans (log_le_four_sqrt_sqrt (by positivity))
  have hss2 : Real.sqrt (Real.sqrt (2 : ℝ)) ≤ 2 := by
    have h1 : Real.sqrt (2 : ℝ) ≤ 4 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hlogn1_le : Real.log ((n : ℝ) + 1) ≤ 8 * Real.sqrt (Real.sqrt (n : ℝ)) := by
    rw [sqrt_sqrt_le_mul_of_le (by norm_num)] at hlogn1
    nlinarith [Real.sqrt_nonneg (Real.sqrt (n : ℝ))]
  set s := Real.sqrt (Real.sqrt (n : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq_eq : Real.sqrt (n : ℝ) = s ^ 2 := hsqn.symm
  have hn_eq : (n : ℝ) = s ^ 4 := by
    calc (n : ℝ) = Real.sqrt (n : ℝ) ^ 2 := hsq2.symm
      _ = (s ^ 2) ^ 2 := by rw [hsq_eq]
      _ = s ^ 4 := by ring
  have hterm1 : 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ 8 * s ^ 3 := by
    rw [hsq_eq]
    nlinarith [sq_nonneg s]
  have hterm2 : 8 * s ^ 3 + 8 * s ≤ 0.1 * s ^ 4 := by
    have hs3 : 100 * s ^ 3 ≤ s ^ 4 := by nlinarith [pow_nonneg hs0 3]
    have hs1 : s ≤ s ^ 3 := by nlinarith [sq_nonneg s]
    nlinarith
  have hlog_tot : Real.log ((n : ℝ) + 1) + 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ 0.1 * (n : ℝ) := by
    calc Real.log ((n : ℝ) + 1) + 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
        ≤ 8 * s + 8 * s ^ 3 := add_le_add hlogn1_le hterm1
      _ ≤ 0.1 * s ^ 4 := by linarith
      _ = 0.1 * (n : ℝ) := by rw [hn_eq]
  nlinarith

private lemma theta_three_sub_ge {X : ℕ} (hX : 10 ^ 10 ≤ X) :
    (X : ℝ) / 2 ≤ Chebyshev.theta ((3 * X : ℕ) : ℝ) - Chebyshev.theta (X : ℝ) := by
  have hge := Chebyshev.theta_ge (3 * X)
  have hle := Chebyshev.theta_le_log4_mul_x (x := (X : ℝ)) (by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hX_pos : (0 : ℝ) < X := by positivity
  have hX_big : (10 ^ 10 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  set s := Real.sqrt (Real.sqrt ((3 * X : ℕ) : ℝ))
  have h3X_pos : (0 : ℝ) < ((3 * X : ℕ) : ℝ) := by positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h3X_big : (3 * 10 ^ 10 : ℝ) ≤ ((3 * X : ℕ) : ℝ) := by
    push_cast; linarith
  have hs_ge : (130 : ℝ) ≤ s := by
    have h1 : (16900 : ℝ) ≤ Real.sqrt ((3 * X : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) h3X_pos.le]; nlinarith
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]; nlinarith
  have hsq : Real.sqrt ((3 * X : ℕ) : ℝ) = s ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
  have h3X_eq : ((3 * X : ℕ) : ℝ) = s ^ 4 := by
    calc ((3 * X : ℕ) : ℝ) = Real.sqrt ((3 * X : ℕ) : ℝ) ^ 2 := (Real.sq_sqrt h3X_pos.le).symm
      _ = (s ^ 2) ^ 2 := by rw [hsq]
      _ = s ^ 4 := by ring
  have hlog3X : Real.log ((3 * X : ℕ) : ℝ) ≤ 4 * s := log_le_four_sqrt_sqrt h3X_pos
  have hlog3X1 : Real.log (((3 * X : ℕ) : ℝ) + 1) ≤ 8 * s := by
    have h1 : Real.log (((3 * X : ℕ) : ℝ) + 1) ≤ Real.log (2 * ((3 * X : ℕ) : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (2 * ((3 * X : ℕ) : ℝ)) ≤ 4 * Real.sqrt (Real.sqrt (2 * ((3 * X : ℕ) : ℝ))) :=
      log_le_four_sqrt_sqrt (by positivity)
    rw [sqrt_sqrt_le_mul_of_le (by norm_num)] at h2
    have hss2 : Real.sqrt (Real.sqrt (2 : ℝ)) ≤ 2 := by
      have ha : Real.sqrt (2 : ℝ) ≤ 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    nlinarith
  have hterm : 2 * Real.sqrt ((3 * X : ℕ) : ℝ) * Real.log ((3 * X : ℕ) : ℝ) ≤ 8 * s ^ 3 := by
    rw [hsq]; nlinarith [sq_nonneg s]
  have hrem : 8 * s ^ 3 + 8 * s ≤ 0.063 * s ^ 4 := by
    have hs3 : 130 * s ^ 3 ≤ s ^ 4 := by nlinarith [pow_nonneg hs0 3]
    have hs1 : 100 * s ≤ s ^ 3 := by nlinarith [sq_nonneg s]
    nlinarith
  have hcast : ((3 * X : ℕ) : ℝ) = 3 * (X : ℝ) := by push_cast; ring
  have herr : Real.log (((3 * X : ℕ) : ℝ) + 1) +
      2 * Real.sqrt ((3 * X : ℕ) : ℝ) * Real.log ((3 * X : ℕ) : ℝ) ≤ 0.189 * (X : ℝ) := by
    linarith [h3X_eq, hcast]
  rw [hlog4] at hle
  rw [hcast] at hge herr
  rw [hcast]
  nlinarith

private lemma five_primes_in_Ioc_three {X : ℕ} (hX : 10 ^ 10 ≤ X) :
    5 ≤ ((Ioc X (3 * X)).filter Nat.Prime).card := by
  have hth := theta_three_sub_ge hX
  rw [theta_sub_eq_sum_Ioc (by omega : X ≤ 3 * X)] at hth
  have hX_pos : (0 : ℝ) < X := by positivity
  have h3X_pos : (0 : ℝ) < ((3 * X : ℕ) : ℝ) := by positivity
  have hsum_le : ∑ p ∈ (Ioc X (3 * X)).filter Nat.Prime, Real.log (p : ℝ) ≤
      (((Ioc X (3 * X)).filter Nat.Prime).card : ℝ) * Real.log ((3 * X : ℕ) : ℝ) := by
    calc ∑ p ∈ (Ioc X (3 * X)).filter Nat.Prime, Real.log (p : ℝ)
        ≤ ∑ _p ∈ (Ioc X (3 * X)).filter Nat.Prime, Real.log ((3 * X : ℕ) : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          have hp' := mem_filter.mp hp
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
          exact Real.log_le_log hp_pos (by exact_mod_cast (mem_Ioc.mp hp'.1).2)
      _ = (((Ioc X (3 * X)).filter Nat.Prime).card : ℝ) * Real.log ((3 * X : ℕ) : ℝ) := by simp
  have hlog_le : Real.log ((3 * X : ℕ) : ℝ) ≤ 4 * Real.sqrt (Real.sqrt ((3 * X : ℕ) : ℝ)) :=
    log_le_four_sqrt_sqrt h3X_pos
  have hlog_pos : 0 < Real.log ((3 * X : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * X by omega))
  set s := Real.sqrt (Real.sqrt ((3 * X : ℕ) : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h3X_big : (3 * 10 ^ 10 : ℝ) ≤ ((3 * X : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : 3 * 10 ^ 10 ≤ 3 * X)
  have hs_ge : (130 : ℝ) ≤ s := by
    have h1 : (16900 : ℝ) ≤ Real.sqrt ((3 * X : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) h3X_pos.le]; nlinarith
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]; nlinarith
  have h3X_eq : ((3 * X : ℕ) : ℝ) = s ^ 4 := by
    have hsq : Real.sqrt ((3 * X : ℕ) : ℝ) = s ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
    calc ((3 * X : ℕ) : ℝ) = Real.sqrt ((3 * X : ℕ) : ℝ) ^ 2 := (Real.sq_sqrt h3X_pos.le).symm
      _ = (s ^ 2) ^ 2 := by rw [hsq]
      _ = s ^ 4 := by ring
  have hcast : ((3 * X : ℕ) : ℝ) = 3 * (X : ℝ) := by push_cast; ring
  have h5log : 5 * Real.log ((3 * X : ℕ) : ℝ) ≤ (X : ℝ) / 2 := by
    have hs3 : 130 ^ 3 * s ≤ s ^ 4 := by
      have ha : 130 ^ 2 ≤ s ^ 2 := by nlinarith
      have hb : 130 ^ 3 ≤ s ^ 3 := by nlinarith
      nlinarith
    linarith [h3X_eq, hcast]
  have hcard_real : (5 : ℝ) ≤ (((Ioc X (3 * X)).filter Nat.Prime).card : ℝ) := by
    nlinarith
  exact_mod_cast hcard_real

private lemma theta_four_sub_ge {P : ℕ} (hP : 10 ^ 10 ≤ P) :
    (P : ℝ) ≤ Chebyshev.theta ((4 * P : ℕ) : ℝ) - Chebyshev.theta (P : ℝ) := by
  have hge := Chebyshev.theta_ge (4 * P)
  have hle := Chebyshev.theta_le_log4_mul_x (x := (P : ℝ)) (by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have h4P_pos : (0 : ℝ) < ((4 * P : ℕ) : ℝ) := by positivity
  set s := Real.sqrt (Real.sqrt ((4 * P : ℕ) : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h4P_big : (4 * 10 ^ 10 : ℝ) ≤ ((4 * P : ℕ) : ℝ) := by
    push_cast; exact_mod_cast (by omega : 4 * 10 ^ 10 ≤ 4 * P)
  have hs_ge : (140 : ℝ) ≤ s := by
    have h1 : (19600 : ℝ) ≤ Real.sqrt ((4 * P : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) h4P_pos.le]; nlinarith
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]; nlinarith
  have hsq : Real.sqrt ((4 * P : ℕ) : ℝ) = s ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
  have h4P_eq : ((4 * P : ℕ) : ℝ) = s ^ 4 := by
    calc ((4 * P : ℕ) : ℝ) = Real.sqrt ((4 * P : ℕ) : ℝ) ^ 2 := (Real.sq_sqrt h4P_pos.le).symm
      _ = (s ^ 2) ^ 2 := by rw [hsq]
      _ = s ^ 4 := by ring
  have hlog4P : Real.log ((4 * P : ℕ) : ℝ) ≤ 4 * s := log_le_four_sqrt_sqrt h4P_pos
  have hlog4P1 : Real.log (((4 * P : ℕ) : ℝ) + 1) ≤ 8 * s := by
    have h1 : Real.log (((4 * P : ℕ) : ℝ) + 1) ≤ Real.log (2 * ((4 * P : ℕ) : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (2 * ((4 * P : ℕ) : ℝ)) ≤ 4 * Real.sqrt (Real.sqrt (2 * ((4 * P : ℕ) : ℝ))) :=
      log_le_four_sqrt_sqrt (by positivity)
    rw [sqrt_sqrt_le_mul_of_le (by norm_num)] at h2
    have hss2 : Real.sqrt (Real.sqrt (2 : ℝ)) ≤ 2 := by
      have ha : Real.sqrt (2 : ℝ) ≤ 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    nlinarith
  have hterm : 2 * Real.sqrt ((4 * P : ℕ) : ℝ) * Real.log ((4 * P : ℕ) : ℝ) ≤ 8 * s ^ 3 := by
    rw [hsq]; nlinarith [sq_nonneg s]
  have hrem : 8 * s ^ 3 + 8 * s ≤ 0.06 * s ^ 4 := by
    have hs3 : 140 * s ^ 3 ≤ s ^ 4 := by nlinarith [pow_nonneg hs0 3]
    have hs1 : 100 * s ≤ s ^ 3 := by nlinarith [sq_nonneg s]
    nlinarith
  have hcast : ((4 * P : ℕ) : ℝ) = 4 * (P : ℝ) := by push_cast; ring
  have herr : Real.log (((4 * P : ℕ) : ℝ) + 1) +
      2 * Real.sqrt ((4 * P : ℕ) : ℝ) * Real.log ((4 * P : ℕ) : ℝ) ≤ 0.24 * (P : ℝ) := by
    linarith [h4P_eq, hcast]
  rw [hlog4] at hle
  rw [hcast] at hge herr
  rw [hcast]
  nlinarith

private lemma card_primesLE_ge {U : ℕ} (hU : 10 ^ 10 ≤ U) :
    (U : ℝ) / (2 * Real.log (U : ℝ)) ≤ ((Nat.primesLE U).card : ℝ) := by
  have hth := theta_ge_half hU
  rw [Chebyshev.theta_eq_sum_primesLE_log U] at hth
  have hU_pos : (0 : ℝ) < U := by positivity
  have hlogU_pos : 0 < Real.log (U : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hsum_le : ∑ p ∈ Nat.primesLE U, Real.log (p : ℝ) ≤
      ((Nat.primesLE U).card : ℝ) * Real.log (U : ℝ) := by
    calc ∑ p ∈ Nat.primesLE U, Real.log (p : ℝ)
        ≤ ∑ _p ∈ Nat.primesLE U, Real.log (U : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          have hp' := Nat.mem_primesLE.mp hp
          exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hp'.1)
      _ = ((Nat.primesLE U).card : ℝ) * Real.log (U : ℝ) := by simp
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log (U : ℝ))]
  linarith

private lemma eight_log_four_le_quarter {P : ℕ} (hP : 10 ^ 10 ≤ P) :
    8 * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 4 := by
  have h4P_pos : (0 : ℝ) < ((4 * P : ℕ) : ℝ) := by positivity
  have hlog := log_le_four_sqrt_sqrt h4P_pos
  set s := Real.sqrt (Real.sqrt ((4 * P : ℕ) : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h4P_big : (4 * 10 ^ 10 : ℝ) ≤ ((4 * P : ℕ) : ℝ) := by
    push_cast; exact_mod_cast (by omega : 4 * 10 ^ 10 ≤ 4 * P)
  have hs_ge : (140 : ℝ) ≤ s := by
    have h1 : (19600 : ℝ) ≤ Real.sqrt ((4 * P : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) h4P_pos.le]; nlinarith
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]; nlinarith
  have h4P_eq : ((4 * P : ℕ) : ℝ) = s ^ 4 := by
    have hsq : Real.sqrt ((4 * P : ℕ) : ℝ) = s ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
    calc ((4 * P : ℕ) : ℝ) = Real.sqrt ((4 * P : ℕ) : ℝ) ^ 2 := (Real.sq_sqrt h4P_pos.le).symm
      _ = (s ^ 2) ^ 2 := by rw [hsq]
      _ = s ^ 4 := by ring
  have hcast : ((4 * P : ℕ) : ℝ) = 4 * (P : ℝ) := by push_cast; ring
  have hs3 : 140 ^ 3 * s ≤ s ^ 4 := by
    have ha : 140 ^ 2 ≤ s ^ 2 := by nlinarith
    have hb : 140 ^ 3 ≤ s ^ 3 := by nlinarith
    nlinarith
  linarith [h4P_eq, hcast]

end PrimeCounting

/- ## Section 2: Arithmetic helpers and minor-arc divisibility core -/

section MinorArcCore

private def qOf (S p : ℕ) : ℕ := p ^ (p.log S)

private lemma qOf_pos {S p : ℕ} (hp : p.Prime) : 0 < qOf S p :=
  Nat.pow_pos hp.pos

private lemma qOf_le_S {S p : ℕ} (hS : S ≠ 0) : qOf S p ≤ S :=
  Nat.pow_log_le_self p hS

private lemma prime_dvd_qOf {S p : ℕ} (hp : p ∈ Nat.primesLE S) : p ∣ qOf S p := by
  have ⟨hpS, hpr⟩ := Nat.mem_primesLE.mp hp
  have hlog : 1 ≤ p.log S := Nat.le_log_of_pow_le hpr.one_lt (by simpa using hpS)
  exact dvd_pow_self p (by omega)

private lemma qOf_dvd_lcmUpto {S p : ℕ} (hp : p ∈ Nat.primesLE S) :
    qOf S p ∣ Nat.lcmUpto S := by
  rw [Nat.lcmUpto_eq_prod_pow_log S]
  exact Finset.dvd_prod_of_mem (fun q => q ^ q.log S) hp

private lemma primeFactors_qOf_subset {S p : ℕ} (hp : p.Prime) :
    (qOf S p).primeFactors ⊆ {p} := by
  intro r hr
  have ⟨hrp, hrdvd, _⟩ := Nat.mem_primeFactors.mp hr
  have hrp' : r ∣ p := hrp.dvd_of_dvd_pow hrdvd
  exact mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hrp hp).mp hrp')

private lemma coprime_qOf_of_ne {S p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) :
    Nat.Coprime (qOf S p₁) (qOf S p₂) :=
  ((Nat.coprime_primes hp₁ hp₂).mpr hne).pow _ _

private lemma coprime_qOf_prime_of_ne {S p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) :
    Nat.Coprime (qOf S p) r :=
  ((Nat.coprime_primes hp hr).mpr hne).pow_left _

private lemma prime_dvd_lcmUpto {S r : ℕ} (hr : r.Prime) (hrS : r ≤ S) :
    r ∣ Nat.lcmUpto S :=
  (prime_dvd_qOf (Nat.mem_primesLE.mpr ⟨hrS, hr⟩)).trans
    (qOf_dvd_lcmUpto (Nat.mem_primesLE.mpr ⟨hrS, hr⟩))

private lemma prod_dvd_of_natCoprime {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ} {m : ℕ}
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime (f a) (f b))
    (hdvd : ∀ a ∈ s, f a ∣ m) :
    (∏ a ∈ s, f a) ∣ m := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcop_a : Nat.Coprime (f a) (∏ b ∈ s, f b) :=
      Nat.Coprime.prod_right fun b hb =>
        hcop a (mem_insert_self a s) b (mem_insert_of_mem hb) (fun h => ha (h ▸ hb))
    have hdvd_s : (∏ b ∈ s, f b) ∣ m :=
      ih (fun x hx y hy hxy => hcop x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy)
        (fun x hx => hdvd x (mem_insert_of_mem hx))
    exact hcop_a.mul_dvd_of_dvd_of_dvd (hdvd a (mem_insert_self a s)) hdvd_s

private lemma four_mul_prod_qOf_dvd {S : ℕ} {D : Finset ℕ} (hDsub : D ⊆ Nat.primesLE S)
    (hDne : D.Nonempty) {x : ℤ}
    (hx : ∀ p ∈ D, ((4 * qOf S p : ℕ) : ℤ) ∣ x) :
    ((4 * ∏ p ∈ D, qOf S p : ℕ) : ℤ) ∣ x := by
  have hnat : 4 * ∏ p ∈ D, qOf S p ∣ x.natAbs := by
    have hx' : ∀ p ∈ D, 4 * qOf S p ∣ x.natAbs := fun p hp => Int.natCast_dvd.mp (hx p hp)
    by_cases h2 : 2 ∈ D
    · have hprod : ∏ p ∈ D, qOf S p = qOf S 2 * ∏ p ∈ D.erase 2, qOf S p :=
        (Finset.mul_prod_erase D (qOf S) h2).symm
      rw [hprod, ← mul_assoc]
      have hcop : Nat.Coprime (4 * qOf S 2) (∏ p ∈ D.erase 2, qOf S p) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have ⟨hne, hpD⟩ := mem_erase.mp hp
        have hpr := Nat.prime_of_mem_primesLE (hDsub hpD)
        have hcop2 : Nat.Coprime 2 (qOf S p) :=
          ((Nat.coprime_primes Nat.prime_two hpr).mpr hne.symm).pow_right _
        have hcop4 : Nat.Coprime 4 (qOf S p) := by
          simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hcop2.pow_left 2
        exact hcop4.mul_left (coprime_qOf_of_ne Nat.prime_two hpr hne.symm)
      have hdvd1 : 4 * qOf S 2 ∣ x.natAbs := hx' 2 h2
      have hdvd2 : ∏ p ∈ D.erase 2, qOf S p ∣ x.natAbs := by
        refine prod_dvd_of_natCoprime ?_ fun p hp =>
          (dvd_mul_left (qOf S p) 4).trans (hx' p (mem_of_mem_erase hp))
        intro a ha b hb hab
        exact coprime_qOf_of_ne (Nat.prime_of_mem_primesLE (hDsub (mem_of_mem_erase ha)))
          (Nat.prime_of_mem_primesLE (hDsub (mem_of_mem_erase hb))) hab
      exact hcop.mul_dvd_of_dvd_of_dvd hdvd1 hdvd2
    · obtain ⟨p₀, hp₀⟩ := hDne
      have hdvd4 : 4 ∣ x.natAbs := (dvd_mul_right 4 (qOf S p₀)).trans (hx' p₀ hp₀)
      have hcop : Nat.Coprime 4 (∏ p ∈ D, qOf S p) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hpr := Nat.prime_of_mem_primesLE (hDsub hp)
        have hne : 2 ≠ p := fun h => h2 (h ▸ hp)
        have hcop2 : Nat.Coprime 2 (qOf S p) :=
          ((Nat.coprime_primes Nat.prime_two hpr).mpr hne).pow_right _
        simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hcop2.pow_left 2
      have hdvdP : ∏ p ∈ D, qOf S p ∣ x.natAbs := by
        refine prod_dvd_of_natCoprime ?_ fun p hp =>
          (dvd_mul_left (qOf S p) 4).trans (hx' p hp)
        intro a ha b hb hab
        exact coprime_qOf_of_ne (Nat.prime_of_mem_primesLE (hDsub ha))
          (Nat.prime_of_mem_primesLE (hDsub hb)) hab
      exact hcop.mul_dvd_of_dvd_of_dvd hdvd4 hdvdP
  exact Int.natCast_dvd.mpr hnat

private lemma card_primeFactors_mul_le (a b : ℕ) :
    (a * b).primeFactors.card ≤ a.primeFactors.card + b.primeFactors.card := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [Nat.primeFactors_mul ha hb]
  exact Finset.card_union_le _ _

private lemma exists_good_p' {U t M_bad p : ℕ} {B : Finset ℕ}
    (hB_pos : ∀ n ∈ B, 0 < n)
    (hB_omega : ∀ n ∈ B, n.primeFactors.card ≤ 5)
    (hB_lt : B.card < t)
    (havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1)) :
    ∃ p' ∈ (Nat.primesLE U).erase p, (B.filter (fun n => p' ∣ n)).card ≤ M_bad := by
  by_contra! hall
  let S' := (Nat.primesLE U).erase p
  have hS'_card : (Nat.primesLE U).card - 1 ≤ S'.card := by
    dsimp [S']
    by_cases hp : p ∈ Nat.primesLE U
    · rw [Finset.card_erase_of_mem hp]
    · rw [Finset.erase_eq_of_notMem hp]; omega
  have hlo : S'.card * (M_bad + 1) ≤ ∑ p' ∈ S', (B.filter (fun n => p' ∣ n)).card := by
    calc S'.card * (M_bad + 1)
        = ∑ _p' ∈ S', (M_bad + 1) := by simp
      _ ≤ ∑ p' ∈ S', (B.filter (fun n => p' ∣ n)).card :=
          sum_le_sum fun p' hp' => Nat.succ_le_of_lt (hall p' hp')
  have hswap : ∑ p' ∈ S', (B.filter (fun n => p' ∣ n)).card =
      ∑ n ∈ B, (S'.filter (fun p' => p' ∣ n)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hhi : ∑ n ∈ B, (S'.filter (fun p' => p' ∣ n)).card ≤ 5 * B.card := by
    calc ∑ n ∈ B, (S'.filter (fun p' => p' ∣ n)).card
        ≤ ∑ n ∈ B, n.primeFactors.card := by
          refine sum_le_sum fun n hn => Finset.card_le_card fun p' hp' => ?_
          have ⟨hp'S, hp'n⟩ := mem_filter.mp hp'
          exact Nat.mem_primeFactors.mpr
            ⟨Nat.prime_of_mem_primesLE (mem_of_mem_erase hp'S), hp'n, (hB_pos n hn).ne'⟩
      _ ≤ ∑ _n ∈ B, 5 := sum_le_sum fun n hn => hB_omega n hn
      _ = 5 * B.card := by simp [mul_comm]
  have h1 : ((Nat.primesLE U).card - 1) * (M_bad + 1) ≤ S'.card * (M_bad + 1) :=
    Nat.mul_le_mul_right _ hS'_card
  omega

private lemma exists_prime_avoiding {X : ℕ} (hX : 10 ^ 10 ≤ X) {avoid : Finset ℕ}
    (hav : avoid.card ≤ 3) :
    ∃ r : ℕ, r.Prime ∧ X < r ∧ r ≤ 3 * X ∧ r ∉ avoid := by
  let Pset := (Ioc X (3 * X)).filter Nat.Prime
  have hcard : 5 ≤ Pset.card := five_primes_in_Ioc_three hX
  have hdiff : (Pset \ avoid).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Pset ⊆ avoid := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  obtain ⟨r, hr⟩ := hdiff
  have ⟨hrP, hrA⟩ := mem_sdiff.mp hr
  have ⟨hrI, hrPr⟩ := mem_filter.mp hrP
  have ⟨hr1, hr2⟩ := mem_Ioc.mp hrI
  exact ⟨r, hrPr, hr1, hr2, hrA⟩

private lemma exists_multiplier_r {N S P K U p p' : ℕ}
    (hS_big : 10 ^ 22 ≤ S)
    (hSN : S ≤ N)
    (hP_pos : 0 < P)
    (hK_def : K = N / (16 * P))
    (hSU_L0 : 10 ^ 11 * S * U ≤ K + 1)
    (hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S)
    (hp : p ∈ Nat.primesLE S)
    (hp' : p' ∈ (Nat.primesLE U).erase p) :
    let d := qOf S p * p'
    ∃ r : ℕ, K + 1 ≤ d * r ∧ 4 * P * (d * r) ≤ N ∧
      r ∣ Nat.lcmUpto S ∧ Nat.Coprime d r ∧ r.primeFactors.card ≤ 2 := by
  intro d
  have hp_pr : p.Prime := Nat.prime_of_mem_primesLE hp
  have hp'_mem : p' ∈ Nat.primesLE U := mem_of_mem_erase hp'
  have hp'_pr : p'.Prime := Nat.prime_of_mem_primesLE hp'_mem
  have hp'_le : p' ≤ U := Nat.le_of_mem_primesLE hp'_mem
  have hd_pos : 0 < d := Nat.mul_pos (qOf_pos hp_pr) hp'_pr.pos
  have hd_le : d ≤ S * U := Nat.mul_le_mul (qOf_le_S (by omega)) hp'_le
  set L₀ := K + 1
  set U₀ := N / (4 * P)
  have h4K_U0 : 4 * K ≤ U₀ := by
    have h1 : 16 * P * K ≤ N := by rw [hK_def]; exact Nat.mul_div_le N (16 * P)
    have h2 : (4 * K) * (4 * P) ≤ N := by nlinarith
    exact (Nat.le_div_iff_mul_le (by positivity)).mpr h2
  have hd_L0 : 10 ^ 11 * d ≤ L₀ := by
    calc 10 ^ 11 * d ≤ 10 ^ 11 * (S * U) := Nat.mul_le_mul_left _ hd_le
      _ = 10 ^ 11 * S * U := by ring
      _ ≤ L₀ := hSU_L0
  have hd_pf : d.primeFactors.card ≤ 2 := by
    calc d.primeFactors.card
        ≤ (qOf S p).primeFactors.card + p'.primeFactors.card := card_primeFactors_mul_le _ _
      _ ≤ ({p} : Finset ℕ).card + 1 := by
          rw [hp'_pr.primeFactors, Finset.card_singleton]
          exact Nat.add_le_add_right (Finset.card_le_card (primeFactors_qOf_subset hp_pr)) 1
      _ = 2 := by simp
  set X := L₀ / d + 1
  have hX_big : 10 ^ 10 ≤ X := by
    have : 10 ^ 11 ≤ L₀ / d := (Nat.le_div_iff_mul_le hd_pos).mpr (by linarith)
    omega
  by_cases hA : 3 * X ≤ S
  · obtain ⟨r₁, hr₁_pr, hr₁_gt, hr₁_le, hr₁_av⟩ :=
      exists_prime_avoiding hX_big (by omega : d.primeFactors.card ≤ 3)
    have hcop : Nat.Coprime d r₁ := by
      rw [Nat.coprime_comm]
      refine hr₁_pr.coprime_iff_not_dvd.mpr fun hdvd => hr₁_av ?_
      exact Nat.mem_primeFactors.mpr ⟨hr₁_pr, hdvd, hd_pos.ne'⟩
    have hlo : L₀ ≤ d * r₁ := by
      have h1 : L₀ < d * X := Nat.lt_mul_div_succ L₀ hd_pos
      have h2 : d * X ≤ d * r₁ := Nat.mul_le_mul_left d hr₁_gt.le
      omega
    have hhi : d * r₁ ≤ U₀ := by
      have h1 : d * r₁ ≤ d * (3 * X) := Nat.mul_le_mul_left d hr₁_le
      have h2 : d * (L₀ / d) ≤ L₀ := Nat.mul_div_le L₀ d
      have h3 : d * (3 * X) = 3 * (d * (L₀ / d)) + 3 * d := by dsimp [X]; ring
      omega
    have hhiN : 4 * P * (d * r₁) ≤ N := by
      have h1 : 4 * P * (d * r₁) ≤ 4 * P * U₀ := Nat.mul_le_mul_left _ hhi
      exact h1.trans (Nat.mul_div_le N (4 * P))
    refine ⟨r₁, hlo, hhiN, prime_dvd_lcmUpto hr₁_pr (hr₁_le.trans hA), hcop, ?_⟩
    rw [hr₁_pr.primeFactors, Finset.card_singleton]; decide
  · have hSX : S < 3 * X := lt_of_not_ge hA
    set Y₁ := S / 10 ^ 12
    have hY₁_big : 10 ^ 10 ≤ Y₁ := (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
    obtain ⟨r₁, hr₁_pr, hr₁_gt, hr₁_le, hr₁_av⟩ :=
      exists_prime_avoiding hY₁_big (by omega : d.primeFactors.card ≤ 3)
    have hr₁_S : r₁ ≤ S := by
      have : 10 ^ 12 * Y₁ ≤ S := Nat.mul_div_le S (10 ^ 12)
      omega
    have hcop₁ : Nat.Coprime d r₁ := by
      rw [Nat.coprime_comm]
      refine hr₁_pr.coprime_iff_not_dvd.mpr fun hdvd => hr₁_av ?_
      exact Nat.mem_primeFactors.mpr ⟨hr₁_pr, hdvd, hd_pos.ne'⟩
    set d₁ := d * r₁
    have hd₁_pos : 0 < d₁ := Nat.mul_pos hd_pos hr₁_pr.pos
    have hd₁_pf : d₁.primeFactors.card ≤ 3 := by
      calc d₁.primeFactors.card
          ≤ d.primeFactors.card + r₁.primeFactors.card := card_primeFactors_mul_le _ _
        _ ≤ 2 + 1 := by rw [hr₁_pr.primeFactors, Finset.card_singleton]; omega
        _ = 3 := rfl
    have hdS_le : d * S ≤ 4 * L₀ := by
      have h1 : S ≤ 4 * (L₀ / d) := by dsimp [X] at hSX; omega
      have h2 : d * S ≤ 4 * (d * (L₀ / d)) := by
        calc d * S ≤ d * (4 * (L₀ / d)) := Nat.mul_le_mul_left d h1
          _ = 4 * (d * (L₀ / d)) := by ring
      have h3 : d * (L₀ / d) ≤ L₀ := Nat.mul_div_le L₀ d
      omega
    have hr₁_ub : 10 ^ 12 * r₁ ≤ 3 * S := by
      have h1 : 10 ^ 12 * Y₁ ≤ S := Nat.mul_div_le S (10 ^ 12)
      omega
    have hd₁_L0 : 10 ^ 12 * d₁ ≤ 12 * L₀ := by
      calc 10 ^ 12 * d₁ = d * (10 ^ 12 * r₁) := by dsimp [d₁]; ring
        _ ≤ d * (3 * S) := Nat.mul_le_mul_left d hr₁_ub
        _ = 3 * (d * S) := by ring
        _ ≤ 3 * (4 * L₀) := Nat.mul_le_mul_left 3 hdS_le
        _ = 12 * L₀ := by ring
    set X₂ := L₀ / d₁ + 1
    have hX₂_big : 10 ^ 10 ≤ X₂ := by
      have h1 : 10 ^ 10 * d₁ ≤ L₀ := by omega
      have h2 : 10 ^ 10 ≤ L₀ / d₁ := (Nat.le_div_iff_mul_le hd₁_pos).mpr (by linarith)
      omega
    have h3X₂_S : 3 * X₂ ≤ S := by
      have hr₁_lb : S < 10 ^ 12 * r₁ := by
        have h1 : S < 10 ^ 12 * (Y₁ + 1) := Nat.lt_mul_div_succ S (by positivity)
        have h2 : 10 ^ 12 * (Y₁ + 1) ≤ 10 ^ 12 * r₁ := Nat.mul_le_mul_left _ hr₁_gt
        omega
      have hL₀_N : L₀ ≤ N := by
        have h1 : 16 * P * K ≤ N := by rw [hK_def]; exact Nat.mul_div_le N (16 * P)
        have h2 : K ≤ N := by nlinarith
        have : 16 * K ≤ N := by nlinarith
        omega
      have hprod_le : S * (L₀ / d₁) ≤ 10 ^ 12 * N := by
        calc S * (L₀ / d₁)
            ≤ (10 ^ 12 * r₁) * (L₀ / d₁) := Nat.mul_le_mul_right _ hr₁_lb.le
          _ ≤ (10 ^ 12 * d₁) * (L₀ / d₁) := by
              refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
              exact Nat.le_mul_of_pos_left r₁ hd_pos
          _ = 10 ^ 12 * (d₁ * (L₀ / d₁)) := by ring
          _ ≤ 10 ^ 12 * L₀ := Nat.mul_le_mul_left _ (Nat.mul_div_le L₀ d₁)
          _ ≤ 10 ^ 12 * N := Nat.mul_le_mul_left _ hL₀_N
      have hmul_S : (3 * X₂) * S ≤ S * S := by
        have h1 : (3 * X₂) * S = 3 * (S * (L₀ / d₁)) + 3 * S := by dsimp [X₂]; ring
        rw [h1]
        have h2 : 3 * S ≤ 10 ^ 12 * N := by omega
        linarith
      exact Nat.le_of_mul_le_mul_right hmul_S (by omega)
    obtain ⟨r₂, hr₂_pr, hr₂_gt, hr₂_le, hr₂_av⟩ :=
      exists_prime_avoiding hX₂_big hd₁_pf
    have hr₂_S : r₂ ≤ S := hr₂_le.trans h3X₂_S
    have hcop_d₁_r₂ : Nat.Coprime d₁ r₂ := by
      rw [Nat.coprime_comm]
      refine hr₂_pr.coprime_iff_not_dvd.mpr fun hdvd => hr₂_av ?_
      exact Nat.mem_primeFactors.mpr ⟨hr₂_pr, hdvd, hd₁_pos.ne'⟩
    have ⟨hcop_d_r₂, hcop_r₁_r₂⟩ := Nat.coprime_mul_iff_left.mp hcop_d₁_r₂
    have hcop_d_r : Nat.Coprime d (r₁ * r₂) := hcop₁.mul_right hcop_d_r₂
    have hr_dvd : r₁ * r₂ ∣ Nat.lcmUpto S :=
      hcop_r₁_r₂.mul_dvd_of_dvd_of_dvd (prime_dvd_lcmUpto hr₁_pr hr₁_S)
        (prime_dvd_lcmUpto hr₂_pr hr₂_S)
    have hlo : L₀ ≤ d * (r₁ * r₂) := by
      rw [← mul_assoc]
      change L₀ ≤ d₁ * r₂
      have h1 : L₀ < d₁ * X₂ := Nat.lt_mul_div_succ L₀ hd₁_pos
      have h2 : d₁ * X₂ ≤ d₁ * r₂ := Nat.mul_le_mul_left d₁ hr₂_gt.le
      omega
    have hhi : d * (r₁ * r₂) ≤ U₀ := by
      rw [← mul_assoc]
      change d₁ * r₂ ≤ U₀
      have h1 : d₁ * r₂ ≤ d₁ * (3 * X₂) := Nat.mul_le_mul_left d₁ hr₂_le
      have h2 : d₁ * (L₀ / d₁) ≤ L₀ := Nat.mul_div_le L₀ d₁
      have h3 : d₁ * (3 * X₂) = 3 * (d₁ * (L₀ / d₁)) + 3 * d₁ := by dsimp [X₂]; ring
      have h4 : 3 * d₁ + 4 ≤ L₀ := by omega
      omega
    have hhiN : 4 * P * (d * (r₁ * r₂)) ≤ N := by
      have h1 : 4 * P * (d * (r₁ * r₂)) ≤ 4 * P * U₀ := Nat.mul_le_mul_left _ hhi
      exact h1.trans (Nat.mul_div_le N (4 * P))
    have hpf : (r₁ * r₂).primeFactors.card ≤ 2 := by
      calc (r₁ * r₂).primeFactors.card
          ≤ r₁.primeFactors.card + r₂.primeFactors.card := card_primeFactors_mul_le _ _
        _ = 1 + 1 := by rw [hr₁_pr.primeFactors, hr₂_pr.primeFactors]; simp
        _ = 2 := rfl
    exact ⟨r₁ * r₂, hlo, hhiN, hr_dvd, hcop_d_r, hpf⟩

private lemma prod_P_inter_gt_N {N P M_bad : ℕ}
    (hN2 : 2 ≤ N)
    (hP_ge : 4 * Real.log (N : ℝ) ≤ (P : ℝ))
    (hP_big : 10 ^ 10 ≤ P)
    (hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2)
    {P₁ P₂ : Finset ℕ}
    (hP₁_sub : P₁ ⊆ (Ioc P (4 * P)).filter Nat.Prime)
    (_hP₂_sub : P₂ ⊆ (Ioc P (4 * P)).filter Nat.Prime)
    (hP₁_bad : ((Ioc P (4 * P)).filter Nat.Prime \ P₁).card ≤ M_bad + 4)
    (hP₂_bad : ((Ioc P (4 * P)).filter Nat.Prime \ P₂).card ≤ M_bad + 4) :
    N < ∏ p ∈ P₁ ∩ P₂, p := by
  let Pset := (Ioc P (4 * P)).filter Nat.Prime
  have hth : (P : ℝ) ≤ ∑ p ∈ Pset, Real.log (p : ℝ) := by
    rw [← theta_sub_eq_sum_Ioc (by omega : P ≤ 4 * P)]
    exact theta_four_sub_ge hP_big
  have hinter_sub : P₁ ∩ P₂ ⊆ Pset := Finset.inter_subset_left.trans hP₁_sub
  have hsdiff_sub : Pset \ (P₁ ∩ P₂) ⊆ (Pset \ P₁) ∪ (Pset \ P₂) := by
    intro p hp
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union] at hp ⊢
    by_cases h1 : p ∈ P₁
    · exact Or.inr ⟨hp.1, fun h2 => hp.2 ⟨h1, h2⟩⟩
    · exact Or.inl ⟨hp.1, h1⟩
  have hbad_card : (Pset \ (P₁ ∩ P₂)).card ≤ 2 * M_bad + 8 := by
    calc (Pset \ (P₁ ∩ P₂)).card
        ≤ ((Pset \ P₁) ∪ (Pset \ P₂)).card := Finset.card_le_card hsdiff_sub
      _ ≤ (Pset \ P₁).card + (Pset \ P₂).card := Finset.card_union_le _ _
      _ ≤ (M_bad + 4) + (M_bad + 4) := Nat.add_le_add hP₁_bad hP₂_bad
      _ = 2 * M_bad + 8 := by ring
  have hbad_sum : ∑ p ∈ Pset \ (P₁ ∩ P₂), Real.log (p : ℝ) ≤ (P : ℝ) / 2 := by
    calc ∑ p ∈ Pset \ (P₁ ∩ P₂), Real.log (p : ℝ)
        ≤ ∑ _p ∈ Pset \ (P₁ ∩ P₂), Real.log ((4 * P : ℕ) : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          have hpP := (mem_sdiff.mp hp).1
          have hp' := mem_filter.mp hpP
          exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast (mem_Ioc.mp hp'.1).2)
      _ = ((Pset \ (P₁ ∩ P₂)).card : ℝ) * Real.log ((4 * P : ℕ) : ℝ) := by simp
      _ ≤ (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4 * P by omega)))
          exact_mod_cast hbad_card
      _ ≤ (P : ℝ) / 2 := hM_le
  have hsplit := Finset.sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hinter_sub
  have hgood_log : (P : ℝ) / 2 ≤ ∑ p ∈ P₁ ∩ P₂, Real.log (p : ℝ) := by linarith
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogN_lt : Real.log (N : ℝ) < ∑ p ∈ P₁ ∩ P₂, Real.log (p : ℝ) := by linarith
  have hprod_pos : ∀ p ∈ P₁ ∩ P₂, (p : ℝ) ≠ 0 := fun p hp => by
    have hpP := mem_filter.mp (hinter_sub hp)
    exact_mod_cast hpP.2.ne_zero
  have hexp : (N : ℝ) < ((∏ p ∈ P₁ ∩ P₂, p : ℕ) : ℝ) := by
    rw [← Real.exp_log (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N)]
    have hlog_prod : Real.log ((∏ p ∈ P₁ ∩ P₂, p : ℕ) : ℝ) = ∑ p ∈ P₁ ∩ P₂, Real.log (p : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod hprod_pos]
    have hprod_gt0 : (0 : ℝ) < ((∏ p ∈ P₁ ∩ P₂, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      exact Finset.prod_pos fun p hp => by
        exact_mod_cast (mem_filter.mp (hinter_sub hp)).2.pos
    rw [← Real.exp_log hprod_gt0, hlog_prod]
    exact Real.exp_lt_exp.mpr hlogN_lt
  exact_mod_cast hexp

private noncomputable def Dof (N S K t : ℕ) (j : ℤ) : Finset ℕ :=
  let Q := Nat.lcmUpto S
  let A' := ((Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q).filter fun n => n.primeFactors.card ≤ 5
  (Nat.primesLE S).filter fun p =>
    (A'.filter fun n => qOf S p ∣ n ∧
      ¬ 2 * (j - 4 * (n : ℤ) * round ((j : ℝ) / (4 * n))).natAbs < K).card < t

private lemma exists_common_multiple_near_h {N S P K U t M_bad : ℕ}
    (hN2 : 2 ≤ N)
    (hS_big : 10 ^ 22 ≤ S)
    (hSN : S ≤ N)
    (hP_ge : 4 * Real.log (N : ℝ) ≤ (P : ℝ))
    (hP_big : 10 ^ 10 ≤ P)
    (h4P_S : 4 * P ≤ S)
    (hK_def : K = N / (16 * P))
    (hU_S : U ≤ S)
    (hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2)
    (havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1))
    (hSU_L0 : 10 ^ 11 * S * U ≤ K + 1)
    (hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S)
    (j : ℤ)
    (hDne : (Dof N S K t j).Nonempty) :
    ∃ x : ℤ, 2 * (j - x).natAbs < K ∧ ((4 * ∏ p ∈ Dof N S K t j, qOf S p : ℕ) : ℤ) ∣ x := by
  let Q := Nat.lcmUpto S
  let A' := ((Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q).filter fun n => n.primeFactors.card ≤ 5
  let jNear := fun n : ℕ => 2 * (j - 4 * (n : ℤ) * round ((j : ℝ) / (4 * n))).natAbs < K
  let D := Dof N S K t j
  let Pset := (Ioc P (4 * P)).filter Nat.Prime
  have hK_lt_N : K < N := by
    rw [hK_def]
    exact Nat.div_lt_self (by omega) (by omega)
  have hfor_p : ∀ p ∈ D,
      ∃ (x : ℤ) (Pp : Finset ℕ),
        2 * (j - x).natAbs < K ∧
        ((4 * qOf S p : ℕ) : ℤ) ∣ x ∧
        Pp ⊆ Pset ∧
        (Pset \ Pp).card ≤ M_bad + 4 ∧
        ∀ r ∈ Pp, (r : ℤ) ∣ x := by
    intro p hpD
    have ⟨hpS, hB_lt⟩ := mem_filter.mp hpD
    have hp_pr : p.Prime := Nat.prime_of_mem_primesLE hpS
    let B := A'.filter fun n => qOf S p ∣ n ∧ ¬ jNear n
    have hB_pos : ∀ n ∈ B, 0 < n := fun n hn => by
      have hn1 := (mem_filter.mp hn).1
      have hn2 := (mem_filter.mp hn1).1
      have hn3 := (mem_Icc.mp (mem_filter.mp hn2).1).1
      omega
    have hB_omega : ∀ n ∈ B, n.primeFactors.card ≤ 5 := fun n hn =>
      (mem_filter.mp (mem_filter.mp hn).1).2
    obtain ⟨p', hp'_er, hp'_bad⟩ := exists_good_p' hB_pos hB_omega hB_lt havg
    have hp'_mem : p' ∈ Nat.primesLE U := mem_of_mem_erase hp'_er
    have hp'_pr : p'.Prime := Nat.prime_of_mem_primesLE hp'_mem
    have hp'_ne : p' ≠ p := ne_of_mem_erase hp'_er
    have hp'_S : p' ≤ S := (Nat.le_of_mem_primesLE hp'_mem).trans hU_S
    obtain ⟨r, hr_lo, hr_hi, hr_dvd, hr_cop, hr_pf⟩ :=
      exists_multiplier_r hS_big hSN (by omega) hK_def hSU_L0 hCaseB_S hpS hp'_er
    set d := qOf S p * p'
    set m := d * r
    have hm_pos : 0 < m := by omega
    have hm_dvd_Q : m ∣ Q := by
      have hd_dvd : d ∣ Q :=
        (coprime_qOf_prime_of_ne hp_pr hp'_pr hp'_ne.symm).mul_dvd_of_dvd_of_dvd
          (qOf_dvd_lcmUpto hpS) (prime_dvd_lcmUpto hp'_pr hp'_S)
      exact hr_cop.mul_dvd_of_dvd_of_dvd hd_dvd hr_dvd
    have hm_pf : m.primeFactors.card ≤ 4 := by
      have hd_pf : d.primeFactors.card ≤ 2 := by
        calc d.primeFactors.card
            ≤ (qOf S p).primeFactors.card + p'.primeFactors.card := card_primeFactors_mul_le _ _
          _ ≤ ({p} : Finset ℕ).card + 1 := by
              rw [hp'_pr.primeFactors, Finset.card_singleton]
              exact Nat.add_le_add_right (Finset.card_le_card (primeFactors_qOf_subset hp_pr)) 1
          _ = 2 := by simp
      calc m.primeFactors.card ≤ d.primeFactors.card + r.primeFactors.card :=
            card_primeFactors_mul_le d r
        _ ≤ 2 + 2 := Nat.add_le_add hd_pf hr_pf
        _ = 4 := rfl
    have hmul_mem_A' : ∀ r' ∈ Pset, ¬ r' ∣ m → m * r' ∈ A' ∧ qOf S p ∣ m * r' := by
      intro r' hr' hndvd
      have ⟨hr'I, hr'_pr⟩ := mem_filter.mp hr'
      have ⟨hr'1, hr'2⟩ := mem_Ioc.mp hr'I
      have hcop_mr' : Nat.Coprime m r' := (hr'_pr.coprime_iff_not_dvd.mpr hndvd).symm
      have hmr'_dvd : m * r' ∣ Q :=
        hcop_mr'.mul_dvd_of_dvd_of_dvd hm_dvd_Q (prime_dvd_lcmUpto hr'_pr (hr'2.trans h4P_S))
      have hmr'_leN : m * r' ≤ N := by
        calc m * r' ≤ m * (4 * P) := Nat.mul_le_mul_left m hr'2
          _ = 4 * P * m := by ring
          _ ≤ N := hr_hi
      have hmr'_ge : N ≤ 16 * (m * r') := by
        have h1 : N < 16 * P * (K + 1) := by
          rw [hK_def]; exact Nat.lt_mul_div_succ N (by positivity)
        have h2 : 16 * P * (K + 1) ≤ 16 * r' * m := by
          have ha : 16 * P ≤ 16 * r' := Nat.mul_le_mul_left 16 hr'1.le
          exact Nat.mul_le_mul ha hr_lo
        nlinarith
      have hmr'_pf : (m * r').primeFactors.card ≤ 5 := by
        calc (m * r').primeFactors.card
            ≤ m.primeFactors.card + r'.primeFactors.card := card_primeFactors_mul_le _ _
          _ ≤ 4 + 1 := by rw [hr'_pr.primeFactors, Finset.card_singleton]; omega
          _ = 5 := rfl
      refine ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hm_pos hr'_pr.pos, hmr'_leN⟩, hmr'_ge, hmr'_dvd⟩,
        hmr'_pf⟩, ?_⟩
      exact (dvd_mul_right (qOf S p) p').trans ((dvd_mul_right d r).trans (dvd_mul_right m r'))
    let Pp := Pset.filter fun r' => ¬ r' ∣ m ∧ jNear (m * r')
    have hPp_sub : Pp ⊆ Pset := Finset.filter_subset _ _
    have hPp_bad : (Pset \ Pp).card ≤ M_bad + 4 := by
      let S_div := Pset.filter fun r' => r' ∣ m
      let S_far := Pset.filter fun r' => ¬ r' ∣ m ∧ ¬ jNear (m * r')
      have hcov : Pset \ Pp ⊆ S_div ∪ S_far := by
        intro r' hr'
        have ⟨hr'P, hr'n⟩ := mem_sdiff.mp hr'
        simp only [Pp, mem_filter] at hr'n
        by_cases hdvd : r' ∣ m
        · exact mem_union_left _ (mem_filter.mpr ⟨hr'P, hdvd⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨hr'P, hdvd, fun hjn => hr'n ⟨hr'P, hdvd, hjn⟩⟩)
      have hdiv_card : S_div.card ≤ 4 := by
        have hsub : S_div ⊆ m.primeFactors := by
          intro r' hr'
          have ⟨hr'P, hr'm⟩ := mem_filter.mp hr'
          exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hr'P).2, hr'm, hm_pos.ne'⟩
        exact (Finset.card_le_card hsub).trans hm_pf
      have hfar_card : S_far.card ≤ M_bad := by
        have hinj : S_far.card ≤ (B.filter (fun n => p' ∣ n)).card := by
          refine Finset.card_le_card_of_injOn (fun r' => m * r') ?_ ?_
          · intro r' hr'
            have ⟨hr'P, hndvd, hnjn⟩ := mem_filter.mp hr'
            obtain ⟨hA', hq⟩ := hmul_mem_A' r' hr'P hndvd
            have hp'_dvd : p' ∣ m * r' :=
              (dvd_mul_left p' (qOf S p)).trans ((dvd_mul_right d r).trans (dvd_mul_right m r'))
            exact mem_filter.mpr ⟨mem_filter.mpr ⟨hA', hq, hnjn⟩, hp'_dvd⟩
          · intro a _ b _ hab
            exact Nat.eq_of_mul_eq_mul_left hm_pos hab
        exact hinj.trans hp'_bad
      calc (Pset \ Pp).card ≤ (S_div ∪ S_far).card := Finset.card_le_card hcov
        _ ≤ S_div.card + S_far.card := Finset.card_union_le _ _
        _ ≤ 4 + M_bad := Nat.add_le_add hdiv_card hfar_card
        _ = M_bad + 4 := by omega
    have hPp_ne : Pp.Nonempty := by
      have hgt := prod_P_inter_gt_N hN2 hP_ge hP_big hM_le hPp_sub hPp_sub hPp_bad hPp_bad
      rw [Finset.inter_self] at hgt
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.prod_empty] at hgt
      omega
    obtain ⟨r₀, hr₀⟩ := hPp_ne
    have hr₀_jn : jNear (m * r₀) := (mem_filter.mp hr₀).2.2
    let x : ℤ := 4 * ((m * r₀ : ℕ) : ℤ) * round ((j : ℝ) / (4 * ((m * r₀ : ℕ) : ℝ)))
    have hx_near : 2 * (j - x).natAbs < K := by
      simpa only [jNear, x, Nat.cast_mul] using hr₀_jn
    have hx_4m : ((4 * m : ℕ) : ℤ) ∣ x := by
      refine ⟨(r₀ : ℤ) * round ((j : ℝ) / (4 * ((m * r₀ : ℕ) : ℝ))), ?_⟩
      dsimp only [x]; push_cast; ring
    have hx_4q : ((4 * qOf S p : ℕ) : ℤ) ∣ x := by
      have hqm : 4 * qOf S p ∣ 4 * m :=
        Nat.mul_dvd_mul_left 4 ((dvd_mul_right (qOf S p) p').trans (dvd_mul_right d r))
      exact (Int.natCast_dvd_natCast.mpr hqm).trans hx_4m
    have hx_div_Pp : ∀ r' ∈ Pp, (r' : ℤ) ∣ x := by
      intro r' hr'
      have hr'_jn : jNear (m * r') := (mem_filter.mp hr').2.2
      let y : ℤ := 4 * ((m * r' : ℕ) : ℤ) * round ((j : ℝ) / (4 * ((m * r' : ℕ) : ℝ)))
      have hy_near : 2 * (j - y).natAbs < K := by
        simpa only [jNear, y, Nat.cast_mul] using hr'_jn
      have hy_4m : ((4 * m : ℕ) : ℤ) ∣ y := by
        refine ⟨(r' : ℤ) * round ((j : ℝ) / (4 * ((m * r' : ℕ) : ℝ))), ?_⟩
        dsimp only [y]; push_cast; ring
      have hy_r' : (r' : ℤ) ∣ y := by
        refine ⟨4 * (m : ℤ) * round ((j : ℝ) / (4 * ((m * r' : ℕ) : ℝ))), ?_⟩
        dsimp only [y]; push_cast; ring
      have hdiff_dvd : 4 * m ∣ (x - y).natAbs :=
        Int.natCast_dvd.mp (dvd_sub hx_4m hy_4m)
      have hdiff_lt : (x - y).natAbs < 4 * m := by
        have htri : (x - y).natAbs ≤ (j - x).natAbs + (j - y).natAbs := by
          have heq : x - y = -(j - x) + (j - y) := by ring
          rw [heq]
          calc (-(j - x) + (j - y)).natAbs ≤ (-(j - x)).natAbs + (j - y).natAbs :=
                Int.natAbs_add_le _ _
            _ = (j - x).natAbs + (j - y).natAbs := by rw [Int.natAbs_neg]
        omega
      have hdiff0 : (x - y).natAbs = 0 := by
        by_contra hne
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiff_dvd
        omega
      have hxy : x = y := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hdiff0)
      rw [hxy]; exact hy_r'
    exact ⟨x, Pp, hx_near, hx_4q, hPp_sub, hPp_bad, hx_div_Pp⟩
  obtain ⟨p₀, hp₀⟩ := hDne
  obtain ⟨x₀, P₀, hx₀_near, _, hP₀_sub, hP₀_bad, hx₀_div⟩ := hfor_p p₀ hp₀
  have halleq : ∀ p ∈ D, ((4 * qOf S p : ℕ) : ℤ) ∣ x₀ := by
    intro p hp
    obtain ⟨x₁, P₁, hx₁_near, hx₁_4q, hP₁_sub, hP₁_bad, hx₁_div⟩ := hfor_p p hp
    have hgt : N < ∏ r ∈ P₀ ∩ P₁, r :=
      prod_P_inter_gt_N hN2 hP_ge hP_big hM_le hP₀_sub hP₁_sub hP₀_bad hP₁_bad
    have hprod_dvd : (∏ r ∈ P₀ ∩ P₁, r) ∣ (x₀ - x₁).natAbs := by
      refine prod_dvd_of_natCoprime ?_ fun r hr => ?_
      · intro a ha b hb hab
        have ha' := (mem_filter.mp (hP₀_sub (mem_inter.mp ha).1)).2
        have hb' := (mem_filter.mp (hP₀_sub (mem_inter.mp hb).1)).2
        exact (Nat.coprime_primes ha' hb').mpr hab
      · have hr0 := hx₀_div r (mem_inter.mp hr).1
        have hr1 := hx₁_div r (mem_inter.mp hr).2
        exact Int.natCast_dvd.mp (dvd_sub hr0 hr1)
    have hdiff_lt : (x₀ - x₁).natAbs < ∏ r ∈ P₀ ∩ P₁, r := by
      have htri : (x₀ - x₁).natAbs ≤ (j - x₀).natAbs + (j - x₁).natAbs := by
        have heq : x₀ - x₁ = -(j - x₀) + (j - x₁) := by ring
        rw [heq]
        calc (-(j - x₀) + (j - x₁)).natAbs ≤ (-(j - x₀)).natAbs + (j - x₁).natAbs :=
              Int.natAbs_add_le _ _
          _ = (j - x₀).natAbs + (j - x₁).natAbs := by rw [Int.natAbs_neg]
      omega
    have hdiff0 : (x₀ - x₁).natAbs = 0 := by
      by_contra hne
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hprod_dvd
      omega
    have hxeq : x₀ = x₁ := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hdiff0)
    rw [hxeq]; exact hx₁_4q
  refine ⟨x₀, hx₀_near, four_mul_prod_qOf_dvd (Finset.filter_subset _ _) ⟨p₀, hp₀⟩ halleq⟩

private lemma D_ne_primesLE {N S P K U t M_bad : ℕ}
    (hN2 : 2 ≤ N)
    (hS_big : 10 ^ 22 ≤ S)
    (hSN : S ≤ N)
    (hP_ge : 4 * Real.log (N : ℝ) ≤ (P : ℝ))
    (hP_big : 10 ^ 10 ≤ P)
    (h4P_S : 4 * P ≤ S)
    (hK_def : K = N / (16 * P))
    (hK_lt_Q : K < Nat.lcmUpto S)
    (hU_S : U ≤ S)
    (hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2)
    (havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1))
    (hSU_L0 : 10 ^ 11 * S * U ≤ K + 1)
    (hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S)
    (h : ZMod (4 * Nat.lcmUpto S))
    (hfar : N < 16 * h.valMinAbs.natAbs) :
    Dof N S K t h.valMinAbs ≠ Nat.primesLE S := by
  intro hEq
  let Q := Nat.lcmUpto S
  have hQ_pos : 0 < Q := Nat.lcmUpto_pos S
  have : NeZero (4 * Q) := ⟨by positivity⟩
  have hDne : (Dof N S K t h.valMinAbs).Nonempty := by
    rw [hEq]
    exact ⟨2, Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩⟩
  obtain ⟨x, hx_near, hx_dvd⟩ :=
    exists_common_multiple_near_h hN2 hS_big hSN hP_ge hP_big h4P_S hK_def hU_S hM_le havg
      hSU_L0 hCaseB_S h.valMinAbs hDne
  rw [hEq] at hx_dvd
  have hprodQ : ∏ p ∈ Nat.primesLE S, qOf S p = Q := (Nat.lcmUpto_eq_prod_pow_log S).symm
  rw [hprodQ] at hx_dvd
  have hx_dvd_nat : 4 * Q ∣ x.natAbs := Int.natCast_dvd.mp hx_dvd
  have hj_le : h.valMinAbs.natAbs ≤ 2 * Q := by
    have := ZMod.natAbs_valMinAbs_le h
    omega
  have hx_lt : x.natAbs < 4 * Q := by
    have htri : x.natAbs ≤ h.valMinAbs.natAbs + (h.valMinAbs - x).natAbs := by
      calc x.natAbs = (h.valMinAbs + -(h.valMinAbs - x)).natAbs := by congr 1; ring
        _ ≤ h.valMinAbs.natAbs + (-(h.valMinAbs - x)).natAbs := Int.natAbs_add_le _ _
        _ = h.valMinAbs.natAbs + (h.valMinAbs - x).natAbs := by rw [Int.natAbs_neg]
    omega
  have hx0 : x = 0 := by
    have h0 : x.natAbs = 0 := by
      by_contra hne
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hx_dvd_nat
      omega
    exact Int.natAbs_eq_zero.mp h0
  rw [hx0, sub_zero] at hx_near
  have hK_le : 16 * K ≤ N := by
    have h1 : 16 * P * K ≤ N := by rw [hK_def]; exact Nat.mul_div_le N (16 * P)
    nlinarith
  omega

private lemma weight_le_inv_pow {N S K t : ℕ}
    (hN2 : 2 ≤ N)
    (hK_pos : 0 < K)
    (ht_ge : 10800 * (N : ℝ) ^ 2 * Real.log (N : ℝ) / (K : ℝ) ^ 2 ≤ (t : ℝ))
    (j : ℤ) :
    let Q := Nat.lcmUpto S
    let A := (Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q
    let s := (Nat.primesLE S \ Dof N S K t j).card
    Real.exp (-(8 / 27 : ℝ) * ∑ n ∈ A,
      let x := (j : ℝ) / (4 * n)
      (x - round x) ^ 2) ≤ ((N : ℝ) ^ (10 * s))⁻¹ := by
  intro Q A s
  let A' := A.filter fun n => n.primeFactors.card ≤ 5
  let jNear := fun n : ℕ => 2 * (j - 4 * (n : ℤ) * round ((j : ℝ) / (4 * n))).natAbs < K
  let D := Dof N S K t j
  let f : ℕ → ℝ := fun n =>
    let x := (j : ℝ) / (4 * n)
    (x - round x) ^ 2
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => sq_nonneg _
  have hsubA : ∑ n ∈ A', f n ≤ ∑ n ∈ A, f n :=
    sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => hf_nonneg _
  have hdouble : ∑ p ∈ Nat.primesLE S, ∑ n ∈ A'.filter (fun n => qOf S p ∣ n), f n ≤
      5 * ∑ n ∈ A', f n := by
    have h1 : ∑ p ∈ Nat.primesLE S, ∑ n ∈ A'.filter (fun n => qOf S p ∣ n), f n =
        ∑ n ∈ A', (((Nat.primesLE S).filter (fun p => qOf S p ∣ n)).card : ℝ) * f n := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [h1, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    refine mul_le_mul_of_nonneg_right ?_ (hf_nonneg n)
    have hn_pos : 0 < n := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hn).1).1).1
    have hn_pf : n.primeFactors.card ≤ 5 := (mem_filter.mp hn).2
    have hsub : (Nat.primesLE S).filter (fun p => qOf S p ∣ n) ⊆ n.primeFactors := by
      intro p hp
      have ⟨hpS, hqn⟩ := mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primesLE hpS, (prime_dvd_qOf hpS).trans hqn, hn_pos.ne'⟩
    exact_mod_cast (Finset.card_le_card hsub).trans hn_pf
  have hterm_far : ∀ n ∈ A', ¬ jNear n → (K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2) ≤ f n := by
    intro n hn hnj
    have hnA := mem_filter.mp (mem_filter.mp hn).1
    have ⟨hn1, hnN⟩ := mem_Icc.mp hnA.1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hN_pos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hgeK : K ≤ 2 * (j - 4 * (n : ℤ) * round ((j : ℝ) / (4 * n))).natAbs := le_of_not_gt hnj
    have hgeK_real : (K : ℝ) ≤ 2 * |(j : ℝ) - 4 * (n : ℝ) * (round ((j : ℝ) / (4 * n)) : ℝ)| := by
      have hcast : (((j - 4 * (n : ℤ) * round ((j : ℝ) / (4 * n))).natAbs : ℕ) : ℝ) =
          |(j : ℝ) - 4 * (n : ℝ) * (round ((j : ℝ) / (4 * n)) : ℝ)| := by
        rw [← Int.cast_natCast, ← Int.abs_eq_natAbs, Int.cast_abs]
        push_cast; rfl
      rw [← hcast]
      exact_mod_cast hgeK
    have hfrac : (j : ℝ) / (4 * (n : ℝ)) - (round ((j : ℝ) / (4 * (n : ℝ))) : ℝ) =
        ((j : ℝ) - 4 * (n : ℝ) * (round ((j : ℝ) / (4 * (n : ℝ))) : ℝ)) / (4 * (n : ℝ)) := by
      field_simp [hn_pos.ne']
    have habs : (K : ℝ) / (8 * (N : ℝ)) ≤
        |(j : ℝ) / (4 * (n : ℝ)) - (round ((j : ℝ) / (4 * (n : ℝ))) : ℝ)| := by
      rw [hfrac, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * (n : ℝ))]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      have h1 : (K : ℝ) * (4 * (n : ℝ)) ≤ (K : ℝ) * (4 * (N : ℝ)) := by nlinarith
      nlinarith
    have hsq := pow_le_pow_left₀ (by positivity) habs 2
    rw [sq_abs] at hsq
    have heq : ((K : ℝ) / (8 * (N : ℝ))) ^ 2 = (K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2) := by ring
    dsimp only [f]
    linarith
  have hbad_lower : (s : ℝ) * ((t : ℝ) * ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2))) ≤
      ∑ p ∈ Nat.primesLE S, ∑ n ∈ A'.filter (fun n => qOf S p ∣ n), f n := by
    calc (s : ℝ) * ((t : ℝ) * ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2)))
        = ∑ _p ∈ Nat.primesLE S \ D, (t : ℝ) * ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2)) := by
          simp only [Finset.sum_const, nsmul_eq_mul, s, D]
      _ ≤ ∑ p ∈ Nat.primesLE S \ D,
            ∑ n ∈ A'.filter (fun n => qOf S p ∣ n ∧ ¬ jNear n), f n := by
          refine sum_le_sum fun p hp => ?_
          have ⟨hpS, hpD⟩ := mem_sdiff.mp hp
          have hcard : t ≤ (A'.filter (fun n => qOf S p ∣ n ∧ ¬ jNear n)).card := by
            by_contra hlt
            exact hpD (mem_filter.mpr ⟨hpS, lt_of_not_ge hlt⟩)
          calc (t : ℝ) * ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2))
              ≤ ((A'.filter (fun n => qOf S p ∣ n ∧ ¬ jNear n)).card : ℝ) *
                  ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2)) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
            _ = ∑ _n ∈ A'.filter (fun n => qOf S p ∣ n ∧ ¬ jNear n),
                  (K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2) := by simp
            _ ≤ ∑ n ∈ A'.filter (fun n => qOf S p ∣ n ∧ ¬ jNear n), f n :=
                sum_le_sum fun n hn => hterm_far n (mem_filter.mp hn).1 (mem_filter.mp hn).2.2
      _ ≤ ∑ p ∈ Nat.primesLE S \ D, ∑ n ∈ A'.filter (fun n => qOf S p ∣ n), f n := by
          refine sum_le_sum fun p _ => sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hf_nonneg _
          intro n hn; have ⟨h1, h2, _⟩ := mem_filter.mp hn; exact mem_filter.mpr ⟨h1, h2⟩
      _ ≤ ∑ p ∈ Nat.primesLE S, ∑ n ∈ A'.filter (fun n => qOf S p ∣ n), f n :=
          sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ =>
            sum_nonneg fun _ _ => hf_nonneg _
  have hK_pos' : (0 : ℝ) < K := by exact_mod_cast hK_pos
  have hN_pos' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht_mul : 10800 * Real.log (N : ℝ) / 64 ≤ (t : ℝ) * ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2)) := by
    have h1 := mul_le_mul_of_nonneg_right ht_ge (by positivity : 0 ≤ (K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2))
    have heq : 10800 * (N : ℝ) ^ 2 * Real.log (N : ℝ) / (K : ℝ) ^ 2 *
        ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2)) = 10800 * Real.log (N : ℝ) / 64 := by
      field_simp [hK_pos'.ne', hN_pos'.ne']
    linarith
  have hexp_le : -(8 / 27 : ℝ) * ∑ n ∈ A, f n ≤ -((10 * s : ℕ) : ℝ) * Real.log (N : ℝ) := by
    have h1 : (s : ℝ) * (10800 * Real.log (N : ℝ) / 64) ≤ 5 * ∑ n ∈ A, f n := by
      have hmul := mul_le_mul_of_nonneg_left ht_mul (Nat.cast_nonneg s)
      linarith
    push_cast
    linarith
  calc Real.exp (-(8 / 27 : ℝ) * ∑ n ∈ A, f n)
      ≤ Real.exp (-((10 * s : ℕ) : ℝ) * Real.log (N : ℝ)) := Real.exp_le_exp.mpr hexp_le
    _ = ((N : ℝ) ^ (10 * s))⁻¹ := by
        rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hN_pos']

private lemma card_far_with_D_le {N S P K U t M_bad : ℕ}
    (hN4 : 4 ≤ N)
    (hS_big : 10 ^ 22 ≤ S)
    (hSN : S ≤ N)
    (hP_ge : 4 * Real.log (N : ℝ) ≤ (P : ℝ))
    (hP_big : 10 ^ 10 ≤ P)
    (h4P_S : 4 * P ≤ S)
    (hK_def : K = N / (16 * P))
    (hU_S : U ≤ S)
    (hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2)
    (havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1))
    (hSU_L0 : 10 ^ 11 * S * U ≤ K + 1)
    (hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S)
    (D : Finset ℕ) (hDsub : D ⊆ Nat.primesLE S) :
    let Q := Nat.lcmUpto S
    letI : NeZero Q := ⟨Nat.lcmUpto_ne_zero S⟩
    let s := (Nat.primesLE S \ D).card
    (univ.filter fun h : ZMod (4 * Q) => N < 16 * h.valMinAbs.natAbs ∧ Dof N S K t h.valMinAbs = D).card ≤
      N ^ (s + 1) := by
  dsimp only
  set Q := Nat.lcmUpto S
  have : NeZero Q := ⟨Nat.lcmUpto_ne_zero S⟩
  set s := (Nat.primesLE S \ D).card
  let H := univ.filter fun h : ZMod (4 * Q) => N < 16 * h.valMinAbs.natAbs ∧ Dof N S K t h.valMinAbs = D
  have hprod_split : (∏ p ∈ D, qOf S p) * (∏ p ∈ Nat.primesLE S \ D, qOf S p) = Q := by
    rw [mul_comm, Finset.prod_sdiff hDsub]
    exact (Nat.lcmUpto_eq_prod_pow_log S).symm
  have hR_le : ∏ p ∈ Nat.primesLE S \ D, qOf S p ≤ N ^ s := by
    calc ∏ p ∈ Nat.primesLE S \ D, qOf S p
        ≤ ∏ _p ∈ Nat.primesLE S \ D, N :=
          Finset.prod_le_prod' fun p _ => (qOf_le_S (by omega)).trans hSN
      _ = N ^ s := by simp [s]
  by_cases hDne : D.Nonempty
  · set M := 4 * ∏ p ∈ D, qOf S p
    set R := ∏ p ∈ Nat.primesLE S \ D, qOf S p
    have hMR : M * R = 4 * Q := by
      dsimp [M, R]; rw [mul_assoc, hprod_split]
    have hR_pos : 0 < R := Finset.prod_pos fun p hp => qOf_pos (Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1)
    let box := Finset.range R ×ˢ Finset.Icc (-(K / 2 : ℤ)) (K / 2 : ℤ)
    let φ : ℕ × ℤ → ZMod (4 * Q) := fun p => ((M * p.1 : ℕ) : ZMod (4 * Q)) + (p.2 : ZMod (4 * Q))
    have hsub_img : H ⊆ box.image φ := by
      intro h hh
      have ⟨_, hD_eq⟩ := (mem_filter.mp hh).2
      have hDne' : (Dof N S K t h.valMinAbs).Nonempty := hD_eq.symm ▸ hDne
      obtain ⟨x, hx_near, hx_dvd⟩ :=
        exists_common_multiple_near_h (by omega) hS_big hSN hP_ge hP_big h4P_S hK_def hU_S hM_le
          havg hSU_L0 hCaseB_S h.valMinAbs hDne'
      rw [hD_eq] at hx_dvd
      obtain ⟨u, hu⟩ := hx_dvd
      set r_int : ℤ := u % (R : ℤ)
      have hr_nonneg : 0 ≤ r_int := Int.emod_nonneg u (by exact_mod_cast hR_pos.ne')
      have hr_lt : r_int < (R : ℤ) := Int.emod_lt_of_pos u (by exact_mod_cast hR_pos)
      set r_nat : ℕ := r_int.toNat
      have hr_nat_lt : r_nat < R := by omega
      have hr_cast : (r_nat : ℤ) = r_int := Int.toNat_of_nonneg hr_nonneg
      set d_int : ℤ := h.valMinAbs - x
      have hd_mem : d_int ∈ Finset.Icc (-(K / 2 : ℤ)) (K / 2 : ℤ) := by
        rw [mem_Icc]
        have h1 : 2 * d_int.natAbs < K := hx_near
        have h2 : |d_int| = (d_int.natAbs : ℤ) := Int.abs_eq_natAbs d_int
        have h3 : -(d_int.natAbs : ℤ) ≤ d_int ∧ d_int ≤ (d_int.natAbs : ℤ) := abs_le.mp (le_of_eq h2)
        omega
      refine mem_image.mpr ⟨(r_nat, d_int), mem_product.mpr ⟨mem_range.mpr hr_nat_lt, hd_mem⟩, ?_⟩
      dsimp only [φ]
      have hx_mod : (x : ZMod (4 * Q)) = ((M * r_nat : ℕ) : ZMod (4 * Q)) := by
        have hdiv_mod : u = (R : ℤ) * (u / (R : ℤ)) + r_int := by
          have := Int.emod_add_mul_ediv u (R : ℤ)
          dsimp [r_int]; linarith
        have hx_eq : x = ((4 * Q : ℕ) : ℤ) * (u / (R : ℤ)) + ((M * r_nat : ℕ) : ℤ) := by
          have hMR' : ((4 * Q : ℕ) : ℤ) = (M : ℤ) * (R : ℤ) := by exact_mod_cast hMR.symm
          have hu' : x = (M : ℤ) * u := hu
          rw [hu', hMR']
          conv_lhs => rw [hdiv_mod, ← hr_cast]
          push_cast; ring
        rw [hx_eq]
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add]
      rw [← hx_mod, ← Int.cast_add, show x + d_int = h.valMinAbs by dsimp [d_int]; ring]
      exact h.coe_valMinAbs
    have hK_le : K + 1 ≤ N := by
      have h1 : 16 * P * K ≤ N := by rw [hK_def]; exact Nat.mul_div_le N (16 * P)
      nlinarith
    have hIcc_card : (Finset.Icc (-(K / 2 : ℤ)) (K / 2 : ℤ)).card ≤ N := by
      rw [Int.card_Icc]
      omega
    calc H.card ≤ (box.image φ).card := Finset.card_le_card hsub_img
      _ ≤ box.card := Finset.card_image_le
      _ = R * (Finset.Icc (-(K / 2 : ℤ)) (K / 2 : ℤ)).card := by simp [box]
      _ ≤ N ^ s * N := Nat.mul_le_mul hR_le hIcc_card
      _ = N ^ (s + 1) := by rw [pow_succ]
  · rw [Finset.not_nonempty_iff_eq_empty] at hDne
    have hH_le : H.card ≤ Fintype.card (ZMod (4 * Q)) := Finset.card_le_univ H
    rw [ZMod.card (4 * Q)] at hH_le
    have hQ_eq : Q = ∏ p ∈ Nat.primesLE S \ D, qOf S p := by
      rw [hDne, Finset.sdiff_empty]; exact Nat.lcmUpto_eq_prod_pow_log S
    calc H.card ≤ 4 * Q := hH_le
      _ = 4 * ∏ p ∈ Nat.primesLE S \ D, qOf S p := by rw [hQ_eq]
      _ ≤ N * N ^ s := Nat.mul_le_mul hN4 hR_le
      _ = N ^ (s + 1) := by rw [pow_succ']

private lemma choose_le_pow_self (n k : ℕ) : n.choose k ≤ n ^ k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp
    | succ m =>
      have h1 : (m + 1).choose (k + 1) * (k + 1) = (m + 1) * m.choose k := by
        have := Nat.add_one_mul_choose_eq m k
        linarith
      have h2 : (m + 1).choose (k + 1) ≤ (m + 1) * m.choose k := by
        calc (m + 1).choose (k + 1) ≤ (m + 1).choose (k + 1) * (k + 1) :=
              Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
          _ = (m + 1) * m.choose k := h1
      calc (m + 1).choose (k + 1) ≤ (m + 1) * m.choose k := h2
        _ ≤ (m + 1) * m ^ k := Nat.mul_le_mul_left _ (ih m)
        _ ≤ (m + 1) * (m + 1) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ m) k)
        _ = (m + 1) ^ (k + 1) := by rw [pow_succ']

private lemma far_sum_lt_half {N S P K U t M_bad : ℕ}
    (hN4 : 4 ≤ N)
    (hS_big : 10 ^ 22 ≤ S)
    (hSN : S ≤ N)
    (hP_ge : 4 * Real.log (N : ℝ) ≤ (P : ℝ))
    (hP_big : 10 ^ 10 ≤ P)
    (h4P_S : 4 * P ≤ S)
    (hK_def : K = N / (16 * P))
    (hK_pos : 0 < K)
    (hK_lt_Q : K < Nat.lcmUpto S)
    (hU_S : U ≤ S)
    (ht_ge : 10800 * (N : ℝ) ^ 2 * Real.log (N : ℝ) / (K : ℝ) ^ 2 ≤ (t : ℝ))
    (hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2)
    (havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1))
    (hSU_L0 : 10 ^ 11 * S * U ≤ K + 1)
    (hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S) :
    let Q := Nat.lcmUpto S
    letI : NeZero Q := ⟨Nat.lcmUpto_ne_zero S⟩
    let A := (Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q
    let far := univ.filter fun h : ZMod (4 * Q) => N < 16 * h.valMinAbs.natAbs
    (∑ h ∈ far, Real.exp (-(8 / 27 : ℝ) * ∑ n ∈ A,
      let x := (h.valMinAbs : ℝ) / (4 * n)
      (x - round x) ^ 2)) < 1 / 2 := by
  dsimp only
  set Q := Nat.lcmUpto S
  have : NeZero Q := ⟨Nat.lcmUpto_ne_zero S⟩
  set A := (Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q
  set far := univ.filter fun h : ZMod (4 * Q) => N < 16 * h.valMinAbs.natAbs
  let DofH : ZMod (4 * Q) → Finset ℕ := fun h => Dof N S K t h.valMinAbs
  let W : ZMod (4 * Q) → ℝ := fun h =>
    Real.exp (-(8 / 27 : ℝ) * ∑ n ∈ A,
      let x := (h.valMinAbs : ℝ) / (4 * n)
      (x - round x) ^ 2)
  let PS := Nat.primesLE S
  have hPS_le_N : PS.card ≤ N := by
    have hsub : PS ⊆ Icc 1 S := by
      intro p hp
      have ⟨hpS, hpr⟩ := Nat.mem_primesLE.mp hp
      exact mem_Icc.mpr ⟨hpr.one_le, hpS⟩
    calc PS.card ≤ (Icc 1 S).card := Finset.card_le_card hsub
      _ = S := by simp
      _ ≤ N := hSN
  have hmaps : ∀ h ∈ far, DofH h ∈ PS.powerset.erase PS := by
    intro h hh
    refine mem_erase.mpr ⟨?_, mem_powerset.mpr (Finset.filter_subset _ _)⟩
    exact D_ne_primesLE (by omega) hS_big hSN hP_ge hP_big h4P_S hK_def hK_lt_Q hU_S hM_le havg
      hSU_L0 hCaseB_S h (mem_filter.mp hh).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps W]
  have hfiber_le : ∀ D ∈ PS.powerset.erase PS,
      ∑ h ∈ far.filter (fun h => DofH h = D), W h ≤
        ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ := by
    intro D hD
    have hDsub : D ⊆ PS := mem_powerset.mp (mem_of_mem_erase hD)
    have hcard := card_far_with_D_le hN4 hS_big hSN hP_ge hP_big h4P_S hK_def hU_S hM_le havg
      hSU_L0 hCaseB_S D hDsub
    have hfilt_eq : far.filter (fun h => DofH h = D) =
        univ.filter fun h : ZMod (4 * Q) => N < 16 * h.valMinAbs.natAbs ∧ Dof N S K t h.valMinAbs = D := by
      ext h; simp [far, DofH]
    calc ∑ h ∈ far.filter (fun h => DofH h = D), W h
        ≤ ∑ _h ∈ far.filter (fun h => DofH h = D), ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ := by
          refine sum_le_sum fun h hh => ?_
          have hEq : Dof N S K t h.valMinAbs = D := (mem_filter.mp hh).2
          simpa only [W, A, Q, PS, hEq] using
            weight_le_inv_pow (S := S) (by omega) hK_pos ht_ge h.valMinAbs
      _ = ((far.filter (fun h => DofH h = D)).card : ℝ) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ := by simp
      _ ≤ ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hfilt_eq]
          exact_mod_cast hcard
  have hsum1 : ∑ D ∈ PS.powerset.erase PS, ∑ h ∈ far.filter (fun h => DofH h = D), W h ≤
      ∑ D ∈ PS.powerset.erase PS, ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ :=
    sum_le_sum hfiber_le
  have hmaps_s : ∀ D ∈ PS.powerset.erase PS, (PS \ D).card ∈ Icc 1 PS.card := by
    intro D hD
    have ⟨hne, hsub⟩ := mem_erase.mp hD
    have hsub' : D ⊆ PS := mem_powerset.mp hsub
    have hs_pos : 1 ≤ (PS \ D).card := by
      by_contra h0
      have hemp : PS \ D = ∅ := Finset.card_eq_zero.mp (by omega)
      exact hne (Finset.Subset.antisymm hsub' (Finset.sdiff_eq_empty_iff_subset.mp hemp))
    exact mem_Icc.mpr ⟨hs_pos, Finset.card_le_card Finset.sdiff_subset⟩
  conv_rhs at hsum1 => rw [← Finset.sum_fiberwise_of_maps_to hmaps_s]
  have hN_pos : (0 : ℝ) < N := by positivity
  have hN_ge4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hterm_s : ∀ s ∈ Icc 1 PS.card,
      ∑ D ∈ (PS.powerset.erase PS).filter (fun D => (PS \ D).card = s),
        ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ ≤
        ((N : ℝ) ^ 7)⁻¹ := by
    intro s hs
    have hs1 : 1 ≤ s := (mem_Icc.mp hs).1
    have hcard_D : ((PS.powerset.erase PS).filter (fun D => (PS \ D).card = s)).card ≤ N ^ s := by
      have hinj : ((PS.powerset.erase PS).filter (fun D => (PS \ D).card = s)).card ≤
          (PS.powersetCard s).card := by
        refine Finset.card_le_card_of_injOn (fun D => PS \ D) ?_ ?_
        · intro D hD
          have ⟨h1, h2⟩ := mem_filter.mp hD
          exact mem_powersetCard.mpr ⟨Finset.sdiff_subset, h2⟩
        · intro D₁ hD₁ D₂ hD₂ heq
          dsimp only at heq
          have hsub₁ : D₁ ⊆ PS := mem_powerset.mp (mem_of_mem_erase (mem_filter.mp hD₁).1)
          have hsub₂ : D₂ ⊆ PS := mem_powerset.mp (mem_of_mem_erase (mem_filter.mp hD₂).1)
          rw [← Finset.sdiff_sdiff_eq_self hsub₁, ← Finset.sdiff_sdiff_eq_self hsub₂, heq]
      calc ((PS.powerset.erase PS).filter (fun D => (PS \ D).card = s)).card
          ≤ (PS.powersetCard s).card := hinj
        _ = PS.card.choose s := Finset.card_powersetCard s PS
        _ ≤ PS.card ^ s := choose_le_pow_self PS.card s
        _ ≤ N ^ s := Nat.pow_le_pow_left hPS_le_N s
    have hpow_le : (N : ℝ) ^ s * ((N : ℝ) ^ (s + 1) * ((N : ℝ) ^ (10 * s))⁻¹) ≤ ((N : ℝ) ^ 7)⁻¹ := by
      have h1 : (N : ℝ) ^ s * ((N : ℝ) ^ (s + 1) * ((N : ℝ) ^ (10 * s))⁻¹) =
          ((N : ℝ) ^ (2 * s + 1)) / ((N : ℝ) ^ (10 * s)) := by
        rw [div_eq_mul_inv, ← mul_assoc, ← pow_add]
        congr 2; omega
      rw [h1, ← one_div, div_le_div_iff₀ (pow_pos hN_pos _) (pow_pos hN_pos _), one_mul, ← pow_add]
      exact pow_le_pow_right₀ (by linarith) (by omega : 2 * s + 1 + 7 ≤ 10 * s)
    calc ∑ D ∈ (PS.powerset.erase PS).filter (fun D => (PS \ D).card = s),
            ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹
        = ∑ _D ∈ (PS.powerset.erase PS).filter (fun D => (PS \ D).card = s),
            ((N : ℝ) ^ (s + 1)) * ((N : ℝ) ^ (10 * s))⁻¹ :=
          Finset.sum_congr rfl fun D hD => by rw [(mem_filter.mp hD).2]
      _ = (((PS.powerset.erase PS).filter (fun D => (PS \ D).card = s)).card : ℝ) *
            (((N : ℝ) ^ (s + 1)) * ((N : ℝ) ^ (10 * s))⁻¹) := by simp
      _ ≤ (N : ℝ) ^ s * (((N : ℝ) ^ (s + 1)) * ((N : ℝ) ^ (10 * s))⁻¹) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_D) (by positivity)
      _ ≤ ((N : ℝ) ^ 7)⁻¹ := hpow_le
  have hsum2 : ∑ s ∈ Icc 1 PS.card,
      ∑ D ∈ (PS.powerset.erase PS).filter (fun D => (PS \ D).card = s),
        ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ ≤
      (N : ℝ) * ((N : ℝ) ^ 7)⁻¹ := by
    calc _ ≤ ∑ _s ∈ Icc 1 PS.card, ((N : ℝ) ^ 7)⁻¹ := sum_le_sum hterm_s
      _ = ((Icc 1 PS.card).card : ℝ) * ((N : ℝ) ^ 7)⁻¹ := by simp
      _ ≤ (N : ℝ) * ((N : ℝ) ^ 7)⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Icc]; exact_mod_cast (show PS.card + 1 - 1 ≤ N by omega)
  have hfinal : (N : ℝ) * ((N : ℝ) ^ 7)⁻¹ < 1 / 2 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ (pow_pos hN_pos 7)]
    have hN6 : (4 : ℝ) ^ 6 ≤ (N : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hN_ge4 6
    have hpow : (N : ℝ) ^ 7 = (N : ℝ) * (N : ℝ) ^ 6 := by ring
    rw [hpow]
    nlinarith
  exact lt_of_le_of_lt (hsum1.trans hsum2) hfinal

end MinorArcCore

/- ## Section 3: Asymptotic parameter verification for `c = 1` -/

section Asymptotics

private lemma pow_seven_le_exp_quarter {L : ℝ} (hL : 10 ^ 16 ≤ L) :
    L ^ 7 ≤ Real.exp (L / 4) := by
  have hpow := Real.pow_div_factorial_le_exp (L / 4) (by linarith) 8
  have hfac : (Nat.factorial 8 : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [hfac] at hpow
  have h1 : L ^ 7 * (4 ^ 8 * 40320 : ℝ) ≤ L ^ 8 := by
    have ha : (4 ^ 8 * 40320 : ℝ) ≤ L := by linarith
    have hb := mul_le_mul_of_nonneg_left ha (pow_nonneg (by linarith : 0 ≤ L) 7)
    linarith [show L ^ 7 * L = L ^ 8 by ring]
  have h2 : L ^ 7 ≤ (L / 4) ^ 8 / 40320 := by
    have heq : (L / 4) ^ 8 / 40320 = L ^ 8 / (4 ^ 8 * 40320) := by ring
    rw [heq, le_div_iff₀ (by norm_num)]
    exact h1
  exact h2.trans hpow

private lemma params_avg_bound {N P K U t M_bad : ℕ} {L LL : ℝ}
    (hN_pos : (0 : ℝ) < N)
    (hL_ge : 10 ^ 16 ≤ L)
    (hLL_ge : 10 ^ 15 ≤ LL)
    (hLL_def : LL = Real.log L)
    (hP_ge : 4 * L ≤ (P : ℝ))
    (hP_le : (P : ℝ) ≤ 5 * L)
    (hP_big : 10 ^ 10 ≤ P)
    (hK_real_lo : (N : ℝ) / (100 * L) ≤ (K : ℝ))
    (hU_hi : (U : ℝ) ≤ L ^ 2 * LL ^ 3)
    (hU_lo : L ^ 2 * LL ^ 3 / 2 ≤ (U : ℝ))
    (hU_big : 10 ^ 10 ≤ U)
    (ht_def : t = ⌈10800 * (N : ℝ) ^ 2 * L / (K : ℝ) ^ 2⌉₊)
    (hM_def : M_bad = ⌊(P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ))⌋₊) :
    5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1) := by
  have hL_pos : 0 < L := by linarith
  have hLL_pos : 0 < LL := by linarith
  have hLL_le_L : LL ≤ L := by rw [hLL_def]; linarith [Real.log_le_sub_one_of_pos hL_pos]
  have ht_ub : (t : ℝ) ≤ 2 * 10 ^ 8 * L ^ 3 := by
    have h1 : (t : ℝ) < 10800 * (N : ℝ) ^ 2 * L / (K : ℝ) ^ 2 + 1 := by
      rw [ht_def]; exact Nat.ceil_lt_add_one (by positivity)
    have hK2 : ((N : ℝ) / (100 * L)) ^ 2 ≤ (K : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hK_real_lo 2
    have h2 : 10800 * (N : ℝ) ^ 2 * L / (K : ℝ) ^ 2 ≤
        10800 * (N : ℝ) ^ 2 * L / ((N : ℝ) / (100 * L)) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hK2
    have heq : 10800 * (N : ℝ) ^ 2 * L / ((N : ℝ) / (100 * L)) ^ 2 = 10800 * 10000 * L ^ 3 := by
      field_simp [hN_pos.ne', hL_pos.ne']; ring
    have hL3 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hlogU_ub : Real.log (U : ℝ) ≤ 5 * LL := by
    have h1 : (U : ℝ) ≤ L ^ 5 := by
      have ha : LL ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hLL_pos.le hLL_le_L 3
      calc (U : ℝ) ≤ L ^ 2 * LL ^ 3 := hU_hi
        _ ≤ L ^ 2 * L ^ 3 := mul_le_mul_of_nonneg_left ha (by positivity)
        _ = L ^ 5 := by ring
    have h2 := Real.log_le_log (by exact_mod_cast (show 0 < U by omega)) h1
    rw [Real.log_pow, ← hLL_def] at h2
    exact h2
  have hpiU_lo : L ^ 2 * LL ^ 2 / 20 ≤ ((Nat.primesLE U).card : ℝ) := by
    have h1 := card_primesLE_ge hU_big
    have hlogU_pos : 0 < Real.log (U : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < U by omega))
    have h2 : L ^ 2 * LL ^ 3 / 2 / (2 * (5 * LL)) ≤ (U : ℝ) / (2 * Real.log (U : ℝ)) :=
      div_le_div₀ (by positivity) hU_lo (by positivity) (by linarith)
    have heq : L ^ 2 * LL ^ 3 / 2 / (2 * (5 * LL)) = L ^ 2 * LL ^ 2 / 20 := by
      field_simp [hLL_pos.ne']; ring
    linarith
  have hpiU_sub : L ^ 2 * LL ^ 2 / 40 ≤ (((Nat.primesLE U).card - 1 : ℕ) : ℝ) := by
    have hLL2 : (1 : ℝ) ≤ LL ^ 2 := one_le_pow₀ (by linarith)
    have hL2 : (10 ^ 20 : ℝ) ≤ L ^ 2 := by nlinarith only [hL_ge]
    have hpi_ge2 : (40 : ℝ) ≤ L ^ 2 * LL ^ 2 / 40 := by nlinarith only [hL2, hLL2]
    have hpi_nat : 1 ≤ (Nat.primesLE U).card := by
      have : (1 : ℝ) ≤ ((Nat.primesLE U).card : ℝ) := by linarith
      exact_mod_cast this
    rw [Nat.cast_sub hpi_nat, Nat.cast_one]
    linarith
  have hlog4P_ub : Real.log ((4 * P : ℕ) : ℝ) ≤ 2 * LL := by
    have h1 : ((4 * P : ℕ) : ℝ) ≤ L ^ 2 := by
      push_cast; nlinarith only [hP_le, hL_ge]
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, ← hLL_def] at h2
    exact h2
  have hlog4P_pos : 0 < Real.log ((4 * P : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 4 * P by omega))
  have hM1_lo : L / (4 * LL) ≤ ((M_bad + 1 : ℕ) : ℝ) := by
    have h1 : (P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ)) < ((M_bad + 1 : ℕ) : ℝ) := by
      rw [hM_def]; push_cast; exact Nat.lt_floor_add_one _
    have h2 : 4 * L / (8 * (2 * LL)) ≤ (P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ)) :=
      div_le_div₀ (by positivity) hP_ge (by positivity) (by linarith)
    have heq : 4 * L / (8 * (2 * LL)) = L / (4 * LL) := by field_simp [hLL_pos.ne']; ring
    linarith
  have hprod_lo : L ^ 3 * LL / 160 ≤
      (((Nat.primesLE U).card - 1 : ℕ) : ℝ) * ((M_bad + 1 : ℕ) : ℝ) := by
    have hmul := mul_le_mul hpiU_sub hM1_lo (by positivity) (by positivity)
    have heq : (L ^ 2 * LL ^ 2 / 40) * (L / (4 * LL)) = L ^ 3 * LL / 160 := by
      field_simp [hLL_pos.ne']; ring
    linarith
  have hreal : ((5 * t : ℕ) : ℝ) ≤ (((Nat.primesLE U).card - 1) * (M_bad + 1) : ℕ) := by
    push_cast
    push_cast at hprod_lo
    have h1 : 10 ^ 9 * L ^ 3 ≤ L ^ 3 * LL / 160 := by
      rw [le_div_iff₀ (by norm_num)]
      have ha : (160 * 10 ^ 9 : ℝ) ≤ LL := by linarith
      nlinarith only [ha, pow_pos hL_pos 3]
    linarith
  exact_mod_cast hreal

private lemma asymptotic_far_params :
    ∀ᶠ N : ℕ in atTop,
      let S := ⌊(1 : ℝ) * (N : ℝ) / ((Real.log (N : ℝ)) ^ 3 * (Real.log (Real.log (N : ℝ))) ^ 4)⌋₊
      let P := ⌈4 * Real.log (N : ℝ)⌉₊
      let K := N / (16 * P)
      let U := ⌊(Real.log (N : ℝ)) ^ 2 * (Real.log (Real.log (N : ℝ))) ^ 3⌋₊
      let t := ⌈10800 * (N : ℝ) ^ 2 * Real.log (N : ℝ) / (K : ℝ) ^ 2⌉₊
      let M_bad := ⌊(P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ))⌋₊
      4 ≤ N ∧ 10 ^ 22 ≤ S ∧ S ≤ N ∧
      4 * Real.log (N : ℝ) ≤ (P : ℝ) ∧ 10 ^ 10 ≤ P ∧ 4 * P ≤ S ∧
      0 < K ∧ K < Nat.lcmUpto S ∧ U ≤ S ∧
      10800 * (N : ℝ) ^ 2 * Real.log (N : ℝ) / (K : ℝ) ^ 2 ≤ (t : ℝ) ∧
      (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2 ∧
      5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1) ∧
      10 ^ 11 * S * U ≤ K + 1 ∧
      4 * 10 ^ 12 * N ≤ S * S := by
  have hL_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL_top : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp hL_top
  filter_upwards [eventually_ge_atTop (10 ^ 10), hL_top.eventually_ge_atTop (10 ^ 16),
    hLL_top.eventually_ge_atTop (10 ^ 15)] with N hN_ge hL_ge hLL_ge
  set L := Real.log (N : ℝ)
  set LL := Real.log L
  set D := L ^ 3 * LL ^ 4
  set S := ⌊(1 : ℝ) * (N : ℝ) / D⌋₊
  set P := ⌈4 * L⌉₊
  set K := N / (16 * P)
  set U := ⌊L ^ 2 * LL ^ 3⌋₊
  set t := ⌈10800 * (N : ℝ) ^ 2 * L / (K : ℝ) ^ 2⌉₊
  set M_bad := ⌊(P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ))⌋₊
  set E := Real.exp (L / 4)
  have hN_pos : (0 : ℝ) < N := by positivity
  have hL_pos : 0 < L := by linarith
  have hLL_pos : 0 < LL := by linarith
  have hD_pos : 0 < D := by positivity
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_ge : (10 ^ 15 : ℝ) ≤ E := by
    have h1 := Real.add_one_le_exp (L / 4)
    dsimp [E]; linarith
  have hE4 : E ^ 4 = (N : ℝ) := by
    dsimp [E]; rw [← Real.exp_nat_mul]
    have heq : (4 : ℕ) * (L / 4) = L := by push_cast; ring
    rw [heq]; exact Real.exp_log hN_pos
  have hLL_le_L : LL ≤ L := by linarith [Real.log_le_sub_one_of_pos hL_pos]
  have hD_le_L7 : D ≤ L ^ 7 := by
    have h1 : LL ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hLL_pos.le hLL_le_L 4
    dsimp [D]; nlinarith only [h1, pow_nonneg hL_pos.le 3]
  have hL7_le_E : L ^ 7 ≤ E := pow_seven_le_exp_quarter hL_ge
  have hD_le_E : D ≤ E := hD_le_L7.trans hL7_le_E
  have hE3_le_ND : E ^ 3 ≤ (N : ℝ) / D := by
    rw [le_div_iff₀ hD_pos, ← hE4]
    have h1 := mul_le_mul_of_nonneg_left hD_le_E (pow_nonneg hE_pos.le 3)
    linarith [show E ^ 3 * E = E ^ 4 by ring]
  have hE3_big : (10 ^ 45 : ℝ) ≤ E ^ 3 := by
    have h1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10 ^ 15) hE_ge 3
    linarith [show ((10 ^ 15 : ℝ) ^ 3) = (10 ^ 45 : ℝ) by norm_num]
  have hS_eq : S = ⌊(N : ℝ) / D⌋₊ := by dsimp [S]; rw [one_mul]
  have hS_real_lo : (N : ℝ) / D - 1 < (S : ℝ) := by
    rw [hS_eq]; linarith [Nat.lt_floor_add_one ((N : ℝ) / D)]
  have hS_real_hi : (S : ℝ) ≤ (N : ℝ) / D := by
    rw [hS_eq]; exact Nat.floor_le (by positivity)
  have hS_ge_E3half : E ^ 3 / 2 ≤ (S : ℝ) := by linarith
  have hS_big : 10 ^ 22 ≤ S := by
    have : (10 ^ 22 : ℝ) ≤ (S : ℝ) := by linarith
    exact_mod_cast this
  have hSN : S ≤ N := by
    have hD1 : 1 ≤ D := by
      have h1 : 1 ≤ L ^ 3 := one_le_pow₀ (by linarith)
      have h2 : 1 ≤ LL ^ 4 := one_le_pow₀ (by linarith)
      dsimp [D]; nlinarith only [h1, h2]
    exact_mod_cast hS_real_hi.trans (div_le_self hN_pos.le hD1)
  have hP_ge : 4 * L ≤ (P : ℝ) := Nat.le_ceil (4 * L)
  have hP_le : (P : ℝ) ≤ 5 * L := by
    have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * L)
    linarith
  have hP_big : 10 ^ 10 ≤ P := by
    have : (10 ^ 10 : ℝ) ≤ (P : ℝ) := by linarith
    exact_mod_cast this
  have hL_le_E : L ≤ E := by
    have h1 : 1 ≤ L ^ 6 := one_le_pow₀ (by linarith)
    nlinarith only [h1, hL_pos, hL7_le_E]
  have hE2_big : (10 ^ 30 : ℝ) ≤ E ^ 2 := by nlinarith only [hE_ge]
  have hE_le_E3 : 10 ^ 30 * E ≤ E ^ 3 := by
    have ha : E ^ 3 = E * E ^ 2 := by ring
    rw [ha]; nlinarith only [hE2_big, hE_pos]
  have h4P_S : 4 * P ≤ S := by
    have h1 : ((4 * P : ℕ) : ℝ) ≤ (S : ℝ) := by push_cast; linarith
    exact_mod_cast h1
  have hK_real_lo : (N : ℝ) / (100 * L) ≤ (K : ℝ) := by
    have h1 : (N : ℝ) / (16 * (P : ℝ)) - 1 < (K : ℝ) := by
      have hnat : N < 16 * P * (K + 1) := Nat.lt_mul_div_succ N (by positivity)
      have hreal : (N : ℝ) < 16 * (P : ℝ) * ((K : ℝ) + 1) := by exact_mod_cast hnat
      rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]
      linarith
    have h2 : (N : ℝ) / (80 * L) ≤ (N : ℝ) / (16 * (P : ℝ)) :=
      div_le_div_of_nonneg_left hN_pos.le (by positivity) (by linarith)
    have h3 : (N : ℝ) / (80 * L) - (N : ℝ) / (100 * L) = (N : ℝ) / (400 * L) := by
      field_simp [hL_pos.ne']; ring
    have h4 : 1 ≤ (N : ℝ) / (400 * L) := by
      rw [one_le_div (by positivity), ← hE4]
      have ha : E ^ 4 = E * E ^ 3 := by ring
      rw [ha]; nlinarith only [hL_le_E, hE3_big, hE_pos]
    linarith
  have hK_pos : 0 < K := by
    have h1 : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le (by positivity) hK_real_lo
    exact_mod_cast h1
  have hK_lt_Q : K < Nat.lcmUpto S := by
    have hQ_pos : (0 : ℝ) < (Nat.lcmUpto S : ℝ) := by exact_mod_cast Nat.lcmUpto_pos S
    have hpsi := Chebyshev.psi_ge S
    rw [Chebyshev.psi_eq_log_lcmUpto S] at hpsi
    have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hlogS1 : Real.log ((S : ℝ) + 1) ≤ (S : ℝ) / 10 := by
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((S : ℝ) + 1) / 20 by positivity)
      have h2 : Real.log (((S : ℝ) + 1) / 20) = Real.log ((S : ℝ) + 1) - Real.log 20 :=
        Real.log_div (by positivity) (by norm_num)
      have h3 : Real.log 20 ≤ 20 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)]
      linarith
    have hL_le_S : L ≤ (S : ℝ) / 4 := by
      have h1 : ((4 * P : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast h4P_S
      push_cast at h1; linarith
    have hS_pos : (0 : ℝ) < S := by positivity
    have hL_lt_logQ : L < Real.log (Nat.lcmUpto S : ℝ) := by
      nlinarith only [hpsi, hlog2, hlogS1, hL_le_S, hS_pos]
    have hN_lt_Q : (N : ℝ) < (Nat.lcmUpto S : ℝ) := by
      rw [← Real.exp_log hN_pos, ← Real.exp_log hQ_pos]
      exact Real.exp_lt_exp.mpr hL_lt_logQ
    have hN_lt_Q_nat : N < Nat.lcmUpto S := by exact_mod_cast hN_lt_Q
    have hK_le_N : K ≤ N := Nat.div_le_self N (16 * P)
    omega
  have hU_hi : (U : ℝ) ≤ L ^ 2 * LL ^ 3 := Nat.floor_le (by positivity)
  have hU_lo : L ^ 2 * LL ^ 3 / 2 ≤ (U : ℝ) := by
    have h1 := Nat.lt_floor_add_one (L ^ 2 * LL ^ 3)
    have ha : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ (by linarith)
    have hb2 : (1 : ℝ) ≤ LL ^ 2 := one_le_pow₀ (by linarith)
    have hb : (2 : ℝ) ≤ LL ^ 3 := by nlinarith only [hb2, hLL_ge]
    have h2 : 2 ≤ L ^ 2 * LL ^ 3 := by nlinarith only [ha, hb]
    linarith
  have hU_big : 10 ^ 10 ≤ U := by
    have ha : (10 ^ 20 : ℝ) ≤ L ^ 2 := by nlinarith only [hL_ge]
    have hb : (1 : ℝ) ≤ LL ^ 3 := one_le_pow₀ (by linarith)
    have h1 : (10 ^ 10 : ℝ) ≤ (U : ℝ) := by nlinarith only [ha, hb, hU_lo]
    exact_mod_cast h1
  have hU_S : U ≤ S := by
    have ha : LL ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hLL_pos.le hLL_le_L 3
    have hb : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ (by linarith)
    have h1 : L ^ 2 * LL ^ 3 ≤ L ^ 7 := by
      calc L ^ 2 * LL ^ 3 ≤ L ^ 2 * L ^ 3 := mul_le_mul_of_nonneg_left ha (by positivity)
        _ = L ^ 5 := by ring
        _ ≤ L ^ 5 * L ^ 2 := le_mul_of_one_le_right (by positivity) hb
        _ = L ^ 7 := by ring
    have h2 : (U : ℝ) ≤ (S : ℝ) := by linarith
    exact_mod_cast h2
  have ht_ge : 10800 * (N : ℝ) ^ 2 * L / (K : ℝ) ^ 2 ≤ (t : ℝ) := Nat.le_ceil _
  have hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2 := by
    have hlog4P_pos : 0 < Real.log ((4 * P : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < 4 * P by omega))
    have hM_hi : (M_bad : ℝ) ≤ (P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ)) :=
      Nat.floor_le (by positivity)
    have h1 : 2 * (M_bad : ℝ) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 4 := by
      have ha := mul_le_mul_of_nonneg_right hM_hi (by positivity : 0 ≤ 2 * Real.log ((4 * P : ℕ) : ℝ))
      have heq : (P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ)) * (2 * Real.log ((4 * P : ℕ) : ℝ)) =
          (P : ℝ) / 4 := by field_simp [hlog4P_pos.ne']; ring
      linarith
    linarith [eight_log_four_le_quarter hP_big]
  have havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1) :=
    params_avg_bound hN_pos hL_ge hLL_ge rfl hP_ge hP_le hP_big hK_real_lo hU_hi hU_lo hU_big rfl rfl
  have hSU_L0 : 10 ^ 11 * S * U ≤ K + 1 := by
    have hSU_le : (S : ℝ) * (U : ℝ) ≤ (N : ℝ) / (L * LL) := by
      have hmul := mul_le_mul hS_real_hi hU_hi (by positivity) (by positivity)
      have heq : (N : ℝ) / D * (L ^ 2 * LL ^ 3) = (N : ℝ) / (L * LL) := by
        dsimp [D]; field_simp [hL_pos.ne', hLL_pos.ne']
      linarith
    have h1 : 10 ^ 11 * ((N : ℝ) / (L * LL)) ≤ (N : ℝ) / (100 * L) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : (10 ^ 11 * 100 : ℝ) ≤ LL := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (N : ℝ) * L)
      linarith [show (N : ℝ) * L * (10 ^ 11 * 100) = 10 ^ 11 * (N : ℝ) * (100 * L) by ring,
        show (N : ℝ) * L * LL = (N : ℝ) * (L * LL) by ring]
    have hreal : ((10 ^ 11 * S * U : ℕ) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast hreal
  have hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S := by
    have hsq : E ^ 6 / 4 ≤ (S : ℝ) * (S : ℝ) := by
      have h1 : (E ^ 3 / 2) ^ 2 ≤ (S : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hS_ge_E3half 2
      have heq : (E ^ 3 / 2) ^ 2 = E ^ 6 / 4 := by ring
      have heq2 : (S : ℝ) ^ 2 = (S : ℝ) * (S : ℝ) := sq _
      linarith
    have hreal : ((4 * 10 ^ 12 * N : ℕ) : ℝ) ≤ ((S * S : ℕ) : ℝ) := by
      push_cast; rw [← hE4]
      have ha : E ^ 6 = E ^ 4 * E ^ 2 := by ring
      have h1 : 16 * 10 ^ 12 * E ^ 4 ≤ E ^ 6 := by
        rw [ha]; nlinarith only [hE2_big, pow_pos hE_pos 4]
      linarith
    exact_mod_cast hreal
  exact ⟨by omega, hS_big, hSN, hP_ge, hP_big, h4P_S, hK_pos, hK_lt_Q, hU_S, ht_ge, hM_le,
    havg, hSU_L0, hCaseB_S⟩

end Asymptotics

end Erdos294StepH2

theorem OMA.solution : OMA.R_Erdos294_erdos_294_R1_H1_R1_H2_R1.H2 := by
  refine ⟨1, zero_lt_one, ?_⟩
  filter_upwards [Erdos294StepH2.asymptotic_far_params] with N hN
  obtain ⟨hN4, hS_big, hSN, hP_ge, hP_big, h4P_S, hK_pos, hK_lt_Q, hU_S, ht_ge, hM_le,
    havg, hSU_L0, hCaseB_S⟩ := hN
  exact Erdos294StepH2.far_sum_lt_half hN4 hS_big hSN hP_ge hP_big h4P_S rfl hK_pos hK_lt_Q
    hU_S ht_ge hM_le havg hSU_L0 hCaseB_S
