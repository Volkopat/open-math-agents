import FormalConjectures.ErdosProblems.«955»

/-!
Troupe's upper-tail theorem for the number of distinct prime factors of the aliquot sum.

This file combines the reduction in PR 6384, the upper-tail proof by @mattdorman
in PR 18395, and the composite-divisor proof by @caa1982 in PR 7364.
The reduction and the two proofs are included so the file requires only the
pinned Formal Conjectures module.
-/

/-! Reduction of Troupe's upper-tail statement for the number of prime factors of s(n) to the
same statement normalised by log log n instead of log log s(n), together with the elementary
bound s(n) ^ 2 >= n for composite n. A prime n has s(n) = 1 and is never in the exceptional
set; for composite n the bound gives log log s(n) >= log log n - log 2, which is absorbed by
halving epsilon once n is large. -/

namespace OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1

open Filter Topology

/-- Troupe (J. Number Theory 2015), upper half of the normal-order theorem for the number of
distinct prime factors of s(n), with the normalisation log log n. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    {n : ℕ | (1 + ε) * Real.log (Real.log (n : ℝ)) <
      (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)}.HasDensity 0

/-- A composite n has a proper divisor at least sqrt n, so s(n) ^ 2 >= n. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ¬ n.Prime → n ≤ Erdos955.s n ^ 2

lemma s_prime {p : ℕ} (hp : p.Prime) : Erdos955.s p = 1 := by
  have h : ArithmeticFunction.sigma 1 p = p + 1 := by
    rw [ArithmeticFunction.sigma_one_apply, hp.sum_divisors]
  unfold Erdos955.s
  omega

theorem main : H1 → H2 →
    type_of% @Erdos955.erdos_955.variants.troupe_unusually_many_prime_factors := by
  intro h1 h2 ε hε
  have hS := h1 (ε / 2) (by positivity)
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    (hll.eventually_ge_atTop ((1 + ε) * Real.log 2 * (2 / ε)))
  have hsub : {x : ℕ | (1 + ε) * Real.log (Real.log (Erdos955.s x)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s x) : ℝ)} ⊆
      {n : ℕ | (1 + ε / 2) * Real.log (Real.log (n : ℝ)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ∪ Set.Iio (max N0 2) := by
    intro n hn
    by_cases hlt : n < max N0 2
    · exact Or.inr hlt
    · left
      have hn1 : max N0 2 ≤ n := not_lt.mp hlt
      have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn1
      have hnN0 : N0 ≤ n := le_trans (le_max_left _ _) hn1
      have hnp : ¬ n.Prime := by
        intro hp
        have hs1 : Erdos955.s n = 1 := s_prime hp
        rw [Set.mem_ofPred_eq, hs1] at hn
        simp at hn
      have hsq := h2 n hn2 hnp
      have hLL := hN0 n hnN0
      have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hnpos : (0 : ℝ) < n := by linarith
      have hLpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
      have hsqR : (n : ℝ) ≤ (Erdos955.s n : ℝ) ^ 2 := by exact_mod_cast hsq
      have hlog1 : Real.log (n : ℝ) ≤ 2 * Real.log (Erdos955.s n : ℝ) := by
        have h := Real.log_le_log hnpos hsqR
        rw [Real.log_pow] at h
        push_cast at h
        exact h
      have hhalf : 0 < Real.log (n : ℝ) / 2 := by positivity
      have hlog2 : Real.log (Real.log (n : ℝ)) - Real.log 2 ≤
          Real.log (Real.log (Erdos955.s n : ℝ)) := by
        rw [← Real.log_div hLpos.ne' (by norm_num)]
        exact Real.log_le_log hhalf (by linarith)
      have hkey : (1 + ε) * Real.log 2 ≤ ε / 2 * Real.log (Real.log (n : ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hLL (by positivity : (0 : ℝ) ≤ ε / 2)
        have he : ε / 2 * ((1 + ε) * Real.log 2 * (2 / ε)) = (1 + ε) * Real.log 2 := by
          field_simp
        linarith
      rw [Set.mem_ofPred_eq] at hn ⊢
      have hmul : (1 + ε) * (Real.log (Real.log (n : ℝ)) - Real.log 2) ≤
          (1 + ε) * Real.log (Real.log (Erdos955.s n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog2 (by positivity)
      nlinarith
  rw [Set.HasDensity] at hS ⊢
  have hN : Tendsto (fun b : ℕ => ((max N0 2 : ℕ) : ℝ) / (b : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hsum := hS.add hN
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun b => ?_)
    (fun b => ?_)
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hfin : (({n : ℕ | (1 + ε / 2) * Real.log (Real.log (n : ℝ)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ∩ Set.Iio b) ∪
        Set.Iio (max N0 2)).Finite :=
      ((Set.finite_Iio b).inter_of_right _).union (Set.finite_Iio _)
    have hle1 := Set.ncard_le_ncard (s := {x : ℕ | (1 + ε) * Real.log (Real.log (Erdos955.s x)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s x) : ℝ)} ∩ Set.Iio b)
      (fun x hx => by
        rcases hsub hx.1 with h | h
        · exact Or.inl ⟨h, hx.2⟩
        · exact Or.inr h) hfin
    have hle2 := Set.ncard_union_le ({n : ℕ | (1 + ε / 2) * Real.log (Real.log (n : ℝ)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ∩ Set.Iio b)
      (Set.Iio (max N0 2))
    have hle3 : (Set.Iio (max N0 2)).ncard = max N0 2 := Nat.ncard_Iio _
    have hle4 := hle1.trans hle2
    rw [hle3] at hle4
    exact_mod_cast hle4

end OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1

/-!
# Upper Tail for Prime Factors of the Sum-of-Proper-Divisors Function

Self-contained elementary proof that for every `ε > 0`, the set of natural numbers `n` satisfying
`(1 + ε) * log (log n) < ω(s(n))` has asymptotic density zero.
-/

open Filter Topology Finset
open scoped ArithmeticFunction ArithmeticFunction.sigma Classical

namespace Erdos955TroupeH1

/- ## Section 1: Elementary Real, Harmonic, and Prime Sum Bounds -/

private lemma log_two_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  have h1 : (2 : ℝ) > Real.exp (1 / 2) := by
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have he : Real.exp 1 < 4 := by
      have := Real.exp_one_lt_d9
      linarith
    nlinarith [Real.exp_pos (1 / 2)]
  calc (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp _).symm
    _ < Real.log 2 := Real.log_lt_log (Real.exp_pos _) h1

private lemma log_four_lt_two : Real.log 4 < 2 := by
  have h1 : (4 : ℝ) < Real.exp 2 := by
    have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hsq : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith
  calc Real.log 4 < Real.log (Real.exp 2) := Real.log_lt_log (by norm_num) h1
    _ = 2 := Real.log_exp 2

private lemma log_log_two_gt_neg_one : (-1 : ℝ) < Real.log (Real.log 2) := by
  have h1 : Real.exp (-1) < Real.log 2 := by
    have h2 : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg]
      have he : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      rw [inv_eq_one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) he
    linarith [log_two_gt_half]
  calc (-1 : ℝ) = Real.log (Real.exp (-1)) := (Real.log_exp _).symm
    _ < Real.log (Real.log 2) := Real.log_lt_log (Real.exp_pos _) h1

private lemma log_le_self_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  linarith [Real.log_le_sub_one_of_pos hx]

private lemma sum_Icc_inv_eq_harmonic (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]

private lemma sum_Icc_inv_le_one_add_log (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log N := by
  rw [sum_Icc_inv_eq_harmonic]
  exact harmonic_le_one_add_log N

private lemma sum_Ioc_inv_sq_le (A B : ℕ) (hA : 1 ≤ A) :
    ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / ((m : ℝ) ^ 2) ≤ 1 / (A : ℝ) := by
  by_cases hAB : B ≤ A
  · simp [Finset.Ioc_eq_empty (not_lt.mpr hAB)]
  push Not at hAB
  have hterm : ∀ m ∈ Finset.Ioc A B,
      (1 : ℝ) / ((m : ℝ) ^ 2) ≤ 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm2 : 2 ≤ m := by omega
    have hm_pos : (0 : ℝ) < m := by positivity
    have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
      have : 1 ≤ m - 1 := by omega
      positivity
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast, div_sub_div _ _ (by linarith) hm_pos.ne']
    rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith
  calc ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / ((m : ℝ) ^ 2)
      ≤ ∑ m ∈ Finset.Ioc A B, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 1 / (A : ℝ) - 1 / (B : ℝ) := by
        have hstep : ∀ k : ℕ, A ≤ k →
            ∑ m ∈ Finset.Ioc A k, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) =
              1 / (A : ℝ) - 1 / (k : ℝ) := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => simp
          | succ n hn ih =>
            rw [Finset.sum_Ioc_succ_top hn, ih]
            simp only [Nat.add_sub_cancel]
            ring
        exact hstep B hAB.le
    _ ≤ 1 / (A : ℝ) := by
        have : (0 : ℝ) ≤ 1 / (B : ℝ) := by positivity
        linarith

private lemma sum_Ioc_inv_rpow_three_halves_le (A B : ℕ) (hA : 1 ≤ A) :
    ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / ((m : ℝ) * Real.sqrt m) ≤ 2 / Real.sqrt A := by
  by_cases hAB : B ≤ A
  · simp [Finset.Ioc_eq_empty (not_lt.mpr hAB)]
    positivity
  push Not at hAB
  have hterm : ∀ m ∈ Finset.Ioc A B,
      (1 : ℝ) / ((m : ℝ) * Real.sqrt m) ≤
        2 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 2 / Real.sqrt (m : ℝ) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm2 : 2 ≤ m := by omega
    have hm_pos : (0 : ℝ) < m := by positivity
    have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
      have : 1 ≤ m - 1 := by omega
      positivity
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
    have hsm1 : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hm1_pos
    have hdiff : (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) *
        (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ)) = 1 := by
      nlinarith [Real.sq_sqrt hm_pos.le, Real.sq_sqrt hm1_pos.le, hcast]
    have hle : Real.sqrt ((m - 1 : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) :=
      Real.sqrt_le_sqrt (by linarith)
    rw [div_sub_div _ _ hsm1.ne' hsm.ne']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 2 * Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ) * 2 =
        2 * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) := by ring
    rw [h1]
    have h2 : Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
      calc Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ)
          ≤ Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) := by nlinarith
        _ = (m : ℝ) := Real.mul_self_sqrt hm_pos.le
    have h3 : 1 ≤ 2 * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) * Real.sqrt (m : ℝ) := by
      nlinarith
    nlinarith
  calc ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / ((m : ℝ) * Real.sqrt m)
      ≤ ∑ m ∈ Finset.Ioc A B,
          (2 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 2 / Real.sqrt (m : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 2 / Real.sqrt A - 2 / Real.sqrt B := by
        have hstep : ∀ k : ℕ, A ≤ k →
            ∑ m ∈ Finset.Ioc A k,
                (2 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 2 / Real.sqrt (m : ℝ)) =
              2 / Real.sqrt A - 2 / Real.sqrt k := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => simp
          | succ n hn ih =>
            rw [Finset.sum_Ioc_succ_top hn, ih]
            simp only [Nat.add_sub_cancel]
            ring
        exact hstep B hAB.le
    _ ≤ 2 / Real.sqrt A := by
        have : (0 : ℝ) ≤ 2 / Real.sqrt B := by positivity
        linarith

private lemma sum_Ioc_log_div_sq_le (A B : ℕ) (hA : 1 ≤ A) :
    ∑ m ∈ Finset.Ioc A B, Real.log m / ((m : ℝ) ^ 2) ≤ 4 / Real.sqrt A := by
  have hle : ∀ m ∈ Finset.Ioc A B,
      Real.log m / ((m : ℝ) ^ 2) ≤ 2 * ((1 : ℝ) / ((m : ℝ) * Real.sqrt m)) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm1 : 1 ≤ m := by omega
    have hm_pos : (0 : ℝ) < m := by positivity
    have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
    have hlog : Real.log (m : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
      have h1 : Real.log (Real.sqrt (m : ℝ)) ≤ Real.sqrt (m : ℝ) := log_le_self_of_pos hsm
      rw [Real.log_sqrt hm_pos.le] at h1
      linarith
    have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt hm_pos.le
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hmul : Real.log (m : ℝ) * ((m : ℝ) * Real.sqrt (m : ℝ)) ≤
        (2 * Real.sqrt (m : ℝ)) * ((m : ℝ) * Real.sqrt (m : ℝ)) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    have hrhs : (2 * Real.sqrt (m : ℝ)) * ((m : ℝ) * Real.sqrt (m : ℝ)) = 2 * (m : ℝ) ^ 2 := by
      nlinarith [hsq]
    linarith
  calc ∑ m ∈ Finset.Ioc A B, Real.log m / ((m : ℝ) ^ 2)
      ≤ ∑ m ∈ Finset.Ioc A B, 2 * ((1 : ℝ) / ((m : ℝ) * Real.sqrt m)) :=
        Finset.sum_le_sum hle
    _ = 2 * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / ((m : ℝ) * Real.sqrt m) := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * (2 / Real.sqrt A) := by
        gcongr
        exact sum_Ioc_inv_rpow_three_halves_le A B hA
    _ = 4 / Real.sqrt A := by ring

private lemma sum_Icc_inv_mul_log_le (N : ℕ) (hN : 3 ≤ N) :
    ∑ m ∈ Finset.Icc 3 N, (1 : ℝ) / ((m : ℝ) * Real.log m) ≤
      Real.log (Real.log N) + 1 := by
  have hterm : ∀ m ∈ Finset.Icc 3 N,
      (1 : ℝ) / ((m : ℝ) * Real.log m) ≤
        Real.log (Real.log (m : ℝ)) - Real.log (Real.log ((m - 1 : ℕ) : ℝ)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm3 : 3 ≤ m := hm.1
    have hm_pos : (0 : ℝ) < m := by positivity
    have hm1_ge2 : (2 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
      have : 2 ≤ m - 1 := by omega
      exact_mod_cast this
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have ha_pos : 0 < Real.log ((m - 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hb_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by
      have : (3 : ℝ) ≤ m := by exact_mod_cast hm3
      linarith)
    have h1 : (1 : ℝ) / (m : ℝ) ≤ Real.log (m : ℝ) - Real.log ((m - 1 : ℕ) : ℝ) := by
      have hdiv : ((m - 1 : ℕ) : ℝ) / (m : ℝ) = 1 - 1 / (m : ℝ) := by
        rw [hcast]; field_simp
      have hle := Real.log_le_sub_one_of_pos (show 0 < ((m - 1 : ℕ) : ℝ) / (m : ℝ) by positivity)
      rw [Real.log_div (by positivity) hm_pos.ne', hdiv] at hle
      linarith
    have h2 : (Real.log (m : ℝ) - Real.log ((m - 1 : ℕ) : ℝ)) / Real.log (m : ℝ) ≤
        Real.log (Real.log (m : ℝ)) - Real.log (Real.log ((m - 1 : ℕ) : ℝ)) := by
      have hle := Real.log_le_sub_one_of_pos
        (show 0 < Real.log ((m - 1 : ℕ) : ℝ) / Real.log (m : ℝ) by positivity)
      rw [Real.log_div ha_pos.ne' hb_pos.ne'] at hle
      have : 1 - Real.log ((m - 1 : ℕ) : ℝ) / Real.log (m : ℝ) =
          (Real.log (m : ℝ) - Real.log ((m - 1 : ℕ) : ℝ)) / Real.log (m : ℝ) := by
        field_simp
      linarith
    have h3 : (1 : ℝ) / ((m : ℝ) * Real.log m) ≤
        (Real.log (m : ℝ) - Real.log ((m - 1 : ℕ) : ℝ)) / Real.log (m : ℝ) := by
      rw [show (1 : ℝ) / ((m : ℝ) * Real.log m) = (1 / (m : ℝ)) / Real.log m by ring]
      exact div_le_div_of_nonneg_right h1 hb_pos.le
    exact h3.trans h2
  calc ∑ m ∈ Finset.Icc 3 N, (1 : ℝ) / ((m : ℝ) * Real.log m)
      ≤ ∑ m ∈ Finset.Icc 3 N,
          (Real.log (Real.log (m : ℝ)) - Real.log (Real.log ((m - 1 : ℕ) : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = Real.log (Real.log (N : ℝ)) - Real.log (Real.log (2 : ℝ)) := by
        have hstep : ∀ k : ℕ, 2 ≤ k →
            ∑ m ∈ Finset.Ioc 2 k,
                (Real.log (Real.log (m : ℝ)) - Real.log (Real.log ((m - 1 : ℕ) : ℝ))) =
              Real.log (Real.log (k : ℝ)) - Real.log (Real.log (2 : ℝ)) := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => simp
          | succ n hn ih =>
            rw [Finset.sum_Ioc_succ_top hn, ih]
            simp only [Nat.add_sub_cancel]
            ring
        have hIcc : Finset.Icc 3 N = Finset.Ioc 2 N := rfl
        rw [hIcc]
        exact hstep N (by omega)
    _ ≤ Real.log (Real.log N) + 1 := by
        linarith [log_log_two_gt_neg_one]

/-- Summation by parts on `Icc a b` for `1 ≤ a ≤ b`. -/
private lemma sum_by_parts_Icc (S f : ℕ → ℝ) (a b : ℕ) (_ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ m ∈ Finset.Icc a b, (S m - S (m - 1)) * f m =
      S b * f b - S (a - 1) * f a +
        ∑ m ∈ Finset.Ico a b, S m * (f m - f (m + 1)) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp [Finset.Icc_self]
    ring
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hn, ih]
    simp only [Nat.add_sub_cancel]
    ring

/-- Mertens first theorem (upper bound) with leading constant 1. -/
private lemma sum_log_div_prime_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ) ≤ Real.log N + Real.log 4 := by
  have hN_pos : (0 : ℝ) < N := by positivity
  have hfact_le : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by
    exact_mod_cast Nat.factorial_le_pow N
  have hlog_fact_le : Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
    calc Real.log (N.factorial : ℝ) ≤ Real.log ((N : ℝ) ^ N) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) hfact_le
      _ = (N : ℝ) * Real.log N := Real.log_pow (N : ℝ) N
  have hdiv_le : ∀ p ∈ Nat.primesLE N, N / p ≤ N.factorial.factorization p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hle : p ≤ N := Nat.le_of_mem_primesLE hp
    rw [Nat.factorization_factorial hpp (Nat.lt_add_one (Nat.log p N))]
    have h1mem : 1 ∈ Finset.Ico 1 (Nat.log p N + 1) := by
      rw [Finset.mem_Ico]
      refine ⟨le_rfl, Nat.lt_add_one_iff.mpr ?_⟩
      exact Nat.le_log_of_pow_le hpp.one_lt (by simpa using hle)
    calc N / p = N / p ^ 1 := by simp
      _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p N + 1), N / p ^ i :=
          Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1mem
  have hprod_dvd : (∏ p ∈ Nat.primesLE N, p ^ (N / p)) ∣ N.factorial := by
    rw [← Nat.factorization_le_iff_dvd (by
      exact Finset.prod_ne_zero_iff.mpr fun p hp =>
        pow_ne_zero _ (Nat.prime_of_mem_primesLE hp).ne_zero) (Nat.factorial_ne_zero N)]
    intro q
    rw [Nat.factorization_prod (fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primesLE hp).ne_zero)]
    simp only [Finsupp.finsetSum_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hq : q ∈ Nat.primesLE N
    · rw [Finset.sum_eq_single q]
      · rw [(Nat.prime_of_mem_primesLE hq).factorization_self, mul_one]
        exact hdiv_le q hq
      · intro p hp hpq
        rw [(Nat.prime_of_mem_primesLE hp).factorization,
          Finsupp.single_eq_of_ne (Ne.symm hpq), mul_zero]
      · intro h; exact absurd hq h
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro p hp
        have hpq : p ≠ q := fun h => hq (h ▸ hp)
        rw [(Nat.prime_of_mem_primesLE hp).factorization,
          Finsupp.single_eq_of_ne (Ne.symm hpq), mul_zero]
  have hprod_le : (∏ p ∈ Nat.primesLE N, (p : ℝ) ^ (N / p)) ≤ (N.factorial : ℝ) := by
    have hnat : ∏ p ∈ Nat.primesLE N, p ^ (N / p) ≤ N.factorial :=
      Nat.le_of_dvd (Nat.factorial_pos N) hprod_dvd
    exact_mod_cast hnat
  have hsum_le : ∑ p ∈ Nat.primesLE N, ((N / p : ℕ) : ℝ) * Real.log p ≤ (N : ℝ) * Real.log N := by
    have hlog_prod : ∑ p ∈ Nat.primesLE N, ((N / p : ℕ) : ℝ) * Real.log p =
        Real.log (∏ p ∈ Nat.primesLE N, (p : ℝ) ^ (N / p)) := by
      rw [Real.log_prod (fun p hp =>
        pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero))]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Real.log_pow]
    rw [hlog_prod]
    exact (Real.log_le_log (Finset.prod_pos fun p hp =>
      pow_pos (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos) _) hprod_le).trans
      hlog_fact_le
  have hfloor : ∀ p ∈ Nat.primesLE N,
      ((N : ℝ) / (p : ℝ) - 1) * Real.log p ≤ ((N / p : ℕ) : ℝ) * Real.log p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    have hnat : N < (N / p + 1) * p := by
      have := Nat.lt_div_mul_add hpp.pos (a := N)
      linarith
    have hreal : (N : ℝ) / (p : ℝ) - 1 ≤ ((N / p : ℕ) : ℝ) := by
      have hnatR : (N : ℝ) < (((N / p : ℕ) : ℝ) + 1) * (p : ℝ) := by exact_mod_cast hnat
      rw [sub_le_iff_le_add, div_le_iff₀ hp_pos]
      linarith
    exact mul_le_mul_of_nonneg_right hreal hlog_nn
  have hstep : (N : ℝ) * (∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ)) -
      ∑ p ∈ Nat.primesLE N, Real.log p ≤ (N : ℝ) * Real.log N := by
    calc (N : ℝ) * (∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ)) -
            ∑ p ∈ Nat.primesLE N, Real.log p
        = ∑ p ∈ Nat.primesLE N, ((N : ℝ) / (p : ℝ) - 1) * Real.log p := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ ∑ p ∈ Nat.primesLE N, ((N / p : ℕ) : ℝ) * Real.log p :=
          Finset.sum_le_sum hfloor
      _ ≤ (N : ℝ) * Real.log N := hsum_le
  have htheta : ∑ p ∈ Nat.primesLE N, Real.log p ≤ Real.log 4 * (N : ℝ) := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)
  have hcomb : (N : ℝ) * (∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ)) ≤
      (N : ℝ) * (Real.log N + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left hcomb hN_pos

/-- Mertens second theorem (upper bound) with leading constant 1. -/
private lemma sum_inv_prime_le (N : ℕ) (hN : 3 ≤ N) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / (p : ℝ) ≤ Real.log (Real.log N) + 10 := by
  let S : ℕ → ℝ := fun m => ∑ p ∈ Nat.primesLE m, Real.log p / (p : ℝ)
  let f : ℕ → ℝ := fun m => (Real.log (m : ℝ))⁻¹
  have hS_diff : ∀ m : ℕ, 2 ≤ m →
      S m - S (m - 1) = if m.Prime then Real.log m / (m : ℝ) else 0 := by
    intro m hm
    have hprev : Nat.primesLE m =
        (if m.Prime then {m} else ∅) ∪ Nat.primesLE (m - 1) := by
      ext p
      simp only [Nat.mem_primesLE, Finset.mem_union]
      split_ifs with hmp
      · simp only [Finset.mem_singleton]
        constructor
        · rintro ⟨hple, hp⟩
          by_cases hpm : p = m
          · exact Or.inl hpm
          · exact Or.inr ⟨by omega, hp⟩
        · rintro (rfl | ⟨hple, hp⟩)
          · exact ⟨le_rfl, hmp⟩
          · exact ⟨by omega, hp⟩
      · simp only [Finset.notMem_empty, false_or]
        constructor
        · rintro ⟨hple, hp⟩
          have hpm : p ≠ m := fun h => hmp (h ▸ hp)
          exact ⟨by omega, hp⟩
        · rintro ⟨hple, hp⟩
          exact ⟨by omega, hp⟩
    have hdisj : Disjoint (if m.Prime then ({m} : Finset ℕ) else ∅) (Nat.primesLE (m - 1)) := by
      split_ifs
      · rw [Finset.disjoint_singleton_left, Nat.mem_primesLE]
        intro h; omega
      · exact Finset.disjoint_empty_left _
    change (∑ p ∈ Nat.primesLE m, Real.log p / (p : ℝ)) -
      (∑ p ∈ Nat.primesLE (m - 1), Real.log p / (p : ℝ)) = _
    rw [hprev, Finset.sum_union hdisj, add_sub_cancel_right]
    split_ifs <;> simp
  have hrewrite : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / (p : ℝ) =
      ∑ m ∈ Finset.Icc 2 N, (S m - S (m - 1)) * f m := by
    have h1 : ∑ m ∈ Finset.Icc 2 N, (S m - S (m - 1)) * f m =
        ∑ m ∈ (Finset.Icc 2 N).filter Nat.Prime, (1 : ℝ) / (m : ℝ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_Icc] at hm
      rw [hS_diff m hm.1]
      split_ifs with hmp
      · have hlog_ne : Real.log (m : ℝ) ≠ 0 :=
          (Real.log_pos (by exact_mod_cast hmp.one_lt)).ne'
        simp only [f]
        field_simp [hlog_ne]
      · simp
    rw [h1]
    congr 1
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hple, hp⟩; exact ⟨⟨hp.two_le, hple⟩, hp⟩
    · rintro ⟨⟨_, hple⟩, hp⟩; exact ⟨hple, hp⟩
  rw [hrewrite, sum_by_parts_Icc S f 2 N (by omega) (by omega)]
  have hS1 : S 1 = 0 := by
    simp only [S, Nat.primesLE_eq_filter_Icc_zero]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    have : x = 0 ∨ x = 1 := by omega
    rcases this with rfl | rfl
    · exact absurd hx.2 Nat.not_prime_zero
    · exact absurd hx.2 Nat.not_prime_one
  simp only [Nat.reduceSub, hS1, zero_mul, sub_zero]
  have hSN : S N * f N ≤ 3 := by
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hlog2N : Real.log 2 ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ N))
    have hS_bd : S N ≤ Real.log N + Real.log 4 := sum_log_div_prime_le N (by omega)
    have hdiv : Real.log 4 / Real.log N ≤ 2 := by
      rw [div_le_iff₀ hlogN]
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    simp only [f]
    calc S N * (Real.log N)⁻¹ ≤ (Real.log N + Real.log 4) * (Real.log N)⁻¹ := by
          gcongr
      _ = 1 + Real.log 4 / Real.log N := by field_simp [hlogN.ne']
      _ ≤ 1 + 2 := by linarith
      _ = 3 := by norm_num
  have hsum_bd : ∑ m ∈ Finset.Ico 2 N, S m * (f m - f (m + 1)) ≤
      Real.log (Real.log N) + 7 := by
    have hterm : ∀ m ∈ Finset.Ico 2 N,
        S m * (f m - f (m + 1)) ≤
          Real.log 4 * (f m - f (m + 1)) +
            Real.log m * (f m - f (m + 1)) := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      have hfm : f (m + 1) ≤ f m := by
        simp only [f]
        have hm_pos : (0 : ℝ) < m := by have : 2 ≤ m := hm.1; positivity
        exact inv_anti₀ (Real.log_pos (by exact_mod_cast (by omega : 1 < m)))
          (Real.log_le_log hm_pos (by exact_mod_cast Nat.le_succ m))
      have hS_bd : S m ≤ Real.log m + Real.log 4 := sum_log_div_prime_le m (by omega)
      nlinarith
    have hconst : ∑ m ∈ Finset.Ico 2 N, Real.log 4 * (f m - f (m + 1)) ≤ 2 := by
      rw [← Finset.mul_sum]
      have htel : ∑ m ∈ Finset.Ico 2 N, (f m - f (m + 1)) = f 2 - f N := by
        have hstep : ∀ k : ℕ, 2 ≤ k →
            ∑ m ∈ Finset.Ico 2 k, (f m - f (m + 1)) = f 2 - f k := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => simp
          | succ n hn ih =>
            rw [Finset.sum_Ico_succ_top hn, ih]; ring
        exact hstep N (by omega)
      rw [htel]
      have hfN : 0 ≤ f N := by
        simp only [f]
        exact inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have h2 : Real.log 4 * f 2 = 2 := by
        simp only [f, Nat.cast_ofNat, h4]
        have hlog2_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
        field_simp [hlog2_ne]
      have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      nlinarith
    have hmain : ∑ m ∈ Finset.Ico 2 N, Real.log m * (f m - f (m + 1)) ≤
        Real.log (Real.log N) + 2 := by
      have hsplit : Finset.Ico 2 N = insert 2 (Finset.Icc 3 (N - 1)) := by
        ext m
        simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have hm2 : Real.log (2 : ℕ) * (f 2 - f (2 + 1)) ≤ 1 := by
        simp only [f, Nat.cast_ofNat]
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hlog3 : 0 < Real.log (2 + 1 : ℕ) := Real.log_pos (by norm_num)
        have : Real.log 2 * ((Real.log 2)⁻¹ - (Real.log (2 + 1 : ℕ))⁻¹) =
            1 - Real.log 2 / Real.log (2 + 1 : ℕ) := by field_simp [hlog2.ne']
        rw [this]
        have : 0 ≤ Real.log 2 / Real.log (2 + 1 : ℕ) := by positivity
        linarith
      have hrest : ∑ m ∈ Finset.Icc 3 (N - 1), Real.log m * (f m - f (m + 1)) ≤
          Real.log (Real.log N) + 1 := by
        have hsub : Finset.Icc 3 (N - 1) ⊆ Finset.Icc 3 N :=
          Finset.Icc_subset_Icc_right (Nat.sub_le N 1)
        have hle_m : ∀ m ∈ Finset.Icc 3 (N - 1),
            Real.log m * (f m - f (m + 1)) ≤ (1 : ℝ) / ((m : ℝ) * Real.log m) := by
          intro m hm
          rw [Finset.mem_Icc] at hm
          have hm_pos : (0 : ℝ) < m := by have : 3 ≤ m := hm.1; positivity
          have hlm : 0 < Real.log (m : ℝ) :=
            Real.log_pos (by exact_mod_cast (by omega : 1 < m))
          have hlm1 : 0 < Real.log ((m + 1 : ℕ) : ℝ) :=
            Real.log_pos (by exact_mod_cast (by omega : 1 < m + 1))
          have hlm_le : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
            Real.log_le_log hm_pos (by exact_mod_cast Nat.le_succ m)
          have hdiff : Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
            have h1 := Real.log_le_sub_one_of_pos
              (show 0 < ((m + 1 : ℕ) : ℝ) / (m : ℝ) by positivity)
            rw [Real.log_div (by positivity) hm_pos.ne'] at h1
            have h2 : ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
              push_cast; field_simp; ring
            linarith
          have hrew : Real.log (m : ℝ) * (f m - f (m + 1)) =
              (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) / Real.log ((m + 1 : ℕ) : ℝ) := by
            simp only [f]
            field_simp [hlm.ne', hlm1.ne']
          rw [hrew]
          calc (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) / Real.log ((m + 1 : ℕ) : ℝ)
              ≤ (1 / (m : ℝ)) / Real.log ((m + 1 : ℕ) : ℝ) :=
                div_le_div_of_nonneg_right hdiff hlm1.le
            _ ≤ (1 / (m : ℝ)) / Real.log (m : ℝ) :=
                div_le_div_of_nonneg_left (by positivity) hlm hlm_le
            _ = 1 / ((m : ℝ) * Real.log m) := by ring
        calc ∑ m ∈ Finset.Icc 3 (N - 1), Real.log m * (f m - f (m + 1))
            ≤ ∑ m ∈ Finset.Icc 3 (N - 1), (1 : ℝ) / ((m : ℝ) * Real.log m) :=
              Finset.sum_le_sum hle_m
          _ ≤ ∑ m ∈ Finset.Icc 3 N, (1 : ℝ) / ((m : ℝ) * Real.log m) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => ?_
              rw [Finset.mem_Icc] at hm
              have : 0 < Real.log (m : ℝ) :=
                Real.log_pos (by exact_mod_cast (by omega : 1 < m))
              positivity
          _ ≤ Real.log (Real.log N) + 1 := sum_Icc_inv_mul_log_le N hN
      linarith
    calc ∑ m ∈ Finset.Ico 2 N, S m * (f m - f (m + 1))
        ≤ ∑ m ∈ Finset.Ico 2 N,
            (Real.log 4 * (f m - f (m + 1)) + Real.log m * (f m - f (m + 1))) :=
          Finset.sum_le_sum hterm
      _ = (∑ m ∈ Finset.Ico 2 N, Real.log 4 * (f m - f (m + 1))) +
          (∑ m ∈ Finset.Ico 2 N, Real.log m * (f m - f (m + 1))) :=
          Finset.sum_add_distrib
      _ ≤ 2 + (Real.log (Real.log N) + 2) := by linarith
      _ ≤ Real.log (Real.log N) + 7 := by linarith
  linarith

private lemma sum_inv_prime_sub_one_le (N : ℕ) (hN : 3 ≤ N) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) - 1) ≤ Real.log (Real.log N) + 11 := by
  have hdiff : ∑ p ∈ Nat.primesLE N, ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ)) ≤ 1 := by
    have hsub : Nat.primesLE N ⊆ Finset.Ioc 1 N := by
      intro p hp
      rw [Finset.mem_Ioc]
      exact ⟨(Nat.prime_of_mem_primesLE hp).one_lt, Nat.le_of_mem_primesLE hp⟩
    have hle : ∀ p ∈ Nat.primesLE N,
        (1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ) ≤ 1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ) := by
      intro p hp
      have hp2 := (Nat.prime_of_mem_primesLE hp).two_le
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hnonneg : ∀ m ∈ Finset.Ioc 1 N,
        (0 : ℝ) ≤ 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      have hm2 : 2 ≤ m := hm.1
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast, sub_nonneg]
      exact one_div_le_one_div_of_le (by
        have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
        linarith) (by linarith)
    calc ∑ p ∈ Nat.primesLE N, ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ))
        ≤ ∑ p ∈ Nat.primesLE N, (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) :=
          Finset.sum_le_sum hle
      _ ≤ ∑ m ∈ Finset.Ioc 1 N, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => hnonneg m hm
      _ = 1 / (1 : ℝ) - 1 / (N : ℝ) := by
          have hstep : ∀ k : ℕ, 1 ≤ k →
              ∑ m ∈ Finset.Ioc 1 k, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) =
                1 / (1 : ℝ) - 1 / (k : ℝ) := by
            intro k hk
            induction k, hk using Nat.le_induction with
            | base => simp
            | succ n hn ih =>
              rw [Finset.sum_Ioc_succ_top hn, ih]
              simp only [Nat.add_sub_cancel]
              ring
          exact hstep N (by omega)
      _ ≤ 1 := by
          have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
          linarith
  have hsum : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) - 1) =
      (∑ p ∈ Nat.primesLE N, (1 : ℝ) / (p : ℝ)) +
      (∑ p ∈ Nat.primesLE N, ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  linarith [sum_inv_prime_le N hN]

private lemma primeCounting_le_six_mul_div_log (x : ℝ) (hx : 4 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 6 * x / Real.log x := by
  have hx1 : 1 < x := by linarith
  have hx_pos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hpi := Chebyshev.pi_le_log4_mul_div hx1
  have hlog_sqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx_pos.le
  have hsqrt_le : Real.sqrt x ≤ 2 * x / Real.log x := by
    rw [le_div_iff₀ hlogx]
    have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x :=
      log_le_self_of_pos (Real.sqrt_pos.mpr hx_pos)
    rw [hlog_sqrt] at h1
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx_pos.le
    nlinarith [Real.sqrt_nonneg x]
  rw [hlog_sqrt, div_div_eq_mul_div] at hpi
  have hlog4 : Real.log 4 * x * 2 / Real.log x ≤ 4 * x / Real.log x := by
    apply div_le_div_of_nonneg_right _ hlogx.le
    nlinarith [log_four_lt_two]
  have hsum : 4 * x / Real.log x + 2 * x / Real.log x = 6 * x / Real.log x := by ring
  linarith

private lemma primeCounting_nat_le (n : ℕ) (hn : 4 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ 6 * (n : ℝ) / Real.log n := by
  have h := primeCounting_le_six_mul_div_log (n : ℝ) (by exact_mod_cast hn)
  rwa [Nat.floor_natCast] at h

private lemma sum_inv_prime_sq_tail (A B : ℕ) (hA : 4 ≤ A) :
    ∑ p ∈ (Nat.primesLE B).filter (fun p => A < p), (1 : ℝ) / ((p : ℝ) ^ 2) ≤
      24 / ((A : ℝ) * Real.log A) := by
  by_cases hAB : B ≤ A
  · have hemp : (Nat.primesLE B).filter (fun p => A < p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      have := Nat.le_of_mem_primesLE hp
      omega
    rw [hemp, Finset.sum_empty]
    have hlogA : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
    positivity
  push Not at hAB
  let P : ℕ → ℝ := fun m => (Nat.primeCounting m : ℝ)
  let f : ℕ → ℝ := fun m => (1 : ℝ) / ((m : ℝ) ^ 2)
  have hP_diff : ∀ m : ℕ, 1 ≤ m →
      P m - P (m - 1) = if m.Prime then 1 else 0 := by
    intro m hm
    have hstep : Nat.primeCounting m = Nat.primeCounting (m - 1) + if m.Prime then 1 else 0 := by
      have hm_eq : m = (m - 1) + 1 := by omega
      conv_lhs => rw [hm_eq]
      rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
      simp only [Nat.primeCounting, Nat.primeCounting', Nat.sub_add_cancel hm]
    simp only [P, hstep]
    split_ifs <;> push_cast <;> ring
  have hrewrite : ∑ p ∈ (Nat.primesLE B).filter (fun p => A < p), (1 : ℝ) / ((p : ℝ) ^ 2) =
      ∑ m ∈ Finset.Icc (A + 1) B, (P m - P (m - 1)) * f m := by
    have h1 : ∑ m ∈ Finset.Icc (A + 1) B, (P m - P (m - 1)) * f m =
        ∑ m ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, f m := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_Icc] at hm
      rw [hP_diff m (by omega)]
      split_ifs <;> simp
    rw [h1]
    congr 1
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hpB, hp⟩, hAp⟩; exact ⟨⟨by omega, hpB⟩, hp⟩
    · rintro ⟨⟨hAp, hpB⟩, hp⟩; exact ⟨⟨hpB, hp⟩, by omega⟩
  rw [hrewrite, sum_by_parts_Icc P f (A + 1) B (by omega) hAB]
  have hlogA : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  have hPB : P B * f B ≤ 6 / ((A : ℝ) * Real.log A) := by
    have h1 : P B ≤ 6 * (B : ℝ) / Real.log B := primeCounting_nat_le B (by omega)
    have h2 : (A : ℝ) * Real.log A ≤ (B : ℝ) * Real.log B := by
      have hAB_R : (A : ℝ) ≤ B := by exact_mod_cast hAB.le
      have hlogAB : Real.log (A : ℝ) ≤ Real.log B := Real.log_le_log (by positivity) hAB_R
      nlinarith
    have hB_pos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    simp only [f]
    calc P B * (1 / (B : ℝ) ^ 2)
        ≤ (6 * (B : ℝ) / Real.log B) * (1 / (B : ℝ) ^ 2) := by gcongr
      _ = 6 / ((B : ℝ) * Real.log B) := by
          field_simp [hB_pos.ne', hlogB.ne']
      _ ≤ 6 / ((A : ℝ) * Real.log A) := by
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h2
  have hneg : 0 ≤ P (A + 1 - 1) * f (A + 1) := by
    simp only [P, f]
    positivity
  have hsum : ∑ m ∈ Finset.Ico (A + 1) B, P m * (f m - f (m + 1)) ≤
      18 / ((A : ℝ) * Real.log A) := by
    have hterm : ∀ m ∈ Finset.Ico (A + 1) B,
        P m * (f m - f (m + 1)) ≤ (18 / Real.log A) * ((1 : ℝ) / ((m : ℝ) ^ 2)) := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      have hm4 : 4 ≤ m := by omega
      have hm_pos : (0 : ℝ) < m := by positivity
      have hlogm : Real.log (A : ℝ) ≤ Real.log (m : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (by omega : A ≤ m))
      have hPm : P m ≤ 6 * (m : ℝ) / Real.log A := by
        calc P m ≤ 6 * (m : ℝ) / Real.log m := primeCounting_nat_le m hm4
          _ ≤ 6 * (m : ℝ) / Real.log A :=
              div_le_div_of_nonneg_left (by positivity) hlogA hlogm
      have hfdiff : f m - f (m + 1) ≤ 3 / ((m : ℝ) ^ 3) := by
        simp only [f]
        have hrew : 1 / (m : ℝ) ^ 2 - 1 / ((m + 1 : ℕ) : ℝ) ^ 2 =
            (2 * (m : ℝ) + 1) / ((m : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2) := by
          push_cast; field_simp; ring
        rw [hrew, div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        nlinarith
      have hdiff_nn : 0 ≤ f m - f (m + 1) := by
        simp only [f, sub_nonneg]
        apply one_div_le_one_div_of_le (by positivity)
        have : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
        nlinarith
      calc P m * (f m - f (m + 1))
          ≤ (6 * (m : ℝ) / Real.log A) * (3 / ((m : ℝ) ^ 3)) := by
            exact mul_le_mul hPm hfdiff hdiff_nn (by positivity)
        _ = (18 / Real.log A) * (1 / ((m : ℝ) ^ 2)) := by
            field_simp [hm_pos.ne', hlogA.ne']
            ring
    calc ∑ m ∈ Finset.Ico (A + 1) B, P m * (f m - f (m + 1))
        ≤ ∑ m ∈ Finset.Ico (A + 1) B, (18 / Real.log A) * ((1 : ℝ) / ((m : ℝ) ^ 2)) :=
          Finset.sum_le_sum hterm
      _ = (18 / Real.log A) * ∑ m ∈ Finset.Ico (A + 1) B, (1 : ℝ) / ((m : ℝ) ^ 2) := by
          rw [← Finset.mul_sum]
      _ ≤ (18 / Real.log A) * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / ((m : ℝ) ^ 2) := by
          gcongr
          intro m hm
          rw [Finset.mem_Ico] at hm
          rw [Finset.mem_Ioc]; omega
      _ ≤ (18 / Real.log A) * (1 / (A : ℝ)) := by
          gcongr
          exact sum_Ioc_inv_sq_le A B (by omega)
      _ = 18 / ((A : ℝ) * Real.log A) := by ring
  have h24 : 6 / ((A : ℝ) * Real.log A) + 18 / ((A : ℝ) * Real.log A) =
      24 / ((A : ℝ) * Real.log A) := by ring
  linarith

/- ## Section 2: Selberg Upper Bound Sieve and Brun-Titchmarsh Inequality -/

private lemma squarefree_totient_eq_prod (m : ℕ) (hm : Squarefree m) :
    Nat.totient m = ∏ p ∈ m.primeFactors, (p - 1) := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hrad : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hm
  have hmul := Nat.totient_mul_prod_primeFactors m
  rw [hrad] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm0) (by linarith)

private lemma real_div_totient_eq_prod (d : ℕ) (hd : 1 ≤ d) :
    (d : ℝ) / (Nat.totient d : ℝ) =
      ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hphi_pos : (0 : ℝ) < Nat.totient d := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hmul := Nat.totient_mul_prod_primeFactors d
  have hmulR : (Nat.totient d : ℝ) * ∏ p ∈ d.primeFactors, (p : ℝ) =
      (d : ℝ) * ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
    have h1 : ((Nat.totient d * ∏ p ∈ d.primeFactors, p : ℕ) : ℝ) =
        ((d * ∏ p ∈ d.primeFactors, (p - 1) : ℕ) : ℝ) := by exact_mod_cast hmul
    push_cast at h1
    convert h1 using 2
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hden_ne : (∏ p ∈ d.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  rw [Finset.prod_div_distrib, div_eq_div_iff hphi_pos.ne' hden_ne]
  linarith

private lemma squarefree_div_totient_eq_sum_divisors (r : ℕ) (hr : Squarefree r) :
    (r : ℝ) / (Nat.totient r : ℝ) = ∑ u ∈ r.divisors, (1 : ℝ) / (Nat.totient u : ℝ) := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hrad : ∏ p ∈ r.primeFactors, p = r := Nat.prod_primeFactors_of_squarefree hr
  rw [real_div_totient_eq_prod r (Nat.pos_of_ne_zero hr0)]
  have hprod : ∏ p ∈ r.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) =
      ∏ p ∈ r.primeFactors, (1 + (1 : ℝ) / ((p : ℝ) - 1)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
    ring
  rw [hprod, Finset.prod_one_add]
  refine Finset.sum_bij (fun s _ => ∏ p ∈ s, p) ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_powerset] at hs
    rw [Nat.mem_divisors]
    refine ⟨?_, hr0⟩
    rw [← hrad]
    exact Finset.prod_dvd_prod_of_subset s r.primeFactors id hs
  · intro s1 hs1 s2 hs2 heq
    rw [Finset.mem_powerset] at hs1 hs2
    have hpf : ∀ s ⊆ r.primeFactors, (∏ p ∈ s, p).primeFactors = s := fun s hs =>
      Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hs hp))
    rw [← hpf s1 hs1, ← hpf s2 hs2, heq]
  · intro u hu
    rw [Nat.mem_divisors] at hu
    have hu_sq : Squarefree u := hr.squarefree_of_dvd hu.1
    refine ⟨u.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hu_sq⟩
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono hu.1 hr0
  · intro s hs
    rw [Finset.mem_powerset] at hs
    have h1 : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hs hp)
    have hsq : Squarefree (∏ p ∈ s, p) := by
      refine hr.squarefree_of_dvd ?_
      rw [← hrad]
      exact Finset.prod_dvd_prod_of_subset s r.primeFactors id hs
    have hpf : (∏ p ∈ s, p).primeFactors = s := Nat.primeFactors_prod h1
    rw [squarefree_totient_eq_prod _ hsq, hpf]
    push_cast
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (h1 p hp).one_le, Nat.cast_one]

private lemma geom_sum_inv_prime_le (p z : ℕ) (hp : p.Prime) :
    ∑ j ∈ Finset.range (z + 1), ((1 : ℝ) / (p : ℝ)) ^ j ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp_pos : (0 : ℝ) < p := by linarith
  have h1 : (1 - (1 : ℝ) / (p : ℝ)) * ∑ j ∈ Finset.range (z + 1), ((1 : ℝ) / (p : ℝ)) ^ j =
      1 - ((1 : ℝ) / (p : ℝ)) ^ (z + 1) := by
    rw [mul_comm, geom_sum_mul_neg]
  have hpos : 0 < 1 - (1 : ℝ) / (p : ℝ) := by
    rw [sub_pos, div_lt_one hp_pos]; linarith
  have hpow_nn : (0 : ℝ) ≤ ((1 : ℝ) / (p : ℝ)) ^ (z + 1) := by positivity
  have hrew : (p : ℝ) / ((p : ℝ) - 1) = 1 / (1 - (1 : ℝ) / (p : ℝ)) := by
    field_simp [hp_pos.ne', show (p : ℝ) - 1 ≠ 0 by linarith]
  rw [hrew, le_div_iff₀ hpos]
  linarith

private lemma geom_sum_Icc_inv_prime_le (p z : ℕ) (hp : p.Prime) :
    ∑ j ∈ Finset.Icc 1 z, ((1 : ℝ) / (p : ℝ)) ^ j ≤ 1 / ((p : ℝ) - 1) := by
  by_cases hz : z = 0
  · subst hz; simp only [Finset.Icc_eq_empty (by decide : ¬ 1 ≤ 0), Finset.sum_empty]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact one_div_nonneg.mpr (by linarith)
  have hrew : ∑ j ∈ Finset.Icc 1 z, ((1 : ℝ) / (p : ℝ)) ^ j =
      ((1 : ℝ) / (p : ℝ)) * ∑ j ∈ Finset.range z, ((1 : ℝ) / (p : ℝ)) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
    · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
    · intro j1 hj1 j2 hj2 heq
      rw [Finset.mem_Icc] at hj1 hj2; omega
    · intro k hk; rw [Finset.mem_range] at hk
      exact ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj; rw [Finset.mem_Icc] at hj
      have hj_eq : j = (j - 1) + 1 := by omega
      conv_lhs => rw [hj_eq, pow_succ']
  rw [hrew]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsub : ∑ j ∈ Finset.range z, ((1 : ℝ) / (p : ℝ)) ^ j ≤
      ∑ j ∈ Finset.range (z + 1), ((1 : ℝ) / (p : ℝ)) ^ j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ z))
      (fun _ _ _ => by positivity)
  calc ((1 : ℝ) / (p : ℝ)) * ∑ j ∈ Finset.range z, ((1 : ℝ) / (p : ℝ)) ^ j
      ≤ ((1 : ℝ) / (p : ℝ)) * ((p : ℝ) / ((p : ℝ) - 1)) := by
        gcongr
        exact hsub.trans (geom_sum_inv_prime_le p z hp)
    _ = 1 / ((p : ℝ) - 1) := by field_simp [show (p : ℝ) ≠ 0 by linarith]

private lemma prime_pow_factorization_lt (n p z : ℕ) (hn : 1 ≤ n) (hnz : n ≤ z) (hp : p.Prime) :
    n.factorization p ≤ z := by
  have hpow : p ^ (n.factorization p) ≤ n :=
    Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)
  have hlt : n.factorization p < 2 ^ (n.factorization p) := Nat.lt_two_pow_self
  have h2p : 2 ^ (n.factorization p) ≤ p ^ (n.factorization p) :=
    Nat.pow_le_pow_left hp.two_le _
  omega

private lemma sum_inv_smooth_le_prod (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) (z : ℕ) :
    ∑ b ∈ (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ F), (1 : ℝ) / (b : ℝ) ≤
      ∏ p ∈ F, (p : ℝ) / ((p : ℝ) - 1) := by
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have hsub : (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ ∅) ⊆ {1} := by
      intro b hb
      rw [Finset.mem_filter, Finset.mem_Icc] at hb
      rw [Finset.mem_singleton]
      have hemp : b.primeFactors = ∅ := Finset.subset_empty.mp hb.2
      by_contra hne
      have hb2 : 2 ≤ b := by omega
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : b ≠ 1)
      have hmem : p ∈ b.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by omega⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty p hmem
    calc ∑ b ∈ (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ ∅), (1 : ℝ) / (b : ℝ)
        ≤ ∑ b ∈ ({1} : Finset ℕ), (1 : ℝ) / (b : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | @insert p s hps ih =>
    have hp : p.Prime := hF p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hF q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps]
    let S1 := (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ insert p s)
    let S0 := (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ s)
    have hinj : ∑ b ∈ S1, (1 : ℝ) / (b : ℝ) ≤
        ∑ x ∈ Finset.range (z + 1) ×ˢ S0,
          ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)) := by
      let phi : ℕ → ℕ × ℕ := fun b => (b.factorization p, b / p ^ (b.factorization p))
      have hmaps : ∀ b ∈ S1, phi b ∈ Finset.range (z + 1) ×ˢ S0 := by
        intro b hb
        simp only [S1, Finset.mem_filter, Finset.mem_Icc] at hb
        rw [Finset.mem_product, Finset.mem_range]
        refine ⟨Nat.lt_succ_of_le (prime_pow_factorization_lt b p z hb.1.1 hb.1.2 hp), ?_⟩
        simp only [S0, Finset.mem_filter, Finset.mem_Icc]
        have hdvd : p ^ (b.factorization p) ∣ b := Nat.ordProj_dvd b p
        have hpos : 0 < b / p ^ (b.factorization p) :=
          Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (pow_pos hp.pos _)
        have hle : b / p ^ (b.factorization p) ≤ z := (Nat.div_le_self b _).trans hb.1.2
        refine ⟨⟨hpos, hle⟩, ?_⟩
        intro q hq
        have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
        have hqdvd_quot : q ∣ b / p ^ (b.factorization p) := Nat.dvd_of_mem_primeFactors hq
        have hqdvd_b : q ∣ b := hqdvd_quot.trans (Nat.div_dvd_of_dvd hdvd)
        have hqmem : q ∈ insert p s := hb.2 (Nat.mem_primeFactors.mpr ⟨hqp, hqdvd_b, by omega⟩)
        rcases Finset.mem_insert.mp hqmem with rfl | hqs
        · exfalso
          exact Nat.not_dvd_ordCompl hp (by omega) hqdvd_quot
        · exact hqs
      have hinj_phi : Set.InjOn phi S1 := by
        intro b1 hb1 b2 hb2 heq
        simp only [phi, Prod.mk.injEq] at heq
        have h1 := Nat.mul_div_cancel' (Nat.ordProj_dvd b1 p)
        have h2 := Nat.mul_div_cancel' (Nat.ordProj_dvd b2 p)
        rw [← h1, ← h2, heq.2, heq.1]
      have hval : ∀ b ∈ S1,
          (1 : ℝ) / (b : ℝ) = ((1 : ℝ) / (p : ℝ)) ^ (phi b).1 * ((1 : ℝ) / ((phi b).2 : ℝ)) := by
        intro b hb
        simp only [phi]
        have hmul := Nat.mul_div_cancel' (Nat.ordProj_dvd b p)
        have hmulR : (b : ℝ) = (p : ℝ) ^ (b.factorization p) * ((b / p ^ (b.factorization p) : ℕ) : ℝ) := by
          exact_mod_cast hmul.symm
        rw [hmulR, one_div_pow, one_div_mul_one_div]
      calc ∑ b ∈ S1, (1 : ℝ) / (b : ℝ)
          = ∑ b ∈ S1, ((1 : ℝ) / (p : ℝ)) ^ (phi b).1 * ((1 : ℝ) / ((phi b).2 : ℝ)) :=
            Finset.sum_congr rfl hval
        _ = ∑ x ∈ S1.image phi, ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)) :=
            (Finset.sum_image (f := fun x : ℕ × ℕ => ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)))
              (fun a ha b hb h => hinj_phi ha hb h)).symm
        _ ≤ ∑ x ∈ Finset.range (z + 1) ×ˢ S0,
              ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.image_subset_iff.mpr hmaps) (fun _ _ _ => by positivity)
    calc ∑ b ∈ S1, (1 : ℝ) / (b : ℝ)
        ≤ ∑ x ∈ Finset.range (z + 1) ×ˢ S0,
            ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)) := hinj
      _ = (∑ j ∈ Finset.range (z + 1), ((1 : ℝ) / (p : ℝ)) ^ j) *
            (∑ b ∈ S0, (1 : ℝ) / (b : ℝ)) := by
          simp only [Finset.sum_product]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum ..).symm
      _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) * ∏ q ∈ s, (q : ℝ) / ((q : ℝ) - 1) := by
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          apply mul_le_mul (geom_sum_inv_prime_le p z hp) (ih hs)
            (Finset.sum_nonneg fun _ _ => by positivity)
            (div_nonneg (by linarith) (by linarith))

private lemma sum_inv_same_primeFactors_le_prod (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) (z : ℕ) :
    ∑ a ∈ (Finset.Icc 1 z).filter (fun a => a.primeFactors = F), (1 : ℝ) / (a : ℝ) ≤
      ∏ p ∈ F, (1 : ℝ) / ((p : ℝ) - 1) := by
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have hsub : (Finset.Icc 1 z).filter (fun a => a.primeFactors = ∅) ⊆ {1} := by
      intro a ha
      rw [Finset.mem_filter, Finset.mem_Icc] at ha
      rw [Finset.mem_singleton]
      by_contra hne
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
      have hmem : p ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by omega⟩
      rw [ha.2] at hmem
      exact Finset.notMem_empty p hmem
    calc ∑ a ∈ (Finset.Icc 1 z).filter (fun a => a.primeFactors = ∅), (1 : ℝ) / (a : ℝ)
        ≤ ∑ a ∈ ({1} : Finset ℕ), (1 : ℝ) / (a : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | @insert p s hps ih =>
    have hp : p.Prime := hF p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hF q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps]
    let S1 := (Finset.Icc 1 z).filter (fun a => a.primeFactors = insert p s)
    let S0 := (Finset.Icc 1 z).filter (fun a => a.primeFactors = s)
    let phi : ℕ → ℕ × ℕ := fun a => (a.factorization p, a / p ^ (a.factorization p))
    have hmaps : ∀ a ∈ S1, phi a ∈ Finset.Icc 1 z ×ˢ S0 := by
      intro a ha
      simp only [S1, Finset.mem_filter, Finset.mem_Icc] at ha
      rw [Finset.mem_product, Finset.mem_Icc]
      have hpmem : p ∈ a.primeFactors := by rw [ha.2]; exact Finset.mem_insert_self p s
      have hpdvd : p ∣ a := Nat.dvd_of_mem_primeFactors hpmem
      have hfac_pos : 1 ≤ a.factorization p := by
        have hne : a.factorization p ≠ 0 :=
          (Nat.Prime.dvd_iff_one_le_factorization hp (by omega)).mp hpdvd |> Nat.pos_iff_ne_zero.mp
        omega
      refine ⟨⟨hfac_pos, prime_pow_factorization_lt a p z ha.1.1 ha.1.2 hp⟩, ?_⟩
      simp only [S0, Finset.mem_filter, Finset.mem_Icc]
      have hdvd : p ^ (a.factorization p) ∣ a := Nat.ordProj_dvd a p
      have hpos : 0 < a / p ^ (a.factorization p) :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (pow_pos hp.pos _)
      have hle : a / p ^ (a.factorization p) ≤ z := (Nat.div_le_self a _).trans ha.1.2
      refine ⟨⟨hpos, hle⟩, ?_⟩
      ext q
      constructor
      · intro hq
        have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
        have hqdvd_quot : q ∣ a / p ^ (a.factorization p) := Nat.dvd_of_mem_primeFactors hq
        have hqdvd_a : q ∣ a := hqdvd_quot.trans (Nat.div_dvd_of_dvd hdvd)
        have hqmem : q ∈ insert p s := by
          rw [← ha.2]; exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd_a, by omega⟩
        rcases Finset.mem_insert.mp hqmem with rfl | hqs
        · exfalso
          exact Nat.not_dvd_ordCompl hp (by omega) hqdvd_quot
        · exact hqs
      · intro hqs
        have hqp : q.Prime := hs q hqs
        have hqne : q ≠ p := fun h => hps (h ▸ hqs)
        have hqmem : q ∈ a.primeFactors := by rw [ha.2]; exact Finset.mem_insert_of_mem hqs
        have hqdvd_a : q ∣ a := Nat.dvd_of_mem_primeFactors hqmem
        have hcop : Nat.Coprime q (p ^ (a.factorization p)) :=
          (hqp.coprime_iff_not_dvd.mpr fun h => hqne ((Nat.prime_dvd_prime_iff_eq hqp hp).mp h)).pow_right _
        have hmul : p ^ (a.factorization p) * (a / p ^ (a.factorization p)) = a :=
          Nat.mul_div_cancel' hdvd
        have hqdvd_quot : q ∣ a / p ^ (a.factorization p) := by
          rw [← hmul] at hqdvd_a
          exact hcop.dvd_of_dvd_mul_left hqdvd_a
        exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd_quot, hpos.ne'⟩
    have hinj_phi : Set.InjOn phi S1 := by
      intro a1 ha1 a2 ha2 heq
      simp only [phi, Prod.mk.injEq] at heq
      have h1 := Nat.mul_div_cancel' (Nat.ordProj_dvd a1 p)
      have h2 := Nat.mul_div_cancel' (Nat.ordProj_dvd a2 p)
      rw [← h1, ← h2, heq.2, heq.1]
    have hval : ∀ a ∈ S1,
        (1 : ℝ) / (a : ℝ) = ((1 : ℝ) / (p : ℝ)) ^ (phi a).1 * ((1 : ℝ) / ((phi a).2 : ℝ)) := by
      intro a ha
      simp only [phi]
      have hmul := Nat.mul_div_cancel' (Nat.ordProj_dvd a p)
      have hmulR : (a : ℝ) = (p : ℝ) ^ (a.factorization p) * ((a / p ^ (a.factorization p) : ℕ) : ℝ) := by
        exact_mod_cast hmul.symm
      rw [hmulR, one_div_pow, one_div_mul_one_div]
    calc ∑ a ∈ S1, (1 : ℝ) / (a : ℝ)
        = ∑ a ∈ S1, ((1 : ℝ) / (p : ℝ)) ^ (phi a).1 * ((1 : ℝ) / ((phi a).2 : ℝ)) :=
          Finset.sum_congr rfl hval
      _ = ∑ x ∈ S1.image phi, ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)) :=
          (Finset.sum_image (f := fun x : ℕ × ℕ => ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)))
            (fun a ha b hb h => hinj_phi ha hb h)).symm
      _ ≤ ∑ x ∈ Finset.Icc 1 z ×ˢ S0,
            ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.image_subset_iff.mpr hmaps) (fun _ _ _ => by positivity)
      _ = (∑ j ∈ Finset.Icc 1 z, ((1 : ℝ) / (p : ℝ)) ^ j) *
            (∑ a ∈ S0, (1 : ℝ) / (a : ℝ)) := by
          simp only [Finset.sum_product]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum ..).symm
      _ ≤ (1 / ((p : ℝ) - 1)) * ∏ q ∈ s, (1 : ℝ) / ((q : ℝ) - 1) := by
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          apply mul_le_mul (geom_sum_Icc_inv_prime_le p z hp) (ih hs)
            (Finset.sum_nonneg fun _ _ => by positivity)
            (div_nonneg zero_le_one (by linarith))

private lemma selberg_G_lower_bound (z d : ℕ) (_hz : 1 ≤ z) (hd : 1 ≤ d) :
    Real.log ((z + 1 : ℕ) : ℝ) ≤
      ((d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ Nat.Coprime m d),
          (1 : ℝ) / (Nat.totient m : ℝ) := by
  let S := (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ Nat.Coprime m d)
  let B := (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ d.primeFactors)
  let A : ℕ → Finset ℕ := fun m => (Finset.Icc 1 z).filter (fun a => a.primeFactors = m.primeFactors)
  have hB : ∑ b ∈ B, (1 : ℝ) / (b : ℝ) ≤ (d : ℝ) / (Nat.totient d : ℝ) := by
    rw [real_div_totient_eq_prod d hd]
    exact sum_inv_smooth_le_prod d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) z
  have hA : ∀ m ∈ S, ∑ a ∈ A m, (1 : ℝ) / (a : ℝ) ≤ (1 : ℝ) / (Nat.totient m : ℝ) := by
    intro m hm
    simp only [S, Finset.mem_filter] at hm
    rw [squarefree_totient_eq_prod m hm.2.1]
    have hprod_eq : (1 : ℝ) / ((∏ p ∈ m.primeFactors, (p - 1) : ℕ) : ℝ) =
        ∏ p ∈ m.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
      push_cast
      rw [Finset.prod_div_distrib, Finset.prod_const_one]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
    rw [hprod_eq]
    exact sum_inv_same_primeFactors_le_prod m.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp) z
  let bPart : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors.filter (· ∣ d), p ^ (n.factorization p)
  let aPart : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ d), p ^ (n.factorization p)
  let radA : ℕ → ℕ := fun n => ∏ p ∈ (aPart n).primeFactors, p
  let psi : ℕ → ℕ × ℕ × ℕ := fun n => (bPart n, radA n, aPart n)
  have hmul_ba : ∀ n ∈ Finset.Icc 1 z, bPart n * aPart n = n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    dsimp only [bPart, aPart]
    rw [Finset.prod_filter_mul_prod_filter_not]
    have h := Nat.prod_factorization_pow_eq_self (by omega : n ≠ 0)
    rw [Finsupp.prod] at h
    simpa [Nat.support_factorization] using h
  have hmaps : ∀ n ∈ Finset.Icc 1 z,
      psi n ∈ B ×ˢ (S.biUnion fun m => ({m} : Finset ℕ) ×ˢ A m) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hba := hmul_ba n (Finset.mem_Icc.mpr hn)
    have hb_pos : 1 ≤ bPart n := by
      have : 0 < bPart n := Finset.prod_pos fun p hp =>
        pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
      omega
    have ha_pos : 1 ≤ aPart n := by
      have : 0 < aPart n := Finset.prod_pos fun p hp =>
        pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
      omega
    have hb_le : bPart n ≤ z := by nlinarith
    have ha_le : aPart n ≤ z := by nlinarith
    have hb_mem : bPart n ∈ B := by
      simp only [B, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hb_pos, hb_le⟩, fun q hq => ?_⟩
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqdvd : q ∣ bPart n := Nat.dvd_of_mem_primeFactors hq
      rw [hqp.prime.dvd_finsetProd_iff] at hqdvd
      obtain ⟨p, hp, hqpow⟩ := hqdvd
      rw [Finset.mem_filter] at hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
      have hqp_eq : q = p := (Nat.prime_dvd_prime_iff_eq hqp hpp).mp (hqp.dvd_of_dvd_pow hqpow)
      subst hqp_eq
      exact Nat.mem_primeFactors.mpr ⟨hpp, hp.2, by omega⟩
    have ha_cop : Nat.Coprime (aPart n) d := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨q, hqp, hqdvd⟩ := Nat.exists_prime_and_dvd hne
      have hqa : q ∣ aPart n := hqdvd.trans (Nat.gcd_dvd_left _ _)
      have hqd : q ∣ d := hqdvd.trans (Nat.gcd_dvd_right _ _)
      rw [hqp.prime.dvd_finsetProd_iff] at hqa
      obtain ⟨p, hp, hqpow⟩ := hqa
      rw [Finset.mem_filter] at hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
      have hqp_eq : q = p := (Nat.prime_dvd_prime_iff_eq hqp hpp).mp (hqp.dvd_of_dvd_pow hqpow)
      subst hqp_eq
      exact hp.2 hqd
    have hrad_dvd : radA n ∣ aPart n := Nat.prod_primeFactors_dvd (aPart n)
    have hrad_pos : 1 ≤ radA n := by
      have : 0 < radA n := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
      omega
    have hrad_le : radA n ≤ z := (Nat.le_of_dvd ha_pos hrad_dvd).trans ha_le
    have hrad_pf : (radA n).primeFactors = (aPart n).primeFactors :=
      Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)
    have hrad_sq : Squarefree (radA n) := by
      dsimp only [radA]
      rw [Nat.squarefree_iff_prime_squarefree]
      intro q hq hq2
      have hqmem : q ∈ (aPart n).primeFactors := by
        rw [← hrad_pf]
        exact Nat.mem_primeFactors.mpr ⟨hq, (dvd_mul_left q q).trans hq2, by omega⟩
      have hprod_eq : ∏ p ∈ (aPart n).primeFactors, p =
          q * ∏ p ∈ (aPart n).primeFactors.erase q, p :=
        (Finset.mul_prod_erase _ _ hqmem).symm
      rw [hprod_eq] at hq2
      have hq_rest : q ∣ ∏ p ∈ (aPart n).primeFactors.erase q, p :=
        (Nat.mul_dvd_mul_iff_left hq.pos).mp hq2
      rw [hq.prime.dvd_finsetProd_iff] at hq_rest
      obtain ⟨p, hp, hqp⟩ := hq_rest
      rw [Finset.mem_erase] at hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.2
      exact hp.1 ((Nat.prime_dvd_prime_iff_eq hq hpp).mp hqp).symm
    have hrad_cop : Nat.Coprime (radA n) d := ha_cop.coprime_dvd_left hrad_dvd
    have hrad_mem : radA n ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hrad_pos, hrad_le⟩, hrad_sq, hrad_cop⟩
    have ha_mem : aPart n ∈ A (radA n) := by
      simp only [A, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨ha_pos, ha_le⟩, hrad_pf.symm⟩
    rw [Finset.mem_product]
    refine ⟨hb_mem, Finset.mem_biUnion.mpr ⟨radA n, hrad_mem, ?_⟩⟩
    rw [Finset.mem_product, Finset.mem_singleton]
    exact ⟨rfl, ha_mem⟩
  have hinj : Set.InjOn psi (Finset.Icc 1 z) := by
    intro n1 hn1 n2 hn2 heq
    simp only [psi, Prod.mk.injEq] at heq
    rw [← hmul_ba n1 hn1, ← hmul_ba n2 hn2, heq.1, heq.2.2]
  have hsum_le : ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ) ≤
      (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) * (∑ m ∈ S, ∑ a ∈ A m, (1 : ℝ) / (a : ℝ)) := by
    have hval : ∀ n ∈ Finset.Icc 1 z,
        (1 : ℝ) / (n : ℝ) = ((1 : ℝ) / ((psi n).1 : ℝ)) * ((1 : ℝ) / ((psi n).2.2 : ℝ)) := by
      intro n hn
      simp only [psi]
      have hba : (n : ℝ) = (bPart n : ℝ) * (aPart n : ℝ) := by
        exact_mod_cast (hmul_ba n hn).symm
      rw [hba, one_div_mul_one_div]
    calc ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ)
        = ∑ n ∈ Finset.Icc 1 z,
            ((1 : ℝ) / ((psi n).1 : ℝ)) * ((1 : ℝ) / ((psi n).2.2 : ℝ)) :=
          Finset.sum_congr rfl hval
      _ = ∑ x ∈ (Finset.Icc 1 z).image psi,
            ((1 : ℝ) / (x.1 : ℝ)) * ((1 : ℝ) / (x.2.2 : ℝ)) :=
          (Finset.sum_image
            (f := fun x : ℕ × ℕ × ℕ => ((1 : ℝ) / (x.1 : ℝ)) * ((1 : ℝ) / (x.2.2 : ℝ)))
            (fun a ha b hb h => hinj ha hb h)).symm
      _ ≤ ∑ x ∈ B ×ˢ (S.biUnion fun m => ({m} : Finset ℕ) ×ˢ A m),
            ((1 : ℝ) / (x.1 : ℝ)) * ((1 : ℝ) / (x.2.2 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.image_subset_iff.mpr hmaps) (fun _ _ _ => by positivity)
      _ = (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) *
            (∑ y ∈ S.biUnion (fun m => ({m} : Finset ℕ) ×ˢ A m), (1 : ℝ) / (y.2 : ℝ)) := by
          simp only [Finset.sum_product]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => (Finset.mul_sum ..).symm
      _ = (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) * (∑ m ∈ S, ∑ a ∈ A m, (1 : ℝ) / (a : ℝ)) := by
          congr 1
          rw [Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun m _ => ?_
            simp only [Finset.sum_product, Finset.sum_singleton]
          · intro m1 _ m2 _ hne
            change Disjoint (({m1} : Finset ℕ) ×ˢ A m1) (({m2} : Finset ℕ) ×ˢ A m2)
            rw [Finset.disjoint_left]
            intro y hy1 hy2
            rw [Finset.mem_product, Finset.mem_singleton] at hy1 hy2
            exact hne (hy1.1.symm.trans hy2.1)
  have hlog_le : Real.log ((z + 1 : ℕ) : ℝ) ≤ ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ) := by
    rw [sum_Icc_inv_eq_harmonic]
    exact log_add_one_le_harmonic z
  calc Real.log ((z + 1 : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ) := hlog_le
    _ ≤ (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) * (∑ m ∈ S, ∑ a ∈ A m, (1 : ℝ) / (a : ℝ)) := hsum_le
    _ ≤ ((d : ℝ) / (Nat.totient d : ℝ)) * (∑ m ∈ S, (1 : ℝ) / (Nat.totient m : ℝ)) := by
        apply mul_le_mul hB (Finset.sum_le_sum hA)
          (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
          (by positivity)

private lemma count_mod_eq_Icc_approx (X : ℝ) (M c : ℕ) (hX : 0 ≤ X) (hM : 1 ≤ M) (hc : c < M) :
    |((((Finset.Icc 1 ⌊X⌋₊).filter (fun n => n % M = c)).card : ℝ) - X / (M : ℝ))| ≤ 1 := by
  let N := ⌊X⌋₊
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hX
  have hXN : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
  have hM_pos : (0 : ℝ) < M := by positivity
  by_cases hc0 : c = 0
  · subst hc0
    have hcard : ((Finset.Icc 1 N).filter (fun n => n % M = 0)).card = N / M := by
      have hbij : ((Finset.Icc 1 N).filter (fun n => n % M = 0)) =
          (Finset.Icc 1 (N / M)).image (fun k => k * M) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hn1, hnN⟩, hmod⟩
          have hdvd : M ∣ n := Nat.dvd_of_mod_eq_zero hmod
          refine ⟨n / M, ⟨?_, Nat.div_le_div_right hnN⟩, Nat.div_mul_cancel hdvd⟩
          exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
        · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
          refine ⟨⟨by nlinarith, (Nat.mul_le_mul_right M hkN).trans (Nat.div_mul_le_self N M)⟩,
            Nat.mul_mod_left k M⟩
      rw [hbij, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right (by omega) h)]
      simp
    rw [hcard, abs_le]
    have h1 : (N / M : ℕ) * M ≤ N := Nat.div_mul_le_self N M
    have h2 : N < (N / M + 1) * M := by
      have := Nat.lt_div_mul_add (a := N) (by omega : 0 < M)
      linarith
    have h1R : ((N / M : ℕ) : ℝ) * (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
    have h2R : (N : ℝ) < (((N / M : ℕ) : ℝ) + 1) * (M : ℝ) := by exact_mod_cast h2
    constructor
    · have hnat2 : N + 1 ≤ (N / M + 1) * M := h2
      have hnat2R : (N : ℝ) + 1 ≤ (((N / M : ℕ) : ℝ) + 1) * (M : ℝ) := by exact_mod_cast hnat2
      have hdiv : X / (M : ℝ) ≤ ((N / M : ℕ) : ℝ) + 1 := (div_le_iff₀ hM_pos).mpr (by linarith)
      linarith
    · rw [sub_le_iff_le_add]
      have : ((N / M : ℕ) : ℝ) ≤ X / (M : ℝ) := by rw [le_div_iff₀ hM_pos]; linarith
      linarith
  · have hc1 : 1 ≤ c := by omega
    let q := (N + M - c) / M
    have hcard : ((Finset.Icc 1 N).filter (fun n => n % M = c)).card = q := by
      have hbij : ((Finset.Icc 1 N).filter (fun n => n % M = c)) =
          (Finset.range q).image (fun k => c + k * M) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨⟨hn1, hnN⟩, hmod⟩
          have hdiv : M * (n / M) + c = n := by rw [← hmod]; exact Nat.div_add_mod n M
          refine ⟨n / M, ?_, by linarith⟩
          have hmul_le : (n / M + 1) * M ≤ N + M - c := by
            have : (n / M + 1) * M = M * (n / M) + M := by ring
            omega
          have hle_q : n / M + 1 ≤ q := (Nat.le_div_iff_mul_le (by omega)).mpr hmul_le
          omega
        · rintro ⟨k, hk, rfl⟩
          have hklt : k * M + c ≤ N := by
            have h1 : (k + 1) * M ≤ q * M := Nat.mul_le_mul_right M hk
            have h2 : q * M ≤ N + M - c := Nat.div_mul_le_self (N + M - c) M
            have h3 : (k + 1) * M = k * M + M := by ring
            omega
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
      rw [hbij, Finset.card_image_of_injective _ (fun a b h => by
        have h1 : a * M = b * M := by omega
        exact Nat.eq_of_mul_eq_mul_right (by omega) h1), Finset.card_range]
    rw [hcard, abs_le]
    have hq1 : q * M ≤ N + M - c := Nat.div_mul_le_self (N + M - c) M
    have hq2 : N + M - c < (q + 1) * M := by
      have := Nat.lt_div_mul_add (a := N + M - c) (by omega : 0 < M)
      dsimp only [q]
      rw [add_mul, one_mul]
      omega
    have hq1_le : q * M + 1 ≤ N + M := by omega
    have hq2_ge : N + 1 ≤ (q + 1) * M := by omega
    have hq1R : (q : ℝ) * (M : ℝ) + 1 ≤ (N : ℝ) + (M : ℝ) := by exact_mod_cast hq1_le
    have hq2R : (N : ℝ) + 1 ≤ ((q : ℝ) + 1) * (M : ℝ) := by exact_mod_cast hq2_ge
    constructor
    · have hdiv : X / (M : ℝ) ≤ (q : ℝ) + 1 := (div_le_iff₀ hM_pos).mpr (by linarith)
      linarith
    · rw [sub_le_iff_le_add]
      have : (q : ℝ) * (M : ℝ) ≤ X + (M : ℝ) := by linarith
      rw [show (1 : ℝ) + X / (M : ℝ) = (X + (M : ℝ)) / (M : ℝ) by field_simp [hM_pos.ne']; ring]
      exact (le_div_iff₀ hM_pos).mpr this

private lemma count_ap_dvd_approx (X : ℝ) (d a L : ℕ)
    (hX : 0 ≤ X) (hd : 1 ≤ d) (hL : 1 ≤ L) (hcop : Nat.Coprime L d) :
    |((((Finset.Icc 1 ⌊X⌋₊).filter (fun n => n % d = a % d ∧ L ∣ n)).card : ℝ) -
        X / ((d * L : ℕ) : ℝ))| ≤ 1 := by
  let cr := Nat.chineseRemainder hcop 0 a
  let c := cr.val % (d * L)
  have hM : 1 ≤ d * L := Nat.mul_pos (by omega) (by omega)
  have hc : c < d * L := Nat.mod_lt _ hM
  have hc_mod_d : c % d = a % d := by
    have h1 : c % d = cr.val % d := Nat.mod_mod_of_dvd cr.val (dvd_mul_right d L)
    rw [h1]
    exact cr.property.2
  have hc_dvd_L : L ∣ c := by
    have h1 : c % L = cr.val % L := Nat.mod_mod_of_dvd cr.val (dvd_mul_left L d)
    rw [Nat.dvd_iff_mod_eq_zero, h1]
    have h2 : cr.val ≡ 0 [MOD L] := cr.property.1
    simpa [Nat.ModEq] using h2
  have hfilt : (Finset.Icc 1 ⌊X⌋₊).filter (fun n => n % d = a % d ∧ L ∣ n) =
      (Finset.Icc 1 ⌊X⌋₊).filter (fun n => n % (d * L) = c) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hnd, hnL⟩
      refine ⟨hn, ?_⟩
      have hmod_d : n ≡ c [MOD d] := by
        show n % d = c % d; rw [hnd, hc_mod_d]
      have hmod_L : n ≡ c [MOD L] := by
        show n % L = c % L
        rw [Nat.dvd_iff_mod_eq_zero.mp hnL, Nat.dvd_iff_mod_eq_zero.mp hc_dvd_L]
      have hmod_dL : n ≡ c [MOD d * L] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mp ⟨hmod_d, hmod_L⟩
      show n % (d * L) = c
      rw [Nat.ModEq] at hmod_dL
      rwa [Nat.mod_eq_of_lt hc] at hmod_dL
    · rintro ⟨hn, hnc⟩
      refine ⟨hn, ?_, ?_⟩
      · calc n % d = (n % (d * L)) % d := (Nat.mod_mod_of_dvd n (dvd_mul_right d L)).symm
          _ = c % d := by rw [hnc]
          _ = a % d := hc_mod_d
      · rw [Nat.dvd_iff_mod_eq_zero]
        calc n % L = (n % (d * L)) % L := (Nat.mod_mod_of_dvd n (dvd_mul_left L d)).symm
          _ = c % L := by rw [hnc]
          _ = 0 := Nat.dvd_iff_mod_eq_zero.mp hc_dvd_L
  rw [hfilt]
  exact count_mod_eq_Icc_approx X (d * L) c hX hM hc

private lemma sum_moebius_divisors_eq_ite (k : ℕ) (hk : 1 ≤ k) :
    ∑ t ∈ k.divisors, (ArithmeticFunction.moebius t : ℝ) = if k = 1 then 1 else 0 := by
  have hZ : ∑ t ∈ k.divisors, (ArithmeticFunction.moebius t : ℤ) = if k = 1 then 1 else 0 := by
    have h := congr_fun (congr_arg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) k
    simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, ArithmeticFunction.one_apply, Nat.cast_ite,
      Nat.cast_zero, Nat.cast_one] at h
    rw [Nat.sum_divisorsAntidiagonal (fun x y =>
      ArithmeticFunction.moebius x * (if y = 0 then (0 : ℤ) else 1))] at h
    have heq : ∑ t ∈ k.divisors, ArithmeticFunction.moebius t *
        (if k / t = 0 then (0 : ℤ) else 1) =
        ∑ t ∈ k.divisors, ArithmeticFunction.moebius t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Nat.mem_divisors] at ht
      have hkt : k / t ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) ht.1)
        (Nat.pos_of_dvd_of_pos ht.1 (by omega))).ne'
      simp [hkt]
    rw [heq] at h
    exact h
  have hR : ((∑ t ∈ k.divisors, (ArithmeticFunction.moebius t : ℤ) : ℤ) : ℝ) =
      ((if k = 1 then (1 : ℤ) else 0) : ℝ) := by exact_mod_cast hZ
  push_cast at hR
  exact hR

private noncomputable def selbergS (z d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ Nat.Coprime m d)

private noncomputable def selbergG (z d : ℕ) : ℝ :=
  ∑ m ∈ selbergS z d, (1 : ℝ) / (Nat.totient m : ℝ)

private noncomputable def selbergY (z d m : ℕ) : ℝ :=
  if m ∈ selbergS z d then
    (ArithmeticFunction.moebius m : ℝ) / ((Nat.totient m : ℝ) * selbergG z d)
  else 0

private noncomputable def selbergLam (z d r : ℕ) : ℝ :=
  if r ∈ selbergS z d then
    (r : ℝ) * ∑ m ∈ (selbergS z d).filter (r ∣ ·),
      (ArithmeticFunction.moebius (m / r) : ℝ) * selbergY z d m
  else 0

private lemma one_mem_selbergS {z d : ℕ} (hz : 1 ≤ z) : 1 ∈ selbergS z d := by
  simp only [selbergS, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨le_rfl, hz⟩, squarefree_one, Nat.coprime_one_left d⟩

private lemma selbergS_dvd_closed {z d m k : ℕ} (hk : k ∈ selbergS z d) (hmk : m ∣ k) :
    m ∈ selbergS z d := by
  simp only [selbergS, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
  have hm_pos : 1 ≤ m := Nat.pos_of_dvd_of_pos hmk (by omega)
  have hm_le : m ≤ z := (Nat.le_of_dvd (by omega) hmk).trans hk.1.2
  exact ⟨⟨hm_pos, hm_le⟩, hk.2.1.squarefree_of_dvd hmk, hk.2.2.coprime_dvd_left hmk⟩

private lemma selbergG_ge_one {z d : ℕ} (hz : 1 ≤ z) : 1 ≤ selbergG z d := by
  dsimp only [selbergG]
  calc (1 : ℝ) = (1 : ℝ) / (Nat.totient 1 : ℝ) := by simp
    _ ≤ ∑ m ∈ selbergS z d, (1 : ℝ) / (Nat.totient m : ℝ) :=
        Finset.single_le_sum (f := fun m => (1 : ℝ) / (Nat.totient m : ℝ))
          (fun _ _ => by positivity) (one_mem_selbergS hz)

private lemma moebius_sq_of_mem_selbergS {z d m : ℕ} (hm : m ∈ selbergS z d) :
    ((ArithmeticFunction.moebius m : ℝ)) ^ 2 = 1 := by
  simp only [selbergS, Finset.mem_filter] at hm
  rw [ArithmeticFunction.moebius_apply_of_squarefree hm.2.1]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  simp

private lemma selbergLam_one {z d : ℕ} (hz : 1 ≤ z) : selbergLam z d 1 = 1 := by
  have h1S : 1 ∈ selbergS z d := one_mem_selbergS hz
  have hG_pos : 0 < selbergG z d := lt_of_lt_of_le zero_lt_one (selbergG_ge_one hz)
  simp only [selbergLam, h1S, ↓reduceIte, Nat.cast_one, one_mul, Nat.div_one]
  have hfilt1 : (selbergS z d).filter (1 ∣ ·) = selbergS z d :=
    Finset.filter_true_of_mem fun _ _ => one_dvd _
  rw [hfilt1]
  calc ∑ m ∈ selbergS z d, (ArithmeticFunction.moebius m : ℝ) * selbergY z d m
      = ∑ m ∈ selbergS z d, (1 : ℝ) / ((Nat.totient m : ℝ) * selbergG z d) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        simp only [selbergY, hm, ↓reduceIte]
        have hsq := moebius_sq_of_mem_selbergS hm
        have hphi_ne : (Nat.totient m : ℝ) ≠ 0 := by
          simp only [selbergS, Finset.mem_filter, Finset.mem_Icc] at hm
          exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
        field_simp [hphi_ne, hG_pos.ne']
        linarith
    _ = (1 / selbergG z d) * selbergG z d := by
        dsimp only [selbergG]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => by ring
    _ = 1 := by field_simp [hG_pos.ne']

private lemma selbergLam_inv {z d m : ℕ} (hm : m ∈ selbergS z d) :
    ∑ r ∈ (selbergS z d).filter (m ∣ ·), selbergLam z d r / (r : ℝ) = selbergY z d m := by
  let S := selbergS z d
  have hstep1 : ∑ r ∈ S.filter (m ∣ ·), selbergLam z d r / (r : ℝ) =
      ∑ r ∈ S.filter (m ∣ ·), ∑ k ∈ S.filter (r ∣ ·),
        (ArithmeticFunction.moebius (k / r) : ℝ) * selbergY z d k := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_filter] at hr
    have hr_pos : (0 : ℝ) < r := by
      simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hr
      exact_mod_cast (by omega : 0 < r)
    have hrS : r ∈ selbergS z d := hr.1
    simp only [selbergLam, hrS, ↓reduceIte]
    field_simp [hr_pos.ne']
    rfl
  rw [hstep1]
  have hswap : ∑ r ∈ S.filter (m ∣ ·), ∑ k ∈ S.filter (r ∣ ·),
        (ArithmeticFunction.moebius (k / r) : ℝ) * selbergY z d k =
      ∑ k ∈ S.filter (m ∣ ·), (∑ r ∈ k.divisors.filter (m ∣ ·),
        (ArithmeticFunction.moebius (k / r) : ℝ)) * selbergY z d k := by
    trans ∑ r ∈ S.filter (m ∣ ·), ∑ k ∈ S.filter (m ∣ ·),
        if r ∣ k then (ArithmeticFunction.moebius (k / r) : ℝ) * selbergY z d k else 0
    · refine Finset.sum_congr rfl fun r hr => ?_
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter]
      rw [Finset.mem_filter] at hr
      constructor
      · rintro ⟨hk, hrk⟩; exact ⟨⟨hk, hr.2.trans hrk⟩, hrk⟩
      · rintro ⟨⟨hk, _⟩, hrk⟩; exact ⟨hk, hrk⟩
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← Finset.sum_filter, Finset.sum_mul]
      congr 1
      ext r
      simp only [Finset.mem_filter, Nat.mem_divisors]
      rw [Finset.mem_filter] at hk
      have hk0 : k ≠ 0 := by
        simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hk; omega
      constructor
      · rintro ⟨⟨_, hmr⟩, hrk⟩; exact ⟨⟨hrk, hk0⟩, hmr⟩
      · rintro ⟨⟨hrk, _⟩, hmr⟩; exact ⟨⟨selbergS_dvd_closed hk.1 hrk, hmr⟩, hrk⟩
  rw [hswap]
  have hinner : ∀ k ∈ S.filter (m ∣ ·),
      (∑ r ∈ k.divisors.filter (m ∣ ·), (ArithmeticFunction.moebius (k / r) : ℝ)) * selbergY z d k =
        if k = m then selbergY z d m else 0 := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have hk_pos : 1 ≤ k := by
      simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hk; omega
    have hm_pos : 1 ≤ m := by
      simp only [selbergS, Finset.mem_filter, Finset.mem_Icc] at hm; omega
    have hkm_pos : 1 ≤ k / m := Nat.div_pos (Nat.le_of_dvd hk_pos hk.2) hm_pos
    have hbij : ∑ r ∈ k.divisors.filter (m ∣ ·), (ArithmeticFunction.moebius (k / r) : ℝ) =
        ∑ t ∈ (k / m).divisors, (ArithmeticFunction.moebius t : ℝ) := by
      refine Finset.sum_bij (fun r _ => k / r) ?_ ?_ ?_ ?_
      · intro r hr
        rw [Finset.mem_filter, Nat.mem_divisors] at hr
        rw [Nat.mem_divisors]
        refine ⟨?_, by omega⟩
        obtain ⟨q, rfl⟩ := hr.2
        obtain ⟨t, ht⟩ := hr.1.1
        have h1 : k / (m * q) = t := by
          rw [ht]
          exact Nat.mul_div_right t (Nat.pos_of_dvd_of_pos hr.1.1 hk_pos)
        have h2 : k / m = q * t := by
          rw [ht, mul_assoc]
          exact Nat.mul_div_right (q * t) hm_pos
        rw [h1, h2]; exact dvd_mul_left t q
      · intro r1 hr1 r2 hr2 heq
        rw [Finset.mem_filter, Nat.mem_divisors] at hr1 hr2
        have h1 := Nat.div_mul_cancel hr1.1.1
        have h2 := Nat.div_mul_cancel hr2.1.1
        rw [heq] at h1
        have hpos : 0 < k / r2 := Nat.div_pos (Nat.le_of_dvd hk_pos hr2.1.1)
          (Nat.pos_of_dvd_of_pos hr2.1.1 hk_pos)
        exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
      · intro t ht
        rw [Nat.mem_divisors] at ht
        have ht_pos : 0 < t := Nat.pos_of_dvd_of_pos ht.1 hkm_pos
        have ht_dvd_k : t ∣ k := ht.1.trans (Nat.div_dvd_of_dvd hk.2)
        refine ⟨k / t, ?_, Nat.div_div_self ht_dvd_k (by omega)⟩
        rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨Nat.div_dvd_of_dvd ht_dvd_k, by omega⟩, ?_⟩
        obtain ⟨u, hu⟩ := ht.1
        have hk_eq : k = m * (t * u) := by
          have := Nat.mul_div_cancel' hk.2
          rw [hu] at this; exact this.symm
        have : k / t = m * u := by
          rw [hk_eq, mul_left_comm]
          exact Nat.mul_div_right (m * u) ht_pos
        rw [this]; exact dvd_mul_right m u
      · intro _ _; rfl
    rw [hbij, sum_moebius_divisors_eq_ite (k / m) hkm_pos]
    have hiff : k / m = 1 ↔ k = m := by
      constructor
      · intro h
        have := Nat.mul_div_cancel' hk.2
        rw [h, mul_one] at this; exact this.symm
      · rintro rfl; exact Nat.div_self hm_pos
    simp only [hiff]
    split_ifs with heq
    · subst heq; simp
    · simp
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
  have hmm : m ∈ S.filter (m ∣ ·) := Finset.mem_filter.mpr ⟨hm, dvd_refl m⟩
  simp [hmm]

private lemma selberg_quad_form {z d : ℕ} (hz : 1 ≤ z) :
    ∑ r1 ∈ selbergS z d, ∑ r2 ∈ selbergS z d,
      selbergLam z d r1 * selbergLam z d r2 / (Nat.lcm r1 r2 : ℝ) = 1 / selbergG z d := by
  let S := selbergS z d
  have hG_pos : 0 < selbergG z d := lt_of_lt_of_le zero_lt_one (selbergG_ge_one hz)
  have hterm : ∀ r1 ∈ S, ∀ r2 ∈ S,
      selbergLam z d r1 * selbergLam z d r2 / (Nat.lcm r1 r2 : ℝ) =
        ∑ m ∈ S, if m ∣ r1 ∧ m ∣ r2 then
          (Nat.totient m : ℝ) * (selbergLam z d r1 / (r1 : ℝ)) *
            (selbergLam z d r2 / (r2 : ℝ)) else 0 := by
    intro r1 hr1 r2 hr2
    have hr1_pos : (0 : ℝ) < r1 := by
      simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hr1
      exact_mod_cast (by omega : 0 < r1)
    have hr2_pos : (0 : ℝ) < r2 := by
      simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hr2
      exact_mod_cast (by omega : 0 < r2)
    have hlcm : (Nat.gcd r1 r2 : ℝ) * (Nat.lcm r1 r2 : ℝ) = (r1 : ℝ) * (r2 : ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm r1 r2
    have hlcm_pos : (0 : ℝ) < Nat.lcm r1 r2 := by
      have h1 : 0 < r1 := by simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hr1; omega
      have h2 : 0 < r2 := by simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hr2; omega
      exact_mod_cast Nat.lcm_pos h1 h2
    have htot : (Nat.gcd r1 r2 : ℝ) = ∑ m ∈ (Nat.gcd r1 r2).divisors, (Nat.totient m : ℝ) := by
      exact_mod_cast (Nat.sum_totient (Nat.gcd r1 r2)).symm
    rw [← Finset.sum_filter]
    have hfilt : S.filter (fun m => m ∣ r1 ∧ m ∣ r2) = (Nat.gcd r1 r2).divisors := by
      ext m
      simp only [Finset.mem_filter, Nat.mem_divisors]
      have hgcd_ne : Nat.gcd r1 r2 ≠ 0 := by
        have h1 : 0 < r1 := by simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hr1; omega
        exact (Nat.gcd_pos_of_pos_left r2 h1).ne'
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨Nat.dvd_gcd h1 h2, hgcd_ne⟩
      · rintro ⟨hdvd, _⟩
        have h1 : m ∣ r1 := hdvd.trans (Nat.gcd_dvd_left r1 r2)
        have h2 : m ∣ r2 := hdvd.trans (Nat.gcd_dvd_right r1 r2)
        exact ⟨selbergS_dvd_closed hr1 h1, h1, h2⟩
    rw [hfilt, ← Finset.sum_mul, ← Finset.sum_mul, ← htot]
    field_simp [hr1_pos.ne', hr2_pos.ne', hlcm_pos.ne']
    calc selbergLam z d r1 * selbergLam z d r2 * (r1 : ℝ) * (r2 : ℝ)
        = selbergLam z d r1 * selbergLam z d r2 * ((r1 : ℝ) * (r2 : ℝ)) := by ring
      _ = selbergLam z d r1 * selbergLam z d r2 * ((Nat.gcd r1 r2 : ℝ) * (Nat.lcm r1 r2 : ℝ)) := by
          rw [hlcm]
      _ = selbergLam z d r1 * selbergLam z d r2 * (Nat.lcm r1 r2 : ℝ) * (Nat.gcd r1 r2 : ℝ) := by
          ring
  have htriple : ∑ r1 ∈ S, ∑ r2 ∈ S, ∑ m ∈ S,
        (if m ∣ r1 ∧ m ∣ r2 then
          (Nat.totient m : ℝ) * (selbergLam z d r1 / (r1 : ℝ)) *
            (selbergLam z d r2 / (r2 : ℝ)) else 0) =
      ∑ m ∈ S, (Nat.totient m : ℝ) *
        (∑ r1 ∈ S.filter (m ∣ ·), selbergLam z d r1 / (r1 : ℝ)) *
        (∑ r2 ∈ S.filter (m ∣ ·), selbergLam z d r2 / (r2 : ℝ)) := by
    have hswap1 : ∑ r1 ∈ S, ∑ r2 ∈ S, ∑ m ∈ S,
          (if m ∣ r1 ∧ m ∣ r2 then
            (Nat.totient m : ℝ) * (selbergLam z d r1 / (r1 : ℝ)) *
              (selbergLam z d r2 / (r2 : ℝ)) else 0) =
        ∑ m ∈ S, ∑ r1 ∈ S, ∑ r2 ∈ S,
          (if m ∣ r1 ∧ m ∣ r2 then
            (Nat.totient m : ℝ) * (selbergLam z d r1 / (r1 : ℝ)) *
              (selbergLam z d r2 / (r2 : ℝ)) else 0) := by
      trans ∑ r1 ∈ S, ∑ m ∈ S, ∑ r2 ∈ S,
          (if m ∣ r1 ∧ m ∣ r2 then
            (Nat.totient m : ℝ) * (selbergLam z d r1 / (r1 : ℝ)) *
              (selbergLam z d r2 / (r2 : ℝ)) else 0)
      · refine Finset.sum_congr rfl fun r1 _ => Finset.sum_comm
      · exact Finset.sum_comm
    rw [hswap1]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hfactor : ∀ r1 ∈ S,
        (∑ r2 ∈ S, if m ∣ r1 ∧ m ∣ r2 then
          (Nat.totient m : ℝ) * (selbergLam z d r1 / (r1 : ℝ)) *
            (selbergLam z d r2 / (r2 : ℝ)) else 0) =
        if m ∣ r1 then
          ((Nat.totient m : ℝ) * (selbergLam z d r1 / (r1 : ℝ))) *
            (∑ r2 ∈ S.filter (m ∣ ·), selbergLam z d r2 / (r2 : ℝ))
        else 0 := by
      intro r1 _
      split_ifs with h1
      · rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun r2 _ => by simp [h1]
      · simp [h1]
    rw [Finset.sum_congr rfl hfactor, ← Finset.sum_filter, ← Finset.sum_mul, ← Finset.mul_sum]
  calc ∑ r1 ∈ S, ∑ r2 ∈ S, selbergLam z d r1 * selbergLam z d r2 / (Nat.lcm r1 r2 : ℝ)
      = ∑ r1 ∈ S, ∑ r2 ∈ S, ∑ m ∈ S,
          (if m ∣ r1 ∧ m ∣ r2 then
            (Nat.totient m : ℝ) * (selbergLam z d r1 / (r1 : ℝ)) *
              (selbergLam z d r2 / (r2 : ℝ)) else 0) :=
        Finset.sum_congr rfl fun r1 hr1 => Finset.sum_congr rfl fun r2 hr2 => hterm r1 hr1 r2 hr2
    _ = ∑ m ∈ S, (Nat.totient m : ℝ) *
          (∑ r1 ∈ S.filter (m ∣ ·), selbergLam z d r1 / (r1 : ℝ)) *
          (∑ r2 ∈ S.filter (m ∣ ·), selbergLam z d r2 / (r2 : ℝ)) := htriple
    _ = ∑ m ∈ S, (Nat.totient m : ℝ) * selbergY z d m * selbergY z d m :=
        Finset.sum_congr rfl fun m hm => by rw [selbergLam_inv hm]
    _ = 1 / selbergG z d := by
        have h1 : ∀ m ∈ S, (Nat.totient m : ℝ) * selbergY z d m * selbergY z d m =
            (1 / (selbergG z d ^ 2)) * ((1 : ℝ) / (Nat.totient m : ℝ)) := by
          intro m hm
          have hmS : m ∈ selbergS z d := hm
          simp only [selbergY, hmS, ↓reduceIte]
          have hsq := moebius_sq_of_mem_selbergS hm
          have hphi_ne : (Nat.totient m : ℝ) ≠ 0 := by
            simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hm
            exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
          field_simp [hphi_ne, hG_pos.ne']
          linarith
        rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
        change (1 / selbergG z d ^ 2) * selbergG z d = 1 / selbergG z d
        field_simp [hG_pos.ne']

private lemma selbergLam_abs_le_one {z d r : ℕ} (hz : 1 ≤ z) (hr : r ∈ selbergS z d) :
    |selbergLam z d r| ≤ 1 := by
  let S := selbergS z d
  have hG_pos : 0 < selbergG z d := lt_of_lt_of_le zero_lt_one (selbergG_ge_one hz)
  have hr_info := hr
  simp only [selbergS, Finset.mem_filter, Finset.mem_Icc] at hr_info
  have hr_pos : 1 ≤ r := hr_info.1.1
  have hr_sq : Squarefree r := hr_info.2.1
  have hr_cop : Nat.Coprime r d := hr_info.2.2
  let Kr := (Finset.Icc 1 (z / r)).filter (fun k => Squarefree k ∧ Nat.Coprime k (r * d))
  have hlam_eq : selbergLam z d r = ((ArithmeticFunction.moebius r : ℝ) / selbergG z d) *
      ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ k ∈ Kr, (1 : ℝ) / (Nat.totient k : ℝ) := by
    simp only [selbergLam, hr, ↓reduceIte]
    have hbij : ∑ m ∈ S.filter (r ∣ ·), (ArithmeticFunction.moebius (m / r) : ℝ) * selbergY z d m =
        ((ArithmeticFunction.moebius r : ℝ) / ((Nat.totient r : ℝ) * selbergG z d)) *
          ∑ k ∈ Kr, (1 : ℝ) / (Nat.totient k : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun m _ => m / r) ?_ ?_ ?_ ?_
      · intro m hm
        rw [Finset.mem_filter] at hm
        have hm_info := hm.1
        simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hm_info
        simp only [Kr, Finset.mem_filter, Finset.mem_Icc]
        have hmul : r * (m / r) = m := Nat.mul_div_cancel' hm.2
        have hk_pos : 1 ≤ m / r := Nat.div_pos (Nat.le_of_dvd (by omega) hm.2) hr_pos
        have hk_le : m / r ≤ z / r := Nat.div_le_div_right hm_info.1.2
        have hsq_rk : Squarefree (r * (m / r)) := hmul.symm ▸ hm_info.2.1
        have hcop_rk : Nat.Coprime r (m / r) := (Nat.squarefree_mul_iff.mp hsq_rk).1
        have hsq_k : Squarefree (m / r) := (Nat.squarefree_mul_iff.mp hsq_rk).2.2
        have hcop_kd : Nat.Coprime (m / r) d := hm_info.2.2.coprime_dvd_left (Nat.div_dvd_of_dvd hm.2)
        exact ⟨⟨hk_pos, hk_le⟩, hsq_k, hcop_rk.symm.mul_right hcop_kd⟩
      · intro m1 hm1 m2 hm2 heq
        rw [Finset.mem_filter] at hm1 hm2
        rw [← Nat.mul_div_cancel' hm1.2, ← Nat.mul_div_cancel' hm2.2, heq]
      · intro k hk
        simp only [Kr, Finset.mem_filter, Finset.mem_Icc] at hk
        have hcop_rk : Nat.Coprime r k := (Nat.coprime_mul_iff_right.mp hk.2.2).1.symm
        have hcop_kd : Nat.Coprime k d := (Nat.coprime_mul_iff_right.mp hk.2.2).2
        refine ⟨r * k, ?_, Nat.mul_div_right k hr_pos⟩
        rw [Finset.mem_filter]
        refine ⟨?_, dvd_mul_right r k⟩
        simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.mul_pos hr_pos hk.1.1, ?_⟩,
          Nat.squarefree_mul_iff.mpr ⟨hcop_rk, hr_sq, hk.2.1⟩, hr_cop.mul_left hcop_kd⟩
        calc r * k ≤ r * (z / r) := Nat.mul_le_mul_left r hk.1.2
          _ ≤ z := Nat.mul_div_le z r
      · intro m hm
        rw [Finset.mem_filter] at hm
        have hmS : m ∈ S := hm.1
        have hmul : r * (m / r) = m := Nat.mul_div_cancel' hm.2
        have hm_sq : Squarefree m := (Finset.mem_filter.mp hmS).2.1
        have hcop_rk : Nat.Coprime r (m / r) :=
          (Nat.squarefree_mul_iff.mp (hmul.symm ▸ hm_sq)).1
        have hk_sq : Squarefree (m / r) :=
          (Nat.squarefree_mul_iff.mp (hmul.symm ▸ hm_sq)).2.2
        have hmu_mul : (ArithmeticFunction.moebius m : ℝ) =
            (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius (m / r) : ℝ) := by
          conv_lhs => rw [← hmul]
          exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_rk
        have hmu_k_sq : ((ArithmeticFunction.moebius (m / r) : ℝ)) ^ 2 = 1 := by
          rw [ArithmeticFunction.moebius_apply_of_squarefree hk_sq]
          push_cast
          rw [← pow_mul, mul_comm, pow_mul]
          simp
        have hphi_mul : (Nat.totient m : ℝ) = (Nat.totient r : ℝ) * (Nat.totient (m / r) : ℝ) := by
          conv_lhs => rw [← hmul]
          exact_mod_cast Nat.totient_mul hcop_rk
        have hmS' : m ∈ selbergS z d := hm.1
        simp only [selbergY, hmS', ↓reduceIte, hmu_mul, hphi_mul]
        have hphi_r_ne : (Nat.totient r : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr hr_pos).ne'
        have hphi_k_ne : (Nat.totient (m / r) : ℝ) ≠ 0 := by
          have hk_pos : 1 ≤ m / r := by
            simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hmS
            exact Nat.div_pos (Nat.le_of_dvd (by omega) hm.2) hr_pos
          exact_mod_cast (Nat.totient_pos.mpr hk_pos).ne'
        field_simp [hphi_r_ne, hphi_k_ne, hG_pos.ne']
        nlinarith [hmu_k_sq]
    rw [hbij]
    ring
  have hprod_le_G : ((r : ℝ) / (Nat.totient r : ℝ)) *
      ∑ k ∈ Kr, (1 : ℝ) / (Nat.totient k : ℝ) ≤ selbergG z d := by
    rw [squarefree_div_totient_eq_sum_divisors r hr_sq]
    have hmul_sum : (∑ u ∈ r.divisors, (1 : ℝ) / (Nat.totient u : ℝ)) *
        (∑ k ∈ Kr, (1 : ℝ) / (Nat.totient k : ℝ)) =
        ∑ x ∈ r.divisors ×ˢ Kr, (1 : ℝ) / (Nat.totient (x.1 * x.2) : ℝ) := by
      simp only [Finset.sum_product]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Nat.mem_divisors] at hu
      simp only [Kr, Finset.mem_filter] at hk
      have hcop_kr : Nat.Coprime k r := (Nat.coprime_mul_iff_right.mp hk.2.2).1
      have hcop_uk : Nat.Coprime u k := hcop_kr.symm.coprime_dvd_left hu.1
      rw [Nat.totient_mul hcop_uk]
      push_cast
      ring
    rw [hmul_sum]
    have hmaps : ∀ x ∈ r.divisors ×ˢ Kr, x.1 * x.2 ∈ S := by
      intro x hx
      rw [Finset.mem_product, Nat.mem_divisors] at hx
      simp only [Kr, Finset.mem_filter, Finset.mem_Icc] at hx
      simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc]
      have hu_pos : 1 ≤ x.1 := Nat.pos_of_dvd_of_pos hx.1.1 hr_pos
      have hu_le : x.1 ≤ r := Nat.le_of_dvd hr_pos hx.1.1
      have hcop_kr : Nat.Coprime x.2 r := (Nat.coprime_mul_iff_right.mp hx.2.2.2).1
      have hcop_kd : Nat.Coprime x.2 d := (Nat.coprime_mul_iff_right.mp hx.2.2.2).2
      have hcop_uk : Nat.Coprime x.1 x.2 := hcop_kr.symm.coprime_dvd_left hx.1.1
      have hle_z : x.1 * x.2 ≤ z := by
        calc x.1 * x.2 ≤ r * (z / r) := Nat.mul_le_mul hu_le hx.2.1.2
          _ ≤ z := Nat.mul_div_le z r
      exact ⟨⟨Nat.mul_pos hu_pos hx.2.1.1, hle_z⟩,
        Nat.squarefree_mul_iff.mpr ⟨hcop_uk, hr_sq.squarefree_of_dvd hx.1.1, hx.2.2.1⟩,
        (hr_cop.coprime_dvd_left hx.1.1).mul_left hcop_kd⟩
    have hinj : ∀ x1 ∈ r.divisors ×ˢ Kr, ∀ x2 ∈ r.divisors ×ˢ Kr,
        x1.1 * x1.2 = x2.1 * x2.2 → x1 = x2 := by
      intro x1 hx1 x2 hx2 heq
      rw [Finset.mem_product, Nat.mem_divisors] at hx1 hx2
      simp only [Kr, Finset.mem_filter] at hx1 hx2
      have hg1 : Nat.gcd (x1.1 * x1.2) r = x1.1 := by
        have hcop : Nat.Coprime x1.2 r := (Nat.coprime_mul_iff_right.mp hx1.2.2.2).1
        rw [hcop.gcd_mul_right_cancel, Nat.gcd_eq_left hx1.1.1]
      have hg2 : Nat.gcd (x2.1 * x2.2) r = x2.1 := by
        have hcop : Nat.Coprime x2.2 r := (Nat.coprime_mul_iff_right.mp hx2.2.2.2).1
        rw [hcop.gcd_mul_right_cancel, Nat.gcd_eq_left hx2.1.1]
      have h1 : x1.1 = x2.1 := by rw [← hg1, ← hg2, heq]
      have hx1_pos : 0 < x1.1 := Nat.pos_of_dvd_of_pos hx1.1.1 hr_pos
      have h2 : x1.2 = x2.2 := Nat.eq_of_mul_eq_mul_left hx1_pos (h1 ▸ heq)
      exact Prod.ext h1 h2
    calc ∑ x ∈ r.divisors ×ˢ Kr, (1 : ℝ) / (Nat.totient (x.1 * x.2) : ℝ)
        = ∑ m ∈ (r.divisors ×ˢ Kr).image (fun x => x.1 * x.2),
            (1 : ℝ) / (Nat.totient m : ℝ) :=
          (Finset.sum_image (f := fun m => (1 : ℝ) / (Nat.totient m : ℝ))
            (fun a ha b hb h => hinj a ha b hb h)).symm
      _ ≤ selbergG z d := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr hmaps) (fun _ _ _ => by positivity)
  rw [hlam_eq, abs_mul, abs_mul, abs_div]
  have hmu_abs : |(ArithmeticFunction.moebius r : ℝ)| = 1 := by
    have hsq := moebius_sq_of_mem_selbergS hr
    nlinarith [sq_abs (ArithmeticFunction.moebius r : ℝ), abs_nonneg (ArithmeticFunction.moebius r : ℝ)]
  have hnn1 : 0 ≤ (r : ℝ) / (Nat.totient r : ℝ) := by positivity
  have hnn2 : 0 ≤ ∑ k ∈ Kr, (1 : ℝ) / (Nat.totient k : ℝ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [hmu_abs, abs_of_pos hG_pos, abs_of_nonneg hnn1, abs_of_nonneg hnn2]
  calc 1 / selbergG z d * ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ k ∈ Kr, (1 : ℝ) / (Nat.totient k : ℝ)
      = (1 / selbergG z d) *
          (((r : ℝ) / (Nat.totient r : ℝ)) * ∑ k ∈ Kr, (1 : ℝ) / (Nat.totient k : ℝ)) := by ring
    _ ≤ (1 / selbergG z d) * selbergG z d := by gcongr
    _ = 1 := by field_simp [hG_pos.ne']

/-- Explicit Brun-Titchmarsh inequality via Selberg upper bound sieve. -/
private theorem brun_titchmarsh (X : ℝ) (d a : ℕ) (hd : 1 ≤ d) (hXd : 8 * (d : ℝ) ≤ X) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % d = a % d)).card : ℝ) ≤
      9 * X / ((Nat.totient d : ℝ) * Real.log (X / (d : ℝ))) := by
  have hd_pos : (0 : ℝ) < d := by positivity
  have hX_pos : 0 < X := by linarith
  have hXd_ge8 : 8 ≤ X / (d : ℝ) := (le_div_iff₀ hd_pos).mpr hXd
  have hphi_pos : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hphi_le : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have hlogXd : 0 < Real.log (X / (d : ℝ)) := Real.log_pos (by linarith)
  let zr : ℝ := (X / (d : ℝ)) ^ ((1 : ℝ) / 3)
  have hzr_ge2 : 2 ≤ zr := by
    have h8 : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h8]
    exact Real.rpow_le_rpow (by norm_num) hXd_ge8 (by norm_num)
  let z : ℕ := ⌊zr⌋₊
  have hz2 : 2 ≤ z := (Nat.le_floor_iff (by linarith)).mpr hzr_ge2
  have hz1 : 1 ≤ z := by omega
  have hz_le : (z : ℝ) ≤ zr := Nat.floor_le (by linarith)
  have hzr_lt : zr < ((z + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one zr
  have hlogz : (1 / 3 : ℝ) * Real.log (X / (d : ℝ)) ≤ Real.log ((z + 1 : ℕ) : ℝ) := by
    have h1 : Real.log zr = (1 / 3 : ℝ) * Real.log (X / (d : ℝ)) := by
      dsimp only [zr]
      rw [Real.log_rpow (by linarith)]
    rw [← h1]
    exact Real.log_le_log (by linarith) hzr_lt.le
  let S := selbergS z d
  let G := selbergG z d
  let lam := selbergLam z d
  have h1S : 1 ∈ S := one_mem_selbergS hz1
  have hG_lb : ((Nat.totient d : ℝ) / (d : ℝ)) * ((1 / 3 : ℝ) * Real.log (X / (d : ℝ))) ≤ G := by
    have h1 := selberg_G_lower_bound z d hz1 hd
    have h2 : (1 / 3 : ℝ) * Real.log (X / (d : ℝ)) ≤ ((d : ℝ) / (Nat.totient d : ℝ)) * G :=
      hlogz.trans h1
    calc ((Nat.totient d : ℝ) / (d : ℝ)) * ((1 / 3 : ℝ) * Real.log (X / (d : ℝ)))
        ≤ ((Nat.totient d : ℝ) / (d : ℝ)) * (((d : ℝ) / (Nat.totient d : ℝ)) * G) := by gcongr
      _ = G := by field_simp [hd_pos.ne', hphi_pos.ne']
  let Aset := (Finset.Icc 1 ⌊X⌋₊).filter (fun n => n % d = a % d)
  let P_all := (Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % d = a % d)
  let P_lo := P_all.filter (fun p => p ≤ z)
  let P_hi := P_all.filter (fun p => z < p)
  have hP_split : P_all.card ≤ P_lo.card + P_hi.card := by
    have hunion : P_all ⊆ P_lo ∪ P_hi := by
      intro p hp
      rw [Finset.mem_union]
      by_cases hle : p ≤ z
      · exact Or.inl (Finset.mem_filter.mpr ⟨hp, hle⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hp, not_le.mp hle⟩)
    exact (Finset.card_le_card hunion).trans (Finset.card_union_le _ _)
  have hPlo_le : (P_lo.card : ℝ) ≤ (z : ℝ) := by
    have hsub : P_lo ⊆ Finset.Icc 1 z := by
      intro p hp
      simp only [P_lo, P_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨hp.1.1.1, hp.2⟩
    have hle : P_lo.card ≤ z := (Finset.card_le_card hsub).trans (by simp)
    exact_mod_cast hle
  have hPhi_le : (P_hi.card : ℝ) ≤ ∑ n ∈ Aset, (∑ r ∈ S.filter (· ∣ n), lam r) ^ 2 := by
    have hsub : P_hi ⊆ Aset := by
      intro p hp
      simp only [P_hi, P_all, Aset, Finset.mem_filter] at hp ⊢
      exact ⟨hp.1.1, hp.1.2.2⟩
    have hone : ∀ p ∈ P_hi, (1 : ℝ) ≤ (∑ r ∈ S.filter (· ∣ p), lam r) ^ 2 := by
      intro p hp
      simp only [P_hi, P_all, Finset.mem_filter] at hp
      have hfilt : S.filter (· ∣ p) = {1} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hrS, hrp⟩
          rcases (Nat.dvd_prime hp.1.2.1).mp hrp with rfl | rfl
          · rfl
          · exfalso
            simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hrS
            omega
        · rintro rfl
          exact ⟨h1S, one_dvd p⟩
      rw [hfilt, Finset.sum_singleton]
      dsimp only [lam]
      rw [selbergLam_one hz1]
      norm_num
    calc (P_hi.card : ℝ) = ∑ _p ∈ P_hi, (1 : ℝ) := by simp
      _ ≤ ∑ p ∈ P_hi, (∑ r ∈ S.filter (· ∣ p), lam r) ^ 2 := Finset.sum_le_sum hone
      _ ≤ ∑ n ∈ Aset, (∑ r ∈ S.filter (· ∣ n), lam r) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hexpand : ∑ n ∈ Aset, (∑ r ∈ S.filter (· ∣ n), lam r) ^ 2 =
      ∑ r1 ∈ S, ∑ r2 ∈ S, lam r1 * lam r2 *
        (((Aset.filter (fun n => Nat.lcm r1 r2 ∣ n)).card : ℝ)) := by
    have hsq_sum : ∀ n ∈ Aset, (∑ r ∈ S.filter (· ∣ n), lam r) ^ 2 =
        ∑ r1 ∈ S, ∑ r2 ∈ S, if Nat.lcm r1 r2 ∣ n then lam r1 * lam r2 else 0 := by
      intro n _
      rw [sq, Finset.sum_mul]
      trans ∑ r1 ∈ S, ∑ r2 ∈ S, if r1 ∣ n ∧ r2 ∣ n then lam r1 * lam r2 else 0
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun r1 _ => ?_
        split_ifs with h1
        · rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun r2 _ => by simp [h1]
        · simp [h1]
      · refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => ?_
        simp [Nat.lcm_dvd_iff]
    rw [Finset.sum_congr rfl hsq_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r2 _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsieve_bd : ∑ n ∈ Aset, (∑ r ∈ S.filter (· ∣ n), lam r) ^ 2 ≤
      (X / (d : ℝ)) * (1 / G) + (z : ℝ) ^ 2 := by
    rw [hexpand]
    have hdiff : ∀ r1 ∈ S, ∀ r2 ∈ S,
        lam r1 * lam r2 * (((Aset.filter (fun n => Nat.lcm r1 r2 ∣ n)).card : ℝ)) ≤
          (X / (d : ℝ)) * (lam r1 * lam r2 / (Nat.lcm r1 r2 : ℝ)) + |lam r1| * |lam r2| := by
      intro r1 hr1 r2 hr2
      have hL_pos : 1 ≤ Nat.lcm r1 r2 := by
        simp only [S, selbergS, Finset.mem_filter, Finset.mem_Icc] at hr1 hr2
        exact Nat.lcm_pos (by omega) (by omega)
      have hcop_L : Nat.Coprime (Nat.lcm r1 r2) d := by
        simp only [S, selbergS, Finset.mem_filter] at hr1 hr2
        exact (hr1.2.2.mul_left hr2.2.2).coprime_dvd_left (Nat.lcm_dvd_mul r1 r2)
      have hfilt_eq : Aset.filter (fun n => Nat.lcm r1 r2 ∣ n) =
          (Finset.Icc 1 ⌊X⌋₊).filter (fun n => n % d = a % d ∧ Nat.lcm r1 r2 ∣ n) := by
        ext n; simp only [Aset, Finset.mem_filter]; tauto
      have happ := count_ap_dvd_approx X d a (Nat.lcm r1 r2) hX_pos.le hd hL_pos hcop_L
      rw [← hfilt_eq] at happ
      have hcast : X / ((d * Nat.lcm r1 r2 : ℕ) : ℝ) = (X / (d : ℝ)) / (Nat.lcm r1 r2 : ℝ) := by
        push_cast; ring
      rw [hcast] at happ
      set c := ((Aset.filter (fun n => Nat.lcm r1 r2 ∣ n)).card : ℝ)
      set m := (X / (d : ℝ)) / (Nat.lcm r1 r2 : ℝ)
      have h1 : lam r1 * lam r2 * (c - m) ≤ |lam r1 * lam r2| * |c - m| := by
        calc lam r1 * lam r2 * (c - m) ≤ |lam r1 * lam r2 * (c - m)| := le_abs_self _
          _ = |lam r1 * lam r2| * |c - m| := abs_mul _ _
      have h2 : |lam r1 * lam r2| * |c - m| ≤ |lam r1| * |lam r2| := by
        rw [abs_mul]
        calc |lam r1| * |lam r2| * |c - m| ≤ |lam r1| * |lam r2| * 1 := by gcongr
          _ = |lam r1| * |lam r2| := mul_one _
      have hrew : (X / (d : ℝ)) * (lam r1 * lam r2 / (Nat.lcm r1 r2 : ℝ)) = lam r1 * lam r2 * m := by
        dsimp only [m]; ring
      linarith
    have hsum_abs : ∑ r1 ∈ S, ∑ r2 ∈ S, |lam r1| * |lam r2| ≤ (z : ℝ) ^ 2 := by
      have h1 : ∑ r1 ∈ S, ∑ r2 ∈ S, |lam r1| * |lam r2| = (∑ r ∈ S, |lam r|) ^ 2 := by
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun r1 _ => (Finset.mul_sum ..).symm
      rw [h1]
      have h2 : ∑ r ∈ S, |lam r| ≤ (z : ℝ) := by
        calc ∑ r ∈ S, |lam r| ≤ ∑ _r ∈ S, (1 : ℝ) :=
              Finset.sum_le_sum fun r hr => selbergLam_abs_le_one hz1 hr
          _ = (S.card : ℝ) := by simp
          _ ≤ (z : ℝ) := by
            have : S.card ≤ z := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
            exact_mod_cast this
      nlinarith [Finset.sum_nonneg (s := S) (f := fun r => |lam r|) (fun _ _ => abs_nonneg _)]
    calc ∑ r1 ∈ S, ∑ r2 ∈ S, lam r1 * lam r2 *
            (((Aset.filter (fun n => Nat.lcm r1 r2 ∣ n)).card : ℝ))
        ≤ ∑ r1 ∈ S, ∑ r2 ∈ S,
            ((X / (d : ℝ)) * (lam r1 * lam r2 / (Nat.lcm r1 r2 : ℝ)) + |lam r1| * |lam r2|) :=
          Finset.sum_le_sum fun r1 hr1 => Finset.sum_le_sum fun r2 hr2 => hdiff r1 hr1 r2 hr2
      _ = (X / (d : ℝ)) * (∑ r1 ∈ S, ∑ r2 ∈ S, lam r1 * lam r2 / (Nat.lcm r1 r2 : ℝ)) +
            ∑ r1 ∈ S, ∑ r2 ∈ S, |lam r1| * |lam r2| := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (X / (d : ℝ)) * (1 / G) + (z : ℝ) ^ 2 := by
          rw [selberg_quad_form hz1]; linarith
  have hmain_bd : (X / (d : ℝ)) * (1 / G) ≤ 3 * X / ((Nat.totient d : ℝ) * Real.log (X / (d : ℝ))) := by
    have h1 : 1 / G ≤ 1 / (((Nat.totient d : ℝ) / (d : ℝ)) * ((1 / 3 : ℝ) * Real.log (X / (d : ℝ)))) :=
      one_div_le_one_div_of_le (by positivity) hG_lb
    calc (X / (d : ℝ)) * (1 / G)
        ≤ (X / (d : ℝ)) * (1 / (((Nat.totient d : ℝ) / (d : ℝ)) * ((1 / 3 : ℝ) * Real.log (X / (d : ℝ))))) := by
          gcongr
      _ = 3 * X / ((Nat.totient d : ℝ) * Real.log (X / (d : ℝ))) := by
          field_simp [hd_pos.ne', hphi_pos.ne', hlogXd.ne']
  have herr_bd : (z : ℝ) + (z : ℝ) ^ 2 ≤ 6 * X / ((Nat.totient d : ℝ) * Real.log (X / (d : ℝ))) := by
    have hzr3 : zr ^ 3 = X / (d : ℝ) := by
      dsimp only [zr]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    have hlog_zr : Real.log (X / (d : ℝ)) ≤ 3 * zr := by
      have h1 : Real.log zr ≤ zr := log_le_self_of_pos (by linarith)
      have h2 : Real.log (X / (d : ℝ)) = 3 * Real.log zr := by
        rw [← hzr3, Real.log_pow]; norm_num
      linarith
    have hz_sq : (z : ℝ) + (z : ℝ) ^ 2 ≤ 2 * zr ^ 2 := by nlinarith
    have h2zr2 : 2 * zr ^ 2 ≤ 6 * (X / (d : ℝ)) / Real.log (X / (d : ℝ)) := by
      rw [le_div_iff₀ hlogXd]
      nlinarith [sq_nonneg zr]
    have hphi_div : 6 * (X / (d : ℝ)) / Real.log (X / (d : ℝ)) ≤
        6 * X / ((Nat.totient d : ℝ) * Real.log (X / (d : ℝ))) := by
      rw [show 6 * (X / (d : ℝ)) / Real.log (X / (d : ℝ)) =
          6 * X / ((d : ℝ) * Real.log (X / (d : ℝ))) by ring]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    linarith
  have hP_all : (P_all.card : ℝ) ≤ (P_lo.card : ℝ) + (P_hi.card : ℝ) := by exact_mod_cast hP_split
  have h9 : 3 * X / ((Nat.totient d : ℝ) * Real.log (X / (d : ℝ))) +
      6 * X / ((Nat.totient d : ℝ) * Real.log (X / (d : ℝ))) =
      9 * X / ((Nat.totient d : ℝ) * Real.log (X / (d : ℝ))) := by ring
  linarith

/- ## Section 3: Exceptional Set Bounds -/

private def maxPrimeFactor (n : ℕ) : ℕ := n.primeFactors.sup id

private lemma maxPrimeFactor_mem {n : ℕ} (hn : 2 ≤ n) :
    maxPrimeFactor n ∈ n.primeFactors := by
  have hne : n.primeFactors.Nonempty := by
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by omega⟩⟩
  obtain ⟨m, hm, hsup⟩ := Finset.exists_mem_eq_sup n.primeFactors hne id
  dsimp only [maxPrimeFactor]
  rw [hsup]
  exact hm

private lemma maxPrimeFactor_prime {n : ℕ} (hn : 2 ≤ n) : (maxPrimeFactor n).Prime :=
  Nat.prime_of_mem_primeFactors (maxPrimeFactor_mem hn)

private lemma maxPrimeFactor_dvd {n : ℕ} (hn : 2 ≤ n) : maxPrimeFactor n ∣ n :=
  Nat.dvd_of_mem_primeFactors (maxPrimeFactor_mem hn)

private lemma le_maxPrimeFactor {n p : ℕ} (hp : p ∈ n.primeFactors) : p ≤ maxPrimeFactor n :=
  Finset.le_sup (f := id) hp

private lemma maxPrimeFactor_le_self (n : ℕ) : maxPrimeFactor n ≤ n := by
  by_cases hn : 2 ≤ n
  · exact Nat.le_of_dvd (by omega) (maxPrimeFactor_dvd hn)
  · have h : n = 0 ∨ n = 1 := by omega
    rcases h with rfl | rfl <;> simp [maxPrimeFactor]

private noncomputable def E_A (N : ℕ) (y : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => (maxPrimeFactor n : ℝ) ≤ y)

private noncomputable def E_B (N : ℕ) (y : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => y < (maxPrimeFactor n : ℝ) ∧ (maxPrimeFactor n) ^ 2 ∣ n)

private noncomputable def E_F (N y0 : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => ∃ q : ℕ, q.Prime ∧ y0 < q ∧ q ∣ n ∧ q ∣ σ 1 n)

private noncomputable def Good (N : ℕ) (y_smooth : ℝ) (y0 : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n =>
    y_smooth < (maxPrimeFactor n : ℝ) ∧
    ¬ (maxPrimeFactor n) ^ 2 ∣ n ∧
    ¬ ∃ q : ℕ, q.Prime ∧ y0 < q ∧ q ∣ n ∧ q ∣ σ 1 n)

private lemma Icc_subset_good_union_exc (N : ℕ) (y_smooth : ℝ) (y0 : ℕ) :
    Finset.Icc 1 N ⊆ Good N y_smooth y0 ∪ (E_A N y_smooth ∪ (E_B N y_smooth ∪ E_F N y0)) := by
  intro n hn
  simp only [Finset.mem_union, Good, E_A, E_B, E_F, Finset.mem_filter]
  by_cases h1 : (maxPrimeFactor n : ℝ) ≤ y_smooth
  · exact Or.inr (Or.inl ⟨hn, h1⟩)
  · have h1' : y_smooth < (maxPrimeFactor n : ℝ) := not_le.mp h1
    by_cases h2 : (maxPrimeFactor n) ^ 2 ∣ n
    · exact Or.inr (Or.inr (Or.inl ⟨hn, h1', h2⟩))
    · by_cases h3 : ∃ q : ℕ, q.Prime ∧ y0 < q ∧ q ∣ n ∧ q ∣ σ 1 n
      · exact Or.inr (Or.inr (Or.inr ⟨hn, h3⟩))
      · exact Or.inl ⟨hn, h1', h2, h3⟩

private lemma card_E_A_le (N : ℕ) (y : ℝ) (hN : 4 ≤ N) (hy : 2 ≤ y) :
    ((E_A N y).card : ℝ) ≤
      Real.sqrt N + 4 * (N : ℝ) * (Real.log y + Real.log 4) / Real.log N := by
  have hN_pos : (0 : ℝ) < N := by positivity
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  let E_lo : Finset ℕ := (E_A N y).filter (fun n : ℕ => (n : ℝ) ≤ Real.sqrt N)
  let E_hi : Finset ℕ := (E_A N y).filter (fun n : ℕ => Real.sqrt N < (n : ℝ))
  have hsplit : (E_A N y).card ≤ E_lo.card + E_hi.card := by
    have hu : E_A N y ⊆ E_lo ∪ E_hi := by
      intro n hn
      rw [Finset.mem_union]
      by_cases h : (n : ℝ) ≤ Real.sqrt N
      · exact Or.inl (Finset.mem_filter.mpr ⟨hn, h⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hn, not_le.mp h⟩)
    exact (Finset.card_le_card hu).trans (Finset.card_union_le _ _)
  have hlo : (E_lo.card : ℝ) ≤ Real.sqrt N := by
    have hsub : E_lo ⊆ Finset.Icc 1 ⌊Real.sqrt N⌋₊ := by
      intro n hn
      simp only [E_lo, E_A, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1.1.1, Nat.le_floor hn.2⟩
    have hcard : E_lo.card ≤ ⌊Real.sqrt N⌋₊ := (Finset.card_le_card hsub).trans (by simp)
    exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le (Real.sqrt_nonneg _))
  have hhi : ((E_hi.card : ℝ)) * ((1 / 2 : ℝ) * Real.log N) ≤
      2 * (N : ℝ) * (Real.log y + Real.log 4) := by
    have hlog_ge : ∀ n ∈ E_hi,
        (1 / 2 : ℝ) * Real.log N ≤
          ∑ p ∈ Nat.primesLE ⌊y⌋₊, ((n.factorization p : ℕ) : ℝ) * Real.log p := by
      intro n hn
      simp only [E_hi, E_A, Finset.mem_filter, Finset.mem_Icc] at hn
      have hn0 : n ≠ 0 := by omega
      have h1 : (1 / 2 : ℝ) * Real.log N ≤ Real.log (n : ℝ) := by
        have hsq : Real.log (Real.sqrt N) = (1 / 2 : ℝ) * Real.log N := by
          rw [Real.log_sqrt hN_pos.le]; ring
        rw [← hsq]
        exact Real.log_le_log (Real.sqrt_pos.mpr hN_pos) hn.2.le
      have h2 : Real.log (n : ℝ) =
          ∑ p ∈ n.primeFactors, ((n.factorization p : ℕ) : ℝ) * Real.log p := by
        have hfac := Nat.prod_factorization_pow_eq_self hn0
        rw [Finsupp.prod, Nat.support_factorization] at hfac
        have hcast : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
          exact_mod_cast hfac.symm
        rw [hcast, Real.log_prod (fun p hp =>
          pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
        refine Finset.sum_congr rfl fun p _ => Real.log_pow (p : ℝ) _
      have hsub : n.primeFactors ⊆ Nat.primesLE ⌊y⌋₊ := by
        intro p hp
        rw [Nat.mem_primesLE]
        refine ⟨Nat.le_floor ?_, Nat.prime_of_mem_primeFactors hp⟩
        exact (Nat.cast_le.mpr (le_maxPrimeFactor hp)).trans hn.1.2
      rw [h2] at h1
      exact h1.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => by
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
        have := Real.log_nonneg hp1
        positivity)
    have hsum_fac : ∀ p ∈ Nat.primesLE ⌊y⌋₊,
        ∑ n ∈ Finset.Icc 1 N, ((n.factorization p : ℕ) : ℝ) ≤ 2 * (N : ℝ) / (p : ℝ) := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
      have hprod_fac : ∑ n ∈ Finset.Icc 1 N, n.factorization p = N.factorial.factorization p := by
        have hfact : N.factorial = ∏ n ∈ Finset.Icc 1 N, n := by
          clear hN hN_pos hlogN E_lo E_hi hsplit hlo hlog_ge hp hpp
          induction N with
          | zero => simp
          | succ m ih =>
            rw [Nat.factorial_succ, ih, Finset.prod_Icc_succ_top (Nat.succ_pos m), mul_comm]
        rw [hfact, Nat.factorization_prod (fun n hn => by
          rw [Finset.mem_Icc] at hn; omega)]
        simp [Finsupp.finsetSum_apply]
      have hle_nat : N.factorial.factorization p ≤ N / (p - 1) :=
        Nat.factorization_factorial_le_div_pred hpp N
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      calc ∑ n ∈ Finset.Icc 1 N, ((n.factorization p : ℕ) : ℝ)
          = ((N.factorial.factorization p : ℕ) : ℝ) := by exact_mod_cast hprod_fac
        _ ≤ ((N / (p - 1) : ℕ) : ℝ) := by exact_mod_cast hle_nat
        _ ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
        _ = (N : ℝ) / ((p : ℝ) - 1) := by rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
        _ ≤ 2 * (N : ℝ) / (p : ℝ) := by
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            nlinarith
    have hhi_sub : E_hi ⊆ Finset.Icc 1 N := by
      intro n hn
      simp only [E_hi, E_A, Finset.mem_filter] at hn
      exact hn.1.1
    calc ((E_hi.card : ℝ)) * ((1 / 2 : ℝ) * Real.log N)
        = ∑ _n ∈ E_hi, (1 / 2 : ℝ) * Real.log N := by simp
      _ ≤ ∑ n ∈ E_hi, ∑ p ∈ Nat.primesLE ⌊y⌋₊, ((n.factorization p : ℕ) : ℝ) * Real.log p :=
          Finset.sum_le_sum hlog_ge
      _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ Nat.primesLE ⌊y⌋₊,
            ((n.factorization p : ℕ) : ℝ) * Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hhi_sub fun _ _ _ =>
            Finset.sum_nonneg fun p hp => by
              have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
              have := Real.log_nonneg this
              positivity
      _ = ∑ p ∈ Nat.primesLE ⌊y⌋₊,
            (∑ n ∈ Finset.Icc 1 N, ((n.factorization p : ℕ) : ℝ)) * Real.log p := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => (Finset.sum_mul ..).symm
      _ ≤ ∑ p ∈ Nat.primesLE ⌊y⌋₊, (2 * (N : ℝ) / (p : ℝ)) * Real.log p := by
          refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hsum_fac p hp) ?_
          exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
      _ = 2 * (N : ℝ) * ∑ p ∈ Nat.primesLE ⌊y⌋₊, Real.log p / (p : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ 2 * (N : ℝ) * (Real.log (⌊y⌋₊ : ℝ) + Real.log 4) := by
          gcongr
          exact sum_log_div_prime_le ⌊y⌋₊ (Nat.le_floor (by norm_num; linarith))
      _ ≤ 2 * (N : ℝ) * (Real.log y + Real.log 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hfl1 : (0 : ℝ) < (⌊y⌋₊ : ℝ) := by
            have h1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
            exact_mod_cast h1
          linarith [Real.log_le_log hfl1 (Nat.floor_le (by linarith))]
  have hhi' : (E_hi.card : ℝ) ≤ 4 * (N : ℝ) * (Real.log y + Real.log 4) / Real.log N := by
    rw [le_div_iff₀ hlogN]
    linarith
  have hsplitR : ((E_A N y).card : ℝ) ≤ (E_lo.card : ℝ) + (E_hi.card : ℝ) := by
    exact_mod_cast hsplit
  linarith

private lemma card_E_B_le (N : ℕ) (y : ℝ) (hy : 2 ≤ y) :
    ((E_B N y).card : ℝ) ≤ (N : ℝ) / (⌊y⌋₊ : ℝ) := by
  have hy_fl : 2 ≤ ⌊y⌋₊ := Nat.le_floor hy
  have hsub : E_B N y ⊆ (Finset.Ioc ⌊y⌋₊ N).biUnion
      (fun p => (Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ n)) := by
    intro n hn
    simp only [E_B, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_biUnion]
    refine ⟨maxPrimeFactor n, ?_, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hn.1, hn.2.2⟩⟩
    rw [Finset.mem_Ioc]
    have hgt : ⌊y⌋₊ < maxPrimeFactor n := by
      have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
      exact_mod_cast h1.trans_lt hn.2.1
    exact ⟨hgt, (maxPrimeFactor_le_self n).trans hn.1.2⟩
  have hcard_dvd : ∀ p : ℕ, 1 ≤ p →
      (((Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ n)).card : ℝ) ≤ (N : ℝ) / ((p : ℝ) ^ 2) := by
    intro p hp
    have hp2 : 1 ≤ p ^ 2 := by nlinarith
    have hbij : (Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ n) =
        (Finset.Icc 1 (N / p ^ 2)).image (fun k => k * p ^ 2) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
        refine ⟨n / p ^ 2, ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp2,
          Nat.div_le_div_right hnN⟩, Nat.div_mul_cancel hdvd⟩
      · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
        exact ⟨⟨by nlinarith, (Nat.mul_le_mul_right _ hkN).trans (Nat.div_mul_le_self N _)⟩,
          dvd_mul_left _ k⟩
    rw [hbij, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hp2 h)]
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    calc ((N / p ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / ((p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      _ = (N : ℝ) / ((p : ℝ) ^ 2) := by push_cast; rfl
  calc ((E_B N y).card : ℝ)
      ≤ (((Finset.Ioc ⌊y⌋₊ N).biUnion
          (fun p => (Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ n))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Finset.Ioc ⌊y⌋₊ N,
          (((Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ n)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ p ∈ Finset.Ioc ⌊y⌋₊ N, (N : ℝ) / ((p : ℝ) ^ 2) :=
        Finset.sum_le_sum fun p hp => hcard_dvd p (by rw [Finset.mem_Ioc] at hp; omega)
    _ = (N : ℝ) * ∑ p ∈ Finset.Ioc ⌊y⌋₊ N, (1 : ℝ) / ((p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
    _ ≤ (N : ℝ) * (1 / (⌊y⌋₊ : ℝ)) := by
        gcongr
        exact sum_Ioc_inv_sq_le ⌊y⌋₊ N (by omega)
    _ = (N : ℝ) / (⌊y⌋₊ : ℝ) := by ring

private lemma sum_inv_prime_congr_neg_one_le (N q : ℕ) (hN : 4 ≤ N) (hq : q.Prime) (hq4 : 4 ≤ q) :
    ∑ p ∈ (Nat.primesLE N).filter (fun p => p % q = q - 1), (1 : ℝ) / (p : ℝ) ≤
      (116 + 2 * Real.log q + 36 * Real.log (Real.log N)) / (q : ℝ) := by
  have hq_pos : (0 : ℝ) < q := by positivity
  let A := 8 * q ^ 2
  let P_all := (Nat.primesLE N).filter (fun p => p % q = q - 1)
  let P_lo := P_all.filter (fun p => p ≤ A)
  let P_hi := P_all.filter (fun p => A < p)
  have hsplit : ∑ p ∈ P_all, (1 : ℝ) / (p : ℝ) =
      (∑ p ∈ P_lo, (1 : ℝ) / (p : ℝ)) + (∑ p ∈ P_hi, (1 : ℝ) / (p : ℝ)) := by
    have hu : P_all = P_lo ∪ P_hi := by
      ext p
      simp only [P_lo, P_hi, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hp
        by_cases hle : p ≤ A
        · exact Or.inl ⟨hp, hle⟩
        · exact Or.inr ⟨hp, not_le.mp hle⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    have hdisj : Disjoint P_lo P_hi := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [P_lo, P_hi, Finset.mem_filter] at h1 h2; omega
    conv_lhs => rw [hu]
    exact Finset.sum_union hdisj
  -- Bound low part p ≤ 8 q^2
  have hlo : ∑ p ∈ P_lo, (1 : ℝ) / (p : ℝ) ≤ (8 + 2 * Real.log q) / (q : ℝ) := by
    have hsub : P_lo ⊆ (Finset.Icc 1 (8 * q)).image (fun j => j * q - 1) := by
      intro p hp
      simp only [P_lo, P_all, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_image,
        Finset.mem_Icc] at hp ⊢
      have hdiv : q * (p / q) + (q - 1) = p := by
        rw [← hp.1.2]; exact Nat.div_add_mod p q
      have h1 : (p / q) * q + (q - 1) ≤ 8 * q ^ 2 := by
        have hA : A = 8 * q ^ 2 := rfl
        have : (p / q) * q + (q - 1) = p := by linarith
        linarith [hp.2]
      have hdiv_lt : p / q + 1 ≤ 8 * q := by
        have hqsq : q * q = q ^ 2 := by ring
        have h2 : (p / q + 1) * q = (p / q) * q + q := by ring
        have h3 : (p / q + 1) * q ≤ 8 * q * q + 1 := by
          have : q = (q - 1) + 1 := by omega
          nlinarith
        have h4 : (p / q + 1) * q ≤ 8 * q * q := by
          by_contra hgt
          have hgt' : 8 * q * q < (p / q + 1) * q := not_le.mp hgt
          have hstep : 8 * q + 1 ≤ p / q + 1 := by
            by_contra hle
            have : p / q + 1 ≤ 8 * q := by omega
            have := Nat.mul_le_mul_right q this
            nlinarith
          have := Nat.mul_le_mul_right q hstep
          nlinarith
        exact Nat.le_of_mul_le_mul_right h4 (by omega)
      refine ⟨p / q + 1, ⟨Nat.succ_pos _, hdiv_lt⟩, ?_⟩
      have h2 : (p / q + 1) * q = q * (p / q) + q := by ring
      omega
    have hsum_img : ∑ p ∈ P_lo, (1 : ℝ) / (p : ℝ) ≤
        ∑ j ∈ Finset.Icc 1 (8 * q), (1 : ℝ) / ((j * q - 1 : ℕ) : ℝ) := by
      calc ∑ p ∈ P_lo, (1 : ℝ) / (p : ℝ)
          ≤ ∑ p ∈ (Finset.Icc 1 (8 * q)).image (fun j => j * q - 1), (1 : ℝ) / (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = ∑ j ∈ Finset.Icc 1 (8 * q), (1 : ℝ) / ((j * q - 1 : ℕ) : ℝ) := by
            refine Finset.sum_image fun a ha b hb heq => ?_
            simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
            have h1 : a * q = b * q := by
              have : 1 ≤ a * q := by nlinarith
              have : 1 ≤ b * q := by nlinarith
              omega
            exact Nat.eq_of_mul_eq_mul_right (by omega) h1
    have hterm : ∀ j ∈ Finset.Icc 1 (8 * q),
        (1 : ℝ) / ((j * q - 1 : ℕ) : ℝ) ≤ (2 / (q : ℝ)) * ((1 : ℝ) / (j : ℝ)) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hjq_ge : 4 ≤ j * q := by nlinarith
      have hjq : j * q ≤ 2 * (j * q - 1) := by omega
      have hpos1 : (0 : ℝ) < ((j * q - 1 : ℕ) : ℝ) := by
        have : 1 ≤ j * q - 1 := by omega
        positivity
      have hj_pos : (0 : ℝ) < j := by have : 1 ≤ j := hj.1; positivity
      have hjqR : (j : ℝ) * (q : ℝ) ≤ 2 * ((j * q - 1 : ℕ) : ℝ) := by exact_mod_cast hjq
      rw [show (2 / (q : ℝ)) * ((1 : ℝ) / (j : ℝ)) = 2 / ((j : ℝ) * (q : ℝ)) by ring]
      rw [div_le_div_iff₀ hpos1 (by positivity)]
      linarith
    have hlog8q : Real.log ((8 * q : ℕ) : ℝ) ≤ 3 + Real.log q := by
      push_cast
      rw [Real.log_mul (by norm_num) hq_pos.ne']
      have h8 : Real.log 8 ≤ 3 := by
        have : Real.log 8 = 3 * Real.log 2 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
        have h2 : Real.log 2 < 1 := by
          have : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
          calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) this
            _ = 1 := Real.log_exp 1
        linarith
      linarith
    calc ∑ p ∈ P_lo, (1 : ℝ) / (p : ℝ)
        ≤ ∑ j ∈ Finset.Icc 1 (8 * q), (1 : ℝ) / ((j * q - 1 : ℕ) : ℝ) := hsum_img
      _ ≤ ∑ j ∈ Finset.Icc 1 (8 * q), (2 / (q : ℝ)) * ((1 : ℝ) / (j : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (2 / (q : ℝ)) * ∑ j ∈ Finset.Icc 1 (8 * q), (1 : ℝ) / (j : ℝ) := by
          rw [← Finset.mul_sum]
      _ ≤ (2 / (q : ℝ)) * (1 + Real.log ((8 * q : ℕ) : ℝ)) := by
          gcongr
          exact sum_Icc_inv_le_one_add_log (8 * q)
      _ ≤ (2 / (q : ℝ)) * (1 + (3 + Real.log q)) := by gcongr
      _ = (8 + 2 * Real.log q) / (q : ℝ) := by ring
  -- Bound high part 8 q^2 < p ≤ N via summation by parts + Brun-Titchmarsh
  have hhi : ∑ p ∈ P_hi, (1 : ℝ) / (p : ℝ) ≤
      (108 + 36 * Real.log (Real.log N)) / (q : ℝ) := by
    by_cases hNA : N ≤ A
    · have hemp : P_hi = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp
        simp only [P_all, Finset.mem_filter, Nat.mem_primesLE] at hp
        omega
      rw [hemp, Finset.sum_empty]
      have : 0 ≤ Real.log (Real.log (N : ℝ)) := by
        have hlogN : 1 ≤ Real.log (N : ℝ) := by
          have h1 : Real.exp 1 ≤ (N : ℝ) := by
            have := Real.exp_one_lt_d9
            have : (4 : ℝ) ≤ N := by exact_mod_cast hN
            linarith
          calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
            _ ≤ Real.log (N : ℝ) := Real.log_le_log (Real.exp_pos 1) h1
        exact Real.log_nonneg hlogN
      positivity
    push Not at hNA
    let Pq : ℕ → ℝ := fun m =>
      (((Finset.Icc 1 m).filter (fun p => p.Prime ∧ p % q = q - 1)).card : ℝ)
    let f : ℕ → ℝ := fun m => (1 : ℝ) / (m : ℝ)
    have hPq_diff : ∀ m : ℕ, 1 ≤ m →
        Pq m - Pq (m - 1) = if m.Prime ∧ m % q = q - 1 then 1 else 0 := by
      intro m hm
      have hprev : (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p % q = q - 1) =
          (if m.Prime ∧ m % q = q - 1 then {m} else ∅) ∪
          (Finset.Icc 1 (m - 1)).filter (fun p => p.Prime ∧ p % q = q - 1) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
        split_ifs with hcond
        · simp only [Finset.mem_singleton]
          constructor
          · rintro ⟨⟨hp1, hpm⟩, hpc⟩
            by_cases heq : p = m
            · exact Or.inl heq
            · exact Or.inr ⟨⟨hp1, by omega⟩, hpc⟩
          · rintro (rfl | ⟨⟨hp1, hpm⟩, hpc⟩)
            · exact ⟨⟨hm, le_rfl⟩, hcond⟩
            · exact ⟨⟨hp1, by omega⟩, hpc⟩
        · simp only [Finset.notMem_empty, false_or]
          constructor
          · rintro ⟨⟨hp1, hpm⟩, hpc⟩
            have hne : p ≠ m := fun h => hcond (h ▸ hpc)
            exact ⟨⟨hp1, by omega⟩, hpc⟩
          · rintro ⟨⟨hp1, hpm⟩, hpc⟩
            exact ⟨⟨hp1, by omega⟩, hpc⟩
      have hdisj : Disjoint (if m.Prime ∧ m % q = q - 1 then ({m} : Finset ℕ) else ∅)
          ((Finset.Icc 1 (m - 1)).filter (fun p => p.Prime ∧ p % q = q - 1)) := by
        split_ifs
        · rw [Finset.disjoint_singleton_left, Finset.mem_filter, Finset.mem_Icc]
          intro h; omega
        · exact Finset.disjoint_empty_left _
      simp only [Pq, hprev, Finset.card_union_of_disjoint hdisj]
      split_ifs <;> push_cast <;> simp
    have hPq_bt : ∀ m : ℕ, A ≤ m → Pq m ≤ 36 * (m : ℝ) / ((q : ℝ) * Real.log m) := by
      intro m hm
      have hm_ge : 8 * (q : ℝ) ≤ (m : ℝ) := by
        have : 8 * q ≤ m := by dsimp only [A] at hm; nlinarith
        exact_mod_cast this
      have hbt := brun_titchmarsh (m : ℝ) q (q - 1) (by omega) hm_ge
      rw [Nat.floor_natCast, Nat.mod_eq_of_lt (by omega : q - 1 < q)] at hbt
      have hphi_q : (Nat.totient q : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.totient_prime hq, Nat.cast_sub hq.one_le, Nat.cast_one]
      have hq_half : (q : ℝ) / 2 ≤ (q : ℝ) - 1 := by
        have : (4 : ℝ) ≤ q := by exact_mod_cast hq4
        linarith
      have hmq : Real.sqrt (m : ℝ) ≤ (m : ℝ) / (q : ℝ) := by
        have h1 : (q : ℝ) ^ 2 ≤ (m : ℝ) := by
          have : q ^ 2 ≤ m := by dsimp only [A] at hm; nlinarith
          exact_mod_cast this
        have h2 : (q : ℝ) ≤ Real.sqrt (m : ℝ) := by
          calc (q : ℝ) = Real.sqrt ((q : ℝ) ^ 2) := (Real.sqrt_sq hq_pos.le).symm
            _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt h1
        rw [le_div_iff₀ hq_pos]
        nlinarith [Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ m)]
      have hm_pos : (0 : ℝ) < m := by
        have : 1 ≤ m := by dsimp only [A] at hm; nlinarith
        positivity
      have hlogm : 0 < Real.log (m : ℝ) := by
        apply Real.log_pos
        have : 2 ≤ m := by dsimp only [A] at hm; nlinarith
        exact_mod_cast (by omega : 1 < m)
      have hlog_half : (1 / 2 : ℝ) * Real.log m ≤ Real.log ((m : ℝ) / (q : ℝ)) := by
        have h1 : Real.log (Real.sqrt (m : ℝ)) = (1 / 2 : ℝ) * Real.log m := by
          rw [Real.log_sqrt hm_pos.le]; ring
        rw [← h1]
        exact Real.log_le_log (Real.sqrt_pos.mpr hm_pos) hmq
      have hden : ((q : ℝ) / 2) * ((1 / 2 : ℝ) * Real.log m) ≤
          (Nat.totient q : ℝ) * Real.log ((m : ℝ) / (q : ℝ)) := by
        rw [hphi_q]
        exact mul_le_mul hq_half hlog_half (by positivity) (by linarith)
      calc Pq m ≤ 9 * (m : ℝ) / ((Nat.totient q : ℝ) * Real.log ((m : ℝ) / (q : ℝ))) := hbt
        _ ≤ 9 * (m : ℝ) / (((q : ℝ) / 2) * ((1 / 2 : ℝ) * Real.log m)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = 36 * (m : ℝ) / ((q : ℝ) * Real.log m) := by ring
    have hrewrite : ∑ p ∈ P_hi, (1 : ℝ) / (p : ℝ) =
        ∑ m ∈ Finset.Icc (A + 1) N, (Pq m - Pq (m - 1)) * f m := by
      have h1 : ∑ m ∈ Finset.Icc (A + 1) N, (Pq m - Pq (m - 1)) * f m =
          ∑ m ∈ (Finset.Icc (A + 1) N).filter (fun m => m.Prime ∧ m % q = q - 1), f m := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.mem_Icc] at hm
        rw [hPq_diff m (by omega)]
        split_ifs <;> simp
      rw [h1]
      congr 1
      ext p
      simp only [P_hi, P_all, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hpN, hpp⟩, hmod⟩, hAp⟩; exact ⟨⟨by omega, hpN⟩, hpp, hmod⟩
      · rintro ⟨⟨hAp, hpN⟩, hpp, hmod⟩; exact ⟨⟨⟨hpN, hpp⟩, hmod⟩, by omega⟩
    rw [hrewrite, sum_by_parts_Icc Pq f (A + 1) N (by omega) hNA]
    have hlogN : 1 ≤ Real.log (N : ℝ) := by
      have h1 : Real.exp 1 ≤ (N : ℝ) := by
        have := Real.exp_one_lt_d9
        have : (4 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (N : ℝ) := Real.log_le_log (Real.exp_pos 1) h1
    have hN_pos : (0 : ℝ) < N := by positivity
    have hPN : Pq N * f N ≤ 36 / (q : ℝ) := by
      have h1 := hPq_bt N hNA.le
      simp only [f]
      calc Pq N * (1 / (N : ℝ))
          ≤ (36 * (N : ℝ) / ((q : ℝ) * Real.log N)) * (1 / (N : ℝ)) := by gcongr
        _ = 36 / ((q : ℝ) * Real.log N) := by field_simp [hN_pos.ne', hq_pos.ne', (by linarith : Real.log (N : ℝ) ≠ 0)]
        _ ≤ 36 / (q : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) hq_pos]
            nlinarith
    have hneg : 0 ≤ Pq (A + 1 - 1) * f (A + 1) := by simp only [Pq, f]; positivity
    have hsum : ∑ m ∈ Finset.Ico (A + 1) N, Pq m * (f m - f (m + 1)) ≤
        (36 * (Real.log (Real.log N) + 1)) / (q : ℝ) := by
      have hterm : ∀ m ∈ Finset.Ico (A + 1) N,
          Pq m * (f m - f (m + 1)) ≤
            (36 / (q : ℝ)) * ((1 : ℝ) / ((m : ℝ) * Real.log m)) := by
        intro m hm
        rw [Finset.mem_Ico] at hm
        have hmA : A ≤ m := by omega
        have hm1 : 1 ≤ m := by dsimp only [A] at hmA; nlinarith
        have hm_pos : (0 : ℝ) < m := by positivity
        have hlogm : 0 < Real.log (m : ℝ) := by
          apply Real.log_pos
          have : 2 ≤ m := by dsimp only [A] at hmA; nlinarith
          exact_mod_cast (by omega : 1 < m)
        have hdiff : f m - f (m + 1) ≤ 1 / ((m : ℝ) ^ 2) := by
          simp only [f]
          have hrew : 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) =
              1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
            push_cast; field_simp; ring
          rw [hrew, div_le_div_iff₀ (by positivity) (by positivity)]
          push_cast; nlinarith
        have hdiff_nn : 0 ≤ f m - f (m + 1) := by
          simp only [f, sub_nonneg]
          exact one_div_le_one_div_of_le hm_pos (by exact_mod_cast Nat.le_succ m)
        calc Pq m * (f m - f (m + 1))
            ≤ (36 * (m : ℝ) / ((q : ℝ) * Real.log m)) * (1 / ((m : ℝ) ^ 2)) :=
              mul_le_mul (hPq_bt m hmA) hdiff hdiff_nn (by positivity)
          _ = (36 / (q : ℝ)) * (1 / ((m : ℝ) * Real.log m)) := by
              field_simp [hm_pos.ne', hq_pos.ne', hlogm.ne']
      have hsub : Finset.Ico (A + 1) N ⊆ Finset.Icc 3 N := by
        intro m hm
        rw [Finset.mem_Ico] at hm
        rw [Finset.mem_Icc]
        have : 3 ≤ A := by dsimp only [A]; nlinarith
        omega
      calc ∑ m ∈ Finset.Ico (A + 1) N, Pq m * (f m - f (m + 1))
          ≤ ∑ m ∈ Finset.Ico (A + 1) N,
              (36 / (q : ℝ)) * ((1 : ℝ) / ((m : ℝ) * Real.log m)) :=
            Finset.sum_le_sum hterm
        _ = (36 / (q : ℝ)) * ∑ m ∈ Finset.Ico (A + 1) N,
              (1 : ℝ) / ((m : ℝ) * Real.log m) := by rw [← Finset.mul_sum]
        _ ≤ (36 / (q : ℝ)) * ∑ m ∈ Finset.Icc 3 N,
              (1 : ℝ) / ((m : ℝ) * Real.log m) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => ?_
            rw [Finset.mem_Icc] at hm
            have : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
            positivity
        _ ≤ (36 / (q : ℝ)) * (Real.log (Real.log N) + 1) := by
            gcongr
            exact sum_Icc_inv_mul_log_le N (by omega)
        _ = (36 * (Real.log (Real.log N) + 1)) / (q : ℝ) := by ring
    have h72 : 36 / (q : ℝ) + (36 * (Real.log (Real.log N) + 1)) / (q : ℝ) ≤
        (108 + 36 * Real.log (Real.log N)) / (q : ℝ) := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hq_pos.le
      linarith
    linarith
  have hlo' : ∑ p ∈ P_lo, (1 : ℝ) / (p : ℝ) ≤ (8 + 2 * Real.log q) / (q : ℝ) := hlo
  rw [hsplit]
  have hadd : (8 + 2 * Real.log q) / (q : ℝ) + (108 + 36 * Real.log (Real.log N)) / (q : ℝ) =
      (116 + 2 * Real.log q + 36 * Real.log (Real.log N)) / (q : ℝ) := by ring
  linarith

private lemma sigma_prime_pow_lt_two_mul (p e : ℕ) (hp : p.Prime) :
    σ 1 (p ^ e) < 2 * p ^ e := by
  rw [ArithmeticFunction.sigma_apply_prime_pow hp]
  simp only [mul_one]
  have hgeom : (p - 1) * ∑ i ∈ Finset.range (e + 1), p ^ i = p ^ (e + 1) - 1 := by
    induction e with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hp1 : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ hp.pos
      have hp2 : 1 ≤ p ^ (k + 2) := Nat.one_le_pow _ _ hp.pos
      zify [hp1, hp2, hp.one_le]
      ring
  have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  have hlt : (p - 1) * ∑ i ∈ Finset.range (e + 1), p ^ i < (p - 1) * (2 * p ^ e) := by
    rw [hgeom]
    have h1 : p ^ (e + 1) = p * p ^ e := by ring
    have h2 : p ≤ 2 * (p - 1) := by have := hp.two_le; omega
    have h3 : p ^ (e + 1) ≤ (p - 1) * (2 * p ^ e) := by
      rw [h1]
      calc p * p ^ e ≤ (2 * (p - 1)) * p ^ e := Nat.mul_le_mul_right _ h2
        _ = (p - 1) * (2 * p ^ e) := by ring
    have h4 : 1 ≤ p ^ (e + 1) := Nat.one_le_pow _ _ hp.pos
    omega
  exact Nat.lt_of_mul_lt_mul_left hlt

private lemma card_E_F_le (N y0 : ℕ) (hN : 16 ≤ N) (hy0 : 4 ≤ y0) :
    ((E_F N y0).card : ℝ) ≤
      (N : ℝ) * (120 / (y0 : ℝ) + 20 / Real.sqrt y0 +
        864 * Real.log (Real.log N) / ((y0 : ℝ) * Real.log y0)) := by
  let EF1 := (E_F N y0).filter (fun n => ∃ q : ℕ, q.Prime ∧ y0 < q ∧ q ^ 2 ∣ n)
  let EF2a := (E_F N y0).filter (fun n =>
    ∃ q : ℕ, q.Prime ∧ y0 < q ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n ∧
      ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ p ^ e ∣ n / q ∧ q < 2 * p ^ e)
  let EF2b := (E_F N y0).filter (fun n =>
    ∃ q p : ℕ, q.Prime ∧ p.Prime ∧ y0 < q ∧ p % q = q - 1 ∧ q * p ∣ n)
  have hcover : E_F N y0 ⊆ EF1 ∪ (EF2a ∪ EF2b) := by
    intro n hn
    simp only [Finset.mem_union, EF1, EF2a, EF2b, Finset.mem_filter]
    have hn_info := hn
    simp only [E_F, Finset.mem_filter, Finset.mem_Icc] at hn_info
    obtain ⟨q, hq, hqy0, hqn, hqsig⟩ := hn_info.2
    by_cases hq2 : q ^ 2 ∣ n
    · exact Or.inl ⟨hn, q, hq, hqy0, hq2⟩
    · right
      let r := n / q
      have hqr : q * r = n := Nat.mul_div_cancel' hqn
      have hqnd_r : ¬ q ∣ r := by
        intro hqr_dvd
        apply hq2
        rw [← hqr, sq]
        exact Nat.mul_dvd_mul_left q hqr_dvd
      have hcop_qr : Nat.Coprime q r := hq.coprime_iff_not_dvd.mpr hqnd_r
      have hsig_mul : σ 1 n = σ 1 q * σ 1 r := by
        rw [← hqr]
        exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop_qr
      have hsig_q : σ 1 q = q + 1 := by
        rw [ArithmeticFunction.sigma_one_apply, hq.sum_divisors]
      rw [hsig_mul, hsig_q] at hqsig
      have hcop_qq1 : Nat.Coprime q (q + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right q)
      have hqsig_r : q ∣ σ 1 r := hcop_qq1.dvd_of_dvd_mul_left hqsig
      have hr0 : r ≠ 0 := by
        intro hr0; rw [hr0, mul_zero] at hqr; omega
      have hsig_r_prod : σ 1 r = ∏ p ∈ r.primeFactors, σ 1 (p ^ (r.factorization p)) := by
        have hfac := Nat.prod_factorization_pow_eq_self hr0
        rw [Finsupp.prod, Nat.support_factorization] at hfac
        conv_lhs => rw [← hfac]
        exact ArithmeticFunction.isMultiplicative_sigma.map_prod (fun p => p ^ r.factorization p)
          r.primeFactors (fun p hp q' hq' hpq =>
            ((Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mpr fun h =>
              hpq ((Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hp)
                (Nat.prime_of_mem_primeFactors hq')).mp h)).pow _ _)
      rw [hsig_r_prod] at hqsig_r
      rw [hq.prime.dvd_finsetProd_iff] at hqsig_r
      obtain ⟨p, hp_mem, hq_sig_pe⟩ := hqsig_r
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hpdvd_r : p ∣ r := Nat.dvd_of_mem_primeFactors hp_mem
      set e := r.factorization p
      have he1 : 1 ≤ e := (Nat.Prime.dvd_iff_one_le_factorization hp hr0).mp hpdvd_r
      by_cases he2 : 2 ≤ e
      · left
        refine ⟨hn, q, hq, hqy0, hqn, hq2, p, e, hp, he2, Nat.ordProj_dvd r p, ?_⟩
        have hsig_pos : 0 < σ 1 (p ^ e) := by
          rw [ArithmeticFunction.sigma_one_apply]
          exact Finset.sum_pos (fun d hd => Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1
            (pow_pos hp.pos e)) ⟨1, Nat.one_mem_divisors.mpr (pow_ne_zero e hp.ne_zero)⟩
        have hle : q ≤ σ 1 (p ^ e) := Nat.le_of_dvd hsig_pos hq_sig_pe
        exact hle.trans_lt (sigma_prime_pow_lt_two_mul p e hp)
      · right
        have he_eq : e = 1 := by omega
        rw [he_eq, pow_one, ArithmeticFunction.sigma_one_apply, hp.sum_divisors] at hq_sig_pe
        have hmod : p % q = q - 1 := by
          obtain ⟨k, hk⟩ := hq_sig_pe
          have hk1 : 1 ≤ k := by
            by_contra hk0
            have : k = 0 := by omega
            rw [this, mul_zero] at hk; omega
          have hp_eq : p = (k - 1) * q + (q - 1) := by
            have hkq : q * k = (k - 1) * q + q := by
              cases k with
              | zero => omega
              | succ m => simp only [Nat.add_sub_cancel]; ring
            omega
          rw [hp_eq, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        refine ⟨hn, q, p, hq, hp, hqy0, hmod, ?_⟩
        rw [← hqr]
        exact Nat.mul_dvd_mul_left q hpdvd_r
  -- Bound EF1
  have hEF1 : (EF1.card : ℝ) ≤ (N : ℝ) / (y0 : ℝ) := by
    have hsub : EF1 ⊆ (Finset.Ioc y0 N).biUnion
        (fun q => (Finset.Icc 1 N).filter (fun n => q ^ 2 ∣ n)) := by
      intro n hn
      simp only [EF1, E_F, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨q, hq, hqy0, hq2⟩ := hn.2
      rw [Finset.mem_biUnion]
      have hqle : q ≤ N := by
        have h1 : q ^ 2 ≤ n := Nat.le_of_dvd (by omega) hq2
        have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
        omega
      exact ⟨q, Finset.mem_Ioc.mpr ⟨hqy0, hqle⟩, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hn.1.1, hq2⟩⟩
    calc (EF1.card : ℝ)
        ≤ (((Finset.Ioc y0 N).biUnion
            (fun q => (Finset.Icc 1 N).filter (fun n => q ^ 2 ∣ n))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ q ∈ Finset.Ioc y0 N, (((Finset.Icc 1 N).filter (fun n => q ^ 2 ∣ n)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ Finset.Ioc y0 N, (N : ℝ) / ((q : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [Finset.mem_Ioc] at hq
          have hq2 : 1 ≤ q ^ 2 := by nlinarith
          have hbij : (Finset.Icc 1 N).filter (fun n => q ^ 2 ∣ n) =
              (Finset.Icc 1 (N / q ^ 2)).image (fun k => k * q ^ 2) := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
            constructor
            · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
              exact ⟨n / q ^ 2, ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hq2,
                Nat.div_le_div_right hnN⟩, Nat.div_mul_cancel hdvd⟩
            · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
              exact ⟨⟨by nlinarith, (Nat.mul_le_mul_right _ hkN).trans (Nat.div_mul_le_self N _)⟩,
                dvd_mul_left _ k⟩
          rw [hbij, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hq2 h)]
          simp only [Nat.card_Icc, Nat.add_sub_cancel]
          calc ((N / q ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / ((q ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
            _ = (N : ℝ) / ((q : ℝ) ^ 2) := by push_cast; rfl
      _ = (N : ℝ) * ∑ q ∈ Finset.Ioc y0 N, (1 : ℝ) / ((q : ℝ) ^ 2) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ (N : ℝ) * (1 / (y0 : ℝ)) := by gcongr; exact sum_Ioc_inv_sq_le y0 N (by omega)
      _ = (N : ℝ) / (y0 : ℝ) := by ring
  -- Bound EF2a: split prime power p^e > q/2 into p > ⌊√(q/2)⌋ and p ≤ ⌊√(q/2)⌋
  have hEF2a : (EF2a.card : ℝ) ≤ 12 * (N : ℝ) / Real.sqrt y0 := by
    have hcard_dvd : ∀ M : ℕ, 1 ≤ M →
        (((Finset.Icc 1 N).filter (fun n => M ∣ n)).card : ℝ) ≤ (N : ℝ) / (M : ℝ) := by
      intro M hM
      have hbij : (Finset.Icc 1 N).filter (fun n => M ∣ n) =
          (Finset.Icc 1 (N / M)).image (fun k => k * M) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
          exact ⟨n / M, ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hM,
            Nat.div_le_div_right hnN⟩, Nat.div_mul_cancel hdvd⟩
        · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
          exact ⟨⟨by nlinarith, (Nat.mul_le_mul_right _ hkN).trans (Nat.div_mul_le_self N _)⟩,
            dvd_mul_left _ k⟩
      rw [hbij, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hM h)]
      simp only [Nat.card_Icc, Nat.add_sub_cancel]
      exact Nat.cast_div_le
    -- For each q ∈ Ioc y0 N, bound # {n ∈ EF2a for this q} ≤ 6 * N / (q * √q)
    let perQ : ℕ → Finset ℕ := fun q =>
      (Finset.Icc 1 N).filter (fun n =>
        q ∣ n ∧ ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ p ^ e ∣ n / q ∧ q < 2 * p ^ e)
    have hsub : EF2a ⊆ (Finset.Ioc y0 N).biUnion perQ := by
      intro n hn
      simp only [EF2a, E_F, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨q, hq, hqy0, hqn, _, p, e, hp, he2, hpe, hqlt⟩ := hn.2
      rw [Finset.mem_biUnion]
      have hqle : q ≤ N := (Nat.le_of_dvd (by omega) hqn).trans hn.1.1.2
      exact ⟨q, Finset.mem_Ioc.mpr ⟨hqy0, hqle⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hn.1.1, hqn, p, e, hp, he2, hpe, hqlt⟩⟩
    have hperQ : ∀ q ∈ Finset.Ioc y0 N,
        ((perQ q).card : ℝ) ≤ 6 * (N : ℝ) / ((q : ℝ) * Real.sqrt q) := by
      intro q hq
      rw [Finset.mem_Ioc] at hq
      have hq5 : 5 ≤ q := by omega
      let t := Nat.sqrt (q / 2)
      have ht1 : 1 ≤ t := by
        have : 1 ≤ q / 2 := by omega
        exact Nat.sqrt_pos.mpr this
      have ht_sq_le : t ^ 2 ≤ q / 2 := by
        simpa [sq] using Nat.sqrt_le (q / 2)
      have hq_lt_succ : q / 2 < (t + 1) ^ 2 := by
        simpa [sq] using Nat.lt_succ_sqrt (q / 2)
      have hbig : perQ q ⊆
          ((Finset.Ioc t N).biUnion (fun p => (Finset.Icc 1 N).filter (fun n => q * p ^ 2 ∣ n))) ∪
          ((Finset.Icc 2 t).biUnion (fun p =>
            (Finset.Icc 1 N).filter (fun n => q * p ^ (Nat.log p (q / 2) + 1) ∣ n))) := by
        intro n hn
        simp only [perQ, Finset.mem_filter, Finset.mem_Icc] at hn
        obtain ⟨⟨hn1, hnN⟩, hqn, p, e, hp, he2, hpe, hqlt⟩ := hn
        have hqpe_dvd : q * p ^ e ∣ n := by
          have := Nat.mul_dvd_mul_left q hpe
          rwa [Nat.mul_div_cancel' hqn] at this
        rw [Finset.mem_union]
        by_cases hpt : t < p
        · left
          rw [Finset.mem_biUnion]
          have hp2_dvd : q * p ^ 2 ∣ n :=
            (Nat.mul_dvd_mul_left q (pow_dvd_pow p he2)).trans hqpe_dvd
          have hpN : p ≤ N := by
            have h1 : p ^ 2 ≤ n := (Nat.le_of_dvd (by omega) ((dvd_mul_left _ q).trans hp2_dvd))
            have h2 : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
            omega
          exact ⟨p, Finset.mem_Ioc.mpr ⟨hpt, hpN⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, hp2_dvd⟩⟩
        · right
          rw [Finset.mem_biUnion]
          have hple : p ≤ t := not_lt.mp hpt
          have he_ge : Nat.log p (q / 2) + 1 ≤ e := by
            have hlt : q / 2 < p ^ e := by omega
            have hlog_lt : Nat.log p (q / 2) < e :=
              (Nat.log_lt_of_lt_pow (by omega) hlt)
            omega
          have hdvd_e0 : q * p ^ (Nat.log p (q / 2) + 1) ∣ n :=
            (Nat.mul_dvd_mul_left q (pow_dvd_pow p he_ge)).trans hqpe_dvd
          exact ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, hple⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, hdvd_e0⟩⟩
      have hpart1 : ((((Finset.Ioc t N).biUnion
          (fun p => (Finset.Icc 1 N).filter (fun n => q * p ^ 2 ∣ n))).card : ℝ)) ≤
          4 * (N : ℝ) / ((q : ℝ) * Real.sqrt q) := by
        have hq_pos : (0 : ℝ) < q := by positivity
        have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
        have ht_lb : Real.sqrt (q : ℝ) / 4 ≤ (t : ℝ) := by
          have h1 : (q : ℝ) ≤ 2 * (((t + 1 : ℕ) : ℝ) ^ 2) := by
            have : q ≤ 2 * (t + 1) ^ 2 := by omega
            exact_mod_cast this
          have h2 : ((t + 1 : ℕ) : ℝ) ≤ 2 * (t : ℝ) := by
            have : t + 1 ≤ 2 * t := by omega
            exact_mod_cast this
          have h3 : (q : ℝ) ≤ 8 * (t : ℝ) ^ 2 := by nlinarith
          have h4 : Real.sqrt (q : ℝ) ≤ Real.sqrt (16 * (t : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
          have h5 : Real.sqrt (16 * (t : ℝ) ^ 2) = 4 * (t : ℝ) := by
            rw [show 16 * (t : ℝ) ^ 2 = (4 * (t : ℝ)) ^ 2 by ring, Real.sqrt_sq (by positivity)]
          linarith
        calc ((((Finset.Ioc t N).biUnion
              (fun p => (Finset.Icc 1 N).filter (fun n => q * p ^ 2 ∣ n))).card : ℝ))
            ≤ ∑ p ∈ Finset.Ioc t N,
                (((Finset.Icc 1 N).filter (fun n => q * p ^ 2 ∣ n)).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ p ∈ Finset.Ioc t N, (N : ℝ) / ((q * p ^ 2 : ℕ) : ℝ) :=
              Finset.sum_le_sum fun p hp => hcard_dvd (q * p ^ 2) (by
                rw [Finset.mem_Ioc] at hp; nlinarith)
          _ = ((N : ℝ) / (q : ℝ)) * ∑ p ∈ Finset.Ioc t N, (1 : ℝ) / ((p : ℝ) ^ 2) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => by push_cast; ring
          _ ≤ ((N : ℝ) / (q : ℝ)) * (1 / (t : ℝ)) := by
              gcongr; exact sum_Ioc_inv_sq_le t N ht1
          _ ≤ ((N : ℝ) / (q : ℝ)) * (4 / Real.sqrt q) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [div_le_div_iff₀ (by positivity) hsqq]
              linarith
          _ = 4 * (N : ℝ) / ((q : ℝ) * Real.sqrt q) := by ring
      have hpart2 : ((((Finset.Icc 2 t).biUnion (fun p =>
          (Finset.Icc 1 N).filter (fun n => q * p ^ (Nat.log p (q / 2) + 1) ∣ n))).card : ℝ)) ≤
          2 * (N : ℝ) / ((q : ℝ) * Real.sqrt q) := by
        have hq_pos : (0 : ℝ) < q := by positivity
        have hsqq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
        have ht_ub : (t : ℝ) ≤ Real.sqrt (q : ℝ) := by
          have h1 : (t : ℝ) ^ 2 ≤ (q : ℝ) := by
            have : t ^ 2 ≤ q := by omega
            exact_mod_cast this
          calc (t : ℝ) = Real.sqrt ((t : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
            _ ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt h1
        calc ((((Finset.Icc 2 t).biUnion (fun p =>
              (Finset.Icc 1 N).filter (fun n => q * p ^ (Nat.log p (q / 2) + 1) ∣ n))).card : ℝ))
            ≤ ∑ p ∈ Finset.Icc 2 t,
                (((Finset.Icc 1 N).filter (fun n => q * p ^ (Nat.log p (q / 2) + 1) ∣ n)).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ p ∈ Finset.Icc 2 t, (N : ℝ) / ((q * p ^ (Nat.log p (q / 2) + 1) : ℕ) : ℝ) :=
              Finset.sum_le_sum fun p hp => hcard_dvd _ (by
                rw [Finset.mem_Icc] at hp
                exact Nat.mul_pos (by omega) (pow_pos (by omega) _))
          _ ≤ ∑ _p ∈ Finset.Icc 2 t, 2 * (N : ℝ) / ((q : ℝ) ^ 2) := by
              refine Finset.sum_le_sum fun p hp => ?_
              rw [Finset.mem_Icc] at hp
              have hpow_gt : q / 2 < p ^ (Nat.log p (q / 2) + 1) :=
                Nat.lt_pow_succ_log_self (by omega : 1 < p) (q / 2)
              have hq_le : q ≤ 2 * p ^ (Nat.log p (q / 2) + 1) := by omega
              have hq_leR : (q : ℝ) ≤ 2 * ((p ^ (Nat.log p (q / 2) + 1) : ℕ) : ℝ) := by
                exact_mod_cast hq_le
              push_cast
              rw [div_le_div_iff₀ (by
                have : 1 ≤ p ^ (Nat.log p (q / 2) + 1) := Nat.one_le_pow _ _ (by omega)
                have : (1 : ℝ) ≤ (p : ℝ) ^ (Nat.log p (q / 2) + 1) := by exact_mod_cast this
                positivity) (by positivity)]
              have hq_leR' : (q : ℝ) ≤ 2 * (p : ℝ) ^ (Nat.log p (q / 2) + 1) := by
                exact_mod_cast hq_le
              have hmul : (N : ℝ) * (q : ℝ) ^ 2 ≤
                  (N : ℝ) * (q : ℝ) * (2 * (p : ℝ) ^ (Nat.log p (q / 2) + 1)) := by
                have hNq_nn : 0 ≤ (N : ℝ) * (q : ℝ) := by positivity
                calc (N : ℝ) * (q : ℝ) ^ 2 = ((N : ℝ) * (q : ℝ)) * (q : ℝ) := by ring
                  _ ≤ ((N : ℝ) * (q : ℝ)) * (2 * (p : ℝ) ^ (Nat.log p (q / 2) + 1)) :=
                      mul_le_mul_of_nonneg_left hq_leR' hNq_nn
              linarith
          _ = (((Finset.Icc 2 t).card : ℝ)) * (2 * (N : ℝ) / ((q : ℝ) ^ 2)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (t : ℝ) * (2 * (N : ℝ) / ((q : ℝ) ^ 2)) := by
              gcongr
              have : (Finset.Icc 2 t).card ≤ t := by rw [Nat.card_Icc]; omega
              exact_mod_cast this
          _ ≤ Real.sqrt (q : ℝ) * (2 * (N : ℝ) / ((q : ℝ) ^ 2)) := by gcongr
          _ = 2 * (N : ℝ) / ((q : ℝ) * Real.sqrt q) := by
              have hsq : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) := Real.mul_self_sqrt hq_pos.le
              field_simp [hq_pos.ne', hsqq.ne']
              nlinarith
      have hunion : ((perQ q).card : ℝ) ≤
          ((((Finset.Ioc t N).biUnion
            (fun p => (Finset.Icc 1 N).filter (fun n => q * p ^ 2 ∣ n))).card : ℝ)) +
          ((((Finset.Icc 2 t).biUnion (fun p =>
            (Finset.Icc 1 N).filter (fun n => q * p ^ (Nat.log p (q / 2) + 1) ∣ n))).card : ℝ)) := by
        exact_mod_cast (Finset.card_le_card hbig).trans (Finset.card_union_le _ _)
      have hsum6 : 4 * (N : ℝ) / ((q : ℝ) * Real.sqrt q) +
          2 * (N : ℝ) / ((q : ℝ) * Real.sqrt q) =
          6 * (N : ℝ) / ((q : ℝ) * Real.sqrt q) := by ring
      linarith
    calc (EF2a.card : ℝ)
        ≤ (((Finset.Ioc y0 N).biUnion perQ).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ q ∈ Finset.Ioc y0 N, ((perQ q).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ Finset.Ioc y0 N, 6 * (N : ℝ) / ((q : ℝ) * Real.sqrt q) :=
          Finset.sum_le_sum hperQ
      _ = 6 * (N : ℝ) * ∑ q ∈ Finset.Ioc y0 N, (1 : ℝ) / ((q : ℝ) * Real.sqrt q) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ 6 * (N : ℝ) * (2 / Real.sqrt y0) := by
          gcongr; exact sum_Ioc_inv_rpow_three_halves_le y0 N (by omega)
      _ = 12 * (N : ℝ) / Real.sqrt y0 := by ring
  -- Bound EF2b
  have hEF2b : (EF2b.card : ℝ) ≤
      (N : ℝ) * (116 / (y0 : ℝ) + 8 / Real.sqrt y0 +
        864 * Real.log (Real.log N) / ((y0 : ℝ) * Real.log y0)) := by
    let Qset := (Nat.primesLE N).filter (fun q => y0 < q)
    let perQP : ℕ → Finset ℕ := fun q =>
      ((Nat.primesLE N).filter (fun p => p % q = q - 1)).biUnion
        (fun p => (Finset.Icc 1 N).filter (fun n => q * p ∣ n))
    have hsub : EF2b ⊆ Qset.biUnion perQP := by
      intro n hn
      simp only [EF2b, E_F, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨q, p, hq, hp, hqy0, hmod, hqpdvd⟩ := hn.2
      rw [Finset.mem_biUnion]
      have hqle : q ≤ N := (Nat.le_of_dvd (by omega) ((dvd_mul_right q p).trans hqpdvd)).trans hn.1.1.2
      have hple : p ≤ N := (Nat.le_of_dvd (by omega) ((dvd_mul_left p q).trans hqpdvd)).trans hn.1.1.2
      refine ⟨q, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hqle, hq⟩, hqy0⟩, ?_⟩
      rw [Finset.mem_biUnion]
      exact ⟨p, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hple, hp⟩, hmod⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hn.1.1, hqpdvd⟩⟩
    have hperQ : ∀ q ∈ Qset,
        ((perQP q).card : ℝ) ≤
          (N : ℝ) * ((116 + 2 * Real.log q + 36 * Real.log (Real.log N)) / ((q : ℝ) ^ 2)) := by
      intro q hq
      simp only [Qset, Finset.mem_filter, Nat.mem_primesLE] at hq
      calc ((perQP q).card : ℝ)
          ≤ ∑ p ∈ (Nat.primesLE N).filter (fun p => p % q = q - 1),
              (((Finset.Icc 1 N).filter (fun n => q * p ∣ n)).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ p ∈ (Nat.primesLE N).filter (fun p => p % q = q - 1),
              (N : ℝ) / ((q * p : ℕ) : ℝ) := by
            refine Finset.sum_le_sum fun p hp => ?_
            simp only [Finset.mem_filter, Nat.mem_primesLE] at hp
            have hqp : 1 ≤ q * p := Nat.mul_pos hq.1.2.pos hp.1.2.pos
            have hbij : (Finset.Icc 1 N).filter (fun n => q * p ∣ n) =
                (Finset.Icc 1 (N / (q * p))).image (fun k => k * (q * p)) := by
              ext n
              simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
              constructor
              · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
                exact ⟨n / (q * p), ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hqp,
                  Nat.div_le_div_right hnN⟩, Nat.div_mul_cancel hdvd⟩
              · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
                exact ⟨⟨by nlinarith, (Nat.mul_le_mul_right _ hkN).trans (Nat.div_mul_le_self N _)⟩,
                  dvd_mul_left _ k⟩
            rw [hbij, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hqp h)]
            simp only [Nat.card_Icc, Nat.add_sub_cancel]
            exact Nat.cast_div_le
        _ = ((N : ℝ) / (q : ℝ)) *
              ∑ p ∈ (Nat.primesLE N).filter (fun p => p % q = q - 1), (1 : ℝ) / (p : ℝ) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by push_cast; ring
        _ ≤ ((N : ℝ) / (q : ℝ)) *
              ((116 + 2 * Real.log q + 36 * Real.log (Real.log N)) / (q : ℝ)) := by
            gcongr
            exact sum_inv_prime_congr_neg_one_le N q (by omega) hq.1.2 (by omega)
        _ = (N : ℝ) * ((116 + 2 * Real.log q + 36 * Real.log (Real.log N)) / ((q : ℝ) ^ 2)) := by
            ring
    have hQsub : Qset ⊆ Finset.Ioc y0 N := by
      intro q hq
      simp only [Qset, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_Ioc] at hq ⊢
      exact ⟨hq.2, hq.1.1⟩
    have hloglogN_nn : 0 ≤ Real.log (Real.log (N : ℝ)) := by
      have h1 : Real.exp 1 ≤ (N : ℝ) := by
        have := Real.exp_one_lt_d9
        have : (16 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      exact Real.log_nonneg (by
        calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ ≤ Real.log (N : ℝ) := Real.log_le_log (Real.exp_pos 1) h1)
    calc (EF2b.card : ℝ)
        ≤ ((Qset.biUnion perQP).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ q ∈ Qset, ((perQP q).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ Qset, (N : ℝ) * ((116 + 2 * Real.log q + 36 * Real.log (Real.log N)) / ((q : ℝ) ^ 2)) :=
          Finset.sum_le_sum hperQ
      _ = (N : ℝ) * (116 * (∑ q ∈ Qset, (1 : ℝ) / ((q : ℝ) ^ 2)) +
            2 * (∑ q ∈ Qset, Real.log q / ((q : ℝ) ^ 2)) +
            36 * Real.log (Real.log N) * (∑ q ∈ Qset, (1 : ℝ) / ((q : ℝ) ^ 2))) := by
          rw [← Finset.mul_sum]
          congr 1
          simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun q _ => by ring
      _ ≤ (N : ℝ) * (116 * (1 / (y0 : ℝ)) + 2 * (4 / Real.sqrt y0) +
            36 * Real.log (Real.log N) * (24 / ((y0 : ℝ) * Real.log y0))) := by
          gcongr
          · calc ∑ q ∈ Qset, (1 : ℝ) / ((q : ℝ) ^ 2)
                ≤ ∑ q ∈ Finset.Ioc y0 N, (1 : ℝ) / ((q : ℝ) ^ 2) :=
                  Finset.sum_le_sum_of_subset_of_nonneg hQsub (fun _ _ _ => by positivity)
              _ ≤ 1 / (y0 : ℝ) := sum_Ioc_inv_sq_le y0 N (by omega)
          · calc ∑ q ∈ Qset, Real.log q / ((q : ℝ) ^ 2)
                ≤ ∑ q ∈ Finset.Ioc y0 N, Real.log q / ((q : ℝ) ^ 2) :=
                  Finset.sum_le_sum_of_subset_of_nonneg hQsub (fun q hq _ => by
                    rw [Finset.mem_Ioc] at hq
                    have : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
                    have := Real.log_nonneg this
                    positivity)
              _ ≤ 4 / Real.sqrt y0 := sum_Ioc_log_div_sq_le y0 N (by omega)
          · exact sum_inv_prime_sq_tail y0 N hy0
      _ = (N : ℝ) * (116 / (y0 : ℝ) + 8 / Real.sqrt y0 +
            864 * Real.log (Real.log N) / ((y0 : ℝ) * Real.log y0)) := by ring
  have hunion : ((E_F N y0).card : ℝ) ≤ (EF1.card : ℝ) + (EF2a.card : ℝ) + (EF2b.card : ℝ) := by
    have h1 : (E_F N y0).card ≤ EF1.card + (EF2a ∪ EF2b).card :=
      (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have h2 : (EF2a ∪ EF2b).card ≤ EF2a.card + EF2b.card := Finset.card_union_le _ _
    have h3 : (E_F N y0).card ≤ EF1.card + EF2a.card + EF2b.card := by omega
    exact_mod_cast h3
  have h1 : (N : ℝ) / (y0 : ℝ) + 12 * (N : ℝ) / Real.sqrt y0 +
      (N : ℝ) * (116 / (y0 : ℝ) + 8 / Real.sqrt y0 +
        864 * Real.log (Real.log N) / ((y0 : ℝ) * Real.log y0)) ≤
      (N : ℝ) * (120 / (y0 : ℝ) + 20 / Real.sqrt y0 +
        864 * Real.log (Real.log N) / ((y0 : ℝ) * Real.log y0)) := by
    have hy0_pos : (0 : ℝ) < y0 := by positivity
    have hsqy : 0 < Real.sqrt (y0 : ℝ) := Real.sqrt_pos.mpr hy0_pos
    have h1' : (N : ℝ) * (1 / (y0 : ℝ) + 116 / (y0 : ℝ)) ≤ (N : ℝ) * (120 / (y0 : ℝ)) := by
      gcongr; rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hy0_pos.le
    have h2' : (N : ℝ) * (12 / Real.sqrt y0 + 8 / Real.sqrt y0) ≤ (N : ℝ) * (20 / Real.sqrt y0) := by
      gcongr; rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hsqy.le
    have hlhs : (N : ℝ) / (y0 : ℝ) + 12 * (N : ℝ) / Real.sqrt y0 +
        (N : ℝ) * (116 / (y0 : ℝ) + 8 / Real.sqrt y0 +
          864 * Real.log (Real.log N) / ((y0 : ℝ) * Real.log y0)) =
        (N : ℝ) * (1 / (y0 : ℝ) + 116 / (y0 : ℝ)) +
        (N : ℝ) * (12 / Real.sqrt y0 + 8 / Real.sqrt y0) +
        (N : ℝ) * (864 * Real.log (Real.log N) / ((y0 : ℝ) * Real.log y0)) := by ring
    have hrhs : (N : ℝ) * (120 / (y0 : ℝ) + 20 / Real.sqrt y0 +
        864 * Real.log (Real.log N) / ((y0 : ℝ) * Real.log y0)) =
        (N : ℝ) * (120 / (y0 : ℝ)) + (N : ℝ) * (20 / Real.sqrt y0) +
        (N : ℝ) * (864 * Real.log (Real.log N) / ((y0 : ℝ) * Real.log y0)) := by ring
    linarith
  linarith

/- ## Section 4: Key Divisibility Bound for Squarefree Moduli -/

private lemma le_sigma_one_of_pos {m : ℕ} (hm : 1 ≤ m) : m ≤ σ 1 m := by
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self m (by omega))

private lemma s_mul_prime_of_not_dvd {m P : ℕ} (hm : 1 ≤ m) (hP : P.Prime) (hnd : ¬ P ∣ m) :
    Erdos955.s (m * P) = Erdos955.s m * P + σ 1 m := by
  have hcop : Nat.Coprime m P := (hP.coprime_iff_not_dvd.mpr hnd).symm
  have hsigP : σ 1 P = P + 1 := by
    rw [ArithmeticFunction.sigma_one_apply, hP.sum_divisors]
  have hsig : σ 1 (m * P) = σ 1 m * (P + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsigP]
  have hle : m ≤ σ 1 m := le_sigma_one_of_pos hm
  unfold Erdos955.s
  rw [hsig]
  zify [hle, show m * P ≤ σ 1 m * (P + 1) by nlinarith]
  ring

private lemma card_good_dvd_s_le (N y0 d : ℕ) (y_smooth : ℝ)
    (hN : 16 ≤ N) (hy : 64 ≤ y_smooth)
    (hd1 : 1 ≤ d) (hd_prime : ∀ q ∈ d.primeFactors, y0 < q)
    (hd_le : (d : ℝ) ≤ Real.sqrt y_smooth) :
    (((Good N y_smooth y0).filter (fun n => d ∣ Erdos955.s n)).card : ℝ) ≤
      18 * (N : ℝ) * (1 + Real.log N) / ((Nat.totient d : ℝ) * Real.log y_smooth) := by
  have : NeZero d := ⟨by omega⟩
  have hy_pos : 0 < y_smooth := by linarith
  have hlogy : 0 < Real.log y_smooth := Real.log_pos (by linarith)
  have hd_pos : (0 : ℝ) < d := by positivity
  have hphi_pos : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd1
  have hd_lt_y : (d : ℝ) < y_smooth := by
    have hsq : Real.sqrt y_smooth < y_smooth := by
      have : Real.sqrt y_smooth ^ 2 = y_smooth := Real.sq_sqrt hy_pos.le
      nlinarith [Real.sqrt_nonneg y_smooth]
    linarith
  -- For each m, the unique residue class a_m mod d (when Coprime (s m) d)
  let perM : ℕ → Finset ℕ := fun m =>
    (Finset.Icc 1 (N / m)).filter (fun P =>
      P.Prime ∧ y_smooth < (P : ℝ) ∧ d ∣ Erdos955.s m * P + σ 1 m ∧ Nat.Coprime (Erdos955.s m) d)
  let Gset := (Good N y_smooth y0).filter (fun n => d ∣ Erdos955.s n)
  let splitFn : ℕ → ℕ × ℕ := fun n => (n / maxPrimeFactor n, maxPrimeFactor n)
  have hmaps : ∀ n ∈ Gset, splitFn n ∈ (Finset.Icc 1 N).biUnion (fun m => ({m} : Finset ℕ) ×ˢ perM m) := by
    intro n hn
    simp only [Gset, Good, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnN⟩, hyP, hP2, hF⟩, hds⟩ := hn
    set P := maxPrimeFactor n
    have hP_ge2 : 2 ≤ P := by
      have : (64 : ℝ) < (P : ℝ) := by linarith
      exact_mod_cast (by linarith : (2 : ℝ) ≤ P)
    have hn2 : 2 ≤ n := by
      have := maxPrimeFactor_le_self n; omega
    have hP_prime : P.Prime := maxPrimeFactor_prime hn2
    have hP_dvd : P ∣ n := maxPrimeFactor_dvd hn2
    set m := n / P
    have hmP : m * P = n := Nat.div_mul_cancel hP_dvd
    have hm1 : 1 ≤ m := Nat.div_pos (Nat.le_of_dvd (by omega) hP_dvd) hP_prime.pos
    have hmN : m ≤ N := (Nat.div_le_self n P).trans hnN
    have hPnd_m : ¬ P ∣ m := by
      intro hPm
      apply hP2
      rw [← hmP, sq]
      exact Nat.mul_dvd_mul_right hPm P
    have hs_eq : Erdos955.s n = Erdos955.s m * P + σ 1 m := by
      rw [← hmP]
      exact s_mul_prime_of_not_dvd hm1 hP_prime hPnd_m
    have hcop_sm : Nat.Coprime (Erdos955.s m) d := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
      have hq_sm : q ∣ Erdos955.s m := hqdvd.trans (Nat.gcd_dvd_left _ _)
      have hq_d : q ∣ d := hqdvd.trans (Nat.gcd_dvd_right _ _)
      have hq_gt : y0 < q := hd_prime q (Nat.mem_primeFactors.mpr ⟨hq, hq_d, by omega⟩)
      have hq_sn : q ∣ Erdos955.s m * P + σ 1 m := by rw [← hs_eq]; exact hq_d.trans hds
      have hq_sigm : q ∣ σ 1 m := (Nat.dvd_add_right (hq_sm.mul_right P)).mp hq_sn
      have hsig_eq : Erdos955.s m + m = σ 1 m := Nat.sub_add_cancel (le_sigma_one_of_pos hm1)
      have hq_m : q ∣ m := (Nat.dvd_add_right hq_sm).mp (hsig_eq.symm ▸ hq_sigm)
      have hq_n : q ∣ n := by rw [← hmP]; exact hq_m.mul_right P
      have hq_sign : q ∣ σ 1 n := by
        have hcop_mP : Nat.Coprime m P := (hP_prime.coprime_iff_not_dvd.mpr hPnd_m).symm
        rw [← hmP, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop_mP]
        exact hq_sigm.mul_right _
      exact hF ⟨q, hq, hq_gt, hq_n, hq_sign⟩
    have hP_le : P ≤ N / m := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm, hmP]; exact hnN)
    rw [Finset.mem_biUnion]
    refine ⟨m, Finset.mem_Icc.mpr ⟨hm1, hmN⟩, ?_⟩
    rw [Finset.mem_product, Finset.mem_singleton]
    refine ⟨rfl, ?_⟩
    simp only [perM, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hP_prime.one_le, hP_le⟩, hP_prime, hyP, hs_eq ▸ hds, hcop_sm⟩
  have hinj : Set.InjOn splitFn Gset := by
    intro n1 hn1 n2 hn2 heq
    simp only [splitFn, Prod.mk.injEq] at heq
    simp only [Finset.mem_coe, Gset, Good, Finset.mem_filter] at hn1 hn2
    have h1 : 2 ≤ n1 := by
      have : (64 : ℝ) < (maxPrimeFactor n1 : ℝ) := by linarith [hn1.1.2.1]
      have : 2 ≤ maxPrimeFactor n1 := by exact_mod_cast (by linarith : (2 : ℝ) ≤ maxPrimeFactor n1)
      have := maxPrimeFactor_le_self n1; omega
    have h2 : 2 ≤ n2 := by
      have : (64 : ℝ) < (maxPrimeFactor n2 : ℝ) := by linarith [hn2.1.2.1]
      have : 2 ≤ maxPrimeFactor n2 := by exact_mod_cast (by linarith : (2 : ℝ) ≤ maxPrimeFactor n2)
      have := maxPrimeFactor_le_self n2; omega
    have hd1' := Nat.div_mul_cancel (maxPrimeFactor_dvd h1)
    have hd2' := Nat.div_mul_cancel (maxPrimeFactor_dvd h2)
    rw [← hd1', ← hd2', heq.1, heq.2]
  have hperM : ∀ m ∈ Finset.Icc 1 N,
      ((perM m).card : ℝ) ≤ (18 * (N : ℝ) / ((Nat.totient d : ℝ) * Real.log y_smooth)) * ((1 : ℝ) / (m : ℝ)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := hm.1
    have hm_pos : (0 : ℝ) < m := by positivity
    by_cases hne : (perM m).Nonempty
    · obtain ⟨P0, hP0⟩ := hne
      simp only [perM, Finset.mem_filter, Finset.mem_Icc] at hP0
      have hcop_sm : Nat.Coprime (Erdos955.s m) d := hP0.2.2.2.2
      have hNm_gt : y_smooth < (N : ℝ) / (m : ℝ) := by
        have h1 : (P0 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hP0.1.2
        have h2 : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := Nat.cast_div_le
        linarith [hP0.2.2.1]
      let u : (ZMod d)ˣ := ZMod.unitOfCoprime (Erdos955.s m) hcop_sm
      let a_m : ℕ := ((-(σ 1 m : ZMod d)) * (u⁻¹ : ZMod d)).val
      have hsub : perM m ⊆ (Finset.Icc 1 ⌊(N : ℝ) / (m : ℝ)⌋₊).filter (fun P => P.Prime ∧ P % d = a_m % d) := by
        intro P hP
        simp only [perM, Finset.mem_filter, Finset.mem_Icc] at hP ⊢
        refine ⟨⟨hP.1.1, ?_⟩, hP.2.1, ?_⟩
        · exact Nat.le_floor ((Nat.cast_le.mpr hP.1.2).trans Nat.cast_div_le)
        · have hz0 : ((Erdos955.s m * P + σ 1 m : ℕ) : ZMod d) = 0 :=
            (ZMod.natCast_eq_zero_iff _ d).mpr hP.2.2.2.1
          push_cast at hz0
          have hu_eq : (u : ZMod d) = (Erdos955.s m : ZMod d) := ZMod.coe_unitOfCoprime _ _
          have hP_eq : (P : ZMod d) = (-(σ 1 m : ZMod d)) * (u⁻¹ : ZMod d) := by
            have h1 : (u : ZMod d) * (P : ZMod d) = -(σ 1 m : ZMod d) := by
              rw [hu_eq]; exact eq_neg_of_add_eq_zero_left hz0
            calc (P : ZMod d) = ((u⁻¹ : (ZMod d)ˣ) : ZMod d) * ((u : ZMod d) * (P : ZMod d)) := by
                  rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
              _ = ((u⁻¹ : (ZMod d)ˣ) : ZMod d) * (-(σ 1 m : ZMod d)) := by rw [h1]
              _ = (-(σ 1 m : ZMod d)) * ((u⁻¹ : (ZMod d)ˣ) : ZMod d) := mul_comm _ _
          have ha_eq : (a_m : ZMod d) = (-(σ 1 m : ZMod d)) * (u⁻¹ : ZMod d) := ZMod.natCast_zmod_val _
          exact (ZMod.natCast_eq_natCast_iff' P a_m d).mp (hP_eq.trans ha_eq.symm)
      have hXd : 8 * (d : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
        have hsqrt8 : 8 ≤ Real.sqrt y_smooth := by
          calc (8 : ℝ) = Real.sqrt 64 := by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
            _ ≤ Real.sqrt y_smooth := Real.sqrt_le_sqrt hy
        have h1 : 8 * (d : ℝ) ≤ y_smooth := by
          calc 8 * (d : ℝ) ≤ Real.sqrt y_smooth * Real.sqrt y_smooth :=
                mul_le_mul hsqrt8 hd_le hd_pos.le (Real.sqrt_nonneg _)
            _ = y_smooth := Real.mul_self_sqrt hy_pos.le
        linarith
      have hbt := brun_titchmarsh ((N : ℝ) / (m : ℝ)) d a_m hd1 hXd
      have hlog_ge : (1 / 2 : ℝ) * Real.log y_smooth ≤ Real.log (((N : ℝ) / (m : ℝ)) / (d : ℝ)) := by
        have h1 : Real.sqrt y_smooth ≤ ((N : ℝ) / (m : ℝ)) / (d : ℝ) := by
          rw [le_div_iff₀ hd_pos]
          have h2 : Real.sqrt y_smooth * (d : ℝ) ≤ Real.sqrt y_smooth * Real.sqrt y_smooth :=
            mul_le_mul_of_nonneg_left hd_le (Real.sqrt_nonneg _)
          rw [Real.mul_self_sqrt hy_pos.le] at h2
          linarith
        have h2 : Real.log (Real.sqrt y_smooth) = (1 / 2 : ℝ) * Real.log y_smooth := by
          rw [Real.log_sqrt hy_pos.le]; ring
        rw [← h2]
        exact Real.log_le_log (Real.sqrt_pos.mpr hy_pos) h1
      calc ((perM m).card : ℝ)
          ≤ (((Finset.Icc 1 ⌊(N : ℝ) / (m : ℝ)⌋₊).filter
              (fun P => P.Prime ∧ P % d = a_m % d)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ 9 * ((N : ℝ) / (m : ℝ)) / ((Nat.totient d : ℝ) * Real.log (((N : ℝ) / (m : ℝ)) / (d : ℝ))) := hbt
        _ ≤ 9 * ((N : ℝ) / (m : ℝ)) / ((Nat.totient d : ℝ) * ((1 / 2 : ℝ) * Real.log y_smooth)) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hlog_ge hphi_pos.le
        _ = (18 * (N : ℝ) / ((Nat.totient d : ℝ) * Real.log y_smooth)) * ((1 : ℝ) / (m : ℝ)) := by
            ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      positivity
  calc (Gset.card : ℝ)
      = ((Gset.image splitFn).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ ((((Finset.Icc 1 N).biUnion (fun m => ({m} : Finset ℕ) ×ˢ perM m)).card : ℝ)) := by
        exact_mod_cast Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)
    _ ≤ ∑ m ∈ Finset.Icc 1 N, (((({m} : Finset ℕ) ×ˢ perM m).card : ℝ)) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ m ∈ Finset.Icc 1 N, ((perM m).card : ℝ) := by
        refine Finset.sum_congr rfl fun m _ => by simp
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
          (18 * (N : ℝ) / ((Nat.totient d : ℝ) * Real.log y_smooth)) * ((1 : ℝ) / (m : ℝ)) :=
        Finset.sum_le_sum hperM
    _ = (18 * (N : ℝ) / ((Nat.totient d : ℝ) * Real.log y_smooth)) *
          ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) := by rw [← Finset.mul_sum]
    _ ≤ (18 * (N : ℝ) / ((Nat.totient d : ℝ) * Real.log y_smooth)) * (1 + Real.log N) := by
        gcongr; exact sum_Icc_inv_le_one_add_log N
    _ = 18 * (N : ℝ) * (1 + Real.log N) / ((Nat.totient d : ℝ) * Real.log y_smooth) := by ring

/- ## Section 5: k-th Moment Bound and Density Zero Proof -/

private lemma factorial_mul_sum_powersetCard_prod_le {α : Type*} [DecidableEq α]
    (F : Finset α) (f : α → ℝ) (hf : ∀ x ∈ F, 0 ≤ f x) (k : ℕ) :
    (k.factorial : ℝ) * ∑ T ∈ F.powersetCard k, ∏ x ∈ T, f x ≤ (∑ x ∈ F, f x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ((k + 1 : ℕ) : ℝ) * ∑ T ∈ F.powersetCard (k + 1), ∏ x ∈ T, f x ≤
        (∑ x ∈ F, f x) * ∑ S ∈ F.powersetCard k, ∏ y ∈ S, f y := by
      have h1 : ((k + 1 : ℕ) : ℝ) * ∑ T ∈ F.powersetCard (k + 1), ∏ x ∈ T, f x =
          ∑ T ∈ F.powersetCard (k + 1), ∑ x ∈ T, f x * ∏ y ∈ T.erase x, f y := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [Finset.mem_powersetCard] at hT
        have hinner : ∀ x ∈ T, f x * ∏ y ∈ T.erase x, f y = ∏ y ∈ T, f y :=
          fun x hx => Finset.mul_prod_erase T f hx
        rw [Finset.sum_congr rfl hinner, Finset.sum_const, hT.2, nsmul_eq_mul]
      rw [h1]
      have hbij : ∑ T ∈ F.powersetCard (k + 1), ∑ x ∈ T, f x * ∏ y ∈ T.erase x, f y =
          ∑ S ∈ F.powersetCard k, ∑ x ∈ F \ S, f x * ∏ y ∈ S, f y := by
        rw [← Finset.sum_sigma (F.powersetCard (k + 1)) (fun T => T) (fun p => f p.2 * ∏ y ∈ p.1.erase p.2, f y),
          ← Finset.sum_sigma (F.powersetCard k) (fun S => F \ S) (fun p => f p.2 * ∏ y ∈ p.1, f y)]
        refine Finset.sum_bij (fun p _ => ⟨p.1.erase p.2, p.2⟩) ?_ ?_ ?_ ?_
        · intro ⟨T, x⟩ hp
          rw [Finset.mem_sigma, Finset.mem_powersetCard] at hp
          rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff]
          refine ⟨⟨(Finset.erase_subset x T).trans hp.1.1, by
            rw [Finset.card_erase_of_mem hp.2, hp.1.2]; omega⟩,
            hp.1.1 hp.2, Finset.notMem_erase x T⟩
        · intro ⟨T1, x1⟩ hp1 ⟨T2, x2⟩ hp2 heq
          rw [Finset.mem_sigma] at hp1 hp2
          simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
          rcases heq with ⟨herase, rfl⟩
          dsimp only at hp1 hp2
          have hT : T1 = T2 := by
            rw [← Finset.insert_erase hp1.2, ← Finset.insert_erase hp2.2, herase]
          subst hT; rfl
        · intro ⟨S, x⟩ hp
          rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hp
          refine ⟨⟨insert x S, x⟩, ?_, ?_⟩
          · rw [Finset.mem_sigma, Finset.mem_powersetCard]
            refine ⟨⟨Finset.insert_subset hp.2.1 hp.1.1, ?_⟩, Finset.mem_insert_self x S⟩
            rw [Finset.card_insert_of_notMem hp.2.2, hp.1.2]
          · simp [Finset.erase_insert hp.2.2]
        · intro ⟨T, x⟩ _; rfl
      rw [hbij]
      calc ∑ S ∈ F.powersetCard k, ∑ x ∈ F \ S, f x * ∏ y ∈ S, f y
          ≤ ∑ S ∈ F.powersetCard k, ∑ x ∈ F, f x * ∏ y ∈ S, f y := by
            refine Finset.sum_le_sum fun S hS => ?_
            rw [Finset.mem_powersetCard] at hS
            refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun x hx _ => ?_
            exact mul_nonneg (hf x hx) (Finset.prod_nonneg fun y hy => hf y (hS.1 hy))
        _ = (∑ x ∈ F, f x) * ∑ S ∈ F.powersetCard k, ∏ y ∈ S, f y := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun S _ => (Finset.sum_mul ..).symm
    have hfac : ((k + 1).factorial : ℝ) = (k.factorial : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac, mul_assoc, pow_succ']
    calc (k.factorial : ℝ) * (((k + 1 : ℕ) : ℝ) * ∑ T ∈ F.powersetCard (k + 1), ∏ x ∈ T, f x)
        ≤ (k.factorial : ℝ) * ((∑ x ∈ F, f x) * ∑ S ∈ F.powersetCard k, ∏ y ∈ S, f y) := by
          gcongr
      _ = (∑ x ∈ F, f x) * ((k.factorial : ℝ) * ∑ S ∈ F.powersetCard k, ∏ y ∈ S, f y) := by ring
      _ ≤ (∑ x ∈ F, f x) * (∑ x ∈ F, f x) ^ k := by
          apply mul_le_mul_of_nonneg_left ih (Finset.sum_nonneg hf)

private lemma cardDistinctFactors_eq_card_primeFactors (n : ℕ) :
    ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

private lemma s_le_sq (n : ℕ) : Erdos955.s n ≤ n ^ 2 := by
  by_cases hn : n = 0
  · subst hn; simp [Erdos955.s]
  have h1 : Erdos955.s n ≤ σ 1 n := Nat.sub_le _ _
  have h2 : σ 1 n ≤ n ^ 2 := by
    rw [ArithmeticFunction.sigma_one_apply]
    calc ∑ d ∈ n.divisors, d
        ≤ ∑ _d ∈ n.divisors, n :=
          Finset.sum_le_sum fun d hd => Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp hd).1
      _ = n.divisors.card * n := by simp
      _ ≤ n * n := by
          apply Nat.mul_le_mul_right
          have hsub : n.divisors ⊆ Finset.Icc 1 n := by
            intro d hd
            rw [Nat.mem_divisors] at hd
            rw [Finset.mem_Icc]
            exact ⟨Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero hn),
              Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd.1⟩
          exact (Finset.card_le_card hsub).trans (by simp)
      _ = n ^ 2 := by ring
  exact h1.trans h2

private lemma descFactorial_ge_sub_pow (M k : ℕ) (hk : k ≤ M) :
    (M - k) ^ k ≤ M.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, pow_succ']
    have h1 : (M - (k + 1)) ^ k ≤ (M - k) ^ k := Nat.pow_le_pow_left (by omega) k
    have h2 : M - (k + 1) ≤ M - k := by omega
    calc (M - (k + 1)) * (M - (k + 1)) ^ k
        ≤ (M - k) * (M - k) ^ k := Nat.mul_le_mul h2 h1
      _ ≤ (M - k) * M.descFactorial k := Nat.mul_le_mul_left _ (ih (by omega))

private lemma exp_ge_cube_div_six {t : ℝ} (ht : 0 ≤ t) : t ^ 3 / 6 ≤ Real.exp t := by
  have h := Real.sum_le_exp_of_nonneg ht 4
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.factorial, pow_zero, pow_one, Nat.cast_one, div_one] at h
  have h1 : 0 ≤ t ^ 2 / (2 : ℝ) := by positivity
  linarith

private lemma card_A_good_div_le (N y0 z k M : ℕ) (δ y_smooth : ℝ)
    (hN16 : 16 ≤ N) (hδ : 0 < δ) (hy64 : 64 ≤ y_smooth)
    (hL1_gt1 : 1 < Real.log (N : ℝ))
    (hL2_pos : 0 < Real.log (Real.log (N : ℝ)))
    (hL3_ge100 : 100 ≤ Real.log (Real.log (Real.log (N : ℝ))))
    (hL3_ge_d : 1000 / δ ≤ Real.log (Real.log (Real.log (N : ℝ))))
    (hy_smooth_log : Real.log y_smooth = Real.log (N : ℝ) / Real.log (Real.log (Real.log (N : ℝ))))
    (hz_le_N : z ≤ N)
    (hzk_le : (z : ℝ) ^ k ≤ Real.sqrt y_smooth)
    (hk_le : (k : ℝ) ≤ δ * Real.log (Real.log (N : ℝ)) / (64 * Real.log (Real.log (Real.log (N : ℝ)))))
    (hk_ge : δ * Real.log (Real.log (N : ℝ)) / (128 * Real.log (Real.log (Real.log (N : ℝ)))) ≤ (k : ℝ))
    (hM_gt : (1 + δ / 2) * Real.log (Real.log (N : ℝ)) < (M : ℝ)) :
    ((((Good N y_smooth y0).filter
        (fun n => M ≤ ((Erdos955.s n).primeFactors ∩
          ((Nat.primesLE z).filter (fun p => y0 < p))).card)).card : ℝ) / (N : ℝ)) ≤
      30000 / ((-Real.log ((1 + δ / 8) / (1 + 3 * δ / 8))) * δ *
        Real.log (Real.log (Real.log (N : ℝ)))) := by
  set L1 : ℝ := Real.log (N : ℝ)
  set L2 : ℝ := Real.log L1
  set L3 : ℝ := Real.log L2
  set r : ℝ := (1 + δ / 8) / (1 + 3 * δ / 8)
  set alpha : ℝ := -Real.log r
  set P_set : Finset ℕ := (Nat.primesLE z).filter (fun p => y0 < p)
  set A_good : Finset ℕ := (Good N y_smooth y0).filter
    (fun n => M ≤ ((Erdos955.s n).primeFactors ∩ P_set).card)
  have hN_pos : (0 : ℝ) < N := by positivity
  have hr_pos : 0 < r := by positivity
  have hr_lt1 : r < 1 := by
    dsimp only [r]; rw [div_lt_one (by positivity)]; linarith
  have halpha_pos : 0 < alpha := by
    dsimp only [alpha]; linarith [Real.log_neg hr_pos hr_lt1]
  have hL2_eq_exp : L2 = Real.exp L3 := (Real.exp_log hL2_pos).symm
  have hL2_ge_cube : L3 ^ 3 / 6 ≤ L2 := hL2_eq_exp ▸ exp_ge_cube_div_six (by linarith)
  have hL3_sq : 10000 ≤ L3 ^ 2 := by nlinarith
  have hL2_ge_1000 : 1000 * L3 ≤ L2 := by
    have : 1000 * L3 ≤ L3 ^ 3 / 6 := by nlinarith
    linarith
  have hL3d : 1000 ≤ L3 * δ := (div_le_iff₀ hδ).mp hL3_ge_d
  have hdouble : (Nat.choose M k : ℝ) * (A_good.card : ℝ) ≤
      ∑ T ∈ P_set.powersetCard k,
        (((Good N y_smooth y0).filter (fun n => (∏ p ∈ T, p) ∣ Erdos955.s n)).card : ℝ) := by
    have hleft : (Nat.choose M k : ℝ) * (A_good.card : ℝ) ≤
        ∑ n ∈ A_good,
          ((((P_set.powersetCard k).filter (fun T => (∏ p ∈ T, p) ∣ Erdos955.s n)).card : ℝ)) := by
      rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun n hn => ?_
      simp only [A_good, Finset.mem_filter] at hn
      have hsub : ((Erdos955.s n).primeFactors ∩ P_set).powersetCard k ⊆
          (P_set.powersetCard k).filter (fun T => (∏ p ∈ T, p) ∣ Erdos955.s n) := by
        intro T hT
        rw [Finset.mem_powersetCard] at hT
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        have hT_P : T ⊆ P_set := hT.1.trans Finset.inter_subset_right
        have hT_pf : T ⊆ (Erdos955.s n).primeFactors := hT.1.trans Finset.inter_subset_left
        exact ⟨⟨hT_P, hT.2⟩,
          (Finset.prod_dvd_prod_of_subset T _ id hT_pf).trans (Nat.prod_primeFactors_dvd _)⟩
      calc (Nat.choose M k : ℝ)
          ≤ (Nat.choose ((Erdos955.s n).primeFactors ∩ P_set).card k : ℝ) := by
            exact_mod_cast Nat.choose_le_choose k hn.2
        _ = ((((Erdos955.s n).primeFactors ∩ P_set).powersetCard k).card : ℝ) := by
            rw [Finset.card_powersetCard]
        _ ≤ ((((P_set.powersetCard k).filter (fun T => (∏ p ∈ T, p) ∣ Erdos955.s n)).card : ℝ)) := by
            exact_mod_cast Finset.card_le_card hsub
    have hswap : ∑ n ∈ A_good,
          ((((P_set.powersetCard k).filter (fun T => (∏ p ∈ T, p) ∣ Erdos955.s n)).card : ℝ)) ≤
        ∑ T ∈ P_set.powersetCard k,
          (((Good N y_smooth y0).filter (fun n => (∏ p ∈ T, p) ∣ Erdos955.s n)).card : ℝ) := by
      calc ∑ n ∈ A_good,
            ((((P_set.powersetCard k).filter (fun T => (∏ p ∈ T, p) ∣ Erdos955.s n)).card : ℝ))
          ≤ ∑ n ∈ Good N y_smooth y0,
              ((((P_set.powersetCard k).filter (fun T => (∏ p ∈ T, p) ∣ Erdos955.s n)).card : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
        _ = ∑ n ∈ Good N y_smooth y0, ∑ T ∈ P_set.powersetCard k,
              if (∏ p ∈ T, p) ∣ Erdos955.s n then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl fun n _ => by simp [Finset.sum_boole]
        _ = ∑ T ∈ P_set.powersetCard k, ∑ n ∈ Good N y_smooth y0,
              if (∏ p ∈ T, p) ∣ Erdos955.s n then (1 : ℝ) else 0 := Finset.sum_comm
        _ = ∑ T ∈ P_set.powersetCard k,
              (((Good N y_smooth y0).filter (fun n => (∏ p ∈ T, p) ∣ Erdos955.s n)).card : ℝ) := by
            refine Finset.sum_congr rfl fun T _ => by simp [Finset.sum_boole]
    exact hleft.trans hswap
  have hT_bd : ∀ T ∈ P_set.powersetCard k,
      (((Good N y_smooth y0).filter (fun n => (∏ p ∈ T, p) ∣ Erdos955.s n)).card : ℝ) ≤
        36 * (N : ℝ) * L3 * ∏ p ∈ T, ((1 : ℝ) / ((p : ℝ) - 1)) := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    set d := ∏ p ∈ T, p
    have hT_prime : ∀ p ∈ T, p.Prime := fun p hp =>
      Nat.prime_of_mem_primesLE (Finset.mem_filter.mp (hT.1 hp)).1
    have hd1 : 1 ≤ d := Finset.prod_pos fun p hp => (hT_prime p hp).pos
    have hd_pf : d.primeFactors = T := Nat.primeFactors_prod hT_prime
    have hd_gt : ∀ q ∈ d.primeFactors, y0 < q := by
      intro q hq; rw [hd_pf] at hq
      exact (Finset.mem_filter.mp (hT.1 hq)).2
    have hd_le : (d : ℝ) ≤ Real.sqrt y_smooth := by
      have h1 : (d : ℝ) ≤ (z : ℝ) ^ k := by
        dsimp only [d]
        push_cast
        calc ∏ p ∈ T, (p : ℝ) ≤ ∏ _p ∈ T, (z : ℝ) := by
              refine Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun p hp => ?_
              exact_mod_cast Nat.le_of_mem_primesLE (Finset.mem_filter.mp (hT.1 hp)).1
          _ = (z : ℝ) ^ T.card := by simp
          _ = (z : ℝ) ^ k := by rw [hT.2]
      exact h1.trans hzk_le
    have hd_sq : Squarefree d := by
      dsimp only [d]
      rw [Nat.squarefree_iff_prime_squarefree]
      intro q hq hq2
      have hqmem : q ∈ T := by
        rw [← hd_pf]
        exact Nat.mem_primeFactors.mpr ⟨hq, (dvd_mul_left q q).trans hq2, by omega⟩
      have hprod_eq : ∏ p ∈ T, p = q * ∏ p ∈ T.erase q, p :=
        (Finset.mul_prod_erase T id hqmem).symm
      rw [hprod_eq] at hq2
      have hq_rest : q ∣ ∏ p ∈ T.erase q, p := (Nat.mul_dvd_mul_iff_left hq.pos).mp hq2
      rw [hq.prime.dvd_finsetProd_iff] at hq_rest
      obtain ⟨p, hp, hqp⟩ := hq_rest
      rw [Finset.mem_erase] at hp
      exact hp.1 ((Nat.prime_dvd_prime_iff_eq hq (hT_prime p hp.2)).mp hqp).symm
    have hphi_d : (Nat.totient d : ℝ) = ∏ p ∈ T, ((p : ℝ) - 1) := by
      rw [squarefree_totient_eq_prod d hd_sq, hd_pf]
      push_cast
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.cast_sub (hT_prime p hp).one_le, Nat.cast_one]
    have hdiv_bd := card_good_dvd_s_le N y0 d y_smooth hN16 hy64 hd1 hd_gt hd_le
    rw [hy_smooth_log, hphi_d] at hdiv_bd
    have h1L1 : 1 + L1 ≤ 2 * L1 := by linarith
    have hprod_pos : 0 < ∏ p ∈ T, ((p : ℝ) - 1) := Finset.prod_pos fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (hT_prime p hp).two_le
      linarith
    calc (((Good N y_smooth y0).filter (fun n => d ∣ Erdos955.s n)).card : ℝ)
        ≤ 18 * (N : ℝ) * (1 + L1) / ((∏ p ∈ T, ((p : ℝ) - 1)) * (L1 / L3)) := hdiv_bd
      _ ≤ 18 * (N : ℝ) * (2 * L1) / ((∏ p ∈ T, ((p : ℝ) - 1)) * (L1 / L3)) := by gcongr
      _ = 36 * (N : ℝ) * L3 / ∏ p ∈ T, ((p : ℝ) - 1) := by
          field_simp [hprod_pos.ne', (by linarith : L1 ≠ 0), (by linarith : L3 ≠ 0)]
          ring
      _ = 36 * (N : ℝ) * L3 * ∏ p ∈ T, ((1 : ℝ) / ((p : ℝ) - 1)) := by
          rw [Finset.prod_div_distrib, Finset.prod_const_one]; ring
  have hsum_P : ∑ p ∈ P_set, (1 : ℝ) / ((p : ℝ) - 1) ≤ L2 + 11 := by
    have hsub : P_set ⊆ Nat.primesLE N :=
      (Finset.filter_subset _ _).trans (Nat.primesLE_mono hz_le_N)
    calc ∑ p ∈ P_set, (1 : ℝ) / ((p : ℝ) - 1)
        ≤ ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) - 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => by
            have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
            exact div_nonneg zero_le_one (by linarith)
      _ ≤ L2 + 11 := sum_inv_prime_sub_one_le N (by omega)
  have hk_small : (k : ℝ) ≤ (δ / 8) * L2 := by
    calc (k : ℝ) ≤ δ * L2 / (64 * L3) := hk_le
      _ ≤ (δ / 8) * L2 := by
          rw [div_le_iff₀ (by positivity)]
          have h1 : (δ / 8) * L2 * (64 * L3) = (8 * L3) * (δ * L2) := by ring
          have h2 : 0 < δ * L2 := by positivity
          nlinarith only [h1, h2, hL3_ge100]
  have hMk_le : k ≤ M := by
    have h1 : (k : ℝ) ≤ (M : ℝ) := by linarith
    exact_mod_cast h1
  have hM_sub_k_ge : (1 + 3 * δ / 8) * L2 ≤ ((M - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hMk_le]
    linarith
  have hL2_11_le : L2 + 11 ≤ (1 + δ / 8) * L2 := by
    have : 1000 * 1000 ≤ δ * L2 := by nlinarith
    nlinarith
  have hM_sub_k_pos : 0 < ((M - k : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hM_sub_k_ge
  have hmain_k : (((M - k : ℕ) : ℝ) ^ k) * (A_good.card : ℝ) ≤
      36 * (N : ℝ) * L3 * (L2 + 11) ^ k := by
    have h1 : (((M - k : ℕ) : ℝ) ^ k) ≤ (k.factorial : ℝ) * (Nat.choose M k : ℝ) := by
      have := descFactorial_ge_sub_pow M k hMk_le
      rw [Nat.descFactorial_eq_factorial_mul_choose] at this
      exact_mod_cast this
    calc (((M - k : ℕ) : ℝ) ^ k) * (A_good.card : ℝ)
        ≤ ((k.factorial : ℝ) * (Nat.choose M k : ℝ)) * (A_good.card : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      _ = (k.factorial : ℝ) * ((Nat.choose M k : ℝ) * (A_good.card : ℝ)) := by ring
      _ ≤ (k.factorial : ℝ) * ∑ T ∈ P_set.powersetCard k,
            36 * (N : ℝ) * L3 * ∏ p ∈ T, ((1 : ℝ) / ((p : ℝ) - 1)) := by
          gcongr
          exact hdouble.trans (Finset.sum_le_sum hT_bd)
      _ = 36 * (N : ℝ) * L3 * ((k.factorial : ℝ) * ∑ T ∈ P_set.powersetCard k,
            ∏ p ∈ T, ((1 : ℝ) / ((p : ℝ) - 1))) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ 36 * (N : ℝ) * L3 * (∑ p ∈ P_set, (1 : ℝ) / ((p : ℝ) - 1)) ^ k := by
          gcongr
          exact factorial_mul_sum_powersetCard_prod_le P_set (fun p => (1 : ℝ) / ((p : ℝ) - 1))
            (fun p hp => by
              have : (2 : ℝ) ≤ p := by
                exact_mod_cast (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).two_le
              exact div_nonneg zero_le_one (by linarith)) k
      _ ≤ 36 * (N : ℝ) * L3 * (L2 + 11) ^ k := by
          gcongr
          exact Finset.sum_nonneg fun p hp => by
            have : (2 : ℝ) ≤ p := by
              exact_mod_cast (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).two_le
            exact div_nonneg zero_le_one (by linarith)
  have hratio : (L2 + 11) / ((M - k : ℕ) : ℝ) ≤ r := by
    dsimp only [r]
    calc (L2 + 11) / ((M - k : ℕ) : ℝ)
        ≤ ((1 + δ / 8) * L2) / ((1 + 3 * δ / 8) * L2) :=
          div_le_div₀ (by positivity) hL2_11_le (by positivity) hM_sub_k_ge
      _ = (1 + δ / 8) / (1 + 3 * δ / 8) := by field_simp [hL2_pos.ne']
  have hA_div : (A_good.card : ℝ) / (N : ℝ) ≤ 36 * L3 * r ^ k := by
    have h1 : (A_good.card : ℝ) / (N : ℝ) ≤
        36 * L3 * ((L2 + 11) / ((M - k : ℕ) : ℝ)) ^ k := by
      rw [div_pow, div_le_iff₀ hN_pos]
      have h2 := (le_div_iff₀ (pow_pos hM_sub_k_pos k)).mpr
        (by linarith : (A_good.card : ℝ) * ((M - k : ℕ) : ℝ) ^ k ≤ 36 * (N : ℝ) * L3 * (L2 + 11) ^ k)
      calc (A_good.card : ℝ) ≤ 36 * (N : ℝ) * L3 * (L2 + 11) ^ k / ((M - k : ℕ) : ℝ) ^ k := h2
        _ = 36 * L3 * ((L2 + 11) ^ k / ((M - k : ℕ) : ℝ) ^ k) * (N : ℝ) := by ring
    exact h1.trans (by gcongr)
  have hk_lb : (δ / 768) * L3 ^ 2 ≤ (k : ℝ) := by
    have h1 : δ * (L3 ^ 3 / 6) / (128 * L3) ≤ δ * L2 / (128 * L3) := by gcongr
    have h2 : δ * (L3 ^ 3 / 6) / (128 * L3) = (δ / 768) * L3 ^ 2 := by
      field_simp [(by linarith : L3 ≠ 0)]; ring
    linarith
  have hk_pos_R : 0 < (k : ℝ) := lt_of_lt_of_le (by positivity) hk_lb
  have hrk_le : r ^ k ≤ 1 / (alpha * (k : ℝ)) := by
    have hrk_eq : r ^ k = Real.exp (-(alpha * (k : ℝ))) := by
      dsimp only [alpha]
      conv_lhs => rw [← Real.exp_log hr_pos]
      rw [← Real.exp_nat_mul]
      congr 1; ring
    rw [hrk_eq, Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    linarith [Real.add_one_le_exp (alpha * (k : ℝ))]
  calc (A_good.card : ℝ) / (N : ℝ)
      ≤ 36 * L3 * r ^ k := hA_div
    _ ≤ 36 * L3 * (1 / (alpha * (k : ℝ))) := by gcongr
    _ ≤ 36 * L3 * (1 / (alpha * ((δ / 768) * L3 ^ 2))) := by gcongr
    _ = 27648 / (alpha * δ * L3) := by
        field_simp [halpha_pos.ne', hδ.ne', (by linarith : L3 ≠ 0)]
        norm_num
    _ ≤ 30000 / (alpha * δ * L3) :=
        div_le_div_of_nonneg_right (by norm_num) (by positivity)

private lemma upper_tail_fixed_eps_le_one (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    {n : ℕ | (1 + ε) * Real.log (Real.log (n : ℝ)) <
      (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)}.HasDensity 0 := by
  set S_bad : Set ℕ := {n : ℕ | (1 + ε) * Real.log (Real.log (n : ℝ)) <
    (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)}
  rw [Set.HasDensity, Metric.tendsto_atTop]
  intro η hη
  set δ : ℝ := ε / 2
  have hδ : 0 < δ := by positivity
  have hL1 : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL2 : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL1
  have hL3 : Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL2
  set r : ℝ := (1 + δ / 8) / (1 + 3 * δ / 8)
  have hr_pos : 0 < r := by positivity
  have hr_lt1 : r < 1 := by
    dsimp only [r]; rw [div_lt_one (by positivity)]; linarith
  set alpha : ℝ := -Real.log r
  have halpha_pos : 0 < alpha := by
    dsimp only [alpha]; linarith [Real.log_neg hr_pos hr_lt1]
  have hEv1 : ∀ᶠ N : ℕ in atTop, 16 ≤ N := eventually_ge_atTop 16
  have hEv2 : ∀ᶠ N : ℕ in atTop, (1 + ε) * Real.log 2 ≤ (ε / 2) * Real.log (Real.log (N : ℝ)) :=
    (hL2.eventually_ge_atTop ((1 + ε) * Real.log 2 / (ε / 2))).mono fun N hN => by
      have := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ ε / 2)
      field_simp [show ε / 2 ≠ 0 by positivity] at this ⊢
      linarith
  have hEv3 : ∀ᶠ N : ℕ in atTop, max 100 (1000 / δ) ≤ Real.log (Real.log (Real.log (N : ℝ))) :=
    hL3.eventually_ge_atTop (max 100 (1000 / δ))
  have hEv4 : ∀ᶠ N : ℕ in atTop,
      (6 / (Real.log (Real.log (Real.log (N : ℝ))) - 1)) ≤ δ / 8 := by
    filter_upwards [hL3.eventually_ge_atTop (48 / δ + 2)] with N hN
    have hden : 0 < Real.log (Real.log (Real.log (N : ℝ))) - 1 := by
      have : 0 < 48 / δ := by positivity
      linarith
    rw [div_le_iff₀ hden]
    have hmul : (δ / 8) * (48 / δ) = 6 := by field_simp [hδ.ne']; ring
    nlinarith
  have hEv5 : ∀ᶠ N : ℕ in atTop,
      10000 / Real.log (Real.log (Real.log (N : ℝ))) +
      10000 / Real.sqrt (Real.log (Real.log (N : ℝ)) / 2) +
      30000 / (alpha * δ * Real.log (Real.log (Real.log (N : ℝ)))) +
      10 / Real.sqrt (N : ℝ) < η := by
    have hsqrt_top : Tendsto Real.sqrt atTop atTop :=
      Filter.tendsto_atTop_atTop.mpr fun b => ⟨(max b 0) ^ 2, fun x hx => by
        calc b ≤ max b 0 := le_max_left _ _
          _ = Real.sqrt ((max b 0) ^ 2) := (Real.sqrt_sq (le_max_right _ _)).symm
          _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx⟩
    have ht1 : Tendsto (fun N : ℕ => 10000 / Real.log (Real.log (Real.log (N : ℝ)))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hL3
    have ht2 : Tendsto (fun N : ℕ => 10000 / Real.sqrt (Real.log (Real.log (N : ℝ)) / 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hsqrt_top.comp (hL2.atTop_div_const (by norm_num : (0 : ℝ) < 2)))
    have ht3 : Tendsto (fun N : ℕ => 30000 / (alpha * δ * Real.log (Real.log (Real.log (N : ℝ))))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Filter.Tendsto.const_mul_atTop (by positivity) hL3)
    have ht4 : Tendsto (fun N : ℕ => 10 / Real.sqrt (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hsqrt_top.comp tendsto_natCast_atTop_atTop)
    have hsum := ((ht1.add ht2).add ht3).add ht4
    simp only [add_zero] at hsum
    exact hsum.eventually (gt_mem_nhds hη)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hEv1.and (hEv2.and (hEv3.and (hEv4.and hEv5))))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hN16, hN2, hN3, hN4, hN5⟩ := hN0 N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
    simp only [Set.partialDensity]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  set L1 : ℝ := Real.log (N : ℝ)
  set L2 : ℝ := Real.log L1
  set L3 : ℝ := Real.log L2
  have hN_pos : (0 : ℝ) < N := by positivity
  have hL1_gt1 : 1 < L1 := by
    have h1 : Real.exp 1 < (N : ℝ) := by
      have := Real.exp_one_lt_d9
      have : (16 : ℝ) ≤ N := by exact_mod_cast hN16
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < L1 := Real.log_lt_log (Real.exp_pos 1) h1
  have hL2_pos : 0 < L2 := Real.log_pos hL1_gt1
  have hL3_ge100 : 100 ≤ L3 := (le_max_left _ _).trans hN3
  have hL3_ge_d : 1000 / δ ≤ L3 := (le_max_right _ _).trans hN3
  have hL3d : 1000 ≤ L3 * δ := (div_le_iff₀ hδ).mp hL3_ge_d
  have hL2_ge_cube : L3 ^ 3 / 6 ≤ L2 := (Real.exp_log hL2_pos) ▸ exp_ge_cube_div_six (by linarith)
  have hL3_sq : 10000 ≤ L3 ^ 2 := by nlinarith
  have hL2_ge_1000 : 1000 * L3 ≤ L2 := by
    have : 1000 * L3 ≤ L3 ^ 3 / 6 := by nlinarith
    linarith
  have hL1_pos : 0 < L1 := by linarith only [hL1_gt1]
  have hL1_eq_exp : L1 = Real.exp L2 := (Real.exp_log hL1_pos).symm
  have hL1_ge_cube : L2 ^ 3 / 6 ≤ L1 := hL1_eq_exp ▸ exp_ge_cube_div_six hL2_pos.le
  have hL2_sq : 10000 ≤ L2 ^ 2 := by nlinarith only [hL2_ge_1000, hL3_ge100]
  have hL1_ge_1000 : 1000 * L2 ≤ L1 := by
    have : 1000 * L2 ≤ L2 ^ 3 / 6 := by nlinarith only [hL2_sq, hL2_pos]
    linarith only [this, hL1_ge_cube]
  set y_smooth : ℝ := (N : ℝ) ^ (1 / L3)
  set y0 : ℕ := ⌊L2⌋₊
  set z : ℕ := ⌊Real.exp (16 * L1 / (δ * L2))⌋₊
  set k : ℕ := ⌊δ * L2 / (64 * L3)⌋₊
  set M : ℕ := ⌊(1 + δ / 2) * L2⌋₊ + 1
  have hy_smooth_log : Real.log y_smooth = L1 / L3 := by
    dsimp only [y_smooth]; rw [Real.log_rpow hN_pos]; ring
  have hlog2_lt1 : Real.log 2 < 1 := by
    calc Real.log 2 < Real.log (Real.exp 1) :=
          Real.log_lt_log (by norm_num) (lt_trans (by norm_num) Real.exp_one_gt_d9)
      _ = 1 := Real.log_exp 1
  have hy_smooth_ge64 : 64 ≤ y_smooth := by
    have hlog64 : Real.log 64 ≤ L1 / L3 := by
      have h1 : Real.log 64 ≤ 6 := by
        rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
        norm_num
        linarith only [hlog2_lt1]
      have h2 : 6 * L3 ≤ L1 := by linarith only [hL2_ge_1000, hL1_ge_1000, hL3_ge100]
      exact h1.trans ((le_div_iff₀ (by linarith only [hL3_ge100])).mpr h2)
    have hpos : 0 < y_smooth := Real.rpow_pos_of_pos hN_pos _
    calc (64 : ℝ) = Real.exp (Real.log 64) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log y_smooth) := Real.exp_le_exp.mpr (hy_smooth_log.symm ▸ hlog64)
      _ = y_smooth := Real.exp_log hpos
  have hy0_ge : L2 / 2 ≤ (y0 : ℝ) := by linarith only [Nat.sub_one_lt_floor L2, hL2_ge_1000, hL3_ge100]
  have hy0_le : (y0 : ℝ) ≤ L2 := Nat.floor_le hL2_pos.le
  have hy0_ge4 : 4 ≤ y0 := Nat.le_floor (by norm_num; linarith only [hL2_ge_1000, hL3_ge100])
  have hlog_y0_ge : L3 - 1 ≤ Real.log (y0 : ℝ) := by
    have h1 : Real.log (L2 / 2) = L3 - Real.log 2 := by rw [Real.log_div hL2_pos.ne' (by norm_num)]
    have h2 : Real.log (L2 / 2) ≤ Real.log (y0 : ℝ) := Real.log_le_log (by positivity) hy0_ge
    linarith only [h1, h2, hlog2_lt1]
  have hz_le_N : z ≤ N := by
    have h1 : 16 * L1 / (δ * L2) ≤ L1 := by
      rw [div_le_iff₀ (by positivity)]
      have h2 : 16 ≤ δ * L2 := by nlinarith only [hL3d, hL2_ge_1000, hδ]
      nlinarith only [h2, hL1_pos]
    have h2 : Real.exp (16 * L1 / (δ * L2)) ≤ (N : ℝ) := by
      calc Real.exp (16 * L1 / (δ * L2)) ≤ Real.exp L1 := Real.exp_le_exp.mpr h1
        _ = (N : ℝ) := Real.exp_log hN_pos
    exact Nat.floor_le_of_le h2
  have harg_ge2 : 2 ≤ 16 * L1 / (δ * L2) := by
    rw [le_div_iff₀ (by positivity)]
    have hδ1 : δ ≤ 1 / 2 := by dsimp only [δ]; linarith only [hε1]
    nlinarith only [hδ1, hL1_ge_1000, hL2_pos]
  have hlogz_ge : 8 * L1 / (δ * L2) ≤ Real.log (z : ℝ) := by
    have hexp_ge4 : 4 ≤ Real.exp (16 * L1 / (δ * L2)) := by
      have h1 : (4 : ℝ) ≤ Real.exp 2 := by
        have he := Real.exp_one_gt_d9
        have hsq : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        nlinarith only [he, hsq]
      exact h1.trans (Real.exp_le_exp.mpr harg_ge2)
    have hz_ge_half : Real.exp (16 * L1 / (δ * L2)) / 2 ≤ (z : ℝ) := by
      linarith only [Nat.sub_one_lt_floor (Real.exp (16 * L1 / (δ * L2))), hexp_ge4]
    have h1 : 16 * L1 / (δ * L2) - Real.log 2 ≤ Real.log (z : ℝ) := by
      have h2 : Real.log (Real.exp (16 * L1 / (δ * L2)) / 2) = 16 * L1 / (δ * L2) - Real.log 2 := by
        rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
      rw [← h2]
      exact Real.log_le_log (by positivity) hz_ge_half
    have hhalf : 8 * L1 / (δ * L2) = (16 * L1 / (δ * L2)) / 2 := by ring
    linarith only [h1, hhalf, harg_ge2, hlog2_lt1]
  have hk_le : (k : ℝ) ≤ δ * L2 / (64 * L3) := Nat.floor_le (by positivity)
  have hk_ge : δ * L2 / (128 * L3) ≤ (k : ℝ) := by
    have h1 : δ * L2 / (64 * L3) - 1 < (k : ℝ) := Nat.sub_one_lt_floor _
    have h2 : 2 ≤ δ * L2 / (64 * L3) := by
      rw [le_div_iff₀ (by positivity)]
      have h3 : 1000 * L3 ≤ δ * L3 ^ 2 := by nlinarith only [hL3d, hL3_ge100]
      have h4 : 1000 * L3 ^ 2 ≤ δ * L3 ^ 3 := by nlinarith only [h3, hL3_ge100]
      nlinarith only [h4, hL2_ge_cube, hL3_ge100, hδ]
    have hhalf : δ * L2 / (128 * L3) = (δ * L2 / (64 * L3)) / 2 := by ring
    linarith only [h1, h2, hhalf]
  have hz_pos : 0 < (z : ℝ) := by
    have hlogz_pos : 0 < Real.log (z : ℝ) := lt_of_lt_of_le (by positivity) hlogz_ge
    by_contra hle; push Not at hle
    have hz0 : z = 0 := Nat.eq_zero_of_le_zero (by exact_mod_cast hle)
    rw [hz0, Nat.cast_zero, Real.log_zero] at hlogz_pos
    linarith
  have hzk_le : ((z : ℝ) ^ k) ≤ Real.sqrt y_smooth := by
    have hlog_zk : Real.log ((z : ℝ) ^ k) ≤ Real.log (Real.sqrt y_smooth) := by
      rw [Real.log_pow, Real.log_sqrt (by linarith), hy_smooth_log]
      have hlogz_ub : Real.log (z : ℝ) ≤ 16 * L1 / (δ * L2) := by
        calc Real.log (z : ℝ) ≤ Real.log (Real.exp (16 * L1 / (δ * L2))) :=
              Real.log_le_log hz_pos (Nat.floor_le (Real.exp_pos _).le)
          _ = 16 * L1 / (δ * L2) := Real.log_exp _
      calc (k : ℝ) * Real.log (z : ℝ)
          ≤ (δ * L2 / (64 * L3)) * (16 * L1 / (δ * L2)) :=
            mul_le_mul hk_le hlogz_ub (by positivity) (by positivity)
        _ = L1 / (4 * L3) := by field_simp [hδ.ne', hL2_pos.ne', (by linarith only [hL3_ge100] : L3 ≠ 0)]; ring
        _ ≤ (L1 / L3) / 2 := by
            have h4 : L1 / (4 * L3) = (L1 / L3) / 4 := by ring
            have hpos : 0 < L1 / L3 := by positivity
            linarith only [h4, hpos]
    have hpos_zk : 0 < (z : ℝ) ^ k := pow_pos hz_pos k
    calc (z : ℝ) ^ k = Real.exp (Real.log ((z : ℝ) ^ k)) := (Real.exp_log hpos_zk).symm
      _ ≤ Real.exp (Real.log (Real.sqrt y_smooth)) := Real.exp_le_exp.mpr hlog_zk
      _ = Real.sqrt y_smooth := Real.exp_log (Real.sqrt_pos.mpr (by linarith))
  have hM_gt : (1 + δ / 2) * L2 < (M : ℝ) := by
    dsimp only [M]; push_cast; exact Nat.lt_floor_add_one _
  let P_set := (Nat.primesLE z).filter (fun p => y0 < p)
  let A_good := (Good N y_smooth y0).filter (fun n => M ≤ ((Erdos955.s n).primeFactors ∩ P_set).card)
  let Small := Finset.range (⌊Real.sqrt N⌋₊ + 1)
  have hcover : (S_bad ∩ Set.Iio N) ⊆
      ((Small ∪ (E_A N y_smooth ∪ (E_B N y_smooth ∪ (E_F N y0 ∪ A_good))) : Finset ℕ) : Set ℕ) := by
    intro n hn
    rcases hn with ⟨hbad, hnN⟩
    rw [Set.mem_Iio] at hnN
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    by_cases hsm : n ≤ ⌊Real.sqrt N⌋₊
    · exact Or.inl (Finset.mem_range.mpr (Nat.lt_succ_of_le hsm))
    · right
      have hn_gt_sq : Real.sqrt (N : ℝ) < (n : ℝ) := by
        have h1 : ⌊Real.sqrt N⌋₊ + 1 ≤ n := by omega
        have h2 : Real.sqrt (N : ℝ) < ((⌊Real.sqrt N⌋₊ + 1 : ℕ) : ℝ) := by
          push_cast; exact Nat.lt_floor_add_one _
        exact h2.trans_le (by exact_mod_cast h1)
      have hn1 : 1 ≤ n := by
        have : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ N))
        have : (1 : ℝ) < (n : ℝ) := by linarith
        exact_mod_cast this.le
      have hn_Icc : n ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hn1, hnN.le⟩
      have hmem := Icc_subset_good_union_exc N y_smooth y0 hn_Icc
      simp only [Finset.mem_union] at hmem
      rcases hmem with hgood | hEA | hEB | hEF
      · right; right; right
        simp only [A_good, Finset.mem_filter]
        refine ⟨hgood, ?_⟩
        have hloglog_n : L2 - Real.log 2 ≤ Real.log (Real.log (n : ℝ)) := by
          have hlog_n : L1 / 2 ≤ Real.log (n : ℝ) := by
            have h1 : Real.log (Real.sqrt (N : ℝ)) = L1 / 2 := Real.log_sqrt hN_pos.le
            rw [← h1]
            exact Real.log_le_log (Real.sqrt_pos.mpr hN_pos) hn_gt_sq.le
          have h1 : Real.log (L1 / 2) = L2 - Real.log 2 := by
            rw [Real.log_div (by linarith) (by norm_num)]
          rw [← h1]
          exact Real.log_le_log (by linarith) hlog_n
        have homega_gt : (1 + δ) * L2 < ((Erdos955.s n).primeFactors.card : ℝ) := by
          rw [← cardDistinctFactors_eq_card_primeFactors]
          rw [Set.mem_ofPred_eq] at hbad
          have h1 : (1 + ε) * (L2 - Real.log 2) ≤ (1 + ε) * Real.log (Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hloglog_n (by positivity)
          have h2 : (1 + δ) * L2 ≤ (1 + ε) * (L2 - Real.log 2) := by
            dsimp only [δ]; linarith [hN2]
          linarith
        have hsn_pos : 1 ≤ Erdos955.s n := by
          by_contra h0
          have hsn0 : Erdos955.s n = 0 := by omega
          rw [hsn0, Nat.primeFactors_zero, Finset.card_empty, Nat.cast_zero] at homega_gt
          have : 0 < (1 + δ) * L2 := by positivity
          linarith
        let PF := (Erdos955.s n).primeFactors
        let PF_lo := PF.filter (fun p => p ≤ y0)
        let PF_hi := PF.filter (fun p => z < p)
        have hpf_sub : PF ⊆ PF_lo ∪ ((PF ∩ P_set) ∪ PF_hi) := by
          intro p hp
          simp only [PF_lo, PF_hi, P_set, Finset.mem_union, Finset.mem_filter, Finset.mem_inter,
            Nat.mem_primesLE]
          by_cases h1 : p ≤ y0
          · exact Or.inl ⟨hp, h1⟩
          · by_cases h2 : p ≤ z
            · exact Or.inr (Or.inl ⟨hp, ⟨h2, Nat.prime_of_mem_primeFactors hp⟩, not_le.mp h1⟩)
            · exact Or.inr (Or.inr ⟨hp, not_le.mp h2⟩)
        have hpf_card : (PF.card : ℝ) ≤ (PF_lo.card : ℝ) + ((PF ∩ P_set).card : ℝ) + (PF_hi.card : ℝ) := by
          have h1 := (Finset.card_le_card hpf_sub).trans (Finset.card_union_le _ _)
          have h2 := Finset.card_union_le (PF ∩ P_set) PF_hi
          have h3 : PF.card ≤ PF_lo.card + (PF ∩ P_set).card + PF_hi.card := by omega
          exact_mod_cast h3
        have hlo_bd : (PF_lo.card : ℝ) ≤ (δ / 8) * L2 := by
          have hsub : PF_lo ⊆ Nat.primesLE y0 := by
            intro p hp
            simp only [PF_lo, PF, Finset.mem_filter] at hp
            exact Nat.mem_primesLE.mpr ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
          have h1 : (PF_lo.card : ℝ) ≤ (Nat.primeCounting y0 : ℝ) := by
            rw [← Nat.primesLE_card_eq_primeCounting]
            exact_mod_cast Finset.card_le_card hsub
          have h2 : (Nat.primeCounting y0 : ℝ) ≤ 6 * (y0 : ℝ) / Real.log (y0 : ℝ) :=
            primeCounting_nat_le y0 hy0_ge4
          have h3 : 6 * (y0 : ℝ) / Real.log (y0 : ℝ) ≤ 6 * L2 / (L3 - 1) := by
            calc 6 * (y0 : ℝ) / Real.log (y0 : ℝ)
                ≤ 6 * L2 / Real.log (y0 : ℝ) := by gcongr
              _ ≤ 6 * L2 / (L3 - 1) :=
                  div_le_div_of_nonneg_left (by positivity) (by linarith) hlog_y0_ge
          calc (PF_lo.card : ℝ) ≤ 6 * L2 / (L3 - 1) := h1.trans (h2.trans h3)
            _ = (6 / (L3 - 1)) * L2 := by ring
            _ ≤ (δ / 8) * L2 := mul_le_mul_of_nonneg_right hN4 hL2_pos.le
        have hhi_bd : (PF_hi.card : ℝ) ≤ (δ / 4) * L2 := by
          have hprod_dvd : (∏ p ∈ PF_hi, p) ∣ Erdos955.s n :=
            (Finset.prod_dvd_prod_of_subset PF_hi PF id (Finset.filter_subset _ _)).trans
              (Nat.prod_primeFactors_dvd (Erdos955.s n))
          have hprod_le : (∏ p ∈ PF_hi, (p : ℝ)) ≤ (N : ℝ) ^ 2 := by
            have h1 : ∏ p ∈ PF_hi, p ≤ Erdos955.s n := Nat.le_of_dvd hsn_pos hprod_dvd
            have h2 : Erdos955.s n ≤ n ^ 2 := s_le_sq n
            have h3 : n ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hnN.le 2
            have hnat : ∏ p ∈ PF_hi, p ≤ N ^ 2 := h1.trans (h2.trans h3)
            have hR : ((∏ p ∈ PF_hi, p : ℕ) : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
            push_cast at hR
            exact hR
          have hz_pow_le : (z : ℝ) ^ PF_hi.card ≤ ∏ p ∈ PF_hi, (p : ℝ) := by
            calc (z : ℝ) ^ PF_hi.card = ∏ _p ∈ PF_hi, (z : ℝ) := by simp
              _ ≤ ∏ p ∈ PF_hi, (p : ℝ) := by
                refine Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg z) fun p hp => ?_
                simp only [PF_hi, Finset.mem_filter] at hp
                exact_mod_cast hp.2.le
          have hlog_ineq : (PF_hi.card : ℝ) * Real.log (z : ℝ) ≤ 2 * L1 := by
            have h1 := Real.log_le_log (pow_pos hz_pos _) (hz_pow_le.trans hprod_le)
            rw [Real.log_pow, Real.log_pow] at h1
            push_cast at h1
            exact h1
          have hlogz_pos : 0 < Real.log (z : ℝ) := lt_of_lt_of_le (by positivity) hlogz_ge
          calc (PF_hi.card : ℝ) ≤ 2 * L1 / Real.log (z : ℝ) := (le_div_iff₀ hlogz_pos).mpr hlog_ineq
            _ ≤ 2 * L1 / (8 * L1 / (δ * L2)) :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hlogz_ge
            _ = (δ / 4) * L2 := by field_simp [hδ.ne', hL2_pos.ne', (by linarith : L1 ≠ 0)]; ring
        have hM_lt : (1 + δ / 2) * L2 < ((PF ∩ P_set).card : ℝ) := by
          linarith only [homega_gt, hpf_card, hlo_bd, hhi_bd, hL2_pos]
        have hfl : ⌊(1 + δ / 2) * L2⌋₊ < (PF ∩ P_set).card :=
          (Nat.floor_lt (by positivity)).mpr hM_lt
        dsimp only [M, PF] at hfl ⊢
        omega
      · exact Or.inl hEA
      · exact Or.inr (Or.inl hEB)
      · exact Or.inr (Or.inr (Or.inl hEF))
  have hA_good_bd : (A_good.card : ℝ) / (N : ℝ) ≤ 30000 / (alpha * δ * L3) :=
    card_A_good_div_le N y0 z k M δ y_smooth hN16 hδ hy_smooth_ge64 hL1_gt1 hL2_pos
      hL3_ge100 hL3_ge_d hy_smooth_log hz_le_N hzk_le hk_le hk_ge hM_gt
  have hncard_le : ((S_bad ∩ Set.Iio N).ncard : ℝ) ≤
      (Small.card : ℝ) + ((E_A N y_smooth).card : ℝ) + ((E_B N y_smooth).card : ℝ) +
        ((E_F N y0).card : ℝ) + (A_good.card : ℝ) := by
    have h1 : (S_bad ∩ Set.Iio N).ncard ≤
        (Small ∪ (E_A N y_smooth ∪ (E_B N y_smooth ∪ (E_F N y0 ∪ A_good)))).card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hcover (Finset.finite_toSet _)
    have h2 := Finset.card_union_le Small (E_A N y_smooth ∪ (E_B N y_smooth ∪ (E_F N y0 ∪ A_good)))
    have h3 := Finset.card_union_le (E_A N y_smooth) (E_B N y_smooth ∪ (E_F N y0 ∪ A_good))
    have h4 := Finset.card_union_le (E_B N y_smooth) (E_F N y0 ∪ A_good)
    have h5 := Finset.card_union_le (E_F N y0) A_good
    have htot : (S_bad ∩ Set.Iio N).ncard ≤ Small.card + (E_A N y_smooth).card +
        (E_B N y_smooth).card + (E_F N y0).card + A_good.card := by omega
    exact_mod_cast htot
  have hSmall_div : (Small.card : ℝ) / (N : ℝ) ≤ 2 / Real.sqrt (N : ℝ) := by
    have h1 : (Small.card : ℝ) ≤ Real.sqrt (N : ℝ) + 1 := by
      simp only [Small, Finset.card_range]
      push_cast
      linarith [Nat.floor_le (Real.sqrt_nonneg (N : ℝ))]
    have hsq : 1 ≤ Real.sqrt (N : ℝ) := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ N))
    have hsq2 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN_pos.le
    calc (Small.card : ℝ) / (N : ℝ) ≤ (2 * Real.sqrt (N : ℝ)) / (N : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) hN_pos.le
      _ = 2 / Real.sqrt (N : ℝ) := by
          field_simp [hN_pos.ne', (Real.sqrt_pos.mpr hN_pos).ne']
          linarith
  have hEA_div : ((E_A N y_smooth).card : ℝ) / (N : ℝ) ≤
      1 / Real.sqrt (N : ℝ) + 8 / L3 := by
    have h1 := card_E_A_le N y_smooth (by omega) (by linarith)
    rw [hy_smooth_log] at h1
    have h2 : 4 * (N : ℝ) * (L1 / L3 + Real.log 4) / L1 ≤ (N : ℝ) * (8 / L3) := by
      have hlog4 : Real.log 4 ≤ L1 / L3 := by
        have hlt := log_four_lt_two
        have : 2 * L3 ≤ L1 := by linarith only [hL2_ge_1000, hL1_ge_1000, hL3_ge100]
        exact hlt.le.trans ((le_div_iff₀ (by linarith only [hL3_ge100])).mpr this)
      have h3 : 4 * (N : ℝ) * (L1 / L3 + Real.log 4) ≤ 4 * (N : ℝ) * (2 * (L1 / L3)) := by
        gcongr; linarith only [hlog4]
      calc 4 * (N : ℝ) * (L1 / L3 + Real.log 4) / L1
          ≤ 4 * (N : ℝ) * (2 * (L1 / L3)) / L1 := by gcongr
        _ = (N : ℝ) * (8 / L3) := by field_simp [(by linarith only [hL1_gt1] : L1 ≠ 0), (by linarith only [hL3_ge100] : L3 ≠ 0)]; ring
    have hsq2 : Real.sqrt (N : ℝ) / (N : ℝ) = 1 / Real.sqrt (N : ℝ) := by
      have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN_pos.le
      field_simp [hN_pos.ne', (Real.sqrt_pos.mpr hN_pos).ne']
      linarith only [hsq]
    calc ((E_A N y_smooth).card : ℝ) / (N : ℝ)
        ≤ (Real.sqrt (N : ℝ) + (N : ℝ) * (8 / L3)) / (N : ℝ) :=
          div_le_div_of_nonneg_right (by linarith only [h1, h2]) hN_pos.le
      _ = Real.sqrt (N : ℝ) / (N : ℝ) + 8 / L3 := by field_simp [hN_pos.ne']
      _ = 1 / Real.sqrt (N : ℝ) + 8 / L3 := by rw [hsq2]
  have hEB_div : ((E_B N y_smooth).card : ℝ) / (N : ℝ) ≤ 1 / L3 := by
    have h1 := card_E_B_le N y_smooth (by linarith only [hy_smooth_ge64])
    have hfl_ge : y_smooth / 2 ≤ (⌊y_smooth⌋₊ : ℝ) := by
      linarith only [Nat.sub_one_lt_floor y_smooth, hy_smooth_ge64]
    have hy_ge_2L3 : 2 * L3 ≤ y_smooth := by
      have hlog_le : Real.log (2 * L3) ≤ L1 / L3 := by
        have h1' : Real.log (2 * L3) ≤ 2 * L3 := log_le_self_of_pos (by linarith only [hL3_ge100])
        have h2' : 2 * L3 * L3 ≤ L1 := by
          have : 2 * L3 * L3 ≤ L3 ^ 3 / 6 := by nlinarith only [hL3_ge100, hL3_sq]
          linarith only [this, hL2_ge_cube, hL1_ge_1000, hL2_pos]
        exact h1'.trans ((le_div_iff₀ (by linarith only [hL3_ge100])).mpr h2')
      have hypos : 0 < y_smooth := by linarith
      calc 2 * L3 = Real.exp (Real.log (2 * L3)) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (Real.log y_smooth) := Real.exp_le_exp.mpr (hy_smooth_log.symm ▸ hlog_le)
        _ = y_smooth := Real.exp_log hypos
    have hfl_ge_L3 : L3 ≤ (⌊y_smooth⌋₊ : ℝ) := by linarith only [hfl_ge, hy_ge_2L3]
    calc ((E_B N y_smooth).card : ℝ) / (N : ℝ)
        ≤ ((N : ℝ) / (⌊y_smooth⌋₊ : ℝ)) / (N : ℝ) := div_le_div_of_nonneg_right h1 hN_pos.le
      _ = 1 / (⌊y_smooth⌋₊ : ℝ) := by field_simp [hN_pos.ne']
      _ ≤ 1 / L3 := one_div_le_one_div_of_le (by linarith only [hL3_ge100]) hfl_ge_L3
  have hEF_div : ((E_F N y0).card : ℝ) / (N : ℝ) ≤
      240 / L3 + 20 / Real.sqrt (L2 / 2) + 4000 / L3 := by
    have h1 := card_E_F_le N y0 hN16 hy0_ge4
    have hdiv : ((E_F N y0).card : ℝ) / (N : ℝ) ≤
        120 / (y0 : ℝ) + 20 / Real.sqrt y0 + 864 * L2 / ((y0 : ℝ) * Real.log (y0 : ℝ)) := by
      rw [div_le_iff₀ hN_pos]
      calc ((E_F N y0).card : ℝ)
          ≤ (N : ℝ) * (120 / (y0 : ℝ) + 20 / Real.sqrt y0 +
              864 * L2 / ((y0 : ℝ) * Real.log (y0 : ℝ))) := h1
        _ = (120 / (y0 : ℝ) + 20 / Real.sqrt y0 +
              864 * L2 / ((y0 : ℝ) * Real.log (y0 : ℝ))) * (N : ℝ) := mul_comm _ _
    have hp1 : 120 / (y0 : ℝ) ≤ 240 / L3 := by
      have hhalf : L3 / 2 ≤ (y0 : ℝ) := by linarith only [hy0_ge, hL2_ge_1000, hL3_ge100]
      calc 120 / (y0 : ℝ) ≤ 120 / (L3 / 2) :=
            div_le_div_of_nonneg_left (by norm_num) (by linarith only [hL3_ge100]) hhalf
        _ = 240 / L3 := by ring
    have hp2 : 20 / Real.sqrt (y0 : ℝ) ≤ 20 / Real.sqrt (L2 / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr (by positivity))
        (Real.sqrt_le_sqrt hy0_ge)
    have hp3 : 864 * L2 / ((y0 : ℝ) * Real.log (y0 : ℝ)) ≤ 4000 / L3 := by
      have hden : (L2 / 2) * (L3 / 2) ≤ (y0 : ℝ) * Real.log (y0 : ℝ) :=
        mul_le_mul hy0_ge (by linarith only [hlog_y0_ge, hL3_ge100])
          (by linarith only [hL3_ge100]) (by positivity)
      calc 864 * L2 / ((y0 : ℝ) * Real.log (y0 : ℝ))
          ≤ 864 * L2 / ((L2 / 2) * (L3 / 2)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = 3456 / L3 := by field_simp [hL2_pos.ne', (by linarith only [hL3_ge100] : L3 ≠ 0)]; ring
        _ ≤ 4000 / L3 := div_le_div_of_nonneg_right (by norm_num) (by linarith only [hL3_ge100])
    linarith only [hdiv, hp1, hp2, hp3]
  have hcomb1 : (2 : ℝ) / Real.sqrt (N : ℝ) + 1 / Real.sqrt (N : ℝ) ≤ 10 / Real.sqrt (N : ℝ) := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
  have hcomb2 : (8 : ℝ) / L3 + 1 / L3 + 240 / L3 + 4000 / L3 ≤ 10000 / L3 := by
    have : (8 : ℝ) / L3 + 1 / L3 + 240 / L3 + 4000 / L3 = 4249 / L3 := by ring
    rw [this]; exact div_le_div_of_nonneg_right (by norm_num) (by linarith only [hL3_ge100])
  have hcomb3 : (20 : ℝ) / Real.sqrt (L2 / 2) ≤ 10000 / Real.sqrt (L2 / 2) :=
    div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
  calc ((S_bad ∩ Set.Iio N).ncard : ℝ) / (N : ℝ)
      ≤ ((Small.card : ℝ) + ((E_A N y_smooth).card : ℝ) + ((E_B N y_smooth).card : ℝ) +
          ((E_F N y0).card : ℝ) + (A_good.card : ℝ)) / (N : ℝ) :=
        div_le_div_of_nonneg_right hncard_le hN_pos.le
    _ = (Small.card : ℝ) / (N : ℝ) + ((E_A N y_smooth).card : ℝ) / (N : ℝ) +
          ((E_B N y_smooth).card : ℝ) / (N : ℝ) + ((E_F N y0).card : ℝ) / (N : ℝ) +
          (A_good.card : ℝ) / (N : ℝ) := by ring
    _ ≤ 10000 / L3 + 10000 / Real.sqrt (L2 / 2) + 30000 / (alpha * δ * L3) +
          10 / Real.sqrt (N : ℝ) := by
        linarith only [hSmall_div, hEA_div, hEB_div, hEF_div, hA_good_bd, hcomb1, hcomb2, hcomb3]
    _ < η := hN5

end Erdos955TroupeH1

private theorem troupeUpperTail :
    OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1.H1 := by
  intro ε hε
  by_cases hε1 : ε ≤ 1
  · exact Erdos955TroupeH1.upper_tail_fixed_eps_le_one ε hε hε1
  · have h1 := Erdos955TroupeH1.upper_tail_fixed_eps_le_one 1 zero_lt_one le_rfl
    have hsub : {n : ℕ | (1 + ε) * Real.log (Real.log (n : ℝ)) <
          (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ⊆
        {n : ℕ | (1 + 1) * Real.log (Real.log (n : ℝ)) <
          (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ∪ Set.Iio 3 := by
      intro n hn
      by_cases hlt : n < 3
      · exact Or.inr hlt
      · left
        have hn3 : 3 ≤ n := not_lt.mp hlt
        have hlog1 : 1 < Real.log (n : ℝ) := by
          have : Real.exp 1 < (n : ℝ) := by
            have := Real.exp_one_lt_d9
            have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
            linarith
          calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
            _ < Real.log (n : ℝ) := Real.log_lt_log (Real.exp_pos 1) this
        have hll : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog1
        rw [Set.mem_ofPred_eq] at hn ⊢
        nlinarith
    rw [Set.HasDensity] at h1 ⊢
    have hfin : Tendsto (fun b : ℕ => (3 : ℝ) / (b : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 3
    have hsum := h1.add hfin
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun b => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (fun b => ?_)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hfinS : (({n : ℕ | (1 + 1) * Real.log (Real.log (n : ℝ)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ∩ Set.Iio b) ∪
        Set.Iio 3).Finite := ((Set.finite_Iio b).inter_of_right _).union (Set.finite_Iio 3)
    have hle1 := Set.ncard_le_ncard
      (s := {n : ℕ | (1 + ε) * Real.log (Real.log (n : ℝ)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ∩ Set.Iio b)
      (fun x hx => by rcases hsub hx.1 with h | h; exact Or.inl ⟨h, hx.2⟩; exact Or.inr h) hfinS
    have hle2 := Set.ncard_union_le
      ({n : ℕ | (1 + 1) * Real.log (Real.log (n : ℝ)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ∩ Set.Iio b) (Set.Iio 3)
    have hle3 : (Set.Iio 3).ncard = 3 := Nat.ncard_Iio 3
    have hle4 := hle1.trans hle2
    rw [hle3] at hle4
    exact_mod_cast hle4

-- Step Erdos955.erdos_955.variants.troupe_unusually_many_prime_factors.R1.H2
-- Credit: @caa1982

private theorem compositeDivisorBound : OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1.H2 := by
  intro n hn hnp
  set p := n.minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have hp_sq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  set d := n / p
  have hpd : p * d = n := Nat.mul_div_cancel' hp_dvd
  have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp_prime.pos
  have hd_lt : d < n := by
    have : 2 ≤ p := hp_prime.two_le
    nlinarith
  have hd_dvd : d ∣ n := ⟨p, by rw [mul_comm, hpd]⟩
  have hsub : ({d, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨hd_dvd, by omega⟩
    · exact Nat.mem_divisors_self _ (by omega)
  have hsum : d + n ≤ ArithmeticFunction.sigma 1 n := by
    rw [ArithmeticFunction.sigma_one_apply]
    calc d + n = ∑ x ∈ ({d, n} : Finset ℕ), x := (Finset.sum_pair (f := fun x => x) hd_lt.ne).symm
      _ ≤ ∑ x ∈ n.divisors, x := Finset.sum_le_sum_of_subset hsub
  have hd_le_s : d ≤ Erdos955.s n := by
    unfold Erdos955.s
    omega
  have hp_le_d : p ≤ d := by
    have : p * p ≤ p * d := by rw [← sq, hpd]; exact hp_sq
    exact Nat.le_of_mul_le_mul_left this hp_prime.pos
  calc n = p * d := hpd.symm
    _ ≤ d * d := Nat.mul_le_mul_right d hp_le_d
    _ = d ^ 2 := (sq d).symm
    _ ≤ Erdos955.s n ^ 2 := Nat.pow_le_pow_left hd_le_s 2

theorem OMA.solution : type_of% @Erdos955.erdos_955.variants.troupe_unusually_many_prime_factors := by
  exact OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1.main
    troupeUpperTail compositeDivisorBound
