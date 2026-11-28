import OMAStatements.S_oeis_a067786
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

-- Problem: A067786: Numbers n such that phi(n) = 2*pi(n) where pi(n) = A000720(n) and phi(n) = A000010(n).
-- Upstream: formal-conjectures statements/oeis-a067786.lean:0 (declaration OMA.S_oeis_a067786.main)
-- Credit: @umarsxlim (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.S_oeis_a067786

section Analytic
open Finset Real ArithmeticFunction Chebyshev

/-! ## Module A: Elementary lower bounds on `n.totient` -/

private lemma totient_div_eq_prod_real {n : ℕ} (hn : 0 < n) :
    (n.totient : ℝ) / (n : ℝ) = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hprod_pos : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p : ℝ) :=
    Finset.prod_pos fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hmul : (n.totient : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have h := Nat.totient_mul_prod_primeFactors n
    have hcast : ((n.totient * ∏ p ∈ n.primeFactors, p : ℕ) : ℝ) =
        ((n * ∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hcast
    rw [hcast]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Nat.cast_sub hp1, Nat.cast_one]
  rw [div_eq_iff hn0]
  have hrew : ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) =
      (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) / ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
  rw [hrew, div_mul_eq_mul_div, eq_div_iff hprod_pos.ne']
  linarith

private lemma totient_lower_avoid {n next : ℕ} {bad good : Finset ℕ}
    (hn : 0 < n)
    (hnext : 2 ≤ next)
    (hgood_prime : ∀ p ∈ good, p.Prime)
    (hgood_lt : ∀ p ∈ good, p < next)
    (hcover : ∀ p : ℕ, p.Prime → p < next → p ∉ bad → p ∈ good)
    (havoid : ∀ p ∈ bad, ¬ p ∣ n)
    (hlt : n < (∏ p ∈ good, p) * next) :
    (∏ p ∈ good, (p - 1)) * n ≤ (∏ p ∈ good, p) * n.totient := by
  let P := n.primeFactors
  let S := P ∩ good
  let L := P \ good
  let M := good \ S
  have hP_union : S ∪ L = P := by
    ext x; simp only [S, L, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hP_disj : Disjoint S L := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [S, L, Finset.mem_inter, Finset.mem_sdiff] at h1 h2; exact h2.2 h1.2
  have hG_union : S ∪ M = good := Finset.union_sdiff_of_subset Finset.inter_subset_right
  have hG_disj : Disjoint S M := disjoint_sdiff_self_right
  have hL_ge : ∀ q ∈ L, next ≤ q := by
    intro q hq
    rw [Finset.mem_sdiff] at hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq.1
    have hqdvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq.1
    have hqnbad : q ∉ bad := fun hb => havoid q hb hqdvd
    by_contra hltq
    push Not at hltq
    exact hq.2 (hcover q hqp hltq hqnbad)
  have hM_lt : ∀ p ∈ M, p < next := fun p hp => hgood_lt p (Finset.sdiff_subset hp)
  have hcard : L.card ≤ M.card := by
    by_contra hgt
    push Not at hgt
    have hLne : L.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q₀, hq₀⟩ := hLne
    let L' := L.erase q₀
    have hL'card : M.card ≤ L'.card := by
      have hce : L'.card = L.card - 1 := Finset.card_erase_of_mem hq₀
      omega
    have hMprod : ∏ p ∈ M, p ≤ next ^ M.card := by
      calc ∏ p ∈ M, p ≤ ∏ _p ∈ M, next := Finset.prod_le_prod' fun p hp => (hM_lt p hp).le
        _ = next ^ M.card := Finset.prod_const next
    have hL'prod : next ^ L'.card ≤ ∏ q ∈ L', q := by
      calc next ^ L'.card = ∏ _q ∈ L', next := (Finset.prod_const next).symm
        _ ≤ ∏ q ∈ L', q := Finset.prod_le_prod' fun q hq => hL_ge q (Finset.mem_of_mem_erase hq)
    have hpow : next ^ M.card ≤ next ^ L'.card :=
      Nat.pow_le_pow_right (by omega) hL'card
    have hLprod : (∏ p ∈ M, p) * next ≤ ∏ q ∈ L, q := by
      calc (∏ p ∈ M, p) * next ≤ next ^ L'.card * q₀ :=
            Nat.mul_le_mul (hMprod.trans hpow) (hL_ge q₀ hq₀)
        _ ≤ (∏ q ∈ L', q) * q₀ := Nat.mul_le_mul_right q₀ hL'prod
        _ = ∏ q ∈ L, q := by rw [mul_comm, Finset.mul_prod_erase L (fun x => x) hq₀]
    have hP_le_n : ∏ q ∈ P, q ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
    have hbad_le : (∏ p ∈ good, p) * next ≤ n := by
      calc (∏ p ∈ good, p) * next
        _ = (∏ p ∈ S, p) * ((∏ p ∈ M, p) * next) := by
              rw [← hG_union, Finset.prod_union hG_disj, mul_assoc]
        _ ≤ (∏ p ∈ S, p) * (∏ q ∈ L, q) := Nat.mul_le_mul_left _ hLprod
        _ = ∏ q ∈ P, q := by rw [← Finset.prod_union hP_disj, hP_union]
        _ ≤ n := hP_le_n
    omega
  -- Compare products in ℝ
  have hnext_pos : (0 : ℝ) < (next : ℝ) := by exact_mod_cast (show 0 < next by omega)
  have h1next_nn : (0 : ℝ) ≤ 1 - 1 / (next : ℝ) := by
    rw [sub_nonneg, div_le_one hnext_pos]
    exact_mod_cast (show 1 ≤ next by omega)
  have h1next_le : 1 - 1 / (next : ℝ) ≤ 1 := by
    linarith [div_nonneg zero_le_one hnext_pos.le]
  have hM_prod_le : ∏ p ∈ M, (1 - 1 / (p : ℝ)) ≤ (1 - 1 / (next : ℝ)) ^ M.card := by
    calc ∏ p ∈ M, (1 - 1 / (p : ℝ))
      _ ≤ ∏ _p ∈ M, (1 - 1 / (next : ℝ)) := by
            apply Finset.prod_le_prod
            · intro p hp
              have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
                exact_mod_cast (hgood_prime p (Finset.sdiff_subset hp)).one_le
              rw [sub_nonneg, div_le_one (by linarith)]
              exact hp1
            · intro p hp
              have hp_pos : (0 : ℝ) < (p : ℝ) := by
                exact_mod_cast (hgood_prime p (Finset.sdiff_subset hp)).pos
              have hp_le : (p : ℝ) ≤ (next : ℝ) := by exact_mod_cast (hM_lt p hp).le
              gcongr
      _ = (1 - 1 / (next : ℝ)) ^ M.card := Finset.prod_const _
  have hL_prod_ge : (1 - 1 / (next : ℝ)) ^ L.card ≤ ∏ q ∈ L, (1 - 1 / (q : ℝ)) := by
    calc (1 - 1 / (next : ℝ)) ^ L.card
      _ = ∏ _q ∈ L, (1 - 1 / (next : ℝ)) := (Finset.prod_const _).symm
      _ ≤ ∏ q ∈ L, (1 - 1 / (q : ℝ)) := by
            apply Finset.prod_le_prod
            · intro _ _; exact h1next_nn
            · intro q hq
              have hq_ge : (next : ℝ) ≤ (q : ℝ) := by exact_mod_cast hL_ge q hq
              gcongr
  have hpow_ge : (1 - 1 / (next : ℝ)) ^ M.card ≤ (1 - 1 / (next : ℝ)) ^ L.card :=
    pow_le_pow_of_le_one h1next_nn h1next_le hcard
  have hS_nn : (0 : ℝ) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_inter_left hp)).one_le
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hp1
  have hratio : ∏ p ∈ good, (1 - 1 / (p : ℝ)) ≤ (n.totient : ℝ) / (n : ℝ) := by
    rw [totient_div_eq_prod_real hn]
    change ∏ p ∈ good, (1 - 1 / (p : ℝ)) ≤ ∏ q ∈ P, (1 - 1 / (q : ℝ))
    rw [← hG_union, ← hP_union,
        Finset.prod_union hG_disj, Finset.prod_union hP_disj]
    exact mul_le_mul_of_nonneg_left (hM_prod_le.trans (hpow_ge.trans hL_prod_ge)) hS_nn
  have hGprod_pos : (0 : ℝ) < ∏ p ∈ good, (p : ℝ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (hgood_prime p hp).pos
  have hGrew : ∏ p ∈ good, (1 - 1 / (p : ℝ)) =
      (∏ p ∈ good, ((p : ℝ) - 1)) / ∏ p ∈ good, (p : ℝ) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hgood_prime p hp).ne_zero
    field_simp
  rw [hGrew] at hratio
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hineq_real : (∏ p ∈ good, ((p : ℝ) - 1)) * (n : ℝ) ≤
      (∏ p ∈ good, (p : ℝ)) * (n.totient : ℝ) := by
    rw [div_le_div_iff₀ hGprod_pos hn_pos] at hratio
    linarith
  have hcast_lhs : ((∏ p ∈ good, (p - 1)) * n : ℕ) = (∏ p ∈ good, ((p : ℝ) - 1)) * (n : ℝ) := by
    push_cast
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (hgood_prime p hp).one_le, Nat.cast_one]
  have hcast_rhs : ((∏ p ∈ good, p) * n.totient : ℕ) = (∏ p ∈ good, (p : ℝ)) * (n.totient : ℝ) := by
    push_cast; rfl
  exact_mod_cast (hcast_lhs.symm ▸ hcast_rhs.symm ▸ hineq_real)

/-! ## Mod-6 telescoping product bound for `n ≥ P_12` -/

private lemma mod6_step_cube (j : ℕ) (hj : 1 ≤ j) :
    ((6 * (j : ℝ) - 5) / (6 * (j : ℝ) + 1)) ≤
      (((6 * (j : ℝ) - 2) / (6 * (j : ℝ) - 1)) * ((6 * (j : ℝ)) / (6 * (j : ℝ) + 1))) ^ 3 := by
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h1 : (0 : ℝ) < 6 * (j : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < 6 * (j : ℝ) + 1 := by linarith
  rw [mul_pow, div_pow, div_pow, div_mul_div_comm, div_le_div_iff₀ h2 (by positivity)]
  have hdiff : ((6 * (j : ℝ) - 2) ^ 3 * (6 * (j : ℝ)) ^ 3) * (6 * (j : ℝ) + 1) -
      (6 * (j : ℝ) - 5) * ((6 * (j : ℝ) - 1) ^ 3 * (6 * (j : ℝ) + 1) ^ 3) =
      ((j : ℝ) - 1) * (69984 * (j : ℝ) ^ 4 + 55728 * (j : ℝ) ^ 3 +
        53352 * (j : ℝ) ^ 2 + 53892 * (j : ℝ) + 53898) + 53893 := by
    ring
  have hnn : (0 : ℝ) ≤ ((j : ℝ) - 1) * (69984 * (j : ℝ) ^ 4 + 55728 * (j : ℝ) ^ 3 +
        53352 * (j : ℝ) ^ 2 + 53892 * (j : ℝ) + 53898) + 53893 := by
    have hj1 : (0 : ℝ) ≤ (j : ℝ) - 1 := by linarith
    positivity
  linarith

private lemma mod6_prod_cube_ge (K : ℕ) (hK : 8 ≤ K) :
    (49 : ℝ) / (6 * (K : ℝ) + 1) ≤
      (∏ j ∈ Finset.Icc 9 K,
        (((6 * (j : ℝ) - 2) / (6 * (j : ℝ) - 1)) * ((6 * (j : ℝ)) / (6 * (j : ℝ) + 1)))) ^ 3 := by
  induction K, hK using Nat.le_induction with
  | base =>
    simp
    norm_num
  | succ k hk ih =>
    have hIcc : Finset.Icc 9 (k + 1) = insert (k + 1) (Finset.Icc 9 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp), mul_pow]
    have hstep := mod6_step_cube (k + 1) (by omega)
    have hkr : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hden_pos : (0 : ℝ) < 6 * (k : ℝ) + 1 := by linarith
    have hsub : 6 * ((k + 1 : ℕ) : ℝ) - 5 = 6 * (k : ℝ) + 1 := by push_cast; ring
    rw [hsub] at hstep
    have hnn1 : (0 : ℝ) ≤ (6 * (k : ℝ) + 1) / (6 * ((k + 1 : ℕ) : ℝ) + 1) := by positivity
    have hnn2 : (0 : ℝ) ≤ (49 : ℝ) / (6 * (k : ℝ) + 1) := by positivity
    have hmul := mul_le_mul hstep ih hnn2 (by linarith)
    calc (49 : ℝ) / (6 * ((k + 1 : ℕ) : ℝ) + 1)
      _ = ((6 * (k : ℝ) + 1) / (6 * ((k + 1 : ℕ) : ℝ) + 1)) * ((49 : ℝ) / (6 * (k : ℝ) + 1)) := by
            field_simp
      _ ≤ _ := hmul

/-! ## Module B: Chebyshev 30-identity and explicit `π(x)` upper bound -/

noncomputable def logFact (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ)

private lemma logFact_ge {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1 ≤ logFact n := by
  induction n, hn using Nat.le_induction with
  | base => simp [logFact]
  | succ k hk ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [logFact, hIcc, Finset.sum_insert (by simp)]
    change Real.log ((k + 1 : ℕ) : ℝ) + logFact k ≥ _
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hlog : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤ ((k : ℝ) + 1) / (k : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hk_pos.ne'] at hlog
    have h1 : (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hlog hk_pos.le
      have hsimp : (k : ℝ) * (((k : ℝ) + 1) / (k : ℝ) - 1) = 1 := by field_simp; ring
      linarith
    push_cast
    linarith

private lemma logFact_le {n : ℕ} (hn : 1 ≤ n) :
    logFact n ≤ ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) - (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp [logFact]
    norm_num
    linarith [Real.log_two_gt_d9]
  | succ k hk ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [logFact, hIcc, Finset.sum_insert (by simp)]
    change Real.log ((k + 1 : ℕ) : ℝ) + logFact k ≤ _
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2_pos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hlog : Real.log (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hk1_pos.ne' hk2_pos.ne'] at hlog
    have h1 : 1 ≤ ((k : ℝ) + 2) * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hlog hk2_pos.le
      have hsimp : ((k : ℝ) + 2) * (((k : ℝ) + 1) / ((k : ℝ) + 2) - 1) = -1 := by field_simp; ring
      linarith
    push_cast
    have h2 : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    rw [h2]
    linarith

private lemma logFact_eq_sum_vonMangoldt (n : ℕ) :
    logFact n = ∑ d ∈ Finset.Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
  unfold logFact
  have h1 : ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) =
      ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ k.divisors, Λ d := by
    apply Finset.sum_congr rfl
    intro k _
    exact (ArithmeticFunction.vonMangoldt_sum).symm
  rw [h1]
  have h2 : ∀ k ∈ Finset.Icc 1 n,
      ∑ d ∈ k.divisors, Λ d = ∑ d ∈ Finset.Icc 1 n, if d ∣ k then Λ d else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, hkne⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), (Nat.le_of_dvd (by omega) hdvd).trans hk.2⟩, hdvd⟩
    · rintro ⟨_, hdvd⟩
      exact ⟨hdvd, by omega⟩
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Icc] at hd
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have hcard : ({k ∈ Finset.Icc 1 n | d ∣ k}).card = (Finset.range (n / d)).card := by
    refine Finset.card_bij (fun k _ => k / d - 1) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hk ⊢
      have h1 : 1 ≤ k / d := Nat.div_pos (Nat.le_of_dvd (by omega) hk.2) (by omega)
      have h2 : k / d ≤ n / d := Nat.div_le_div_right hk.1.2
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
      have ha1 : 1 ≤ a / d := Nat.div_pos (Nat.le_of_dvd (by omega) ha.2) (by omega)
      have hb1 : 1 ≤ b / d := Nat.div_pos (Nat.le_of_dvd (by omega) hb.2) (by omega)
      have hq : a / d = b / d := by omega
      rw [← Nat.mul_div_cancel' ha.2, ← Nat.mul_div_cancel' hb.2, hq]
    · intro m hm
      rw [Finset.mem_range] at hm
      refine ⟨d * (m + 1), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d (m + 1)⟩
        calc d * (m + 1) ≤ d * (n / d) := Nat.mul_le_mul_left d (by omega)
          _ ≤ n := Nat.mul_div_le n d
      · rw [Nat.mul_div_cancel_left _ (by omega)]
        omega
  simpa using hcard

private lemma cheb30_floor_ineq (u : ℕ) :
    ((if 1 ≤ u then (1 : ℤ) else 0) - (if 6 ≤ u then (1 : ℤ) else 0)) ≤
      (u : ℤ) - (u / 2 : ℕ) - (u / 3 : ℕ) - (u / 5 : ℕ) + (u / 30 : ℕ) := by
  omega

private lemma psi_sub_psi_div6_le (n : ℕ) :
    ψ (n : ℝ) - ψ ((n / 6 : ℕ) : ℝ) ≤
      logFact n - logFact (n / 2) - logFact (n / 3) - logFact (n / 5) + logFact (n / 30) := by
  have hT : ∀ c : ℕ, 1 ≤ c →
      logFact (n / c) = ∑ d ∈ Finset.Icc 1 n, Λ d * ((n / d / c : ℕ) : ℝ) := by
    intro c hc
    rw [logFact_eq_sum_vonMangoldt (n / c)]
    have hsub : Finset.Icc 1 (n / c) ⊆ Finset.Icc 1 n :=
      Finset.Icc_subset_Icc_right (Nat.div_le_self n c)
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro d _
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm c d]
    · intro d hd hdnot
      rw [Finset.mem_Icc] at hd hdnot
      have hgt : n / c < d := by omega
      have hz : n / d / c = 0 := by
        rw [Nat.div_div_eq_div_mul, mul_comm d c, ← Nat.div_div_eq_div_mul]
        exact Nat.div_eq_of_lt hgt
      simp [hz]
  rw [logFact_eq_sum_vonMangoldt n, hT 2 (by omega), hT 3 (by omega),
      hT 5 (by omega), hT 30 (by omega)]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have hpsi_Icc1 : ∀ m : ℕ, ψ (m : ℝ) = ∑ d ∈ Finset.Icc 1 m, Λ d := by
    intro m
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    symm
    apply Finset.sum_subset (Finset.Icc_subset_Icc_left (by omega : 0 ≤ 1))
    intro d hd hdnot
    rw [Finset.mem_Icc] at hd hdnot
    have hd0 : d = 0 := by omega
    subst hd0; simp
  have hpsi_n : ψ (n : ℝ) = ∑ d ∈ Finset.Icc 1 n, Λ d * (if 1 ≤ n / d then (1 : ℝ) else 0) := by
    rw [hpsi_Icc1 n]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_Icc] at hd
    have : 1 ≤ n / d := Nat.div_pos hd.2 (by omega)
    simp [this]
  have hpsi_6 : ψ ((n / 6 : ℕ) : ℝ) = ∑ d ∈ Finset.Icc 1 n, Λ d * (if 6 ≤ n / d then (1 : ℝ) else 0) := by
    rw [hpsi_Icc1 (n / 6)]
    have hsub : Finset.Icc 1 (n / 6) ⊆ Finset.Icc 1 n :=
      Finset.Icc_subset_Icc_right (Nat.div_le_self n 6)
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_Icc] at hd
      have h6 : 6 ≤ n / d := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        calc 6 * d ≤ 6 * (n / 6) := Nat.mul_le_mul_left 6 hd.2
          _ ≤ n := Nat.mul_div_le n 6
      simp [h6]
    · intro d hd hdnot
      rw [Finset.mem_Icc] at hd hdnot
      have hlt : n / d < 6 := by
        by_contra hge
        push Not at hge
        have : d ≤ n / 6 := by
          rw [Nat.le_div_iff_mul_le (by omega)]
          have := (Nat.le_div_iff_mul_le (by omega)).mp hge
          linarith
        exact hdnot ⟨hd.1, this⟩
      have hnot : ¬ 6 ≤ n / d := by omega
      simp [hnot]
  rw [hpsi_n, hpsi_6, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro d _
  have hfl := cheb30_floor_ineq (n / d)
  have hflR : ((if 1 ≤ n / d then (1 : ℝ) else 0) - (if 6 ≤ n / d then (1 : ℝ) else 0)) ≤
      ((n / d : ℕ) : ℝ) - ((n / d / 2 : ℕ) : ℝ) - ((n / d / 3 : ℕ) : ℝ) -
        ((n / d / 5 : ℕ) : ℝ) + ((n / d / 30 : ℕ) : ℝ) := by
    have hcast : (((if 1 ≤ n / d then (1 : ℤ) else 0) - (if 6 ≤ n / d then (1 : ℤ) else 0) : ℤ) : ℝ) ≤
        (((n / d : ℕ) : ℤ) - (n / d / 2 : ℕ) - (n / d / 3 : ℕ) - (n / d / 5 : ℕ) + (n / d / 30 : ℕ) : ℤ) := by
      exact_mod_cast hfl
    simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast] at hcast
    by_cases h1 : 1 ≤ n / d <;> by_cases h6 : 6 ≤ n / d <;> simp [h1, h6] at hcast ⊢ <;> linarith
  have hlam : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  nlinarith

private lemma xlogx_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b * Real.log b - b) - (a * Real.log a - a) ≤ (b - a) * Real.log b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hlog : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog ha.le
  have hsimp : a * (b / a - 1) = b - a := by field_simp
  linarith

private lemma cheb30_E_le {n : ℕ} (hn : 30 ≤ n) :
    logFact n - logFact (n / 2) - logFact (n / 3) - logFact (n / 5) + logFact (n / 30) ≤
      0.9213 * (n : ℝ) + 5 * Real.log ((n : ℝ) + 1) := by
  have hnR : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hT1 := logFact_le (show 1 ≤ n by omega)
  have hT2 := logFact_ge (show 1 ≤ n / 2 by omega)
  have hT3 := logFact_ge (show 1 ≤ n / 3 by omega)
  have hT5 := logFact_ge (show 1 ≤ n / 5 by omega)
  have hT30 := logFact_le (show 1 ≤ n / 30 by omega)
  -- Convert n/k floors to exact reals n/k using xlogx_sub_le
  have hdiv_lb : ∀ c : ℕ, 2 ≤ c → c ≤ 5 →
      ((n : ℝ) / c) * Real.log ((n : ℝ) / c) - (n : ℝ) / c - Real.log ((n : ℝ) + 1) ≤
        ((n / c : ℕ) : ℝ) * Real.log ((n / c : ℕ) : ℝ) - ((n / c : ℕ) : ℝ) := by
    intro c hc2 hc5
    have hcr : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc2
    have hcr5 : (c : ℝ) ≤ 5 := by exact_mod_cast hc5
    have hfl_pos : (1 : ℝ) ≤ ((n / c : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_pos (by omega : c ≤ n) (by omega : 0 < c))
    have hfl_le : ((n / c : ℕ) : ℝ) ≤ (n : ℝ) / (c : ℝ) := Nat.cast_div_le
    have hdiff_le : (n : ℝ) / (c : ℝ) - ((n / c : ℕ) : ℝ) ≤ 1 := by
      have h1 : n < (n / c + 1) * c := by
        have := Nat.lt_div_mul_add (a := n) (b := c) (by omega)
        linarith
      have h1r : (n : ℝ) < (((n / c : ℕ) : ℝ) + 1) * (c : ℝ) := by exact_mod_cast h1
      have : (n : ℝ) / (c : ℝ) < ((n / c : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ (by positivity)]
        exact h1r
      linarith
    have hmv := xlogx_sub_le (by linarith : (0 : ℝ) < ((n / c : ℕ) : ℝ)) hfl_le
    have hlog_le : Real.log ((n : ℝ) / (c : ℝ)) ≤ Real.log ((n : ℝ) + 1) := by
      apply Real.log_le_log (by positivity)
      have : (n : ℝ) / (c : ℝ) ≤ (n : ℝ) := div_le_self (by positivity) (by linarith)
      linarith
    have hlog_nn : 0 ≤ Real.log ((n : ℝ) / (c : ℝ)) :=
      Real.log_nonneg (by rw [one_le_div (by positivity)]; linarith)
    nlinarith
  have h2 := hdiv_lb 2 (by omega) (by omega)
  have h3 := hdiv_lb 3 (by omega) (by omega)
  have h5 := hdiv_lb 5 (by omega) (by omega)
  -- For T(n): (n+1) log(n+1) - n <= n log n - n + log(n+1) + 1
  have hT1' : ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) - (n : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log ((n : ℝ) + 1) + 1 := by
    have hlog : Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ ((n : ℝ) + 1) / (n : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ (n : ℝ))
    have hsimp : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by field_simp; ring
    linarith
  -- For T(n/30): ((n/30)+1) log((n/30)+1) - (n/30) <= (n/30) log(n/30) - n/30 + log(n+1) + 2
  have hT30' : (((n / 30 : ℕ) : ℝ) + 1) * Real.log (((n / 30 : ℕ) : ℝ) + 1) - ((n / 30 : ℕ) : ℝ) ≤
      ((n : ℝ) / 30) * Real.log ((n : ℝ) / 30) - (n : ℝ) / 30 + Real.log ((n : ℝ) + 1) + 2 := by
    have hfl_le : ((n / 30 : ℕ) : ℝ) ≤ (n : ℝ) / 30 := Nat.cast_div_le
    have hfl_ge : (n : ℝ) / 30 - 1 ≤ ((n / 30 : ℕ) : ℝ) := by
      have h1 : n < (n / 30 + 1) * 30 := by
        have := Nat.lt_div_mul_add (a := n) (b := 30) (by omega)
        linarith
      have h1r : (n : ℝ) < (((n / 30 : ℕ) : ℝ) + 1) * 30 := by exact_mod_cast h1
      linarith
    have hlog1 : Real.log (((n / 30 : ℕ) : ℝ) + 1) ≤ Real.log ((n : ℝ) / 30 + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog2 : Real.log (((n : ℝ) / 30 + 1) / ((n : ℝ) / 30)) ≤
        ((n : ℝ) / 30 + 1) / ((n : ℝ) / 30) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at hlog2
    have hmul := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ (n : ℝ) / 30)
    have hsimp : ((n : ℝ) / 30) * (((n : ℝ) / 30 + 1) / ((n : ℝ) / 30) - 1) = 1 := by field_simp; ring
    have hlog3 : Real.log ((n : ℝ) / 30 + 1) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog_nn : 0 ≤ Real.log (((n / 30 : ℕ) : ℝ) + 1) := Real.log_nonneg (by linarith)
    nlinarith
  -- Expand log(n/c) = log n - log c
  have hl2 : Real.log ((n : ℝ) / 2) = Real.log (n : ℝ) - Real.log 2 :=
    Real.log_div (by positivity) (by norm_num)
  have hl3 : Real.log ((n : ℝ) / 3) = Real.log (n : ℝ) - Real.log 3 :=
    Real.log_div (by positivity) (by norm_num)
  have hl5 : Real.log ((n : ℝ) / 5) = Real.log (n : ℝ) - Real.log 5 :=
    Real.log_div (by positivity) (by norm_num)
  have hl30 : Real.log ((n : ℝ) / 30) = Real.log (n : ℝ) - (Real.log 2 + Real.log 3 + Real.log 5) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    have h30 : (30 : ℝ) = 2 * 3 * 5 := by norm_num
    rw [h30, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have hA : Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 -
      (Real.log 2 + Real.log 3 + Real.log 5) / 30 ≤ 0.9213 := by
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]
  have hAn : (Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 -
      (Real.log 2 + Real.log 3 + Real.log 5) / 30) * (n : ℝ) ≤ 0.9213 * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hA (by positivity)
  push_cast at h2 h3 h5
  rw [hl2] at h2
  rw [hl3] at h3
  rw [hl5] at h5
  rw [hl30] at hT30'
  have halg :
      ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log ((n : ℝ) + 1) + 1)
      - ((n : ℝ) / 2 * (Real.log (n : ℝ) - Real.log 2) - (n : ℝ) / 2 - Real.log ((n : ℝ) + 1) + 1)
      - ((n : ℝ) / 3 * (Real.log (n : ℝ) - Real.log 3) - (n : ℝ) / 3 - Real.log ((n : ℝ) + 1) + 1)
      - ((n : ℝ) / 5 * (Real.log (n : ℝ) - Real.log 5) - (n : ℝ) / 5 - Real.log ((n : ℝ) + 1) + 1)
      + ((n : ℝ) / 30 * (Real.log (n : ℝ) - (Real.log 2 + Real.log 3 + Real.log 5)) - (n : ℝ) / 30 + Real.log ((n : ℝ) + 1) + 2)
      = (Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 -
          (Real.log 2 + Real.log 3 + Real.log 5) / 30) * (n : ℝ) + 5 * Real.log ((n : ℝ) + 1) := by
    ring
  linarith

private lemma psi_le_cheb30 (n : ℕ) :
    ψ (n : ℝ) ≤ 1.1056 * (n : ℝ) + 4 * (Real.log ((n : ℝ) + 1)) ^ 2 +
      30 * Real.log ((n : ℝ) + 1) + 40 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 30
    · rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
      have hIcc1 : ∑ d ∈ Finset.Icc 0 n, Λ d = ∑ d ∈ Finset.Icc 1 n, Λ d := by
        symm
        apply Finset.sum_subset (Finset.Icc_subset_Icc_left (by omega : 0 ≤ 1))
        intro d hd hdnot
        rw [Finset.mem_Icc] at hd hdnot
        have hd0 : d = 0 := by omega
        subst hd0; simp
      rw [hIcc1]
      have hsum : ∑ d ∈ Finset.Icc 1 n, Λ d ≤ ∑ _d ∈ Finset.Icc 1 n, Real.log ((n : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [Finset.mem_Icc] at hd
        calc Λ d ≤ Real.log (d : ℝ) := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by exact_mod_cast hd.1) (by exact_mod_cast (show d ≤ n + 1 by omega))
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
      have hcard : (n + 1 - 1 : ℕ) = n := by omega
      rw [hcard] at hsum
      have hnr : (n : ℝ) ≤ 30 := by exact_mod_cast (show n ≤ 30 by omega)
      have hlog_nn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
      nlinarith [sq_nonneg (Real.log ((n : ℝ) + 1))]
    · push Not at hn
      have hstep := psi_sub_psi_div6_le n
      have hE := cheb30_E_le hn
      have hih := ih (n / 6) (Nat.div_lt_self (by omega) (by omega))
      have hdiv6_le : ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) / 6 := Nat.cast_div_le
      have hlog6 : Real.log (((n / 6 : ℕ) : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log 3 := by
        have h3le : 3 * (n / 6 + 1) ≤ n + 1 := by omega
        have h3r : 3 * (((n / 6 : ℕ) : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast h3le
        have h := Real.log_le_log (by positivity) h3r
        rw [Real.log_mul (by norm_num) (by positivity)] at h
        linarith
      have hlog6_nn : 0 ≤ Real.log (((n / 6 : ℕ) : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (n / 6)])
      have hlog_ge : Real.log 3 ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ n + 1 by omega))
      have hsq : (Real.log (((n / 6 : ℕ) : ℝ) + 1)) ^ 2 ≤
          (Real.log ((n : ℝ) + 1) - Real.log 3) ^ 2 := by
        nlinarith
      have hl3_gt := Real.log_three_gt_d9
      have hl3_lt := Real.log_three_lt_d9
      have hnr : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith



/-! ## Explicit upper bound on `π(x)` for `x ≥ 65536` -/

private lemma theta_le_cheb30 {t : ℝ} (ht : 0 ≤ t) :
    θ t ≤ 1.1056 * t + 4 * (Real.log (t + 1)) ^ 2 + 30 * Real.log (t + 1) + 40 := by
  have h1 : θ t ≤ ψ t := Chebyshev.theta_le_psi t
  rw [Chebyshev.psi_eq_psi_coe_floor t] at h1
  have h2 := psi_le_cheb30 ⌊t⌋₊
  have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have hlog_le : Real.log ((⌊t⌋₊ : ℝ) + 1) ≤ Real.log (t + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog_nn : 0 ≤ Real.log ((⌊t⌋₊ : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) ⌊t⌋₊])
  nlinarith

private lemma integral_theta_small_piece {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, θ t / (t * (Real.log t) ^ 2) ≤ (b - a) * (2 * Real.log 2) / (Real.log a) ^ 2 := by
  have hint1 : IntervalIntegrable (fun t => θ t / (t * (Real.log t) ^ 2)) MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq b).mono_set
      (Set.Icc_subset_Icc_left ha)
  have hint2 : IntervalIntegrable (fun _ : ℝ => (2 * Real.log 2) / (Real.log a) ^ 2) MeasureTheory.volume a b :=
    intervalIntegrable_const
  calc ∫ t in a..b, θ t / (t * (Real.log t) ^ 2)
    _ ≤ ∫ _t in a..b, (2 * Real.log 2) / (Real.log a) ^ 2 := by
          apply intervalIntegral.integral_mono_on hab hint1 hint2
          intro t ⟨hta, _⟩
          have ht_pos : 0 < t := by linarith
          have hlog_a_pos : 0 < Real.log a := Real.log_pos (by linarith)
          have hlog_le : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) hta
          have hth : θ t ≤ 2 * Real.log 2 * t := by
            have := Chebyshev.theta_le_log4_mul_x (by linarith : 0 ≤ t)
            rwa [Real.log_four_eq] at this
          have hsq : (Real.log a) ^ 2 ≤ (Real.log t) ^ 2 := by nlinarith
          have hdiv1 : θ t / (t * (Real.log t) ^ 2) ≤ (2 * Real.log 2 * t) / (t * (Real.log t) ^ 2) :=
            div_le_div_of_nonneg_right hth (by positivity)
          have hcancel : (2 * Real.log 2 * t) / (t * (Real.log t) ^ 2) = (2 * Real.log 2) / (Real.log t) ^ 2 := by
            field_simp
          have hdiv2 : (2 * Real.log 2) / (Real.log t) ^ 2 ≤ (2 * Real.log 2) / (Real.log a) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
          linarith
    _ = (b - a) * (2 * Real.log 2) / (Real.log a) ^ 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring

private lemma hasDerivAt_id_div_log_sq {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (fun u => u / (Real.log u) ^ 2) ((1 - 2 / Real.log t) / (Real.log t) ^ 2) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
  have h1 : HasDerivAt (fun u => u) 1 t := hasDerivAt_id t
  have h2 : HasDerivAt (fun u => (Real.log u) ^ 2) (2 * Real.log t * t⁻¹) t := by
    have hmul := (Real.hasDerivAt_log ht0).mul (Real.hasDerivAt_log ht0)
    have hsq : (fun u => (Real.log u) ^ 2) = (fun u => Real.log u * Real.log u) := by
      ext u; ring
    have heq2 : t⁻¹ * Real.log t + Real.log t * t⁻¹ = 2 * Real.log t * t⁻¹ := by ring
    rw [hsq, ← heq2]
    exact hmul
  have hd := h1.div h2 (pow_ne_zero 2 hl0)
  have heq : (1 * (Real.log t) ^ 2 - t * (2 * Real.log t * t⁻¹)) / ((Real.log t) ^ 2) ^ 2 =
      (1 - 2 / Real.log t) / (Real.log t) ^ 2 := by
    field_simp [ht0, hl0]
  rwa [heq] at hd

private lemma pi_le_explicit {x : ℝ} (hx : 65536 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      1.1056 * x / Real.log x + 1.1056 * (11 / 9) * x / (Real.log x) ^ 2 +
        1900 + 14 * Real.log x := by
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral (by linarith)]
  have hint_all : ∀ a b : ℝ, 2 ≤ a → a ≤ b → b ≤ x →
      IntervalIntegrable (fun t => θ t / (t * (Real.log t) ^ 2)) MeasureTheory.volume a b := by
    intro a b ha hab hbx
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (Set.Icc_subset_Icc ha hbx)
  -- Split ∫ 2..x into [2,64], [64,2048], [2048,65536], [65536,x]
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hint_all 2 64 (by norm_num) (by norm_num) (by linarith))
    (hint_all 64 x (by norm_num) (by linarith) le_rfl)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hint_all 64 2048 (by norm_num) (by norm_num) (by linarith))
    (hint_all 2048 x (by norm_num) (by linarith) le_rfl)
  have hsplit3 := intervalIntegral.integral_add_adjacent_intervals
    (hint_all 2048 65536 (by norm_num) (by norm_num) hx)
    (hint_all 65536 x (by norm_num) hx le_rfl)
  have hp1 := integral_theta_small_piece (a := 2) (b := 64) (by norm_num) (by norm_num)
  have hp2 := integral_theta_small_piece (a := 64) (b := 2048) (by norm_num) (by norm_num)
  have hp3 := integral_theta_small_piece (a := 2048) (b := 65536) (by norm_num) (by norm_num)
  have hl64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hl2048 : Real.log 2048 = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ (11 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hl65536 : Real.log 65536 = 16 * Real.log 2 := by
    rw [show (65536 : ℝ) = 2 ^ (16 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hl2_gt := Real.log_two_gt_d9
  have hl2_lt := Real.log_two_lt_d9
  have hp1_num : (64 - 2) * (2 * Real.log 2) / (Real.log 2) ^ 2 ≤ 180 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hp2_num : (2048 - 64) * (2 * Real.log 2) / (Real.log 64) ^ 2 ≤ 160 := by
    rw [hl64, div_le_iff₀ (by positivity)]
    nlinarith
  have hp3_num : (65536 - 2048) * (2 * Real.log 2) / (Real.log 2048) ^ 2 ≤ 1515 := by
    rw [hl2048, div_le_iff₀ (by positivity)]
    nlinarith
  -- Tail integral on [65536, x]
  let F : ℝ → ℝ := fun t => 1.1056 * (11 / 9) * (t / (Real.log t) ^ 2) + 9 * Real.log t
  let F' : ℝ → ℝ := fun t => 1.1056 * (11 / 9) * ((1 - 2 / Real.log t) / (Real.log t) ^ 2) + 9 * t⁻¹
  have hFderiv : ∀ t ∈ Set.uIcc 65536 x, HasDerivAt F (F' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht2 : 2 ≤ t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    exact ((hasDerivAt_id_div_log_sq ht2).const_mul _).add ((Real.hasDerivAt_log ht0).const_mul 9)
  have hF'int : IntervalIntegrable F' MeasureTheory.volume 65536 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht_pos : 0 < t := by linarith [ht.1]
    have hl0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    apply ContinuousAt.continuousWithinAt
    unfold F'
    fun_prop (disch := positivity)
  have htail_le : ∫ t in (65536 : ℝ)..x, θ t / (t * (Real.log t) ^ 2) ≤ F x - F 65536 := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv hF'int]
    apply intervalIntegral.integral_mono_on hx (hint_all 65536 x (by norm_num) hx le_rfl) hF'int
    intro t ⟨ht1, _⟩
    have hlt_ge : 11 ≤ Real.log t := by
      have := Real.log_le_log (by norm_num) ht1
      linarith [hl65536]
    have hlog1 : Real.log (t + 1) ≤ (11 / 10) * Real.log t := by
      have h := Real.log_le_sub_one_of_pos (show 0 < (t + 1) / t by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have hinv : (t + 1) / t - 1 ≤ 1 / 65536 := by
        rw [show (t + 1) / t - 1 = 1 / t by field_simp; ring]
        exact div_le_div_of_nonneg_left zero_le_one (by norm_num) ht1
      linarith
    have hth := theta_le_cheb30 (by linarith : 0 ≤ t)
    have hlt_pos : 0 < Real.log t := by linarith
    have hlog1_nn : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
    have hsq1 : (Real.log (t + 1)) ^ 2 ≤ ((11 / 10) * Real.log t) ^ 2 := by nlinarith
    have hnum_le : θ t ≤ 1.1056 * t + 9 * (Real.log t) ^ 2 := by
      nlinarith
    have hdiv_le : θ t / (t * (Real.log t) ^ 2) ≤ 1.1056 / (Real.log t) ^ 2 + 9 * t⁻¹ := by
      have h1 := div_le_div_of_nonneg_right hnum_le (show 0 ≤ t * (Real.log t) ^ 2 by positivity)
      have h2 : (1.1056 * t + 9 * (Real.log t) ^ 2) / (t * (Real.log t) ^ 2) =
          1.1056 / (Real.log t) ^ 2 + 9 * t⁻¹ := by
        field_simp
      linarith
    have hfac : 9 / 11 ≤ 1 - 2 / Real.log t := by
      have : 2 / Real.log t ≤ 2 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlt_ge
      linarith
    have hterm1 : 1.1056 / (Real.log t) ^ 2 ≤
        1.1056 * (11 / 9) * ((1 - 2 / Real.log t) / (Real.log t) ^ 2) := by
      have : 1 ≤ (11 / 9 : ℝ) * (1 - 2 / Real.log t) := by linarith
      have h := mul_le_mul_of_nonneg_right this (show 0 ≤ 1.1056 / (Real.log t) ^ 2 by positivity)
      have heq : (11 / 9 : ℝ) * (1 - 2 / Real.log t) * (1.1056 / (Real.log t) ^ 2) =
          1.1056 * (11 / 9) * ((1 - 2 / Real.log t) / (Real.log t) ^ 2) := by ring
      linarith
    dsimp [F']
    linarith
  have hF65536_nn : 0 ≤ F 65536 := by
    dsimp [F]
    have : 0 ≤ Real.log 65536 := Real.log_nonneg (by norm_num)
    positivity
  -- Bound θ x / log x
  have hlx_ge : 11 ≤ Real.log x := by
    have := Real.log_le_log (by norm_num) hx
    linarith [hl65536]
  have hlogx1 : Real.log (x + 1) ≤ (11 / 10) * Real.log x := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h
    have hinv : (x + 1) / x - 1 ≤ 1 / 65536 := by
      rw [show (x + 1) / x - 1 = 1 / x by field_simp; ring]
      exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hx
    linarith
  have hth_x := theta_le_cheb30 (by linarith : 0 ≤ x)
  have hth_x_div : θ x / Real.log x ≤ 1.1056 * x / Real.log x + 5 * Real.log x + 45 := by
    rw [div_le_iff₀ (by linarith)]
    have hlogx1_nn : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    have hsq1 : (Real.log (x + 1)) ^ 2 ≤ ((11 / 10) * Real.log x) ^ 2 := by nlinarith
    have hrew : (1.1056 * x / Real.log x + 5 * Real.log x + 45) * Real.log x =
        1.1056 * x + 5 * (Real.log x) ^ 2 + 45 * Real.log x := by field_simp
    rw [hrew]
    nlinarith
  dsimp [F] at htail_le hF65536_nn
  have hmul_eq : 1.1056 * (11 / 9) * (x / (Real.log x) ^ 2) =
      1.1056 * (11 / 9) * x / (Real.log x) ^ 2 := by ring
  linarith

/-! ## All `n ≥ 1,000,000`: `2 * π(n) < φ(n)` -/

private lemma totient_cube_ge_large {n : ℕ} (hn : 7420738134810 ≤ n) :
    (0.117 : ℝ) / (6 * Real.log (n : ℝ) + 7) ≤ ((n.totient : ℝ) / (n : ℝ)) ^ 3 := by
  have hn_pos : 0 < n := by omega
  have hnR : (7420738134810 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Lower bound log n >= 29.24
  have hlog_ge : (29.24 : ℝ) ≤ Real.log (n : ℝ) := by
    have hle : (5 * 10 ^ 12 : ℝ) ≤ (n : ℝ) := by linarith
    have h := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_ten_eq] at h
    push_cast at h
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  let K : ℕ := ⌈Real.log (n : ℝ)⌉₊
  have hK_ge_log : Real.log (n : ℝ) ≤ (K : ℝ) := Nat.le_ceil _
  have hK_lt : (K : ℝ) < Real.log (n : ℝ) + 1 := Nat.ceil_lt_add_one (by linarith)
  have hK_ge : 30 ≤ K := by
    have : (29 : ℝ) < (K : ℝ) := by linarith
    exact_mod_cast (show 29 < K by exact_mod_cast this)
  let P := n.primeFactors
  let P1 := P.filter (fun p => p ≤ 47)
  let P2 := P.filter (fun p => 47 < p ∧ p ≤ 6 * K + 1)
  let P3 := P.filter (fun p => 6 * K + 1 < p)
  have hP_part : ∏ p ∈ P, (1 - 1 / (p : ℝ)) =
      (∏ p ∈ P1, (1 - 1 / (p : ℝ))) *
      (∏ p ∈ P2, (1 - 1 / (p : ℝ))) *
      (∏ p ∈ P3, (1 - 1 / (p : ℝ))) := by
    have h12 : P1 ∪ P2 = P.filter (fun p => p ≤ 6 * K + 1) := by
      ext p; simp only [P1, P2, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, h1⟩ | ⟨h, _, h2⟩) <;> exact ⟨h, by omega⟩
      · rintro ⟨h, h2⟩
        by_cases h1 : p ≤ 47
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr ⟨h, by omega, h2⟩
    have hd12 : Disjoint P1 P2 := by
      rw [Finset.disjoint_left]; intro p h1 h2
      simp only [P1, P2, Finset.mem_filter] at h1 h2; omega
    have h123 : (P1 ∪ P2) ∪ P3 = P := by
      rw [h12]; ext p; simp only [P3, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hle : p ≤ 6 * K + 1
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr ⟨h, by omega⟩
    have hd123 : Disjoint (P1 ∪ P2) P3 := by
      rw [h12, Finset.disjoint_left]; intro p h1 h2
      simp only [P3, Finset.mem_filter] at h1 h2; omega
    rw [← h123, Finset.prod_union hd123, Finset.prod_union hd12]
  -- Helper: shrinking a Finset with factors in (0, 1] increases the product
  have hprod_anti : ∀ A B : Finset ℕ, A ⊆ B → (∀ p ∈ B, 2 ≤ p) →
      ∏ p ∈ B, (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ A, (1 - 1 / (p : ℝ)) := by
    intro A B hAB hB2
    rw [← Finset.union_sdiff_of_subset hAB, Finset.prod_union disjoint_sdiff_self_right]
    have h1 : 0 ≤ ∏ p ∈ A, (1 - 1 / (p : ℝ)) := Finset.prod_nonneg fun p hp => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hB2 p (hAB hp)
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have h2 : ∏ p ∈ B \ A, (1 - 1 / (p : ℝ)) ≤ 1 := Finset.prod_le_one (fun p hp => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hB2 p (Finset.sdiff_subset hp)
      rw [sub_nonneg, div_le_one (by linarith)]; linarith) (fun p hp => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hB2 p (Finset.sdiff_subset hp)
      linarith [div_nonneg zero_le_one (show (0 : ℝ) ≤ p by linarith)])
    nlinarith
  -- Part 1: P1 ⊆ primes47
  let primes47 : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47}
  have hP1_sub : P1 ⊆ primes47 := by
    intro p hp
    simp only [P1, Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp.1
    have h47 := hp.2
    have hdec : ∀ q ∈ Finset.range 48, q.Prime → q ∈ primes47 := by decide
    exact hdec p (Finset.mem_range.mpr (by omega)) hpp
  have hP1_ge : (0.1387 : ℝ) ≤ ∏ p ∈ P1, (1 - 1 / (p : ℝ)) := by
    have h1 := hprod_anti P1 primes47 hP1_sub (by decide)
    have hrew : ∏ p ∈ primes47, (1 - 1 / (p : ℝ)) =
        ((∏ p ∈ primes47, (p - 1) : ℕ) : ℝ) / ((∏ p ∈ primes47, p : ℕ) : ℝ) := by
      push_cast
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp1 : 1 ≤ p := by
        have h : ∀ q ∈ primes47, 2 ≤ q := by decide
        have := h p hp; omega
      have hp0 : (p : ℝ) ≠ 0 := by positivity
      rw [Nat.cast_sub hp1, Nat.cast_one]
      field_simp
    have hnum : ∏ p ∈ primes47, (p - 1) = 85287729364992000 := by decide
    have hden : ∏ p ∈ primes47, p = 614889782588491410 := by decide
    have h2 : (0.1387 : ℝ) ≤ ∏ p ∈ primes47, (1 - 1 / (p : ℝ)) := by
      rw [hrew, hnum, hden]
      norm_num
    linarith
  -- Part 2: P2 ⊆ ⋃ j ∈ Icc 9 K, {6j - 1, 6j + 1}
  let B2 : Finset ℕ := (Finset.Icc 9 K).biUnion (fun j => {6 * j - 1, 6 * j + 1})
  have hP2_sub : P2 ⊆ B2 := by
    intro p hp
    simp only [P2, Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp.1
    have hnot2 : p % 2 ≠ 0 := fun h => by
      have h2dvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
      rcases hpp.eq_one_or_self_of_dvd 2 h2dvd with h1 | h2 <;> omega
    have hnot3 : p % 3 ≠ 0 := fun h => by
      have h3dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      rcases hpp.eq_one_or_self_of_dvd 3 h3dvd with h1 | h3 <;> omega
    have hp47 : 47 < p := hp.2.1
    have hpK : p ≤ 6 * K + 1 := hp.2.2
    have hp49 : p ≠ 49 := fun h => by subst h; exact absurd hpp (by decide)
    rw [Finset.mem_biUnion]
    rcases (show p % 6 = 1 ∨ p % 6 = 5 by omega) with h1 | h5
    · refine ⟨p / 6, ?_, ?_⟩
      · rw [Finset.mem_Icc]; omega
      · simp; omega
    · refine ⟨p / 6 + 1, ?_, ?_⟩
      · rw [Finset.mem_Icc]; omega
      · simp; omega
  have hB2_eq : ∏ p ∈ B2, (1 - 1 / (p : ℝ)) =
      ∏ j ∈ Finset.Icc 9 K,
        (((6 * (j : ℝ) - 2) / (6 * (j : ℝ) - 1)) * ((6 * (j : ℝ)) / (6 * (j : ℝ) + 1))) := by
    rw [Finset.prod_biUnion]
    · apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.prod_pair (by omega)]
      have hj1 : 1 ≤ 6 * j := by omega
      rw [Nat.cast_sub hj1]
      push_cast
      have h1 : (6 * (j : ℝ) - 1) ≠ 0 := by
        have : (9 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
        linarith
      have h2 : (6 * (j : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_Icc] at hi hj
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx1 hx2
      simp at hx1 hx2
      omega
  have hP2_nn : 0 ≤ ∏ p ∈ P2, (1 - 1 / (p : ℝ)) := Finset.prod_nonneg fun p hp => by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      simp only [P2, Finset.mem_filter] at hp
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp.1).two_le
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hB2_nn : 0 ≤ ∏ p ∈ B2, (1 - 1 / (p : ℝ)) := Finset.prod_nonneg fun p hp => by
    rw [Finset.mem_biUnion] at hp
    rcases hp with ⟨j, hj, hpj⟩
    rw [Finset.mem_Icc] at hj; simp at hpj
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 2 ≤ p by omega)
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hP2_ge_B2 : ∏ p ∈ B2, (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ P2, (1 - 1 / (p : ℝ)) := by
    apply hprod_anti P2 B2 hP2_sub
    intro p hp
    rw [Finset.mem_biUnion] at hp
    rcases hp with ⟨j, hj, hpj⟩
    rw [Finset.mem_Icc] at hj; simp at hpj; omega
  have hP2_cube : (49 : ℝ) / (6 * (K : ℝ) + 1) ≤ (∏ p ∈ P2, (1 - 1 / (p : ℝ))) ^ 3 := by
    have h1 := mod6_prod_cube_ge K (by omega)
    rw [← hB2_eq] at h1
    exact h1.trans (pow_le_pow_left₀ hB2_nn hP2_ge_B2 3)
  -- Part 3: P3 tail via Bernoulli
  have hP3_ge : (0.965 : ℝ) ≤ ∏ p ∈ P3, (1 - 1 / (p : ℝ)) := by
    let s := P3.card
    have hM_pos : (0 : ℝ) < (6 * (K : ℝ) + 1) := by positivity
    have hM_ge : (181 : ℝ) ≤ 6 * (K : ℝ) + 1 := by
      have : (30 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_ge
      linarith
    have hpow_le : (6 * K + 1) ^ s ≤ n := by
      calc (6 * K + 1) ^ s = ∏ _p ∈ P3, (6 * K + 1) := (Finset.prod_const _).symm
        _ ≤ ∏ p ∈ P3, p := Finset.prod_le_prod' fun p hp => by
              simp only [P3, Finset.mem_filter] at hp; omega
        _ ≤ ∏ p ∈ P, p := Finset.prod_le_prod_of_subset_of_one_le'
              (Finset.filter_subset _ P) (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_le)
        _ ≤ n := Nat.le_of_dvd hn_pos (Nat.prod_primeFactors_dvd n)
    have hs_log : (s : ℝ) * Real.log (6 * (K : ℝ) + 1) ≤ Real.log (n : ℝ) := by
      have hpowR : ((6 * (K : ℝ) + 1) ^ s) ≤ (n : ℝ) := by exact_mod_cast hpow_le
      have h := Real.log_le_log (by positivity) hpowR
      rwa [Real.log_pow] at h
    have hlogM_ge : (4.85 : ℝ) ≤ Real.log (6 * (K : ℝ) + 1) := by
      have h128 : (2 ^ (7 : ℕ) : ℝ) ≤ 6 * (K : ℝ) + 1 := by norm_num; linarith
      have h := Real.log_le_log (by positivity) h128
      rw [Real.log_pow] at h; push_cast at h
      linarith [Real.log_two_gt_d9]
    have hs_div : (s : ℝ) / (6 * (K : ℝ) + 1) ≤ 0.035 := by
      rw [div_le_iff₀ hM_pos]
      have h1 : (s : ℝ) * 4.85 ≤ Real.log (n : ℝ) := by nlinarith
      have h2 : 6 * Real.log (n : ℝ) ≤ 6 * (K : ℝ) + 1 := by linarith
      nlinarith
    have hbern : 1 - (s : ℝ) / (6 * (K : ℝ) + 1) ≤ (1 - 1 / (6 * (K : ℝ) + 1)) ^ s := by
      have := one_add_mul_le_pow (a := -(1 / (6 * (K : ℝ) + 1))) (by
        have : 1 / (6 * (K : ℝ) + 1) ≤ 1 := by rw [div_le_one hM_pos]; linarith
        linarith) s
      have heq1 : 1 + (s : ℝ) * -(1 / (6 * (K : ℝ) + 1)) = 1 - (s : ℝ) / (6 * (K : ℝ) + 1) := by ring
      have heq2 : 1 + -(1 / (6 * (K : ℝ) + 1)) = 1 - 1 / (6 * (K : ℝ) + 1) := by ring
      rw [heq1, heq2] at this
      exact this
    have hprod_ge : (1 - 1 / (6 * (K : ℝ) + 1)) ^ s ≤ ∏ p ∈ P3, (1 - 1 / (p : ℝ)) := by
      calc (1 - 1 / (6 * (K : ℝ) + 1)) ^ s
        _ = ∏ _p ∈ P3, (1 - 1 / (6 * (K : ℝ) + 1)) := (Finset.prod_const _).symm
        _ ≤ ∏ p ∈ P3, (1 - 1 / (p : ℝ)) := by
              apply Finset.prod_le_prod
              · intro _ _; rw [sub_nonneg, div_le_one hM_pos]; linarith
              · intro p hp
                simp only [P3, Finset.mem_filter] at hp
                have hpg : 6 * (K : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hp.2.le
                gcongr
    linarith
  -- Combine all three parts and cube!
  rw [totient_div_eq_prod_real hn_pos, hP_part, mul_pow, mul_pow]
  have h13 : (0.1387 : ℝ) ^ 3 * (0.965 : ℝ) ^ 3 * 49 ≥ 0.117 := by norm_num
  have h1p : (0.1387 : ℝ) ^ 3 ≤ (∏ p ∈ P1, (1 - 1 / (p : ℝ))) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hP1_ge 3
  have h3p : (0.965 : ℝ) ^ 3 ≤ (∏ p ∈ P3, (1 - 1 / (p : ℝ))) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hP3_ge 3
  have hden_le : 6 * (K : ℝ) + 1 ≤ 6 * Real.log (n : ℝ) + 7 := by linarith
  have h2p : (49 : ℝ) / (6 * Real.log (n : ℝ) + 7) ≤ (∏ p ∈ P2, (1 - 1 / (p : ℝ))) ^ 3 := by
    calc (49 : ℝ) / (6 * Real.log (n : ℝ) + 7)
      _ ≤ (49 : ℝ) / (6 * (K : ℝ) + 1) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hden_le
      _ ≤ _ := hP2_cube
  have hprod_mul : (0.1387 : ℝ) ^ 3 * ((49 : ℝ) / (6 * Real.log (n : ℝ) + 7)) * (0.965 : ℝ) ^ 3 ≤
      (∏ p ∈ P1, (1 - 1 / (p : ℝ))) ^ 3 * (∏ p ∈ P2, (1 - 1 / (p : ℝ))) ^ 3 *
      (∏ p ∈ P3, (1 - 1 / (p : ℝ))) ^ 3 := by
    have h12 := mul_le_mul h1p h2p (by positivity) (by positivity)
    exact mul_le_mul h12 h3p (by positivity) (by positivity)
  have hlhs_le : (0.117 : ℝ) / (6 * Real.log (n : ℝ) + 7) ≤
      (0.1387 : ℝ) ^ 3 * ((49 : ℝ) / (6 * Real.log (n : ℝ) + 7)) * (0.965 : ℝ) ^ 3 := by
    have heq : (0.1387 : ℝ) ^ 3 * ((49 : ℝ) / (6 * Real.log (n : ℝ) + 7)) * (0.965 : ℝ) ^ 3 =
        ((0.1387 : ℝ) ^ 3 * (0.965 : ℝ) ^ 3 * 49) / (6 * Real.log (n : ℝ) + 7) := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right h13 (by positivity)
  linarith

private lemma phi_gt_two_pi_ge_1M {n : ℕ} (hn : 1000000 ≤ n) :
    2 * Nat.primeCounting n < n.totient := by
  have hn_pos : 0 < n := by omega
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpi := pi_le_explicit (x := (n : ℝ)) (by linarith)
  rw [Nat.floor_natCast] at hpi
  have hlog_ge_1M : (13.8155 : ℝ) ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (by positivity) hnR
    rw [show (1000000 : ℝ) = 10 ^ (6 : ℕ) by norm_num, Real.log_pow, Real.log_ten_eq] at h
    push_cast at h
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  -- Helper for the 5 primorial ranges:
  have hrange_kill : ∀ (L0 r_lb c_err : ℝ),
      13.8 ≤ L0 → L0 ≤ Real.log (n : ℝ) →
      1900 + 14 * Real.log (n : ℝ) ≤ c_err * (n : ℝ) →
      r_lb * (n : ℝ) ≤ (n.totient : ℝ) →
      2 * (1.1056 / L0 + 1.1056 * (11 / 9) / L0 ^ 2 + c_err) < r_lb →
      2 * Nat.primeCounting n < n.totient := by
    intro L0 r_lb c_err hL0 hL hcerr hphi hgap
    have hL_pos : 0 < Real.log (n : ℝ) := by linarith
    have hL0_pos : 0 < L0 := by linarith
    have h1 : 1.1056 * (n : ℝ) / Real.log (n : ℝ) ≤ (1.1056 / L0) * (n : ℝ) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) hL0_pos hL
    have h2 : 1.1056 * (11 / 9) * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤
        (1.1056 * (11 / 9) / L0 ^ 2) * (n : ℝ) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    have hpi_le : (Nat.primeCounting n : ℝ) ≤
        (1.1056 / L0 + 1.1056 * (11 / 9) / L0 ^ 2 + c_err) * (n : ℝ) := by linarith
    have hlt_real : (2 * (Nat.primeCounting n : ℝ)) < (n.totient : ℝ) := by nlinarith
    exact_mod_cast hlt_real
  -- Helper: bound 1900 + 14 * log n linearly from n >= N0
  have hlin_err : ∀ (N0 L_ub : ℝ), 1000000 ≤ N0 → N0 ≤ (n : ℝ) → Real.log N0 ≤ L_ub →
      1900 + 14 * Real.log (n : ℝ) ≤ ((1900 + 14 * L_ub) / N0 + 14 / N0) * (n : ℝ) := by
    intro N0 L_ub hN0 hle hLub
    have hN0_pos : 0 < N0 := by linarith
    have hlog := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) / N0 by positivity)
    rw [Real.log_div (by positivity) hN0_pos.ne'] at hlog
    have hlog_n : Real.log (n : ℝ) ≤ L_ub + (n : ℝ) / N0 := by linarith
    have h1 : 1900 + 14 * L_ub ≤ ((1900 + 14 * L_ub) / N0) * (n : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hN0_pos]
      have hnn : 0 ≤ 1900 + 14 * L_ub := by
        have : 0 ≤ Real.log N0 := Real.log_nonneg (by linarith)
        linarith
      nlinarith
    have h2 : 14 * ((n : ℝ) / N0) = (14 / N0) * (n : ℝ) := by ring
    linarith
  -- Split into 6 ranges
  by_cases h8 : n < 9699690
  · -- [10^6, P_8): good = {2,3,5,7,11,13,17}, next = 19
    have hcov : ∀ p ∈ Finset.range 19, p.Prime → p ∈ ({2,3,5,7,11,13,17} : Finset ℕ) := by decide
    have hP : ∏ p ∈ ({2,3,5,7,11,13,17} : Finset ℕ), p = 510510 := by decide
    have hPm : ∏ p ∈ ({2,3,5,7,11,13,17} : Finset ℕ), (p - 1) = 92160 := by decide
    have hphi := totient_lower_avoid (bad := ∅) (good := {2,3,5,7,11,13,17}) (next := 19)
      hn_pos (by omega) (by decide) (by decide)
      (fun p hp hlt _ => hcov p (Finset.mem_range.mpr hlt) hp) (by simp) (by rw [hP]; omega)
    rw [hP, hPm] at hphi
    have hphiR : (92160 : ℝ) * (n : ℝ) ≤ (510510 : ℝ) * (n.totient : ℝ) := by exact_mod_cast hphi
    have hphi' : (0.18052 : ℝ) * (n : ℝ) ≤ (n.totient : ℝ) := by linarith
    have herr : 1900 + 14 * Real.log (n : ℝ) ≤ 0.00212 * (n : ℝ) := by
      have hL : Real.log 1000000 ≤ 13.82 := by
        rw [show (1000000 : ℝ) = 10 ^ (6 : ℕ) by norm_num, Real.log_pow, Real.log_ten_eq]
        push_cast; linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
      have := hlin_err 1000000 13.82 le_rfl hnR hL
      have hconst : ((1900 + 14 * 13.82) / 1000000 + 14 / 1000000) * (n : ℝ) ≤ (0.00212 : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith
    exact hrange_kill 13.8155 0.18052 0.00212 (by norm_num) hlog_ge_1M herr hphi' (by norm_num)
  push Not at h8
  by_cases h9 : n < 223092870
  · -- [P_8, P_9): good = {2..19}, next = 23
    have hcov : ∀ p ∈ Finset.range 23, p.Prime → p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ) := by decide
    have hP : ∏ p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ), p = 9699690 := by decide
    have hPm : ∏ p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ), (p - 1) = 1658880 := by decide
    have hphi := totient_lower_avoid (bad := ∅) (good := {2,3,5,7,11,13,17,19}) (next := 23)
      hn_pos (by omega) (by decide) (by decide)
      (fun p hp hlt _ => hcov p (Finset.mem_range.mpr hlt) hp) (by simp) (by rw [hP]; omega)
    rw [hP, hPm] at hphi
    have hphiR : (1658880 : ℝ) * (n : ℝ) ≤ (9699690 : ℝ) * (n.totient : ℝ) := by exact_mod_cast hphi
    have hphi' : (0.17102 : ℝ) * (n : ℝ) ≤ (n.totient : ℝ) := by linarith
    have hlog9 : (16.01 : ℝ) ≤ Real.log (n : ℝ) := by
      have hle : (9 * 10 ^ 6 : ℝ) ≤ (n : ℝ) := by
        have : (9699690 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h8
        linarith
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by norm_num) (by positivity),
          show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow, Real.log_pow, Real.log_ten_eq] at h
      push_cast at h
      linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
    have herr : 1900 + 14 * Real.log (n : ℝ) ≤ 0.00025 * (n : ℝ) := by
      have hL : Real.log 9000000 ≤ 16.02 := by
        rw [show (9000000 : ℝ) = 3 ^ (2 : ℕ) * 10 ^ (6 : ℕ) by norm_num,
            Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_ten_eq]
        push_cast; linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]
      have hn9 : (9000000 : ℝ) ≤ (n : ℝ) := by
        have : (9699690 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h8
        linarith
      have := hlin_err 9000000 16.02 (by norm_num) hn9 hL
      have hconst : ((1900 + 14 * 16.02) / 9000000 + 14 / 9000000) * (n : ℝ) ≤ (0.00025 : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith
    exact hrange_kill 16.01 0.17102 0.00025 (by norm_num) hlog9 herr hphi' (by norm_num)
  push Not at h9
  by_cases h10 : n < 6469693230
  · -- [P_9, P_10): good = {2..23}, next = 29
    have hcov : ∀ p ∈ Finset.range 29, p.Prime → p ∈ ({2,3,5,7,11,13,17,19,23} : Finset ℕ) := by decide
    have hP : ∏ p ∈ ({2,3,5,7,11,13,17,19,23} : Finset ℕ), p = 223092870 := by decide
    have hPm : ∏ p ∈ ({2,3,5,7,11,13,17,19,23} : Finset ℕ), (p - 1) = 36495360 := by decide
    have hphi := totient_lower_avoid (bad := ∅) (good := {2,3,5,7,11,13,17,19,23}) (next := 29)
      hn_pos (by omega) (by decide) (by decide)
      (fun p hp hlt _ => hcov p (Finset.mem_range.mpr hlt) hp) (by simp) (by rw [hP]; omega)
    rw [hP, hPm] at hphi
    have hphiR : (36495360 : ℝ) * (n : ℝ) ≤ (223092870 : ℝ) * (n.totient : ℝ) := by exact_mod_cast hphi
    have hphi' : (0.16358 : ℝ) * (n : ℝ) ≤ (n.totient : ℝ) := by linarith
    have hlog10 : (19.1 : ℝ) ≤ Real.log (n : ℝ) := by
      have hle : (2 * 10 ^ 8 : ℝ) ≤ (n : ℝ) := by
        have : (223092870 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h9
        linarith
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_ten_eq] at h
      push_cast at h
      linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    have herr : 1900 + 14 * Real.log (n : ℝ) ≤ 0.00002 * (n : ℝ) := by
      have hL : Real.log 200000000 ≤ 19.2 := by
        rw [show (200000000 : ℝ) = 2 * 10 ^ (8 : ℕ) by norm_num,
            Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_ten_eq]
        push_cast; linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
      have hn10 : (200000000 : ℝ) ≤ (n : ℝ) := by
        have : (223092870 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h9
        linarith
      have := hlin_err 200000000 19.2 (by norm_num) hn10 hL
      have hconst : ((1900 + 14 * 19.2) / 200000000 + 14 / 200000000) * (n : ℝ) ≤ (0.00002 : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith
    exact hrange_kill 19.1 0.16358 0.00002 (by norm_num) hlog10 herr hphi' (by norm_num)
  push Not at h10
  by_cases h11 : n < 200560490130
  · -- [P_10, P_11): good = {2..29}, next = 31
    have hcov : ∀ p ∈ Finset.range 31, p.Prime → p ∈ ({2,3,5,7,11,13,17,19,23,29} : Finset ℕ) := by decide
    have hP : ∏ p ∈ ({2,3,5,7,11,13,17,19,23,29} : Finset ℕ), p = 6469693230 := by decide
    have hPm : ∏ p ∈ ({2,3,5,7,11,13,17,19,23,29} : Finset ℕ), (p - 1) = 1021870080 := by decide
    have hphi := totient_lower_avoid (bad := ∅) (good := {2,3,5,7,11,13,17,19,23,29}) (next := 31)
      hn_pos (by omega) (by decide) (by decide)
      (fun p hp hlt _ => hcov p (Finset.mem_range.mpr hlt) hp) (by simp) (by rw [hP]; omega)
    rw [hP, hPm] at hphi
    have hphiR : (1021870080 : ℝ) * (n : ℝ) ≤ (6469693230 : ℝ) * (n.totient : ℝ) := by exact_mod_cast hphi
    have hphi' : (0.15794 : ℝ) * (n : ℝ) ≤ (n.totient : ℝ) := by linarith
    have hlog11 : (22.5 : ℝ) ≤ Real.log (n : ℝ) := by
      have hle : (6 * 10 ^ 9 : ℝ) ≤ (n : ℝ) := by
        have : (6469693230 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h10
        linarith
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by norm_num) (by positivity),
          show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
          Real.log_pow, Real.log_ten_eq] at h
      push_cast at h
      linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
    have herr : 1900 + 14 * Real.log (n : ℝ) ≤ 0.00001 * (n : ℝ) := by
      have hL : Real.log 6000000000 ≤ 22.6 := by
        rw [show (6000000000 : ℝ) = 2 * 3 * 10 ^ (9 : ℕ) by norm_num,
            Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_ten_eq]
        push_cast; linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]
      have hn11 : (6000000000 : ℝ) ≤ (n : ℝ) := by
        have : (6469693230 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h10
        linarith
      have := hlin_err 6000000000 22.6 (by norm_num) hn11 hL
      have hconst : ((1900 + 14 * 22.6) / 6000000000 + 14 / 6000000000) * (n : ℝ) ≤ (0.00001 : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith
    exact hrange_kill 22.5 0.15794 0.00001 (by norm_num) hlog11 herr hphi' (by norm_num)
  push Not at h11
  by_cases h12 : n < 7420738134810
  · -- [P_11, P_12): good = {2..31}, next = 37
    have hcov : ∀ p ∈ Finset.range 37, p.Prime → p ∈ ({2,3,5,7,11,13,17,19,23,29,31} : Finset ℕ) := by decide
    have hP : ∏ p ∈ ({2,3,5,7,11,13,17,19,23,29,31} : Finset ℕ), p = 200560490130 := by decide
    have hPm : ∏ p ∈ ({2,3,5,7,11,13,17,19,23,29,31} : Finset ℕ), (p - 1) = 30656102400 := by decide
    have hphi := totient_lower_avoid (bad := ∅) (good := {2,3,5,7,11,13,17,19,23,29,31}) (next := 37)
      hn_pos (by omega) (by decide) (by decide)
      (fun p hp hlt _ => hcov p (Finset.mem_range.mpr hlt) hp) (by simp) (by rw [hP]; omega)
    rw [hP, hPm] at hphi
    have hphiR : (30656102400 : ℝ) * (n : ℝ) ≤ (200560490130 : ℝ) * (n.totient : ℝ) := by exact_mod_cast hphi
    have hphi' : (0.15284 : ℝ) * (n : ℝ) ≤ (n.totient : ℝ) := by linarith
    have hlog12 : (26.0 : ℝ) ≤ Real.log (n : ℝ) := by
      have hle : (2 * 10 ^ 11 : ℝ) ≤ (n : ℝ) := by
        have : (200560490130 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h11
        linarith
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_ten_eq] at h
      push_cast at h
      linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    have herr : 1900 + 14 * Real.log (n : ℝ) ≤ 0.00001 * (n : ℝ) := by
      have hL : Real.log 200000000000 ≤ 26.1 := by
        rw [show (200000000000 : ℝ) = 2 * 10 ^ (11 : ℕ) by norm_num,
            Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_ten_eq]
        push_cast; linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
      have hn12 : (200000000000 : ℝ) ≤ (n : ℝ) := by
        have : (200560490130 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h11
        linarith
      have := hlin_err 200000000000 26.1 (by norm_num) hn12 hL
      have hconst : ((1900 + 14 * 26.1) / 200000000000 + 14 / 200000000000) * (n : ℝ) ≤ (0.00001 : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith
    exact hrange_kill 26.0 0.15284 0.00001 (by norm_num) hlog12 herr hphi' (by norm_num)
  push Not at h12
  -- [P_12, ∞): use mod-6 cube bound!
  have hphi_cube := totient_cube_ge_large h12
  have hlog13 : (29.24 : ℝ) ≤ Real.log (n : ℝ) := by
    have hle : (5 * 10 ^ 12 : ℝ) ≤ (n : ℝ) := by
      have : (7420738134810 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h12
      linarith
    have h := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_ten_eq] at h
    push_cast at h
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  set L := Real.log (n : ℝ)
  have hL_pos : 0 < L := by linarith
  -- Bound 1900 + 14 * L <= 0.02 * n / L using n = exp L >= L^7 / 5040
  have hexp7 : L ^ 7 / (7 : ℕ).factorial ≤ (n : ℝ) := by
    have h := Real.pow_div_factorial_le_exp L hL_pos.le 7
    rwa [Real.exp_log (by positivity : (0 : ℝ) < n)] at h
  have h5040 : L ^ 7 ≤ 5040 * (n : ℝ) := by
    have : ((7 : ℕ).factorial : ℝ) = 5040 := by norm_num
    rw [this, div_le_iff₀ (by norm_num)] at hexp7
    linarith
  have herr_large : 1900 + 14 * L ≤ 0.02 * (n : ℝ) / L := by
    rw [le_div_iff₀ hL_pos]
    have hL2 : (29.24 : ℝ) ^ 2 ≤ L ^ 2 := by
      have := mul_le_mul hlog13 hlog13 (by norm_num) hL_pos.le; linarith
    have hL5 : (29.24 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) hlog13 5
    have hL7 : L ^ 5 * L ^ 2 = L ^ 7 := by ring
    have h1 : (1900 + 14 * L) * L ≤ 80 * L ^ 2 := by
      have : 1900 * L ≤ 66 * L ^ 2 := by
        have := mul_le_mul_of_nonneg_right hlog13 hL_pos.le; linarith
      linarith
    have h2 : (80 * 5040 : ℝ) * L ^ 2 ≤ (0.02 * (29.24 : ℝ) ^ 5) * L ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg L)
    have h3 : (29.24 : ℝ) ^ 5 * L ^ 2 ≤ L ^ 5 * L ^ 2 :=
      mul_le_mul_of_nonneg_right hL5 (sq_nonneg L)
    linarith
  have hpi_ratio : 2 * (Nat.primeCounting n : ℝ) / (n : ℝ) ≤ 2.35 / L := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1.1056 * (11 / 9) * (n : ℝ) / L ^ 2 ≤ (1.1056 * (11 / 9) / 29.24) * ((n : ℝ) / L) := by
      have heq : (1.1056 * (11 / 9) / 29.24) * ((n : ℝ) / L) =
          1.1056 * (11 / 9) * (n : ℝ) / (29.24 * L) := by ring
      rw [heq]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by
        have := mul_le_mul_of_nonneg_right hlog13 hL_pos.le; linarith)
    have h2 : 1.1056 * (n : ℝ) / L = 1.1056 * ((n : ℝ) / L) := by ring
    have h3 : 0.02 * (n : ℝ) / L = 0.02 * ((n : ℝ) / L) := by ring
    have h4 : (2.35 / L) * (n : ℝ) = 2.35 * ((n : ℝ) / L) := by ring
    have hconst : 2 * (1.1056 + 1.1056 * (11 / 9) / 29.24 + 0.02) * ((n : ℝ) / L) ≤
        2.35 * ((n : ℝ) / L) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have hcube_lt : (2.35 / L) ^ 3 < (0.117 : ℝ) / (6 * L + 7) := by
    rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hL2 : (29.24 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hlog13 2
    have hL3 : (29.24 : ℝ) ^ 2 * L ≤ L ^ 3 := by
      have := mul_le_mul_of_nonneg_right hL2 hL_pos.le; linarith
    have hnum : (2.35 : ℝ) ^ 3 * (6 * L + 7) < 0.117 * ((29.24 : ℝ) ^ 2 * L) := by linarith
    linarith
  have hlt_cube : (2 * (Nat.primeCounting n : ℝ) / (n : ℝ)) ^ 3 < ((n.totient : ℝ) / (n : ℝ)) ^ 3 := by
    calc (2 * (Nat.primeCounting n : ℝ) / (n : ℝ)) ^ 3
      _ ≤ (2.35 / L) ^ 3 := pow_le_pow_left₀ (by positivity) hpi_ratio 3
      _ < (0.117 : ℝ) / (6 * L + 7) := hcube_lt
      _ ≤ ((n.totient : ℝ) / (n : ℝ)) ^ 3 := hphi_cube
  have hlt_ratio : 2 * (Nat.primeCounting n : ℝ) / (n : ℝ) < (n.totient : ℝ) / (n : ℝ) := by
    by_contra hge
    push Not at hge
    have := pow_le_pow_left₀ (by positivity) hge 3
    linarith
  have hlt_real : 2 * (Nat.primeCounting n : ℝ) < (n.totient : ℝ) := by
    rwa [div_lt_div_iff_of_pos_right (by positivity)] at hlt_ratio
  exact_mod_cast hlt_real

end Analytic

section Sieve
open Finset

private def pow2Fuel : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | f + 1, n, base, acc =>
    if n = 0 then acc
    else if n % 2 = 1 then pow2Fuel f (n / 2) (base * base) (acc * base)
    else pow2Fuel f (n / 2) (base * base) acc

private def fastPow2 (n : Nat) : Nat := pow2Fuel 25 n 2 1

private lemma pow2Fuel_eq : ∀ f n b a, n < 2 ^ f → pow2Fuel f n b a = a * b ^ n
  | 0, n, b, a, hn => by
    have h0 : n = 0 := by omega
    subst h0; simp [pow2Fuel]
  | f + 1, n, b, a, hn => by
    unfold pow2Fuel
    split_ifs with h0 h1
    · subst h0; simp
    · have hlt : n / 2 < 2 ^ f := by
        have : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
        omega
      rw [pow2Fuel_eq f (n / 2) (b * b) (a * b) hlt]
      have hn_eq : n = 2 * (n / 2) + 1 := by omega
      conv_rhs => rw [hn_eq]
      rw [pow_succ, pow_mul]
      ring
    · have hlt : n / 2 < 2 ^ f := by
        have : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
        omega
      rw [pow2Fuel_eq f (n / 2) (b * b) a hlt]
      have hn_eq : n = 2 * (n / 2) := by omega
      conv_rhs => rw [hn_eq]
      rw [pow_mul]
      ring

private lemma fastPow2_eq {n : ℕ} (hn : n < 2 ^ 25) : fastPow2 n = 2 ^ n := by
  rw [fastPow2, pow2Fuel_eq 25 n 2 1 hn, one_mul]

/-! ## Base-B digit extraction and bit testing -/

private lemma sum_pow_lt {B : ℕ} (hB : 2 ≤ B) : ∀ (r : ℕ) (c : ℕ → ℕ),
    (∀ j < r, c j < B) → ∑ j ∈ Finset.range r, c j * B ^ j < B ^ r
  | 0, _, _ => by simp
  | r + 1, c, hc => by
    rw [Finset.sum_range_succ]
    have ih := sum_pow_lt hB r c (fun j hj => hc j (by omega))
    have hcr : c r + 1 ≤ B := hc r (by omega)
    calc (∑ j ∈ Finset.range r, c j * B ^ j) + c r * B ^ r
      _ < B ^ r + c r * B ^ r := Nat.add_lt_add_right ih _
      _ = (c r + 1) * B ^ r := by ring
      _ ≤ B * B ^ r := Nat.mul_le_mul_right _ hcr
      _ = B ^ (r + 1) := by ring

private lemma digit_extract {B : ℕ} (hB : 2 ≤ B) (r : ℕ) (c : ℕ → ℕ)
    (hc : ∀ j < r, c j < B) (j : ℕ) (hj : j < r) :
    (∑ i ∈ Finset.range r, c i * B ^ i) / B ^ j % B = c j := by
  have hsplit : ∑ i ∈ Finset.range r, c i * B ^ i =
      (∑ i ∈ Finset.range j, c i * B ^ i) +
      c j * B ^ j +
      (∑ i ∈ Finset.range (r - j - 1), c (j + 1 + i) * B ^ i) * B ^ (j + 1) := by
    have hr1 : r = j + (r - j) := by omega
    have hr2 : r - j = 1 + (r - j - 1) := by omega
    conv_lhs => rw [hr1, Finset.sum_range_add, hr2, Finset.sum_range_add]
    simp only [Finset.sum_range_one, add_zero]
    rw [← add_assoc]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have : j + (1 + i) = j + 1 + i := by omega
    rw [this, pow_add]
    ring
  rw [hsplit]
  have hlt : ∑ i ∈ Finset.range j, c i * B ^ i < B ^ j :=
    sum_pow_lt hB j c (fun i hi => hc i (by omega))
  have hBj_pos : 0 < B ^ j := pow_pos (by omega) j
  have hrew : (∑ i ∈ Finset.range j, c i * B ^ i) + c j * B ^ j +
      (∑ i ∈ Finset.range (r - j - 1), c (j + 1 + i) * B ^ i) * B ^ (j + 1) =
      (∑ i ∈ Finset.range j, c i * B ^ i) +
      (c j + (∑ i ∈ Finset.range (r - j - 1), c (j + 1 + i) * B ^ i) * B) * B ^ j := by
    rw [pow_succ]; ring
  rw [hrew, Nat.add_mul_div_right _ _ hBj_pos, Nat.div_eq_of_lt hlt, zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hc j hj)]

private lemma geom_sum_base {B : ℕ} (hB : 2 ≤ B) : ∀ r : ℕ,
    (∑ j ∈ Finset.range r, (B - 1) * B ^ j) = B ^ r - 1
  | 0 => by simp
  | r + 1 => by
    rw [Finset.sum_range_succ, geom_sum_base hB r]
    have h1 : 1 ≤ B ^ r := Nat.one_le_pow r B (by omega)
    have h3 : 1 ≤ B ^ (r + 1) := Nat.one_le_pow (r + 1) B (by omega)
    zify [h1, show 1 ≤ B by omega, h3]
    rw [pow_succ]; ring

private lemma geom_sum_pow2 (p : ℕ) (hp : 1 ≤ p) : ∀ r : ℕ,
    (∑ k ∈ Finset.range r, 2 ^ (k * p)) * (2 ^ p - 1) = 2 ^ (p * r) - 1
  | 0 => by simp
  | r + 1 => by
    rw [Finset.sum_range_succ, add_mul, geom_sum_pow2 p hp r]
    have h1 : 1 ≤ 2 ^ (p * r) := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ 2 ^ (p * (r + 1)) := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2, h3]
    rw [show p * (r + 1) = p * r + p by ring, pow_add, mul_comm r p]; ring

/-! ## Sieve bitmask specification -/

private def multMask (N p : Nat) : Nat :=
  let m := N / p
  let bp := fastPow2 p
  (fastPow2 (p * (m + 1)) - 1) / (bp - 1) - 1 - bp

private lemma multMask_eq_sum {N p : ℕ} (hp : 2 ≤ p) (hbound : p * (N / p + 1) < 2 ^ 25) :
    multMask N p = ∑ k ∈ Finset.Ico 2 (N / p + 1), 2 ^ (k * p) := by
  unfold multMask
  dsimp only
  have hp_lt : p < 2 ^ 25 := by
    have : 1 ≤ N / p + 1 := Nat.succ_pos _
    nlinarith
  rw [fastPow2_eq hbound, fastPow2_eq hp_lt]
  have hden_pos : 0 < 2 ^ p - 1 := by
    have : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hp
    omega
  have hgeom := geom_sum_pow2 p (by omega) (N / p + 1)
  have hdiv : (2 ^ (p * (N / p + 1)) - 1) / (2 ^ p - 1) =
      ∑ k ∈ Finset.range (N / p + 1), 2 ^ (k * p) := by
    rw [← hgeom, Nat.mul_div_cancel _ hden_pos]
  rw [hdiv]
  rcases Nat.eq_zero_or_pos (N / p) with h0 | hpos
  · rw [h0]; simp
  · rcases Nat.eq_or_lt_of_le hpos with h1 | h2
    · rw [← h1]; simp [Finset.sum_range_succ]
    · have hsplit : Finset.range (N / p + 1) = Finset.range 2 ∪ Finset.Ico 2 (N / p + 1) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range 2) (Finset.Ico 2 (N / p + 1)) := by
        rw [Finset.disjoint_left]; intro x h1 h2
        simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
      rw [hsplit, Finset.sum_union hdisj]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, zero_mul, pow_zero, one_mul]
      omega

private lemma multMask_testBit {N p n : ℕ} (hp : 2 ≤ p) (hbound : p * (N / p + 1) < 2 ^ 25) :
    (multMask N p).testBit n = true ↔ ∃ k, 2 ≤ k ∧ k ≤ N / p ∧ n = k * p := by
  rw [multMask_eq_sum hp hbound]
  let r := N / p + 1
  let c : ℕ → ℕ := fun j => if 2 ≤ j ∧ j < r then 1 else 0
  have hsum_eq : ∑ k ∈ Finset.Ico 2 r, 2 ^ (k * p) =
      ∑ j ∈ Finset.range (max r (n / p + 1)), c j * (2 ^ p) ^ j := by
    have hsub : Finset.Ico 2 r ⊆ Finset.range (max r (n / p + 1)) := by
      intro x hx; simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢; omega
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [c, hj.1, hj.2, and_self, ↓reduceIte, one_mul, ← pow_mul, mul_comm p j]
    · intro j _ hjn
      simp only [Finset.mem_Ico] at hjn
      simp only [c, hjn, ↓reduceIte, zero_mul]
  rw [hsum_eq]
  have hBp : 2 ≤ 2 ^ p := by
    have : 2 ^ 1 ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hc : ∀ j < max r (n / p + 1), c j < 2 ^ p := by
    intro j _; dsimp [c]; split_ifs <;> omega
  have hdig := digit_extract hBp (max r (n / p + 1)) c hc (n / p) (by omega)
  -- Express testBit n via chunk n / p and offset n % p
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hn_div : n = (n / p) * p + n % p := (Nat.div_add_mod' n p).symm
  have hmod_lt : n % p < p := Nat.mod_lt n (by omega)
  have hpow_split : 2 ^ n = (2 ^ p) ^ (n / p) * 2 ^ (n % p) := by
    conv_lhs => rw [hn_div]
    rw [pow_add, ← pow_mul, mul_comm p (n / p)]
  rw [hpow_split, ← Nat.div_div_eq_div_mul]
  set Q := (∑ j ∈ Finset.range (max r (n / p + 1)), c j * (2 ^ p) ^ j) / (2 ^ p) ^ (n / p)
  have hQ_mod : Q % 2 ^ p = c (n / p) := hdig
  have hQ_split : Q = (Q / 2 ^ p) * 2 ^ p + c (n / p) := by
    rw [← hQ_mod, mul_comm]; exact (Nat.div_add_mod Q (2 ^ p)).symm
  have hdiv2 : Q / 2 ^ (n % p) = (Q / 2 ^ p) * 2 ^ (p - n % p) + c (n / p) / 2 ^ (n % p) := by
    conv_lhs => rw [hQ_split]
    have h2p : 2 ^ p = 2 ^ (p - n % p) * 2 ^ (n % p) := by
      rw [← pow_add]; congr 1; omega
    have hrew : (Q / 2 ^ p) * 2 ^ p + c (n / p) =
        2 ^ (n % p) * ((Q / 2 ^ p) * 2 ^ (p - n % p)) + c (n / p) := by
      rw [h2p]; ring
    rw [hrew, Nat.mul_add_div (pow_pos (by omega) _)]
  rw [hdiv2]
  have h2even : 2 ∣ 2 ^ (p - n % p) := dvd_pow_self 2 (by omega)
  have hmod2 : ((Q / 2 ^ p) * 2 ^ (p - n % p) + c (n / p) / 2 ^ (n % p)) % 2 =
      (c (n / p) / 2 ^ (n % p)) % 2 := by
    obtain ⟨t, ht⟩ := h2even
    rw [ht, show (Q / 2 ^ p) * (2 * t) = 2 * ((Q / 2 ^ p) * t) by ring, Nat.mul_add_mod]
  rw [hmod2]
  simp only [decide_eq_true_eq]
  constructor
  · intro h1
    by_cases hrem : n % p = 0
    · rw [hrem, pow_zero, Nat.div_one] at h1
      dsimp [c] at h1
      split_ifs at h1 with hc_cond
      · exact ⟨n / p, hc_cond.1, by omega, by omega⟩
    · have hge2 : 2 ≤ 2 ^ (n % p) := by
        have : 2 ^ 1 ≤ 2 ^ (n % p) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hcle : c (n / p) ≤ 1 := by dsimp [c]; split_ifs <;> omega
      have hdz : c (n / p) / 2 ^ (n % p) = 0 := Nat.div_eq_of_lt (by omega)
      omega
  · rintro ⟨k, hk2, hkle, rfl⟩
    have hdiv_k : k * p / p = k := Nat.mul_div_cancel k (by omega)
    have hmod_k : k * p % p = 0 := Nat.mul_mod_left k p
    rw [hdiv_k, hmod_k, pow_zero, Nat.div_one]
    dsimp [c]
    have : 2 ≤ k ∧ k < r := ⟨hk2, by omega⟩
    simp [this]

private def buildCompMask (N : Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | p :: ps, acc => buildCompMask N ps (acc ||| multMask N p)

private lemma buildCompMask_testBit (N : ℕ) : ∀ (ps : List ℕ) (acc n : ℕ),
    (buildCompMask N ps acc).testBit n =
      (acc.testBit n || ps.any (fun p => (multMask N p).testBit n))
  | [], acc, n => by simp [buildCompMask]
  | p :: ps, acc, n => by
    simp only [buildCompMask, buildCompMask_testBit, Nat.testBit_or, List.any_cons, Bool.or_assoc]

private def primeMaskWith (N : Nat) (ps : List Nat) : Nat :=
  let full := fastPow2 (N + 1) - 4
  let comp := buildCompMask N ps 0
  full &&& (full ^^^ comp)

private lemma full_testBit {N n : ℕ} (hN : 2 ≤ N) (hN25 : N + 1 < 2 ^ 25) :
    (fastPow2 (N + 1) - 4).testBit n = decide (2 ≤ n ∧ n ≤ N) := by
  rw [fastPow2_eq hN25]
  have hsum : 2 ^ (N + 1) - 4 = ∑ j ∈ Finset.range (max (N + 1) (n + 1)),
      (if 2 ≤ j ∧ j ≤ N then 1 else 0) * 2 ^ j := by
    have hsub : Finset.Ico 2 (N + 1) ⊆ Finset.range (max (N + 1) (n + 1)) := by
      intro x hx; simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢; omega
    have h1 : ∑ j ∈ Finset.range (max (N + 1) (n + 1)),
        (if 2 ≤ j ∧ j ≤ N then 1 else 0) * 2 ^ j =
        ∑ j ∈ Finset.Ico 2 (N + 1), 2 ^ j := by
      rw [← Finset.sum_subset hsub]
      · apply Finset.sum_congr rfl; intro j hj
        simp only [Finset.mem_Ico] at hj
        have : 2 ≤ j ∧ j ≤ N := by omega
        simp [this]
      · intro j _ hjn
        simp only [Finset.mem_Ico] at hjn
        have : ¬ (2 ≤ j ∧ j ≤ N) := by omega
        simp [this]
    rw [h1]
    have hgeom := geom_sum_base (B := 2) (by omega) (N + 1)
    simp only [Nat.reduceSub, one_mul] at hgeom
    have hsplit : Finset.range (N + 1) = Finset.range 2 ∪ Finset.Ico 2 (N + 1) := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range 2) (Finset.Ico 2 (N + 1)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
    rw [hsplit, Finset.sum_union hdisj] at hgeom
    simp [Finset.sum_range_succ] at hgeom
    omega
  rw [hsum, Nat.testBit_eq_decide_div_mod_eq]
  have hdig := digit_extract (B := 2) (by omega) (max (N + 1) (n + 1))
    (fun j => if 2 ≤ j ∧ j ≤ N then 1 else 0)
    (fun j _ => by split_ifs <;> omega) n (by omega)
  rw [hdig]
  split_ifs with h <;> simp [h]

private lemma primeMaskWith_testBit {N : ℕ} {ps : List ℕ}
    (hN : 2 ≤ N) (hN25 : N + 1 < 2 ^ 25)
    (hps_ge : ∀ p ∈ ps, 2 ≤ p ∧ p * (N / p + 1) < 2 ^ 25)
    (hps_cover : ∀ q : ℕ, q.Prime → q * q ≤ N → q ∈ ps)
    {n : ℕ} (hn : n ≤ N) :
    (primeMaskWith N ps).testBit n = true ↔ n.Prime := by
  unfold primeMaskWith
  rw [Nat.testBit_and, Nat.testBit_xor, full_testBit hN hN25, buildCompMask_testBit]
  simp only [Nat.zero_testBit, Bool.false_or]
  by_cases hn2 : 2 ≤ n
  · have hdec : decide (2 ≤ n ∧ n ≤ N) = true := decide_eq_true ⟨hn2, hn⟩
    rw [hdec]
    simp only [Bool.true_and, Bool.true_xor, Bool.not_eq_true', List.any_eq_false]
    constructor
    · intro hno
      by_contra hnp
      have hmf_p : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hmf_dvd : n.minFac ∣ n := Nat.minFac_dvd n
      have hmf_sq : n.minFac * n.minFac ≤ n := by
        simpa [sq] using Nat.minFac_sq_le_self (by omega) hnp
      have hmf_mem : n.minFac ∈ ps := hps_cover n.minFac hmf_p (hmf_sq.trans hn)
      have hmf_ge2 : 2 ≤ n.minFac := hmf_p.two_le
      have hmf_bnd := (hps_ge n.minFac hmf_mem).2
      have htb : (multMask N n.minFac).testBit n = true :=
        (multMask_testBit (n := n) hmf_ge2 hmf_bnd).mpr ⟨n / n.minFac, ?_, ?_, ?_⟩
      · have := hno n.minFac hmf_mem
        rw [htb] at this; exact this rfl
      · have : n.minFac * 2 ≤ n.minFac * n.minFac := Nat.mul_le_mul_left _ hmf_ge2
        have : n.minFac * 2 ≤ n := this.trans hmf_sq
        exact (Nat.le_div_iff_mul_le hmf_p.pos).mpr (by linarith)
      · exact Nat.div_le_div_right hn
      · exact (Nat.div_mul_cancel hmf_dvd).symm
    · intro hp q hq
      have hq_info := hps_ge q hq
      intro htb
      obtain ⟨k, hk2, _, hnk⟩ := (multMask_testBit hq_info.1 hq_info.2).mp htb
      have hqdvd : q ∣ n := ⟨k, by linarith⟩
      rcases hp.eq_one_or_self_of_dvd q hqdvd with h1 | hself
      · omega
      · nlinarith
  · have hdec : decide (2 ≤ n ∧ n ≤ N) = false := decide_eq_false (by omega)
    rw [hdec]
    simp only [Bool.false_and, Bool.false_eq_true, false_iff]
    intro hp
    have := hp.two_le
    omega

/-! ## SWAR popcount specification -/

private def swarStep (allOnes : Nat) (k : Nat) (x : Nat) : Nat :=
  let w := fastPow2 k
  let mask := allOnes / (fastPow2 w + 1)
  (x &&& mask) + ((x >>> w) &&& mask)

private def swarLoop (allOnes : Nat) : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | fuel + 1, k, x => swarLoop allOnes fuel (k + 1) (swarStep allOnes k x)

private def swarPopcount (d : Nat) (x : Nat) : Nat :=
  let allOnes := fastPow2 (fastPow2 d) - 1
  swarLoop allOnes d 0 x

private def bitCount (x lo len : ℕ) : ℕ :=
  #{i ∈ Finset.Ico lo (lo + len) | x.testBit i = true}

private lemma bitCount_le (x lo len : ℕ) : bitCount x lo len ≤ len := by
  calc bitCount x lo len ≤ (Finset.Ico lo (lo + len)).card := Finset.card_filter_le _ _
    _ = len := by rw [Nat.card_Ico]; omega

private lemma bitCount_add (x lo a b : ℕ) :
    bitCount x lo (a + b) = bitCount x lo a + bitCount x (lo + a) b := by
  unfold bitCount
  have hsplit : Finset.Ico lo (lo + (a + b)) = Finset.Ico lo (lo + a) ∪ Finset.Ico (lo + a) (lo + a + b) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ico lo (lo + a)) (Finset.Ico (lo + a) (lo + a + b)) := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Finset.mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj)]

private lemma swarMask_eq {d k : ℕ} (hk : k < d) (_hd : 2 ^ d < 2 ^ 25) :
    (2 ^ (2 ^ d) - 1) / (2 ^ (2 ^ k) + 1) =
      ∑ j ∈ Finset.range (2 ^ (d - k - 1)), (2 ^ (2 ^ k) - 1) * (2 ^ (2 ^ (k + 1))) ^ j := by
  set w := 2 ^ k
  set m := 2 ^ (d - k - 1)
  have h2w : 2 ^ (k + 1) = 2 * w := by dsimp [w]; ring
  have hdim : 2 * w * m = 2 ^ d := by
    dsimp [w, m]
    rw [← pow_succ', ← pow_add]
    congr 1; omega
  have hB : 2 ≤ 2 ^ (2 * w) := by
    have hw1 : 1 ≤ w := Nat.one_le_pow k 2 (by omega)
    have : 2 ^ 1 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hgeom := geom_sum_base hB m
  have hpow_m : (2 ^ (2 * w)) ^ m = 2 ^ (2 ^ d) := by
    rw [← pow_mul, hdim]
  rw [hpow_m] at hgeom
  have hmul : (∑ j ∈ Finset.range m, (2 ^ w - 1) * (2 ^ (2 * w)) ^ j) * (2 ^ w + 1) =
      2 ^ (2 ^ d) - 1 := by
    rw [Finset.sum_mul, ← hgeom]
    apply Finset.sum_congr rfl
    intro j _
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ 2 ^ (2 * w) := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    rw [show 2 * w = w + w by ring, pow_add]; ring
  have hden_pos : 0 < 2 ^ w + 1 := by positivity
  rw [h2w, ← hmul, Nat.mul_div_cancel _ hden_pos]

private lemma land_swarMask_eq {d k x : ℕ} (hk : k < d) (hd : 2 ^ d < 2 ^ 25) (hx : x < 2 ^ (2 ^ d)) :
    x &&& ((2 ^ (2 ^ d) - 1) / (2 ^ (2 ^ k) + 1)) =
      ∑ j ∈ Finset.range (2 ^ (d - k - 1)),
        ((x / 2 ^ (2 * j * 2 ^ k)) % 2 ^ (2 ^ k)) * (2 ^ (2 ^ (k + 1))) ^ j := by
  set w := 2 ^ k
  set m := 2 ^ (d - k - 1)
  have hw_pos : 1 ≤ w := Nat.one_le_pow k 2 (by omega)
  have h2w : 2 ^ (k + 1) = 2 * w := by dsimp [w]; ring
  have hdim : 2 * w * m = 2 ^ d := by
    dsimp [w, m]; rw [← pow_succ', ← pow_add]; congr 1; omega
  have hmask := swarMask_eq hk hd
  -- Prove equality by extensionality on testBit!
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, hmask]
  by_cases hi : i < 2 ^ d
  · set q := i / (2 * w)
    set r := i % (2 * w)
    have hq_lt : q < m := by
      have : i < m * (2 * w) := by linarith
      exact (Nat.div_lt_iff_lt_mul (by omega)).mpr this
    have hr_lt : r < 2 * w := Nat.mod_lt i (by omega)
    have hi_eq : i = q * (2 * w) + r := (Nat.div_add_mod' i (2 * w)).symm
    have hB : 2 ≤ 2 ^ (2 * w) := by
      have : 2 ^ 1 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    -- Helper: testBit i of ∑ j < m, f j * (2^(2w))^j = (f q).testBit r!
    have hsum_tb : ∀ (f : ℕ → ℕ), (∀ j < m, f j < 2 ^ (2 * w)) →
        (∑ j ∈ Finset.range m, f j * (2 ^ (2 * w)) ^ j).testBit i = (f q).testBit r := by
      intro f hf
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hpow_i : 2 ^ i = (2 ^ (2 * w)) ^ q * 2 ^ r := by
        conv_lhs => rw [hi_eq]
        rw [pow_add, ← pow_mul, mul_comm (2 * w) q]
      rw [hpow_i, ← Nat.div_div_eq_div_mul]
      set Q := (∑ j ∈ Finset.range m, f j * (2 ^ (2 * w)) ^ j) / (2 ^ (2 * w)) ^ q
      have hQ_mod : Q % 2 ^ (2 * w) = f q := digit_extract hB m f hf q hq_lt
      have hQ_split : Q = (Q / 2 ^ (2 * w)) * 2 ^ (2 * w) + f q := by
        rw [← hQ_mod, mul_comm]; exact (Nat.div_add_mod Q (2 ^ (2 * w))).symm
      have hdiv2 : Q / 2 ^ r = (Q / 2 ^ (2 * w)) * 2 ^ (2 * w - r) + f q / 2 ^ r := by
        conv_lhs => rw [hQ_split]
        have h2p : 2 ^ (2 * w) = 2 ^ (2 * w - r) * 2 ^ r := by rw [← pow_add]; congr 1; omega
        have hrew : (Q / 2 ^ (2 * w)) * 2 ^ (2 * w) + f q =
            2 ^ r * ((Q / 2 ^ (2 * w)) * 2 ^ (2 * w - r)) + f q := by rw [h2p]; ring
        rw [hrew, Nat.mul_add_div (pow_pos (by omega) _)]
      rw [hdiv2]
      obtain ⟨t, ht⟩ : 2 ∣ 2 ^ (2 * w - r) := dvd_pow_self 2 (by omega)
      rw [ht, show (Q / 2 ^ (2 * w)) * (2 * t) = 2 * ((Q / 2 ^ (2 * w)) * t) by ring, Nat.mul_add_mod]
    have hlt_pow : 2 ^ w < 2 ^ (2 * w) := Nat.pow_lt_pow_right (by omega) (by omega)
    rw [h2w]
    rw [hsum_tb (fun _ => 2 ^ w - 1) (fun _ _ => by omega)]
    rw [hsum_tb (fun j => (x / 2 ^ (2 * j * w)) % 2 ^ w) (fun j _ => (Nat.mod_lt _ (pow_pos (by omega) _)).trans hlt_pow)]
    -- Now compare LHS: x.testBit i && (2^w - 1).testBit r  vs  RHS: ((x / 2^(2*q*w)) % 2^w).testBit r
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hrw : r < w
    · simp only [hrw, decide_true, Bool.and_true, Nat.testBit_mod_two_pow, Bool.true_and,
                 Nat.testBit_div_two_pow]
      congr 1; rw [hi_eq]; ring
    · simp only [hrw, decide_false, Bool.and_false, Nat.testBit_mod_two_pow, Bool.false_and]
  · -- i >= 2^d: both sides are < 2^(2^d), so testBit i = false!
    have hge : 2 ^ d ≤ i := by omega
    have hlhs_lt : x &&& (∑ j ∈ Finset.range m, (2 ^ w - 1) * (2 ^ (2 ^ (k + 1))) ^ j) < 2 ^ (2 ^ d) := by
      have : x &&& (∑ j ∈ Finset.range m, (2 ^ w - 1) * (2 ^ (2 ^ (k + 1))) ^ j) ≤ x :=
        Nat.and_le_left
      omega
    have hlt_pow : 2 ^ w < 2 ^ (2 * w) := Nat.pow_lt_pow_right (by omega) (by omega)
    have hrhs_lt : ∑ j ∈ Finset.range m,
        ((x / 2 ^ (2 * j * w)) % 2 ^ w) * (2 ^ (2 ^ (k + 1))) ^ j < 2 ^ (2 ^ d) := by
      rw [h2w]
      have hB : 2 ≤ 2 ^ (2 * w) := by
        have : 2 ^ 1 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hs := sum_pow_lt hB m (fun j => (x / 2 ^ (2 * j * w)) % 2 ^ w)
        (fun j _ => (Nat.mod_lt _ (pow_pos (by omega) _)).trans hlt_pow)
      rwa [← pow_mul, hdim] at hs
    rw [← Nat.testBit_and]
    have h1 : (x &&& (∑ j ∈ Finset.range m, (2 ^ w - 1) * (2 ^ (2 ^ (k + 1))) ^ j)).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlhs_lt (Nat.pow_le_pow_right (by omega) hge))
    have h2 : (∑ j ∈ Finset.range m, ((x / 2 ^ (2 * j * w)) % 2 ^ w) * (2 ^ (2 ^ (k + 1))) ^ j).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hrhs_lt (Nat.pow_le_pow_right (by omega) hge))
    rw [h1, h2]



private lemma swarStep_spec {d k orig cur : ℕ} (hk : k < d) (hd : 2 ^ d < 2 ^ 25)
    (hcur_lt : cur < 2 ^ (2 ^ d))
    (hinv : ∀ j < 2 ^ (d - k), (cur / 2 ^ (j * 2 ^ k)) % 2 ^ (2 ^ k) = bitCount orig (j * 2 ^ k) (2 ^ k)) :
    let nxt := swarStep (2 ^ (2 ^ d) - 1) k cur
    nxt < 2 ^ (2 ^ d) ∧
    ∀ j < 2 ^ (d - (k + 1)),
      (nxt / 2 ^ (j * 2 ^ (k + 1))) % 2 ^ (2 ^ (k + 1)) = bitCount orig (j * 2 ^ (k + 1)) (2 ^ (k + 1)) := by
  set w := 2 ^ k
  set m := 2 ^ (d - k - 1)
  have hk25 : k < 2 ^ 25 := lt_of_lt_of_le (Nat.lt_two_pow_self) (by
    have : 2 ^ k ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hk.le
    omega)
  have hw25 : w < 2 ^ 25 := by
    have : 2 ^ k ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hk.le
    omega
  have h2w : 2 ^ (k + 1) = 2 * w := by dsimp [w]; ring
  have hdim : 2 * w * m = 2 ^ d := by
    dsimp [w, m]; rw [← pow_succ', ← pow_add]; congr 1; omega
  have hB : 2 ≤ 2 ^ (2 * w) := by
    have : 1 ≤ w := Nat.one_le_pow k 2 (by omega)
    have : 2 ^ 1 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hshr_lt : cur >>> w < 2 ^ (2 ^ d) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hcur_lt
  have hstep_eq : swarStep (2 ^ (2 ^ d) - 1) k cur =
      ∑ j ∈ Finset.range m,
        (bitCount orig (j * (2 * w)) (2 * w)) * (2 ^ (2 * w)) ^ j := by
    unfold swarStep
    dsimp only
    rw [fastPow2_eq hk25, fastPow2_eq hw25]
    rw [land_swarMask_eq hk hd hcur_lt, land_swarMask_eq hk hd hshr_lt, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hj1 : 2 * j < 2 ^ (d - k) := by
      have : 2 ^ (d - k) = 2 * m := by dsimp [m]; rw [← pow_succ']; congr 1; omega
      omega
    have hj2 : 2 * j + 1 < 2 ^ (d - k) := by
      have : 2 ^ (d - k) = 2 * m := by dsimp [m]; rw [← pow_succ']; congr 1; omega
      omega
    have ha := hinv (2 * j) hj1
    have hb := hinv (2 * j + 1) hj2
    have hshr_div : (cur >>> w) / 2 ^ (2 * j * w) = cur / 2 ^ ((2 * j + 1) * w) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
      congr 2; ring
    rw [hshr_div, ha, hb, ← add_mul, h2w]
    congr 1
    have hlo : j * (2 * w) = 2 * j * w := by ring
    have hlo2 : 2 * j * w + w = (2 * j + 1) * w := by ring
    rw [hlo, show 2 * w = w + w by ring, bitCount_add, hlo2]
  have hlt_coeff : ∀ j < m, bitCount orig (j * (2 * w)) (2 * w) < 2 ^ (2 * w) := by
    intro j _
    calc bitCount orig (j * (2 * w)) (2 * w) ≤ 2 * w := bitCount_le _ _ _
      _ < 2 ^ (2 * w) := Nat.lt_two_pow_self
  dsimp only
  rw [hstep_eq]
  constructor
  · have hs := sum_pow_lt hB m (fun j => bitCount orig (j * (2 * w)) (2 * w)) hlt_coeff
    rwa [← pow_mul, hdim] at hs
  · intro j hj
    have hjm : j < m := by
      dsimp [m]; convert hj using 2; omega
    have hpow_j : 2 ^ (j * (2 * w)) = (2 ^ (2 * w)) ^ j := by
      rw [← pow_mul, mul_comm (2 * w) j]
    rw [h2w, hpow_j]
    exact digit_extract hB m (fun i => bitCount orig (i * (2 * w)) (2 * w)) hlt_coeff j hjm

private lemma swarLoop_spec (d : ℕ) (hd : 2 ^ d < 2 ^ 25) (orig : ℕ) :
    ∀ fuel k cur, fuel + k = d →
    cur < 2 ^ (2 ^ d) →
    (∀ j < 2 ^ (d - k), (cur / 2 ^ (j * 2 ^ k)) % 2 ^ (2 ^ k) = bitCount orig (j * 2 ^ k) (2 ^ k)) →
    swarLoop (2 ^ (2 ^ d) - 1) fuel k cur = bitCount orig 0 (2 ^ d)
  | 0, k, cur, hkd, hcur_lt, hinv => by
    have hk : k = d := by omega
    subst hk
    simp only [swarLoop]
    have h0 := hinv 0 (by simp)
    simp only [zero_mul, pow_zero, Nat.div_one] at h0
    rwa [Nat.mod_eq_of_lt hcur_lt] at h0
  | fuel + 1, k, cur, hkd, hcur_lt, hinv => by
    simp only [swarLoop]
    have hk : k < d := by omega
    obtain ⟨hnxt_lt, hnxt_inv⟩ := swarStep_spec hk hd hcur_lt hinv
    exact swarLoop_spec d hd orig fuel (k + 1) _ (by omega) hnxt_lt hnxt_inv

private lemma swarPopcount_eq {d x : ℕ} (hd : 2 ^ d < 2 ^ 25) (hx : x < 2 ^ (2 ^ d)) :
    swarPopcount d x = bitCount x 0 (2 ^ d) := by
  unfold swarPopcount
  have hd25 : d < 2 ^ 25 := lt_of_lt_of_le Nat.lt_two_pow_self hd.le
  rw [fastPow2_eq hd25, fastPow2_eq hd]
  apply swarLoop_spec d hd x d 0 x (by omega) hx
  intro j _
  have hIco : Finset.Ico j (j + 1) = {j} := by
    ext a; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
  simp only [pow_zero, mul_one, pow_one, bitCount, hIco]
  by_cases htb : x.testBit j = true
  · have hmod : (x / 2 ^ j) % 2 = 1 := by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at htb; exact htb
    rw [hmod, Finset.filter_singleton, if_pos htb, Finset.card_singleton]
  · have hmod : (x / 2 ^ j) % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at htb
      omega
    rw [hmod, Finset.filter_singleton, if_neg htb, Finset.card_empty]

private lemma swarPopcount_slice_eq {d pm A B : ℕ}
    (hd : 2 ^ d < 2 ^ 25) (hAB : B - A ≤ 2 ^ d) :
    swarPopcount d ((pm >>> (A + 1)) &&& (fastPow2 (B - A) - 1)) =
      #{i ∈ Finset.Ioc A B | pm.testBit i = true} := by
  have hBA25 : B - A < 2 ^ 25 := by omega
  rw [fastPow2_eq hBA25]
  set s := (pm >>> (A + 1)) &&& (2 ^ (B - A) - 1)
  have hs_lt : s < 2 ^ (2 ^ d) := by
    have h1 : s ≤ 2 ^ (B - A) - 1 := Nat.and_le_right
    have h2 : 2 ^ (B - A) ≤ 2 ^ (2 ^ d) := Nat.pow_le_pow_right (by omega) hAB
    have h3 : 1 ≤ 2 ^ (B - A) := Nat.one_le_pow _ _ (by omega)
    omega
  rw [swarPopcount_eq hd hs_lt]
  unfold bitCount
  rw [zero_add]
  refine Finset.card_bij (fun j _ => A + 1 + j) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc] at hj ⊢
    dsimp [s] at hj
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    exact ⟨⟨by omega, by omega⟩, hj.2.1⟩
  · intro a _ b _ hab; omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hi
    refine ⟨i - (A + 1), ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    dsimp [s]
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
    have h1 : A + 1 + (i - (A + 1)) = i := by omega
    have h2 : i - (A + 1) < B - A := by omega
    simp [h1, h2, hi.2]

private lemma piFastD_eq_primeCounting {d N B : ℕ} {ps : List ℕ}
    (hd : 2 ^ d < 2 ^ 25) (hN : 2 ≤ N) (hN25 : N + 1 < 2 ^ 25)
    (hBN : B ≤ N) (hB_pow : B + 1 ≤ 2 ^ d)
    (hps_ge : ∀ p ∈ ps, 2 ≤ p ∧ p * (N / p + 1) < 2 ^ 25)
    (hps_cover : ∀ q : ℕ, q.Prime → q * q ≤ N → q ∈ ps) :
    swarPopcount d ((primeMaskWith N ps) &&& (fastPow2 (B + 1) - 1)) = Nat.primeCounting B := by
  have hB25 : B + 1 < 2 ^ 25 := by omega
  rw [fastPow2_eq hB25]
  set s := primeMaskWith N ps &&& (2 ^ (B + 1) - 1)
  have hs_lt : s < 2 ^ (2 ^ d) := by
    have h1 : s ≤ 2 ^ (B + 1) - 1 := Nat.and_le_right
    have h2 : 2 ^ (B + 1) ≤ 2 ^ (2 ^ d) := Nat.pow_le_pow_right (by omega) hB_pow
    have h3 : 1 ≤ 2 ^ (B + 1) := Nat.one_le_pow _ _ (by omega)
    omega
  rw [swarPopcount_eq hd hs_lt, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range]
  unfold bitCount
  rw [zero_add]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range, zero_le, true_and]
  dsimp [s]
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨_, htb, hilt⟩
    exact ⟨hilt, (primeMaskWith_testBit hN hN25 hps_ge hps_cover (by omega)).mp htb⟩
  · rintro ⟨hilt, hp⟩
    exact ⟨by omega, (primeMaskWith_testBit hN hN25 hps_ge hps_cover (by omega)).mpr hp, hilt⟩

/-! ## `fastPhi` correctness -/

private def divOut : Nat → Nat → Nat → Nat
  | 0, n, _ => n
  | f + 1, n, p => if n % p = 0 then divOut f (n / p) p else n

private lemma divOut_spec : ∀ f n p, 2 ≤ p → 0 < n → n < 2 ^ f →
    ∃ e, n = divOut f n p * p ^ e ∧ ¬ p ∣ divOut f n p
  | 0, n, _, _, hn0, hn => by omega
  | f + 1, n, p, hp, hn0, hn => by
    unfold divOut
    split_ifs with hmod
    · have hdiv_pos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn0 (Nat.dvd_of_mod_eq_zero hmod)) (by omega)
      have hdiv_lt : n / p < 2 ^ f := by
        have hmul : (n / p) * p ≤ n := Nat.div_mul_le_self n p
        have h2 : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
        nlinarith
      obtain ⟨e, heq, hndvd⟩ := divOut_spec f (n / p) p hp hdiv_pos hdiv_lt
      refine ⟨e + 1, ?_, hndvd⟩
      have hmul : (n / p) * p = n := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
      calc n = (n / p) * p := hmul.symm
        _ = (divOut f (n / p) p * p ^ e) * p := congrArg (· * p) heq
        _ = divOut f (n / p) p * p ^ (e + 1) := by rw [pow_succ]; ring
    · exact ⟨0, by simp, fun h => hmod (Nat.mod_eq_zero_of_dvd h)⟩

private def phiStep (p : Nat) (st : Nat × Nat) : Nat × Nat :=
  let (rem, res) := st
  if rem % p = 0 then (divOut 20 (rem / p) p, res / p * (p - 1)) else (rem, res)

private def phiFromPrimes : List Nat → Nat × Nat → Nat × Nat
  | [], st => st
  | p :: ps, st => if p * p > st.1 then st else phiFromPrimes ps (phiStep p st)

private lemma phiStep_spec {n p rem res : ℕ} (hp : p.Prime)
    (hrem_pos : 0 < rem) (hrem_lt : rem < 2 ^ 20)
    (hinv : res * rem.totient = n.totient * rem) (hdvd : rem ∣ res)
    (hno : ∀ q, q.Prime → q ∣ rem → p ≤ q) :
    let st' := phiStep p (rem, res)
    0 < st'.1 ∧ st'.1 ≤ rem ∧
    st'.2 * st'.1.totient = n.totient * st'.1 ∧
    st'.1 ∣ st'.2 ∧
    (∀ q, q.Prime → q ∣ st'.1 → p < q) := by
  unfold phiStep
  dsimp only
  split_ifs with hmod
  · have hpdvd : p ∣ rem := Nat.dvd_of_mod_eq_zero hmod
    have hdiv_pos : 0 < rem / p := Nat.div_pos (Nat.le_of_dvd hrem_pos hpdvd) hp.pos
    have hdiv_lt : rem / p < 2 ^ 20 := lt_of_le_of_lt (Nat.div_le_self _ _) hrem_lt
    obtain ⟨e, heq, hndvd⟩ := divOut_spec 20 (rem / p) p hp.two_le hdiv_pos hdiv_lt
    set rem' := divOut 20 (rem / p) p
    have hrem_eq : rem = rem' * p ^ (e + 1) := by
      have hmul : (rem / p) * p = rem := Nat.div_mul_cancel hpdvd
      rw [← hmul, heq, pow_succ]; ring
    have hrem'_pos : 0 < rem' := by
      by_contra h0
      have : rem' = 0 := by omega
      rw [this, zero_mul] at hrem_eq; omega
    have hrem'_le : rem' ≤ rem := by
      rw [hrem_eq]
      exact Nat.le_mul_of_pos_right rem' (pow_pos hp.pos _)
    have hcop : Nat.Coprime rem' (p ^ (e + 1)) :=
      (hp.coprime_iff_not_dvd.mpr hndvd).symm.pow_right (e + 1)
    have hphi_rem : rem.totient = rem'.totient * (p ^ e * (p - 1)) := by
      rw [hrem_eq, Nat.totient_mul hcop, Nat.totient_prime_pow hp (by omega)]
      simp [mul_comm]
    have hres_dvd : p ∣ res := hpdvd.trans hdvd
    have hinv' : res / p * (p - 1) * rem'.totient = n.totient * rem' := by
      have h1 : (res / p * (p - 1) * rem'.totient) * p ^ (e + 1) =
          (n.totient * rem') * p ^ (e + 1) := by
        calc (res / p * (p - 1) * rem'.totient) * p ^ (e + 1)
          _ = (res / p * p) * (rem'.totient * (p ^ e * (p - 1))) := by rw [pow_succ]; ring
          _ = res * rem.totient := by rw [Nat.div_mul_cancel hres_dvd, hphi_rem]
          _ = n.totient * rem := hinv
          _ = (n.totient * rem') * p ^ (e + 1) := by rw [hrem_eq]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) h1
    have hdvd' : rem' ∣ res / p * (p - 1) := by
      have hrem'_p : rem' * p ∣ rem := ⟨p ^ e, by rw [hrem_eq, pow_succ]; ring⟩
      obtain ⟨c, hc⟩ := hrem'_p.trans hdvd
      have hdiv_eq : res / p = rem' * c := by
        have : res = (rem' * c) * p := by rw [hc]; ring
        rw [this, Nat.mul_div_cancel _ hp.pos]
      rw [hdiv_eq]
      exact ⟨c * (p - 1), by ring⟩
    have hno' : ∀ q, q.Prime → q ∣ rem' → p < q := by
      intro q hqp hqdvd
      have hqdvd_rem : q ∣ rem := hqdvd.trans ⟨p ^ (e + 1), hrem_eq⟩
      have hge := hno q hqp hqdvd_rem
      have hne : q ≠ p := fun h => hndvd (h ▸ hqdvd)
      omega
    exact ⟨hrem'_pos, hrem'_le, hinv', hdvd', hno'⟩
  · refine ⟨hrem_pos, le_rfl, hinv, hdvd, ?_⟩
    intro q hqp hqdvd
    have hge := hno q hqp hqdvd
    have hne : q ≠ p := fun h => hmod (Nat.mod_eq_zero_of_dvd (h ▸ hqdvd))
    omega

private lemma phiFromPrimes_spec {n : ℕ} :
    ∀ (ps : List ℕ) (rem res bound : ℕ),
    (∀ p ∈ ps, p.Prime ∧ bound ≤ p) →
    (∀ q : ℕ, q.Prime → bound ≤ q → q * q ≤ rem → q ∈ ps) →
    ps.Pairwise (· < ·) →
    0 < rem → rem < 2 ^ 20 →
    res * rem.totient = n.totient * rem → rem ∣ res →
    (∀ q, q.Prime → q ∣ rem → bound ≤ q) →
    let st := phiFromPrimes ps (rem, res)
    (if st.1 > 1 then st.2 / st.1 * (st.1 - 1) else st.2) = n.totient := by
  intro ps
  induction ps with
  | nil =>
    intro rem res bound _ hcov _ hrem_pos _ hinv hdvd hno
    dsimp [phiFromPrimes]
    split_ifs with hgt
    · have hrem_p : rem.Prime := by
        by_contra hnp
        have hmf_p := Nat.minFac_prime (by omega : rem ≠ 1)
        have hmf_dvd := Nat.minFac_dvd rem
        have hmf_sq : rem.minFac * rem.minFac ≤ rem := by
          simpa [sq] using Nat.minFac_sq_le_self hrem_pos hnp
        exact List.not_mem_nil (hcov rem.minFac hmf_p (hno _ hmf_p hmf_dvd) hmf_sq)
      have hphi_eq : rem.totient = rem - 1 := Nat.totient_prime hrem_p
      have hmul : (res / rem * (rem - 1)) * rem = n.totient * rem := by
        calc (res / rem * (rem - 1)) * rem
          _ = (res / rem * rem) * (rem - 1) := by ring
          _ = res * rem.totient := by rw [Nat.div_mul_cancel hdvd, hphi_eq]
          _ = n.totient * rem := hinv
      exact Nat.eq_of_mul_eq_mul_right hrem_pos hmul
    · have h1 : rem = 1 := by omega
      subst h1
      simpa using hinv
  | cons p ps ih =>
    intro rem res bound hps_p hcov hpair hrem_pos hrem_lt hinv hdvd hno
    obtain ⟨hp_lt_tail, hpair_tail⟩ := List.pairwise_cons.mp hpair
    obtain ⟨hp_p, hp_ge_b⟩ := hps_p p List.mem_cons_self
    unfold phiFromPrimes
    dsimp only
    by_cases hstop : p * p > rem
    · rw [if_pos hstop]
      have hno_div : ∀ q, q.Prime → q ∣ rem → ¬ q * q ≤ rem := by
        intro q hqp hqdvd hqsq
        have hmem := hcov q hqp (hno q hqp hqdvd) hqsq
        have hp_le_q : p ≤ q := by
          rcases List.mem_cons.mp hmem with rfl | htail
          · exact le_rfl
          · exact (hp_lt_tail q htail).le
        nlinarith
      split_ifs with hgt
      · have hrem_p : rem.Prime := by
          by_contra hnp
          exact hno_div rem.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd rem)
            (by simpa [sq] using Nat.minFac_sq_le_self hrem_pos hnp)
        have hphi_eq : rem.totient = rem - 1 := Nat.totient_prime hrem_p
        have hmul : (res / rem * (rem - 1)) * rem = n.totient * rem := by
          calc (res / rem * (rem - 1)) * rem
            _ = (res / rem * rem) * (rem - 1) := by ring
            _ = res * rem.totient := by rw [Nat.div_mul_cancel hdvd, hphi_eq]
            _ = n.totient * rem := hinv
        exact Nat.eq_of_mul_eq_mul_right hrem_pos hmul
      · have h1 : rem = 1 := by omega
        subst h1
        simpa using hinv
    · rw [if_neg hstop]
      have hno_p : ∀ q, q.Prime → q ∣ rem → p ≤ q := by
        intro q hqp hqdvd
        by_contra hlt
        push Not at hlt
        have hqsq : q * q ≤ rem := by nlinarith
        have hmem := hcov q hqp (hno q hqp hqdvd) hqsq
        rcases List.mem_cons.mp hmem with rfl | htail
        · omega
        · have := hp_lt_tail q htail; omega
      obtain ⟨hpos', hle', hinv', hdvd', hno'⟩ :=
        phiStep_spec hp_p hrem_pos hrem_lt hinv hdvd hno_p
      have hcov' : ∀ q : ℕ, q.Prime → p + 1 ≤ q → q * q ≤ (phiStep p (rem, res)).1 → q ∈ ps := by
        intro q hqp hqge hqsq
        have hmem := hcov q hqp (by omega) (hqsq.trans hle')
        rcases List.mem_cons.mp hmem with rfl | htail
        · omega
        · exact htail
      exact ih (phiStep p (rem, res)).1 (phiStep p (rem, res)).2 (p + 1)
        (fun q hq => ⟨(hps_p q (List.mem_cons_of_mem p hq)).1, by have := hp_lt_tail q hq; omega⟩)
        hcov' hpair_tail hpos' (lt_of_le_of_lt hle' hrem_lt) hinv' hdvd'
        (fun q hqp hqd => by have := hno' q hqp hqd; omega)



/-! ## Soundness of incremental block and step checkers -/

private lemma primeCounting_add_Ioc {a b : ℕ} (hab : a ≤ b) :
    Nat.primeCounting a + #{i ∈ Finset.Ioc a b | i.Prime} = Nat.primeCounting b := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting]
  have hunion : Nat.primesLE b = Nat.primesLE a ∪ (Finset.Ioc a b).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpb, hp⟩
      by_cases hpa : p ≤ a
      · exact Or.inl ⟨hpa, hp⟩
      · exact Or.inr ⟨⟨by omega, hpb⟩, hp⟩
    · rintro (⟨hpa, hp⟩ | ⟨⟨_, hpb⟩, hp⟩)
      · exact ⟨hpa.trans hab, hp⟩
      · exact ⟨hpb, hp⟩
  have hdisj : Disjoint (Nat.primesLE a) ((Finset.Ioc a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc] at h1 h2
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj]

private lemma primeCounting_step {pm N a b : ℕ} {dSlice : ℕ}
    (hd : 2 ^ dSlice < 2 ^ 25)
    (hpm : ∀ i ≤ N, pm.testBit i = true ↔ i.Prime)
    (hab : a ≤ b) (hbN : b ≤ N) (hw : b - a ≤ 2 ^ dSlice) :
    Nat.primeCounting a + swarPopcount dSlice ((pm >>> (a + 1)) &&& (fastPow2 (b - a) - 1)) =
      Nat.primeCounting b := by
  rw [swarPopcount_slice_eq hd hw, ← primeCounting_add_Ioc hab]
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hi1, hi2⟩, htb⟩
    exact ⟨⟨hi1, hi2⟩, (hpm i (hi2.trans hbN)).mp htb⟩
  · rintro ⟨⟨hi1, hi2⟩, hp⟩
    exact ⟨⟨hi1, hi2⟩, (hpm i (hi2.trans hbN)).mpr hp⟩

private def checkBlocksInc (dSlice : Nat) (pm : Nat) (num den : Nat) :
    Nat → Nat → List (Nat × Nat) → Bool
  | _, _, [] => true
  | prev, pi_prev, (a, b) :: rest =>
    if b < prev || b - prev > fastPow2 dSlice then false
    else
      let slice := (pm >>> (prev + 1)) &&& (fastPow2 (b - prev) - 1)
      let pi_b := pi_prev + swarPopcount dSlice slice
      decide (num * a > den * 2 * pi_b) && checkBlocksInc dSlice pm num den b pi_b rest

private lemma checkBlocksInc_sound {dSlice N num den pm : ℕ}
    (hd : 2 ^ dSlice < 2 ^ 25)
    (hpm : ∀ i ≤ N, pm.testBit i = true ↔ i.Prime) :
    ∀ (prev pi_prev : ℕ) (bs : List (Nat × Nat)),
    pi_prev = Nat.primeCounting prev →
    (∀ ab ∈ bs, ab.2 ≤ N) →
    checkBlocksInc dSlice pm num den prev pi_prev bs = true →
    ∀ ab ∈ bs, num * ab.1 > den * 2 * Nat.primeCounting ab.2
  | _, _, [], _, _, _, _, hab => nomatch hab
  | prev, pi_prev, (a, b) :: rest, hpi_prev, hleN, hchk, ab, hab => by
    unfold checkBlocksInc at hchk
    have hd25 : dSlice < 2 ^ 25 := lt_of_lt_of_le Nat.lt_two_pow_self hd.le
    rw [fastPow2_eq hd25] at hchk
    by_cases hbad : (b < prev || b - prev > 2 ^ dSlice) = true
    · rw [if_pos hbad] at hchk; exact Bool.noConfusion hchk
    · rw [if_neg hbad] at hchk
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hbad
      have hpb : prev ≤ b := hbad.1
      have hw : b - prev ≤ 2 ^ dSlice := hbad.2
      dsimp only at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
      have hbN : b ≤ N := hleN (a, b) List.mem_cons_self
      have hpi_b : pi_prev + swarPopcount dSlice ((pm >>> (prev + 1)) &&& (fastPow2 (b - prev) - 1)) =
          Nat.primeCounting b := by
        rw [hpi_prev]
        exact primeCounting_step hd hpm hpb hbN hw
      rcases List.mem_cons.mp hab with rfl | hrest
      · rw [← hpi_b]; exact hchk.1
      · exact checkBlocksInc_sound hd hpm b _ rest hpi_b
          (fun x hx => hleN x (List.mem_cons_of_mem _ hx)) hchk.2 ab hrest

-- Helper: check that a list of blocks covers [lo, hi]
private def blocksCover : Nat → Nat → List (Nat × Nat) → Bool
  | cur, hi, [] => decide (cur > hi)
  | cur, hi, (a, b) :: rest =>
    decide (a ≤ cur ∧ cur ≤ b) && blocksCover (b + 1) hi rest

private lemma blocksCover_sound : ∀ (cur hi : ℕ) (bs : List (Nat × Nat)),
    blocksCover cur hi bs = true →
    ∀ n, cur ≤ n → n ≤ hi → ∃ ab ∈ bs, ab.1 ≤ n ∧ n ≤ ab.2
  | cur, hi, [], hcov, n, h1, h2 => by
    simp only [blocksCover, decide_eq_true_eq] at hcov; omega
  | cur, hi, (a, b) :: rest, hcov, n, h1, h2 => by
    simp only [blocksCover, Bool.and_eq_true, decide_eq_true_eq] at hcov
    by_cases hnb : n ≤ b
    · exact ⟨(a, b), List.mem_cons_self, by omega, hnb⟩
    · obtain ⟨ab, hab, h1', h2'⟩ := blocksCover_sound (b + 1) hi rest hcov.2 n (by omega) h2
      exact ⟨ab, List.mem_cons_of_mem _ hab, h1', h2'⟩

private def checkLinear (pm : Nat) (listedL : List Nat) (fastPhi : Nat → Nat) :
    Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, n, pi_prev =>
    let pi_n := pi_prev + ((pm >>> n) % 2)
    let ok := (fastPhi n == 2 * pi_n) == (listedL.elem n)
    ok && checkLinear pm listedL fastPhi fuel (n + 1) pi_n

private lemma checkLinear_sound {pm N : ℕ} {listedL : List ℕ} {fastPhi : ℕ → ℕ}
    (hpm : ∀ i ≤ N, pm.testBit i = true ↔ i.Prime)
    (hphi : ∀ n, 1 ≤ n → n ≤ N → fastPhi n = n.totient) :
    ∀ (fuel n pi_prev : ℕ),
    1 ≤ n → n + fuel ≤ N + 1 →
    pi_prev = Nat.primeCounting (n - 1) →
    checkLinear pm listedL fastPhi fuel n pi_prev = true →
    ∀ m, n ≤ m → m < n + fuel → (m.totient = 2 * Nat.primeCounting m ↔ m ∈ listedL)
  | 0, _, _, _, _, _, _, m, h1, h2 => by omega
  | fuel + 1, n, pi_prev, hn1, hleN, hpi_prev, hchk, m, hm1, hm2 => by
    unfold checkLinear at hchk
    simp only [Bool.and_eq_true] at hchk
    have hbit : (pm >>> n) % 2 = if n.Prime then 1 else 0 := by
      have htb : pm.testBit n = decide (((pm >>> n) % 2) = 1) := by
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
      have hiff := hpm n (by omega)
      by_cases hp : n.Prime
      · have h1 := hiff.mpr hp
        rw [htb, decide_eq_true_eq] at h1; simp [hp, h1]
      · have h0 : pm.testBit n = false := by
          cases hb : pm.testBit n
          · rfl
          · exact absurd (hiff.mp hb) hp
        rw [htb, decide_eq_false_iff_not] at h0
        have hlt2 : (pm >>> n) % 2 < 2 := Nat.mod_lt _ (by omega)
        simp [hp]; omega
    have hpi_n : pi_prev + (pm >>> n) % 2 = Nat.primeCounting n := by
      rw [hpi_prev, hbit]
      have hstep := primeCounting_add_Ioc (show n - 1 ≤ n by omega)
      have hIoc : Finset.Ioc (n - 1) n = {n} := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
      rw [hIoc, Finset.filter_singleton] at hstep
      by_cases hp : n.Prime
      · rw [if_pos hp, Finset.card_singleton] at hstep
        rw [if_pos hp]; exact hstep
      · rw [if_neg hp, Finset.card_empty, add_zero] at hstep
        rw [if_neg hp, add_zero]; exact hstep
    by_cases hmn : m = n
    · subst hmn
      have hok := hchk.1
      rw [hpi_n, hphi m hn1 (by omega)] at hok
      simp only [beq_iff_eq, List.elem_eq_mem] at hok
      have heq_iff : ((m.totient == 2 * Nat.primeCounting m) = true) ↔ (decide (m ∈ listedL) = true) := by
        rw [hok]
      simpa [beq_iff_eq, decide_eq_true_eq] using heq_iff
    · exact checkLinear_sound hpm hphi fuel (n + 1) _ (by omega) (by omega)
        (by simpa using hpi_n) hchk.2 m (by omega) (by omega)

private def checkStepInChunk (pm : Nat) (listedL : List Nat) (fastPhi : Nat → Nat)
    (step A piA piB : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, n =>
    let ph := fastPhi n
    let inL := listedL.elem n
    let ok :=
      if !inL && (ph < 2 * piA || ph > 2 * piB) then true
      else
        let slice := (pm >>> (A + 1)) &&& (fastPow2 (n - A) - 1)
        let pi_n := piA + swarPopcount 10 slice
        (ph == 2 * pi_n) == inL
    ok && checkStepInChunk pm listedL fastPhi step A piA piB fuel (n + step)

private lemma checkStepInChunk_sound {pm N : ℕ} {listedL : List ℕ} {fastPhi : ℕ → ℕ}
    {step A piA piB B : ℕ}
    (hpm : ∀ i ≤ N, pm.testBit i = true ↔ i.Prime)
    (hphi : ∀ n, 1 ≤ n → n ≤ N → fastPhi n = n.totient)
    (hBN : B ≤ N) (hAB : B - A ≤ 1024)
    (hpiA : piA = Nat.primeCounting A) (hpiB : piB = Nat.primeCounting B) :
    ∀ (fuel n0 : ℕ),
    1 ≤ n0 → A ≤ n0 →
    (∀ k < fuel, n0 + k * step ≤ B) →
    checkStepInChunk pm listedL fastPhi step A piA piB fuel n0 = true →
    ∀ k < fuel, ((n0 + k * step).totient = 2 * Nat.primeCounting (n0 + k * step) ↔
      (n0 + k * step) ∈ listedL)
  | 0, _, _, _, _, _, k, hk => by omega
  | fuel + 1, n0, hn0_1, hAn0, hleB, hchk, k, hk => by
    unfold checkStepInChunk at hchk
    rw [Bool.and_eq_true] at hchk
    cases k with
    | zero =>
      simp only [zero_mul, add_zero]
      have hn0B : n0 ≤ B := by simpa using hleB 0 (by omega)
      have hn0N : n0 ≤ N := hn0B.trans hBN
      have hok := hchk.1
      have hph : fastPhi n0 = n0.totient := hphi n0 hn0_1 hn0N
      rw [hph] at hok
      by_cases hcond : (!listedL.elem n0 && (decide (n0.totient < 2 * piA) || decide (n0.totient > 2 * piB))) = true
      · simp only [Bool.and_eq_true, Bool.not_eq_true', List.elem_eq_mem, decide_eq_false_iff_not,
                   Bool.or_eq_true, decide_eq_true_eq] at hcond
        have hmono1 : Nat.primeCounting A ≤ Nat.primeCounting n0 := Nat.monotone_primeCounting hAn0
        have hmono2 : Nat.primeCounting n0 ≤ Nat.primeCounting B := Nat.monotone_primeCounting hn0B
        rw [hpiA, hpiB] at hcond
        have hne : n0.totient ≠ 2 * Nat.primeCounting n0 := by omega
        exact ⟨fun h => absurd h hne, fun h => absurd h hcond.1⟩
      · rw [if_neg hcond] at hok
        have hpi_n0 : piA + swarPopcount 10 ((pm >>> (A + 1)) &&& (fastPow2 (n0 - A) - 1)) =
            Nat.primeCounting n0 := by
          rw [hpiA]
          exact primeCounting_step (dSlice := 10) (by norm_num) hpm hAn0 hn0N (by omega)
        dsimp only at hok
        rw [hpi_n0] at hok
        simp only [beq_iff_eq, List.elem_eq_mem] at hok
        have heq_iff : ((n0.totient == 2 * Nat.primeCounting n0) = true) ↔ (decide (n0 ∈ listedL) = true) := by
          rw [hok]
        simpa [beq_iff_eq, decide_eq_true_eq] using heq_iff
    | succ k' =>
      have hih := checkStepInChunk_sound hpm hphi hBN hAB hpiA hpiB fuel (n0 + step)
        (by omega) (by omega)
        (fun j hj => by
          have := hleB (j + 1) (by omega)
          have heq : n0 + step + j * step = n0 + (j + 1) * step := by ring
          linarith)
        hchk.2 k' (by omega)
      have heq : n0 + (k' + 1) * step = n0 + step + k' * step := by ring
      rwa [heq]

private def checkStepRange (pm : Nat) (listedL : List Nat) (fastPhi : Nat → Nat)
    (step lo hi : Nat) : Nat → Nat → Nat → Bool
  | 0, A, _ => decide (A ≥ hi)
  | fuel + 1, A, piA =>
    if A ≥ hi then true
    else
      let B := min hi (A + 1024)
      let slice := (pm >>> (A + 1)) &&& (fastPow2 (B - A) - 1)
      let piB := piA + swarPopcount 10 slice
      let start := max lo (A + 1)
      let first := start + ((step - start % step) % step)
      let cnt := if first > B then 0 else (B - first) / step + 1
      checkStepInChunk pm listedL fastPhi step A piA piB cnt first &&
      checkStepRange pm listedL fastPhi step lo hi fuel B piB

private lemma checkStepRange_sound {pm N : ℕ} {listedL : List ℕ} {fastPhi : ℕ → ℕ}
    {step lo hi : ℕ}
    (hstep : 1 ≤ step) (hlo : 1 ≤ lo) (hhiN : hi ≤ N)
    (hpm : ∀ i ≤ N, pm.testBit i = true ↔ i.Prime)
    (hphi : ∀ n, 1 ≤ n → n ≤ N → fastPhi n = n.totient) :
    ∀ (fuel A piA : ℕ),
    piA = Nat.primeCounting A →
    checkStepRange pm listedL fastPhi step lo hi fuel A piA = true →
    ∀ n, lo ≤ n → A < n → n ≤ hi → step ∣ n →
      (n.totient = 2 * Nat.primeCounting n ↔ n ∈ listedL)
  | 0, A, _, _, hchk, n, _, hAn, nhi, _ => by
    simp only [checkStepRange, decide_eq_true_eq] at hchk; omega
  | fuel + 1, A, piA, hpiA, hchk, n, hlo_n, hAn, nhi, hdvd => by
    unfold checkStepRange at hchk
    split_ifs at hchk with hge
    · omega
    · simp only [Bool.and_eq_true] at hchk
      set B := min hi (A + 1024)
      have hAB : A ≤ B := by dsimp [B]; omega
      have hBN : B ≤ N := by dsimp [B]; omega
      have hw : B - A ≤ 1024 := by dsimp [B]; omega
      have hpiB : piA + swarPopcount 10 ((pm >>> (A + 1)) &&& (fastPow2 (B - A) - 1)) =
          Nat.primeCounting B := by
        rw [hpiA]
        exact primeCounting_step (dSlice := 10) (by norm_num) hpm hAB hBN hw
      by_cases hnB : n ≤ B
      · set start := max lo (A + 1)
        set first := start + ((step - start % step) % step)
        have hstart_le : start ≤ n := by dsimp [start]; omega
        have hfirst_dvd : step ∣ first := by
          dsimp [first]
          have hmod_lt : start % step < step := Nat.mod_lt start (by omega)
          by_cases hm0 : start % step = 0
          · simp [hm0, Nat.dvd_iff_mod_eq_zero]
          · have hsub : (step - start % step) % step = step - start % step :=
              Nat.mod_eq_of_lt (by omega)
            rw [hsub, Nat.dvd_iff_mod_eq_zero]
            have hdiv := Nat.div_add_mod start step
            have hmul : start + (step - start % step) = step * (start / step + 1) := by
              rw [mul_add, mul_one]; omega
            rw [hmul]
            exact Nat.mul_mod_right step (start / step + 1)
        have hfirst_le : first ≤ n := by
          dsimp [first]
          obtain ⟨q, rfl⟩ := hdvd
          have hmod_lt : start % step < step := Nat.mod_lt start (by omega)
          by_cases hm0 : start % step = 0
          · simp [hm0]; omega
          · have hsub : (step - start % step) % step = step - start % step :=
              Nat.mod_eq_of_lt (by omega)
            rw [hsub]
            have hdiv := Nat.div_add_mod start step
            have hlt : step * (start / step) < step * q := by omega
            have hq_ge : start / step + 1 ≤ q := by
              have : start / step < q := Nat.lt_of_mul_lt_mul_left hlt
              omega
            have hmul : start + (step - start % step) = step * (start / step + 1) := by
              rw [mul_add, mul_one]; omega
            rw [hmul]
            exact Nat.mul_le_mul_left step hq_ge
        have hfirst_ge_A : A ≤ first := by dsimp [first, start]; omega
        have hfirst_ge_1 : 1 ≤ first := by dsimp [first, start]; omega
        have hcnt_eq : (if first > B then 0 else (B - first) / step + 1) = (B - first) / step + 1 := by
          have : ¬ first > B := by omega
          simp [this]
        have hdiff_dvd : step ∣ (n - first) := Nat.dvd_sub hdvd hfirst_dvd
        set k := (n - first) / step
        have hn_eq : first + k * step = n := by
          have hmul : k * step = n - first := Nat.div_mul_cancel hdiff_dvd
          omega
        have hk_lt : k < (B - first) / step + 1 := by
          have : k ≤ (B - first) / step := Nat.div_le_div_right (by omega)
          omega
        have hleB : ∀ j < (B - first) / step + 1, first + j * step ≤ B := by
          intro j hj
          have hjle : j ≤ (B - first) / step := by omega
          have h1 : j * step ≤ ((B - first) / step) * step := Nat.mul_le_mul_right step hjle
          have h2 : ((B - first) / step) * step ≤ B - first := Nat.div_mul_le_self (B - first) step
          omega
        have hchk1 := hchk.1
        rw [hcnt_eq] at hchk1
        have hres := checkStepInChunk_sound hpm hphi hBN hw hpiA hpiB
          ((B - first) / step + 1) first hfirst_ge_1 hfirst_ge_A hleB hchk1 k hk_lt
        rwa [hn_eq] at hres
      · exact checkStepRange_sound hstep hlo hhiN hpm hphi fuel B _ hpiB hchk.2 n hlo_n (by omega) nhi hdvd

end Sieve

section Finite
open Finset

private def primes349 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349]
private def primes1021 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021]
private def listedL : List ℕ := [11, 13, 27, 39, 63, 122, 124, 136, 152, 176, 224, 322, 364, 410, 460, 1086, 1164, 3432, 3612, 12012]
private def blocks_avoid2 : List (ℕ × ℕ) := [(751, 918), (919, 1152), (1153, 1510), (1511, 2082), (2083, 3018), (3019, 3100)]
private def blocks_avoid35 : List (ℕ × ℕ) := [(751, 768), (769, 796), (797, 826), (827, 858), (859, 906), (907, 970), (971, 1038), (1039, 1116), (1117, 1228), (1229, 1380), (1381, 1578), (1579, 1860), (1861, 2250), (2251, 2788), (2789, 3100)]
private def blocks_avoid3 : List (ℕ × ℕ) := [(3101, 3162), (3163, 3220), (3221, 3300), (3301, 3370), (3371, 3462), (3463, 3558), (3559, 3670), (3671, 3802), (3803, 3946), (3947, 4128), (4129, 4348), (4349, 4638), (4639, 4992), (4993, 5440), (5441, 5986), (5987, 6688), (6689, 7582), (7583, 8746), (8747, 10266), (10267, 12200)]
private def blocks_avoid57 : List (ℕ × ℕ) := [(3801, 3832), (3833, 3876), (3877, 3918), (3919, 3966), (3967, 4018), (4019, 4090), (4091, 4158), (4159, 4242), (4243, 4348), (4349, 4482), (4483, 4642), (4643, 4830), (4831, 5050), (5051, 5346), (5347, 5682), (5683, 6090), (6091, 6580), (6581, 7210), (7211, 8010), (8011, 9012), (9013, 10272), (10273, 11980), (11981, 12200)]
private def blocks_avoid5 : List (ℕ × ℕ) := [(12201, 12240), (12241, 12276), (12277, 12322), (12323, 12378), (12379, 12432), (12433, 12490), (12491, 12540), (12541, 12588), (12589, 12640), (12641, 12696), (12697, 12762), (12763, 12840), (12841, 12922), (12923, 13006), (13007, 13108), (13109, 13218), (13219, 13338), (13339, 13498), (13499, 13692), (13693, 13900), (13901, 14158), (14159, 14488), (14489, 14826), (14827, 15232), (15233, 15660), (15661, 16138), (16139, 16740), (16741, 17448), (17449, 18252), (18253, 19308), (19309, 20508), (20509, 21936), (21937, 23628), (23629, 25732), (25733, 28318), (28319, 31542), (31543, 35526), (35527, 40636), (40637, 41000)]
private def blocks_avoid711 : List (ℕ × ℕ) := [(22001, 22810), (22811, 23760), (23761, 24916), (24917, 26262), (26263, 27882), (27883, 29818), (29819, 32202), (32203, 34962), (34963, 38376), (38377, 41000)]
private def blocks_avoid7 : List (ℕ × ℕ) := [(41001, 41232), (41233, 41520), (41521, 41842), (41843, 42168), (42169, 42460), (42461, 42766), (42767, 43102), (43103, 43578), (43579, 44100), (44101, 44686), (44687, 45342), (45343, 46152), (46153, 47122), (47123, 48196), (48197, 49408), (49409, 50788), (50789, 52320), (52321, 54120), (54121, 56178), (56179, 58438), (58439, 61120), (61121, 64282), (64283, 67960), (67961, 72000)]
private def blocks_avoid11 : List (ℕ × ℕ) := [(72001, 72226), (72227, 72496), (72497, 72816), (72817, 73126), (73127, 73546), (73547, 74020), (74021, 74520), (74521, 75078), (75079, 75678), (75679, 76378), (76379, 77200), (77201, 78040), (78041, 79042), (79043, 80166), (80167, 81348), (81349, 82618), (82619, 84162), (84163, 85902), (85903, 87852), (87853, 90066), (90067, 92592), (92593, 95382), (95383, 98640), (98641, 102250), (102251, 106530), (106531, 111520), (111521, 117328), (117329, 119999)]
private def blocks_P6 : List (ℕ × ℕ) := [(120000, 122346), (122347, 124990), (124991, 128020), (128021, 131436), (131437, 135346), (135347, 139680), (139681, 144670), (144671, 150298), (150299, 156726), (156727, 164190), (164191, 172882), (172883, 182968), (182969, 194706), (194707, 208456), (208457, 224632), (224633, 243972), (243973, 267096), (267097, 294996), (294997, 328578), (328579, 369892), (369893, 421120), (421121, 485062), (485063, 510509)]
private def blocks_P7 : List (ℕ × ℕ) := [(510510, 560088), (560089, 619188), (619189, 691188), (691189, 778902), (778903, 886540), (886541, 1000000)]

/-! ## Module D: Finite range `[1, 1,000,000]` verification and final assembly -/

-- Assume `blocks_data.lean` definitions (`primes349`, `primes1021`, `listedL`, `blocks_*`)
-- are placed right above this section inside `namespace OMA.S_oeis_a067786`.

private def fastPhi (n : ℕ) : ℕ :=
  let (rem, res) := phiFromPrimes primes349 (n, n)
  if rem > 1 then res / rem * (rem - 1) else res

private def isComp31 (q : ℕ) : Bool :=
  decide (q < 2) ||
  ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).any (fun p => decide (p < q) && decide (q % p = 0))

private lemma not_prime_of_isComp31 {q : ℕ} (h : isComp31 q = true) : ¬ q.Prime := by
  intro hp
  unfold isComp31 at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true] at h
  rcases h with hlt | ⟨p, hpmem, hlt, hmod⟩
  · have := hp.two_le; omega
  · have hp2 : 2 ≤ p := by
      have h : ∀ x ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ), 2 ≤ x := by decide
      exact h p hpmem
    have hdvd : p ∣ q := Nat.dvd_of_mod_eq_zero hmod
    rcases hp.eq_one_or_self_of_dvd p hdvd with h1 | hself <;> omega

private def checkCovSweep : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, q, [] => isComp31 q && checkCovSweep fuel (q + 1) []
  | fuel + 1, q, p :: ps =>
    if q == p then checkCovSweep fuel (q + 1) ps
    else isComp31 q && checkCovSweep fuel (q + 1) (p :: ps)

private lemma checkCovSweep_sound : ∀ (fuel q : ℕ) (ps : List ℕ),
    checkCovSweep fuel q ps = true →
    ∀ x, q ≤ x → x < q + fuel → x.Prime → x ∈ ps
  | 0, _, _, _, x, h1, h2, _ => by omega
  | fuel + 1, q, [], hchk, x, h1, h2, hxp => by
    unfold checkCovSweep at hchk
    simp only [Bool.and_eq_true] at hchk
    by_cases hxq : x = q
    · subst hxq; exact absurd hxp (not_prime_of_isComp31 hchk.1)
    · exact checkCovSweep_sound fuel (q + 1) [] hchk.2 x (by omega) (by omega) hxp
  | fuel + 1, q, p :: ps, hchk, x, h1, h2, hxp => by
    unfold checkCovSweep at hchk
    by_cases hqp : (q == p) = true
    · rw [if_pos hqp] at hchk
      have heq : q = p := beq_iff_eq.mp hqp
      by_cases hxq : x = q
      · subst hxq; rw [heq]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (checkCovSweep_sound fuel (q + 1) ps hchk x (by omega) (by omega) hxp)
    · rw [if_neg hqp] at hchk
      simp only [Bool.and_eq_true] at hchk
      by_cases hxq : x = q
      · subst hxq; exact absurd hxp (not_prime_of_isComp31 hchk.1)
      · exact checkCovSweep_sound fuel (q + 1) (p :: ps) hchk.2 x (by omega) (by omega) hxp

set_option maxRecDepth 8192 in
private lemma primes349_ge : ∀ p ∈ primes349, 2 ≤ p ∧ p * (120000 / p + 1) < 2 ^ 25 := by decide

set_option maxRecDepth 8192 in
private lemma primes1021_ge : ∀ p ∈ primes1021, 2 ≤ p ∧ p * (1000000 / p + 1) < 2 ^ 25 := by decide

set_option maxRecDepth 8192 in
private lemma primes349_cov : ∀ q < 350, q.Prime → q ∈ primes349 := by
  have h : checkCovSweep 350 0 primes349 = true := by decide
  intro q hq hp
  exact checkCovSweep_sound 350 0 primes349 h q (Nat.zero_le _) (by omega) hp

set_option maxRecDepth 8192 in
private lemma primes1021_cov : ∀ q < 1022, q.Prime → q ∈ primes1021 := by
  have h : checkCovSweep 1022 0 primes1021 = true := by decide
  intro q hq hp
  exact checkCovSweep_sound 1022 0 primes1021 h q (Nat.zero_le _) (by omega) hp

set_option maxRecDepth 8192 in
private lemma fastPhi_eq_totient {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 120000) :
    fastPhi n = n.totient := by
  have hp : ∀ p ∈ primes349, p.Prime ∧ 0 ≤ p := by decide
  have hpair : primes349.Pairwise (· < ·) := by decide
  have hcov : ∀ q : ℕ, q.Prime → 0 ≤ q → q * q ≤ n → q ∈ primes349 := by
    intro q hqp _ hqsq
    exact primes349_cov q (by nlinarith) hqp
  exact phiFromPrimes_spec primes349 n n 0 hp hcov hpair (by omega) (by omega)
    (by ring) dvd_rfl (fun _ _ _ => Nat.zero_le _)

private lemma pm120k_testBit (i : ℕ) (hi : i ≤ 120000) :
    (primeMaskWith 120000 primes349).testBit i = true ↔ i.Prime := by
  have hcov : ∀ q : ℕ, q.Prime → q * q ≤ 120000 → q ∈ primes349 := by
    intro q hqp hqsq
    exact primes349_cov q (by nlinarith) hqp
  exact primeMaskWith_testBit (by omega) (by norm_num) primes349_ge hcov hi

private lemma pm1M_testBit (i : ℕ) (hi : i ≤ 1000000) :
    (primeMaskWith 1000000 primes1021).testBit i = true ↔ i.Prime := by
  have hcov : ∀ q : ℕ, q.Prime → q * q ≤ 1000000 → q ∈ primes1021 := by
    intro q hqp hqsq
    exact primes1021_cov q (by nlinarith) hqp
  exact primeMaskWith_testBit (by omega) (by norm_num) primes1021_ge hcov hi

private lemma pm120k_piFastD {d B : ℕ} (hd : 2 ^ d < 2 ^ 25) (hBN : B ≤ 120000) (hBd : B + 1 ≤ 2 ^ d) :
    swarPopcount d ((primeMaskWith 120000 primes349) &&& (fastPow2 (B + 1) - 1)) =
      Nat.primeCounting B := by
  have hcov : ∀ q : ℕ, q.Prime → q * q ≤ 120000 → q ∈ primes349 := fun q hqp hqsq =>
    primes349_cov q (by nlinarith) hqp
  exact piFastD_eq_primeCounting hd (by omega) (by norm_num) hBN hBd primes349_ge hcov

private lemma pm1M_piFastD {d B : ℕ} (hd : 2 ^ d < 2 ^ 25) (hBN : B ≤ 1000000) (hBd : B + 1 ≤ 2 ^ d) :
    swarPopcount d ((primeMaskWith 1000000 primes1021) &&& (fastPow2 (B + 1) - 1)) =
      Nat.primeCounting B := by
  have hcov : ∀ q : ℕ, q.Prime → q * q ≤ 1000000 → q ∈ primes1021 := fun q hqp hqsq =>
    primes1021_cov q (by nlinarith) hqp
  exact piFastD_eq_primeCounting hd (by omega) (by norm_num) hBN hBd primes1021_ge hcov

private def verifyCovers : Bool :=
  blocksCover 751 3100 blocks_avoid2 &&
  blocksCover 751 3100 blocks_avoid35 &&
  blocksCover 3101 12200 blocks_avoid3 &&
  blocksCover 3801 12200 blocks_avoid57 &&
  blocksCover 12201 41000 blocks_avoid5 &&
  blocksCover 22001 41000 blocks_avoid711 &&
  blocksCover 41001 72000 blocks_avoid7 &&
  blocksCover 72001 119999 blocks_avoid11 &&
  blocksCover 120000 510509 blocks_P6 &&
  blocksCover 510510 1000000 blocks_P7

private def verifySmallFast : Bool :=
  let pm := primeMaskWith 120000 primes349
  let pm750 := pm &&& (fastPow2 751 - 1)
  let pi750 := swarPopcount 10 (pm &&& (fastPow2 751 - 1))
  let pi3100 := swarPopcount 12 (pm &&& (fastPow2 3101 - 1))
  let pi3800 := swarPopcount 12 (pm &&& (fastPow2 3801 - 1))
  let pi12200 := swarPopcount 14 (pm &&& (fastPow2 12201 - 1))
  let pi22000 := swarPopcount 15 (pm &&& (fastPow2 22001 - 1))
  let pi41000 := swarPopcount 16 (pm &&& (fastPow2 41001 - 1))
  let pi72000 := swarPopcount 17 (pm &&& (fastPow2 72001 - 1))
  listedL.all (fun m => fastPhi m == 2 * swarPopcount 14 (pm &&& (fastPow2 (m + 1) - 1))) &&
  checkLinear pm750 listedL fastPhi 750 1 0 &&
  checkBlocksInc 10 pm 32 77 750 pi750 blocks_avoid2 &&
  checkBlocksInc 10 pm 360 1001 750 pi750 blocks_avoid35 &&
  checkBlocksInc 11 pm 288 1001 3100 pi3100 blocks_avoid3 &&
  checkBlocksInc 11 pm 40 143 3800 pi3800 blocks_avoid57 &&
  checkBlocksInc 13 pm 240 1001 12200 pi12200 blocks_avoid5 &&
  checkBlocksInc 13 pm 256 1105 22000 pi22000 blocks_avoid711 &&
  checkBlocksInc 13 pm 512 2431 41000 pi41000 blocks_avoid7 &&
  checkBlocksInc 13 pm 1536 7735 72000 pi72000 blocks_avoid11 &&
  checkStepRange pm listedL fastPhi 6 751 3800 5 750 pi750 &&
  checkStepRange pm listedL fastPhi 10 751 3100 5 750 pi750 &&
  checkStepRange pm listedL fastPhi 30 3801 22000 25 3800 pi3800 &&
  checkStepRange pm listedL fastPhi 42 3801 12200 15 3800 pi3800 &&
  checkStepRange pm listedL fastPhi 210 22001 72000 55 22000 pi22000 &&
  checkStepRange pm listedL fastPhi 330 22001 41000 25 22000 pi22000 &&
  checkStepRange pm listedL fastPhi 2310 72001 119999 55 72000 pi72000

private def verifyBigFast : Bool :=
  let pm := primeMaskWith 1000000 primes1021
  let pi119999 := swarPopcount 17 (pm &&& (fastPow2 120000 - 1))
  let pi510509 := swarPopcount 19 (pm &&& (fastPow2 510510 - 1))
  checkBlocksInc 16 pm 5760 30030 119999 pi119999 blocks_P6 &&
  checkBlocksInc 17 pm 92160 510510 510509 pi510509 blocks_P7

private lemma h_verifyCovers : verifyCovers = true := by decide

set_option maxRecDepth 8192 in
private lemma h_verifySmallFast : verifySmallFast = true := by decide

set_option maxRecDepth 8192 in
private lemma h_verifyBigFast : verifyBigFast = true := by decide

private lemma mem_listedL_iff (n : ℕ) : n ∈ listedL ↔ n ∈ listed := by
  simp [listedL, listed]

private lemma listed_eq_two_pi {n : ℕ} (hn : n ∈ listed) :
    n.totient = 2 * Nat.primeCounting n := by
  have hmem : n ∈ listedL := (mem_listedL_iff n).mpr hn
  have hsmall := h_verifySmallFast
  unfold verifySmallFast at hsmall
  dsimp only at hsmall
  simp only [Bool.and_eq_true, and_assoc] at hsmall
  have hall : listedL.all (fun m => fastPhi m ==
      2 * swarPopcount 14 (primeMaskWith 120000 primes349 &&& (fastPow2 (m + 1) - 1))) = true :=
    hsmall.1
  have hitem := List.all_eq_true.mp hall n hmem
  have hle : 1 ≤ n ∧ n ≤ 12012 := by
    have h : ∀ m ∈ listedL, 1 ≤ m ∧ m ≤ 12012 := by decide
    exact h n hmem
  rw [fastPhi_eq_totient hle.1 (by omega),
      pm120k_piFastD (by norm_num) (by omega) (by omega)] at hitem
  exact beq_iff_eq.mp hitem

private lemma iff_of_two_pi_lt {n : ℕ} (h : 2 * Nat.primeCounting n < n.totient) :
    n.totient = 2 * Nat.primeCounting n ↔ n ∈ listed :=
  ⟨fun heq => by omega, fun hmem => by have := listed_eq_two_pi hmem; omega⟩

private lemma block_kill {dSlice N pm num den lo hi prev : ℕ} {bs : List (ℕ × ℕ)}
    (hd : 2 ^ dSlice < 2 ^ 25)
    (hpm : ∀ i ≤ N, pm.testBit i = true ↔ i.Prime)
    (hleN : ∀ ab ∈ bs, ab.2 ≤ N)
    (hcov : blocksCover lo hi bs = true)
    (hchk : checkBlocksInc dSlice pm num den prev (Nat.primeCounting prev) bs = true)
    {n : ℕ} (h1 : lo ≤ n) (h2 : n ≤ hi)
    (_hden_pos : 0 < den)
    (hphi : num * n ≤ den * n.totient) :
    2 * Nat.primeCounting n < n.totient := by
  obtain ⟨ab, hab, ha, hb⟩ := blocksCover_sound lo hi bs hcov n h1 h2
  have hgt := checkBlocksInc_sound hd hpm prev (Nat.primeCounting prev) bs rfl hleN hchk ab hab
  have hmono : Nat.primeCounting n ≤ Nat.primeCounting ab.2 := Nat.monotone_primeCounting hb
  have hmul : den * (2 * Nat.primeCounting n) < den * n.totient := by
    have h3 : num * ab.1 ≤ num * n := Nat.mul_le_mul_left num ha
    have h4 : den * (2 * Nat.primeCounting n) ≤ den * 2 * Nat.primeCounting ab.2 := by
      calc den * (2 * Nat.primeCounting n)
        _ = den * 2 * Nat.primeCounting n := by ring
        _ ≤ den * 2 * Nat.primeCounting ab.2 := Nat.mul_le_mul_left _ hmono
    omega
  exact Nat.lt_of_mul_lt_mul_left hmul

/-! ## Avoid-divisibility lower bounds on `n.totient` -/

private lemma totient_avoid_2_small {n : ℕ} (hn : 0 < n) (hlt : n ≤ 12200) (h2 : ¬ 2 ∣ n) :
    32 * n ≤ 77 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 13, p.Prime → p ∉ ({2} : Finset ℕ) → p ∈ ({3,5,7,11} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({3,5,7,11} : Finset ℕ), p = 1155 := by decide
  have hPm : ∏ p ∈ ({3,5,7,11} : Finset ℕ), (p - 1) = 480 := by decide
  have h := totient_lower_avoid (bad := {2}) (good := {3,5,7,11}) (next := 13)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' hnb => hcov p (Finset.mem_range.mpr hlt') hp hnb)
    (by simp [h2]) (by rw [hP]; omega)
  rw [hP, hPm] at h; omega

private lemma totient_avoid_35 {n : ℕ} (hn : 0 < n) (hlt : n ≤ 3100) (h3 : ¬ 3 ∣ n) (h5 : ¬ 5 ∣ n) :
    360 * n ≤ 1001 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 17, p.Prime → p ∉ ({3,5} : Finset ℕ) → p ∈ ({2,7,11,13} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({2,7,11,13} : Finset ℕ), p = 2002 := by decide
  have hPm : ∏ p ∈ ({2,7,11,13} : Finset ℕ), (p - 1) = 720 := by decide
  have h := totient_lower_avoid (bad := {3,5}) (good := {2,7,11,13}) (next := 17)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' hnb => hcov p (Finset.mem_range.mpr hlt') hp hnb)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> assumption) (by rw [hP]; omega)
  rw [hP, hPm] at h; omega

private lemma totient_avoid_3_only {n : ℕ} (hn : 0 < n) (hlt : n ≤ 119999) (h3 : ¬ 3 ∣ n) :
    288 * n ≤ 1001 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 17, p.Prime → p ∉ ({3} : Finset ℕ) → p ∈ ({2,5,7,11,13} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({2,5,7,11,13} : Finset ℕ), p = 10010 := by decide
  have hPm : ∏ p ∈ ({2,5,7,11,13} : Finset ℕ), (p - 1) = 2880 := by decide
  have h := totient_lower_avoid (bad := {3}) (good := {2,5,7,11,13}) (next := 17)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' hnb => hcov p (Finset.mem_range.mpr hlt') hp hnb)
    (by simp [h3]) (by rw [hP]; omega)
  rw [hP, hPm] at h; omega

private lemma totient_avoid_2_mid {n : ℕ} (hn : 0 < n) (hlt : n ≤ 119999) (h2 : ¬ 2 ∣ n) :
    92160 * n ≤ 255255 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 19, p.Prime → p ∉ ({2} : Finset ℕ) → p ∈ ({3,5,7,11,13,17} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({3,5,7,11,13,17} : Finset ℕ), p = 255255 := by decide
  have hPm : ∏ p ∈ ({3,5,7,11,13,17} : Finset ℕ), (p - 1) = 92160 := by decide
  have h := totient_lower_avoid (bad := {2}) (good := {3,5,7,11,13,17}) (next := 19)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' hnb => hcov p (Finset.mem_range.mpr hlt') hp hnb)
    (by simp [h2]) (by rw [hP]; omega)
  rw [hP, hPm] at h; exact h

private lemma totient_avoid_57 {n : ℕ} (hn : 0 < n) (hlt : n ≤ 12200) (h5 : ¬ 5 ∣ n) (h7 : ¬ 7 ∣ n) :
    40 * n ≤ 143 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 17, p.Prime → p ∉ ({5,7} : Finset ℕ) → p ∈ ({2,3,11,13} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({2,3,11,13} : Finset ℕ), p = 858 := by decide
  have hPm : ∏ p ∈ ({2,3,11,13} : Finset ℕ), (p - 1) = 240 := by decide
  have h := totient_lower_avoid (bad := {5,7}) (good := {2,3,11,13}) (next := 17)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' hnb => hcov p (Finset.mem_range.mpr hlt') hp hnb)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> assumption) (by rw [hP]; omega)
  rw [hP, hPm] at h; omega

private lemma totient_avoid_5_only {n : ℕ} (hn : 0 < n) (hlt : n ≤ 72000) (h5 : ¬ 5 ∣ n) :
    240 * n ≤ 1001 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 17, p.Prime → p ∉ ({5} : Finset ℕ) → p ∈ ({2,3,7,11,13} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({2,3,7,11,13} : Finset ℕ), p = 6006 := by decide
  have hPm : ∏ p ∈ ({2,3,7,11,13} : Finset ℕ), (p - 1) = 1440 := by decide
  have h := totient_lower_avoid (bad := {5}) (good := {2,3,7,11,13}) (next := 17)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' hnb => hcov p (Finset.mem_range.mpr hlt') hp hnb)
    (by simp [h5]) (by rw [hP]; omega)
  rw [hP, hPm] at h; omega

private lemma totient_avoid_5_big {n : ℕ} (hn : 0 < n) (hlt : n ≤ 119999) (h5 : ¬ 5 ∣ n) :
    3840 * n ≤ 17017 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 19, p.Prime → p ∉ ({5} : Finset ℕ) → p ∈ ({2,3,7,11,13,17} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({2,3,7,11,13,17} : Finset ℕ), p = 102102 := by decide
  have hPm : ∏ p ∈ ({2,3,7,11,13,17} : Finset ℕ), (p - 1) = 23040 := by decide
  have h := totient_lower_avoid (bad := {5}) (good := {2,3,7,11,13,17}) (next := 19)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' hnb => hcov p (Finset.mem_range.mpr hlt') hp hnb)
    (by simp [h5]) (by rw [hP]; omega)
  rw [hP, hPm] at h; omega

private lemma totient_avoid_711 {n : ℕ} (hn : 0 < n) (hlt : n ≤ 41000) (h7 : ¬ 7 ∣ n) (h11 : ¬ 11 ∣ n) :
    256 * n ≤ 1105 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 19, p.Prime → p ∉ ({7,11} : Finset ℕ) → p ∈ ({2,3,5,13,17} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({2,3,5,13,17} : Finset ℕ), p = 6630 := by decide
  have hPm : ∏ p ∈ ({2,3,5,13,17} : Finset ℕ), (p - 1) = 1536 := by decide
  have h := totient_lower_avoid (bad := {7,11}) (good := {2,3,5,13,17}) (next := 19)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' hnb => hcov p (Finset.mem_range.mpr hlt') hp hnb)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> assumption) (by rw [hP]; omega)
  rw [hP, hPm] at h; omega

private lemma totient_avoid_7_only {n : ℕ} (hn : 0 < n) (hlt : n ≤ 119999) (h7 : ¬ 7 ∣ n) :
    512 * n ≤ 2431 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 19, p.Prime → p ∉ ({7} : Finset ℕ) → p ∈ ({2,3,5,11,13,17} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({2,3,5,11,13,17} : Finset ℕ), p = 72930 := by decide
  have hPm : ∏ p ∈ ({2,3,5,11,13,17} : Finset ℕ), (p - 1) = 15360 := by decide
  have h := totient_lower_avoid (bad := {7}) (good := {2,3,5,11,13,17}) (next := 19)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' hnb => hcov p (Finset.mem_range.mpr hlt') hp hnb)
    (by simp [h7]) (by rw [hP]; omega)
  rw [hP, hPm] at h; omega

private lemma totient_avoid_11_only {n : ℕ} (hn : 0 < n) (hlt : n ≤ 119999) (h11 : ¬ 11 ∣ n) :
    1536 * n ≤ 7735 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 19, p.Prime → p ∉ ({11} : Finset ℕ) → p ∈ ({2,3,5,7,13,17} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({2,3,5,7,13,17} : Finset ℕ), p = 46410 := by decide
  have hPm : ∏ p ∈ ({2,3,5,7,13,17} : Finset ℕ), (p - 1) = 9216 := by decide
  have h := totient_lower_avoid (bad := {11}) (good := {2,3,5,7,13,17}) (next := 19)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' hnb => hcov p (Finset.mem_range.mpr hlt') hp hnb)
    (by simp [h11]) (by rw [hP]; omega)
  rw [hP, hPm] at h; omega

private lemma totient_P6 {n : ℕ} (hn : 0 < n) (hlt : n ≤ 510509) :
    5760 * n ≤ 30030 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 17, p.Prime → p ∈ ({2,3,5,7,11,13} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({2,3,5,7,11,13} : Finset ℕ), p = 30030 := by decide
  have hPm : ∏ p ∈ ({2,3,5,7,11,13} : Finset ℕ), (p - 1) = 5760 := by decide
  have h := totient_lower_avoid (bad := ∅) (good := {2,3,5,7,11,13}) (next := 17)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' _ => hcov p (Finset.mem_range.mpr hlt') hp) (by simp) (by rw [hP]; omega)
  rw [hP, hPm] at h; exact h

private lemma totient_P7 {n : ℕ} (hn : 0 < n) (hlt : n ≤ 1000000) :
    92160 * n ≤ 510510 * n.totient := by
  have hcov : ∀ p ∈ Finset.range 19, p.Prime → p ∈ ({2,3,5,7,11,13,17} : Finset ℕ) := by decide
  have hP : ∏ p ∈ ({2,3,5,7,11,13,17} : Finset ℕ), p = 510510 := by decide
  have hPm : ∏ p ∈ ({2,3,5,7,11,13,17} : Finset ℕ), (p - 1) = 92160 := by decide
  have h := totient_lower_avoid (bad := ∅) (good := {2,3,5,7,11,13,17}) (next := 19)
    hn (by omega) (by decide) (by decide)
    (fun p hp hlt' _ => hcov p (Finset.mem_range.mpr hlt') hp) (by simp) (by rw [hP]; omega)
  rw [hP, hPm] at h; exact h

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
private lemma main_proof (n : ℕ) (hn : 0 < n) :
    n.totient = 2 * Nat.primeCounting n ↔ n ∈ listed := by
  -- Unpack verifyCovers, verifySmallFast, verifyBigFast
  have hC := h_verifyCovers
  unfold verifyCovers at hC
  simp only [Bool.and_eq_true, and_assoc] at hC
  rcases hC with ⟨hc_a2, hc_a35, hc_a3, hc_a57, hc_a5, hc_a711, hc_a7, hc_a11, hc_P6, hc_P7⟩
  by_cases h1M : 1000000 ≤ n
  · exact iff_of_two_pi_lt (phi_gt_two_pi_ge_1M h1M)
  push Not at h1M
  by_cases h120k : 120000 ≤ n
  · have hB := h_verifyBigFast
    unfold verifyBigFast at hB
    dsimp only at hB
    simp only [Bool.and_eq_true] at hB
    have hpi119999 : swarPopcount 17 (primeMaskWith 1000000 primes1021 &&& (fastPow2 120000 - 1)) =
        Nat.primeCounting 119999 := pm1M_piFastD (B := 119999) (by norm_num) (by omega) (by norm_num)
    have hpi510509 : swarPopcount 19 (primeMaskWith 1000000 primes1021 &&& (fastPow2 510510 - 1)) =
        Nat.primeCounting 510509 := pm1M_piFastD (B := 510509) (by norm_num) (by omega) (by norm_num)
    rw [hpi119999, hpi510509] at hB
    by_cases h510k : n ≤ 510509
    · exact iff_of_two_pi_lt (block_kill (by norm_num) pm1M_testBit (by decide)
        hc_P6 hB.1 h120k h510k (by omega) (totient_P6 hn h510k))
    · exact iff_of_two_pi_lt (block_kill (by norm_num) pm1M_testBit (by decide)
        hc_P7 hB.2 (by omega) (by omega) (by omega) (totient_P7 hn (by omega)))
  push Not at h120k
  have hS := h_verifySmallFast
  unfold verifySmallFast at hS
  dsimp only at hS
  simp only [Bool.and_eq_true, and_assoc] at hS
  rcases hS with ⟨_, hs_lin, hs_a2, hs_a35, hs_a3, hs_a57, hs_a5, hs_a711, hs_a7, hs_a11,
    hs_s6, hs_s10, hs_s30, hs_s42, hs_s210, hs_s330, hs_s2310⟩
  have hpi750 : swarPopcount 10 (primeMaskWith 120000 primes349 &&& (fastPow2 751 - 1)) = Nat.primeCounting 750 :=
    pm120k_piFastD (by norm_num) (by omega) (by norm_num)
  have hpi3100 : swarPopcount 12 (primeMaskWith 120000 primes349 &&& (fastPow2 3101 - 1)) = Nat.primeCounting 3100 :=
    pm120k_piFastD (by norm_num) (by omega) (by norm_num)
  have hpi3800 : swarPopcount 12 (primeMaskWith 120000 primes349 &&& (fastPow2 3801 - 1)) = Nat.primeCounting 3800 :=
    pm120k_piFastD (by norm_num) (by omega) (by norm_num)
  have hpi12200 : swarPopcount 14 (primeMaskWith 120000 primes349 &&& (fastPow2 12201 - 1)) = Nat.primeCounting 12200 :=
    pm120k_piFastD (by norm_num) (by omega) (by norm_num)
  have hpi22000 : swarPopcount 15 (primeMaskWith 120000 primes349 &&& (fastPow2 22001 - 1)) = Nat.primeCounting 22000 :=
    pm120k_piFastD (by norm_num) (by omega) (by norm_num)
  have hpi41000 : swarPopcount 16 (primeMaskWith 120000 primes349 &&& (fastPow2 41001 - 1)) = Nat.primeCounting 41000 :=
    pm120k_piFastD (by norm_num) (by omega) (by norm_num)
  have hpi72000 : swarPopcount 17 (primeMaskWith 120000 primes349 &&& (fastPow2 72001 - 1)) = Nat.primeCounting 72000 :=
    pm120k_piFastD (by norm_num) (by omega) (by norm_num)
  -- Regime 0: [1, 750]
  by_cases h750 : n ≤ 750
  · have hpm750 : ∀ i ≤ 750, (primeMaskWith 120000 primes349 &&& (fastPow2 751 - 1)).testBit i = true ↔ i.Prime := by
      intro i hi
      rw [Nat.testBit_and, fastPow2_eq (by norm_num), Nat.testBit_two_pow_sub_one]
      have hlt : i < 751 := by omega
      simp [hlt, pm120k_testBit i (by omega)]
    rw [← mem_listedL_iff]
    exact checkLinear_sound hpm750 (fun m h1 h2 => fastPhi_eq_totient h1 (by omega))
      750 1 0 le_rfl (by omega) (by simp) hs_lin n (by omega) (by omega)
  -- Regime 1: [751, 3100]
  by_cases h3100 : n ≤ 3100
  · by_cases hd2 : 2 ∣ n
    · by_cases hd3 : 3 ∣ n
      · rw [← mem_listedL_iff]
        exact checkStepRange_sound (by omega) (by omega) (by omega) pm120k_testBit
          (fun m h1 h2 => fastPhi_eq_totient h1 h2) 5 750 _ hpi750 hs_s6 n (by omega) (by omega) (by omega)
          (by rw [Nat.dvd_iff_mod_eq_zero] at hd2 hd3 ⊢; omega)
      · by_cases hd5 : 5 ∣ n
        · rw [← mem_listedL_iff]
          exact checkStepRange_sound (by omega) (by omega) (by omega) pm120k_testBit
            (fun m h1 h2 => fastPhi_eq_totient h1 h2) 5 750 _ hpi750 hs_s10 n (by omega) (by omega) (by omega)
            (by rw [Nat.dvd_iff_mod_eq_zero] at hd2 hd5 ⊢; omega)
        · rw [hpi750] at hs_a35
          exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
            hc_a35 hs_a35 (by omega) h3100 (by omega) (totient_avoid_35 hn h3100 hd3 hd5))
    · rw [hpi750] at hs_a2
      exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
        hc_a2 hs_a2 (by omega) h3100 (by omega) (totient_avoid_2_small hn (by omega) hd2))
  -- Regime 2: [3101, 3800]
  by_cases h3800 : n ≤ 3800
  · by_cases hd2 : 2 ∣ n
    · by_cases hd3 : 3 ∣ n
      · rw [← mem_listedL_iff]
        exact checkStepRange_sound (by omega) (by omega) (by omega) pm120k_testBit
          (fun m h1 h2 => fastPhi_eq_totient h1 h2) 5 750 _ hpi750 hs_s6 n (by omega) (by omega) h3800
          (by rw [Nat.dvd_iff_mod_eq_zero] at hd2 hd3 ⊢; omega)
      · rw [hpi3100] at hs_a3
        exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
          hc_a3 hs_a3 (by omega) (by omega) (by omega) (totient_avoid_3_only hn (by omega) hd3))
    · rw [hpi3100] at hs_a3
      have hphi := totient_avoid_2_small hn (by omega) hd2
      exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
        hc_a3 hs_a3 (by omega) (by omega) (by omega) (by omega))
  -- Regime 3: [3801, 12200]
  by_cases h12200 : n ≤ 12200
  · by_cases hd2 : 2 ∣ n
    · by_cases hd3 : 3 ∣ n
      · by_cases hd5 : 5 ∣ n
        · rw [← mem_listedL_iff]
          exact checkStepRange_sound (by omega) (by omega) (by omega) pm120k_testBit
            (fun m h1 h2 => fastPhi_eq_totient h1 h2) 25 3800 _ hpi3800 hs_s30 n (by omega) (by omega) (by omega)
            (by rw [Nat.dvd_iff_mod_eq_zero] at hd2 hd3 hd5 ⊢; omega)
        · by_cases hd7 : 7 ∣ n
          · rw [← mem_listedL_iff]
            exact checkStepRange_sound (by omega) (by omega) (by omega) pm120k_testBit
              (fun m h1 h2 => fastPhi_eq_totient h1 h2) 15 3800 _ hpi3800 hs_s42 n (by omega) (by omega) h12200
              (by rw [Nat.dvd_iff_mod_eq_zero] at hd2 hd3 hd7 ⊢; omega)
          · rw [hpi3800] at hs_a57
            exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
              hc_a57 hs_a57 (by omega) h12200 (by omega) (totient_avoid_57 hn h12200 hd5 hd7))
      · rw [hpi3100] at hs_a3
        exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
          hc_a3 hs_a3 (by omega) h12200 (by omega) (totient_avoid_3_only hn (by omega) hd3))
    · rw [hpi3100] at hs_a3
      have hphi := totient_avoid_2_small hn h12200 hd2
      exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
        hc_a3 hs_a3 (by omega) h12200 (by omega) (by omega))
  -- Regime 4: [12201, 22000]
  by_cases h22000 : n ≤ 22000
  · by_cases hd2 : 2 ∣ n
    · by_cases hd3 : 3 ∣ n
      · by_cases hd5 : 5 ∣ n
        · rw [← mem_listedL_iff]
          exact checkStepRange_sound (by omega) (by omega) (by omega) pm120k_testBit
            (fun m h1 h2 => fastPhi_eq_totient h1 h2) 25 3800 _ hpi3800 hs_s30 n (by omega) (by omega) h22000
            (by rw [Nat.dvd_iff_mod_eq_zero] at hd2 hd3 hd5 ⊢; omega)
        · rw [hpi12200] at hs_a5
          exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
            hc_a5 hs_a5 (by omega) (by omega) (by omega) (totient_avoid_5_only hn (by omega) hd5))
      · rw [hpi12200] at hs_a5
        have hphi := totient_avoid_3_only hn (by omega) hd3
        exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
          hc_a5 hs_a5 (by omega) (by omega) (by omega) (by omega))
    · rw [hpi12200] at hs_a5
      have hphi := totient_avoid_2_mid hn (by omega) hd2
      exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
        hc_a5 hs_a5 (by omega) (by omega) (by omega) (by omega))
  -- Regime 5: [22001, 41000]
  by_cases h41000 : n ≤ 41000
  · by_cases hd2 : 2 ∣ n
    · by_cases hd3 : 3 ∣ n
      · by_cases hd5 : 5 ∣ n
        · by_cases hd7 : 7 ∣ n
          · rw [← mem_listedL_iff]
            exact checkStepRange_sound (by omega) (by omega) (by omega) pm120k_testBit
              (fun m h1 h2 => fastPhi_eq_totient h1 h2) 55 22000 _ hpi22000 hs_s210 n (by omega) (by omega) (by omega)
              (by rw [Nat.dvd_iff_mod_eq_zero] at hd2 hd3 hd5 hd7 ⊢; omega)
          · by_cases hd11 : 11 ∣ n
            · rw [← mem_listedL_iff]
              exact checkStepRange_sound (by omega) (by omega) (by omega) pm120k_testBit
                (fun m h1 h2 => fastPhi_eq_totient h1 h2) 25 22000 _ hpi22000 hs_s330 n (by omega) (by omega) h41000
                (by rw [Nat.dvd_iff_mod_eq_zero] at hd2 hd3 hd5 hd11 ⊢; omega)
            · rw [hpi22000] at hs_a711
              exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
                hc_a711 hs_a711 (by omega) h41000 (by omega) (totient_avoid_711 hn h41000 hd7 hd11))
        · rw [hpi12200] at hs_a5
          exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
            hc_a5 hs_a5 (by omega) h41000 (by omega) (totient_avoid_5_only hn (by omega) hd5))
      · rw [hpi12200] at hs_a5
        have hphi := totient_avoid_3_only hn (by omega) hd3
        exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
          hc_a5 hs_a5 (by omega) h41000 (by omega) (by omega))
    · rw [hpi12200] at hs_a5
      have hphi := totient_avoid_2_mid hn (by omega) hd2
      exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
        hc_a5 hs_a5 (by omega) h41000 (by omega) (by omega))
  -- Regime 6: [41001, 72000]
  by_cases h72000 : n ≤ 72000
  · by_cases hd2 : 2 ∣ n
    · by_cases hd3 : 3 ∣ n
      · by_cases hd5 : 5 ∣ n
        · by_cases hd7 : 7 ∣ n
          · rw [← mem_listedL_iff]
            exact checkStepRange_sound (by omega) (by omega) (by omega) pm120k_testBit
              (fun m h1 h2 => fastPhi_eq_totient h1 h2) 55 22000 _ hpi22000 hs_s210 n (by omega) (by omega) h72000
              (by rw [Nat.dvd_iff_mod_eq_zero] at hd2 hd3 hd5 hd7 ⊢; omega)
          · rw [hpi41000] at hs_a7
            exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
              hc_a7 hs_a7 (by omega) h72000 (by omega) (totient_avoid_7_only hn (by omega) hd7))
        · rw [hpi41000] at hs_a7
          have hphi := totient_avoid_5_only hn h72000 hd5
          exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
            hc_a7 hs_a7 (by omega) h72000 (by omega) (by omega))
      · rw [hpi41000] at hs_a7
        have hphi := totient_avoid_3_only hn (by omega) hd3
        exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
          hc_a7 hs_a7 (by omega) h72000 (by omega) (by omega))
    · rw [hpi41000] at hs_a7
      have hphi := totient_avoid_2_mid hn (by omega) hd2
      exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
        hc_a7 hs_a7 (by omega) h72000 (by omega) (by omega))
  -- Regime 7: [72001, 119999]
  · by_cases hd2 : 2 ∣ n
    · by_cases hd3 : 3 ∣ n
      · by_cases hd5 : 5 ∣ n
        · by_cases hd7 : 7 ∣ n
          · by_cases hd11 : 11 ∣ n
            · rw [← mem_listedL_iff]
              exact checkStepRange_sound (by omega) (by omega) (by omega) pm120k_testBit
                (fun m h1 h2 => fastPhi_eq_totient h1 h2) 55 72000 _ hpi72000 hs_s2310 n (by omega) (by omega) (by omega)
                (by rw [Nat.dvd_iff_mod_eq_zero] at hd2 hd3 hd5 hd7 hd11 ⊢; omega)
            · rw [hpi72000] at hs_a11
              exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
                hc_a11 hs_a11 (by omega) (by omega) (by omega) (totient_avoid_11_only hn (by omega) hd11))
          · rw [hpi72000] at hs_a11
            have hphi := totient_avoid_7_only hn (by omega) hd7
            exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
              hc_a11 hs_a11 (by omega) (by omega) (by omega) (by omega))
        · rw [hpi72000] at hs_a11
          have hphi := totient_avoid_5_big hn (by omega) hd5
          exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
            hc_a11 hs_a11 (by omega) (by omega) (by omega) (by omega))
      · rw [hpi72000] at hs_a11
        have hphi := totient_avoid_3_only hn (by omega) hd3
        exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
          hc_a11 hs_a11 (by omega) (by omega) (by omega) (by omega))
    · rw [hpi72000] at hs_a11
      have hphi := totient_avoid_2_mid hn (by omega) hd2
      exact iff_of_two_pi_lt (block_kill (by norm_num) pm120k_testBit (by decide)
        hc_a11 hs_a11 (by omega) (by omega) (by omega) (by omega))

end Finite

end OMA.S_oeis_a067786

theorem OMA.solution : type_of% @OMA.S_oeis_a067786.main :=
  OMA.S_oeis_a067786.main_proof

