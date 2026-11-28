import OMAReductions.R_RiemannHypothesis_robin_criterion_rhs_R1
import Mathlib

/-!
# Finite witness certificate for Robin's criterion (step H1 of robin_criterion_rhs.R1)

We prove `∀ n : ℕ, n ≠ 0 → n ≤ 5040 → (σ 1 n * 55440)^28 * 55440 < (σ 1 55440 * n)^28 * n`.
We define a fast prime-factorization divisor-sum evaluator `sigmaF`, prove `sigmaF n = σ 1 n`
for all `n ≠ 0`, and check all `1 ≤ n ≤ 5040` in the kernel via `decide +kernel`, using the
shortcut `5 * σ(n) ≤ 14 * n` for the vast majority of integers.
-/

namespace RobinRhsH1

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

private def splitPow (p n : ℕ) : ℕ × ℕ :=
  if h : 2 ≤ p ∧ p ∣ n ∧ 0 < n then
    let r := splitPow p (n / p)
    (r.1, 1 + p * r.2)
  else (n, 1)
termination_by n
decreasing_by exact Nat.div_lt_self h.2.2 h.1

private lemma splitPow_spec {p : ℕ} (hp : p.Prime) :
    ∀ n : ℕ, 0 < n →
      ∃ k : ℕ, n = p ^ k * (splitPow p n).1 ∧ ¬ p ∣ (splitPow p n).1 ∧
        (splitPow p n).2 = σ 1 (p ^ k) ∧ 0 < (splitPow p n).1 ∧ (splitPow p n).1 ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [splitPow]
    by_cases hdiv : p ∣ n
    · have hcond : 2 ≤ p ∧ p ∣ n ∧ 0 < n := ⟨hp.two_le, hdiv, hn⟩
      rw [dif_pos hcond]
      have hlt : n / p < n := Nat.div_lt_self hn hp.two_le
      have hdiv_pos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hdiv) hp.pos
      obtain ⟨k, hmul, hndiv, hsig, hpos1, hle1⟩ := ih (n / p) hlt hdiv_pos
      refine ⟨k + 1, ?_, hndiv, ?_, hpos1, hle1.trans (Nat.div_le_self n p)⟩
      · dsimp only
        have hnp : p * (n / p) = n := Nat.mul_div_cancel' hdiv
        calc n = p * (n / p) := hnp.symm
          _ = p * (p ^ k * (splitPow p (n / p)).1) := congrArg (p * ·) hmul
          _ = p ^ (k + 1) * (splitPow p (n / p)).1 := by rw [pow_succ']; ring
      · dsimp only
        rw [hsig, ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply,
          Nat.divisors_prime_pow hp, Nat.divisors_prime_pow hp,
          Finset.sum_map, Finset.sum_map]
        simp only [Function.Embedding.coeFn_mk]
        conv_rhs => rw [Finset.sum_range_succ', pow_zero, add_comm]
        rw [Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_succ']
    · have hcond : ¬ (2 ≤ p ∧ p ∣ n ∧ 0 < n) := fun h => hdiv h.2.1
      rw [dif_neg hcond]
      exact ⟨0, by simp, hdiv, by simp, hn, le_rfl⟩

private def sigmaF (n : ℕ) : ℕ :=
  if _hn : n ≤ 1 then n
  else
    let p := n.minFac
    let r := splitPow p n
    r.2 * sigmaF r.1
termination_by n
decreasing_by
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hdiv : n.minFac ∣ n := Nat.minFac_dvd n
  rw [splitPow, dif_pos ⟨hp.two_le, hdiv, by omega⟩]
  dsimp only
  have hpos : 0 < n / n.minFac := Nat.div_pos (Nat.le_of_dvd (by omega) hdiv) hp.pos
  have hle := (splitPow_spec hp (n / n.minFac) hpos).choose_spec.2.2.2.2
  exact lt_of_le_of_lt hle (Nat.div_lt_self (by omega) hp.two_le)

private lemma sigmaF_eq_sigma : ∀ n : ℕ, 0 < n → sigmaF n = σ 1 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [sigmaF]
    by_cases hle1 : n ≤ 1
    · have hn1 : n = 1 := by omega
      subst hn1
      simp
    · rw [dif_neg hle1]
      dsimp only
      have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hdiv : n.minFac ∣ n := Nat.minFac_dvd n
      obtain ⟨k, hmul, hndiv, hsig, hpos1, _⟩ := splitPow_spec hp n hn
      have hlt : (splitPow n.minFac n).1 < n := by
        have hpos_div : 0 < n / n.minFac := Nat.div_pos (Nat.le_of_dvd hn hdiv) hp.pos
        have hle := (splitPow_spec hp (n / n.minFac) hpos_div).choose_spec.2.2.2.2
        have heq1 : (splitPow n.minFac n).1 = (splitPow n.minFac (n / n.minFac)).1 := by
          conv_lhs => rw [splitPow, dif_pos ⟨hp.two_le, hdiv, hn⟩]
        rw [heq1]
        exact lt_of_le_of_lt hle (Nat.div_lt_self hn hp.two_le)
      rw [ih _ hlt hpos1, hsig]
      have hcop : Nat.Coprime (n.minFac ^ k) (splitPow n.minFac n).1 :=
        (hp.coprime_iff_not_dvd.mpr hndiv).pow_left k
      rw [← (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop, ← hmul]

private lemma sigma_55440 : σ 1 55440 = 232128 := by
  rw [← sigmaF_eq_sigma 55440 (by omega)]
  decide +kernel

private def okH1 (n : ℕ) : Bool :=
  let s := sigmaF n
  decide (5 * s ≤ 14 * n) || decide ((s * 55440) ^ 28 * 55440 < (232128 * n) ^ 28 * n)

private def checkRange (lo len : ℕ) : Bool :=
  match len with
  | 0 => true
  | 1 => okH1 lo
  | n + 2 =>
    let half := (n + 2) / 2
    checkRange lo half && checkRange (lo + half) (n + 2 - half)
termination_by len
decreasing_by all_goals omega

private lemma checkRange_spec : ∀ (len lo : ℕ), checkRange lo len = true →
    ∀ n : ℕ, lo ≤ n → n < lo + len → okH1 n = true := by
  intro len
  induction len using Nat.strong_induction_on with
  | h len ih =>
    intro lo hk n hlo hhi
    match len with
    | 0 => omega
    | 1 =>
      have : n = lo := by omega
      subst this
      simpa [checkRange] using hk
    | m + 2 =>
      rw [checkRange] at hk
      simp only [Bool.and_eq_true] at hk
      by_cases hmid : n < lo + (m + 2) / 2
      · exact ih ((m + 2) / 2) (by omega) lo hk.1 n hlo hmid
      · exact ih (m + 2 - (m + 2) / 2) (by omega) (lo + (m + 2) / 2) hk.2 n (by omega) (by omega)

private lemma checkRange_5040 : checkRange 1 5040 = true := by
  decide +kernel

private lemma shortcut_bound {n s : ℕ} (hn : 0 < n) (hs : 5 * s ≤ 14 * n) :
    (s * 55440) ^ 28 * 55440 < (232128 * n) ^ 28 * n := by
  have hconst : (14 * 55440 : ℕ) ^ 28 * 55440 < (232128 * 5 : ℕ) ^ 28 := by decide +kernel
  have h1 : (5 * (s * 55440)) ^ 28 ≤ (14 * 55440 * n) ^ 28 := by
    apply Nat.pow_le_pow_left
    have := Nat.mul_le_mul_right 55440 hs
    linarith
  have h2 : 5 ^ 28 * ((s * 55440) ^ 28 * 55440) ≤ (14 * 55440) ^ 28 * 55440 * n ^ 28 := by
    have heq1 : (5 * (s * 55440)) ^ 28 = 5 ^ 28 * (s * 55440) ^ 28 := Nat.mul_pow _ _ _
    have heq2 : (14 * 55440 * n) ^ 28 = (14 * 55440) ^ 28 * n ^ 28 := Nat.mul_pow _ _ _
    rw [heq1, heq2] at h1
    have := Nat.mul_le_mul_right 55440 h1
    linarith
  have h3 : (14 * 55440) ^ 28 * 55440 * n ^ 28 < (232128 * 5) ^ 28 * n ^ 28 :=
    Nat.mul_lt_mul_of_pos_right hconst (Nat.pow_pos hn)
  have h4 : (232128 * 5) ^ 28 * n ^ 28 ≤ 5 ^ 28 * ((232128 * n) ^ 28 * n) := by
    have heq : (232128 * 5) ^ 28 * n ^ 28 = 5 ^ 28 * (232128 * n) ^ 28 := by
      rw [Nat.mul_pow, Nat.mul_pow]; ring
    rw [heq]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hn)
  have hlt : 5 ^ 28 * ((s * 55440) ^ 28 * 55440) < 5 ^ 28 * ((232128 * n) ^ 28 * n) :=
    lt_of_le_of_lt h2 (lt_of_lt_of_le h3 h4)
  exact Nat.lt_of_mul_lt_mul_left hlt

end RobinRhsH1

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.H1 := by
  intro n hn hle
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  rw [RobinRhsH1.sigma_55440, ← RobinRhsH1.sigmaF_eq_sigma n hn_pos]
  have hok := RobinRhsH1.checkRange_spec 5040 1 RobinRhsH1.checkRange_5040 n hn_pos (by omega)
  simp only [RobinRhsH1.okH1, Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with hfast | hexact
  · exact RobinRhsH1.shortcut_bound hn_pos hfast
  · exact hexact
