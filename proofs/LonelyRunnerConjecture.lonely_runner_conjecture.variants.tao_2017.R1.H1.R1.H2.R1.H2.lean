import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1_H2_R1
import Mathlib

/-!
Proof of hypothesis H2 (bounded smooth part outside a small exceptional set).

Fix `P > 0` and `ε > 0`, let `ω` be the number of prime factors of `P`, and choose `K`
with `ω / ε < 2 ^ K`. Take `S = P ^ K`, `s a = gcd a (P ^ K)` and `r a = a / s a`.
If a prime `p ∣ P` divides `r a`, then `p` does not divide `P ^ K / s a` (the two quotients
by the gcd are coprime), so `p ^ K ∣ s a` and hence `p ^ (K + 1) ∣ a`.
So `r a` is coprime to `P` for every `a` in
`G = {a ∈ [1, A] : no prime p ∣ P has p ^ (K + 1) ∣ a}`.
The complement of `G` in `[1, A]` lies in the union over `p ∣ P` of the multiples of
`p ^ (K + 1)`, so it has at most `ω * (A / 2 ^ (K + 1)) ≤ ε * A` elements.
-/

open Finset

namespace OMAProof.SmoothPart

/-- A prime factor of `P` dividing `a / gcd a (P ^ K)` divides `a` to a power above `K`. -/
theorem pow_dvd_of_dvd_div_gcd {P K a p : ℕ} (ha : 0 < a) (hpP : p ∣ P)
    (hpa : p ∣ a / Nat.gcd a (P ^ K)) : p ^ (K + 1) ∣ a := by
  have hg : 0 < Nat.gcd a (P ^ K) := Nat.gcd_pos_of_pos_left _ ha
  have cop : Nat.Coprime (a / Nat.gcd a (P ^ K)) (P ^ K / Nat.gcd a (P ^ K)) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hc : Nat.Coprime p (P ^ K / Nat.gcd a (P ^ K)) := Nat.Coprime.coprime_dvd_left hpa cop
  have hpk : p ^ K ∣ Nat.gcd a (P ^ K) * (P ^ K / Nat.gcd a (P ^ K)) := by
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right a (P ^ K))]
    exact pow_dvd_pow_of_dvd hpP K
  have hpg : p ^ K ∣ Nat.gcd a (P ^ K) :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left K hc) hpk
  have h : p ^ K * p ∣ Nat.gcd a (P ^ K) * (a / Nat.gcd a (P ^ K)) := Nat.mul_dvd_mul hpg hpa
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a (P ^ K))] at h
  have e : p ^ (K + 1) = p ^ K * p := pow_succ p K
  rw [e]
  exact h

/-- At most `A / d` multiples of `d` lie in `[1, A]`. -/
theorem card_multiples_le (A d : ℕ) : ((Icc 1 A).filter (fun a => d ∣ a)).card ≤ A / d := by
  refine le_of_le_of_eq (card_le_card ?_) (Nat.Ioc_filter_dvd_card_eq_div A d)
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
  obtain ⟨h1, h2⟩ := mem_Icc.mp hx1
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.lt_of_lt_of_le Nat.zero_lt_one h1, h2⟩, hx2⟩

/-- The exceptional set is small. -/
theorem card_bad_le (P K A : ℕ) :
    (Icc 1 A \ (Icc 1 A).filter (fun a => ∀ p ∈ P.primeFactors, ¬ p ^ (K + 1) ∣ a)).card ≤
      P.primeFactors.card * (A / 2 ^ (K + 1)) := by
  have hsub : Icc 1 A \ (Icc 1 A).filter (fun a => ∀ p ∈ P.primeFactors, ¬ p ^ (K + 1) ∣ a) ⊆
      P.primeFactors.biUnion (fun p => (Icc 1 A).filter (fun a => p ^ (K + 1) ∣ a)) := by
    intro x hx
    obtain ⟨h1, h2⟩ := mem_sdiff.mp hx
    by_contra hne
    exact h2 (mem_filter.mpr ⟨h1, fun p hp hd =>
      hne (mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨h1, hd⟩⟩)⟩)
  have hbi : (P.primeFactors.biUnion
      (fun p => (Icc 1 A).filter (fun a => p ^ (K + 1) ∣ a))).card ≤
      P.primeFactors.card * (A / 2 ^ (K + 1)) := by
    apply card_biUnion_le_card_mul
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have h2 : A / p ^ (K + 1) ≤ A / 2 ^ (K + 1) :=
      Nat.div_le_div_left (Nat.pow_le_pow_left hp2 (K + 1)) (by positivity)
    exact (card_multiples_le A (p ^ (K + 1))).trans h2
  exact (card_le_card hsub).trans hbi

theorem real_bound (q A T ε : ℝ) (hT : 0 < T) (hA : 0 ≤ A) (h : q ≤ ε * T) :
    q * (A / T) ≤ ε * A := by
  have h1 : q * (A / T) = q * A / T := by ring
  rw [h1, div_le_iff₀ hT]
  nlinarith [mul_le_mul_of_nonneg_right h hA]

end OMAProof.SmoothPart

theorem OMA.solution : OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1_H2_R1.H2 := by
  intro P hP ε hε
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((P.primeFactors.card : ℝ) / ε)
    (one_lt_two : (1 : ℝ) < 2)
  have hq : (P.primeFactors.card : ℝ) ≤ ε * ((2 ^ (K + 1) : ℕ) : ℝ) := by
    have h1 : (P.primeFactors.card : ℝ) < 2 ^ K * ε := (div_lt_iff₀ hε).mp hK
    have h2 : ((2 ^ (K + 1) : ℕ) : ℝ) = 2 ^ K * 2 := by
      push_cast
      ring
    have h3 : (0 : ℝ) < 2 ^ K := by positivity
    rw [h2]
    nlinarith [mul_pos h3 hε]
  refine ⟨P ^ K, pow_pos hP K, fun A => ?_⟩
  refine ⟨(Icc 1 A).filter (fun a => ∀ p ∈ P.primeFactors, ¬ p ^ (K + 1) ∣ a),
    filter_subset _ _, fun a => Nat.gcd a (P ^ K), fun a => a / Nat.gcd a (P ^ K), ?_, ?_⟩
  · intro a ha
    obtain ⟨haI, hgood⟩ := mem_filter.mp ha
    obtain ⟨ha1, haA⟩ := mem_Icc.mp haI
    have hapos : 0 < a := Nat.lt_of_lt_of_le Nat.zero_lt_one ha1
    have hg : 0 < Nat.gcd a (P ^ K) := Nat.gcd_pos_of_pos_left _ hapos
    have hga : Nat.gcd a (P ^ K) ∣ a := Nat.gcd_dvd_left a (P ^ K)
    have hr0 : 0 < a / Nat.gcd a (P ^ K) := Nat.div_pos (Nat.le_of_dvd hapos hga) hg
    have hr1 : 1 ≤ a / Nat.gcd a (P ^ K) := hr0
    have hrA : a / Nat.gcd a (P ^ K) ≤ A := (Nat.div_le_self _ _).trans haA
    refine ⟨(Nat.mul_div_cancel' hga).symm, hg,
      Nat.le_of_dvd (pow_pos hP K) (Nat.gcd_dvd_right a (P ^ K)),
      mem_Icc.mpr ⟨hr1, hrA⟩, ?_⟩
    by_contra hnc
    obtain ⟨p, hp, hpP, hpa⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    exact hgood p (Nat.mem_primeFactors.mpr ⟨hp, hpP, hP.ne'⟩)
      (OMAProof.SmoothPart.pow_dvd_of_dvd_div_gcd hapos hpP hpa)
  · have hT : (0 : ℝ) < ((2 ^ (K + 1) : ℕ) : ℝ) := by positivity
    have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    have hdiv : ((A / 2 ^ (K + 1) : ℕ) : ℝ) ≤ (A : ℝ) / ((2 ^ (K + 1) : ℕ) : ℝ) :=
      Nat.cast_div_le
    have hrest : ((P.primeFactors.card * (A / 2 ^ (K + 1)) : ℕ) : ℝ) ≤ ε * A := by
      rw [Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)).trans
        (OMAProof.SmoothPart.real_bound _ _ _ _ hT hA0 hq)
    exact (Nat.cast_le.mpr (OMAProof.SmoothPart.card_bad_le P K A)).trans hrest
