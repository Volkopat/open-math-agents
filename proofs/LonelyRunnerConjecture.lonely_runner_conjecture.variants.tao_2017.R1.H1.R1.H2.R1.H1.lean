import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1_H2_R1

/-!
Proof of `OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1_H2_R1.H1`.

Since `∑ 1 / p` diverges, some finite set `s` of primes has `∑_{p ∈ s} 1 / p > log (2 / ε)`.
For `P = ∏_{p ∈ s} p`, Euler's product gives
`φ(P) / P = ∏_{p ∣ P} (1 - 1 / p) ≤ ∏_{p ∈ s} (1 - 1 / p) ≤ exp (- ∑_{p ∈ s} 1 / p) ≤ ε / 2`.
The integers coprime to `P` fill exactly `φ(P)` places in each block of `P` consecutive
integers, so `[1, A]` contains at most `(A / P + 1) φ(P) ≤ ε A / 2 + P ≤ ε A` of them once
`A ≥ 2 P / ε`.
-/

open Finset

namespace OMAProof.CoprimeDensity

/-- Coprime residues in `m` full blocks. -/
theorem card_blocks (P m : ℕ) :
    #{x ∈ Ico 1 (1 + P * m) | P.Coprime x} = m * Nat.totient P := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : Ico 1 (1 + P * (m + 1)) = Ico 1 (1 + P * m) ∪ Ico (1 + P * m) (1 + P * m + P) := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by nlinarith)]
      congr 1
      ring
    have hdisj : Disjoint (Ico 1 (1 + P * m)) (Ico (1 + P * m) (1 + P * m + P)) :=
      Finset.Ico_disjoint_Ico_consecutive _ _ _
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), ih, Nat.filter_coprime_Ico_eq_totient]
    ring

/-- A finite set of primes with large reciprocal sum. -/
theorem exists_primes (L : ℝ) : ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime) ∧ L < ∑ p ∈ s, (1 : ℝ) / p := by
  by_contra hno
  push Not at hno
  apply not_summable_one_div_on_primes
  apply summable_of_sum_le (c := L)
  · intro n
    exact Set.indicator_nonneg (fun m _ => by positivity) n
  · intro t
    have h := hno (t.filter Nat.Prime) (fun p hp => (Finset.mem_filter.mp hp).2)
    calc ∑ n ∈ t, Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n
        = ∑ n ∈ t.filter Nat.Prime, (1 : ℝ) / n := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun n _ => ?_
          by_cases hn : n.Prime
          · simp [Set.indicator_of_mem (show n ∈ {p | p.Prime} from hn), hn]
          · simp [Set.indicator_of_notMem (show n ∉ {p | p.Prime} from hn), hn]
      _ ≤ L := h

end OMAProof.CoprimeDensity

open OMAProof.CoprimeDensity in
theorem OMA.solution :
    OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1_H2_R1.H1 := by
  intro ε hε
  obtain ⟨s, hsp, hsum⟩ := exists_primes (Real.log (2 / ε))
  set P := ∏ p ∈ s, p with hP
  have hP0 : 0 < P := Finset.prod_pos fun p hp => (hsp p hp).pos
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP0
  -- `φ(P) ≤ (ε / 2) P`
  have hsub : s ⊆ P.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hsp p hp, Finset.dvd_prod_of_mem _ hp, hP0.ne'⟩
  have hf01 : ∀ p ∈ P.primeFactors, 0 ≤ 1 - (p : ℝ)⁻¹ ∧ 1 - (p : ℝ)⁻¹ ≤ 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    constructor
    · have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      linarith
    · have : 0 ≤ (p : ℝ)⁻¹ := by positivity
      linarith
  have hphi : (Nat.totient P : ℝ) = P * ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors P)
    push_cast at h
    exact h
  have hprod_sub : ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹) ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
    rw [← Finset.prod_sdiff hsub]
    have hle : ∏ p ∈ P.primeFactors \ s, (1 - (p : ℝ)⁻¹) ≤ 1 :=
      Finset.prod_le_one (fun p hp => (hf01 p (Finset.mem_sdiff.mp hp).1).1)
        (fun p hp => (hf01 p (Finset.mem_sdiff.mp hp).1).2)
    have hnn : 0 ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) :=
      Finset.prod_nonneg fun p hp => (hf01 p (hsub hp)).1
    nlinarith
  have hprod_exp : ∏ p ∈ s, (1 - (p : ℝ)⁻¹) ≤ Real.exp (-∑ p ∈ s, (1 : ℝ) / p) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod (fun p hp => (hf01 p (hsub hp)).1)
    intro p _
    have := Real.add_one_le_exp (-(1 / (p : ℝ)))
    rw [one_div] at this ⊢
    linarith
  have hexp : Real.exp (-∑ p ∈ s, (1 : ℝ) / p) ≤ ε / 2 := by
    have h1 : Real.exp (-∑ p ∈ s, (1 : ℝ) / p) ≤ Real.exp (-Real.log (2 / ε)) :=
      Real.exp_le_exp.mpr (by linarith)
    have e : Real.exp (-Real.log (2 / ε)) = ε / 2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    rw [e] at h1
    exact h1
  have hphiP : (Nat.totient P : ℝ) ≤ ε / 2 * P := by
    rw [hphi]
    have := hprod_sub.trans (hprod_exp.trans hexp)
    nlinarith
  -- counting
  refine ⟨P, ⌈2 * P / ε⌉₊, hP0, fun A hA => ?_⟩
  have hAR : 2 * (P : ℝ) / ε ≤ A := (Nat.ceil_le).mp hA
  have hcover : Icc 1 A ⊆ Ico 1 (1 + P * (A / P + 1)) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_Ico]
    have := Nat.lt_mul_div_succ A hP0
    constructor <;> omega
  have hcount : #{x ∈ Icc 1 A | P.Coprime x} ≤ (A / P + 1) * Nat.totient P := by
    rw [← card_blocks P (A / P + 1)]
    exact Finset.card_le_card (Finset.filter_subset_filter _ hcover)
  have hdivR : ((A / P : ℕ) : ℝ) ≤ (A : ℝ) / P := Nat.cast_div_le
  have htot_le : (Nat.totient P : ℝ) ≤ P := by exact_mod_cast Nat.totient_le P
  have hPA : (P : ℝ) ≤ ε / 2 * A := by
    rw [div_le_iff₀ hε] at hAR
    linarith
  calc ((#{x ∈ Icc 1 A | P.Coprime x} : ℕ) : ℝ)
      ≤ (((A / P + 1) * Nat.totient P : ℕ) : ℝ) := by exact_mod_cast hcount
    _ = ((A / P : ℕ) : ℝ) * Nat.totient P + Nat.totient P := by push_cast; ring
    _ ≤ (A : ℝ) / P * (ε / 2 * P) + P := by
        have h1 := mul_le_mul hdivR hphiP (Nat.cast_nonneg _) (by positivity)
        linarith [htot_le]
    _ = ε / 2 * A + P := by field_simp
    _ ≤ ε * A := by linarith
