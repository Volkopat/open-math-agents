import FormalConjectures.ErdosProblems.«67»

-- Tao, The Erdős discrepancy problem, arXiv 1509.05363, Section 2 and Theorem 1.8.
-- An assignment z of unit phases determines a completely multiplicative function
-- on the positive integers by its prime factors. Only prime coordinates of z are used.

namespace OMA.R_Erdos67_erdos_67_variants_complex_R1

open MeasureTheory

/-- The finite Fourier step. The bound is independent of the horizon N,
although the probability law may depend on N. -/
def H1 : Prop :=
  ∀ (f : ℕ → Metric.sphere (0 : ℂ) 1) (C : ℝ), 0 < C →
    (∀ d ≥ 1, ∀ m ≥ 1, ‖∑ k ∈ Finset.Icc 1 m, (f (k * d)).1‖ ≤ C) →
    ∃ B : ℝ, ∀ N : ℕ, ∃ μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1),
      ∀ n ≤ N, (∫ z : (ℕ → Metric.sphere (0 : ℂ) 1), ‖∑ j ∈ Finset.Icc 1 n,
        ∏ p ∈ j.primeFactors, (z p).1 ^ j.factorization p‖ ^ 2 ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))) ≤ B

/-- The stochastic discrepancy theorem for completely multiplicative functions,
with the probability law expressed in prime coordinates. -/
def H2 : Prop :=
  ∀ (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)) (B : ℝ), ∃ n : ℕ,
    B < ∫ z : (ℕ → Metric.sphere (0 : ℂ) 1), ‖∑ j ∈ Finset.Icc 1 n,
      ∏ p ∈ j.primeFactors, (z p).1 ^ j.factorization p‖ ^ 2 ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))

/-- Closed moment constraints that can be met up to each finite horizon can
all be met by the same point of a compact space. -/
lemma exists_uniform_law {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (M : ℕ → X → ℝ) (hc : ∀ n, Continuous (M n)) (B : ℝ)
    (h : ∀ N : ℕ, ∃ x : X, ∀ n ≤ N, M n x ≤ B) :
    ∃ x : X, ∀ n, M n x ≤ B := by
  let F (N : ℕ) : Set X := ⋂ n, ⋂ (_ : n ≤ N), {x | M n x ≤ B}
  have memF (x : X) (N : ℕ) : x ∈ F N ↔ ∀ n ≤ N, M n x ≤ B := by simp [F]
  have closedF (N : ℕ) : IsClosed (F N) :=
    isClosed_iInter fun n => isClosed_iInter fun _ => isClosed_le (hc n) continuous_const
  have nonemptyF (N : ℕ) : (F N).Nonempty := by
    obtain ⟨x, hx⟩ := h N
    exact ⟨x, (memF x N).2 hx⟩
  have decreasing (N : ℕ) : F (N + 1) ⊆ F N := by
    intro x hx
    exact (memF x N).2 fun n hn => (memF x (N + 1)).1 hx n (Nat.le_succ_of_le hn)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    F decreasing nonemptyF (closedF 0).isCompact closedF
  exact ⟨x, fun n => (memF x n).1 (Set.mem_iInter.mp hx n) n le_rfl⟩

theorem main : H1 → H2 → type_of% @Erdos67.erdos_67.variants.complex := by
  intro hFourier hDivergence f C hC
  by_contra h
  have bound (d : ℕ) (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) :
      ‖∑ k ∈ Finset.Icc 1 m, (f (k * d)).1‖ ≤ C :=
    le_of_not_gt fun hlt => h ⟨d, hd, m, hm, hlt⟩
  obtain ⟨B, hB⟩ := hFourier f C hC bound
  let energy (n : ℕ) : C(ℕ → Metric.sphere (0 : ℂ) 1, ℝ) :=
    ⟨fun z => ‖∑ j ∈ Finset.Icc 1 n,
      ∏ p ∈ j.primeFactors, (z p).1 ^ j.factorization p‖ ^ 2, by fun_prop⟩
  let M (n : ℕ) (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
    ∫ z : (ℕ → Metric.sphere (0 : ℂ) 1), energy n z ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))
  have cont (n : ℕ) : Continuous (M n) :=
    ProbabilityMeasure.continuous_integral_continuousMap (energy n)
  obtain ⟨μ, hμ⟩ := exists_uniform_law M cont B hB
  obtain ⟨n, hn⟩ := hDivergence μ B
  exact (not_lt_of_ge (hμ n)) hn

end OMA.R_Erdos67_erdos_67_variants_complex_R1
