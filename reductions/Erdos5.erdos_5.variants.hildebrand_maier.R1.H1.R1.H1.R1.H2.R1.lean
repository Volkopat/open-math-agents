import OMAReductions.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R1
import Mathlib

/-! Adapted from OpenAI, openai/math 3344da59991ed94f9ba711217b29c1d760badfa6,
Apache-2.0, OAI.NumberTheory.PrimeGaps. Separate the variational small-marked-ratio
construction, the detector-moment estimate for dyadic starts, and the counting
argument taking a prime in the first block and a prime-free second block to a gap. -/
namespace OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R1_H2_R1
open Filter MeasureTheory
open scoped Classical ContDiff Topology

def H1 : Prop :=
  ∀ lam τ ε : ℝ, 0 < lam → 0 < τ → 0 < ε →
    ∃ k : ℕ, ∃ f : (j : ℕ) → (Fin j → ℝ) → ℝ,
      (0 < k ∧ (∀ j ≤ k, ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
        tsupport (f j) ⊆ {t | (∀ i, 0 < t i) ∧ ∑ i, t i < τ} ∧
        ∀ (e : Equiv.Perm (Fin j)) (t : Fin j → ℝ), f j (t ∘ e) = f j t) ∧
        (∀ j, k < j → f j = 0)) ∧ f 0 = 0 ∧
      let mass := fun (j : ℕ) (g : (Fin j → ℝ) → ℝ) => ∫ t, (g t)^2
      let α := fun j : ℕ => lam^j / j.factorial
      let w := ∑ j ∈ Finset.range (k+1), α j * mass j (f j)
      0 < w ∧ (lam * ∑ j ∈ Finset.range (k+1), α j *
        mass j (fun t => f j t + ∫ u : ℝ, f (j+1) (Fin.snoc t u))) / w ≤ ε

def H2 : Prop :=
  (∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → (∑ q ∈ Finset.Icc 1 ⌊x ^ (1/2:ℝ) * Real.log x ^ (-b)⌋₊,
      (((Finset.range q).sup fun c => if Nat.Coprime c q then
        NNReal.mk |(∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n % q = c),
          ArithmeticFunction.vonMangoldt n) - x / q.totient| (abs_nonneg _) else 0 : NNReal) : ℝ))
      ≤ M * x * Real.log x ^ (-A)) →
  (∀ lam τ ε : ℝ, 0 < lam → 0 < τ → 0 < ε →
    ∃ k : ℕ, ∃ f : (j : ℕ) → (Fin j → ℝ) → ℝ,
      (0 < k ∧ (∀ j ≤ k, ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
        tsupport (f j) ⊆ {t | (∀ i, 0 < t i) ∧ ∑ i, t i < τ} ∧
        ∀ (e : Equiv.Perm (Fin j)) (t : Fin j → ℝ), f j (t ∘ e) = f j t) ∧
        (∀ j, k < j → f j = 0)) ∧ f 0 = 0 ∧
      let mass := fun (j : ℕ) (g : (Fin j → ℝ) → ℝ) => ∫ t, (g t)^2
      let α := fun j : ℕ => lam^j / j.factorial
      let w := ∑ j ∈ Finset.range (k+1), α j * mass j (f j)
      0 < w ∧ (lam * ∑ j ∈ Finset.range (k+1), α j *
        mass j (fun t => f j t + ∫ u : ℝ, f (j+1) (Fin.snoc t u))) / w ≤ ε) →
  ∀ C : ℝ, 0 < C → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop,
      let h := ⌊(C+1)*Real.log X⌋₊
      δ * X ≤ (((Finset.Ioc X (2*X)).filter fun m =>
        (∃ p, Nat.Prime p ∧ m < p ∧ p ≤ m+h) ∧
        ∀ q, m+h < q → q ≤ m+2*h → ¬ Nat.Prime q).card : ℝ)

def H3 : Prop :=
  (∀ C : ℝ, 0 < C → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop,
      let h := ⌊(C+1)*Real.log X⌋₊
      δ * X ≤ (((Finset.Ioc X (2*X)).filter fun m =>
        (∃ p, Nat.Prime p ∧ m < p ∧ p ≤ m+h) ∧
        ∀ q, m+h < q → q ≤ m+2*h → ¬ Nat.Prime q).card : ℝ)) →
  ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.Icc 1 N).filter fun n => C * Real.log (Nat.nth Nat.Prime (n - 1)) <
        (Nat.nth Nat.Prime n : ℝ) - (Nat.nth Nat.Prime (n - 1) : ℝ)).card : ℝ)

theorem main : H1 → H2 → H3 → OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R1.H2 := by
  intro profiles sieve count bv
  exact count (sieve bv profiles)

end OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R1_H2_R1
