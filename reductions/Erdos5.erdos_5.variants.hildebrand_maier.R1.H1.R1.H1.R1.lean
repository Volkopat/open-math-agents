import OMAReductions.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1
import Mathlib

/-! Positive density of large prime gaps from Bombieri–Vinogradov (Maier's matrix method
via the detector-weight argument). Adapted from OpenAI, openai/math
3344da59991ed94f9ba711217b29c1d760badfa6, `OAI.LargePrimeGaps.main`,
`OAI.LargePrimeGaps.bombieriVinogradov` and `index_density_of_bombieriVinogradov`
(Apache-2.0). H1 is the Bombieri–Vinogradov theorem with level x^(1/2)(log x)^(-b);
H2 is the conditional density theorem. The prime n of OAI is Nat.nth Nat.Prime (n-1). -/

namespace OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R1

open Filter Finset
open scoped Classical

/-- Bombieri–Vinogradov, with the maximal error over reduced residues. -/
def H1 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → (∑ q ∈ Finset.Icc 1 ⌊x ^ (1/2:ℝ) * Real.log x ^ (-b)⌋₊,
      (((Finset.range q).sup fun c => if Nat.Coprime c q then
        NNReal.mk |(∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n % q = c),
          ArithmeticFunction.vonMangoldt n) - x / q.totient| (abs_nonneg _) else 0 : NNReal) : ℝ))
      ≤ M * x * Real.log x ^ (-A)

/-- Bombieri–Vinogradov implies positive lower density of indices n ≤ N with
p_(n+1) - p_n > C log p_n. -/
def H2 : Prop :=
  (∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → (∑ q ∈ Finset.Icc 1 ⌊x ^ (1/2:ℝ) * Real.log x ^ (-b)⌋₊,
      (((Finset.range q).sup fun c => if Nat.Coprime c q then
        NNReal.mk |(∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n % q = c),
          ArithmeticFunction.vonMangoldt n) - x / q.totient| (abs_nonneg _) else 0 : NNReal) : ℝ))
      ≤ M * x * Real.log x ^ (-A)) →
    ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.Icc 1 N).filter fun n => C * Real.log (Nat.nth Nat.Prime (n - 1)) <
        (Nat.nth Nat.Prime n : ℝ) - (Nat.nth Nat.Prime (n - 1) : ℝ)).card : ℝ)

lemma count_eq (A : ℝ) (N : ℕ) :
    ((range N).filter fun n => A * Real.log (Nat.nth Nat.Prime n) < (primeGap n : ℝ)).card =
      ((Finset.Icc 1 N).filter fun n => A * Real.log (Nat.nth Nat.Prime (n - 1)) <
        (Nat.nth Nat.Prime n : ℝ) - (Nat.nth Nat.Prime (n - 1) : ℝ)).card := by
  have castGap (n : ℕ) : (primeGap n : ℝ) = (Nat.nth Nat.Prime (n+1) : ℝ) - (Nat.nth Nat.Prime n : ℝ) := by
    rw [primeGap, Nat.cast_sub ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self n)).le]
  apply Finset.card_bij (fun n _ => n+1)
  · intro n hn
    obtain ⟨hn,hg⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, Nat.succ_le_of_lt (mem_range.mp hn)⟩,
      by simpa [castGap] using hg⟩
  · intros; omega
  · intro n hn
    obtain ⟨hi,hg⟩ := mem_filter.mp hn
    obtain ⟨lo,hi⟩ := mem_Icc.mp hi
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ⟨k,mem_filter.mpr ⟨mem_range.mpr (by omega),by simpa [castGap] using hg⟩, rfl⟩

theorem main : H1 → H2 → OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1.H1 := by
  intro bv density A hA
  obtain ⟨c,hc,N₀,h⟩ := density bv A hA
  exact ⟨c,hc,eventually_atTop.mpr ⟨N₀,fun N hN => by rw [count_eq]; exact h N hN⟩⟩

end OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R1
