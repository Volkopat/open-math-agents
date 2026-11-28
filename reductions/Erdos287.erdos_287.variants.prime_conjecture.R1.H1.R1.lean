import OMAReductions.R_Erdos287_erdos_287_variants_prime_conjecture_R1
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Filter MeasureTheory
open scoped BigOperators

namespace OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1

/-- The major-arc approximation error after replacing prime sums by their
Siegel–Walfisz density models and summing the reduced residue classes. -/
def H1 : Prop :=
  let F (N : ℕ) (θ : ℝ) :=
    ∑ p ∈ (Finset.Icc N (2 * N)).filter Nat.Prime,
      ∑ q ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log p * Real.log q * Real.cos (2 * Real.pi * ((p : ℝ) + 1 - 2 * q) * θ)
  let A (N : ℕ) : Set ℝ :=
    Set.Icc 0 1 ∩ ⋃ b : ℕ, ⋃ a : ℕ,
      ⋃ (_ : 0 < b ∧ (b : ℝ) ≤ Real.log N ^ 2 ∧ a ≤ b ∧ Nat.Coprime a b),
        Set.Icc ((a : ℝ) / b - Real.log N ^ 2 / N) ((a : ℝ) / b + Real.log N ^ 2 / N)
  let S (N : ℕ) : ℝ :=
    ∑ b ∈ Finset.Icc 1 (Nat.floor (Real.log (N : ℝ) ^ 2)),
      let c := b / Nat.gcd b 2
      ((ArithmeticFunction.moebius b : ℝ) ^ 2 * (ArithmeticFunction.moebius c : ℝ)) /
        ((Nat.totient b : ℝ) * (Nat.totient c : ℝ))
  let J (N : ℕ) : ℝ :=
    let δ := Real.log (N : ℝ) ^ 2 / (N : ℝ)
    ∫ β in Set.Icc (-δ) δ,
      ∫ x in Set.Icc (N : ℝ) (2 * (N : ℝ)),
        ∫ y in Set.Icc (0 : ℝ) (N : ℝ),
          Real.cos (2 * Real.pi * ((x + 1 - 2 * y) * β))
  ∀ᶠ N : ℕ in atTop, |(∫ θ in A N, F N θ) - S N * J N| ≤ (N : ℝ) / 128

/-- A lower bound for the truncated singular series, whose limit is twice
the twin-prime constant. -/
def H2 : Prop :=
  let S (N : ℕ) : ℝ :=
    ∑ b ∈ Finset.Icc 1 (Nat.floor (Real.log (N : ℝ) ^ 2)),
      let c := b / Nat.gcd b 2
      ((ArithmeticFunction.moebius b : ℝ) ^ 2 * (ArithmeticFunction.moebius c : ℝ)) /
        ((Nat.totient b : ℝ) * (Nat.totient c : ℝ))
  ∀ᶠ N : ℕ in atTop, (17 : ℝ) / 16 ≤ S N

/-- A lower bound for the truncated singular integral from the two
continuous prime-density models. -/
def H3 : Prop :=
  let J (N : ℕ) : ℝ :=
    let δ := Real.log (N : ℝ) ^ 2 / (N : ℝ)
    ∫ β in Set.Icc (-δ) δ,
      ∫ x in Set.Icc (N : ℝ) (2 * (N : ℝ)),
        ∫ y in Set.Icc (0 : ℝ) (N : ℝ),
          Real.cos (2 * Real.pi * ((x + 1 - 2 * y) * β))
  ∀ᶠ N : ℕ in atTop, 31 * (N : ℝ) / 64 ≤ J N

theorem main : H1 → H2 → H3 → OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1.H1 := by
  intro herror hseries hintegral
  unfold H1 at herror
  unfold H2 at hseries
  unfold H3 at hintegral
  unfold OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1.H1
  filter_upwards [herror, hseries, hintegral] with N he hs hj
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hJ : 0 ≤ 31 * (N : ℝ) / 64 := by positivity
  have hS : 0 ≤ (17 : ℝ) / 16 := by norm_num
  have hproduct := mul_le_mul hs hj hJ (hS.trans hs)
  have herr := (abs_le.mp he).1
  linarith only [hN, hproduct, herr]

end OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1
