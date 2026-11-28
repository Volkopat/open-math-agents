import OMAReductions.R_Erdos5_erdos_5_variants_merikoski_measure_R1

-- Reduction Erdos5.erdos_5.variants.merikoski_measure.R1.H1.R1 of step
-- Erdos5.erdos_5.variants.merikoski_measure.R1.H1
-- Credit: @arindale
--
-- The step is Merikoski's four-shift theorem in the prime normalization
-- `primeGap n / log (p_n)`.  We reduce it to the same theorem in the index
-- normalization used by `limitPointSet` (where `normalizedGap n` divides by
-- `log n`), plus the elementary transfer of a limit point between the two
-- normalizations, which only uses `log (p_n) / log n -> 1`.

namespace OMA.R_Erdos5_erdos_5_variants_merikoski_measure_R1_H1_R1

open Filter MeasureTheory Real Set Erdos5
open scoped Topology

/-- Merikoski's four-shift theorem, in the index normalization of `limitPointSet`:
for any monotone four-tuple, some difference is a limit point of the normalized
prime gaps. -/
def H1 : Prop :=
  ∀ β : Fin 4 → ℝ, Monotone β → ∃ i j, i < j ∧ β j - β i ∈ limitPointSet

/-- Transfer of a limit point from the index normalization to the prime
normalization `primeGap n / log (p_n)`. -/
def H2 : Prop :=
  ∀ x : ℝ, x ∈ limitPointSet →
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun k => (primeGap (n k) : ℝ) / log (Nat.nth Nat.Prime (n k)))
        atTop (𝓝 x)

theorem main : H1 → H2 → OMA.R_Erdos5_erdos_5_variants_merikoski_measure_R1.H1 := by
  intro h1 h2 β hβ
  obtain ⟨i, j, hij, hx⟩ := h1 β hβ
  obtain ⟨n, hn, ht⟩ := h2 (β j - β i) hx
  exact ⟨i, j, hij, n, hn, ht⟩

end OMA.R_Erdos5_erdos_5_variants_merikoski_measure_R1_H1_R1
