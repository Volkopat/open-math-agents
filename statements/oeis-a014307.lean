import Mathlib

namespace OMA.S_oeis_a014307

def kurkovR (m : ℚ) : ℕ → ℕ → ℚ
  | 0, _ => 1
  | n + 1, 0 => ∑ j ∈ Finset.range (n + 1), kurkovR m n j
  | n + 1, k + 1 =>
      m * (∑ j ∈ Finset.range (n + 1), kurkovR m n j) -
        ∑ j ∈ Finset.range (k + 1), kurkovR m n j

noncomputable def expSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun k => ((k.factorial : ℚ)⁻¹))

theorem main :
    ∀ A : PowerSeries ℚ,
      (∀ n : ℕ, PowerSeries.coeff n A = kurkovR 2 n 0 / (n.factorial : ℚ)) →
      A ^ 2 * (2 - expSeries) = expSeries := by
  sorry

end OMA.S_oeis_a014307
