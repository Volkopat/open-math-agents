import Mathlib

namespace OMA.S_oeis_a217924

def a372205 : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      let m := n + 1
      let v := padicValNat 2 m
      (-1 : ℤ) ^ m * a372205 ((m - 2 ^ v) / 2) + a372205 ((2 * m - 2 ^ v) / 2)
termination_by n => n
decreasing_by
  · have hpos : 1 ≤ 2 ^ padicValNat 2 (n + 1) := Nat.one_le_two_pow
    omega
  · have hpos : 1 ≤ 2 ^ padicValNat 2 (n + 1) := Nat.one_le_two_pow
    omega

noncomputable def expSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun k => ((k.factorial : ℚ)⁻¹))

theorem main :
    ∀ A : PowerSeries ℚ,
      PowerSeries.coeff 0 A = 1 →
      PowerSeries.derivative ℚ A = (2 * expSeries - 1) * A →
      ∀ n : ℕ,
        ((n.factorial : ℚ) * PowerSeries.coeff n A) =
          ((∑ k ∈ Finset.range (2 ^ n), a372205 k : ℤ) : ℚ) := by
  sorry

end OMA.S_oeis_a217924
