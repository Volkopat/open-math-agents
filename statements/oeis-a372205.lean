import Mathlib

namespace OMA.S_oeis_a372205

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
    ∀ B : PowerSeries ℚ,
      PowerSeries.coeff 0 B = 1 →
      PowerSeries.derivative ℚ B = (expSeries - 1) * B →
      ∀ n : ℕ,
        ((n.factorial : ℚ) * PowerSeries.coeff n B) = (a372205 (2 ^ n - 1) : ℚ) := by
  sorry

end OMA.S_oeis_a372205
