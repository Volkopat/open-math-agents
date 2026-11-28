import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! Source: https://mathoverflow.net/questions/292841 -/

namespace OMA.S_mo_292841

/-- Multiplying each product of fractional parts by p² gives a product
of least nonnegative residues. -/
def residueSum (p : ℕ) (a : ZMod p) : ℕ :=
  ∑ k ∈ Finset.range ((p - 1) / 2),
    ((((k + 1 : ℕ) : ZMod p) ^ 2).val) *
      (a * (((k + 1 : ℕ) : ZMod p) ^ 2)).val

/-- The quartic-character congruence in the final display of the source. -/
theorem main :
    ∀ (p : ℕ) [Fact (Nat.Prime p)], p % 4 = 1 →
      ∀ a : ZMod p, a ≠ 0 →
        (-a) ^ ((p - 1) / 4) =
          (-(↑(((p - 1) / 2).factorial) : ZMod p)) ^
            ((1 - legendreSym p a.val) / 2).toNat *
          (-1) ^ residueSum p a := by
  sorry

end OMA.S_mo_292841
