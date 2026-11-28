import Mathlib

/-!
# Simultaneous rational relations between roots of unity

LFM, https://mathoverflow.net/questions/364129 (CC BY-SA 4.0).
Credit: @connoranderson.

The vectors on the nonzero residues are written as functions on all of
`ZMod N` whose zeroth coordinate is zero. The cyclotomic field is viewed
inside the complex numbers. The kernel consists of the functions constant
on each orbit under multiplication by the given subgroup.
-/

namespace OMA.S_mo_364129

theorem main : ∀ (N : ℕ) [NeZero N] (ζ : ℂ), IsPrimitiveRoot ζ N →
    ∀ (Γ : Subgroup (ZMod N)ˣ) (v : ZMod N → ℚ), v 0 = 0 →
    ((∀ n : ZMod N, n ≠ 0 → ∀ r ∈ Γ,
      ∑ i : ZMod N, (v i : ℂ) * (ζ^((r : ZMod N)*i*n).val - ζ^(i*n).val) = 0) ↔
    ∀ r ∈ Γ, ∀ i : ZMod N, v ((r : ZMod N)*i) = v i) := by
  sorry

end OMA.S_mo_364129
