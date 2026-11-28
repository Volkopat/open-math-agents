import Mathlib

/-!
# Least degree for avoiding prescribed sets over a prime field

Michael Ren asks whether, for a prime `p` and `d < p`, every family of
`d`-element forbidden sets indexed by `ZMod p` can be avoided by a polynomial
of degree at most `d`, and whether `d` is the least such bound.
Here `natDegree` assigns degree zero to the zero polynomial, as in the question.

Source: https://mathoverflow.net/questions/498708/interpolating-a-degree-d-polynomial-over-mathbb-f-p-to-avoid-sets-of-size
-/

namespace OMA.S_mo_498708

theorem main :
    ∀ (p d : ℕ) [Fact p.Prime], d < p →
      IsLeast
        {e : ℕ | ∀ forbidden : ZMod p → Finset (ZMod p),
          (∀ i, (forbidden i).card = d) →
            ∃ f : Polynomial (ZMod p), f.natDegree ≤ e ∧ ∀ i, f.eval i ∉ forbidden i} d := by
  sorry

end OMA.S_mo_498708
