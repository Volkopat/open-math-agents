import Mathlib

/-!
# Schanuel's conjecture and the power tower `I ^ (I ^ I)`

Source: https://oeis.org/A116191 (OEIS Foundation, CC BY-SA 4.0).
The sequence gives the decimal expansion of the imaginary part of this power.
Its comment cites Diego Marques and Jonathan Sondow, *Schanuel's conjecture
and algebraic powers z^w and w^z with z and w transcendental*, East-West J.
Math. 12 (2010), 75–84, p. 79: https://arxiv.org/abs/1010.6216.
The conditional transcendence assertion concerns the complex power itself.
Complex powers below use Mathlib's principal branch.
Credit: @connoranderson.
-/

namespace OMA.S_oeis_a116191

/-- Schanuel's conjecture in its transcendence-degree formulation. -/
def SchanuelConjecture : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), LinearIndependent ℚ z →
    n ≤ Algebra.trdeg ℚ
      (IntermediateField.adjoin ℚ (Set.range z ∪ Set.range (Complex.exp ∘ z)))

theorem main : SchanuelConjecture →
    Transcendental ℚ (Complex.I ^ (Complex.I ^ Complex.I)) := by
  sorry

end OMA.S_oeis_a116191
