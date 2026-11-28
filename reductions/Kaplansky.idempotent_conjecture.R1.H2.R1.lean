import OMAReductions.R_Kaplansky_idempotent_conjecture_R1

-- Reduction Kaplansky.idempotent_conjecture.R1.H2.R1 of step Kaplansky.idempotent_conjecture.R1.H2
-- Credit: @arindale

/-!
# Kaplansky's idempotent conjecture: the augmentation-ideal form

The open case `H2` asks that `K[G]` has no non-trivial idempotents for torsion-free groups
without unique products.  We reformulate it in the standard augmentation-ideal shape: it is
enough to show that idempotents of augmentation zero vanish.  Indeed the augmentation is a
ring homomorphism to the field `K`, so the augmentation of an idempotent is `0` or `1`; when it
is `1`, `1 - e` is an idempotent of augmentation `0`, and `e ≠ 1` exactly when `1 - e ≠ 0`.
The two hypotheses split on the characteristic of the field.
-/

namespace OMA.R_Kaplansky_idempotent_conjecture_R1_H2_R1

/-- Characteristic zero: idempotents of augmentation zero vanish. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K], CharZero K →
  ∀ (G : Type) [Group G], Monoid.IsTorsionFree G → ¬ UniqueProds G →
  ∀ a : MonoidAlgebra K G, IsIdempotentElem a →
    (MonoidAlgebra.lift K K G (1 : G →* K) : MonoidAlgebra K G →+* K) a = 0 → a = 0

/-- Non-zero characteristic: idempotents of augmentation zero vanish. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K], ¬ CharZero K →
  ∀ (G : Type) [Group G], Monoid.IsTorsionFree G → ¬ UniqueProds G →
  ∀ a : MonoidAlgebra K G, IsIdempotentElem a →
    (MonoidAlgebra.lift K K G (1 : G →* K) : MonoidAlgebra K G →+* K) a = 0 → a = 0

theorem main : H1 → H2 → OMA.R_Kaplansky_idempotent_conjecture_R1.H2 := by
  intro h1 h2 K _ G _ hG hU a ha
  let φ : MonoidAlgebra K G →+* K :=
    (MonoidAlgebra.lift K K G (1 : G →* K) : MonoidAlgebra K G →+* K)
  have hφ : IsIdempotentElem (φ a) := ha.map φ
  have hzero : φ a * (φ a - 1) = 0 := by
    rw [mul_sub, mul_one, hφ.eq, sub_self]
  rcases mul_eq_zero.mp hzero with h0 | hone
  · by_cases hc : CharZero K
    · exact Or.inl (h1 K hc G hG hU a ha h0)
    · exact Or.inl (h2 K hc G hG hU a ha h0)
  · have hb : IsIdempotentElem (1 - a) := ha.one_sub
    have hb0 : φ (1 - a) = 0 := by
      rw [map_sub, map_one, sub_eq_zero.mp hone, sub_self]
    have hbeq : 1 - a = 0 := by
      by_cases hc : CharZero K
      · exact h1 K hc G hG hU (1 - a) hb hb0
      · exact h2 K hc G hG hU (1 - a) hb hb0
    exact Or.inr (sub_eq_zero.mp hbeq).symm

end OMA.R_Kaplansky_idempotent_conjecture_R1_H2_R1
