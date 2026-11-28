import Mathlib

/-! Source: https://mathoverflow.net/questions/120573 -/

open Filter

namespace OMA.S_mo_120573

/-- The n-fold iterate of a ring endomorphism as a ring homomorphism. -/
def ringIter {R : Type} [Semiring R] (f : R →+* R) : ℕ → R →+* R
  | 0 => RingHom.id R
  | n + 1 => f.comp (ringIter f n)

/-- The proposed eventual squaring of an invariant ideal under an
endomorphism that contracts the maximal ideal and preserves both radicals. -/
theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R →+* R) (a : Ideal R),
    ((IsLocalRing.maximalIdeal R).map f).radical = IsLocalRing.maximalIdeal R →
    (∀ᶠ n in atTop, (IsLocalRing.maximalIdeal R).map (ringIter f n) ≤
      (IsLocalRing.maximalIdeal R) ^ 2) →
    a.map f ≤ a → (a.map f).radical = a.radical →
    ∀ᶠ n in atTop, a.map (ringIter f n) ≤ a ^ 2 := by
  sorry

end OMA.S_mo_120573
