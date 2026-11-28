import Mathlib

/-!
# MathOverflow 35878

Source: https://mathoverflow.net/questions/35878
-/

namespace OMA.S_mo_35878



theorem main : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [FiniteDimensional k A],
    Module.finrank k (IsLocalRing.ResidueField A) ∣ Module.finrank k A := by
  sorry

end OMA.S_mo_35878
