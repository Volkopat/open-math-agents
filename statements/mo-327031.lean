import Mathlib

/-!
# Regularity of non-Noetherian commutative rings

Source https://mathoverflow.net/questions/327031/on-the-definition-of-regular-non-noetherian-commutative-rings

Does there exist a commutative ring whose finitely generated ideals
all have finite projective dimension, with a finitely presented
module of infinite projective dimension?
-/

namespace OMA.S_mo_327031

open CategoryTheory

theorem main :
    ∃ R : CommRingCat,
      (∀ I : Ideal R, I.FG → projectiveDimension (ModuleCat.of R ↥I) < ⊤) ∧
      ∃ M : ModuleCat R, Module.FinitePresentation R M ∧ projectiveDimension M = ⊤ := by
  sorry

end OMA.S_mo_327031
