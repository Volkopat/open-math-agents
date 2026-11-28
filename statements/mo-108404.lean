import Mathlib

/-!
# Kaplansky's sixth conjecture

Source: https://mathoverflow.net/questions/108404
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Kaplansky, 6th of his 1975 Hopf algebra conjectures): for a finite-dimensional
semisimple Hopf algebra `H` over an algebraically closed field of characteristic `0`, the
dimension of every irreducible representation divides `dim H`.

Conventions:
* Irreducible representations are simple left `H`-modules (finite-dimensional automatically, as
  quotients of `H`); `dim` is `Module.finrank` over the base field `k`.
* Semisimple: `H` is a semisimple ring.
-/

namespace OMA.S_mo_108404

theorem main :
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (H : Type) [Ring H] [HopfAlgebra k H]
      [FiniteDimensional k H] [IsSemisimpleRing H]
      (V : Type) [AddCommGroup V] [Module H V] [Module k V] [IsScalarTower k H V],
      IsSimpleModule H V → Module.finrank k V ∣ Module.finrank k H := by
  sorry

end OMA.S_mo_108404
