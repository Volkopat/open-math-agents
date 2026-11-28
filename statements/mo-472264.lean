import Mathlib

/-!
# Dimension inequality for subspaces in field extensions

Source: Shahab, https://mathoverflow.net/questions/472264
Credit: @RiverMint78

For a field extension L/K, the question asks whether the K-span of the
products of elements of A and B has dimension at least dim A + dim B − 1,
under the stated bounds on intersections with aM and bM. The bounds range
over all scalars and all finite intermediate fields other than K and L.

The image under multiplication by a scalar represents aM, and the
submodule product A * B is the K-span of the products.
-/

namespace OMA.S_mo_472264

theorem main :
    ∀ (K L : Type*) [Field K] [Field L] [Algebra K L]
      (A B : Submodule K L) [Module.Finite K A] [Module.Finite K B],
      0 < Module.finrank K A → 0 < Module.finrank K B →
      (∀ (a b : L) (M : IntermediateField K L),
        M ≠ ⊥ → M ≠ ⊤ → Module.Finite K M →
        Module.finrank K (M.toSubmodule.map (Algebra.lmul K L a) ⊓ A : Submodule K L) +
          Module.finrank K (M.toSubmodule.map (Algebra.lmul K L b) ⊓ B : Submodule K L) ≤
          Module.finrank K M + 1) →
      Module.finrank K A + Module.finrank K B - 1 ≤
        Module.finrank K (A * B : Submodule K L) := by
  sorry

end OMA.S_mo_472264
