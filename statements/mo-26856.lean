import Mathlib

/-!
# MathOverflow 26856

Source: https://mathoverflow.net/questions/26856
-/

namespace OMA.S_mo_26856

open Submodule

def scalarRange (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (x : R) : Submodule R M := LinearMap.range (LinearMap.lsmul R M x)

theorem main : ∀ (R M : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
      (p : PrimeSpectrum R) (x : R),
      p.asIdeal ∈ associatedPrimes R M →
      x ∈ IsLocalRing.maximalIdeal R → IsSMulRegular M x →
      ∀ q : PrimeSpectrum R, p ≤ q →
        q.asIdeal ∈ associatedPrimes R (M ⧸ scalarRange R M x) →
        q ∈ Module.support R (M ⧸ scalarRange R M x) := by
  sorry

end OMA.S_mo_26856
