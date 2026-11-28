import Mathlib

/-!
# Can one always solve 1 + b n ≡ 0 modulo a maximal ideal with n a natural number?

Source: https://mathoverflow.net/questions/450204
Asked by MathOverflow user user481562.

Let `K` be a number field and `b ∈ 𝓞_K^*`. The question asks whether for every maximal ideal
`𝔭` of `𝓞_K` one can pick a natural number `n` such that `1 + b n ≡ 0 (mod 𝔭)`.

Translation choices.
* `𝓞_K^*` is read as the unit group of the ring of integers `𝓞_K`. (If it is instead read as
  the nonzero elements of `𝓞_K`, the claim only becomes stronger, so a counterexample to the
  version formalized here is also a counterexample to that reading.)
* `1 + b n ≡ 0 (mod 𝔭)` means that `1 + b * n` lies in the ideal `𝔭`.
* `main` is the affirmative answer, stated for all number fields `K`, all units `b` and all
  maximal ideals `𝔭`.
-/

namespace OMA.S_mo_450204

theorem main :
    ∀ (K : Type) [Field K] [NumberField K] (b : (NumberField.RingOfIntegers K)ˣ)
      (P : Ideal (NumberField.RingOfIntegers K)), P.IsMaximal →
      ∃ n : ℕ, 1 + (b : NumberField.RingOfIntegers K) * (n : NumberField.RingOfIntegers K) ∈ P := by
  sorry

end OMA.S_mo_450204
