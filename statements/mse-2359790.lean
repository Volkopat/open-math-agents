import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Primorial

/-!
# MSE 2359790: primorial translation criterion for admissible tuples

Source: https://math.stackexchange.com/questions/2359790/k-tuple-admissibility

A finite integer tuple is admissible if its residues omit at least one class
modulo every prime. The source asks whether, for a primorial modulus greater
than the tuple's diameter, admissibility is equivalent to the existence of an
integer translate consisting entirely of units modulo that modulus.

We quantify over the primorial modulus M itself. The range of primorial values
is the same whether the index denotes a prime bound or a number of primes.
For a finite set, the strict pairwise distance bound below is exactly the
condition that its diameter is less than M. Membership in the unit group is
expressed by `IsUnit` in the residue ring.
-/

namespace OMA.S_mse_2359790

/-- Every prime modulus has a residue class omitted by the finite integer tuple. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- A primorial exceeding the diameter is proposed to detect admissibility
through the existence of a translate into its units. -/
theorem main :
    ∀ (H : Finset ℤ) (M : ℕ), (∃ m : ℕ, M = primorial m) →
      (∀ a ∈ H, ∀ b ∈ H, |a - b| < (M : ℤ)) →
      ((∃ n : ℤ, ∀ h ∈ H, IsUnit ((h + n : ℤ) : ZMod M)) ↔ Admissible H) := by
  sorry

end OMA.S_mse_2359790
