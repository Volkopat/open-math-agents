import OMAStatements.S_oeis_a058887
import Mathlib

/-! A periodic covering of the exponents proves that the proposed coefficient
works for every exponent. Minimality remains open. -/
namespace OMA.R_oeis_a058887_R1
open OMA.S_oeis_a058887

def H1 : Prop := Nat.Prime 271129 ∧ IsSierpinski 271129

def H2 : Prop := ∀ p : ℕ, p.Prime → IsSierpinski p → 271129 ≤ p

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a058887.main :=
  fun cover minimal => ⟨cover, fun _ hp => minimal _ hp.1 hp.2⟩

end OMA.R_oeis_a058887_R1
