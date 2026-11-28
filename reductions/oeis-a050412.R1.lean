import OMAStatements.S_oeis_a050412
import Mathlib

/-! A periodic covering of the exponents proves that the proposed coefficient
works for every exponent. Minimality remains open. The orbit question is independent. -/
namespace OMA.R_oeis_a050412_R1
open OMA.S_oeis_a050412

def H1 : Prop := IsRiesel 509203

def H2 : Prop := ∀ n < 509203, ¬ IsRiesel n

def H3 : Prop := ∀ n : ℕ, 1 ≤ n → a n = 1 → a (2 * n + 1) ≠ 0

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a050412.main :=
  fun cover minimal orbit => ⟨⟨cover, minimal⟩, orbit⟩

end OMA.R_oeis_a050412_R1
