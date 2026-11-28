import OMAStatements.S_oeis_a394432

/-!
Jianing Song, OEIS A394432. The entry asks three independent questions.
The fourth-power witness and the strictness argument each settle one of them.
Credit: @jatin6
-/

namespace OMA.R_oeis_a394432_R1

def H1 : Prop := OMA.S_oeis_a394432.OddPrimePowers
def H2 : Prop := OMA.S_oeis_a394432.FurtherPower
def H3 : Prop := OMA.S_oeis_a394432.StrictAtPowersOfTwo

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a394432.main :=
  fun primes further strict => ⟨primes, further, strict⟩

end OMA.R_oeis_a394432_R1
