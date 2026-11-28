import FormalConjectures.Wikipedia.Mersenne

-- Credit: @PetrouilFan
-- Reduction of the New Mersenne Conjecture for odd exponents.  The upstream lemma
-- `new_mersenne_conjecture_of_prime` proves the composite-exponent case outright and
-- reduces the whole statement to the prime-exponent case, which is the genuinely open
-- core (upstream variant `new_mersenne_conjecture.variants.prime`).  The two hypotheses
-- are therefore genuinely different regimes, not a restatement of the target.

namespace OMA.R_Mersenne_new_mersenne_conjecture_R1

open Mersenne

-- The open core: odd prime exponents.
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → NewMersenneConjectureStatement p

-- The settled regime: odd composite exponents (proved upstream).
def H2 : Prop :=
  ∀ p : ℕ, ¬ p.Prime → Odd p → NewMersenneConjectureStatement p

theorem main : H1 → H2 → type_of% @Mersenne.new_mersenne_conjecture := by
  intro hp hc p hodd
  by_cases hprime : p.Prime
  · exact hp p hprime hodd
  · exact hc p hprime hodd

end OMA.R_Mersenne_new_mersenne_conjecture_R1
