import OMAReductions.R_oeis_a027697_R1
import Mathlib

-- Reduction oeis-a027697.R1.H3.R1 of step oeis-a027697.R1.H3
-- Credit: @arindale

/-!
# The shifted odious-prime race: a growing lead versus a counting bound

`H3` of the parent reduction says that for every fixed shift `B`, eventually at an odious prime
`x` the evil primes up to `x + B` are no more numerous than the odious primes up to `x`.

A window of `B` consecutive integers contains at most `B` primes, so
`evil(x + B) ≤ evil(x) + B`.  Hence the target follows from the statement that the lead of the
odious primes over the evil primes at odious primes is unbounded: for every `B`, eventually
`evil(x) + B ≤ odious(x)`.  That is the genuine content (the Chebyshev-type bias of the two
binary-weight classes), while the window bound is an elementary counting fact.
-/

namespace OMA.R_oeis_a027697_R1_H3_R1

open Filter OMA.S_oeis_a027697

/-- The lead of the odious primes over the evil primes is unbounded along odious primes. -/
def H1 : Prop :=
  ∀ B : ℕ, ∀ᶠ x : ℕ in atTop, x.Prime ∧ Odd (s2 x) →
    Nat.count (fun p => p.Prime ∧ Even (s2 p)) x + B ≤
      Nat.count (fun p => p.Prime ∧ Odd (s2 p)) x

/-- A window of `B` consecutive integers contains at most `B` evil primes. -/
def H2 : Prop :=
  ∀ x B : ℕ,
    Nat.count (fun p => p.Prime ∧ Even (s2 p)) (x + B) ≤
      Nat.count (fun p => p.Prime ∧ Even (s2 p)) x + B

theorem main : H1 → H2 → OMA.R_oeis_a027697_R1.H3 := by
  intro h1 h2 B
  filter_upwards [h1 B] with x hx
  intro hxprime
  have hgap := hx hxprime
  have hwin := h2 x B
  omega

end OMA.R_oeis_a027697_R1_H3_R1
