import OMAStatements.S_oeis_a054767
import Mathlib

/-! The A054767 conjecture says the least positive period of the Bell numbers modulo a prime p
is N_p = (p^p - 1)/(p - 1). It splits into two halves of very different status.

* That N_p is a period at all is a classical theorem: Touchard's congruence
  B(n + p) = B(n) + B(n + 1) mod p says the shift operator E on the Bell sequence modulo p
  satisfies E^p = E + 1, and in characteristic p this forces E^(p^k) = E + k, so that
  E^(N_p) = (E)(E + 1)...(E + p - 1) = E^p - E = 1 (Touchard 1933, Hall 1934).
* That no smaller positive period exists (the minimality, verified by Wagstaff and later
  authors only for small primes) is the open part.

H1 is the first, classical half; H2 is the open minimality. -/

namespace OMA.R_oeis_a054767_R1

/-- Touchard and Hall: (p^p - 1)/(p - 1) is a period of the Bell numbers modulo every prime p. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → (p ^ p - 1) / (p - 1) ∈ OMA.S_oeis_a054767.positiveBellPeriods p

/-- The open minimality: every positive period of the Bell numbers modulo p is at least
(p^p - 1)/(p - 1). -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ m ∈ OMA.S_oeis_a054767.positiveBellPeriods p, (p ^ p - 1) / (p - 1) ≤ m

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a054767.main := by
  intro h1 h2 p hp
  exact ⟨h1 p hp, fun m hm => h2 p hp m hm⟩

end OMA.R_oeis_a054767_R1
