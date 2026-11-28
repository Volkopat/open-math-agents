import Mathlib

/-! OEIS A138227. The OEIS divisor-sum formula for A137576 yields an infinite
family of members from positive powers of the Wieferich prime 1093. -/

namespace OMA.S_oeis_a138227

/-- Multiplicative order of 2 modulo d. -/
noncomputable def ordTwo (d : ℕ) : ℕ := orderOf (2 : ZMod d)

/-- A137576((n-1)/2) - 1 for odd positive n. -/
noncomputable def excess (n : ℕ) : ℕ :=
  ordTwo n * ((∑ d ∈ n.divisors, d.totient / ordTwo d) - 1)

def IsMember (n : ℕ) : Prop := Odd n ∧ ¬ n.totient ∣ excess n

/-- A138227 is infinite, with 1093^k a member for every k at least 2. -/
theorem main : {n : ℕ | IsMember n}.Infinite ∧ ∀ k : ℕ, IsMember (1093 ^ (k + 2)) := by
  sorry

end OMA.S_oeis_a138227
