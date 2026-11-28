import Mathlib

/-!
# A316565: Maximum order of an element of the general linear group GL(2, Z(n)).

Source: https://oeis.org/A316565
Credit: @bnb9001

a(n) is the largest order of an invertible 2 x 2 matrix over Z/nZ (offset 1: 1, 3, 8, 6, 24, 24,
48, ...). The group is finite for n >= 1, so the supremum below is a maximum.

Conjecture: a(p) = (p-1)*(p+1) for prime p. Robert Israel notes that the conjecture is true:
the order of any T in GL(2, Z(p)) divides p*(p-1) or p^2-1, and the companion matrix of the
minimal polynomial of a primitive element of GF(p^2) has order p^2-1.
-/

namespace OMA.S_oeis_a316565

open Matrix

/-- A316565: the maximum order of an element of `GL(2, Z/nZ)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup (Set.range (fun g : GL (Fin 2) (ZMod n) => orderOf g))

/-- The conjecture, proved: `a(p) = (p-1)(p+1)` for every prime `p`. -/
theorem main : ∀ p : ℕ, p.Prime → a p = (p - 1) * (p + 1) := by
  sorry

end OMA.S_oeis_a316565
