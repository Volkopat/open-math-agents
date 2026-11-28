import Mathlib

/-!
# A191017: Primes with Kronecker symbol (p|14) = 1

Source: https://oeis.org/A191017
Credit: @xor2k

Formalizes the OEIS A191017 conjecture (Vincenzo Librandi, Jun 22 2016): primes congruent to
{1, 3, 5, 9, 13, 15, 19, 23, 25, 27, 39, 45} mod 56. That is, a prime `p` is a term (has
Kronecker symbol `(p|14) = 1`) if and only if `p mod 56` lies in that set. The later comment
of Jianing Song (Nov 21 2019) is a proof sketch of this conjecture (via the residues of `p`
mod 7 and mod 8) and is not formalized separately.

Conventions: Mathlib has no general Kronecker symbol, so `(a|14)` is spelled out by its
definition: the Kronecker symbol is completely multiplicative in the lower argument, so
`(a|14) = (a|2) * (a|7)`; the Kronecker symbol `(a|2)` is `0` for even `a`, `1` for
`a ≡ ±1 (mod 8)` and `-1` for `a ≡ ±3 (mod 8)`, which is exactly Mathlib's character
`ZMod.χ₈`; and `(a|7)` is the Jacobi (here Legendre) symbol `jacobiSym a 7`. Primes are
natural numbers; `p % 56` is the least nonnegative residue.
-/

namespace OMA.S_oeis_a191017

/-- The Kronecker symbol `(a|14) = (a|2) * (a|7)`, with `(a|2) = ZMod.χ₈ a`. -/
def kron14 (a : ℤ) : ℤ :=
  ZMod.χ₈ (a : ZMod 8) * jacobiSym a 7

/-- The residues mod 56 listed in the conjecture. -/
def S : Finset ℕ := {1, 3, 5, 9, 13, 15, 19, 23, 25, 27, 39, 45}

/-- A prime `p` has Kronecker symbol `(p|14) = 1` iff `p mod 56` is one of the listed
residues. -/
theorem main :
    ∀ p : ℕ, p.Prime → (kron14 p = 1 ↔ p % 56 ∈ S) := by
  sorry

end OMA.S_oeis_a191017
