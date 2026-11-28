import Mathlib

/-!
# Prime pairs in OEIS A309392

Row `n` lists the primes `p` for which `p + 2 * n` is prime, using zero
when an entry is missing. The conjecture says that every row is infinite.
OEIS also gives the formulation below for every even integer difference.
The two primes are positive, and their difference may have either sign.

Source: https://oeis.org/A309392 (Felix Fröhlich, OEIS Foundation, CC BY-SA 4.0)
Credit: @hrishikeshio
-/

namespace OMA.S_oeis_a309392

theorem main : ∀ e : ℤ, Even e →
    {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ (p : ℤ) + e = q}.Infinite := by
  sorry

end OMA.S_oeis_a309392
