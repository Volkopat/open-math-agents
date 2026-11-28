import Mathlib

/-!
# A290408: the imaginary part of the fixed point of `z ↦ (i + z)^(-i)`

Source: https://oeis.org/A290408
Credit: @avivorly

Definition (the entry's name): "Decimal expansion of the real part of the solution of z = (i+z)^(-i) in C (i is the
imaginary unit)." The constant is `1.33920916852911196835926998576...`. A later comment of the entry describes the same
point as "The solution to x^i = x + i with the real part greater than 1." (Michal Paulovic).

Conjecture (Stanislav Sykora, in the entry): "Interestingly, the imaginary part of z seems to be equal to -1/2
(verified to 5000 digits)."

Conventions:
- `^` is Mathlib's `Complex.cpow`: `x ^ y = exp (log x * y)` for `x ≠ 0`, with the principal branch of `log`
  (`arg ∈ (-π, π]`). This is the branch of PARI, the language of the entry's programs.
- The entry's "the solution" is pinned by `Re z > 1`, as in Paulovic's comment, because the fixed point is not unique
  in `ℂ` (the same comment's "unique invariant point" fails: another fixed point is `z₁ ≈ -22.6296 - i/2`).
- The first conjunct shows that `Re z > 1` pins exactly one fixed point; the second conjunct is the conjecture for it.
-/

namespace OMA.S_oeis_a290408

theorem main :
    (∃! z : ℂ, (Complex.I + z) ^ (-Complex.I) = z ∧ 1 < z.re) ∧
    ∀ z : ℂ, (Complex.I + z) ^ (-Complex.I) = z → 1 < z.re → z.im = -1 / 2 := by
  sorry

end OMA.S_oeis_a290408
