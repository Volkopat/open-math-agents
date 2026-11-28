import Mathlib

/-!
# Conjecture: `x⁴ + 1` is never a Wieferich prime

Source: https://mathoverflow.net/questions/470571 (CC BY-SA 4.0).

For a natural number `n` let `J(n) = (2^{n-1} - 1) mod n²`, the least residue (the source also sets
`J(2^k) = 1` for powers of two, to avoid trivialities). A prime `p` is a Wieferich prime iff
`J(p) = 0`.

Conjecture 1 of the source: for even `n` we have `J(n² + 1) < J(n⁴ + 1)`; hence `J(n⁴ + 1) > 0`,
so `n⁴ + 1` is never a Wieferich prime. The asker checked it for `n ≤ 10^6` and several very
large `n`. (The source's Conjecture 2, an asymptotic for `log J(n⁴+1) / log J(n²+1)`, is not
stated here.) We state Conjecture 1, the precise claim behind the title.

Formalization notes:
* `J n` is `(2 ^ (n - 1) - 1) % n ^ 2` in `ℕ`. The special value `J(2^k) = 1` never matters
  here: for even `n ≥ 2`, `n² + 1` and `n⁴ + 1` are odd numbers greater than `1`, so not powers of
  two.
* "Even `n`" is read as even `n ≥ 2`. For `n = 0` both arguments equal `1` and `J(1) = 0`, so the
  strict inequality fails trivially; the standard reading excludes this degenerate value.
* Checked numerically for all even `2 ≤ n ≤ 3000`.
-/

namespace OMA.S_mo_470571

/-- `J(n) = (2^{n-1} - 1) mod n²`. -/
def J (n : ℕ) : ℕ :=
  (2 ^ (n - 1) - 1) % n ^ 2

/-- Conjecture 1: for every even `n ≥ 2`, `J(n² + 1) < J(n⁴ + 1)`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → Even n → J (n ^ 2 + 1) < J (n ^ 4 + 1) := by
  sorry

end OMA.S_mo_470571
