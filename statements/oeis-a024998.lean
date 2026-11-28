import Mathlib

/-!
# A024998: number of (s(0), ..., s(n)) with s(0) = 0, |s(i) - s(i-1)| = 1 for i = 1,2, |s(i) - s(i-1)| <= 1 for i >= 3, s(n) = 1.

Source: https://oeis.org/A024998
Credit: @divmxnd0x

Conjecture (R. J. Mathar, Jun 23 2013, stated in A024998):
`(n+1) a(n) + (-3n+2) a(n-1) + (-n-7) a(n-2) + 3 (n-4) a(n-3) = 0`.

Formalization notes:
* A sequence `(s(0), ..., s(n))` with `s(0) = 0` is determined by its steps
  `s(i) - s(i-1) ∈ {-1, 0, 1}`; a step is encoded by `d i : Fin 3` as `(d i : ℤ) - 1`. The first
  two steps (`i = 1, 2`, i.e. indices `0, 1` of `d`) must be `±1` (`d i ≠ 1`), and `s(n) = 1`
  means that the steps sum to `1`. Offset 1: `a 1, a 2, ... = 1, 0, 3, 6, 19, 52, 150, ...`.
* The recurrence involves `a(n-3)`, so it is stated for `n ≥ 4` (all indices `≥ 1`), in `ℤ`.
-/

namespace OMA.S_oeis_a024998

/-- A024998(n): the number of step sequences of length `n` as above. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun d : Fin n → Fin 3 =>
    (∀ i : Fin n, i.val < 2 → d i ≠ 1) ∧ ∑ i, ((d i : ℤ) - 1) = 1).card

/-- Mathar's recurrence for A024998. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n + (-3 * (n : ℤ) + 2) * a (n - 1) + (-(n : ℤ) - 7) * a (n - 2) +
      3 * ((n : ℤ) - 4) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a024998
