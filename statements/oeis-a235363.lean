import Mathlib

/-!
# A235363: (1 + Sum_{k=1..m-1} k^(m-1)) (mod m), for m = 1, 3, 5, 7, 9, ...

Source: https://oeis.org/A235363
Credit: @azmiozgen

Conjecture (the Agoh-Giuga conjecture, as stated in the entry): a(n) = 0 iff 2*n+1 is 1 or a
prime.

Formalization notes:
* a(n), offset 0, is (1 + Sum_{k=1..m-1} k^(m-1)) mod m with m = 2n + 1.
* Stated for every n ≥ 0.
* Controls (computed): a(0..28) = 0, 0, 0, 0, 7, 0, 0, 11, 0, 0, 15, 0, 21, 19, 0, 0, 23, 1, 0, 27,
  0, 0, 22, 0, 43, 35, 0, 1, 39, as in the entry; the equivalence holds for n < 3000.
-/

namespace OMA.S_oeis_a235363

/-- A235363(n) = (1 + ∑_{k=1}^{m-1} k^(m-1)) mod m, with `m = 2n + 1`. -/
def a (n : ℕ) : ℕ := (1 + ∑ k ∈ Finset.Icc 1 (2 * n), k ^ (2 * n)) % (2 * n + 1)

/-- The Agoh–Giuga conjecture for odd `m = 2n+1`. -/
theorem main : ∀ n : ℕ, a n = 0 ↔ (2 * n + 1 = 1 ∨ (2 * n + 1).Prime) := by
  sorry

end OMA.S_oeis_a235363
