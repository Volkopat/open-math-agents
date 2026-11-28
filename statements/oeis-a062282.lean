import Mathlib

/-!
# A062282: permutations of n elements with an even number of fixed points

Source: https://oeis.org/A062282
Credit: @jagong-cmu

Formalizes John Keith's OEIS A062282 conjecture (Jun 30 2020), offset 0:
`Conjecture: a(n) = Sum_{k=0..n} A008290(n, k)*A059841(k).`

Conventions:
* The `n` elements are `Fin n`, and a permutation is an `Equiv.Perm (Fin n)`.
  A fixed point of `σ` is an `i` with `σ i = i`.
* `a n` (A062282) is the number of permutations of `Fin n` whose number of fixed points is even.
* `T n k` (A008290, rencontres numbers) is the number of permutations of `Fin n`
  with exactly `k` fixed points.
* `chiEven k` (A059841) is `1 - (k mod 2)`, the characteristic function of the even numbers.
* The claim is stated for every `n >= 0` (the offset of A062282 is 0).
-/

namespace OMA.S_oeis_a062282

/-- The number of fixed points of a permutation `σ` of `Fin n`. -/
def fixedPts {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i => σ i = i).card

/-- A062282: the number of permutations of `n` elements with an even number of fixed points. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => Even (fixedPts σ)).card

/-- A008290: the number of permutations of `n` elements with exactly `k` fixed points. -/
def T (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => fixedPts σ = k).card

/-- A059841: `1 - (k mod 2)`. -/
def chiEven (k : ℕ) : ℕ := 1 - k % 2

/-- For all `n >= 0`: `a(n) = Sum_{k=0..n} A008290(n, k) * A059841(k)`. -/
theorem main : ∀ n : ℕ, a n = ∑ k ∈ Finset.range (n + 1), T n k * chiEven k := by
  sorry

end OMA.S_oeis_a062282
