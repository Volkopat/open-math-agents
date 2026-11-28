import FormalConjectures.OEIS.«2326»

-- Reduction OeisA2326.conjecture2.R2 of Multiplicative order of 2 mod 2n+1 — conjecture2
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Orders of 2 modulo consecutive powers of an odd prime: the tested grid and the open tail

The theorem says that for every `k ≥ 2` and every odd prime `p`,

  ord of 2 modulo `p ^ (k + 1)` equals `p` times ord of 2 modulo `p ^ k`,

written in the file as `a ((p ^ (k + 1) - 1) / 2) = p * a ((p ^ k - 1) / 2)`, with `a n` the order
of `2` modulo `2 * n + 1`. The OEIS comment on A002326 (Ahmad J. Masad, Oct 17 2020) records exactly
how far this has been tested: there is no counterexample for `k` and `p` both up to 1000.

So the grid of pairs `(k, p)` splits into the tested square and its complement:

* `H1` (tested range): every `k` with `2 ≤ k ≤ 1000` and every odd prime `p ≤ 1000`. This is the
  finite verification reported in the OEIS entry. It is one identity per pair, with both sides
  orders of `2` modulo explicit numbers, so each pair is a finite computation.
* `H2` (the rest): `1000 < k` or `1000 < p`. Nothing here is known. The docstring of the problem
  shows that this tail is in fact equivalent to the `k = 2` case (`conjecture1`) by lifting the
  exponent at `p`, so `H2` is the open core of the problem.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split.
-/

namespace OMA.R_OeisA2326_conjecture2_R2

/-- The tested square: `2 ≤ k ≤ 1000` and odd primes `p ≤ 1000`. -/
def H1 : Prop :=
  ∀ k : ℕ, 2 ≤ k → k ≤ 1000 → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ 1000 →
    OeisA2326.a ((p ^ (k + 1) - 1) / 2) = p * OeisA2326.a ((p ^ k - 1) / 2)

/-- The open tail: `1000 < k` or `1000 < p`. -/
def H2 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ p : ℕ, p.Prime → p ≠ 2 → (1000 < k ∨ 1000 < p) →
    OeisA2326.a ((p ^ (k + 1) - 1) / 2) = p * OeisA2326.a ((p ^ k - 1) / 2)

theorem main : H1 → H2 → type_of% @OeisA2326.conjecture2 := by
  intro h1 h2 k hk p hp hp2
  by_cases hk1 : k ≤ 1000
  · by_cases hp1 : p ≤ 1000
    · exact h1 k hk hk1 p hp hp2 hp1
    · exact h2 k hk p hp hp2 (Or.inr (by omega))
  · exact h2 k hk p hp hp2 (Or.inl (by omega))

end OMA.R_OeisA2326_conjecture2_R2
