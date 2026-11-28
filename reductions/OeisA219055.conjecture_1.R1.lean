import FormalConjectures.OEIS.«219055»

-- Reduction OeisA219055.conjecture_1.R1 of Representations of $n$ using prime pairs with prime gaps of $6$ — conjecture 1
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Representations `n = p + q (3 - (-1)^n)/2` with `p, q, p - 6, q + 6` prime

`a n` counts the `q < n` with `(2 + (n mod 2)) * q < n` for which `q`, `q + 6`, the partner
`p = n - (1 + n mod 2) * q`, and `p - 6` are all prime. Sun's conjecture is that `a n > 0` for every
even `n > 8012` and every odd `n > 15727`; the two thresholds differ because the odd case spends
`2 q` of the representation on `q` and leaves the smaller partner `p = n - 2 q`.

For a fixed `n` the count is a finite search over the primes `q`, so every single `n` is decided by
computation. What is open is a uniform argument, and the statement implies Goldbach's conjecture,
Lemoine's conjecture and the infinitude of primes `q` with `q + 6` also prime.

The OEIS entry A219055 records how far the computation was pushed: the conjecture has been verified
for `n` up to `10^8` (the entry's comment, with a table of `a(n)` for `n = 1..100000`). Beyond a
finite search there is no proof, so the conjecture splits there:

* `H1` (searched range): even `8012 < n <= 10^8` and odd `15727 < n <= 10^8` have `a n > 0`. Finite:
  for each `n` a search over the primes `q < n / (2 + (n mod 2))` and four primality tests.
* `H2` (the open tail): the same for `n > 10^8`. Nothing is known here.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, with no
upstream lemma, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA219055_conjecture_1_R1

/-- The searched range: every even `n` with `8012 < n <= 10^8` and every odd `n` with
`15727 < n <= 10^8` is a sum `n = p + q (3 - (-1)^n)/2` with `p > q` and `p, q, p - 6, q + 6` all
prime (OEIS A219055: the conjecture `a(n) > 0` was verified for `n` up to `10^8`). -/
def H1 : Prop :=
  ∀ n : ℕ, ((Even n ∧ 8012 < n) ∨ (Odd n ∧ 15727 < n)) → n ≤ 100000000 →
    0 < OeisA219055.a n

/-- The open tail: the same representation for even `n > 10^8` and odd `n > 10^8`. This range
contains Goldbach's conjecture and the infinitude of primes `q` with `q + 6` prime, so no argument
is known for it. -/
def H2 : Prop :=
  ∀ n : ℕ, ((Even n ∧ 8012 < n) ∨ (Odd n ∧ 15727 < n)) → 100000000 < n →
    0 < OeisA219055.a n

theorem main : H1 → H2 → type_of% @OeisA219055.conjecture_1 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 100000000
  · exact h1 n hn h
  · exact h2 n hn (Nat.lt_of_not_le h)

end OMA.R_OeisA219055_conjecture_1_R1
