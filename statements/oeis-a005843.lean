import Mathlib

/-!
# A005843: The nonnegative even numbers: a(n) = 2n.

Source: https://oeis.org/A005843
Credit: @diegopluna

The entry's comments record two groups of conjectures. `main` states both, as a conjunction, in
the order the source gives them.

Conjectures 1 and 2 (Eric Desbiaux, Oct 28 2008), as corrected and proved by Sela Fried
(Dec 03 2025, "Proof of two conjectures stated in A005843", linked from the entry). Let
S(n) = sum_{k=1..n} (-1)^(k-1) * 2k be the n-th alternating partial sum of the sequence, let
P(n) = A002378(n) = n(n+1) and B(n) = 2 * A008794(n+1) = 2 * floor((n+1)/2)^2. Fried's
Theorem 1: for n in N,
  1. S(n) = (-1)^(n+1) * A052928(n+1);
  2. P(n) - 2 B(n) = -S(n).
Desbiaux's original comment wrote the second identity with A116471 = 2 * A008794, which is not
correct as stated (A116471 = 0, 2, 8, 8, 18, ... while 2 * A008794 = 0, 0, 2, 2, 8, ...); the
source says the corrected conjectures are true and points to Fried's note for the correction,
so the corrected form is stated here.

Conjecture 3 (Bob Selcoe, Mar 08 2015). For n > 2, a(n) = A020482(n) + A002373(n), "where all
sequences are infinite". A020482(n) is the greatest p with p, q both prime and p + q = 2n;
A002373(n) is the smallest prime in a decomposition of 2n into a sum of two odd primes.

Reading of the source:
* `a n = 2 * n` with the entry's offset 0.
* The alternating sums and identities 1 and 2 are taken over the integers. Fried's n ranges over
  N with S(2n-1) used for n in N, so the identities are stated for n >= 1.
* A052928(m) = 2 * floor(m/2) (the even numbers repeated, offset 0), A002378(n) = n(n+1)
  (offset 0), A008794(m) = floor(m/2)^2 (offset 0).
* Conjecture 3: "all sequences are infinite" is read as A020482(n) and A002373(n) being defined
  for every n > 2, that is, the sets they are the greatest/least element of are nonempty and
  have such an element. `IsGreatest`/`IsLeast` assert exactly that, together with the value.
  As the source remarks, this contains Goldbach's conjecture for every even number 2n >= 6.
-/

namespace OMA.S_oeis_a005843

/-- A005843(n): the nonnegative even numbers, a(n) = 2n. -/
def a (n : ℕ) : ℕ := 2 * n

/-- S(n): the n-th alternating partial sum of A005843, sum_{k=1..n} (-1)^(k-1) * 2k. -/
def altSum (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (k - 1) * (a k : ℤ)

/-- A052928(m): the even numbers repeated, 2 * floor(m/2). -/
def A052928 (m : ℕ) : ℕ := 2 * (m / 2)

/-- A002378(n): the oblong numbers, n(n+1). -/
def A002378 (n : ℕ) : ℕ := n * (n + 1)

/-- A008794(m): the squares repeated, floor(m/2)^2. -/
def A008794 (m : ℕ) : ℕ := (m / 2) ^ 2

/-- The primes `p` for which `2n = p + q` with `q` prime: A020482(n) is the greatest of them. -/
def goldbachPrimes (n : ℕ) : Set ℕ := {p | p.Prime ∧ ∃ q, q.Prime ∧ p + q = 2 * n}

/-- The primes `p` in a decomposition `2n = p + q` into two odd primes: A002373(n) is the
least of them. -/
def oddGoldbachPrimes (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ Odd p ∧ ∃ q, q.Prime ∧ Odd q ∧ p + q = 2 * n}

theorem main :
    -- Conjecture 1 (Desbiaux, corrected by Fried): S(n) = (-1)^(n+1) * A052928(n+1).
    (∀ n : ℕ, 1 ≤ n → altSum n = (-1 : ℤ) ^ (n + 1) * (A052928 (n + 1) : ℤ)) ∧
    -- Conjecture 2 (Desbiaux, corrected by Fried): A002378(n) - 2 * (2 * A008794(n+1)) = -S(n).
    (∀ n : ℕ, 1 ≤ n →
      (A002378 n : ℤ) - 2 * (2 * (A008794 (n + 1) : ℤ)) = -altSum n) ∧
    -- Conjecture 3 (Selcoe): for n > 2, A020482(n) and A002373(n) exist and
    -- a(n) = A020482(n) + A002373(n).
    (∀ n : ℕ, 2 < n →
      ∃ g s : ℕ, IsGreatest (goldbachPrimes n) g ∧ IsLeast (oddGoldbachPrimes n) s ∧
        a n = g + s) := by
  sorry

end OMA.S_oeis_a005843
