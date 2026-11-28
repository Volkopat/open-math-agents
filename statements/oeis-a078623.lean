import Mathlib

/-!
# A078623: Number of matched parentheses and brackets of length n.

Source: https://oeis.org/A078623
Name: Number of matched parentheses and brackets of length n, where a closing
bracket will close any remaining open parentheses back to the matching open
bracket (as in some versions of LISP).
Conjecture (Peter Bala, Oct 23 2015): `a(n-1) = (-1)^(n-1) * (1/n) *
Sum_{k=1..n} binomial(n,k) * binomial(n - 2*k, k - 1)`.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

We take the OEIS recurrence as the definition: with auxiliary sequence `b`,
`a(0) = b(0) = 1`, and for `n >= 1`

* `a(n) = Sum_{j=0..n-2} a(j) * (a(n-2-j) + b(n-2-j))`,
* `b(n) = b(n-1) + Sum_{j=0..n-2} b(j) * (a(n-2-j) + b(n-2-j))`.

This is the count given by the unambiguous context-free grammar stated in the
OEIS entry (`S -> ( S ) S | [ T ] S | e`, `T -> ( T | ( S ) T | [ T ] T | e`).
Binomial coefficients with negative upper index use the polynomial extension
`C(m, r) = (-1)^r * C(r - m - 1, r)` for `m < 0`, which is the convention of
the printed formula.  The body stays `sorry`; a person reviews the translation
before merging.
-/

noncomputable section

open scoped Classical

namespace OMA.S_oeis_a078623

/-- Binomial coefficient extended to negative upper index by the polynomial
convention `C(m, r) = (-1)^r * C(r - m - 1, r)` for `m < 0`. -/
def extChoose (m : ℤ) (r : ℕ) : ℤ :=
  if _hm : m ≥ 0 then
    (Nat.choose m.toNat r : ℤ)
  else
    (-1 : ℤ) ^ r * (Nat.choose (r + m.natAbs - 1) r : ℤ)

/-- Pairs `(a(i), b(i))` for `i < n`, built from the OEIS recurrence. -/
def abPairs : ℕ → List (ℕ × ℕ)
  | 0 => []
  | n + 1 =>
      let ps := abPairs n
      let get := fun j => ps.getD j (0, 0)
      let sa := ((List.range (n - 1)).map
        (fun j => (get j).1 * ((get (n - 2 - j)).1 + (get (n - 2 - j)).2))).sum
      let sb := ((List.range (n - 1)).map
        (fun j => (get j).2 * ((get (n - 2 - j)).1 + (get (n - 2 - j)).2))).sum
      ps ++ [(if n = 0 then 1 else sa,
              if n = 0 then 1 else (get (n - 1)).2 + sb)]

/-- The OEIS A078623 sequence `1, 0, 2, 1, 9, 11, 56, ...`: number of matched
parentheses and brackets of length `n`. -/
def a078623 (n : ℕ) : ℕ := ((abPairs (n + 1)).getLastD (0, 0)).1

/-- Peter Bala's conjectured sum `Sum_{k=1..n} C(n,k) * C(n - 2*k, k - 1)`. -/
def balaSum (n : ℕ) : ℤ :=
  (Finset.range n).sum
    (fun idx => extChoose n (idx + 1) * extChoose ((n : ℤ) - 2 * (idx + 1)) idx)

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (n : ℤ) * (a078623 (n - 1) : ℤ) = (-1 : ℤ) ^ (n - 1) * balaSum n := by
  sorry

end OMA.S_oeis_a078623

end
