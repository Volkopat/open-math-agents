import Mathlib

/-!
# A285076: 1-limiting word of the morphism 0->10, 1-> 010.

Source: https://oeis.org/A285076
Credit: @rickmanelius

Conjecture (R. J. Mathar, Jun 24 2025): a(n) = A285073(n), n>=3.

Formalization notes:
* The morphism sends 0 to 10 and 1 to 010 (`morph`; every letter other than 0 goes to 010, and
  only the letters 0 and 1 occur). S(0) = 0 and S(k+1) is the image of S(k) under the morphism
  (`iter`), as in the comment of the entry: 0 -> 10 -> 01010 -> 100101001010 -> ...
* The comment says the morphism has two limiting words: the even iterates S(0), S(2), S(4), ...
  give the 0-limiting word A285073 and the odd iterates S(1), S(3), S(5), ... give the
  1-limiting word A285076. The entries compute them the same way, as Nest of the morphism on 0
  with 14 (even) and 13 (odd) iterations. S(2) = 01010 begins with S(0) = 0 and S(3) begins with
  S(1) = 10, so each S(k) is an initial segment of S(k+2) (apply the morphism k times), and S(k)
  has at least 2^k letters. Hence letter n (counting from 1, offset 1 in both entries) of the
  1-limiting word is letter n of S(2k+1) for every k with 2^(2k+1) ≥ n, and `a n` reads it from
  S(2n+1); letter n of the 0-limiting word is letter n of S(2k) for every k with 2^(2k) ≥ n, and
  `A285073 n` reads it from S(2n). The values a(1), a(2), ... are 1, 0, 0, 1, 0, 1, 0, 0, 1, ...
  and A285073(1), A285073(2), ... are 0, 1, 0, 1, 0, 1, 0, 0, 1, ..., matching the data.
* The conjecture is stated for n ≥ 3, as in the entry.
-/

namespace OMA.S_oeis_a285076

/-- The morphism 0 -> 10, 1 -> 010 (every letter other than 0 goes to 010). -/
def morph : ℕ → List ℕ
  | 0 => [1, 0]
  | _ => [0, 1, 0]

/-- S(0) = 0 and S(k+1) = image of S(k) under the morphism. -/
def iter : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (iter k).flatMap morph

/-- A285076(n) for n ≥ 1: letter n, counting from 1, of the 1-limiting word (the limit of the
odd iterates S(2k+1)), read from S(2n+1). -/
def a (n : ℕ) : ℕ := (iter (2 * n + 1)).getD (n - 1) 0

/-- A285073(n) for n ≥ 1: letter n, counting from 1, of the 0-limiting word (the limit of the
even iterates S(2k)), read from S(2n). -/
def A285073 (n : ℕ) : ℕ := (iter (2 * n)).getD (n - 1) 0

/-- Mathar's conjecture: a(n) = A285073(n) for n ≥ 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n → a n = A285073 n := by
  sorry

end OMA.S_oeis_a285076
