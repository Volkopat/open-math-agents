import Mathlib

/-!
# Enumerative and Structural Aspects Of Anagrams Without Fixed Letters

Source: https://arxiv.org/abs/1810.07219 (K. Bangachev; published in Enumerative Combinatorics and
Applications 3:2 (2023), Article #S2R9), Conjecture 6.0.1 (Conjecture 6.1 of the published version).
Credit: @tatashbar

For the word `ω = 1^{x_1} 2^{x_2} ... n^{x_n}` (`x_i` copies of the letter `i`), the source denotes by
`A(x_1, ..., x_n)` the number of its anagrams without fixed letters: the words with the same letters,
counted with multiplicity, that differ from `ω` at every position. (Example in the source: the
anagrams without fixed letters of `1123` are `2311` and `3211`, so `A(2, 1, 1) = 2`.)

Conjecture 6.0.1 of the source, verbatim up to typography: "Suppose that
`x_i < max(x_1, x_2, ..., x_n)`. Then,
`A(x_1, x_2, ..., x_{i-1}, x_i, x_{i+1}, ..., x_n) ≤ A(x_1, x_2, ..., x_{i-1}, x_i + 1, x_{i+1}, ..., x_n)`."

`main` states this conjecture as posed.

What the source proves: the inequality under the stronger hypothesis
`x_i < (1/2) max(x_1, ..., x_n)` (Theorem 4.3.4 of the arXiv version, Theorem 4.5 of the published
version), and the analogous inequality for `D = x_1! ⋯ x_n! · A` under the hypothesis of the
conjecture (Theorem 4.3.3, resp. Theorem 4.4). After the latter the source notes that the hypothesis
is tight for `D`: "For example `D(t, t) > 0 = D(t + 1, t)` for `t ≥ 1`." For `A` this reads
`A(t, t) = 1 > 0 = A(t + 1, t)` (a remark of this translation, not of the source; another example,
with both sides positive, is `A(1, 2, 2) = 4 > 3 = A(1, 3, 2)`).

Which open question of the source is formalised, and why. The abstract of the source says: "While
the function A() bears significant importance to economic theory [13], it is not known whether it
can be computed in polynomial time." The fuller sentence, in Section 1.2 of the source, attributes
the question to Emiris and Vidunas (ISSAC 2014): "it is an open question whether one can find the
number `A(x_1, x_2, ..., x_n)` with a polynomial-time algorithm even for the equinumerous case
`x_1 = x_2 = ⋯ = x_n = k` [7]." That question is NOT what `main` states, for the following reason,
which the reviewer is asked to weigh. It has three readings.
* With the multiplicities `x_i` counted in unary, `A` is computable in time polynomial in
  `x_1 + ... + x_n` by the Laguerre-polynomial formula of S. Even and J. Gillis (Math. Proc.
  Cambridge Philos. Soc. 79 (1976) 135-143); R. Vidunas, arXiv 1401.5400, Section 3, says: "For
  computational purposes, the integral representation (6)-(7) gives an effective, polynomial time
  algorithm to get the E-numbers." (His `E` is `A`.)
* With the `x_i` written in binary (the convention of the source for input size, proof of its
  Corollary 3.3.3) and time counted in bit operations, no polynomial-time algorithm can exist,
  because the value is too long to write: `A(k, k, k) = ∑_j C(k, j)^3` has about `3k` binary
  digits.
* With the `x_i` written in binary and time counted in arithmetic operations on integers of any
  size, the question is genuinely open. It is a statement about a model of computation rather than
  about the numbers `A(x)`, and it has no exact form as a Lean statement about `A`.
So the complexity question is settled in the first reading, has a negative answer for a trivial
reason in the second, and is open but not statable here in the third. The statement that the source
itself leaves open and that can be stated exactly is its Conjecture 6.0.1, quoted above. (Its other
conjecture, 6.0.2, on the hamiltonicity of "anagraphs", allows finitely many unspecified
exceptions.)

Conventions of this translation.
* The alphabet is `Fin n` (the letter `i` of the source is `i - 1`) and `x : Fin n → ℕ`; the source
  takes `x ∈ ℤ_{≥0}^n`, zeros allowed.
* The positions of `ω` are the pairs `⟨j, a⟩ : Σ j : Fin n, Fin (x j)`; the position `⟨j, a⟩` carries
  the letter `j`. A word on these positions is a function `w` from the positions to `Fin n`. It is an
  anagram of `ω` when every letter `k` occurs exactly `x k` times in `w`, and it has no fixed letter
  when `w p ≠ p.1` for every position `p`.
* The hypothesis `x_i < max(x_1, ..., x_n)` is written `∃ m, x i < x m`, and replacing `x_i` by
  `x_i + 1` is `Function.update x i (x i + 1)`.
-/

namespace OMA.S_arxiv_1810_07219

/-- `A x`: the number of anagrams without fixed letters of the word with `x j` copies of the letter
`j`, for each `j : Fin n`. A word is a function `w` on the positions `Σ j, Fin (x j)`; it is counted
when no position `⟨j, a⟩` carries the letter `j` and every letter `k` occurs `x k` times. -/
def A {n : ℕ} (x : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun w : (Σ j : Fin n, Fin (x j)) → Fin n =>
    (∀ p, w p ≠ p.1) ∧ ∀ k : Fin n, (Finset.univ.filter fun p => w p = k).card = x k).card

/-- Conjecture 6.0.1 of arXiv 1810.07219: if `x i` is not the largest multiplicity, then adding one
more copy of the letter `i` does not decrease the number of anagrams without fixed letters. -/
theorem main : ∀ (n : ℕ) (x : Fin n → ℕ) (i : Fin n), (∃ m : Fin n, x i < x m) →
    A x ≤ A (Function.update x i (x i + 1)) := by
  sorry

end OMA.S_arxiv_1810_07219
