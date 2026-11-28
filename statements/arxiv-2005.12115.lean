import Mathlib

/-!
# Must a primitive non-deficient number have a component not much larger than its radical?

Source: https://arxiv.org/abs/2005.12115 (Joshua Zelinsky), abstract and Theorem 2.
Credit: @ivillar

Abstract of the source: Let $n$ be a primitive non-deficient number where
$n = p_1^{a_1} p_2^{a_2} \cdots p_k^{a_k}$ where $p_1, p_2, \cdots, p_k$ are distinct primes.
We prove that there exists an $i$ such that $p_i^{a_i+1} < 2k(p_1 p_2 p_3 \cdots p_k)$.

Formalization notes:
* As in Section 1 of the source, $n$ is deficient when $\sigma(n) < 2n$; this is Mathlib's
  `Nat.Deficient` (the proper divisors of `n` sum to less than `n`). A positive integer is
  primitive non-deficient when it is non-deficient and none of its divisors other than itself
  is non-deficient.
* The primes $p_i$ are the elements of `n.primeFactors`, the exponent $a_i$ of $p_i$ is
  `n.factorization p_i`, $k$ is `n.primeFactors.card`, and $p_1 p_2 \cdots p_k$ is the radical
  `∏ q ∈ n.primeFactors, q`.
* `main` is the result that the abstract announces as proved (Theorem 2 of the source), with
  the bound $2k \cdot \mathrm{rad}(n)$. The abstract also conjectures the stronger bound
  $2 \cdot \mathrm{rad}(n)$ (Conjecture 1 of the source); that conjecture is not asserted here.
-/

namespace OMA.S_arxiv_2005_12115

/-- `n` is primitive non-deficient: it is positive and non-deficient, and each of its divisors
other than `n` itself is deficient. -/
def PrimitiveNonDeficient (n : ℕ) : Prop :=
  0 < n ∧ ¬ n.Deficient ∧ ∀ d : ℕ, d ∣ n → d ≠ n → d.Deficient

theorem main : ∀ n : ℕ, PrimitiveNonDeficient n →
    ∃ p ∈ n.primeFactors,
      p ^ (n.factorization p + 1) < 2 * n.primeFactors.card * ∏ q ∈ n.primeFactors, q := by
  sorry

end OMA.S_arxiv_2005_12115
