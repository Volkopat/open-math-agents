import OMAStatements.S_oeis_a074777

-- Reduction oeis-a074777.R1 of OEIS A074777 (integers n with 2 * σ(φ(n)) = n)
-- Credit: @Ciphore
-- The six known terms are 2, 6, 30, 510, 131070, 8589934590: exactly 2 times a product of
-- distinct Fermat primes (3, 5, 17, 257, 65537). The arithmetic is tight: for
-- n = 2 * ∏ F_i a product of distinct Fermat primes, φ(n) = ∏ (F_i - 1) = 2^(1+2+4+...) is a
-- power of 2, and then σ(φ(n)) = 2^(k+1) - 1 must equal n / 2 — which is exactly the product
-- of the Fermat primes because 2^(2^i) - 1 factors as the product of the earlier Fermat
-- numbers. The conjecture therefore intertwines with the distribution of Fermat primes.
--
-- The two directions are mathematically independent and are split here. Each H becomes its
-- own step once this file is accepted; proving both closes the problem.
--
-- H1 (membership / construction): each of the six known values satisfies the equation. For
--    the larger terms this is not finite computation but requires the multiplicative
--    propagation of φ and σ through the Fermat-factor structure — `Nat.totient` and
--    `ArithmeticFunction.sigma` of prime-power and coprime factorizations.
-- H2 (exclusion): no other positive integer satisfies the equation. The hard core; any
--    solution must first be forced into the squarefree Fermat-factor shape (a structure
--    theorem of independent interest), and then the exclusion reduces to the scarcity of
--    Fermat primes.

namespace OMA.R_oeis_a074777_R1

open ArithmeticFunction

/-- Every positive solution of `2 * σ(φ(n)) = n` is one of the six known terms. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → 2 * sigma 1 (Nat.totient n) = n →
  n = 2 ∨ n = 6 ∨ n = 30 ∨ n = 510 ∨ n = 131070 ∨ n = 8589934590

/-- Each of the six known terms satisfies `2 * σ(φ(n)) = n`. -/
def H2 : Prop := ∀ n : ℕ, n = 2 ∨ n = 6 ∨ n = 30 ∨ n = 510 ∨ n = 131070 ∨ n = 8589934590 →
  2 * sigma 1 (Nat.totient n) = n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a074777.main := by
  intro hexcl hmem
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, heq⟩
    exact hexcl n hn heq
  · intro hn
    exact ⟨by rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide, hmem n hn⟩

end OMA.R_oeis_a074777_R1
