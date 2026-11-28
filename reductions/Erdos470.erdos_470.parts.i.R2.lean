import FormalConjectures.ErdosProblems.«470»

-- Reduction Erdos470.erdos_470.parts.i.R2 of Erdős Problem 470 — i
-- Credit: @DevinWatson
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- General Core-Gap Bridge reduction for odd weird numbers:
-- Given an odd core m, an odd coprime multiplier t, and a positive excess E = sigma(m)*sigma(t) - 2*m*t,
-- if every prime factor of t exceeds E and E is not a subset sum of the divisors of m,
-- then n = m * t is an odd weird number.
--
-- H1 (provable, elementary): Any triple (m, t, E) satisfying the core-gap conditions yields
--    (m * t).Weird ∧ Odd (m * t). Indeed, multiplicativity of sigma gives sigma(m*t) = 2*m*t + E,
--    so m*t is abundant with excess E; if a subset S of properDivisors(m*t) summed to m*t,
--    its complement T would sum to E, forcing every d in T to satisfy d <= E < p for every
--    prime p | t, hence d | m, contradicting the subset-sum gap at E for m.divisors.
--    This unifies the excess-630 core (m = 98595, E = 630), the excess-2 family (E = 2),
--    and all jump-prime / missing-prime cores (e.g. m = 26325 E = 2, m = 277725 E = 14,
--    m = 680625 E = 22, m = 1824075 E = 22).
-- H2 (OPEN): Existence of such an arithmetic triple (m, t, E). Mentions neither Weird nor Pseudoperfect.

open scoped BigOperators

namespace OMA.R_Erdos470_erdos_470_parts_i_R2

def H1 : Prop :=
  ∀ m t E : ℕ, Odd m → Odd t → Nat.Coprime m t → 0 < E →
    (∑ d ∈ m.divisors, d) * (∑ d ∈ t.divisors, d) = 2 * m * t + E →
    (∀ p ∈ t.primeFactors, E < p) →
    (∀ s ⊆ m.divisors, ∑ d ∈ s, d ≠ E) →
    (m * t).Weird ∧ Odd (m * t)

def H2 : Prop :=
  ∃ m t E : ℕ, Odd m ∧ Odd t ∧ Nat.Coprime m t ∧ 0 < E ∧
    (∑ d ∈ m.divisors, d) * (∑ d ∈ t.divisors, d) = 2 * m * t + E ∧
    (∀ p ∈ t.primeFactors, E < p) ∧
    (∀ s ⊆ m.divisors, ∑ d ∈ s, d ≠ E)

theorem main : H1 → H2 → type_of% @Erdos470.erdos_470.parts.i := by
  intro h1 h2
  obtain ⟨m, t, E, hm, ht, hcop, hE, hsig, hp, hgap⟩ := h2
  exact ⟨m * t, h1 m t E hm ht hcop hE hsig hp hgap⟩

end OMA.R_Erdos470_erdos_470_parts_i_R2
