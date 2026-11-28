import OMAStatements.S_oeis_a008848

-- Reduction oeis-a008848.R1 of OEIS A008848 (squares whose sum of divisors is a square)
-- Credit: @Ciphore
-- Karttunen's three conjectures are independent set equalities with genuinely distinct
-- mathematical content. The positive instances are verified below by direct computation
-- (`σ(81) = 121 = 11^2`, `σ(400) = 961 = 31^2`, `σ(1) = 1`), so each hypothesis is the
-- pure EXCLUSION core of one conjecture. Each H becomes its own step once this file is
-- accepted; proving all three closes the problem.
--
-- H1 (prime-power exclusion): a prime power `x = p^k` that is a square must have `k = 2j`
--    even, and then `σ(x) = 1 + p + … + p^(2j)` is a geometric sum with an odd number of
--    terms. Requiring this sum to be a perfect square is an exponential Diophantine equation
--    of Lebesgue–Nagell type; `81 = 3^4` with `σ(81) = 121 = 11^2` is conjecturally the
--    only solution.
-- H2 (sigma prime-power exclusion): the inverse-image problem — `σ` is multiplicative, so
--    `σ(x)` being a single prime power forces severe constraints on the coprime factorization
--    of `x`; conjecturally only `81` and `400` qualify.
-- H3 (iteration exclusion): the dynamical core — `σ` mapping squares-with-square-σ back into
--    the sequence. Conjecturally only the trivial case `x = 1` survives iteration.

namespace OMA.R_oeis_a008848_R1

open ArithmeticFunction
open OMA.S_oeis_a008848

/-- The prime-power exclusion core: no prime-power term except `81`. -/
def H1 : Prop := {x : ℕ | IsTerm x ∧ IsPrimePow x} ⊆ {81}

/-- The sigma-prime-power exclusion core: no term with prime-power σ except `81` and `400`. -/
def H2 : Prop := {x : ℕ | IsTerm x ∧ IsPrimePow (sigma 1 x)} ⊆ {81, 400}

/-- The iteration exclusion core: no term whose σ is again a term, except `1`. -/
def H3 : Prop := {x : ℕ | IsTerm x ∧ IsTerm (sigma 1 x)} ⊆ {1}

theorem sigma_81 : sigma 1 81 = 121 := by decide
theorem sigma_400 : sigma 1 400 = 961 := by decide
theorem sigma_1 : sigma 1 1 = 1 := by decide

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a008848.main := by
  intro h1 h2 h3
  have h81sq : IsSquare (81 : ℕ) := ⟨9, by decide⟩
  have h121sq : IsSquare (121 : ℕ) := ⟨11, by decide⟩
  have h400sq : IsSquare (400 : ℕ) := ⟨20, by decide⟩
  have h961sq : IsSquare (961 : ℕ) := ⟨31, by decide⟩
  have h1sq : IsSquare (1 : ℕ) := ⟨1, by decide⟩
  have hT81 : IsTerm 81 := ⟨by decide, h81sq, sigma_81 ▸ h121sq⟩
  have hT400 : IsTerm 400 := ⟨by decide, h400sq, sigma_400 ▸ h961sq⟩
  have hT1 : IsTerm 1 := ⟨by decide, h1sq, sigma_1 ▸ h1sq⟩
  have hpp81 : IsPrimePow 81 := ⟨3, 4, by decide, by decide, by decide⟩
  have hpp121 : IsPrimePow 121 := ⟨11, 2, by decide, by decide, by decide⟩
  have hpp961 : IsPrimePow 961 := ⟨31, 2, by decide, by decide, by decide⟩
  refine ⟨?_, ?_, ?_⟩
  · exact Set.Subset.antisymm h1 (by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hT81, hpp81⟩)
  · exact Set.Subset.antisymm h2 (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨hT81, sigma_81 ▸ hpp121⟩
      · exact ⟨hT400, sigma_400 ▸ hpp961⟩)
  · exact Set.Subset.antisymm h3 (by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hT1, sigma_1 ▸ hT1⟩)

end OMA.R_oeis_a008848_R1
