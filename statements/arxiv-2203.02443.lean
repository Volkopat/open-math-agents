import Mathlib

/-!
# Greedy cyclic products are maximal

Source: https://arxiv.org/abs/2203.02443
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

M. Holmes, A. E. Holroyd and A. Ramírez, "Cyclic products and optimal traps in cyclic birth and
death chains" (arXiv:2203.02443). For `r ∈ [m]`, a permutation `σ` of `{0, …, m-1}` and
`a_m = (a_0, …, a_{m-1})`, with indices mod `m`, the cyclic product is
  `P_r(σ; a_m) = ∑_{k=0}^{m-1} ∏_{i=0}^{r-1} a_{σ⁻¹(k+i)}`,
i.e. the sum of the products of `r` cyclically consecutive entries after arranging the `a_j` around
a cycle. The greedy permutation is given by `σ_greedy⁻¹(i) = 2i` and `σ_greedy⁻¹(m-1-i) = 2i+1` for
`i = 0, …, ⌊m/2⌋ - 1` (and, for odd `m`, `σ_greedy⁻¹((m-1)/2) = m-1`). Conjecture 1 ("greedy cyclic
products are maximal"): for `a_m ∈ (0, ∞)^m` with decreasing entries, every `r ∈ [m]` and every
`σ`, `P_r(σ_greedy; a_m) ≥ P_r(σ; a_m)`. The paper proves it for `r ≤ 3` and `r ≥ m - 3` (so for
all `r` when `m ≤ 7`); the cases `3 < r < m - 3` remain open. This file states Conjecture 1.

Modelling choices:
* Only `σ⁻¹` enters `P_r`, so the arrangement is passed directly as a permutation `τ = σ⁻¹` of
  `Fin m` (ranging over all permutations is the same as ranging over all `σ`); index arithmetic is
  in `Fin m`, i.e. mod `m`.
* "Decreasing entries" is read as non-increasing (`Antitone`); by continuity of `P_r` in `a_m` this
  is equivalent to the strictly decreasing reading.
-/

namespace OMA.S_arxiv_2203_02443

/-- The cyclic product `P_r` of the arrangement `τ = σ⁻¹` of `a` around the cycle `ℤ/mℤ`. -/
def cyclicProduct (m : ℕ) [NeZero m] (r : ℕ) (τ : Fin m → Fin m) (a : Fin m → ℝ) : ℝ :=
  ∑ k : Fin m, ∏ i ∈ Finset.range r, a (τ (k + Fin.ofNat m i))

/-- `σ_greedy⁻¹`: `i ↦ 2i` and `m-1-i ↦ 2i+1` for `i < ⌊m/2⌋`, and the middle position (odd `m`)
`↦ m-1`. -/
def greedy (m : ℕ) [NeZero m] (j : Fin m) : Fin m :=
  if (j : ℕ) < m / 2 then Fin.ofNat m (2 * (j : ℕ))
  else if m - m / 2 ≤ (j : ℕ) then Fin.ofNat m (2 * (m - 1 - (j : ℕ)) + 1)
  else Fin.ofNat m (m - 1)

/-- **Holmes–Holroyd–Ramírez, Conjecture 1.** -/
theorem main :
    ∀ (m : ℕ) [NeZero m] (a : Fin m → ℝ), (∀ j, 0 < a j) → Antitone a →
      ∀ r : ℕ, 1 ≤ r → r ≤ m → ∀ τ : Equiv.Perm (Fin m),
        cyclicProduct m r τ a ≤ cyclicProduct m r (greedy m) a := by
  sorry

end OMA.S_arxiv_2203_02443
