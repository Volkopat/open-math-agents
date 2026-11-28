import Mathlib

/-!
# Simultaneous partition of hypergraphs

Source: https://www.openproblemgarden.org/op/simultaneous_partition_of_hypergraphs
Credit: @lzvxck

The source: let `H₁` and `H₂` be two `r`-uniform hypergraphs on the same vertex set `V`. Does
there always exist a partition of `V` into `r` classes `V₁, ..., V_r` such that for both
`i = 1, 2`, at least `r! m_i / r^r - o(m_i)` hyperedges of `H_i` meet each of the classes
`V₁, ..., V_r`? (Here `m_i` is the number of hyperedges of `H_i`.)

The affirmative form is stated. Conventions: hypergraphs are finite, with hyperedges the
`r`-element subsets of `V` in a finset `H`; `r ≥ 2`. A partition into `r` classes is a map
`c : V → Fin r` (class `j` is `c⁻¹ {j}`; classes may be empty, which can only hurt). The
`o(m_i)` term is one function `g` of `m_i` (depending on `r` only) with `g(m) = o(m)` as
`m → ∞`, the same for all hypergraphs.
-/

namespace OMA.S_opg_simultaneous_partition_of_hypergraphs

/-- The number of hyperedges of `H` meeting every class of the partition `c`. -/
def numMeetingAll {V : Type*} {r : ℕ} (c : V → Fin r) (H : Finset (Finset V)) : ℕ :=
  (H.filter fun e => ∀ j : Fin r, ∃ v ∈ e, c v = j).card

/-- **Simultaneous partition of hypergraphs (Kühn, Osthus).** For every `r ≥ 2` there is
`g(m) = o(m)` such that any two `r`-uniform hypergraphs `H₁, H₂` on a common finite vertex set,
with `m₁, m₂` edges, admit a partition into `r` classes in which, for both `i`, at least
`r! m_i / r^r - g(m_i)` hyperedges of `H_i` meet every class. -/
theorem main : ∀ r : ℕ, 2 ≤ r → ∃ g : ℕ → ℝ, g =o[Filter.atTop] (fun m : ℕ => (m : ℝ)) ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (H₁ H₂ : Finset (Finset V)),
      (∀ e ∈ H₁, e.card = r) → (∀ e ∈ H₂, e.card = r) →
        ∃ c : V → Fin r,
          (r.factorial : ℝ) * H₁.card / (r : ℝ) ^ r - g H₁.card ≤ numMeetingAll c H₁ ∧
          (r.factorial : ℝ) * H₂.card / (r : ℝ) ^ r - g H₂.card ≤ numMeetingAll c H₂ := by
  sorry

end OMA.S_opg_simultaneous_partition_of_hypergraphs
