import Mathlib

/-!
# Erdős Problem 1218

Source: https://www.erdosproblems.com/1218
Credit: @mgv27

Assume the Generalised Continuum Hypothesis and let $\beta=\omega_{\omega+1}$. Is it true
that\[\aleph_{\beta+1} \not\to (\aleph_\beta,4,\ldots,4)^3\](where there are countably infinite
many copies of $4$)?

Formalization notes:
* GCH is a hypothesis of `main`: `2 ^ ℵ_o = ℵ_{o+1}` for every ordinal `o` (cardinals and
  ordinals in universe `0`).
* `β = ω_{ω+1}` is the initial ordinal of `ℵ_{ω+1}`, i.e. `(ℵ_(ω+1)).ord`.
* The negative partition relation is: for a set `V` of size `ℵ_{β+1}` there is a colouring
  `c` of the 3-element subsets of `V` by `ℕ` (colour `0` plays the role of `ℵ_β`, colours
  `1, 2, …` the countably many copies of `4`) with no colour-`0`-homogeneous set of size
  `ℵ_β` and, for each colour `k ≥ 1`, no colour-`k`-homogeneous set of size `4`.
* The colouring is a function on all finsets of `V`; only its values on 3-element finsets
  matter. A set `s` is homogeneous of colour `i` if every 3-element finset contained in `s`
  gets colour `i`.
-/

namespace OMA.S_erdos_1218

open Cardinal Ordinal

/-- The Generalised Continuum Hypothesis: `2 ^ ℵ_o = ℵ_{o+1}` for all ordinals `o`. -/
def GCH : Prop :=
  ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ aleph o = aleph (Order.succ o)

/-- `s` is homogeneous of colour `i` for the colouring `c` of 3-element subsets. -/
def Homogeneous {V : Type} (c : Finset V → ℕ) (s : Set V) (i : ℕ) : Prop :=
  ∀ t : Finset V, (↑t : Set V) ⊆ s → t.card = 3 → c t = i

/-- `β = ω_{ω+1}`. -/
noncomputable def β : Ordinal.{0} := (aleph (ω + 1)).ord

/-- Erdős Problem 1218: under GCH, `ℵ_{β+1} ↛ (ℵ_β, 4, 4, …)^3` with `β = ω_{ω+1}`. -/
theorem main : GCH → ∀ V : Type, #V = aleph (Order.succ β) →
    ∃ c : Finset V → ℕ,
      (∀ s : Set V, #s = aleph β → ¬ Homogeneous c s 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ t : Finset V, t.card = 4 → ¬ Homogeneous c ↑t k) := by
  sorry

end OMA.S_erdos_1218
