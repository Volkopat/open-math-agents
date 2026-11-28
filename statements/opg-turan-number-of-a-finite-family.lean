import Mathlib

/-!
# Turán number of a finite family

Source: https://www.openproblemgarden.org/op/turan_number_of_a_finite_family
Credit: @lzvxck

The source: given a family `𝓕` of graphs and an integer `n`, the Turán number `ex(n, 𝓕)` is
the largest integer `m` such that there exists a graph on `n` vertices with `m` edges which
contains no member of `𝓕` as a subgraph. Conjecture: for every finite family `𝓕` of graphs
there exists an `F ∈ 𝓕` such that `ex(n, F) = O(ex(n, 𝓕))`.

This file states that (first) conjecture; the stronger conjecture of Verstraëte recorded on
the page is not part of it. Conventions: graphs are finite and simple. A finite family is
given as `F i` for `i : Fin m` with `m ≥ 1` (the conjecture is void for the empty family), the
graph `F i` living on a finite type `W i`. "Contains as a subgraph" is Mathlib's `⊑`
(`IsContained`: a copy, not necessarily induced). `ex(n, F)` is Mathlib's `extremalNumber`,
and `ex(n, 𝓕)` is defined below the same way (it is `0` if no graph on `n` vertices avoids
`𝓕`). `O(·)` is as `n → ∞`: some constant `C` and threshold `N` with
`ex(n, F) ≤ C · ex(n, 𝓕)` for all `n ≥ N`.
-/

namespace OMA.S_opg_turan_number_of_a_finite_family

open SimpleGraph

/-- `ex(n, 𝓕)`: the largest number of edges of a graph on `n` vertices containing no member
of the family `F` as a subgraph. -/
noncomputable def familyExtremalNumber (n : ℕ) {m : ℕ} {W : Fin m → Type}
    (F : ∀ i, SimpleGraph (W i)) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = k ∧ ∀ i, ¬ (F i).IsContained G}

/-- **Turán number of a finite family (Erdős–Simonovits).** For every nonempty finite family
`𝓕` of finite graphs, some member `F` satisfies `ex(n, F) = O(ex(n, 𝓕))`. -/
theorem main : ∀ (m : ℕ), 1 ≤ m → ∀ (W : Fin m → Type) [∀ i, Fintype (W i)]
    (F : ∀ i, SimpleGraph (W i)),
      ∃ i : Fin m, ∃ C N : ℕ, ∀ n ≥ N,
        extremalNumber n (F i) ≤ C * familyExtremalNumber n F := by
  sorry

end OMA.S_opg_turan_number_of_a_finite_family
