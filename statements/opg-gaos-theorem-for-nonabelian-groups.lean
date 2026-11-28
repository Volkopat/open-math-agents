import Mathlib

/-!
# Gao's theorem for nonabelian groups

Source: https://www.openproblemgarden.org/op/gaos_theorem_for_nonabelian_groups
Credit: @ishaanzee

For every finite multiplicative group `G`, let `s(G)` (`s'(G)`) denote the smallest integer `m`
so that every sequence of `m` elements of `G` has a subsequence of length `> 0` (length `|G|`)
which has product equal to `1` in some order.

**Conjecture** (M. DeVos). `s'(G) = s(G) + |G| - 1` for every finite group `G`.

Gao's theorem is the abelian case; the inequality `s'(G) ≥ s(G) + |G| - 1` holds for every
finite group.

Formalization:
* A sequence of `m` elements is `a : Fin m → G`. A subsequence of length `ℓ`, multiplied in some
  order, is given by an injective `j : Fin ℓ → Fin m` (distinct positions, listed in the chosen
  order); its product in that order is `(List.ofFn fun i => a (j i)).prod`.
* `s(G)` and `s'(G)` are the least elements (`sInf`) of the sets of admissible lengths `m`. Both
  sets are nonempty (`s(G) ≤ |G|` by the pigeonhole argument on partial products, and
  `s'(G) ≤ 2|G| - 1` by Olson's theorem), so `sInf` is the minimum.
-/

namespace OMA.S_opg_gaos_theorem_for_nonabelian_groups

/-- Some `ℓ` distinct terms of `a`, multiplied in some order, have product `1`. -/
def HasProdOneSubseq {G : Type*} [Group G] {m : ℕ} (a : Fin m → G) (ℓ : ℕ) : Prop :=
  ∃ j : Fin ℓ → Fin m, Function.Injective j ∧ (List.ofFn fun i => a (j i)).prod = 1

/-- `s(G)`: the least `m` such that every sequence of `m` elements of `G` has a nonempty
subsequence with product `1` in some order. -/
noncomputable def s (G : Type*) [Group G] : ℕ :=
  sInf {m : ℕ | ∀ a : Fin m → G, ∃ ℓ, 0 < ℓ ∧ HasProdOneSubseq a ℓ}

/-- `s'(G)`: the least `m` such that every sequence of `m` elements of `G` has a subsequence of
length `|G|` with product `1` in some order. -/
noncomputable def s' (G : Type*) [Group G] [Fintype G] : ℕ :=
  sInf {m : ℕ | ∀ a : Fin m → G, HasProdOneSubseq a (Fintype.card G)}

/-- **DeVos' conjecture**: `s'(G) = s(G) + |G| - 1` for every finite group `G`. -/
theorem main : ∀ (G : Type) [Group G] [Fintype G], s' G = s G + Fintype.card G - 1 := by
  sorry

end OMA.S_opg_gaos_theorem_for_nonabelian_groups
