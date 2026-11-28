import Mathlib

/-!
# Equidistribution of the products of powers of all elements of a finite group

Source: https://mathoverflow.net/questions/206961
Asked by MathOverflow user Ofir Gorodetsky.

In Hecke's proof of Cauchy's theorem for a finite abelian group `G = {g_1, ..., g_n}`, one
considers the multiset of all products `g_1^{a_1} ⋯ g_n^{a_n}` with `0 ≤ a_i < ord(g_i)` and
uses that it contains every element of `G` equally often. The asker asks whether this step
generalizes to arbitrary finite groups: is it true that this multiset contains each element of
`G` the same number of times?

Translation choices.
* The listing `g_1, ..., g_n` of `G` is a duplicate-free list `l` containing every element of
  `G`; the product is taken in the order of the list, `g_1^{a_1} * (g_2^{a_2} * ⋯)`. The
  asker deliberately leaves the order of the factors open; this file uses the order of the
  listing, as in the abelian proof, and asks for the property for every listing.
* `prods l` is the multiset of all products `g_1^{a_1} ⋯ g_n^{a_n}` with
  `0 ≤ a_i < orderOf g_i`, built recursively from the head of the list.
* `main` is the affirmative answer: for every finite group and every listing of its elements,
  all elements of the group have the same multiplicity in `prods l`.
-/

namespace OMA.S_mo_206961

/-- The multiset of the products `g_1^{a_1} * ⋯ * g_n^{a_n}`, `0 ≤ a_i < orderOf g_i`, for the
list `[g_1, ..., g_n]`. -/
noncomputable def prods {G : Type} [Group G] : List G → Multiset G
  | [] => {1}
  | g :: L => (Multiset.range (orderOf g)).bind (fun k => (prods L).map (fun y => g ^ k * y))

theorem main :
    ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (l : List G), l.Nodup →
      (∀ g : G, g ∈ l) → ∀ x y : G, (prods l).count x = (prods l).count y := by
  sorry

end OMA.S_mo_206961
