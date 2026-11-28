import Mathlib

/-!
# Sidon sets in finite groups

Source: https://mathoverflow.net/questions/350448
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `G` be a group and `S ⊆ G`. Call `S` a Sidon subset iff for all quadruples `(a, b, c, d)` of
distinct elements of `S` we have `a b ≠ c d`. Let `Sid(G)` be the maximal cardinality of a Sidon
subset of `G`. Do there exist `0 < c < C < ∞` such that `c ≤ Sid(G) / √|G| ≤ C` for every finite
group `G`?

Conventions:
* distinct means pairwise distinct: `a, b, c, d` are four different elements of `S`, exactly as in
  the source; products are taken in the given (not necessarily commutative) order;
* `Sid G` is the largest cardinality of a Sidon `Finset` of `G`, written as `sSup` of the set of
  attained cardinalities; that set contains `0` and is bounded by `Fintype.card G`, so `sSup` is
  a genuine maximum (no junk value);
* every finite group is isomorphic to one in `Type`, so quantifying over `G : Type` loses nothing;
* the statement is the affirmative answer, with both constants as in the question (the source
  remarks that the upper constant exists; the open part is the lower constant `c`).
-/

namespace OMA.S_mo_350448

/-- `S` is a Sidon subset of `G`: no two products `a * b`, `c * d` of four pairwise distinct
elements of `S` coincide. -/
def IsSidonSubset {G : Type} [Group G] (S : Finset G) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → a * b ≠ c * d

/-- `Sid G`: the maximal cardinality of a Sidon subset of the finite group `G`. -/
noncomputable def Sid (G : Type) [Group G] [Fintype G] : ℕ :=
  sSup {k : ℕ | ∃ S : Finset G, S.card = k ∧ IsSidonSubset S}

/-- There are constants `0 < c < C` with `c ≤ Sid(G) / √|G| ≤ C` for every finite group `G`. -/
theorem main : ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ (G : Type) [Group G] [Fintype G],
      c ≤ (Sid G : ℝ) / Real.sqrt (Fintype.card G) ∧
        (Sid G : ℝ) / Real.sqrt (Fintype.card G) ≤ C := by
  sorry

end OMA.S_mo_350448
