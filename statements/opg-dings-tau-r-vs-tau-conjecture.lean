import Mathlib

/-!
# Ding's tau_r vs. tau conjecture

Source: https://www.openproblemgarden.org/op/dings_tau_r_vs_tau_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture: let `r ≥ 2` and let `H` be a minor-minimal clutter with `τ_r(H)/r < τ(H)`.
Then `H` has a `J_k` minor for some `k ≥ 2`, or `H` has Lehman's property.

Conventions.
* A clutter is a finite ground set with a family of pairwise incomparable subsets (edges).
* `τ_r(H)` is the minimum size of a multiset of vertices meeting every edge at least `r`
  times. (The source says "largest", which is a slip: with "largest" the quantity is
  unbounded, and the source's own remark `τ_r(H) ≤ r τ(H)` fixes the minimum reading.)
  Minimum over the empty set is `0` (Lean's `sInf ∅`); this only occurs when `∅` is an edge,
  where the hypothesis `τ_r < r τ` then fails, matching `∞ < ∞` being false.
* `τ_r/r < τ` is written `τ_r < r * τ`.
* Minors: `H \ X / Y` for disjoint `X, Y ⊆ V(H)` has ground set `V(H) \ (X ∪ Y)` and edges
  the inclusion-minimal sets among `{A \ Y : A ∈ E(H), A ∩ X = ∅}`; proper iff `X ∪ Y ≠ ∅`.
  Minor-minimal means `H` has the property and no proper minor does.
* `b(H)` (blocker) has the same ground set and edges the inclusion-minimal transversals.
* `J_k` has vertices `{0, …, k}` and edges `{0,i}` (`1 ≤ i ≤ k`) and `{1, …, k}`. (The source
  lists `{1,2}, …, {0,k}, {0,1,…,k}`, garbled; this is the standard degenerate projective
  plane, Lehman / Cornuéjols "Combinatorial Optimization: Packing and Covering".)
* Lehman's property is transcribed as in the source, with `n = |V(H)|`, `s = τ(H)`,
  `r' = τ(b(H))`.
-/

namespace OMA.S_opg_dings_tau_r_vs_tau_conjecture

open Finset

/-- A clutter on vertices drawn from `V`. -/
structure Clutter (V : Type) [DecidableEq V] where
  ground : Finset V
  edges : Finset (Finset V)
  sub : ∀ A ∈ edges, A ⊆ ground
  antichain : ∀ A ∈ edges, ∀ B ∈ edges, A ⊆ B → A = B

variable {V : Type} [DecidableEq V]

/-- The inclusion-minimal members of a family. -/
def minimals (F : Finset (Finset V)) : Finset (Finset V) :=
  F.filter fun A => ∀ B ∈ F, B ⊆ A → B = A

/-- The minor `H \ X / Y`. -/
def minor (H : Clutter V) (X Y : Finset V) : Clutter V where
  ground := H.ground \ (X ∪ Y)
  edges := minimals ((H.edges.filter fun A => Disjoint A X).image fun A => A \ Y)
  sub := by
    intro A hA
    simp only [minimals, mem_filter, mem_image] at hA
    obtain ⟨⟨B, ⟨hB, hBX⟩, rfl⟩, -⟩ := hA
    intro v hv
    simp only [mem_sdiff, mem_union] at hv ⊢
    exact ⟨H.sub B hB hv.1, fun h => h.elim (fun hx => disjoint_left.mp hBX hv.1 hx) hv.2⟩
  antichain := by
    intro A hA B hB hAB
    simp only [minimals, mem_filter] at hA hB
    exact hB.2 A hA.1 hAB

/-- The blocker `b(H)`: inclusion-minimal transversals. -/
def blocker (H : Clutter V) : Clutter V where
  ground := H.ground
  edges := minimals (H.ground.powerset.filter fun T => ∀ A ∈ H.edges, (T ∩ A).Nonempty)
  sub := by
    intro A hA
    simp only [minimals, mem_filter, mem_powerset] at hA
    exact hA.1.1
  antichain := by
    intro A hA B hB hAB
    simp only [minimals, mem_filter] at hA hB
    exact hB.2 A hA.1 hAB

/-- `τ_r(H)`: minimum size of a multiset of ground vertices meeting every edge `≥ r` times. -/
noncomputable def tauR (r : ℕ) (H : Clutter V) : ℕ :=
  sInf {t | ∃ w : V → ℕ, (∀ v, v ∉ H.ground → w v = 0) ∧
    (∀ A ∈ H.edges, r ≤ ∑ v ∈ A, w v) ∧ ∑ v ∈ H.ground, w v = t}

/-- `τ(H) = τ_1(H)`. -/
noncomputable def tau (H : Clutter V) : ℕ := tauR 1 H

/-- The property in the conjecture: `τ_r(H) / r < τ(H)`. -/
def Gap (r : ℕ) (H : Clutter V) : Prop := tauR r H < r * tau H

/-- `H` is a minor-minimal clutter with `τ_r(H) / r < τ(H)`. -/
def MinorMinimalGap (r : ℕ) (H : Clutter V) : Prop :=
  Gap r H ∧ ∀ X Y : Finset V, X ⊆ H.ground → Y ⊆ H.ground → Disjoint X Y →
    (X ∪ Y).Nonempty → ¬ Gap r (minor H X Y)

/-- The edges of the degenerate projective plane `J_k` on `Fin (k+1)`. -/
def jEdges (k : ℕ) : Set (Finset (Fin (k + 1))) :=
  {A | (∃ i : Fin (k + 1), i ≠ 0 ∧ A = {0, i}) ∨ A = univ.erase 0}

/-- `H` has a minor isomorphic to `J_k`. -/
def HasJMinor (H : Clutter V) (k : ℕ) : Prop :=
  ∃ X Y : Finset V, X ⊆ H.ground ∧ Y ⊆ H.ground ∧ Disjoint X Y ∧
    ∃ f : Fin (k + 1) → V, Function.Injective f ∧
      (∀ i, f i ∈ (minor H X Y).ground) ∧ (∀ v ∈ (minor H X Y).ground, ∃ i, f i = v) ∧
      ∀ A : Finset (Fin (k + 1)), A ∈ jEdges k ↔ A.image f ∈ (minor H X Y).edges

/-- Lehman's property, as stated in the source. -/
def LehmanProperty (H : Clutter V) : Prop :=
  let n := H.ground.card
  let s := tau H
  let r := tau (blocker H)
  n < r * s ∧
  ∃ A B : Fin n → Finset V,
    Function.Injective A ∧ (∀ X, X ∈ H.edges ↔ ∃ i, A i = X) ∧
    Function.Injective B ∧ (∀ X, X ∈ (blocker H).edges ↔ ∃ i, B i = X) ∧
    (∀ i, (A i).card = r) ∧
    (∀ i, (B i).card = s) ∧
    (∀ i, (A i ∩ B i).card + n = r * s + 1) ∧
    (∀ i j, i ≠ j → (A i ∩ B j).card = 1) ∧
    ∀ v ∈ H.ground,
      (univ.filter fun i => v ∈ A i).card = r ∧
      (univ.filter fun i => v ∈ B i).card = s ∧
      (univ.filter fun i => v ∈ A i ∩ B i).card + n = r * s + 1

/-- Ding's conjecture. -/
theorem main :
    ∀ (V : Type) [DecidableEq V] (r : ℕ), 2 ≤ r → ∀ H : Clutter V,
      MinorMinimalGap r H → (∃ k, 2 ≤ k ∧ HasJMinor H k) ∨ LehmanProperty H := by
  sorry

end OMA.S_opg_dings_tau_r_vs_tau_conjecture
