import OMAReductions.R_erdos_132_R1_H2_R1

-- Reduction erdos-132.R1.H2.R1.H2.R1 of step erdos-132.R1.H2.R1.H2
-- Credit: @Pampasgras

/-!
# Few directions per distance: a second structured case of the residual step

For a finite planar set `A`, a point `p` of `A` and a real `d`, write

* `g p d` for the number of points of `A` at distance `d` from `p` (points on a pinned circle),
* `c d` for the number of displacement vectors `x - y` with `x, y` in `A` at distance `d`
  (both orientations are counted, so `c d` is twice the number of directions of `d`).

`H1` is a theorem about arbitrary planar sets, with no assumption on the number of distinct
distances: if `g ≤ G` and `c ≤ L` everywhere and `k * G * L ≤ |A|`, then `A` has at least `k`
rare distances. It covers lattice-like sets, where every distance has few directions, without
any grid structure, and it is a finite form of the trimmed-projection idea in the note of
@TanmayPatil-1 on erdos-132 (note 48541). Sketch: put `t = |A| / L` and let `W` be the largest,
over the directions of the displacements of `A`, of the gap between the `(t+1)`-st highest and
the `(t+1)`-st lowest point in that direction. A displacement longer than `W` occurs at most `2 t`
times, so a distance above `W` has multiplicity at most `t * L ≤ |A|`. In a maximising direction
a `(t+1)`-st highest point has at least `t` partners at distances above `W`, at most `G` of them
at any one distance.

`H2` is the residual step with one more hypothesis, which `H1` makes free: some pinned circle
and some distance satisfy `|A| < k * g p d * c e`. So a configuration that the residual step
still has to handle contains a rich pinned circle or a distance with many directions.
-/

namespace OMA.R_erdos_132_R1_H2_R1_H2_R1

open Finset
open scoped Classical InnerProductSpace
open OMA.S_erdos_132 (pairMultiplicity rareDistances)

/-- A planar set with at most `G` points on every circle centred at one of its points and at most
`L` displacement vectors at every distance has at least `k` rare distances once
`k * G * L ≤ |A|`. -/
def H1 : Prop :=
  ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))) (G L k : ℕ), 2 ≤ A.card →
    (∀ p ∈ A, ∀ d : ℝ, (A.filter (fun q => dist p q = d)).card ≤ G) →
    (∀ d : ℝ, ((A.offDiag.filter (fun p => dist p.1 p.2 = d)).image
      (fun p => p.1 - p.2)).card ≤ L) →
    k * G * L ≤ A.card →
    k ≤ (rareDistances A).card

/-- The residual step, for configurations in which some pinned circle and some distance have
`|A| < k * (points on the circle) * (displacement vectors at the distance)`. -/
def H2 : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
    (A.offDiag.image (fun p => dist p.1 p.2)).card + 2 ≤ A.card/2+k →
    (∀ (o u v : EuclideanSpace ℝ (Fin 2)), LinearIndependent ℝ ![u,v] → 0 ≤ ⟪u,v⟫_ℝ →
      ∀ x y : ℕ → ℝ, StrictMono x → StrictMono y → ∀ r s : ℕ,
      A ≠ (((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v))) →
    (∀ S ⊆ A.offDiag.image (fun p => dist p.1 p.2), 2*k ≤ S.card →
      2*k*(A.card+1) < (A.offDiag.filter (fun p => dist p.1 p.2 ∈ S)).card) →
    (∃ p ∈ A, ∃ d e : ℝ, A.card < k * (A.filter (fun q => dist p q = d)).card *
      ((A.offDiag.filter (fun p => dist p.1 p.2 = e)).image (fun p => p.1 - p.2)).card) →
    k ≤ (rareDistances A).card

theorem main : H1 → H2 → OMA.R_erdos_132_R1_H2_R1.H2 := by
  classical
  intro few rest k
  obtain ⟨N, hN⟩ := rest k
  refine ⟨max N 2, ?_⟩
  intro A large fewDist nongrid dense
  by_cases rich : ∃ p ∈ A, ∃ d e : ℝ, A.card < k * (A.filter (fun q => dist p q = d)).card *
      ((A.offDiag.filter (fun p => dist p.1 p.2 = e)).image (fun p => p.1 - p.2)).card
  · exact hN A ((le_max_left _ _).trans large) fewDist nongrid dense rich
  · push Not at rich
    have two : 2 ≤ A.card := (le_max_right _ _).trans large
    obtain ⟨x0, hx0, y0, hy0, hxy0⟩ := one_lt_card.mp (by omega : 1 < A.card)
    -- the richest pinned circle and the distance with the most displacement vectors
    obtain ⟨z1, hz1, max1⟩ := (A ×ˢ A).exists_max_image
      (fun z => (A.filter (fun q => dist z.1 q = dist z.1 z.2)).card)
      ⟨(x0, y0), mem_product.mpr ⟨hx0, hy0⟩⟩
    obtain ⟨z2, hz2, max2⟩ := A.offDiag.exists_max_image
      (fun z => ((A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2)).image
        (fun p => p.1 - p.2)).card)
      ⟨(x0, y0), mem_offDiag.mpr ⟨hx0, hy0, hxy0⟩⟩
    refine few A _ _ k two ?_ ?_
      (rich z1.1 (mem_product.mp hz1).1 (dist z1.1 z1.2) (dist z2.1 z2.2))
    · intro p hp d
      by_cases hd : ∃ q ∈ A, dist p q = d
      · obtain ⟨q, hq, rfl⟩ := hd
        exact max1 (p, q) (mem_product.mpr ⟨hp, hq⟩)
      · have empty : A.filter (fun q => dist p q = d) = ∅ :=
          filter_eq_empty_iff.mpr fun q hq h => hd ⟨q, hq, h⟩
        rw [empty]
        exact Nat.zero_le _
    · intro d
      by_cases hd : ∃ z ∈ A.offDiag, dist z.1 z.2 = d
      · obtain ⟨z, hz, rfl⟩ := hd
        exact max2 z hz
      · have empty : A.offDiag.filter (fun p => dist p.1 p.2 = d) = ∅ :=
          filter_eq_empty_iff.mpr fun z hz h => hd ⟨z, hz, h⟩
        rw [empty]
        exact Nat.zero_le _

end OMA.R_erdos_132_R1_H2_R1_H2_R1
