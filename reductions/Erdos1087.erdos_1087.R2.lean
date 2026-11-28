import FormalConjectures.ErdosProblems.«1087»
import Mathlib

-- Reduction Erdos1087.erdos_1087.R2 of Erdős Problem 1087
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
A degenerate four-point set `Q` has two different pairs of points at the same distance. If the
two pairs are disjoint, `Q` is the union of an ordered quadruple `(a, b, c, d)` with
`|ab| = |cd|`. If they share a point, `Q` is an isosceles triple (a three-point set with a
repeated distance) together with one further point. Hence, for every finite `P`,

  `degenerateCount P ≤ E(P) + |P| I(P)`,

where `E(P)` counts the ordered quadruples with `a ≠ b`, `c ≠ d` and `|ab| = |cd|`, and `I(P)`
counts the isosceles triples. This is proved here.

* `H1` is the theorem of Guth and Katz, `E(P) ≪ |P|^3 log |P|`
  (On the Erdős distinct distances problem in the plane, Ann. of Math. 181 (2015)).
* `H2` is the isosceles triangle problem of Erdős and Purdy: `I(P) ≪ |P|^(2+ε)` for every
  `ε > 0`. It is open; the best known exponent is about `2.137` (Pach and Tardos, 2002).

Conversely each isosceles triple lies in `|P| - 3` degenerate four-point sets, so the problem is
equivalent to `H2` once `H1` is known.
-/

open Filter Asymptotics Finset Erdos1087
open scoped EuclideanGeometry Classical

namespace OMA.R_Erdos1087_erdos_1087_R2

/-- Guth and Katz: the number of ordered quadruples `(a, b, c, d)` of points of `P` with
`a ≠ b`, `c ≠ d` and `|ab| = |cd|` is `O(|P|^3 log |P|)`. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℝ²,
    ((((P ×ˢ P) ×ˢ (P ×ˢ P)).filter (fun q : (ℝ² × ℝ²) × (ℝ² × ℝ²) =>
      q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧ dist q.1.1 q.1.2 = dist q.2.1 q.2.2)).card : ℝ) ≤
      C * (P.card : ℝ) ^ 3 * Real.log P.card

/-- The isosceles triangle problem: for every `ε > 0`, a set of `n` points in the plane has
`O(n^(2+ε))` three-point subsets with a repeated distance. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℝ²,
    (((P.powersetCard 3).filter HasRepeatedDistance).card : ℝ) ≤ C * (P.card : ℝ) ^ (2 + ε)

/-- A set with a repeated distance has two different pairs of points at the same distance. -/
theorem pair_of_repeated (Q : Finset ℝ²) (h : HasRepeatedDistance Q) :
    ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q, ∃ d ∈ Q, a ≠ b ∧ c ≠ d ∧ dist a b = dist c d ∧
      ¬ (a = c ∧ b = d) ∧ ¬ (a = d ∧ b = c) := by
  by_contra hno
  let g : Sym2 ℝ² → ℝ := Sym2.lift ⟨fun x y => dist x y, fun x y => dist_comm x y⟩
  have hinj : Set.InjOn g (Q.offDiag.image (Function.uncurry Sym2.mk) : Set (Sym2 ℝ²)) := by
    intro z1 hz1 z2 hz2 hg
    simp only [coe_image, Set.mem_image, mem_coe, mem_offDiag] at hz1 hz2
    obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩ := hz1
    obtain ⟨⟨c, d⟩, ⟨hc, hd, hcd⟩, rfl⟩ := hz2
    dsimp only at ha hb hab hc hd hcd
    simp only [g, Function.uncurry_apply_pair, Sym2.lift_mk] at hg
    by_contra hne
    simp only [Function.uncurry_apply_pair] at hne
    rw [Sym2.eq_iff] at hne
    push Not at hne
    exact hno ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hg, fun h => hne.1 h.1 h.2,
      fun h => hne.2 h.1 h.2⟩
  have himg : distanceSet Q = (Q.offDiag.image (Function.uncurry Sym2.mk)).image g := by
    unfold distanceSet
    rw [Finset.image_image]
    rfl
  unfold HasRepeatedDistance distinctDistances at h
  rw [himg, card_image_of_injOn hinj, Sym2.card_image_offDiag] at h
  exact lt_irrefl _ h

/-- Three distinct points with `|xy| = |xz|` form an isosceles triple. -/
theorem iso_of_apex {x y z : ℝ²} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : dist x y = dist x z) :
    ({x, y, z} : Finset ℝ²).card = 3 ∧ HasRepeatedDistance ({x, y, z} : Finset ℝ²) := by
  have hcard : ({x, y, z} : Finset ℝ²).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  refine ⟨hcard, ?_⟩
  unfold HasRepeatedDistance distinctDistances
  rw [hcard]
  have hsub : distanceSet ({x, y, z} : Finset ℝ²) ⊆ {dist x y, dist y z} := by
    intro r hr
    unfold distanceSet at hr
    simp only [mem_image, mem_offDiag, mem_insert, mem_singleton] at hr
    obtain ⟨⟨p, q⟩, ⟨hp, hq, hpq⟩, rfl⟩ := hr
    dsimp only at hp hq hpq ⊢
    simp only [mem_insert, mem_singleton]
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      simp_all [dist_comm]
  calc (distanceSet ({x, y, z} : Finset ℝ²)).card
      ≤ ({dist x y, dist y z} : Finset ℝ).card := card_le_card hsub
    _ ≤ 2 := card_le_two
    _ < Nat.choose 3 2 := by decide

/-- A four-point subset of `P` containing an isosceles triple is that triple plus a point. -/
theorem mem_iso_image {P Q : Finset ℝ²} (hQP : Q ⊆ P) (hQ4 : Q.card = 4) {x y z : ℝ²}
    (hx : x ∈ Q) (hy : y ∈ Q) (hz : z ∈ Q) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : dist x y = dist x z) :
    Q ∈ (((P.powersetCard 3).filter HasRepeatedDistance) ×ˢ P).image
      (fun t => insert t.2 t.1) := by
  obtain ⟨h3, hrep⟩ := iso_of_apex hxy hxz hyz h
  have hTQ : ({x, y, z} : Finset ℝ²) ⊆ Q := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  obtain ⟨w, hwQ, hwT⟩ := exists_mem_notMem_of_card_lt_card
    (show ({x, y, z} : Finset ℝ²).card < Q.card by rw [h3, hQ4]; norm_num)
  rw [mem_image]
  refine ⟨({x, y, z}, w), ?_, ?_⟩
  · rw [mem_product, mem_filter, mem_powersetCard]
    exact ⟨⟨⟨hTQ.trans hQP, h3⟩, hrep⟩, hQP hwQ⟩
  · apply eq_of_subset_of_card_le (insert_subset hwQ hTQ)
    rw [card_insert_of_notMem hwT, h3, hQ4]

/-- The double count: `degenerateCount P ≤ E(P) + |P| I(P)`. -/
theorem degenerate_le (P : Finset ℝ²) :
    degenerateCount P ≤ (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter (fun q : (ℝ² × ℝ²) × (ℝ² × ℝ²) =>
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧ dist q.1.1 q.1.2 = dist q.2.1 q.2.2)).card +
      P.card * ((P.powersetCard 3).filter HasRepeatedDistance).card := by
  set Qd := ((P ×ˢ P) ×ˢ (P ×ˢ P)).filter (fun q : (ℝ² × ℝ²) × (ℝ² × ℝ²) =>
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧ dist q.1.1 q.1.2 = dist q.2.1 q.2.2) with hQd
  set Iso := (P.powersetCard 3).filter HasRepeatedDistance with hIso
  have hcover : (P.powersetCard 4).filter HasRepeatedDistance ⊆
      Qd.image (fun q => ({q.1.1, q.1.2, q.2.1, q.2.2} : Finset ℝ²)) ∪
      (Iso ×ˢ P).image (fun t => insert t.2 t.1) := by
    intro Q hQ
    rw [mem_filter, mem_powersetCard] at hQ
    obtain ⟨⟨hQP, hQ4⟩, hrep⟩ := hQ
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, heq, hne1, hne2⟩ := pair_of_repeated Q hrep
    by_cases hdisj : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d
    · obtain ⟨hac, had, hbc, hbd⟩ := hdisj
      apply mem_union_left
      rw [mem_image]
      refine ⟨((a, b), (c, d)), ?_, ?_⟩
      · rw [hQd, mem_filter]
        exact ⟨by simp [mem_product, hQP ha, hQP hb, hQP hc, hQP hd], hab, hcd, heq⟩
      · have hsub : ({a, b, c, d} : Finset ℝ²) ⊆ Q := by
          intro w hw
          simp only [mem_insert, mem_singleton] at hw
          rcases hw with rfl | rfl | rfl | rfl <;> assumption
        have hcard : ({a, b, c, d} : Finset ℝ²).card = 4 := by
          rw [card_insert_of_notMem (by simp [hab, hac, had]),
            card_insert_of_notMem (by simp [hbc, hbd]), card_pair hcd]
        exact eq_of_subset_of_card_le hsub (by rw [hcard, hQ4])
    · apply mem_union_right
      rw [not_and_or, not_and_or, not_and_or] at hdisj
      simp only [not_not] at hdisj
      rcases hdisj with rfl | rfl | rfl | rfl
      · have hbd : b ≠ d := fun h => hne1 ⟨rfl, h⟩
        exact mem_iso_image hQP hQ4 ha hb hd hab hcd hbd heq
      · have hbc : b ≠ c := fun h => hne2 ⟨rfl, h⟩
        exact mem_iso_image hQP hQ4 ha hb hc hab (Ne.symm hcd) hbc (by rw [heq, dist_comm])
      · have had : a ≠ d := fun h => hne2 ⟨h, rfl⟩
        exact mem_iso_image hQP hQ4 hb ha hd (Ne.symm hab) hcd had (by rw [dist_comm, heq])
      · have hac : a ≠ c := fun h => hne1 ⟨h, rfl⟩
        exact mem_iso_image hQP hQ4 hb ha hc (Ne.symm hab) (Ne.symm hcd) hac
          (by rw [dist_comm, heq, dist_comm])
  unfold degenerateCount
  calc ((P.powersetCard 4).filter HasRepeatedDistance).card
      ≤ (Qd.image (fun q => ({q.1.1, q.1.2, q.2.1, q.2.2} : Finset ℝ²)) ∪
          (Iso ×ˢ P).image (fun t => insert t.2 t.1)).card := card_le_card hcover
    _ ≤ (Qd.image (fun q => ({q.1.1, q.1.2, q.2.1, q.2.2} : Finset ℝ²))).card +
          ((Iso ×ˢ P).image (fun t => insert t.2 t.1)).card := card_union_le _ _
    _ ≤ Qd.card + (Iso ×ˢ P).card := add_le_add card_image_le card_image_le
    _ = Qd.card + P.card * Iso.card := by rw [card_product, mul_comm]

theorem main : H1 → H2 → type_of% @Erdos1087.erdos_1087 := by
  intro h1 h2 ε hε
  obtain ⟨C1, hC1, hq⟩ := h1
  obtain ⟨C2, hC2, hi⟩ := h2 ε hε
  have hP : ∀ P : Finset ℝ², (degenerateCount P : ℝ) ≤
      (C1 / ε + C2) * (P.card : ℝ) ^ (3 + ε) := by
    intro P
    have h0 : (degenerateCount P : ℝ) ≤ ((((P ×ˢ P) ×ˢ (P ×ˢ P)).filter
        (fun q : (ℝ² × ℝ²) × (ℝ² × ℝ²) => q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
          dist q.1.1 q.1.2 = dist q.2.1 q.2.2)).card : ℝ) +
        (P.card : ℝ) * (((P.powersetCard 3).filter HasRepeatedDistance).card : ℝ) := by
      exact_mod_cast degenerate_le P
    have hq' := hq P
    have hi' := hi P
    set m : ℝ := (P.card : ℝ) with hm
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have hlog : Real.log m ≤ m ^ ε / ε := Real.log_le_rpow_div hm0 hε
    have h3 : m ^ (3 + ε) = m ^ 3 * m ^ ε := by
      rw [Real.rpow_add' hm0 (by linarith)]
      norm_cast
    have h2e : m ^ (2 + ε) = m ^ 2 * m ^ ε := by
      rw [Real.rpow_add' hm0 (by linarith)]
      norm_cast
    have h2' : m * m ^ (2 + ε) = m ^ (3 + ε) := by
      rw [h2e, h3]
      ring
    have hA : C1 * m ^ 3 * Real.log m ≤ C1 / ε * m ^ (3 + ε) := by
      rw [h3]
      calc C1 * m ^ 3 * Real.log m ≤ C1 * m ^ 3 * (m ^ ε / ε) := by gcongr
        _ = C1 / ε * (m ^ 3 * m ^ ε) := by field_simp
    have hB : m * (C2 * m ^ (2 + ε)) = C2 * m ^ (3 + ε) := by rw [← h2']; ring
    calc (degenerateCount P : ℝ) ≤ _ := h0
      _ ≤ C1 * m ^ 3 * Real.log m + m * (C2 * m ^ (2 + ε)) :=
          add_le_add hq' (mul_le_mul_of_nonneg_left hi' hm0)
      _ ≤ C1 / ε * m ^ (3 + ε) + C2 * m ^ (3 + ε) := by
          rw [hB]
          exact add_le_add_left hA _
      _ = (C1 / ε + C2) * m ^ (3 + ε) := by ring
  have hbound : ∀ n : ℕ, (f n : ℝ) ≤ (C1 / ε + C2) * (n : ℝ) ^ (3 + ε) := by
    intro n
    by_cases hne : {m : ℕ | ∃ P : Finset ℝ², P.card = n ∧ degenerateCount P = m}.Nonempty
    · have hbdd : BddAbove {m : ℕ | ∃ P : Finset ℝ², P.card = n ∧ degenerateCount P = m} :=
        ⟨n.choose 4, by rintro m ⟨Q, hQ, rfl⟩; exact hQ ▸ degenerateCount_le Q⟩
      obtain ⟨P, hPn, hPf⟩ := Nat.sSup_mem hne hbdd
      unfold f
      rw [← hPf, ← hPn]
      exact hP P
    · unfold f
      rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
      have : (0 : ℝ) ≤ (C1 / ε + C2) * (n : ℝ) ^ (3 + ε) := by positivity
      simpa using this
  refine Asymptotics.IsBigO.of_bound (C1 / ε + C2) (Eventually.of_forall fun n => ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact hbound n

end OMA.R_Erdos1087_erdos_1087_R2
