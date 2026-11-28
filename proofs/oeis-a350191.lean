import OMAStatements.S_oeis_a350191
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

Proof by @wtho704, retained from the complete companion linked in statement
PR #21848 and task-desk DONE #98534:
https://github.com/wtho704/open-math-agents/blob/0318f5a80b9b10231bda81ec558f08d138a142e7/proofs/oeis-a350191.lean
The mathematical proof is unchanged. The conjecture is Václav Kotěšovec's.

On a triangle of side 3m+1 every rook has coordinate sum 3m. In each
direction k different line numbers have sum at least 0+...+(k-1), with
equality exactly for those k initial lines. At k=2m+1 the three bounds
exhaust the whole coordinate sum, so every rook is in the central hexagon.
A two-piece construction attains this number for every m.

The occupied coordinate ranges also fix the center of any congruence
between full placements. This gives equality for the placement symmetries
of A350191 and the board symmetries of A309260.
-/

open Finset OMA.S_oeis_a350191

namespace OMA.TriangularRooks

theorem mem_triangle {p : Cell} {d : ℕ} :
    p ∈ triangle d ↔ p.1 + p.2.1 + p.2.2 = d := by
  simp only [triangle, mem_filter, mem_product, mem_range]
  omega

theorem mem_hexagon {p : Cell} {m : ℕ} :
    p ∈ hexagon m ↔ p ∈ triangle (3 * m) ∧ ∀ i : Fin 3, line i p ≤ 2 * m := by
  simp [hexagon]

theorem mem_placements {s : Placement} {b : Finset Cell} :
    s ∈ placements b ↔ s ⊆ b ∧ Nonattacking s := by
  classical
  simp [placements]

/-- A finite set of natural numbers minimizes the sum for its size exactly
when it is an initial interval. Insert the largest element last. -/
theorem leastSum (s : Finset ℕ) :
    (∑ x ∈ range s.card, x) ≤ ∑ x ∈ s, x ∧
    ((∑ x ∈ s, x) = (∑ x ∈ range s.card, x) → s = range s.card) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hab ih =>
    have hnot : a ∉ s := fun h => (Nat.lt_irrefl a) (hab a h)
    have hsub : s ⊆ range a := fun x hx => mem_range.mpr (hab x hx)
    have hcard : s.card ≤ a := by simpa using card_le_card hsub
    rw [card_insert_of_notMem hnot, sum_insert hnot, sum_range_succ]
    obtain ⟨hle, heq⟩ := ih
    constructor
    · omega
    · intro h
      have ha : a = s.card := by omega
      have hs : s = range s.card := heq (by omega)
      rw [range_add_one, ha]
      exact congrArg (insert s.card) hs

theorem lineStats {s : Placement} (h : Nonattacking s) (i : Fin 3) :
    (∑ x ∈ range s.card, x) ≤ ∑ p ∈ s, line i p ∧
    ((∑ p ∈ s, line i p) = (∑ x ∈ range s.card, x) →
      s.image (line i) = range s.card) := by
  have hmin := leastSum (s.image (line i))
  have himage : (∑ x ∈ s.image (line i), x) = ∑ p ∈ s, line i p :=
    sum_image (h i)
  rwa [card_image_of_injOn (h i), himage] at hmin

theorem total {s : Placement} {m : ℕ} (h : s ⊆ triangle (3 * m)) :
    (∑ p ∈ s, line 0 p) + (∑ p ∈ s, line 1 p) + (∑ p ∈ s, line 2 p) =
      s.card * (3 * m) := by
  rw [← sum_add_distrib, ← sum_add_distrib]
  calc
    _ = ∑ _p ∈ s, 3 * m := by
      apply sum_congr rfl
      intro p hp
      exact mem_triangle.mp (h hp)
    _ = _ := by simp

theorem upperBound {m : ℕ} {s : Placement} (hs : s ∈ placements (triangle (3 * m))) :
    s.card ≤ 2 * m + 1 := by
  obtain ⟨hb, hn⟩ := mem_placements.mp hs
  have ht := total hb
  have h0 := (lineStats hn 0).1
  have h1 := (lineStats hn 1).1
  have h2 := (lineStats hn 2).1
  have hsum : 3 * (∑ x ∈ range s.card, x) ≤ s.card * (3 * m) := by omega
  by_contra! h
  have hprod : s.card * (2 * m) < s.card * (s.card - 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  nlinarith only [hsum, sum_range_id_mul_two s.card, hprod]

private theorem three_axes (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega

/-- In each direction a full placement occupies every line 0 through 2m. -/
theorem fills {m : ℕ} {s : Placement} (hs : s ∈ placements (triangle (3 * m)))
    (hc : s.card = 2 * m + 1) (i : Fin 3) :
    s.image (line i) = range (2 * m + 1) := by
  obtain ⟨hb, hn⟩ := mem_placements.mp hs
  have ht := total hb
  have h0 := (lineStats hn 0).1
  have h1 := (lineStats hn 1).1
  have h2 := (lineStats hn 2).1
  have hd := sum_range_id_mul_two s.card
  have hsub : s.card - 1 = 2 * m := by omega
  rw [hsub] at hd
  have hexact : s.card * (3 * m) = 3 * (∑ x ∈ range s.card, x) := by
    nlinarith only [hd]
  rw [hexact] at ht
  rw [← hc]
  apply (lineStats hn i).2
  rcases three_axes i with rfl | rfl | rfl <;> omega

/-- The y coordinates cycle forward by m, and the z coordinates run down
the evens and then down the odds. -/
def rook (m x : ℕ) : Cell :=
  if x ≤ m then (x, x + m, 2 * m - 2 * x)
  else (x, x - m - 1, 4 * m + 1 - 2 * x)

theorem rook_in_triangle {m x : ℕ} (hx : x ≤ 2 * m) : rook m x ∈ triangle (3 * m) := by
  apply mem_triangle.mpr
  unfold rook
  split <;> simp only <;> omega

theorem rook_injective {m x y : ℕ} (hx : x ≤ 2 * m) (hy : y ≤ 2 * m) (i : Fin 3) :
    line i (rook m x) = line i (rook m y) → x = y := by
  rcases three_axes i with rfl | rfl | rfl <;>
    by_cases h : x ≤ m <;> by_cases k : y ≤ m <;> simp [line, rook, h, k] <;> omega

theorem attainable (m : ℕ) :
    ∃ s ∈ placements (triangle (3 * m)), s.card = 2 * m + 1 := by
  let r := range (2 * m + 1)
  have hx {x : ℕ} (h : x ∈ r) : x ≤ 2 * m := by
    have := mem_range.mp h
    omega
  refine ⟨r.image (rook m), mem_placements.mpr ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨x, hx', rfl⟩ := mem_image.mp hp
    exact rook_in_triangle (hx hx')
  · intro i p hp q hq heq
    obtain ⟨x, hx', rfl⟩ := mem_image.mp hp
    obtain ⟨y, hy', rfl⟩ := mem_image.mp hq
    exact congrArg (rook m) (rook_injective (hx hx') (hx hy') i heq)
  · rw [card_image_of_injOn]
    · exact card_range _
    · intro x hx' y hy' heq
      exact rook_injective (hx hx') (hx hy') 0 (congrArg (line 0) heq)

/-- Forgetting the outer corners changes none of the placements being counted. -/
theorem samePlacements (m : ℕ) :
    maximumPlacements (placements (triangle (3 * m))) =
      ((placements (hexagon m)).filter fun s => s.card = 2 * m + 1) := by
  classical
  ext s
  simp only [maximumPlacements, mem_filter]
  constructor
  · rintro ⟨hs, hmax⟩
    obtain ⟨w, hw, hwcard⟩ := attainable m
    have hup := upperBound hs
    have hlow := hmax w hw
    have hc : s.card = 2 * m + 1 := by omega
    refine ⟨mem_placements.mpr ⟨?_, (mem_placements.mp hs).2⟩, hc⟩
    intro p hp
    refine mem_hexagon.mpr ⟨(mem_placements.mp hs).1 hp, ?_⟩
    intro i
    have h := mem_image_of_mem (line i) hp
    rw [fills hs hc i, mem_range] at h
    omega
  · rintro ⟨hs, hc⟩
    obtain ⟨hb, hn⟩ := mem_placements.mp hs
    refine ⟨mem_placements.mpr ⟨fun p hp => (mem_hexagon.mp (hb hp)).1, hn⟩, ?_⟩
    intro t ht
    rw [hc]
    exact upperBound ht

/-- Matching two full hexagonal placements pins the translation in all
three coordinates, so every ambient congruence is a board symmetry. -/
theorem sameSymmetries {m : ℕ} {s t : Placement} (hs : s ∈ placements (hexagon m))
    (hc : s.card = 2 * m + 1) (ht : t ∈ placements (hexagon m)) :
    congruent s t ↔ hexCongruent m s t := by
  constructor
  · rintro ⟨σ, flip, shift, hmap⟩
    obtain ⟨hb, hn⟩ := mem_placements.mp hs
    have htri : s ∈ placements (triangle (3 * m)) :=
      mem_placements.mpr ⟨fun _ hp => (mem_hexagon.mp (hb hp)).1, hn⟩
    have hshift : shift = fun _ => if flip then ((2 * m : ℕ) : ℤ) else (0 : ℤ) := by
      funext i
      have hit (v : ℕ) (hv : v ≤ 2 * m) : ∃ p ∈ s, line (σ i) p = v := by
        apply mem_image.mp
        rw [fills htri hc, mem_range]
        omega
      obtain ⟨a, ha, ha0⟩ := hit 0 (Nat.zero_le _)
      obtain ⟨b, hbb, hbtop⟩ := hit (2 * m) le_rfl
      obtain ⟨q, hq, hqa⟩ := hmap.1 a ha
      obtain ⟨r, hr, hrb⟩ := hmap.1 b hbb
      have hqv := hqa i
      have hrv := hrb i
      have hqu := (mem_hexagon.mp ((mem_placements.mp ht).1 hq)).2 i
      have hru := (mem_hexagon.mp ((mem_placements.mp ht).1 hr)).2 i
      cases flip <;> simp [ha0, hbtop] at hqv hrv ⊢ <;> omega
    exact ⟨σ, flip, hshift ▸ hmap⟩
  · rintro ⟨σ, flip, hmap⟩
    exact ⟨σ, flip, _, hmap⟩

end OMA.TriangularRooks

open OMA.TriangularRooks

theorem OMA.solution : type_of% @OMA.S_oeis_a350191.main := by
  classical
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hd : 3 * (m + 1) - 2 - 1 = 3 * m := by omega
  simp only [triangleCount, hexCount, hd, samePlacements]
  unfold classCount
  apply congrArg Finset.card
  apply Finset.image_congr
  intro s hs
  obtain ⟨hs, hc⟩ := mem_filter.mp hs
  ext t
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨ht, hct⟩, hrel⟩
    exact ⟨⟨ht, hct⟩, (sameSymmetries hs hc ht).mp hrel⟩
  · rintro ⟨⟨ht, hct⟩, hrel⟩
    exact ⟨⟨ht, hct⟩, (sameSymmetries hs hc ht).mpr hrel⟩

