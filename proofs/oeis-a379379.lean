import OMAStatements.S_oeis_a379379
import Mathlib.Data.List.SplitBy
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Four formulas for A379379

Match the actual heads of the blocks with the gaps between consecutive
divisors. As in the divisor-block argument for A386993, an even divisor
has its half among the earlier divisors, and cannot start a new block.
Finally partition all odd divisors and all adjacent pairs to obtain the
two complementary sums.

Source: https://oeis.org/A379379. Credit: @Solitude1312
-/

open OMA.S_oeis_a379379
open scoped Classical

namespace OMA.A379379

private abbrev gap (b d : ℕ) := decide (2*b < d)
private abbrev small (b d : ℕ) := decide (d ≤ 2*b)
private abbrev starts (D : Finset ℕ) (d : ℕ) := ∀ j ∈ D, j < d → 2*j < d

private lemma adjacent_cons (f : ℕ → ℕ → Bool) (b d : ℕ) (xs : List ℕ) :
    adjacentSum f b (d::xs) = (if f b d then d else 0) + adjacentSum f d xs := by
  cases h : f b d <;> simp [adjacentSum, h]

private def sumHeads (ls : List (List ℕ)) := (ls.map (fun r => r.headD 0)).sum

private lemma loop_heads (xs : List ℕ) (b : ℕ) (run : List ℕ) (acc : List (List ℕ)) :
    sumHeads (List.splitBy.loop small xs b run acc) =
      sumHeads acc + (b::run).getLast?.getD 0 + adjacentSum gap b xs := by
  induction xs generalizing b run acc with
  | nil => simp [List.splitBy.loop, sumHeads, adjacentSum, List.map_reverse, Nat.add_comm, List.getLast?_cons]
  | cons d xs ih =>
    rw [List.splitBy.loop, adjacent_cons]
    by_cases h : d ≤ 2*b
    · simp [small, gap, h, not_lt_of_ge h, ih, Nat.add_assoc]
    · have hlt : 2*b < d := by omega
      simp only [show small b d = false by simp [small,h], show gap b d = true by simp [gap,hlt], ↓reduceIte]
      rw [ih]
      simp [sumHeads, List.getLast?_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma blocks_eq_gaps (xs : List ℕ) (hp : ∀ d ∈ xs, 0 < d) :
    sumHeads (xs.splitBy small) = adjacentSum gap 0 xs := by
  cases xs with
  | nil => rfl
  | cons d xs =>
    have hd := hp d (by simp)
    rw [List.splitBy, loop_heads, adjacent_cons]
    simp [gap, hd, sumHeads]

private lemma remaining_sum (D : Finset ℕ) (xs : List ℕ) (b : ℕ) (hb : b ∈ D)
    (inside : ∀ j ∈ xs, j ∈ D) (cover : ∀ j ∈ D, j ≤ b ∨ j ∈ xs)
    (order : (b :: xs).Pairwise (· < ·)) :
    adjacentSum gap b xs = (xs.filter fun d => decide (starts D d)).sum := by
  induction xs generalizing b with
  | nil => rfl
  | cons d tail ih =>
    obtain ⟨hbefore, htail⟩ := List.pairwise_cons.mp order
    have hbd : b < d := hbefore d (by simp)
    have hd : d ∈ D := inside d (by simp)
    have hinside : ∀ j ∈ tail, j ∈ D := fun j hj => inside j (by simp [hj])
    have hcover : ∀ j ∈ D, j ≤ d ∨ j ∈ tail := by
      intro j hj
      rcases cover j hj with h | h
      · exact Or.inl (by omega)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl le_rfl
        · exact Or.inr h
    have criterion : starts D d ↔ 2*b < d := by
      constructor
      · intro hs
        exact hs b hb hbd
      · intro h j hj hjd
        rcases cover j hj with hle | hmem
        · omega
        · rcases List.mem_cons.mp hmem with rfl | ht
          · omega
          · have := (List.pairwise_cons.mp htail).1 j ht
            omega
    rw [adjacent_cons, ih d hd hinside hcover htail, List.filter_cons]
    by_cases h : 2*b < d
    · simp [gap, h]
      rw [if_pos (criterion.mpr h), List.sum_cons]
    · simp [gap, h]
      rw [if_neg (fun hs => h (criterion.mp hs))]

private lemma ordered_sum (D : Finset ℕ) (pos : ∀ d ∈ D, 0 < d) :
    adjacentSum gap 0 D.sort = (D.sort.filter fun d => decide (starts D d)).sum := by
  let xs := D.sort
  have hsort : xs.Pairwise (· < ·) := D.sortedLT_sort.pairwise
  have mem (j : ℕ) : j ∈ xs ↔ j ∈ D := by simp [xs]
  change adjacentSum gap 0 xs = (xs.filter _).sum
  cases hl : xs with
  | nil => rfl
  | cons d tail =>
    rw [hl] at hsort mem
    have hd : d ∈ D := (mem d).mp (by simp)
    have hi : ∀ j ∈ tail, j ∈ D := fun j hj => (mem j).mp (by simp [hj])
    have hc : ∀ j ∈ D, j ≤ d ∨ j ∈ tail := by
      intro j hj
      rcases List.mem_cons.mp ((mem j).mpr hj) with rfl | h
      · exact Or.inl le_rfl
      · exact Or.inr h
    have hs : starts D d := by
      intro j hj hjd
      rcases List.mem_cons.mp ((mem j).mpr hj) with rfl | h
      · omega
      · have := (List.pairwise_cons.mp hsort).1 j h
        omega
    rw [adjacent_cons, remaining_sum D tail d hd hi hc hsort, List.filter_cons]
    simp [gap, pos d hd]
    rw [if_pos hs, List.sum_cons]

private lemma start_iff (n d : ℕ) (hd : d ∈ n.divisors) :
    starts n.divisors d ↔ eligible n.divisors d := by
  have hpos := Nat.pos_of_mem_divisors hd
  constructor
  · intro hs
    refine ⟨Nat.not_even_iff_odd.mp ?_, fun j hj hlt => (hs j hj hlt).le⟩
    rintro ⟨u, hu⟩
    have hud : u ∣ d := ⟨2, by omega⟩
    obtain ⟨hdn, hn⟩ := Nat.mem_divisors.mp hd
    have hum : u ∈ n.divisors := Nat.mem_divisors.mpr ⟨hud.trans hdn, hn⟩
    have := hs u hum (by omega)
    omega
  · rintro ⟨⟨t, ht⟩, hw⟩ j hj hlt
    have := hw j hj hlt
    omega

private lemma eligible_eq_gap (n : ℕ) : a n = adjacentSum gap 0 n.divisors.sort := by
  rw [ordered_sum n.divisors (fun _ hd => Nat.pos_of_mem_divisors hd)]
  unfold a
  apply congrArg List.sum
  apply List.filter_congr
  intro d hd
  simp only [decide_eq_decide]
  exact (start_iff n d ((Finset.mem_sort _).mp hd)).symm

private lemma odd_partition (D : Finset ℕ) (xs : List ℕ) :
    (xs.filter fun d => decide (eligible D d)).sum +
      (xs.filter fun d => decide (excluded D d)).sum =
      (xs.filter fun d => decide (Odd d)).sum := by
  induction xs with
  | nil => rfl
  | cons d xs ih =>
    by_cases ho : Odd d
    · by_cases hall : ∀ j ∈ D, j < d → 2*j ≤ d
      · have hyes : eligible D d := ⟨ho, hall⟩
        have hno : ¬ excluded D d := by
          rintro ⟨_, j, hj, hlt, hcut⟩
          have := hall j hj hlt
          omega
        simp [hyes, hno, ho, Nat.add_assoc, ih]
      · have hno : ¬ eligible D d := fun h => hall h.2
        have hyes : excluded D d := by
          push Not at hall
          exact ⟨ho, hall⟩
        simp [hyes, hno, ho]
        omega
    · have hno : ¬ eligible D d := fun h => ho h.1
      have hnone : ¬ excluded D d := fun h => ho h.1
      simpa [hno, hnone, ho] using ih

private lemma adjacent_partition (xs : List ℕ) (b : ℕ) :
    adjacentSum gap b xs + adjacentSum small b xs = xs.sum := by
  induction xs generalizing b with
  | nil => rfl
  | cons d xs ih =>
    rw [adjacent_cons, adjacent_cons, List.sum_cons]
    have hh := ih d
    by_cases h : d ≤ 2*b
    · simp [gap, small, h, not_lt_of_ge h]
      omega
    · simp [gap, small, h, show 2*b < d by omega, Nat.add_assoc, hh]

end OMA.A379379

open OMA.A379379

theorem OMA.solution : type_of% @OMA.S_oeis_a379379.main := by
  intro n _
  have hgap := eligible_eq_gap n
  have hblocks : blockSum n = adjacentSum gap 0 n.divisors.sort :=
    blocks_eq_gaps _ (fun _ h => Nat.pos_of_mem_divisors ((Finset.mem_sort _).mp h))
  have ho : a n + excludedSum n = oddSum n := by
    unfold a excludedSum oddSum
    exact odd_partition n.divisors (n.divisors.sort (· ≤ ·))
  have hd := adjacent_partition n.divisors.sort 0
  have hlast : a n = n.divisors.sort.sum - adjacentSum small 0 n.divisors.sort := by
    rw [hgap, ← hd]
    omega
  exact ⟨hgap.trans hblocks.symm, hgap, by omega, hlast⟩
