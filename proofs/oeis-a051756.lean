import OMAStatements.S_oeis_a051756
import Mathlib

/-!
# Maximum number of queens with exactly three attackers

For each n ≥ 2 the maximum is twice the integer part of (6n−2)/5.
The upper bound counts the two ends of every occupied row, column and
diagonal. The lower bound uses one pattern for each residue modulo five.
The patterns place a fixed number of queens near the corners and twelve
additional queens for every five rows and columns added to the middle.

A point coordinate is either a fixed distance from an edge or one of five
residues in the middle strip. To test a ray from a given point, intersect
its line with each candidate strip. The line key along a strip is constant
or changes by ±5 per step. In the latter case at most one index can match.
In the former case test the appropriate endpoint. For the first, last and
interior indices of a growing strip, each feasibility condition reduces to
affine inequalities in two arbitrary nonnegative integers. Checking the
constant and both coefficients yields bounds valid at every board size.
The lower and upper bounds agree on all eight rays and give degree three.

The finite placements through n=32 are transcribed from Alexander D. Healy's
illustrations in OEIS A051756. The periodic patterns were found by integer
constraint search. All witnesses and arithmetic certificates are checked
by the Lean kernel.

Sources: Jud McCranie and Alexander D. Healy, https://oeis.org/A051756 and
https://oeis.org/A051756/a051756_1.pdf.
-/

/-! The number of pairs of adjacent queens on a nonempty line is one less than
the number of queens on that line. Summing this identity gives the upper bound
recorded by Jud McCranie in A051756. -/

namespace OMA.ThreeAttackers
open Finset OMA.S_oeis_a051756

lemma count_side {α β γ : Type} [DecidableEq α] [DecidableEq β] [LinearOrder γ]
    (s : Finset α) (f : α → β) (r : α → γ) (hr : Function.Injective r) :
    (∑ p ∈ s, if ∃ q ∈ s, f q = f p ∧ r q < r p then 1 else 0) +
      (s.image f).card = s.card := by
  classical
  let earlier (p : α) := ∃ q ∈ s, f q = f p ∧ r q < r p
  let minima := s.filter (fun p => ¬ earlier p)
  have inj : Set.InjOn f (minima : Set α) := by
    intro p hp q hq he
    obtain ⟨hps,hp'⟩ := mem_filter.mp hp
    obtain ⟨hqs,hq'⟩ := mem_filter.mp hq
    apply hr
    apply le_antisymm
    · exact le_of_not_gt (fun h => hp' ⟨q,hqs,he.symm,h⟩)
    · exact le_of_not_gt (fun h => hq' ⟨p,hps,he,h⟩)
  have im : minima.image f = s.image f := by
    apply Subset.antisymm (image_subset_image (filter_subset _ _))
    intro b hb
    obtain ⟨x,hxs,rfl⟩ := mem_image.mp hb
    let t := s.filter (fun p => f p = f x)
    have hx : x ∈ t := mem_filter.mpr ⟨hxs,rfl⟩
    obtain ⟨p,hp,hmin⟩ := t.exists_min_image r ⟨x,hx⟩
    obtain ⟨hps,hpx⟩ := mem_filter.mp hp
    refine mem_image.mpr ⟨p,mem_filter.mpr ⟨hps,?_⟩,hpx⟩
    rintro ⟨q,hqs,hqp,hlt⟩
    exact (not_lt_of_ge (hmin q (mem_filter.mpr ⟨hqs,hqp.trans hpx⟩))) hlt
  have hcard : (s.image f).card = minima.card := im ▸ card_image_of_injOn inj
  change (∑ p ∈ s, if earlier p then 1 else 0) + _ = _
  rw [← sum_filter,hcard]
  simpa [minima] using Finset.card_filter_add_card_filter_not (s := s) earlier

private lemma injrank {n : ℕ} : Function.Injective (rank (n := n)) := by
  intro p q h
  apply finProdFinEquiv.injective
  apply Fin.ext
  simpa [finProdFinEquiv,rank, Nat.mul_comm,Nat.add_comm] using h

theorem one_axis {n : ℕ} (s : Finset (Square n)) (a : Axis) :
    (∑ p ∈ s, visible s p a) + 2*(s.image (line a)).card = 2*s.card := by
  have h1 := count_side s (line a) rank injrank
  have h2 := count_side (γ := ℕᵒᵈ) s (line a) rank injrank
  simp only [visible,sum_add_distrib]
  change (∑ p ∈ s, if ∃ q ∈ s, line a q = line a p ∧ rank p < rank q then 1 else 0) + _ = _ at h2
  omega

theorem upper {n : ℕ} (hn : 2 ≤ n) {s : Finset (Square n)} (hs : valid s) :
    s.card ≤ 2*((6*n-2)/5) := by
  let cap : Axis → ℕ := fun a => match a with
    | .row | .column => n
    | .ascending | .descending => 2*n-1
  have lim (a : Axis) : (s.image (line a)).card ≤ cap a := by
    have sub : s.image (line a) ⊆ range (cap a) := by
      intro k hk
      obtain ⟨p,_,rfl⟩ := mem_image.mp hk
      have := p.1.isLt
      have := p.2.isLt
      cases a <;> simp [line,cap] <;> omega
    simpa using card_le_card sub
  have count := sum_congr (s₁ := s) rfl hs
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id] at count
  have hr := one_axis s .row
  have hc := one_axis s .column
  have hu := one_axis s .ascending
  have hd := one_axis s .descending
  have r := lim .row
  have c := lim .column
  have u := lim .ascending
  have d := lim .descending
  dsimp [cap] at r c u d
  omega

end OMA.ThreeAttackers

open Finset OMA.S_oeis_a051756
namespace OMA.ThreeWitnesses

private theorem certify {n : ℕ} (board : List (Square n)) (k : ℕ)
    (nodup : board.Nodup) (len : board.length = k)
    (check : let side (p : Square n) (a : Axis) := fun (earlier : Bool) =>
        (board.any fun q => decide (line a q = line a p) &&
          (if earlier then decide (rank q < rank p) else decide (rank p < rank q))).toNat
      board.all (fun p => decide (
        side p .row true + side p .row false +
        side p .column true + side p .column false +
        side p .ascending true + side p .ascending false +
        side p .descending true + side p .descending false = 3)) = true) :
    ∃ s : Finset (Square n), valid s ∧ s.card = k := by
  refine ⟨board.toFinset, ?_, ?_⟩
  · intro p hp
    have h := List.all_eq_true.mp check p (List.mem_toFinset.mp hp)
    simp only [decide_eq_true_eq] at h
    have earlier (a : Axis) :
        ((board.any fun q => decide (line a q = line a p) && decide (rank q < rank p))).toNat =
        (if ∃ q ∈ board.toFinset, line a q = line a p ∧ rank q < rank p then 1 else 0) := by
      have flag : (board.any fun q => decide (line a q = line a p) && decide (rank q < rank p)) =
          decide (∃ q ∈ board, line a q = line a p ∧ rank q < rank p) := by
        apply Bool.eq_iff_iff.mpr
        simp [List.any_eq_true]
      rw [flag]
      by_cases w : ∃ q ∈ board, line a q = line a p ∧ rank q < rank p <;> simp [w]
    have later (a : Axis) :
        ((board.any fun q => decide (line a q = line a p) && decide (rank p < rank q))).toNat =
        (if ∃ q ∈ board.toFinset, line a q = line a p ∧ rank p < rank q then 1 else 0) := by
      have flag : (board.any fun q => decide (line a q = line a p) && decide (rank p < rank q)) =
          decide (∃ q ∈ board, line a q = line a p ∧ rank p < rank q) := by
        apply Bool.eq_iff_iff.mpr
        simp [List.any_eq_true]
      rw [flag]
      by_cases w : ∃ q ∈ board, line a q = line a p ∧ rank p < rank q <;> simp [w]
    simp only [if_true,Bool.false_eq_true,if_false,earlier,later] at h
    dsimp only [visible]
    omega
  · simpa [List.toFinset_card_of_nodup nodup] using len

set_option maxRecDepth 20000 in
def W : (n : ℕ) → List (Square n)
  | 2 => [(0,0),(0,1),(1,0),(1,1)]
  | 3 => [(0,0),(0,2),(1,0),(1,2),(2,0),(2,2)]
  | 4 => [(0,0),(0,1),(0,2),(0,3),(3,0),(3,1),(3,2),(3,3)]
  | 5 => [(0,0),(0,4),(1,0),(2,0),(2,1),(2,3),(2,4),(3,4),(4,0),(4,4)]
  | 6 => [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5)]
  | 7 => [(0,0),(0,3),(0,4),(0,6),(1,0),(1,6),(2,0),(3,1),(3,5),(4,6),(5,0),(5,6),(6,0),(6,2),(6,3),(6,6)]
  | 8 => [(0,0),(0,6),(0,7),(1,0),(1,2),(1,4),(2,6),(2,7),(3,5),(4,0),(5,0),(6,7),(7,0),(7,1),(7,3),(7,4),(7,5),(7,7)]
  | 9 => [(0,0),(0,2),(0,3),(0,7),(0,8),(1,0),(1,5),(2,8),(3,1),(3,8),(5,0),(5,7),(6,0),(7,3),(7,8),(8,0),(8,1),(8,5),(8,6),(8,8)]
  | 10 => [(0,0),(0,1),(0,6),(0,7),(0,8),(1,6),(2,0),(3,0),(3,5),(4,0),(4,9),(5,0),(5,9),(6,4),(6,9),(7,9),(8,3),(9,1),(9,2),(9,3),(9,8),(9,9)]
  | 11 => [(0,0),(0,3),(0,4),(0,6),(0,8),(0,10),(1,2),(2,0),(2,9),(3,10),(4,5),(5,0),(5,10),(6,5),(7,0),(8,1),(8,10),(9,8),(10,0),(10,2),(10,4),(10,6),(10,7),(10,10)]
  | 12 => [(0,0),(0,1),(0,2),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,4),(2,6),(3,0),(4,0),(5,0),(6,11),(7,11),(8,11),(9,5),(10,7),(11,0),(11,1),(11,2),(11,3),(11,4),(11,5),(11,9),(11,10),(11,11)]
  | 13 => [(0,0),(0,2),(0,4),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(1,0),(2,3),(3,0),(4,7),(5,0),(7,12),(8,5),(9,12),(10,9),(11,12),(12,0),(12,1),(12,2),(12,3),(12,4),(12,5),(12,6),(12,8),(12,10),(12,12)]
  | 14 => [(0,0),(0,1),(1,8),(1,13),(2,0),(2,3),(2,7),(2,11),(2,13),(3,0),(3,9),(3,13),(4,0),(5,1),(5,13),(6,13),(7,0),(8,0),(8,12),(9,13),(10,0),(10,4),(10,13),(11,0),(11,2),(11,6),(11,10),(11,13),(12,0),(12,5),(13,12),(13,13)]
  | 15 => [(0,0),(0,2),(0,4),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(1,0),(2,3),(3,0),(5,0),(6,9),(8,5),(9,14),(11,14),(12,11),(13,14),(14,0),(14,1),(14,2),(14,3),(14,4),(14,5),(14,6),(14,7),(14,8),(14,10),(14,12),(14,14)]
  | 16 => [(0,1),(0,2),(0,4),(0,5),(1,13),(1,15),(2,1),(2,6),(2,8),(2,10),(2,15),(3,3),(3,12),(4,15),(5,2),(5,15),(6,13),(7,2),(8,13),(9,2),(10,0),(10,13),(11,0),(12,3),(12,12),(13,0),(13,5),(13,7),(13,9),(13,14),(14,0),(14,2),(15,10),(15,11),(15,13),(15,14)]
  | 17 => [(0,0),(0,1),(0,2),(0,5),(0,6),(0,7),(0,8),(0,10),(0,12),(0,16),(1,16),(2,15),(2,16),(3,0),(4,0),(4,15),(5,7),(6,3),(7,16),(8,3),(8,13),(9,0),(10,13),(11,9),(12,1),(12,16),(13,16),(14,0),(14,1),(15,0),(16,0),(16,4),(16,6),(16,8),(16,9),(16,10),(16,11),(16,14),(16,15),(16,16)]
  | 18 => [(0,0),(0,1),(0,4),(0,7),(0,12),(0,14),(0,15),(0,17),(1,5),(1,9),(1,10),(1,17),(2,0),(3,0),(4,1),(4,17),(5,15),(6,17),(7,12),(8,0),(8,8),(9,0),(9,15),(10,0),(11,14),(12,7),(13,0),(13,11),(14,17),(15,14),(15,17),(16,10),(16,12),(17,0),(17,2),(17,3),(17,5),(17,6),(17,10),(17,13),(17,16),(17,17)]
  | 19 => [(0,1),(0,2),(0,5),(0,12),(0,14),(0,15),(0,18),(1,5),(1,8),(1,18),(2,2),(2,11),(2,18),(3,0),(3,4),(4,8),(5,18),(6,9),(7,1),(7,18),(8,18),(9,1),(9,17),(10,0),(11,0),(11,17),(12,9),(13,0),(14,10),(15,14),(15,18),(16,0),(16,7),(16,16),(17,0),(17,10),(17,13),(18,0),(18,3),(18,4),(18,6),(18,13),(18,16),(18,17)]
  | 20 => [(0,0),(0,2),(0,3),(0,4),(0,5),(0,7),(0,8),(0,15),(1,0),(1,9),(1,19),(2,7),(2,19),(3,19),(4,18),(5,17),(5,18),(6,0),(7,13),(7,17),(8,17),(8,19),(9,3),(10,16),(11,0),(11,2),(12,2),(12,6),(13,19),(14,1),(14,2),(15,1),(16,0),(17,0),(17,12),(18,0),(18,10),(18,19),(19,4),(19,11),(19,12),(19,14),(19,15),(19,16),(19,17),(19,19)]
  | 21 => [(0,0),(0,2),(0,12),(0,14),(0,16),(0,20),(1,4),(1,11),(1,14),(1,18),(2,1),(2,20),(3,10),(4,0),(4,7),(4,15),(4,19),(5,4),(6,0),(6,1),(7,16),(8,0),(9,1),(10,3),(10,17),(11,19),(12,20),(13,4),(14,19),(14,20),(15,16),(16,1),(16,5),(16,13),(16,20),(17,10),(18,0),(18,19),(19,2),(19,6),(19,9),(19,16),(20,0),(20,4),(20,6),(20,8),(20,18),(20,20)]
  | 22 => [(0,0),(0,1),(0,6),(0,9),(0,13),(0,16),(0,17),(0,18),(0,19),(0,21),(1,6),(1,21),(2,0),(2,12),(3,0),(3,7),(3,11),(4,0),(5,0),(6,20),(6,21),(7,18),(8,0),(9,2),(9,21),(10,3),(11,18),(12,0),(12,19),(13,21),(14,3),(15,0),(15,1),(16,21),(17,21),(18,10),(18,14),(18,21),(19,9),(19,21),(20,0),(20,15),(21,0),(21,2),(21,3),(21,4),(21,5),(21,8),(21,12),(21,15),(21,20),(21,21)]
  | 23 => [(0,0),(0,5),(0,9),(0,10),(0,11),(0,13),(0,17),(0,19),(0,20),(0,21),(0,22),(1,0),(2,0),(2,6),(3,0),(4,0),(4,22),(5,2),(5,4),(6,0),(6,22),(7,7),(7,22),(8,22),(9,1),(10,22),(11,1),(12,20),(13,6),(14,1),(14,18),(15,3),(15,16),(15,22),(16,0),(16,22),(17,2),(18,0),(19,21),(19,22),(20,22),(21,22),(22,0),(22,1),(22,2),(22,3),(22,5),(22,8),(22,11),(22,12),(22,13),(22,14),(22,17),(22,22)]
  | 24 => [(0,0),(0,3),(0,7),(0,11),(0,13),(0,15),(0,18),(0,21),(0,22),(1,0),(1,4),(2,0),(3,1),(3,6),(3,23),(4,18),(4,23),(5,10),(6,0),(6,23),(7,16),(7,23),(8,0),(8,12),(9,14),(10,0),(11,21),(11,23),(12,0),(12,2),(13,23),(14,9),(15,11),(15,23),(16,0),(16,7),(17,0),(17,23),(18,13),(19,0),(19,5),(20,0),(20,17),(20,22),(21,23),(22,19),(22,23),(23,1),(23,2),(23,5),(23,8),(23,10),(23,12),(23,16),(23,20),(23,23)]
  | 25 => [(0,0),(0,3),(0,5),(0,6),(0,7),(0,12),(0,15),(0,19),(0,21),(0,22),(0,23),(1,0),(1,15),(2,0),(2,16),(2,22),(3,10),(3,14),(4,0),(4,20),(5,23),(6,19),(7,13),(7,24),(8,0),(9,0),(10,0),(10,1),(11,3),(13,21),(14,23),(14,24),(15,24),(16,24),(17,0),(17,11),(18,5),(19,1),(20,4),(20,24),(21,10),(21,14),(22,2),(22,8),(22,24),(23,9),(23,24),(24,1),(24,2),(24,3),(24,5),(24,9),(24,12),(24,17),(24,18),(24,19),(24,21),(24,24)]
  | 26 => [(0,0),(0,5),(0,9),(0,13),(0,14),(0,15),(0,18),(0,19),(0,21),(0,22),(0,23),(0,25),(1,18),(2,0),(2,10),(3,0),(4,0),(4,20),(5,4),(5,25),(6,0),(7,0),(7,1),(8,14),(9,25),(10,0),(10,23),(11,0),(11,8),(12,0),(13,25),(14,17),(14,25),(15,2),(15,25),(16,0),(17,11),(18,24),(18,25),(19,25),(20,0),(20,21),(21,5),(21,25),(22,25),(23,15),(23,25),(24,7),(25,0),(25,2),(25,3),(25,4),(25,6),(25,7),(25,10),(25,11),(25,12),(25,16),(25,20),(25,25)]
  | 27 => [(0,0),(0,7),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(0,24),(0,25),(0,26),(1,0),(2,0),(3,0),(4,0),(4,1),(5,17),(6,0),(7,1),(8,24),(9,0),(9,1),(10,12),(11,0),(11,1),(12,11),(13,8),(13,18),(14,15),(15,25),(15,26),(16,14),(17,25),(17,26),(18,2),(19,25),(20,26),(21,9),(22,25),(22,26),(23,26),(24,26),(25,26),(26,0),(26,1),(26,2),(26,3),(26,4),(26,5),(26,6),(26,7),(26,8),(26,9),(26,10),(26,11),(26,12),(26,13),(26,19),(26,26)]
  | 28 => [(0,0),(0,1),(0,5),(0,7),(0,9),(0,11),(0,12),(0,14),(0,16),(0,21),(0,23),(0,24),(0,26),(1,9),(1,18),(1,19),(1,21),(1,24),(2,0),(2,6),(2,27),(3,0),(4,0),(5,27),(6,0),(7,26),(8,9),(9,9),(10,5),(11,26),(12,8),(13,0),(13,26),(14,0),(15,0),(16,26),(17,27),(18,15),(19,13),(20,12),(21,25),(21,27),(22,4),(23,27),(24,3),(24,12),(24,17),(24,27),(25,3),(25,15),(25,27),(26,0),(27,0),(27,2),(27,3),(27,4),(27,7),(27,8),(27,10),(27,11),(27,16),(27,18),(27,20),(27,22),(27,26),(27,27)]
  | 29 => [(0,0),(0,1),(0,2),(0,3),(0,6),(0,8),(0,12),(0,13),(0,21),(0,24),(0,28),(1,4),(1,18),(1,19),(1,28),(2,7),(2,12),(2,28),(3,28),(4,0),(4,27),(5,18),(6,17),(6,28),(7,0),(7,26),(8,28),(9,1),(10,1),(10,5),(11,6),(12,26),(12,28),(13,28),(15,0),(16,0),(16,2),(17,22),(18,23),(18,27),(19,27),(20,0),(21,2),(21,28),(22,0),(22,11),(23,10),(24,1),(24,28),(25,0),(26,0),(26,16),(26,21),(27,0),(27,9),(27,10),(27,24),(28,0),(28,4),(28,7),(28,15),(28,16),(28,20),(28,22),(28,25),(28,26),(28,27),(28,28)]
  | 30 => [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(0,14),(0,19),(0,23),(0,26),(1,8),(1,29),(2,29),(3,0),(3,12),(3,24),(4,11),(4,29),(5,29),(6,2),(6,20),(7,29),(8,16),(8,28),(9,19),(10,0),(11,0),(11,26),(11,29),(12,0),(12,29),(13,0),(13,29),(14,6),(15,23),(16,0),(16,29),(17,0),(17,29),(18,0),(18,3),(18,29),(19,29),(20,10),(21,1),(21,13),(22,0),(23,9),(23,27),(24,0),(25,0),(25,18),(26,5),(26,17),(26,29),(27,0),(28,0),(28,21),(29,3),(29,6),(29,10),(29,15),(29,22),(29,23),(29,24),(29,25),(29,27),(29,28),(29,29)]
  | 31 => [(0,0),(0,4),(0,16),(0,22),(0,24),(0,28),(0,30),(1,2),(1,6),(1,9),(1,16),(1,18),(1,19),(1,26),(2,0),(2,29),(3,15),(4,1),(4,7),(4,25),(4,30),(5,4),(6,0),(6,17),(6,29),(7,26),(8,0),(9,29),(10,19),(11,1),(11,10),(12,1),(13,6),(14,0),(14,1),(15,3),(15,27),(16,29),(16,30),(17,24),(18,29),(19,20),(19,29),(20,11),(21,1),(22,30),(23,4),(24,1),(24,13),(24,30),(25,26),(26,0),(26,5),(26,23),(26,29),(27,15),(28,1),(28,30),(29,4),(29,11),(29,12),(29,14),(29,21),(29,24),(29,28),(30,0),(30,2),(30,6),(30,8),(30,14),(30,26),(30,30)]
  | 32 => [(0,0),(0,1),(0,4),(0,31),(1,9),(1,12),(1,20),(1,31),(2,0),(2,10),(2,13),(2,14),(2,31),(3,0),(3,16),(3,24),(3,31),(4,31),(5,0),(5,6),(5,31),(6,0),(6,2),(6,31),(7,0),(7,31),(8,31),(9,0),(9,31),(10,0),(11,31),(12,8),(13,26),(13,28),(13,31),(14,0),(14,31),(15,31),(16,0),(17,0),(17,31),(18,0),(18,3),(18,5),(19,23),(20,0),(21,31),(22,0),(22,31),(23,0),(24,0),(24,31),(25,0),(25,29),(25,31),(26,0),(26,25),(26,31),(27,0),(28,0),(28,7),(28,15),(28,31),(29,0),(29,17),(29,18),(29,21),(29,31),(30,0),(30,11),(30,19),(30,22),(31,0),(31,27),(31,30),(31,31)]
  | _ => []

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem small {n : ℕ} (lo : 2≤n) (hi : n≤32) :
    ∃ s : Finset (Square n), valid s ∧ s.card = 2*((6*n-2)/5) := by
  interval_cases n <;> exact certify (W _) _ (by decide +kernel) (by rfl) (by decide +kernel)
end OMA.ThreeWitnesses

/-!
Period-five constructions for the three-attacker queens problem.
An affine form represents c+a*x+b*y for arbitrary nonnegative x and y.
The two free variables describe the position of a square within a growing strip.
-/
namespace OMA.ThreePeriodic

structure Form where
  c : ℤ
  a : ℤ := 0
  b : ℤ := 0
deriving DecidableEq, Repr, Inhabited

namespace Form
def const (z : ℤ) : Form := ⟨z,0,0⟩
def add (f g : Form) : Form := ⟨f.c+g.c,f.a+g.a,f.b+g.b⟩
def sub (f g : Form) : Form := ⟨f.c-g.c,f.a-g.a,f.b-g.b⟩
def scale (k : ℤ) (f : Form) : Form := ⟨k*f.c,k*f.a,k*f.b⟩
def div5 (f : Form) : Form := ⟨f.c/5,f.a/5,f.b/5⟩
def val (f : Form) (x y : ℕ) : ℤ := f.c + f.a*x + f.b*y
def yes (f : Form) : Bool := decide (0 ≤ f.c ∧ 0 ≤ f.a ∧ 0 ≤ f.b)
def no (f : Form) : Bool := decide (f.c < 0 ∧ f.a ≤ 0 ∧ f.b ≤ 0)
@[simp] theorem val_const (z : ℤ) (x y : ℕ) : (const z).val x y=z := by simp [val,const]
@[simp] theorem val_add (f g : Form) (x y : ℕ) : (add f g).val x y=f.val x y+g.val x y := by simp [val,add];ring
@[simp] theorem val_sub (f g : Form) (x y : ℕ) : (sub f g).val x y=f.val x y-g.val x y := by simp [val,sub];ring
@[simp] theorem val_scale (k : ℤ) (f : Form) (x y : ℕ) : (scale k f).val x y=k*f.val x y := by simp [val,scale];ring
theorem lower (f : Form) (h : f.yes=true) (x y : ℕ) : 0 ≤ f.val x y := by
  obtain ⟨hc,ha,hb⟩ := of_decide_eq_true h
  exact add_nonneg (add_nonneg hc (mul_nonneg ha (by positivity))) (mul_nonneg hb (by positivity))
theorem negative (f : Form) (h : f.no=true) (x y : ℕ) : f.val x y < 0 := by
  obtain ⟨hc,ha,hb⟩ := of_decide_eq_true h
  have h1 := mul_nonpos_of_nonpos_of_nonneg ha (show (0:ℤ) ≤ x by positivity)
  have h2 := mul_nonpos_of_nonpos_of_nonneg hb (show (0:ℤ) ≤ y by positivity)
  unfold val; omega
theorem divisible_slopes (f : Form) (ha : f.a%5=0) (hb : f.b%5=0) (x y : ℕ) :
    f.val x y = 5 * (div5 f).val x y + f.c%5 := by
  have ea : f.a=5*(f.a/5) := by omega
  have eb : f.b=5*(f.b/5) := by omega
  have ec : f.c=5*(f.c/5)+f.c%5 := by omega
  unfold val div5
  dsimp
  linear_combination ec + (x:ℤ)*ea + (y:ℤ)*eb
end Form

/-- Sufficient and necessary Boolean bounds for a conjunction of nonnegative forms. -/
def bounds (xs : List Form) : Bool × Bool :=
  (xs.all Form.yes, !xs.any Form.no)

theorem bounds_correct (xs : List Form) (x y : ℕ) :
    ((bounds xs).1 = true → ∀ f ∈ xs, 0 ≤ f.val x y) ∧
    ((∀ f ∈ xs, 0 ≤ f.val x y) → (bounds xs).2 = true) := by
  constructor
  · intro h f hf
    exact f.lower (List.all_eq_true.mp h f hf) x y
  · intro h
    simp only [bounds,Bool.not_eq_true']
    by_contra w
    obtain ⟨f,hf,hno⟩ := List.any_eq_true.mp (Bool.eq_true_of_not_eq_false w)
    exact (not_lt_of_ge (h f hf)) (f.negative hno x y)

/-- The match key changes by d per step along the candidate strip. The signed
coordinate in the direction of travel changes by u per step. -/
def rayBounds (delta extent length : Form) (d u : ℤ) : Bool × Bool :=
  if d=0 then
    let last := length.sub (Form.const 1)
    let reach := extent.add (last.scale (max 0 u))
    bounds [last,delta,delta.scale (-1),reach.sub (Form.const 1)]
  else if d=5 ∨ d= -5 then
    let z := delta.scale (if d=5 then 1 else -1)
    if z.a%5=0 ∧ z.b%5=0 then
      if z.c%5=0 then
        let j := z.div5
        bounds [j,(length.sub (Form.const 1)).sub j,(extent.add (j.scale u)).sub (Form.const 1)]
      else (false,false)
    else (false,true)
  else (false,true)

theorem rayBounds_correct (delta extent length : Form) (d u : ℤ) (x y : ℕ) :
    let feasible := ∃ j : ℤ, 0 ≤ j ∧ j < length.val x y ∧ d*j = delta.val x y ∧
      0 < extent.val x y + u*j
    ((rayBounds delta extent length d u).1 = true → feasible) ∧
    (feasible → (rayBounds delta extent length d u).2 = true) := by
  dsimp only
  unfold rayBounds
  split
  · rename_i hd
    subst d
    have h := bounds_correct [length.sub (Form.const 1),delta,delta.scale (-1),
      (extent.add ((length.sub (Form.const 1)).scale (max 0 u))).sub (Form.const 1)] x y
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      Form.val_sub,Form.val_const,Form.val_scale,Form.val_add] at h
    constructor
    · intro k
      obtain ⟨len, hp, hm, pos⟩ := h.1 k
      by_cases s : 0 ≤ u
      · rw [max_eq_right s] at pos
        exact ⟨length.val x y-1,by omega,by omega,by omega,by omega⟩
      · rw [max_eq_left (by omega : u ≤ 0)] at pos
        exact ⟨0,by omega,by omega,by omega,by simpa using (show 0 < extent.val x y by simpa using (show 0 < extent.val x y + 0*(length.val x y-1) by omega))⟩
    · rintro ⟨j,hj,hl,he,hit⟩
      apply h.2
      refine ⟨by omega,by omega,by omega,?_⟩
      by_cases s : 0 ≤ u
      · rw [max_eq_right s]
        have := mul_le_mul_of_nonneg_left (show j ≤ length.val x y-1 by omega) s
        omega
      · rw [max_eq_left (by omega : u ≤ 0)]
        have := mul_nonpos_of_nonpos_of_nonneg (show u ≤ 0 by omega) hj
        simp only [zero_mul,add_zero]; omega
  · split
    · rename_i hd
      generalize hz : delta.scale (if d=5 then 1 else -1) = z
      have eq (j : ℤ) : d*j = delta.val x y ↔ 5*j=z.val x y := by
        rw [← hz,Form.val_scale]
        rcases hd with rfl | rfl <;> norm_num <;> omega
      dsimp only
      split
      · rename_i hs
        have div := z.divisible_slopes hs.1 hs.2 x y
        split
        · rename_i hc
          rw [hc,add_zero] at div
          have h := bounds_correct [z.div5,(length.sub (Form.const 1)).sub z.div5,
            (extent.add (z.div5.scale u)).sub (Form.const 1)] x y
          simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
            Form.val_sub,Form.val_const,Form.val_scale,Form.val_add] at h
          constructor
          · intro k
            obtain ⟨lo,hi,hit⟩ := h.1 k
            exact ⟨z.div5.val x y,lo,by omega,(eq _).mpr div.symm,by omega⟩
          · rintro ⟨j,lo,hi,match',hit⟩
            have same := (eq j).mp match'
            have je : j = z.div5.val x y := by omega
            subst j
            exact h.2 ⟨lo,by omega,by omega⟩
        · rename_i bad
          constructor
          · simp
          · rintro ⟨j,_,_,match',_⟩
            have := (eq j).mp match'
            omega
      · simp
    · simp
end OMA.ThreePeriodic

namespace OMA.ThreePeriodic
open OMA.S_oeis_a051756 Finset

abbrev Point := ℤ × ℤ

def key (a : Axis) (p : Point) : ℤ :=
  match a with
  | .row => p.1
  | .column => p.2
  | .ascending => p.1+p.2
  | .descending => p.1-p.2

def along (a : Axis) (p : Point) : ℤ :=
  match a with
  | .row => p.2
  | _ => p.1

def sign (earlier : Bool) : ℤ := if earlier then -1 else 1

def onRay (a : Axis) (earlier : Bool) (p q : Point) : Prop :=
  key a q = key a p ∧ 0 < sign earlier * (along a q - along a p)

def liftPoint {n : ℕ} (p : Square n) : Point := ((p.1.val:ℤ),(p.2.val:ℤ))

private lemma rank_lt_of_row {n : ℕ} {p q : Square n} (h : p.1.val < q.1.val) :
    rank p < rank q := by
  have step : (p.1.val+1)*n ≤ q.1.val*n := Nat.mul_le_mul_right n h
  have column := p.2.isLt
  dsimp only [rank]
  rw [Nat.add_mul,one_mul] at step
  omega

private lemma rank_lex {n : ℕ} (p q : Square n) : rank p < rank q ↔
    p.1.val < q.1.val ∨ (p.1.val = q.1.val ∧ p.2.val < q.2.val) := by
  constructor
  · intro h
    rcases lt_trichotomy p.1.val q.1.val with lt | eq | gt
    · exact Or.inl lt
    · right; refine ⟨eq,?_⟩
      simpa [rank,eq] using h
    · exact False.elim ((not_lt_of_ge (rank_lt_of_row gt).le) h)
  · rintro (lt | ⟨eq,lt⟩)
    · exact rank_lt_of_row lt
    · simpa [rank,eq] using lt

private lemma ray_equiv {n : ℕ} (p q : Square n) (a : Axis) (e : Bool) :
    onRay a e (liftPoint p) (liftPoint q) ↔
    line a q = line a p ∧ (if e then rank q < rank p else rank p < rank q) := by
  have h1 := q.2.isLt
  have h2 := p.2.isLt
  cases a <;> cases e <;>
    simp [onRay,key,along,sign,liftPoint,line,rank_lex] <;> omega

/-- Realize an injective parametrization of integer squares as a finite placement. -/
theorem realize {ι : Type} [Fintype ι] (n k : ℕ) (pos : ι → Point)
    (inj : Function.Injective pos)
    (bound : ∀ i, 0 ≤ (pos i).1 ∧ (pos i).1 < n ∧ 0 ≤ (pos i).2 ∧ (pos i).2 < n)
    (size : Fintype.card ι = k)
    (hits : ι → Axis → Bool → Bool)
    (spec : ∀ i a e, hits i a e=true ↔ ∃ j, onRay a e (pos i) (pos j))
    (three : ∀ i, ((hits i .row true).toNat + (hits i .row false).toNat) +
      ((hits i .column true).toNat + (hits i .column false).toNat) +
      ((hits i .ascending true).toNat + (hits i .ascending false).toNat) +
      ((hits i .descending true).toNat + (hits i .descending false).toNat) = 3) :
    ∃ s : Finset (Square n), valid s ∧ s.card=k := by
  classical
  let board (i : ι) : Square n :=
    (⟨(pos i).1.toNat, by have := bound i; omega⟩,⟨(pos i).2.toNat, by have := bound i; omega⟩)
  have lift (i) : liftPoint (board i) = pos i := by
    ext <;> simp [liftPoint,board,Int.toNat_of_nonneg (bound i).1,Int.toNat_of_nonneg (bound i).2.2.1]
  have uniq : Function.Injective board := by
    intro i j eq
    exact inj ((lift i).symm.trans ((congrArg liftPoint eq).trans (lift j)))
  let s := univ.image board
  refine ⟨s,?_,(card_image_of_injective _ uniq).trans (card_univ.trans size)⟩
  intro p hp
  obtain ⟨i,_,rfl⟩ := mem_image.mp hp
  have side (a : Axis) (e : Bool) : hits i a e=true ↔
      ∃ q ∈ s, line a q = line a (board i) ∧
        (if e then rank q < rank (board i) else rank (board i) < rank q) := by
    rw [spec]
    constructor
    · rintro ⟨j,h⟩
      refine ⟨board j,mem_image_of_mem _ (mem_univ _),?_⟩
      apply (ray_equiv _ _ a e).mp
      simpa only [lift] using h
    · rintro ⟨q,hq,h⟩
      obtain ⟨j,_,rfl⟩ := mem_image.mp hq
      exact ⟨j,by simpa only [lift] using (ray_equiv _ _ a e).mpr h⟩
  have cv (a : Axis) : visible s (board i) a =
      (hits i a true).toNat + (hits i a false).toNat := by
    have t := side a true
    have f := side a false
    simp only [Bool.true_eq,if_true,Bool.false_eq_true,if_false] at t f
    unfold visible
    cases ht : hits i a true <;> cases hf : hits i a false <;> simp_all
  simpa only [cv] using three i
end OMA.ThreePeriodic

namespace OMA.ThreePeriodic
open OMA.S_oeis_a051756 Finset

inductive Location where
  | low (v : ℕ)
  | high (v : ℕ)
  | middle (v : ℕ)
  deriving DecidableEq,Repr,Inhabited

namespace Location
def moves : Location → Bool | .middle _ => true | _ => false
def proper (lo hi : ℕ) : Location → Bool
  | .low v => decide (v<lo)
  | .high v => decide (v<hi)
  | .middle v => decide (v<5)
def slope (t : Location) : ℤ := if t.moves then 5 else 0
def start (lo hi : ℕ) (k : ℤ) : Location → ℤ
  | .low v => v
  | .high v => (lo:ℤ)+hi-1-v+5*k
  | .middle v => (lo:ℤ)+v
def atIndex (lo hi : ℕ) (k j : ℤ) (t : Location) : ℤ :=
  t.start lo hi k + t.slope*j
def form (lo hi : ℕ) (k j : Form) : Location → Form
  | .low v => Form.const v
  | .high v => (Form.const ((lo:ℤ)+hi-1-v)).add (k.scale 5)
  | .middle v => (Form.const ((lo:ℤ)+v)).add (j.scale 5)
@[simp] theorem eval_form (lo hi : ℕ) (k j : Form) (x y : ℕ) (t : Location) :
    (form lo hi k j t).val x y = t.atIndex lo hi (k.val x y) (j.val x y) := by
  cases t <;> simp [form,atIndex,start,slope,moves]
theorem coord_bound {lo hi k j : ℕ} {t : Location} (hp : t.proper lo hi = true)
    (bound : t.moves = true → j<k) :
    0 ≤ t.atIndex lo hi k j ∧ t.atIndex lo hi k j < (lo:ℤ)+hi+5*k := by
  cases t <;> simp_all [proper,atIndex,start,slope,moves] <;> omega

def decode (lo hi k : ℕ) (x : ℤ) : Location :=
  if x < lo then .low x.toNat
  else if (lo:ℤ)+5*k ≤ x then .high (((lo:ℤ)+hi+5*k-1-x).toNat)
  else .middle ((x-lo)%5).toNat

theorem recover {lo hi k j : ℕ} {t : Location} (hp : t.proper lo hi = true)
    (bound : t.moves = true → j<k) :
    decode lo hi k (t.atIndex lo hi k j) = t := by
  cases t with
  | low v =>
    have h : v<lo := of_decide_eq_true hp
    simp [decode,atIndex,start,slope,moves,h]
  | high v =>
    have h : v<hi := of_decide_eq_true hp
    simp only [decode,atIndex,start,slope,moves,Bool.false_eq_true,if_false,zero_mul,add_zero]
    rw [if_neg (by omega),if_pos (by omega)]
    congr 1
    omega
  | middle v =>
    have h : v<5 := of_decide_eq_true hp
    have hj := bound rfl
    simp only [decode,atIndex,start,slope,moves,if_true]
    rw [if_neg (by omega),if_neg (by omega)]
    congr 1
    omega
end Location

abbrev Shape := Location × Location
namespace Shape
def moves (s : Shape) := s.1.moves || s.2.moves
def proper (s : Shape) (lo hi : ℕ) := s.1.proper lo hi && s.2.proper lo hi
def extent (s : Shape) (k : ℕ) := if moves s then k else 1
def pos (s : Shape) (lo hi : ℕ) (k j : ℤ) : Point :=
  (s.1.atIndex lo hi k j,s.2.atIndex lo hi k j)
def pointForm (s : Shape) (lo hi : ℕ) (k j : Form) :=
  (s.1.form lo hi k j,s.2.form lo hi k j)
def step (s : Shape) : Point := (s.1.slope,s.2.slope)
theorem within {s : Shape} {lo hi k j : ℕ} (hp : proper s lo hi=true) (hj : j < extent s k) :
    (0 ≤ (pos s lo hi k j).1 ∧ (pos s lo hi k j).1 < (lo:ℤ)+hi+5*k) ∧
    (0 ≤ (pos s lo hi k j).2 ∧ (pos s lo hi k j).2 < (lo:ℤ)+hi+5*k) := by
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp hp
  exact ⟨Location.coord_bound a (fun m => by simpa [extent,moves,m] using hj),
    Location.coord_bound b (fun m => by simpa [extent,moves,m] using hj)⟩

theorem inject {s t : Shape} {lo hi k i j : ℕ} (sp : proper s lo hi=true)
    (tp : proper t lo hi=true) (ia : i<extent s k) (ja : j<extent t k)
    (eq : pos s lo hi k i = pos t lo hi k j) : s=t ∧ i=j := by
  obtain ⟨s1,s2⟩ := Bool.and_eq_true_iff.mp sp
  obtain ⟨t1,t2⟩ := Bool.and_eq_true_iff.mp tp
  have hx := congrArg (fun p : Point => Location.decode lo hi k p.1) eq
  have hy := congrArg (fun p : Point => Location.decode lo hi k p.2) eq
  change Location.decode _ _ _ (Location.atIndex _ _ _ _ _) = Location.decode _ _ _ (Location.atIndex _ _ _ _ _) at hx hy
  rw [Location.recover s1 (fun m => by simpa [extent,moves,m] using ia),
      Location.recover t1 (fun m => by simpa [extent,moves,m] using ja)] at hx
  rw [Location.recover s2 (fun m => by simpa [extent,moves,m] using ia),
      Location.recover t2 (fun m => by simpa [extent,moves,m] using ja)] at hy
  have st : s=t := Prod.ext hx hy
  subst t
  refine ⟨rfl,?_⟩
  by_cases a : s.1.moves=true
  · have h := congrArg Prod.fst eq
    simp [pos,Location.atIndex,Location.slope,a] at h
    omega
  by_cases b : s.2.moves=true
  · have h := congrArg Prod.snd eq
    simp [pos,Location.atIndex,Location.slope,b] at h
    omega
  simp [extent,moves,a,b] at ia ja
  omega
end Shape

def keyForm (a : Axis) (p : Form × Form) : Form :=
  match a with
  | .row => p.1
  | .column => p.2
  | .ascending => p.1.add p.2
  | .descending => p.1.sub p.2
def alongForm (a : Axis) (p : Form × Form) : Form :=
  match a with | .row => p.2 | _ => p.1

@[simp] theorem eval_key (a : Axis) (p : Form × Form) (x y : ℕ) :
    (keyForm a p).val x y = key a (p.1.val x y,p.2.val x y) := by cases a <;> simp [keyForm,key]
@[simp] theorem eval_along (a : Axis) (p : Form × Form) (x y : ℕ) :
    (alongForm a p).val x y = along a (p.1.val x y,p.2.val x y) := by cases a <;> rfl

theorem key_step (a : Axis) (s : Shape) (lo hi : ℕ) (k j : ℤ) :
    key a (s.pos lo hi k j) = key a (s.pos lo hi k 0) + key a s.step*j := by
  cases a <;> simp [Shape.pos,Shape.step,Location.atIndex,key] <;> ring
theorem along_step (a : Axis) (s : Shape) (lo hi : ℕ) (k j : ℤ) :
    along a (s.pos lo hi k j) = along a (s.pos lo hi k 0) + along a s.step*j := by
  cases a <;> simp [Shape.pos,Shape.step,Location.atIndex,along]

def pairBounds (lo hi : ℕ) (k j : Form) (s t : Shape) (a : Axis) (e : Bool) : Bool × Bool :=
  let p := s.pointForm lo hi k j
  let q := t.pointForm lo hi k (Form.const 0)
  rayBounds ((keyForm a p).sub (keyForm a q))
    (((alongForm a q).sub (alongForm a p)).scale (sign e))
    (if t.moves then k else Form.const 1) (key a t.step) (sign e*along a t.step)

theorem pair_spec (lo hi : ℕ) (k j : Form) (s t : Shape) (a : Axis) (e : Bool) (x y K J : ℕ)
    (hk : k.val x y=K) (hj : j.val x y=J) :
    let F := ∃ i : ℕ, i<t.extent K ∧ onRay a e (s.pos lo hi K J) (t.pos lo hi K i)
    ((pairBounds lo hi k j s t a e).1=true → F) ∧
    (F → (pairBounds lo hi k j s t a e).2=true) := by
  dsimp only
  let p := s.pointForm lo hi k j
  let q := t.pointForm lo hi k (Form.const 0)
  let len := if t.moves then k else Form.const 1
  have L : len.val x y = (t.extent K:ℤ) := by
    cases h : t.moves <;> simp [Shape.extent,len,h,hk]
  have evalP : (p.1.val x y,p.2.val x y) = s.pos lo hi K J := by simp [p,Shape.pointForm,Shape.pos,hk,hj]
  have evalQ : (q.1.val x y,q.2.val x y) = t.pos lo hi K 0 := by simp [q,Shape.pointForm,Shape.pos,hk]
  have h := rayBounds_correct ((keyForm a p).sub (keyForm a q))
    (((alongForm a q).sub (alongForm a p)).scale (sign e)) len (key a t.step) (sign e*along a t.step) x y
  dsimp only at h
  simp only [Form.val_sub,Form.val_scale,eval_key,eval_along,evalP,evalQ,L] at h
  constructor
  · intro yes
    obtain ⟨z,hz,hl,he,hd⟩ := h.1 yes
    refine ⟨z.toNat,by omega,?_⟩
    have nat : (z.toNat:ℤ)=z := Int.toNat_of_nonneg hz
    change key a (t.pos lo hi K (z.toNat:ℕ)) = _ ∧ 0 < sign e * (along a (t.pos lo hi K (z.toNat:ℕ)) - _)
    rw [key_step,along_step,nat]
    constructor
    · omega
    · linear_combination hd
  · rintro ⟨i,hi',he,hd⟩
    apply h.2
    refine ⟨i,by positivity,by exact_mod_cast hi',?_,?_⟩
    · rw [key_step] at he
      omega
    · rw [along_step] at hd
      linear_combination hd
end OMA.ThreePeriodic

namespace OMA.ThreePeriodic
open OMA.S_oeis_a051756

def directions : List (Axis × Bool) :=
  [(.row,true),(.row,false),(.column,true),(.column,false),
   (.ascending,true),(.ascending,false),(.descending,true),(.descending,false)]

def degree (hits : Axis → Bool → Bool) : ℕ :=
  ((hits .row true).toNat + (hits .row false).toNat) +
  ((hits .column true).toNat + (hits .column false).toNat) +
  ((hits .ascending true).toNat + (hits .ascending false).toNat) +
  ((hits .descending true).toNat + (hits .descending false).toNat)

def certain (lo hi : ℕ) (S : List Shape) (s : Shape) (k j : Form) (a : Axis) (e : Bool) :=
  S.any fun t => (pairBounds lo hi k j s t a e).1

def possible (lo hi : ℕ) (S : List Shape) (s : Shape) (k j : Form) (a : Axis) (e : Bool) :=
  S.any fun t => (pairBounds lo hi k j s t a e).2

def regionOK (lo hi : ℕ) (S : List Shape) (s : Shape) (k j : Form) : Bool :=
  let low := certain lo hi S s k j
  let high := possible lo hi S s k j
  directions.all (fun (a,e) => low a e == high a e) && decide (degree low = 3)

theorem region_sound {lo hi : ℕ} {S : List Shape} {s : Shape} {k j : Form}
    (checked : regionOK lo hi S s k j=true) (x y K J : ℕ)
    (hk : k.val x y=K) (hj : j.val x y=J) :
    let hit := certain lo hi S s k j
    degree hit=3 ∧ ∀ a e, hit a e=true ↔
      ∃ t ∈ S, ∃ i : ℕ, i<t.extent K ∧ onRay a e (s.pos lo hi K J) (t.pos lo hi K i) := by
  obtain ⟨agree,three⟩ := Bool.and_eq_true_iff.mp checked
  refine ⟨of_decide_eq_true three,?_⟩
  intro a e
  have mem : (a,e) ∈ directions := by cases a <;> cases e <;> decide
  have same := List.all_eq_true.mp agree _ mem
  change (certain lo hi S s k j a e == possible lo hi S s k j a e) = true at same
  constructor
  · intro low
    obtain ⟨t,ht,yes⟩ := List.any_eq_true.mp low
    exact ⟨t,ht,(pair_spec lo hi k j s t a e x y K J hk hj).1 yes⟩
  · rintro ⟨t,ht,w⟩
    rw [eq_of_beq same]
    exact List.any_eq_true.mpr ⟨t,ht,(pair_spec lo hi k j s t a e x y K J hk hj).2 w⟩

def shapeOK (lo hi : ℕ) (S : List Shape) (s : Shape) : Bool :=
  regionOK lo hi S s ⟨3,1,0⟩ ⟨0,0,0⟩ &&
    (if s.moves then
      regionOK lo hi S s ⟨3,1,0⟩ ⟨2,1,0⟩ &&
      regionOK lo hi S s ⟨3,1,1⟩ ⟨1,1,0⟩
    else true)

theorem shape_sound {lo hi : ℕ} {S : List Shape} {s : Shape}
    (good : shapeOK lo hi S s=true) {K J : ℕ} (hK : 3≤K) (hJ : J<s.extent K) :
    ∃ hit : Axis → Bool → Bool, degree hit=3 ∧ ∀ a e, hit a e=true ↔
      ∃ t ∈ S, ∃ i : ℕ, i<t.extent K ∧ onRay a e (s.pos lo hi K J) (t.pos lo hi K i) := by
  obtain ⟨start,more⟩ := Bool.and_eq_true_iff.mp good
  by_cases zero : J=0
  · refine ⟨_,region_sound start (K-3) 0 K J ?_ ?_⟩ <;> simp [Form.val] <;> omega
  have active : s.moves=true := by
    cases h : s.moves with
    | false => simp [Shape.extent,h] at hJ; omega
    | true => rfl
  simp only [active,if_true,Bool.and_eq_true] at more
  have jk : J<K := by simpa [Shape.extent,active] using hJ
  by_cases last : J+1=K
  · refine ⟨_,region_sound more.1 (K-3) 0 K J ?_ ?_⟩ <;> simp [Form.val] <;> omega
  · refine ⟨_,region_sound more.2 (J-1) (K-J-2) K J ?_ ?_⟩ <;> simp [Form.val] <;> omega

end OMA.ThreePeriodic

namespace OMA.ThreePeriodic
open OMA.S_oeis_a051756 Finset

def fixed (S : List Shape) := S.toFinset.filter fun s => s.moves=false
def growing (S : List Shape) := S.toFinset.filter fun s => s.moves=true
abbrev Slot (S : List Shape) (k : ℕ) := (fixed S) ⊕ ((growing S) × Fin k)
def unpack {S : List Shape} {k : ℕ} : Slot S k → Shape × ℕ
  | .inl s => (s.val,0)
  | .inr (s,i) => (s.val,i.val)

theorem slot_valid (S : List Shape) (k : ℕ) (z : Slot S k) :
    (unpack z).1 ∈ S ∧ (unpack z).2 < (unpack z).1.extent k := by
  cases z with
  | inl s =>
    obtain ⟨hs,hm⟩ := mem_filter.mp s.property
    exact ⟨List.mem_toFinset.mp hs,by simp [unpack,Shape.extent,hm]⟩
  | inr si =>
    obtain ⟨s,i⟩ := si
    obtain ⟨hs,hm⟩ := mem_filter.mp s.property
    exact ⟨List.mem_toFinset.mp hs,by simpa [unpack,Shape.extent,hm] using i.isLt⟩

theorem unpack_inj {S : List Shape} {k : ℕ} : Function.Injective (unpack (S:=S) (k:=k)) := by
  intro a b h
  cases a with
  | inl s =>
    cases b with
    | inl t =>
      have eq : s.val=t.val := congrArg Prod.fst h
      exact congrArg Sum.inl (Subtype.ext eq)
    | inr ti =>
      have eq : s.val=ti.1.val := congrArg Prod.fst h
      have m := (mem_filter.mp s.property).2
      have n := (mem_filter.mp ti.1.property).2
      rw [eq] at m
      simp_all
  | inr si =>
    cases b with
    | inl t =>
      have eq : si.1.val=t.val := congrArg Prod.fst h
      have m := (mem_filter.mp si.1.property).2
      have n := (mem_filter.mp t.property).2
      rw [eq] at m
      simp_all
    | inr ti =>
      have eq : si.1.val = ti.1.val := congrArg Prod.fst h
      have ej : si.2.val = ti.2.val := congrArg Prod.snd h
      exact congrArg Sum.inr (Prod.ext (Subtype.ext eq) (Fin.ext ej))

theorem pack {S : List Shape} {k j : ℕ} {s : Shape} (hs : s∈S) (hj : j<s.extent k) :
    ∃ i : Slot S k, unpack i=(s,j) := by
  cases hm : s.moves with
  | false =>
    have hz : j=0 := by simpa [Shape.extent,hm] using hj
    exact ⟨.inl ⟨s,mem_filter.mpr ⟨List.mem_toFinset.mpr hs,hm⟩⟩,by simp [unpack,hz]⟩
  | true =>
    have hk : j<k := by simpa [Shape.extent,hm] using hj
    exact ⟨.inr (⟨s,mem_filter.mpr ⟨List.mem_toFinset.mpr hs,hm⟩⟩,⟨j,hk⟩),rfl⟩

theorem large (lo hi : ℕ) (S : List Shape) (proper : ∀ s ∈ S, s.proper lo hi=true)
    (cert : ∀ s ∈ S, shapeOK lo hi S s=true)
    (count_fixed : (fixed S).card=2*((6*(lo+hi)-2)/5))
    (count_grow : (growing S).card=12) (start : 2≤lo+hi) (k : ℕ) (hk : 3≤k) :
    ∃ s : Finset (Square (lo+hi+5*k)), valid s ∧ s.card=2*((6*(lo+hi+5*k)-2)/5) := by
  classical
  let P (i : Slot S k) := (unpack i).1.pos lo hi k (unpack i).2
  have idx := slot_valid S k
  have inj : Function.Injective P := by
    intro a b eq
    obtain ⟨ex,ey⟩ := Shape.inject (proper _ (idx a).1) (proper _ (idx b).1) (idx a).2 (idx b).2 eq
    exact unpack_inj (Prod.ext ex ey)
  have bound (i : Slot S k) : 0 ≤ (P i).1 ∧ (P i).1 < ((lo+hi+5*k:ℕ):ℤ) ∧
      0 ≤ (P i).2 ∧ (P i).2 < ((lo+hi+5*k:ℕ):ℤ) := by
    have h := Shape.within (proper _ (idx i).1) (idx i).2
    simpa [P,Nat.cast_add,Nat.cast_mul] using And.intro h.1.1 (And.intro h.1.2 h.2)
  have card : Fintype.card (Slot S k)=2*((6*(lo+hi+5*k)-2)/5) := by
    simp only [Slot,Fintype.card_sum,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,count_fixed,count_grow]
    omega
  have witnesses (i : Slot S k) := shape_sound (cert _ (idx i).1) hk (idx i).2
  choose hit hits3 hitSpec using witnesses
  apply realize _ _ P inj bound card hit _ hits3
  intro i a e
  rw [hitSpec]
  constructor
  · rintro ⟨s,hs,j,hj,w⟩
    obtain ⟨z,zu⟩ := pack hs hj
    exact ⟨z,by simpa only [P,zu] using w⟩
  · rintro ⟨z,w⟩
    exact ⟨(unpack z).1,(idx z).1,(unpack z).2,(idx z).2,w⟩

end OMA.ThreePeriodic

namespace OMA.ThreePeriodic.Case0
open OMA.ThreePeriodic
def pattern : List Shape := [
  (.low 0,.low 0), (.low 0,.low 4), (.low 0,.low 7), (.low 0,.high 0), (.low 0,.high 1),
  (.low 0,.high 2), (.low 0,.middle 3), (.low 1,.low 0), (.low 1,.low 2), (.low 2,.low 0),
  (.low 2,.high 4), (.low 3,.low 7), (.low 3,.middle 3), (.low 4,.high 0), (.low 4,.high 1),
  (.low 5,.low 0), (.low 5,.low 1), (.low 6,.low 2), (.low 7,.high 1), (.low 8,.low 1),
  (.low 8,.high 3), (.high 0,.low 0), (.high 0,.low 1), (.high 0,.low 2), (.high 0,.low 5),
  (.high 0,.low 6), (.high 0,.low 8), (.high 0,.high 0), (.high 0,.high 3), (.high 0,.middle 0),
  (.high 0,.middle 2), (.high 0,.middle 4), (.high 1,.high 0), (.high 2,.high 0), (.high 3,.low 0),
  (.high 3,.high 1), (.high 3,.middle 1), (.high 4,.low 0), (.high 5,.low 3), (.high 5,.high 0),
  (.middle 0,.high 0), (.middle 1,.low 1), (.middle 2,.low 2), (.middle 3,.high 1), (.middle 4,.low 1),
  (.middle 4,.high 3)]
theorem proper : ∀ t ∈ pattern, t.proper 9 6=true :=
  List.all_eq_true.mp (by decide +kernel : pattern.all (fun t => t.proper 9 6)=true)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def patternChecked : pattern.all (shapeOK 9 6 pattern) = true := by
  decide +kernel

theorem checked : ∀ t ∈ pattern, shapeOK 9 6 pattern t = true :=
  List.all_eq_true.mp patternChecked

end OMA.ThreePeriodic.Case0

namespace OMA.ThreePeriodic.Case1
open OMA.ThreePeriodic
def pattern : List Shape := [
  (.low 0,.low 0), (.low 0,.low 4), (.low 0,.high 0), (.low 0,.high 1), (.low 0,.high 5),
  (.low 0,.middle 0), (.low 1,.low 0), (.low 1,.high 4), (.low 2,.low 4), (.low 2,.low 5),
  (.low 2,.low 7), (.low 2,.high 0), (.low 2,.middle 2), (.low 3,.low 0), (.low 4,.low 1),
  (.low 5,.low 2), (.low 6,.low 2), (.low 6,.high 0), (.low 7,.high 0), (.low 8,.high 0),
  (.low 9,.low 2), (.low 9,.high 0), (.high 0,.low 0), (.high 0,.low 1), (.high 0,.low 4),
  (.high 0,.high 0), (.high 0,.high 2), (.high 1,.low 4), (.high 1,.low 6), (.high 1,.low 8),
  (.high 1,.low 9), (.high 1,.high 0), (.high 1,.high 3), (.high 1,.middle 1), (.high 1,.middle 3),
  (.high 1,.middle 4), (.high 2,.low 0), (.high 3,.low 0), (.high 4,.low 2), (.high 4,.low 3),
  (.high 5,.high 0), (.middle 0,.low 2), (.middle 1,.low 2), (.middle 1,.high 0), (.middle 2,.high 0),
  (.middle 3,.high 0), (.middle 4,.low 2), (.middle 4,.high 0)]
theorem proper : ∀ t ∈ pattern, t.proper 10 6=true :=
  List.all_eq_true.mp (by decide +kernel : pattern.all (fun t => t.proper 10 6)=true)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def patternChecked : pattern.all (shapeOK 10 6 pattern) = true := by
  decide +kernel

theorem checked : ∀ t ∈ pattern, shapeOK 10 6 pattern t = true :=
  List.all_eq_true.mp patternChecked

end OMA.ThreePeriodic.Case1

namespace OMA.ThreePeriodic.Case2
open OMA.ThreePeriodic
def pattern : List Shape := [
  (.low 0,.low 0), (.low 0,.low 3), (.low 0,.high 0), (.low 0,.high 2), (.low 0,.high 4),
  (.low 0,.high 5), (.low 0,.middle 1), (.low 0,.middle 2), (.low 0,.middle 3), (.low 0,.middle 4),
  (.low 1,.low 0), (.low 1,.high 0), (.low 2,.low 0), (.low 3,.high 0), (.low 4,.low 0),
  (.low 4,.low 2), (.low 5,.low 0), (.high 0,.low 0), (.high 0,.low 2), (.high 0,.high 0),
  (.high 0,.high 3), (.high 1,.low 0), (.high 1,.low 4), (.high 1,.low 5), (.high 1,.high 0),
  (.high 1,.middle 0), (.high 1,.middle 2), (.high 1,.middle 3), (.high 2,.high 0), (.high 3,.low 0),
  (.high 3,.high 1), (.high 4,.low 0), (.high 5,.high 0), (.high 5,.high 1), (.high 5,.high 2),
  (.middle 0,.low 1), (.middle 1,.high 3), (.middle 2,.high 2), (.middle 3,.low 1), (.middle 4,.low 1)]
theorem proper : ∀ t ∈ pattern, t.proper 6 6=true :=
  List.all_eq_true.mp (by decide +kernel : pattern.all (fun t => t.proper 6 6)=true)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def patternChecked : pattern.all (shapeOK 6 6 pattern) = true := by
  decide +kernel

theorem checked : ∀ t ∈ pattern, shapeOK 6 6 pattern t = true :=
  List.all_eq_true.mp patternChecked

end OMA.ThreePeriodic.Case2

namespace OMA.ThreePeriodic.Case3
open OMA.ThreePeriodic
def pattern : List Shape := [
  (.low 0,.low 0), (.low 0,.low 1), (.low 0,.low 3), (.low 0,.low 6), (.low 0,.high 0),
  (.low 0,.high 1), (.low 0,.high 2), (.low 1,.low 4), (.low 1,.low 8), (.low 1,.high 2),
  (.low 1,.high 4), (.low 1,.middle 2), (.low 2,.low 0), (.low 2,.low 9), (.low 2,.middle 3),
  (.low 3,.low 2), (.low 4,.low 0), (.low 4,.high 0), (.low 5,.low 0), (.low 6,.high 0),
  (.low 7,.low 0), (.low 7,.high 0), (.low 8,.low 0), (.low 8,.high 0), (.low 9,.high 0),
  (.low 10,.low 0), (.high 0,.low 0), (.high 0,.low 1), (.high 0,.low 2), (.high 0,.high 0),
  (.high 0,.high 3), (.high 0,.high 6), (.high 1,.low 6), (.high 1,.low 7), (.high 1,.low 10),
  (.high 1,.middle 0), (.high 1,.middle 1), (.high 1,.middle 4), (.high 2,.low 5), (.high 2,.high 0),
  (.high 2,.high 5), (.high 3,.low 0), (.high 4,.low 0), (.high 4,.high 0), (.high 5,.low 0),
  (.high 5,.high 0), (.high 6,.low 0), (.middle 0,.high 0), (.middle 1,.low 0), (.middle 1,.high 0),
  (.middle 2,.low 0), (.middle 2,.high 0), (.middle 3,.high 0), (.middle 4,.low 0)]
theorem proper : ∀ t ∈ pattern, t.proper 11 7=true :=
  List.all_eq_true.mp (by decide +kernel : pattern.all (fun t => t.proper 11 7)=true)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def patternChecked : pattern.all (shapeOK 11 7 pattern) = true := by
  decide +kernel

theorem checked : ∀ t ∈ pattern, shapeOK 11 7 pattern t = true :=
  List.all_eq_true.mp patternChecked

end OMA.ThreePeriodic.Case3

namespace OMA.ThreePeriodic.Case4
open OMA.ThreePeriodic
def pattern : List Shape := [
  (.low 0,.low 0), (.low 0,.low 1), (.low 0,.low 4), (.low 0,.low 5), (.low 0,.high 0),
  (.low 0,.high 3), (.low 1,.high 0), (.low 1,.high 3), (.low 2,.low 4), (.low 2,.low 7),
  (.low 2,.high 0), (.low 2,.middle 1), (.low 2,.middle 2), (.low 2,.middle 4), (.low 3,.low 0),
  (.low 4,.low 3), (.low 5,.high 0), (.low 6,.low 1), (.low 7,.low 1), (.low 7,.high 0),
  (.high 0,.low 0), (.high 0,.low 3), (.high 0,.low 4), (.high 0,.low 6), (.high 0,.high 0),
  (.high 0,.high 1), (.high 0,.high 2), (.high 0,.high 4), (.high 0,.middle 3), (.high 1,.low 0),
  (.high 1,.high 4), (.high 2,.low 0), (.high 3,.high 0), (.high 3,.high 5), (.high 3,.middle 0),
  (.high 4,.low 2), (.high 5,.low 0), (.middle 0,.high 0), (.middle 1,.low 1), (.middle 1,.high 0),
  (.middle 2,.low 1), (.middle 3,.low 1), (.middle 4,.low 1), (.middle 4,.high 0)]
theorem proper : ∀ t ∈ pattern, t.proper 8 6=true :=
  List.all_eq_true.mp (by decide +kernel : pattern.all (fun t => t.proper 8 6)=true)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def patternChecked : pattern.all (shapeOK 8 6 pattern) = true := by
  decide +kernel

theorem checked : ∀ t ∈ pattern, shapeOK 8 6 pattern t = true :=
  List.all_eq_true.mp patternChecked

end OMA.ThreePeriodic.Case4


namespace OMA.ThreePeriodic
open OMA.S_oeis_a051756 Finset

private theorem periodic0 (k : ℕ) (hk : 3 ≤ k) :
    ∃ s : Finset (Square (15+5*k)), valid s ∧ s.card=2*((6*(15+5*k)-2)/5) :=
  large 9 6 Case0.pattern Case0.proper Case0.checked (by decide +kernel) (by decide +kernel) (by decide) k hk

private theorem periodic1 (k : ℕ) (hk : 3 ≤ k) :
    ∃ s : Finset (Square (16+5*k)), valid s ∧ s.card=2*((6*(16+5*k)-2)/5) :=
  large 10 6 Case1.pattern Case1.proper Case1.checked (by decide +kernel) (by decide +kernel) (by decide) k hk

private theorem periodic2 (k : ℕ) (hk : 3 ≤ k) :
    ∃ s : Finset (Square (12+5*k)), valid s ∧ s.card=2*((6*(12+5*k)-2)/5) :=
  large 6 6 Case2.pattern Case2.proper Case2.checked (by decide +kernel) (by decide +kernel) (by decide) k hk

private theorem periodic3 (k : ℕ) (hk : 3 ≤ k) :
    ∃ s : Finset (Square (18+5*k)), valid s ∧ s.card=2*((6*(18+5*k)-2)/5) :=
  large 11 7 Case3.pattern Case3.proper Case3.checked (by decide +kernel) (by decide +kernel) (by decide) k hk

private theorem periodic4 (k : ℕ) (hk : 3 ≤ k) :
    ∃ s : Finset (Square (14+5*k)), valid s ∧ s.card=2*((6*(14+5*k)-2)/5) :=
  large 8 6 Case4.pattern Case4.proper Case4.checked (by decide +kernel) (by decide +kernel) (by decide) k hk

theorem optimal (n : ℕ) (hn : 2≤n) :
    IsGreatest {k : ℕ | ∃ s : Finset (Square n), valid s ∧ s.card=k} (2*((6*n-2)/5)) := by
  constructor
  · change ∃ s : Finset (Square n), valid s ∧ s.card=2*((6*n-2)/5)
    by_cases small : n≤32
    · exact OMA.ThreeWitnesses.small hn small
    have residues : n%5=0 ∨ n%5=1 ∨ n%5=2 ∨ n%5=3 ∨ n%5=4 := by omega
    rcases residues with h | h | h | h | h
    · obtain ⟨k,hk,eq⟩ : ∃ k : ℕ, 3≤k ∧ n=15+5*k := ⟨(n-15)/5,by omega,by omega⟩
      subst n
      exact periodic0 k hk
    · obtain ⟨k,hk,eq⟩ : ∃ k : ℕ, 3≤k ∧ n=16+5*k := ⟨(n-16)/5,by omega,by omega⟩
      subst n
      exact periodic1 k hk
    · obtain ⟨k,hk,eq⟩ : ∃ k : ℕ, 3≤k ∧ n=12+5*k := ⟨(n-12)/5,by omega,by omega⟩
      subst n
      exact periodic2 k hk
    · obtain ⟨k,hk,eq⟩ : ∃ k : ℕ, 3≤k ∧ n=18+5*k := ⟨(n-18)/5,by omega,by omega⟩
      subst n
      exact periodic3 k hk
    · obtain ⟨k,hk,eq⟩ : ∃ k : ℕ, 3≤k ∧ n=14+5*k := ⟨(n-14)/5,by omega,by omega⟩
      subst n
      exact periodic4 k hk
  · rintro k ⟨s,good,rfl⟩
    exact OMA.ThreeAttackers.upper hn good

end OMA.ThreePeriodic

theorem OMA.solution : type_of% @OMA.S_oeis_a051756.main := OMA.ThreePeriodic.optimal
