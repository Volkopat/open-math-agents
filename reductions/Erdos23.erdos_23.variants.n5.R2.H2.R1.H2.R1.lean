import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2_H2_R1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases

/-! For saturated 23-vertex graphs, separate minimum degrees six and seven
from the degree-eight Andrásfai classification. All larger templates admit
a small cut by a finite, kernel-verified enumeration of their class sizes. -/

namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1_H2_R1

namespace AndrasfaiArithmetic

open scoped BigOperators

private def compositions : ℕ → ℕ → List (List ℕ)
  | 0, s => if s = 0 then [[]] else []
  | m + 1, s => (List.range (s + 1)).flatMap fun a =>
      (compositions m (s - a)).map (fun tail => a :: tail)

private theorem mem_compositions (e : List ℕ) : e ∈ compositions e.length e.sum := by
  induction e with
  | nil => simp [compositions]
  | cons a e ih =>
    simp only [List.length_cons, List.sum_cons, compositions, List.mem_flatMap, List.mem_range]
    refine ⟨a, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact List.mem_map.mpr ⟨e, ih, rfl⟩

private def color (m s i : ℕ) : Bool := decide ((i + m - s) % m < m / 2)

private def adjacent (m k i j : ℕ) : Bool :=
  decide (k ≤ (j + m - i) % m ∧ (j + m - i) % m < 2 * k)

private def charged (m k s i j : ℕ) : Bool :=
  decide (i < j) && adjacent m k i j && decide (color m s i = color m s j)

private def weights (m k : ℕ) (e : List ℕ) (i : ℕ) : ℕ :=
  1 + (e[(i+m-k)%m]?.getD 0) + (e[i % m]?.getD 0) + (e[(i+k)%m]?.getD 0)

private def pairs (m k s : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun i =>
    ((List.range m).filter fun j => charged m k s i j).map fun j => (i,j)

private def pairCost (m k : ℕ) (e : List ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  (ps.map fun (i,j) => weights m k e i * weights m k e j).sum

private def cost (m k : ℕ) (e : List ℕ) (s : ℕ) : ℕ := pairCost m k e (pairs m k s)

private theorem sum_mapped_filter {α : Type*} (xs : List α) (p : α → Bool) (f : α → ℕ) :
    ((xs.filter p).map f).sum = (xs.map fun x => if p x then f x else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases h : p x <;> simp [h, ih]

private theorem sum_flatMap {α : Type*} (xs : List α) (f : α → List ℕ) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.sum_append, ih]

private theorem sum_finRange_val (m : ℕ) (f : ℕ → ℕ) :
    ((List.finRange m).map fun i => f i.val).sum = ((List.range m).map f).sum := by
  have hmap : (List.finRange m).map Fin.val = List.range m := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  change ((List.finRange m).map (f ∘ Fin.val)).sum = _
  rw [← List.map_map, hmap]

private theorem cost_eq (m k : ℕ) (e : List ℕ) (s : ℕ) :
    cost m k e s = ∑ i : Fin m, ∑ j : Fin m, if charged m k s i.val j.val then
      weights m k e i.val * weights m k e j.val else 0 := by
  simp only [cost, pairCost, pairs, List.map_flatMap, sum_flatMap, List.map_map,
    Function.comp_apply, sum_mapped_filter, Fin.sum_univ_def]
  let f (i j : ℕ) :=
    if charged m k s i j then weights m k e i * weights m k e j else 0
  change ((List.range m).map (fun i => ((List.range m).map (f i)).sum)).sum =
    ((List.finRange m).map (fun i =>
      ((List.finRange m).map (fun j => f i.val j.val)).sum)).sum
  have inner (i : Fin m) := sum_finRange_val m (f i.val)
  simp_rw [inner]
  exact (sum_finRange_val m (fun i => ((List.range m).map (f i)).sum)).symm

/-- The ordered lists of charged template edges, one list for each rotation.
The six pool lemmas below verify this data against its definition. -/
private def cutData : ℕ → List (List (ℕ × ℕ))
  | 3 => [
    [(0,3),(4,7)],
    [(0,5),(1,4)],
    [(1,6),(2,5)],
    [(2,7),(3,6)],
    [(0,3),(4,7)],
    [(0,5),(1,4)],
    [(1,6),(2,5)],
    [(2,7),(3,6)]]
  | 4 => [
    [(0,4),(5,9),(5,10),(6,10)],
    [(0,6),(0,7),(1,5),(6,10)],
    [(0,7),(1,7),(1,8),(2,6)],
    [(1,8),(2,8),(2,9),(3,7)],
    [(2,9),(3,9),(3,10),(4,8)],
    [(0,4),(3,10),(4,10),(5,9)],
    [(0,4),(0,5),(1,5),(6,10)],
    [(0,7),(1,5),(1,6),(2,6)],
    [(1,8),(2,6),(2,7),(3,7)],
    [(2,9),(3,7),(3,8),(4,8)],
    [(3,10),(4,8),(4,9),(5,9)]]
  | 5 => [
    [(0,5),(0,6),(1,6),(7,12),(7,13),(8,13)],
    [(0,8),(0,9),(1,6),(1,7),(2,7),(8,13)],
    [(0,9),(1,9),(1,10),(2,7),(2,8),(3,8)],
    [(1,10),(2,10),(2,11),(3,8),(3,9),(4,9)],
    [(2,11),(3,11),(3,12),(4,9),(4,10),(5,10)],
    [(3,12),(4,12),(4,13),(5,10),(5,11),(6,11)],
    [(0,5),(4,13),(5,13),(6,11),(6,12),(7,12)],
    [(0,5),(0,6),(1,6),(7,12),(7,13),(8,13)],
    [(0,8),(0,9),(1,6),(1,7),(2,7),(8,13)],
    [(0,9),(1,9),(1,10),(2,7),(2,8),(3,8)],
    [(1,10),(2,10),(2,11),(3,8),(3,9),(4,9)],
    [(2,11),(3,11),(3,12),(4,9),(4,10),(5,10)],
    [(3,12),(4,12),(4,13),(5,10),(5,11),(6,11)],
    [(0,5),(4,13),(5,13),(6,11),(6,12),(7,12)]]
  | 6 => [
    [(0,6),(0,7),(1,7),(8,14),(8,15),(8,16),(9,15),(9,16),(10,16)],
    [(0,9),(0,10),(0,11),(1,7),(1,8),(2,8),(9,15),(9,16),(10,16)],
    [(0,10),(0,11),(1,10),(1,11),(1,12),(2,8),(2,9),(3,9),(10,16)],
    [(0,11),(1,11),(1,12),(2,11),(2,12),(2,13),(3,9),(3,10),(4,10)],
    [(1,12),(2,12),(2,13),(3,12),(3,13),(3,14),(4,10),(4,11),(5,11)],
    [(2,13),(3,13),(3,14),(4,13),(4,14),(4,15),(5,11),(5,12),(6,12)],
    [(3,14),(4,14),(4,15),(5,14),(5,15),(5,16),(6,12),(6,13),(7,13)],
    [(0,6),(4,15),(5,15),(5,16),(6,15),(6,16),(7,13),(7,14),(8,14)],
    [(0,6),(0,7),(1,7),(5,16),(6,16),(7,16),(8,14),(8,15),(9,15)],
    [(0,6),(0,7),(0,8),(1,7),(1,8),(2,8),(9,15),(9,16),(10,16)],
    [(0,10),(0,11),(1,7),(1,8),(1,9),(2,8),(2,9),(3,9),(10,16)],
    [(0,11),(1,11),(1,12),(2,8),(2,9),(2,10),(3,9),(3,10),(4,10)],
    [(1,12),(2,12),(2,13),(3,9),(3,10),(3,11),(4,10),(4,11),(5,11)],
    [(2,13),(3,13),(3,14),(4,10),(4,11),(4,12),(5,11),(5,12),(6,12)],
    [(3,14),(4,14),(4,15),(5,11),(5,12),(5,13),(6,12),(6,13),(7,13)],
    [(4,15),(5,15),(5,16),(6,12),(6,13),(6,14),(7,13),(7,14),(8,14)],
    [(0,6),(5,16),(6,16),(7,13),(7,14),(7,15),(8,14),(8,15),(9,15)]]
  | 7 => [
    [(0,7),(0,8),(0,9),(1,8),(1,9),(2,9),(10,17),(10,18),(10,19),(11,18),(11,19),(12,19)],
    [(0,11),(0,12),(0,13),(1,8),(1,9),(1,10),(2,9),(2,10),(3,10),(11,18),(11,19),(12,19)],
    [(0,12),(0,13),(1,12),(1,13),(1,14),(2,9),(2,10),(2,11),(3,10),(3,11),(4,11),(12,19)],
    [(0,13),(1,13),(1,14),(2,13),(2,14),(2,15),(3,10),(3,11),(3,12),(4,11),(4,12),(5,12)],
    [(1,14),(2,14),(2,15),(3,14),(3,15),(3,16),(4,11),(4,12),(4,13),(5,12),(5,13),(6,13)],
    [(2,15),(3,15),(3,16),(4,15),(4,16),(4,17),(5,12),(5,13),(5,14),(6,13),(6,14),(7,14)],
    [(3,16),(4,16),(4,17),(5,16),(5,17),(5,18),(6,13),(6,14),(6,15),(7,14),(7,15),(8,15)],
    [(4,17),(5,17),(5,18),(6,17),(6,18),(6,19),(7,14),(7,15),(7,16),(8,15),(8,16),(9,16)],
    [(0,7),(5,18),(6,18),(6,19),(7,18),(7,19),(8,15),(8,16),(8,17),(9,16),(9,17),(10,17)],
    [(0,7),(0,8),(1,8),(6,19),(7,19),(8,19),(9,16),(9,17),(9,18),(10,17),(10,18),(11,18)],
    [(0,7),(0,8),(0,9),(1,8),(1,9),(2,9),(10,17),(10,18),(10,19),(11,18),(11,19),(12,19)],
    [(0,11),(0,12),(0,13),(1,8),(1,9),(1,10),(2,9),(2,10),(3,10),(11,18),(11,19),(12,19)],
    [(0,12),(0,13),(1,12),(1,13),(1,14),(2,9),(2,10),(2,11),(3,10),(3,11),(4,11),(12,19)],
    [(0,13),(1,13),(1,14),(2,13),(2,14),(2,15),(3,10),(3,11),(3,12),(4,11),(4,12),(5,12)],
    [(1,14),(2,14),(2,15),(3,14),(3,15),(3,16),(4,11),(4,12),(4,13),(5,12),(5,13),(6,13)],
    [(2,15),(3,15),(3,16),(4,15),(4,16),(4,17),(5,12),(5,13),(5,14),(6,13),(6,14),(7,14)],
    [(3,16),(4,16),(4,17),(5,16),(5,17),(5,18),(6,13),(6,14),(6,15),(7,14),(7,15),(8,15)],
    [(4,17),(5,17),(5,18),(6,17),(6,18),(6,19),(7,14),(7,15),(7,16),(8,15),(8,16),(9,16)],
    [(0,7),(5,18),(6,18),(6,19),(7,18),(7,19),(8,15),(8,16),(8,17),(9,16),(9,17),(10,17)],
    [(0,7),(0,8),(1,8),(6,19),(7,19),(8,19),(9,16),(9,17),(9,18),(10,17),(10,18),(11,18)]]
  | 8 => [
    [(0,8),(0,9),(0,10),(1,9),(1,10),(2,10),(11,19),(11,20),(11,21),(11,22),(12,20),(12,21),(12,22),(13,21),(13,22),(14,22)],
    [(0,12),(0,13),(0,14),(0,15),(1,9),(1,10),(1,11),(2,10),(2,11),(3,11),(12,20),(12,21),(12,22),(13,21),(13,22),(14,22)],
    [(0,13),(0,14),(0,15),(1,13),(1,14),(1,15),(1,16),(2,10),(2,11),(2,12),(3,11),(3,12),(4,12),(13,21),(13,22),(14,22)],
    [(0,14),(0,15),(1,14),(1,15),(1,16),(2,14),(2,15),(2,16),(2,17),(3,11),(3,12),(3,13),(4,12),(4,13),(5,13),(14,22)],
    [(0,15),(1,15),(1,16),(2,15),(2,16),(2,17),(3,15),(3,16),(3,17),(3,18),(4,12),(4,13),(4,14),(5,13),(5,14),(6,14)],
    [(1,16),(2,16),(2,17),(3,16),(3,17),(3,18),(4,16),(4,17),(4,18),(4,19),(5,13),(5,14),(5,15),(6,14),(6,15),(7,15)],
    [(2,17),(3,17),(3,18),(4,17),(4,18),(4,19),(5,17),(5,18),(5,19),(5,20),(6,14),(6,15),(6,16),(7,15),(7,16),(8,16)],
    [(3,18),(4,18),(4,19),(5,18),(5,19),(5,20),(6,18),(6,19),(6,20),(6,21),(7,15),(7,16),(7,17),(8,16),(8,17),(9,17)],
    [(4,19),(5,19),(5,20),(6,19),(6,20),(6,21),(7,19),(7,20),(7,21),(7,22),(8,16),(8,17),(8,18),(9,17),(9,18),(10,18)],
    [(0,8),(5,20),(6,20),(6,21),(7,20),(7,21),(7,22),(8,20),(8,21),(8,22),(9,17),(9,18),(9,19),(10,18),(10,19),(11,19)],
    [(0,8),(0,9),(1,9),(6,21),(7,21),(7,22),(8,21),(8,22),(9,21),(9,22),(10,18),(10,19),(10,20),(11,19),(11,20),(12,20)],
    [(0,8),(0,9),(0,10),(1,9),(1,10),(2,10),(7,22),(8,22),(9,22),(10,22),(11,19),(11,20),(11,21),(12,20),(12,21),(13,21)],
    [(0,8),(0,9),(0,10),(0,11),(1,9),(1,10),(1,11),(2,10),(2,11),(3,11),(12,20),(12,21),(12,22),(13,21),(13,22),(14,22)],
    [(0,13),(0,14),(0,15),(1,9),(1,10),(1,11),(1,12),(2,10),(2,11),(2,12),(3,11),(3,12),(4,12),(13,21),(13,22),(14,22)],
    [(0,14),(0,15),(1,14),(1,15),(1,16),(2,10),(2,11),(2,12),(2,13),(3,11),(3,12),(3,13),(4,12),(4,13),(5,13),(14,22)],
    [(0,15),(1,15),(1,16),(2,15),(2,16),(2,17),(3,11),(3,12),(3,13),(3,14),(4,12),(4,13),(4,14),(5,13),(5,14),(6,14)],
    [(1,16),(2,16),(2,17),(3,16),(3,17),(3,18),(4,12),(4,13),(4,14),(4,15),(5,13),(5,14),(5,15),(6,14),(6,15),(7,15)],
    [(2,17),(3,17),(3,18),(4,17),(4,18),(4,19),(5,13),(5,14),(5,15),(5,16),(6,14),(6,15),(6,16),(7,15),(7,16),(8,16)],
    [(3,18),(4,18),(4,19),(5,18),(5,19),(5,20),(6,14),(6,15),(6,16),(6,17),(7,15),(7,16),(7,17),(8,16),(8,17),(9,17)],
    [(4,19),(5,19),(5,20),(6,19),(6,20),(6,21),(7,15),(7,16),(7,17),(7,18),(8,16),(8,17),(8,18),(9,17),(9,18),(10,18)],
    [(5,20),(6,20),(6,21),(7,20),(7,21),(7,22),(8,16),(8,17),(8,18),(8,19),(9,17),(9,18),(9,19),(10,18),(10,19),(11,19)],
    [(0,8),(6,21),(7,21),(7,22),(8,21),(8,22),(9,17),(9,18),(9,19),(9,20),(10,18),(10,19),(10,20),(11,19),(11,20),(12,20)],
    [(0,8),(0,9),(1,9),(7,22),(8,22),(9,22),(10,18),(10,19),(10,20),(10,21),(11,19),(11,20),(11,21),(12,20),(12,21),(13,21)]]
  | _ => []

private def passed (k : ℕ) (e : List ℕ) : Bool :=
  (cutData k).any fun ps => decide (pairCost (3*k-1) k e ps ≤ 19)

set_option maxRecDepth 12000 in
private theorem pool_3 : cutData 3 = (List.range 8).map (pairs 8 3) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
private theorem check_3 : (compositions 8 5).all (passed 3) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
private theorem pool_4 : cutData 4 = (List.range 11).map (pairs 11 4) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
private theorem check_4 : (compositions 11 4).all (passed 4) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
private theorem pool_5 : cutData 5 = (List.range 14).map (pairs 14 5) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
private theorem check_5 : (compositions 14 3).all (passed 5) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
private theorem pool_6 : cutData 6 = (List.range 17).map (pairs 17 6) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
private theorem check_6 : (compositions 17 2).all (passed 6) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
private theorem pool_7 : cutData 7 = (List.range 20).map (pairs 20 7) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
private theorem check_7 : (compositions 20 1).all (passed 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
private theorem pool_8 : cutData 8 = (List.range 23).map (pairs 23 8) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
private theorem check_8 : (compositions 23 0).all (passed 8) = true := by
  decide +kernel

private theorem verified_cut (k : ℕ) (hk : 3 ≤ k) (hK : k ≤ 8) (e : List ℕ)
    (he : e.length = 3*k-1) (hSum : e.sum = 8-k) :
    ∃ s < 3*k-1, cost (3*k-1) k e s ≤ 19 := by
  have cases : k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
  have all : (compositions (3*k-1) (8-k)).all (passed k) = true := by
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact check_3
    · exact check_4
    · exact check_5
    · exact check_6
    · exact check_7
    · exact check_8
  have table : cutData k = (List.range (3*k-1)).map (pairs (3*k-1) k) := by
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact pool_3
    · exact pool_4
    · exact pool_5
    · exact pool_6
    · exact pool_7
    · exact pool_8
  have m := mem_compositions e
  rw [he, hSum] at m
  have one := List.all_eq_true.mp all e m
  obtain ⟨ps, hps, pass⟩ := List.any_eq_true.mp one
  rw [table] at hps
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hps
  exact ⟨s, List.mem_range.mp hs, of_decide_eq_true pass⟩

end AndrasfaiArithmetic

namespace AndrasfaiBridge

open Finset
open scoped BigOperators

private def classes (r : Fin 6) : ℕ := 3 * r.val + 8
private def rank (r : Fin 6) : ℕ := r.val + 3

private def edge (r : Fin 6) (i j : Fin (classes r)) : Bool :=
  decide (rank r ≤ (j.val + classes r - i.val) % classes r ∧
    (j.val + classes r - i.val) % classes r < 2 * rank r)

private def leftShift (r : Fin 6) (i : Fin (classes r)) : Fin (classes r) :=
  ⟨(i.val + classes r - rank r) % classes r, Nat.mod_lt _ (by unfold classes; omega)⟩

private def rightShift (r : Fin 6) (i : Fin (classes r)) : Fin (classes r) :=
  ⟨(i.val + rank r) % classes r, Nat.mod_lt _ (by unfold classes; omega)⟩

private theorem period_cover (r : Fin 6) : ∀ i j : Fin (classes r),
    (if edge r (leftShift r i) j then (1 : ℕ) else 0) +
    (if edge r i j then 1 else 0) +
    (if edge r (rightShift r i) j then 1 else 0) =
      1 + (if i = j then 1 else 0) := by
  fin_cases r <;> decide +kernel

private theorem degree_count (r : Fin 6) : ∀ j : Fin (classes r),
    (∑ i : Fin (classes r), if edge r i j then (1 : ℕ) else 0) = rank r := by
  fin_cases r <;> decide +kernel

private def degree (r : Fin 6) (w : Fin (classes r) → ℕ) (i : Fin (classes r)) : ℕ :=
  ∑ j, if edge r i j then w j else 0

private theorem weight_formula (r : Fin 6) (w : Fin (classes r) → ℕ)
    (sumW : ∑ i, w i = 23) (hdeg : ∀ i, 8 ≤ degree r w i) :
    ∃ e : Fin (classes r) → ℕ, (∑ i, e i) = 8 - rank r ∧
      ∀ i, w i = 1 + e (leftShift r i) + e i + e (rightShift r i) := by
  let e (i : Fin (classes r)) := degree r w i - 8
  have de (i) : degree r w i = 8 + e i := by unfold e; have := hdeg i; omega
  have degrees : (∑ i, degree r w i) = rank r * 23 := by
    calc
      _ = ∑ j, ∑ i, (if edge r i j then 1 else 0) * w j := by
        unfold AndrasfaiBridge.degree
        rw [sum_comm]
        apply sum_congr rfl
        intro j _
        apply sum_congr rfl
        intro i _
        by_cases hij : edge r i j = true <;> simp [hij]
      _ = ∑ j, rank r * w j := by simp_rw [← sum_mul, degree_count]
      _ = _ := by rw [← mul_sum, sumW]
  have sumE : (∑ i, e i) = 8 - rank r := by
    simp only [de, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul] at degrees
    have rlt := r.isLt
    change (3 * r.val + 8) * 8 + (∑ i, e i) = (r.val + 3) * 23 at degrees
    change (∑ i, e i) = 8 - (r.val + 3)
    omega
  refine ⟨e, sumE, ?_⟩
  intro i
  have dsum : degree r w (leftShift r i) + degree r w i + degree r w (rightShift r i) =
      23 + w i := by
    unfold AndrasfaiBridge.degree
    rw [← sum_add_distrib, ← sum_add_distrib]
    have terms (j : Fin (classes r)) :
        (if edge r (leftShift r i) j then w j else 0) +
        (if edge r i j then w j else 0) +
        (if edge r (rightShift r i) j then w j else 0) =
          w j + (if i = j then w j else 0) := by
      have h := congrArg (fun a : ℕ => a * w j) (period_cover r i j)
      simpa only [add_mul, ite_mul, one_mul, zero_mul] using h
    simp_rw [terms]
    rw [sum_add_distrib, sumW]
    simp
  rw [de, de, de] at dsum
  omega

private theorem weighted_sum {α β : Type*} [Fintype β] [DecidableEq β]
    (W : Finset α) (f : α → β) (g : β → ℕ) :
    (∑ x ∈ W, g (f x)) = ∑ i, (W.filter (fun x => f x = i)).card * g i := by
  rw [← sum_fiberwise' W f g]
  simp

private theorem twice_weighted_sum {α β : Type*} [Fintype β] [DecidableEq β]
    (W : Finset α) (f : α → β) (g : β → β → ℕ) :
    (∑ x ∈ W, ∑ y ∈ W, g (f x) (f y)) =
      ∑ i, ∑ j, (W.filter (fun x => f x = i)).card *
        (W.filter (fun y => f y = j)).card * g i j := by
  rw [weighted_sum W f (fun i => ∑ y ∈ W, g i (f y))]
  simp_rw [weighted_sum W f (g _), mul_sum, mul_assoc]

end AndrasfaiBridge


open Finset SimpleGraph AndrasfaiBridge
open scoped BigOperators Classical

private theorem edge_comm (r : Fin 6) :
    ∀ i j : Fin (classes r), edge r i j = edge r j i := by
  fin_cases r <;> decide +kernel

private theorem edge_self (r : Fin 6) : ∀ i : Fin (classes r), edge r i i = false := by
  fin_cases r <;> decide +kernel

/-- Group vertices by their template class, then apply a verified rotating cut. -/
private theorem template_cut (W : Finset (Fin 25)) (K : SimpleGraph (Fin 25))
    (hW : W.card = 23) (minDegree : ∀ u ∈ W, 8 ≤ (W.filter (K.Adj u)).card)
    (r : Fin 6) (f : Fin 25 → Fin (classes r))
    (hit : ∀ i, ∃ u ∈ W, f u = i)
    (edge_iff : ∀ u ∈ W, ∀ v ∈ W, K.Adj u v ↔ edge r (f u) (f v) = true) :
    ∃ c : Fin 25 → Bool, (∑ u ∈ W, ∑ v ∈ W,
      if K.Adj u v ∧ c u = c v then 1 else 0) ≤ (38 : ℕ) := by
  classical
  let w (i : Fin (classes r)) := (W.filter (fun u => f u = i)).card
  have sumW : (∑ i, w i) = 23 := by
    have hcount := weighted_sum W f (fun _ => 1)
    simpa [w, hW] using hcount.symm
  have hdeg (i : Fin (classes r)) : 8 ≤ degree r w i := by
    obtain ⟨u, hu, heq⟩ := hit i
    calc
      8 ≤ (W.filter (K.Adj u)).card := minDegree u hu
      _ = ∑ v ∈ W, if edge r i (f v) then 1 else 0 := by
        rw [card_filter]
        apply sum_congr rfl
        intro v hv
        simp only [edge_iff u hu v hv, heq]
      _ = degree r w i := by
        rw [weighted_sum W f (fun j => if edge r i j then 1 else 0)]
        unfold AndrasfaiBridge.degree
        apply sum_congr rfl
        intro j _
        by_cases h : edge r i j = true <;> simp [w, h]
  obtain ⟨e, he, hw⟩ := weight_formula r w sumW hdeg
  let values := List.ofFn e
  have shape : classes r = 3 * rank r - 1 := by unfold classes rank; omega
  have positiveRank : 3 ≤ rank r := by unfold rank; omega
  have maxRank : rank r ≤ 8 := by have := r.isLt; unfold rank; omega
  obtain ⟨s, hs, verified⟩ := AndrasfaiArithmetic.verified_cut (rank r) positiveRank maxRank values
    (by simp [values, shape]) (by simpa only [values, Fin.sum_ofFn] using he)
  rw [← shape] at verified
  let colour (i : Fin (classes r)) := AndrasfaiArithmetic.color (classes r) s i.val
  let term (i j : Fin (classes r)) : ℕ :=
    if edge r i j = true ∧ colour i = colour j then w i * w j else 0
  have digit (i : Fin (classes r)) : (values[i.val]?.getD 0) = e i := by
    have bound : i.val < values.length := by simpa only [values, List.length_ofFn] using i.isLt
    rw [List.getElem?_eq_getElem bound, Option.getD_some]
    simp [values]
  have weight (i : Fin (classes r)) :
      AndrasfaiArithmetic.weights (classes r) (rank r) values i.val = w i := by
    rw [hw i]
    unfold AndrasfaiArithmetic.weights
    rw [Nat.mod_eq_of_lt i.isLt]
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·)
      (congrArg (1 + ·) (digit (leftShift r i))) (digit i)) (digit (rightShift r i))
  have halved : AndrasfaiArithmetic.cost (classes r) (rank r) values s =
      ∑ i : Fin (classes r), ∑ j : Fin (classes r), if i < j then term i j else 0 := by
    rw [AndrasfaiArithmetic.cost_eq]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [weight i, weight j]
    change (if (decide (i.val < j.val) && edge r i j && decide (colour i = colour j)) then
      w i * w j else 0) = _
    by_cases hij : i < j
    · have hv : i.val < j.val := hij
      by_cases hE : edge r i j = true <;> by_cases hC : colour i = colour j <;>
        simp [term, hij, hv, hE, hC]
    · have hv : ¬ i.val < j.val := hij
      simp [hij, hv]
  have symm (i j) : term i j = term j i := by
    have same : (edge r i j = true ∧ colour i = colour j) ↔
        (edge r j i = true ∧ colour j = colour i) := by
      rw [edge_comm r j i]
      exact and_congr_right fun _ => eq_comm
    unfold term
    by_cases h : edge r i j = true ∧ colour i = colour j
    · rw [if_pos h, if_pos (same.mp h), Nat.mul_comm]
    · rw [if_neg h, if_neg (fun h' => h (same.mpr h'))]
  have loop (i) : term i i = 0 := by simp [term, edge_self]
  have pairCount := OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1.unordered (univ : Finset (Fin (classes r))) term symm loop
  have exactCost : (∑ i : Fin (classes r), ∑ j : Fin (classes r), term i j) =
      2 * AndrasfaiArithmetic.cost (classes r) (rank r) values s := by
    rw [halved]
    exact pairCount
  let costTerm (i j : Fin (classes r)) : ℕ :=
    if edge r i j = true ∧ colour i = colour j then 1 else 0
  refine ⟨colour ∘ f, ?_⟩
  have counted : (∑ u ∈ W, ∑ v ∈ W, if K.Adj u v ∧ (colour ∘ f) u = (colour ∘ f) v
    then 1 else 0) = ∑ i : Fin (classes r), ∑ j : Fin (classes r), term i j := by
    calc
      _ = ∑ u ∈ W, ∑ v ∈ W, costTerm (f u) (f v) := by
        apply sum_congr rfl
        intro u hu
        apply sum_congr rfl
        intro v hv
        simp only [edge_iff u hu v hv, Function.comp_apply, costTerm]
      _ = ∑ i : Fin (classes r), ∑ j : Fin (classes r), w i * w j * costTerm i j :=
        twice_weighted_sum W f costTerm
      _ = _ := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        by_cases h : edge r i j = true ∧ colour i = colour j <;> simp [costTerm, term, h]
  rw [counted, exactCost]
  omega

/-- The extremal classification for the only lower minimum degrees, six and seven. -/
def H1 : Prop := ∀ (W : Finset (Fin 25)), W.card = 23 → ∀ K : SimpleGraph (Fin 25),
  K.CliqueFree 3 → (∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W) →
  (∀ H : SimpleGraph (Fin 25), K ≤ H → H.CliqueFree 3 →
    (∀ i j, H.Adj i j → i ∈ W ∧ j ∈ W) → H = K) →
  (∀ i ∈ W, 6 ≤ (W.filter (K.Adj i)).card) →
  (∃ v ∈ W, (W.filter (K.Adj v)).card ≤ 7) →
  (∀ c : Fin 25 → Bool, (38 : ℕ) < ∑ i ∈ W, ∑ j ∈ W,
     if K.Adj i j ∧ c i = c j then 1 else 0) →
  ∃ f : Fin 25 → Fin 5, ∀ i j, K.Adj i j → f i + 1 = f j ∨ f j + 1 = f i

/-- The degree-eight structural theorem for saturated graphs. Use the smallest
Andrásfai template and record its classes. The total degree bounds its rank by eight. -/
def H2 : Prop := ∀ (W : Finset (Fin 25)), W.card = 23 → ∀ K : SimpleGraph (Fin 25),
  K.CliqueFree 3 → (∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W) →
  (∀ H : SimpleGraph (Fin 25), K ≤ H → H.CliqueFree 3 →
    (∀ i j, H.Adj i j → i ∈ W ∧ j ∈ W) → H = K) →
  (∀ i ∈ W, 8 ≤ (W.filter (K.Adj i)).card) →
  (∃ f : Fin 25 → Fin 5, ∀ i j, K.Adj i j → f i + 1 = f j ∨ f j + 1 = f i) ∨
  ∃ r : Fin 6, let m := 3 * r.val + 8
    let k := r.val + 3
    ∃ f : Fin 25 → Fin m, (∀ i, ∃ u ∈ W, f u = i) ∧
      ∀ u ∈ W, ∀ v ∈ W, K.Adj u v ↔
        let d := ((f v).val + m - (f u).val) % m
        k ≤ d ∧ d < 2 * k

theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1.H2 := by
  intro low high W hW K hfree hsupport hmax hmin hbad
  by_cases slow : ∃ v ∈ W, (W.filter (K.Adj v)).card ≤ 7
  · exact low W hW K hfree hsupport hmax hmin slow hbad
  have fast : ∀ v ∈ W, 8 ≤ (W.filter (K.Adj v)).card := by
    intro v hv
    by_contra! h
    exact slow ⟨v, hv, by omega⟩
  rcases high W hW K hfree hsupport hmax fast with done | ⟨r, f, hit, hedges⟩
  · exact done
  have hedge : ∀ u ∈ W, ∀ v ∈ W, K.Adj u v ↔ edge r (f u) (f v) = true := by
    intro u hu v hv
    constructor
    · intro h
      exact decide_eq_true ((hedges u hu v hv).mp h)
    · intro h
      exact (hedges u hu v hv).mpr (of_decide_eq_true h)
  obtain ⟨c, hc⟩ := template_cut W K hW fast r f hit hedge
  exact ((hbad c).not_ge hc).elim

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1_H2_R1
