import OMAStatements.S_mo_443260
import Mathlib

open scoped BigOperators

private def encoding (s : Finset (Fin 5)) : ℕ := ∑ i ∈ s, 2 ^ i.val

private def position (mask : ℕ) : ℕ :=
  (#[0, 1, 2, 3, 4, 5, 7, 10, 6, 8, 11, 13, 14, 15, 19, 22,
     9, 12, 16, 17, 18, 20, 23, 25, 21, 24, 26, 27, 28, 29, 30, 31] : Array ℕ)[mask]!

private def rank (s : Finset (Fin 5)) : ℕ := position (encoding s)

private theorem encodingBound : ∀ s : Finset (Fin 5), encoding s < 32 := by decide +kernel

private theorem distinctRanks : Function.Injective rank := by
  change ∀ (s t : Finset (Fin 5)), rank s = rank t → s = t
  decide +kernel

private theorem unionMask : ∀ s t : Finset (Fin 5),
    encoding (s ∪ t) = (encoding s ||| encoding t) := by decide +kernel

private theorem disjointMask : ∀ s t : Finset (Fin 5),
    Disjoint s t → (encoding s &&& encoding t) = 0 := by decide +kernel

private def ordered : LinearOrder (Finset (Fin 5)) :=
  LinearOrder.lift' rank distinctRanks

private def compatible (a c b d : ℕ) : Bool :=
  if position a < position c ∧ position b ≤ position d ∧ (a &&& b) = 0 ∧ (c &&& d) = 0
  then decide (position (a ||| b) < position (c ||| d))
  else true

private def row (a : ℕ) : Bool :=
  (List.range 32).all (fun c =>
    (List.range 32).all (fun b =>
      (List.range 32).all (fun d => compatible a c b d)))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rows (a : Fin 32) : row a.val = true := by
  fin_cases a <;> decide +kernel

private theorem check (a c b d : Fin 32) : compatible a.val c.val b.val d.val = true := by
  have first := List.all_eq_true.mp (rows a) c.val (List.mem_range.mpr c.isLt)
  have second := List.all_eq_true.mp first b.val (List.mem_range.mpr b.isLt)
  exact List.all_eq_true.mp second d.val (List.mem_range.mpr d.isLt)

private theorem sumsCompatible (a c b d : Finset (Fin 5)) :
    ordered.lt a c → ordered.le b d → Disjoint a b → Disjoint c d →
      ordered.lt (a ∪ b) (c ∪ d) := by
  intro hac hbd hab hcd
  have h := check ⟨encoding a, encodingBound a⟩ ⟨encoding c, encodingBound c⟩
    ⟨encoding b, encodingBound b⟩ ⟨encoding d, encodingBound d⟩
  change position (encoding a) < position (encoding c) at hac
  change position (encoding b) ≤ position (encoding d) at hbd
  change position (encoding (a ∪ b)) < position (encoding (c ∪ d))
  rw [unionMask, unionMask]
  simpa [compatible, hac, hbd, disjointMask a b hab, disjointMask c d hcd] using h

private theorem pairSum (f : Fin 5 → ℝ) (a b : Fin 5) (hab : a ≠ b) :
    (∑ i ∈ ({a, b} : Finset (Fin 5)), f i) = f a + f b := by
  rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using hab), Finset.sum_singleton]

private theorem tripleSum (f : Fin 5 → ℝ) (a b c : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ i ∈ ({a, b, c} : Finset (Fin 5)), f i) = f a + (f b + f c) := by
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hab, hac⟩),
    pairSum f b c hbc]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_443260.main) := by
  intro proposed
  obtain ⟨f, agrees⟩ := proposed 5 ordered sumsCompatible
  have h1 := (agrees ({0, 1} : Finset (Fin 5)) {2}).mp (by decide)
  have h2 := (agrees ({1, 2} : Finset (Fin 5)) {0, 3}).mp (by decide)
  have h3 := (agrees ({0, 2, 3} : Finset (Fin 5)) {1, 4}).mp (by decide)
  have h4 := (agrees ({4} : Finset (Fin 5)) {0, 1, 2}).mp (by decide)
  rw [pairSum f 0 1 (by decide), Finset.sum_singleton] at h1
  rw [pairSum f 1 2 (by decide), pairSum f 0 3 (by decide)] at h2
  rw [tripleSum f 0 2 3 (by decide) (by decide) (by decide), pairSum f 1 4 (by decide)] at h3
  rw [Finset.sum_singleton, tripleSum f 0 1 2 (by decide) (by decide) (by decide)] at h4
  linarith