import OMAReductions.R_UnionClosed_union_closed_R1_H3_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
Partition the family by the part outside the given triple. Each trace
family contains the whole triple and is union-closed. Its positive
deficit is one of six small patterns, each containing the empty trace.
Summing the deficits gives the number of required outside witnesses.
-/

namespace OMA.UnionClosedTrace

open Finset

private abbrev Trace := Finset (Fin 3)
private abbrev TraceFamily := Finset Trace

private theorem trace_univ : (univ : TraceFamily) =
    {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, (univ : Trace)} := by
  decide

private def memberBit (P : TraceFamily) (T : Trace) : Bool := decide (T ∈ P)

private def bit (b : Bool) : ℤ := if b then 1 else 0

private def maskDefect (e a b c ab ac bc : Bool) : ℤ :=
  3 * bit e + bit a + bit b + bit c - bit ab - bit ac - bit bc - 3

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1500000 in
set_option synthInstance.maxSize 512 in
private theorem mask_profile :
    ∀ e a b c ab ac bc : Bool,
      (a = true → b = true → ab = true) →
      (a = true → c = true → ac = true) →
      (b = true → c = true → bc = true) →
      maskDefect e a b c ab ac bc ≤ 1 ∧
        (0 < maskDefect e a b c ab ac bc →
          e = true ∧ (a = true ∨ b = true ∨ c = true) ∧
          ¬ (a = true ∧ b = true ∧ c = true) ∧
          ab = (a && b) ∧ ac = (a && c) ∧ bc = (b && c)) := by
  intro e a b c
  cases e <;> cases a <;> cases b <;> cases c <;> decide

private theorem defect_eq_mask (P : TraceFamily) (hTop : univ ∈ P) :
    (3 : ℤ) * P.card - 2 * (∑ T ∈ P, (T.card : ℤ)) =
      maskDefect (memberBit P ∅) (memberBit P {0}) (memberBit P {1}) (memberBit P {2})
        (memberBit P {0, 1}) (memberBit P {0, 2}) (memberBit P {1, 2}) := by
  calc
    _ = ∑ T ∈ P, (3 - 2 * (T.card : ℤ)) := by
      rw [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_comm (P.card : ℤ)]
    _ = ∑ T : Trace, if T ∈ P then (3 - 2 * (T.card : ℤ)) else 0 := by
      rw [← sum_filter]
      congr 1
      ext T
      simp
    _ = _ := by
      rw [trace_univ]
      have h0 : (∅ : Trace) ∉ ({ {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, univ } : TraceFamily) :=
        by decide
      have h1 : ({0} : Trace) ∉ ({ {1}, {2}, {0, 1}, {0, 2}, {1, 2}, univ } : TraceFamily) :=
        by decide
      have h2 : ({1} : Trace) ∉ ({ {2}, {0, 1}, {0, 2}, {1, 2}, univ } : TraceFamily) :=
        by decide
      have h3 : ({2} : Trace) ∉ ({ {0, 1}, {0, 2}, {1, 2}, univ } : TraceFamily) := by decide
      have h4 : ({0, 1} : Trace) ∉ ({ {0, 2}, {1, 2}, univ } : TraceFamily) := by decide
      have h5 : ({0, 2} : Trace) ∉ ({ {1, 2}, univ } : TraceFamily) := by decide
      have h6 : ({1, 2} : Trace) ∉ ({univ} : TraceFamily) := by decide
      have h01 : (0 : Fin 3) ≠ 1 := by decide
      have h02 : (0 : Fin 3) ≠ 2 := by decide
      have h12 : (1 : Fin 3) ≠ 2 := by decide
      simp only [sum_insert h0, sum_insert h1, sum_insert h2, sum_insert h3, sum_insert h4,
        sum_insert h5, sum_insert h6, sum_singleton, card_empty, card_singleton, card_pair h01,
        card_pair h02, card_pair h12, card_univ, Fintype.card_fin, hTop, if_true,
        maskDefect, bit, memberBit, decide_eq_true_eq]
      split_ifs <;> decide

private theorem member_singleton_union {P : TraceFamily}
    (hU : ∀ X ∈ P, ∀ Y ∈ P, X ∪ Y ∈ P) {a b : Fin 3}
    (ha : memberBit P {a} = true) (hb : memberBit P {b} = true) :
    memberBit P {a, b} = true := by
  simpa [memberBit, Finset.singleton_union] using
    hU {a} (of_decide_eq_true ha) {b} (of_decide_eq_true hb)

private theorem mem_pair_iff_of_bits {P : TraceFamily} {i j : Fin 3}
    (h : memberBit P {i, j} = (memberBit P {i} && memberBit P {j})) :
    ({i, j} : Trace) ∈ P ↔ ({i} : Trace) ∈ P ∧ ({j} : Trace) ∈ P := by
  have heq : (memberBit P {i, j} = true) ↔
      (memberBit P {i} && memberBit P {j}) = true := by rw [h]
  simpa only [Bool.and_eq_true, memberBit, decide_eq_true_eq] using heq

private theorem family_eq_insert_powerset (P : TraceFamily) (hTop : univ ∈ P)
    (hE : memberBit P ∅ = true)
    (hAB : memberBit P {0, 1} = (memberBit P {0} && memberBit P {1}))
    (hAC : memberBit P {0, 2} = (memberBit P {0} && memberBit P {2}))
    (hBC : memberBit P {1, 2} = (memberBit P {1} && memberBit P {2})) :
    P = insert univ ((univ : Trace).filter (fun i => ({i} : Trace) ∈ P)).powerset := by
  let S := (univ : Trace).filter (fun i => ({i} : Trace) ∈ P)
  have sc (i : Fin 3) : ({i} : Trace) ≠ univ := by
    intro he
    have h := congrArg Finset.card he
    simp at h
  have pc {i j : Fin 3} (hij : i ≠ j) : ({i, j} : Trace) ≠ univ := by
    intro he
    have h := congrArg Finset.card he
    simp [Finset.card_pair hij] at h
  have eTop : (∅ : Trace) ≠ univ := by decide
  ext T
  have hT : T ∈ (univ : TraceFamily) := mem_univ T
  rw [trace_univ] at hT
  simp only [mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [eTop, of_decide_eq_true hE]
  · simp [sc]
  · simp [sc]
  · simp [sc]
  · simp [pc (by decide : (0 : Fin 3) ≠ 1), Finset.insert_subset_iff, mem_pair_iff_of_bits hAB]
  · simp [pc (by decide : (0 : Fin 3) ≠ 2), Finset.insert_subset_iff, mem_pair_iff_of_bits hAC]
  · simp [pc (by decide : (1 : Fin 3) ≠ 2), Finset.insert_subset_iff, mem_pair_iff_of_bits hBC]
  · simp [hTop]

private theorem trace_profile (P : TraceFamily)
    (hU : ∀ X ∈ P, ∀ Y ∈ P, X ∪ Y ∈ P) (hTop : univ ∈ P) :
    let d := (3 : ℤ) * P.card - 2 * (∑ T ∈ P, (T.card : ℤ))
    d ≤ 1 ∧ (0 < d → ∃ T : Trace, T.Nonempty ∧ T ≠ univ ∧ P = insert univ T.powerset) := by
  dsimp only
  rw [defect_eq_mask P hTop]
  have h := mask_profile (memberBit P ∅) (memberBit P {0}) (memberBit P {1}) (memberBit P {2})
    (memberBit P {0, 1}) (memberBit P {0, 2}) (memberBit P {1, 2})
    (member_singleton_union hU) (member_singleton_union hU) (member_singleton_union hU)
  refine ⟨h.1, ?_⟩
  intro hpos
  obtain ⟨hE, hAny, hNotAll, hAB, hAC, hBC⟩ := h.2 hpos
  let S := (univ : Trace).filter (fun i => ({i} : Trace) ∈ P)
  have hMem (i : Fin 3) : i ∈ S ↔ ({i} : Trace) ∈ P := by simp [S]
  refine ⟨S, ?_, ?_, family_eq_insert_powerset P hTop hE hAB hAC hBC⟩
  · rcases hAny with h0 | h1 | h2
    · exact ⟨0, (hMem 0).mpr (of_decide_eq_true h0)⟩
    · exact ⟨1, (hMem 1).mpr (of_decide_eq_true h1)⟩
    · exact ⟨2, (hMem 2).mpr (of_decide_eq_true h2)⟩
  · intro hS
    apply hNotAll
    refine ⟨?_, ?_, ?_⟩
    · exact decide_eq_true ((hMem 0).mp (hS.symm ▸ mem_univ 0))
    · exact decide_eq_true ((hMem 1).mp (hS.symm ▸ mem_univ 1))
    · exact decide_eq_true ((hMem 2).mp (hS.symm ▸ mem_univ 2))

theorem trace_defect_le_one (P : Finset (Finset (Fin 3)))
    (hU : ∀ X ∈ P, ∀ Y ∈ P, X ∪ Y ∈ P) (hTop : univ ∈ P) :
    (3 : ℤ) * P.card - 2 * (∑ T ∈ P, (T.card : ℤ)) ≤ 1 :=
  (trace_profile P hU hTop).1

open scoped Classical in
theorem trace_defect_le_indicator (P : Finset (Finset (Fin 3)))
    (hU : ∀ X ∈ P, ∀ Y ∈ P, X ∪ Y ∈ P) (hTop : univ ∈ P) :
    (3 : ℤ) * P.card - 2 * (∑ T ∈ P, (T.card : ℤ)) ≤
      if (∃ T : Finset (Fin 3), T.Nonempty ∧ T ≠ univ ∧ P = insert univ T.powerset)
      then 1 else 0 := by
  split_ifs with h
  · exact trace_defect_le_one P hU hTop
  · exact le_of_not_gt fun hpos => h ((trace_profile P hU hTop).2 hpos)

end OMA.UnionClosedTrace

namespace OMA.UnionClosedTrace

open Finset
open scoped BigOperators

private def smallPattern (P : Finset (Finset (Fin 3))) : Prop :=
  ∃ T : Finset (Fin 3), T.Nonempty ∧ T ≠ univ ∧ P = insert univ T.powerset

open scoped Classical in
theorem bad_trace_fiber_lower
    (hlocal : ∀ P : Finset (Finset (Fin 3)),
      (∀ X ∈ P, ∀ Y ∈ P, X ∪ Y ∈ P) → univ ∈ P →
      (3 : ℤ) * P.card - 2 * (∑ T ∈ P, (T.card : ℤ)) ≤
        if smallPattern P then 1 else 0)
    (m : ℕ) (A : Finset (Finset (Fin m))) (e : Fin 3 ↪ Fin m)
    (hu : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A)
    (hS : (univ : Finset (Fin 3)).map e ∈ A)
    (hlow : ∀ i, 2 * (A.filter (fun X => e i ∈ X)).card < A.card) :
    let S := (univ : Finset (Fin 3)).map e
    let tr := fun X : Finset (Fin m) => (univ : Finset (Fin 3)).filter (fun i => e i ∈ X)
    let patterns := fun B : Finset (Fin m) => (A.filter (fun X => X \ S = B)).image tr
    let bad := A.filter fun B => Disjoint B S ∧ ∃ T ∈ (univ : Finset (Finset (Fin 3))),
      T.Nonempty ∧ T ≠ univ ∧ patterns B = insert univ T.powerset
    (if A.card % 2 = 0 then 6 else 3) ≤ bad.card := by
  classical
  let S := (univ : Finset (Fin 3)).map e
  let tr (X : Finset (Fin m)) := (univ : Finset (Fin 3)).filter (fun i => e i ∈ X)
  let out (X : Finset (Fin m)) := X \ S
  let keys := A.image out
  let fiber (B : Finset (Fin m)) := A.filter (fun X => out X = B)
  let patterns (B : Finset (Fin m)) := (fiber B).image tr
  let bad := A.filter fun B => Disjoint B S ∧ ∃ T ∈ (univ : Finset (Finset (Fin 3))),
    T.Nonempty ∧ T ≠ univ ∧ patterns B = insert univ T.powerset
  change (if A.card % 2 = 0 then 6 else 3) ≤ bad.card
  have hInj (B : Finset (Fin m)) : Set.InjOn tr (fiber B : Set (Finset (Fin m))) := by
    intro X hX Y hY hEq
    have hx := (mem_filter.mp (show X ∈ fiber B from hX)).2
    have hy := (mem_filter.mp (show Y ∈ fiber B from hY)).2
    ext a
    by_cases ha : a ∈ S
    · obtain ⟨i, _, rfl⟩ := mem_map.mp ha
      have h : i ∈ tr X ↔ i ∈ tr Y := by rw [hEq]
      simpa [tr] using h
    · have h : a ∈ out X ↔ a ∈ out Y := by rw [hx, hy]
      simpa [out, ha] using h
  have hOutUnion (X Y : Finset (Fin m)) : out (X ∪ Y) = out X ∪ out Y := by
    ext a
    simp [out, or_and_right]
  have hTrUnion (X Y : Finset (Fin m)) : tr (X ∪ Y) = tr X ∪ tr Y := by
    ext i
    simp [tr]
  have hClosed (B : Finset (Fin m)) : ∀ X ∈ patterns B, ∀ Y ∈ patterns B,
      X ∪ Y ∈ patterns B := by
    intro X hX Y hY
    obtain ⟨U, hU, rfl⟩ := mem_image.mp hX
    obtain ⟨V, hV, rfl⟩ := mem_image.mp hY
    obtain ⟨hUA, hUB⟩ := mem_filter.mp hU
    obtain ⟨hVA, hVB⟩ := mem_filter.mp hV
    refine mem_image.mpr ⟨U ∪ V, mem_filter.mpr ⟨hu U hUA V hVA, ?_⟩, hTrUnion U V⟩
    rw [hOutUnion, hUB, hVB, union_idempotent]
  have hTop (B : Finset (Fin m)) (hB : B ∈ keys) : univ ∈ patterns B := by
    obtain ⟨X, hX, hx⟩ := mem_image.mp hB
    refine mem_image.mpr ⟨X ∪ S, mem_filter.mpr ⟨hu X hX S hS, ?_⟩, ?_⟩
    · rw [hOutUnion, hx]
      simp [out]
    · ext i
      have hi : e i ∈ S := mem_map.mpr ⟨i, mem_univ i, rfl⟩
      simp [tr, hi]
  have hBadSubset : keys.filter (fun B => smallPattern (patterns B)) ⊆ bad := by
    intro B hb
    obtain ⟨_, T, hT, hTtop, hPattern⟩ := mem_filter.mp hb
    have hEmpty : ∅ ∈ patterns B := by
      rw [hPattern]
      exact mem_insert_of_mem (mem_powerset.mpr (empty_subset T))
    obtain ⟨X, hX, hTrace⟩ := mem_image.mp hEmpty
    obtain ⟨hXA, hXB⟩ := mem_filter.mp hX
    have hDisj : Disjoint X S := Finset.disjoint_left.mpr fun a ha hSa => by
      obtain ⟨i, _, rfl⟩ := mem_map.mp hSa
      have hi : i ∈ tr X := mem_filter.mpr ⟨mem_univ _, ha⟩
      rw [hTrace] at hi
      simp at hi
    have hEq : X = B := ((sdiff_eq_left.mpr hDisj).symm).trans hXB
    exact mem_filter.mpr ⟨hEq ▸ hXA, hEq ▸ hDisj, T, mem_univ T, hT, hTtop, hPattern⟩
  have hCardSum : (∑ B ∈ keys, ((patterns B).card : ℤ)) = (A.card : ℤ) := by
    calc
      _ = ∑ B ∈ keys, ∑ _X ∈ fiber B, (1 : ℤ) := by
        apply sum_congr rfl
        intro B _
        rw [card_image_of_injOn (hInj B)]
        simp
      _ = ∑ _X ∈ A, (1 : ℤ) :=
        sum_fiberwise_of_maps_to (s := A) (t := keys) (g := out)
          (fun X hX => mem_image_of_mem out hX) _
      _ = _ := by simp
  have hTraceSum :
      (∑ B ∈ keys, ∑ T ∈ patterns B, (T.card : ℤ)) =
        ∑ i : Fin 3, ((A.filter (fun X => e i ∈ X)).card : ℤ) := by
    calc
      _ = ∑ B ∈ keys, ∑ X ∈ fiber B, ((tr X).card : ℤ) := by
        apply sum_congr rfl
        intro B _
        exact sum_image (hInj B)
      _ = ∑ X ∈ A, ((tr X).card : ℤ) :=
        sum_fiberwise_of_maps_to (s := A) (t := keys) (g := out)
          (fun X hX => mem_image_of_mem out hX) _
      _ = _ := by
        simp only [tr, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        exact sum_comm
  have hIndicator : (∑ B ∈ keys, if smallPattern (patterns B) then (1 : ℤ) else 0) =
      ((keys.filter (fun B => smallPattern (patterns B))).card : ℤ) := by
    simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hL (i : Fin 3) : (if A.card % 2 = 0 then (2 : ℤ) else 1) ≤
      (A.card : ℤ) - 2 * ((A.filter (fun X => e i ∈ X)).card : ℤ) := by
    have hi := hlow i
    split <;> omega
  have hGlobal : (if A.card % 2 = 0 then (6 : ℤ) else 3) ≤
      3 * (A.card : ℤ) - 2 * (∑ i : Fin 3, ((A.filter (fun X => e i ∈ X)).card : ℤ)) := by
    calc
      _ = ∑ _i : Fin 3, (if A.card % 2 = 0 then (2 : ℤ) else 1) := by
        split <;> simp [*]
      _ ≤ ∑ i : Fin 3, ((A.card : ℤ) - 2 * ((A.filter (fun X => e i ∈ X)).card : ℤ)) :=
        sum_le_sum (fun i _ => hL i)
      _ = _ := by simp [sum_sub_distrib, ← mul_sum]
  have hResult : (if A.card % 2 = 0 then (6 : ℤ) else 3) ≤ (bad.card : ℤ) := by
    calc
      _ ≤ 3 * (A.card : ℤ) - 2 * (∑ i : Fin 3, ((A.filter (fun X => e i ∈ X)).card : ℤ)) :=
        hGlobal
      _ = ∑ B ∈ keys, (3 * ((patterns B).card : ℤ) - 2 * (∑ T ∈ patterns B, (T.card : ℤ))) := by
        rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hCardSum, hTraceSum]
      _ ≤ ∑ B ∈ keys, if smallPattern (patterns B) then (1 : ℤ) else 0 :=
        sum_le_sum (fun B hB => hlocal (patterns B) (hClosed B) (hTop B hB))
      _ = _ := hIndicator
      _ ≤ _ := by exact_mod_cast card_le_card hBadSubset
  by_cases h : A.card % 2 = 0 <;> simp only [h, if_true, if_false] at hResult ⊢ <;> omega

end OMA.UnionClosedTrace

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1_H3_R1.H1 := by
  apply OMA.UnionClosedTrace.bad_trace_fiber_lower
  intro P hU hTop
  split
  · exact OMA.UnionClosedTrace.trace_defect_le_one P hU hTop
  · rename_i hnot
    have h := OMA.UnionClosedTrace.trace_defect_le_indicator P hU hTop
    split at h
    · rename_i hyes
      exact (hnot hyes).elim
    · exact h
