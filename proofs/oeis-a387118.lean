import OMAStatements.S_oeis_a387118
import Mathlib

open OMA.S_oeis_a387118

/- Formalization of Clément Garrot’s distinct-representative argument in OEIS A387112. -/

private lemma partition_choosable_reverse (y : List ℕ) : Choosable y ↔ Choosable y.reverse := by
  have forward (l : List ℕ) : Choosable l → Choosable l.reverse := by
    rintro ⟨z, hz, h⟩
    let revIndex (i : Fin l.reverse.length) : Fin l.length := (i.cast l.length_reverse).rev
    refine ⟨z ∘ revIndex, hz.comp (Fin.rev_injective.comp (Fin.cast_injective _)), ?_⟩
    intro i
    obtain ⟨h1, h2⟩ := h (revIndex i)
    refine ⟨h1, h2.trans_eq ?_⟩
    simp only [List.get_eq_getElem, List.getElem_reverse]
    congr 1
    simp [revIndex, Fin.rev]
    omega
  exact ⟨forward y, fun h => by simpa using forward y.reverse h⟩

private lemma partition_reverse_sorted (n : ℕ) (p : Nat.Partition n) :
    (parts n p).reverse.SortedLE := by
  apply List.sortedLE_iff_pairwise.mpr
  apply List.pairwise_reverse.mpr
  exact Multiset.pairwise_sort _ (· ≥ ·)

private lemma oma_choosable_iff_superdiagonal (y : List ℕ) (hy : y.SortedLE) :
    Choosable y ↔ Superdiagonal y := by
  constructor
  · rintro ⟨z, hinj, hz⟩ i
    let withinPrefix (j : Fin (i.val+1)) : Fin y.length := ⟨j.val, by omega⟩
    let f (j : Fin (i.val+1)) : Fin (y.get i) :=
      ⟨z (withinPrefix j) - 1, by
        have hj : withinPrefix j ≤ i := by change j.val ≤ i.val; omega
        have lower := (hz (withinPrefix j)).1
        have upper := (hz (withinPrefix j)).2.trans (hy.monotone_get hj)
        omega⟩
    have hf : Function.Injective f := by
      intro a b heq
      have hval := congrArg Fin.val heq
      change z (withinPrefix a) - 1 = z (withinPrefix b) - 1 at hval
      have ha := (hz (withinPrefix a)).1
      have hb := (hz (withinPrefix b)).1
      have hzab : z (withinPrefix a) = z (withinPrefix b) := by omega
      exact Fin.ext (congrArg (fun u : Fin y.length => u.val) (hinj hzab))
    simpa using Fintype.card_le_of_injective f hf
  · intro h
    refine ⟨fun i => i.val + 1, ?_, fun i => ⟨Nat.succ_pos i.val, h i⟩⟩
    intro a b hab
    exact Fin.ext (Nat.add_right_cancel hab)

theorem OMA.solution : type_of% @OMA.S_oeis_a387118.main := by
  intro n
  unfold a
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro p
  exact not_congr ((partition_choosable_reverse _).trans
    (oma_choosable_iff_superdiagonal _ (partition_reverse_sorted n p)))
