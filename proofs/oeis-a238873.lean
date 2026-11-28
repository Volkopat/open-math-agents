import OMAStatements.S_oeis_a238873

open OMA.S_oeis_a238873

private theorem choice_reverse (y : List ℕ) : Choosable y ↔ Choosable y.reverse := by
  let e : Fin y.reverse.length ≃ Fin y.length :=
    (finCongr (List.length_reverse)).trans Fin.revPerm
  have hget (i : Fin y.reverse.length) : y.reverse.get i = y.get (e i) := by
    simp [e, Fin.rev, List.getElem_reverse, Nat.sub_sub, Nat.add_comm]
  constructor
  · rintro ⟨z, hz, hz'⟩
    exact ⟨z ∘ e, hz.comp e.injective, fun i => by simpa only [Function.comp_apply, hget] using hz' (e i)⟩
  · rintro ⟨z, hz, hz'⟩
    refine ⟨z ∘ e.symm, hz.comp e.symm.injective, ?_⟩
    intro i
    simpa only [Function.comp_apply, hget, Equiv.apply_symm_apply] using hz' (e.symm i)

private theorem choice_sorted (y : List ℕ) (hy : y.Pairwise (· ≤ ·)) :
    Choosable y ↔ Superdiagonal y := by
  constructor
  · rintro ⟨z, hz, hbound⟩ i
    let g (j : Fin (i.val+1)) : Fin y.length := ⟨j.val, j.isLt.trans_le (Nat.succ_le_of_lt i.isLt)⟩
    have hg (j : Fin (i.val+1)) : y.get (g j) ≤ y.get i :=
      hy.rel_get_of_le (Nat.le_of_lt_succ j.isLt)
    let f (j : Fin (i.val+1)) : Fin (y.get i) :=
      ⟨z (g j)-1, by
        have h := (hbound (g j)).2.trans (hg j)
        have hpos := (hbound (g j)).1
        omega⟩
    have hfi : Function.Injective f := by
      intro j k h
      have hv := congrArg Fin.val h
      change z (g j)-1 = z (g k)-1 at hv
      have hj := (hbound (g j)).1
      have hk := (hbound (g k)).1
      have e := hz (show z (g j) = z (g k) by omega)
      exact Fin.ext (show j.val = k.val from congrArg (fun i : Fin y.length => i.val) e)
    simpa using Fintype.card_le_of_injective f hfi
  · intro h
    refine ⟨fun i => i.val + 1, ?_, fun i => ⟨Nat.succ_le_succ (Nat.zero_le _), h i⟩⟩
    intro i j hij
    exact Fin.ext (Nat.add_right_cancel hij)

private theorem choice_parts (n : ℕ) (p : Nat.Partition n) :
    Choosable (parts n p) ↔ Superdiagonal (parts n p).reverse := by
  have h : (parts n p).Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
  exact (choice_reverse _).trans (choice_sorted _ h.reverse)

theorem OMA.solution : type_of% @OMA.S_oeis_a238873.main := by
  intro n
  unfold a
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun p => (choice_parts n p).symm))