import OMAStatements.S_oeis_a081732
import Mathlib

namespace OMA.TernaryEdits81732

open OMA.S_oeis_a081732 Finset

private theorem pref_apply (d : Digit) (s : Word) : pref d s = d::s := rfl

private theorem first_apply (d : Digit) (s : Word) : firstDigit s d = d::s := rfl

private theorem canon_cons (d : Digit) (s : Word) (h : 2 ≤ s.length) :
    canonical (d::s) ↔ canonical s := by
  cases s with
  | nil => simp at h
  | cons x s =>
    cases s <;> simp_all [canonical]

private theorem edit_lengths (s : Word) :
    (∀ w ∈ deletions s, w.length+1 = s.length) ∧
    (∀ w ∈ insertions s, w.length = s.length+1) ∧
    (∀ w ∈ substitutions s, w.length = s.length) := by
  induction s with
  | nil => simp [deletions,insertions,substitutions,first_apply]
  | cons d s ih =>
    obtain ⟨hd,hi,hr⟩ := ih
    simp only [deletions,insertions,substitutions,mem_insert,mem_union,mem_map,mem_univ,
      true_and, List.length_cons, pref_apply,first_apply]
    refine ⟨?_,?_,?_⟩
    · rintro w (rfl|⟨t,ht,rfl⟩)
      · rfl
      · simp [hd t ht]
    · rintro w (⟨x,rfl⟩|⟨t,ht,rfl⟩)
      · rfl
      · simp [hi t ht]
    · rintro w (⟨x,_,rfl⟩|⟨t,ht,rfl⟩)
      · rfl
      · simp [hr t ht]

private def total (A : Finset Word) := (A.filter canonical).card

private theorem total_pref (A : Finset Word) (e : Digit) (h : ∀ w ∈ A, 2 ≤ w.length) :
    total (A.map (pref e)) = total A := by
  unfold total
  rw [filter_map,card_map]
  congr 1
  apply filter_congr
  intro w hw
  exact canon_cons e w (h w hw)

private theorem own_insert (e : Digit) (s : Word) : e::s ∈ insertions s := by
  cases s with
  | nil => exact mem_map.mpr ⟨e,mem_univ _,rfl⟩
  | cons d s => exact mem_union_left _ (mem_map.mpr ⟨e,mem_univ _,rfl⟩)

private theorem ins_split (e : Digit) (s : Word) :
    insertions (e::s) = ((univ.erase e).map (firstDigit (e::s))) ∪
      ((insertions s).map (pref e)) := by
  rw [insertions]
  ext w
  simp only [mem_union,mem_map,mem_univ,true_and,mem_erase]
  constructor
  · rintro (⟨d,rfl⟩|h)
    · by_cases h : d=e
      · subst d
        exact Or.inr ⟨e::s,own_insert e s,rfl⟩
      · exact Or.inl ⟨d,⟨h,trivial⟩,rfl⟩
    · exact Or.inr h
  · rintro (⟨d,_,rfl⟩|h)
    · exact Or.inl ⟨d,rfl⟩
    · exact Or.inr h

private theorem new_front (e : Digit) (s : Word) (A : Finset Word)
    (len : 2 ≤ s.length) (ok : canonical s) (ha : ∀ w ∈ A, 2 ≤ w.length) :
    total (((univ.erase e).map (firstDigit s)) ∪ A.map (pref e)) = 2+total A := by
  let B := (univ.erase e).map (firstDigit s)
  have allB : B.filter canonical = B := by
    apply filter_eq_self.mpr
    intro w hw
    obtain ⟨d,_,rfl⟩ := mem_map.mp hw
    exact (canon_cons d s len).2 ok
  have dis : Disjoint B (A.map (pref e)) := by
    rw [disjoint_left]
    intro w hw hp
    obtain ⟨d,hd,rfl⟩ := mem_map.mp hw
    obtain ⟨u,_,eq⟩ := mem_map.mp hp
    exact (mem_erase.mp hd).1 (List.cons.inj eq).1.symm
  change ((B ∪ A.map (pref e)).filter canonical).card = _
  rw [filter_union,allB,card_union_of_disjoint (dis.mono_right (filter_subset ..))]
  change B.card + total (A.map (pref e)) = _
  rw [total_pref A e ha]
  congr 1
  simp [B]

private theorem count_step (s : Word) (d e : Digit) (len : 2 ≤ s.length) (ok : canonical s) :
    count (e::d::s) = count (d::s) + if d=e then 4 else 5 := by
  let t := d::s
  have ht : 3 ≤ t.length := by simp [t]; omega
  have ct : canonical t := (canon_cons d s len).2 ok
  have ct' := (canon_cons e t (by omega)).2 ct
  obtain ⟨dl,il,sl⟩ := edit_lengths t
  have ins : total (insertions (e::t)) = 2+total (insertions t) := by
    rw [ins_split]
    apply new_front _ _ _ (by simp; omega) ct'
    intro w hw
    rw [il w hw]; omega
  have sub : total (substitutions (e::t)) = 2+total (substitutions t) := by
    rw [substitutions]
    apply new_front _ _ _ (by omega) ct
    intro w hw
    rw [sl w hw]; omega
  let M := (deletions t).map (pref e)
  have cardM : total M = total (deletions t) := by
    apply total_pref
    intro w hw
    have := dl w hw
    omega
  have mem : t ∈ M ↔ d=e := by
    constructor
    · intro h
      obtain ⟨w,_,hw⟩ := mem_map.mp h
      exact (List.cons.inj hw).1.symm
    · rintro rfl
      exact mem_map.mpr ⟨s,mem_insert_self ..,rfl⟩
  have del : total (deletions (e::t)) = total (deletions t) + if d=e then 0 else 1 := by
    change ((insert t M).filter canonical).card = _
    rw [filter_insert]
    simp only [ct,if_true]
    by_cases h : d=e
    · rw [if_pos h,insert_eq_of_mem (mem_filter.mpr ⟨mem.mpr h,ct⟩),add_zero]
      exact cardM
    · rw [if_neg h,card_insert_of_notMem (by simpa [ct,mem] using h)]
      rw [← cardM]; rfl
  change total (deletions (e::t)) + total (insertions (e::t)) + total (substitutions (e::t)) =
    total (deletions t) + total (insertions t) + total (substitutions t) + _
  rw [ins,sub,del]
  split_ifs <;> omega

private theorem numeral_step (n : ℕ) (hn : 0 < n) (d : Digit) :
    numeral (3*n+d) = d :: numeral n := by
  have hd := d.isLt
  have hp : 0 < 3*n+(d:ℕ) := by omega
  simp only [numeral, if_neg hp.ne',if_neg hn.ne']
  rw [Nat.digits_def' (by decide : 1 < 3) hp]
  rw [show (3*n+(d:ℕ))/3=n by omega, show (3*n+(d:ℕ))%3=d by omega]
  simp [trit,Nat.mod_eq_of_lt hd]

private theorem numeral_good (n : ℕ) (hn : 3 ≤ n) :
    2 ≤ (numeral n).length ∧ canonical (numeral n) := by
  have nz : n ≠ 0 := by omega
  simp only [numeral,if_neg nz]
  let xs := Nat.digits 3 n
  have ne : xs ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr nz
  have len : 1 < xs.length := (Nat.lt_digits_length_iff (by decide : 1 < 3) n).mpr (by simpa)
  have lt3 : xs.getLast ne < 3 := Nat.digits_lt_base (by decide) (List.getLast_mem ne)
  have pos := Nat.getLast_digit_ne_zero 3 nz
  have last : trit (xs.getLast ne) ≠ 0 := by
    intro e
    have v := congrArg Fin.val e
    simp only [trit,Nat.mod_eq_of_lt lt3,Fin.val_zero] at v
    exact pos v
  refine ⟨?_, ?_⟩
  · simp only [List.length_map]
    change 2 ≤ xs.length
    omega
  change canonical (xs.map trit)
  refine ⟨by simpa using ne, Or.inr ?_⟩
  simpa [List.getLast?_map, List.getLast?_eq_some_getLast ne] using last

theorem result (m : ℕ) (hm : 3 ≤ m) (d e : Digit) :
    a (9*m + 3*(d:ℕ) + (e:ℕ)) =
      a (3*m+(d:ℕ)) + if d=e then 4 else 5 := by
  have h := numeral_good m hm
  unfold a
  rw [show 9*m+3*(d:ℕ)+(e:ℕ) = 3*(3*m+(d:ℕ))+(e:ℕ) by omega,
    numeral_step _ (by omega) e,numeral_step m (by omega) d]
  exact count_step _ _ _ h.1 h.2

end OMA.TernaryEdits81732

theorem OMA.solution : type_of% @OMA.S_oeis_a081732.main := OMA.TernaryEdits81732.result
