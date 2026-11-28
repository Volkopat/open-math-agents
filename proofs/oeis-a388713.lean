import OMAStatements.S_oeis_a388713

namespace OMA.Choosable

lemma core (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) :
    (∃ z : Fin l.length → ℕ, Function.Injective z ∧ ∀ i, 1 ≤ z i ∧ z i ≤ l.get i) ↔
    (∀ i : Fin l.reverse.length, i.val + 1 ≤ l.reverse.get i) := by
  have hmono : ∀ a b : ℕ, (ha : a < l.length) → (hb : b < l.length) → a ≤ b → l[b] ≤ l[a] := by
    intro a b ha hb hab
    rcases hab.lt_or_eq with h | h
    · exact (List.pairwise_iff_getElem.1 hl) a b ha hb h
    · subst h; exact le_refl _
  constructor
  · rintro ⟨z, hz, hb⟩ ⟨i, hi⟩
    simp only [List.length_reverse] at hi
    simp only [List.get_eq_getElem, List.getElem_reverse]
    let g : Fin (i + 1) → ℕ := fun t => z ⟨l.length - 1 - i + t.val, by omega⟩
    have hcard := Finset.card_le_card_of_injOn g (s := Finset.univ)
      (t := Finset.Icc 1 (l[l.length - 1 - i]'(by omega)))
      (by
        intro t _
        have h1 := hb ⟨l.length - 1 - i + t.val, by omega⟩
        simp only [List.get_eq_getElem] at h1
        rw [Finset.mem_coe, Finset.mem_Icc]
        exact ⟨h1.1, h1.2.trans (hmono _ _ _ _ (by omega))⟩)
      (by
        intro s _ t _ hst
        have := hz hst
        simp only [Fin.mk.injEq] at this
        exact Fin.ext (by omega))
    simpa using hcard
  · intro h
    refine ⟨fun j => l.length - j.val, ?_, ?_⟩
    · intro a b hab
      have ha := a.2; have hb := b.2
      simp only at hab
      exact Fin.ext (by omega)
    · intro j
      have hj := j.2
      refine ⟨show 1 ≤ l.length - j.val by omega, show l.length - j.val ≤ l.get j from ?_⟩
      have := h ⟨l.length - 1 - j.val, by simp; omega⟩
      simp only [List.get_eq_getElem, List.getElem_reverse] at this ⊢
      have e : l.length - 1 - (l.length - 1 - j.val) = j.val := by omega
      simp only [e] at this
      omega

end OMA.Choosable

theorem OMA.solution : type_of% @OMA.S_oeis_a388713.main := by
  intro n k
  unfold OMA.S_oeis_a388713.T
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro p
  have hc := OMA.Choosable.core (OMA.S_oeis_a388713.parts n p) (Multiset.pairwise_sort p.parts (· ≥ ·))
  rw [OMA.S_oeis_a388713.Choosable, hc]
  rfl
