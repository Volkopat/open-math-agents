import OMAStatements.S_oeis_a091916

namespace OMA.S_oeis_a091916

private theorem odd_product (s : Multiset ℕ) : Odd s.prod ↔ ∀ x ∈ s, Odd x := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih => simp [Nat.odd_mul, ih]

private theorem product_le_max {n : ℕ} (s : Multiset ℕ) (hs : s.sum = n)
    (ho : ∀ x ∈ s, Odd x) : s.prod ≤ a n := by
  let p : Nat.Partition n := ⟨s, fun {x} hx => (ho x hx).pos, hs⟩
  unfold a
  exact Finset.le_sup (f := fun q : Nat.Partition n => q.parts.prod)
    (b := p) (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact (odd_product s).2 ho)

private theorem max_attained (n : ℕ) :
    ∃ p : Nat.Partition n, Odd p.parts.prod ∧ p.parts.prod = a n := by
  let s := Multiset.replicate n (1 : ℕ)
  let p : Nat.Partition n := ⟨s, fun {x} h => by have := Multiset.eq_of_mem_replicate h; omega,
    by simp [s]⟩
  let F := (Finset.univ : Finset (Nat.Partition n)).filter (fun q => Odd q.parts.prod)
  have hp : p ∈ F := by
    simp [F, p, s, Multiset.prod_replicate]
  obtain ⟨q, hq, he⟩ := Finset.exists_mem_eq_sup F ⟨p, hp⟩ (fun q => q.parts.prod)
  exact ⟨q, (Finset.mem_filter.mp hq).2, he.symm⟩

private theorem max_contains_three {n : ℕ} (hn : 9 ≤ n)
    (p : Nat.Partition n) (ho : Odd p.parts.prod) (hmax : p.parts.prod = a n) :
    3 ∈ p.parts := by
  have oddPart := (odd_product p.parts).1 ho
  have cannotImprove (removed inserted : Multiset ℕ) (hremoved : removed ≤ p.parts)
      (hsum : removed.sum = inserted.sum) (hi : ∀ x ∈ inserted, Odd x)
      (hprod : removed.prod < inserted.prod) : False := by
    let rest := p.parts - removed
    have hrest : rest + removed = p.parts := Multiset.sub_add_cancel hremoved
    have oddRest (x : ℕ) (hx : x ∈ rest) : Odd x :=
      oddPart x (hrest ▸ Multiset.mem_add.mpr (Or.inl hx))
    have hnewSum : (rest + inserted).sum = n := by
      rw [Multiset.sum_add, ← hsum, ← Multiset.sum_add, hrest, p.parts_sum]
    have hnewOdd (x : ℕ) (hx : x ∈ rest + inserted) : Odd x := by
      rcases Multiset.mem_add.mp hx with hx | hx
      · exact oddRest x hx
      · exact hi x hx
    have bound := product_le_max (rest + inserted) hnewSum hnewOdd
    have hpos : 0 < rest.prod :=
      Multiset.prod_pos (fun x hx => (oddRest x hx).pos)
    have increase : (rest + removed).prod < (rest + inserted).prod := by
      simp only [Multiset.prod_add]
      exact Nat.mul_lt_mul_of_pos_left hprod hpos
    rw [hrest, hmax] at increase
    exact (not_lt_of_ge bound) increase
  by_contra hthree
  have smallPart (x : ℕ) (hx : x ∈ p.parts) : x = 1 ∨ x = 5 := by
    have hxmod := Nat.odd_iff.mp (oddPart x hx)
    have hx3 : x ≠ 3 := fun h => hthree (h ▸ hx)
    by_cases hlarge : 7 ≤ x
    · exfalso
      apply cannotImprove {x} (3 ::ₘ 3 ::ₘ {x - 6}) (Multiset.singleton_le.mpr hx)
      · simp
        omega
      · have hxrest : Odd (x - 6) := Nat.odd_iff.mpr (by omega)
        have hodd3 : Odd (3 : ℕ) := by decide
        simp [hodd3, hxrest]
      · simp
        omega
    · omega
  by_cases hf : 5 ∈ p.parts
  · have hrest : 5 ::ₘ p.parts.erase 5 = p.parts := Multiset.cons_erase hf
    have hne : p.parts.erase 5 ≠ 0 := by
      intro hzero
      have hsum := congrArg Multiset.sum hrest
      simp [hzero, p.parts_sum] at hsum
      omega
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    have hxs : x ∈ p.parts := hrest ▸ Multiset.mem_cons_of_mem hx
    have hcut : 5 ::ₘ ({x} : Multiset ℕ) ≤ p.parts :=
      hrest ▸ Multiset.cons_le_cons 5 (Multiset.singleton_le.mpr hx)
    rcases smallPart x hxs with h | h
    · subst x
      exact cannotImprove (5 ::ₘ {1}) (3 ::ₘ {3}) hcut (by decide) (by decide) (by decide)
    · subst x
      exact cannotImprove (5 ::ₘ {5}) (3 ::ₘ 3 ::ₘ 3 ::ₘ {1}) hcut (by decide)
        (by decide) (by decide)
  · have hrep : p.parts = Multiset.replicate p.parts.card 1 :=
      Multiset.eq_replicate_card.mpr fun x hx => (smallPart x hx).resolve_right
        (fun h => hf (h ▸ hx))
    have hcard : p.parts.card = n := by
      have hsum := congrArg Multiset.sum hrep
      simpa [p.parts_sum] using hsum.symm
    have hcut : Multiset.replicate 3 (1 : ℕ) ≤ p.parts := by
      conv_rhs => rw [hrep]
      exact Multiset.replicate_le_replicate _ |>.mpr (by omega)
    exact cannotImprove (Multiset.replicate 3 1) {3} hcut (by decide) (by decide) (by decide)

end OMA.S_oeis_a091916

open OMA.S_oeis_a091916 in
theorem OMA.solution : type_of% @OMA.S_oeis_a091916.main := by
  intro n hn
  obtain ⟨p, ho, hp⟩ := max_attained n
  obtain ⟨q, hqOdd, hq⟩ := max_attained (n + 3)
  apply le_antisymm
  · have hthree := max_contains_three (by omega) q hqOdd hq
    have hsplit : 3 ::ₘ q.parts.erase 3 = q.parts := Multiset.cons_erase hthree
    have hs := congrArg Multiset.sum hsplit
    simp only [Multiset.sum_cons, q.parts_sum] at hs
    have hsmall := product_le_max (q.parts.erase 3) (show (q.parts.erase 3).sum = n by omega)
      (fun x hx => (odd_product q.parts).1 hqOdd x (hsplit ▸ Multiset.mem_cons_of_mem hx))
    rw [← hq, ← hsplit, Multiset.prod_cons]
    exact Nat.mul_le_mul_left 3 hsmall
  · have hlarge := product_le_max (3 ::ₘ p.parts) (n := n + 3)
      (by simp [p.parts_sum, Nat.add_comm])
      (fun x hx => by
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · decide
        · exact (odd_product p.parts).1 ho x hx)
    simpa only [Multiset.prod_cons, hp] using hlarge
