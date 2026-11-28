import FormalConjectures.Wikipedia.LeinsterGroup

/-! In a finite cyclic group the subgroup of order `d` is the kernel of `x ↦ x ^ d`, so
`H ↦ |H|` and `d ↦ ker (x ↦ x ^ d)` are inverse bijections between subgroups and divisors. -/

open scoped IsMulCommutative in
theorem OMA.solution : type_of% @LeinsterGroup.cyclic_of_perfect_is_leinster := by
  intro G _ _ _ hp
  rw [LeinsterGroup.IsLeinster, ← (Nat.perfect_iff_sum_divisors_eq_two_mul Fintype.card_pos).1 hp]
  have c (d : ℕ) := IsCyclic.card_powMonoidHom_ker G d
  refine Finset.sum_nbij' (fun H => Nat.card H.1) (fun d => ⟨(powMonoidHom d).ker, inferInstance⟩)
    (fun H _ => Nat.mem_divisors.2 ⟨by simpa using H.1.card_subgroup_dvd_card,
      Fintype.card_ne_zero⟩) (by simp) (fun H _ => Subtype.ext ?_) (fun d hd => ?_) (fun _ _ => rfl)
  · exact (Subgroup.eq_of_le_of_card_ge (fun x hx => orderOf_dvd_iff_pow_eq_one.1
      (H.1.orderOf_dvd_natCard hx)) ((c _).trans_le (Nat.gcd_le_right _ Nat.card_pos))).symm
  · exact (c d).trans (Nat.gcd_eq_right (by simpa using Nat.dvd_of_mem_divisors hd))
