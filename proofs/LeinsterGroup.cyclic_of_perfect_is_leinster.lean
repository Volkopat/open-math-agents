import FormalConjectures.Wikipedia.LeinsterGroup

/-! Construct divisor-order subgroups by powers of a cyclic generator. -/

-- Original Lean proof credit: @ldy985.

open scoped IsMulCommutative

namespace OMA.P6

theorem subset_pow_eq_one {G : Type*} [Group G] (H : Subgroup G) [Finite H] :
    ((H : Set G)) ⊆ {a : G | a ^ Nat.card H = 1} := by
  intro x hx
  show x ^ Nat.card H = 1
  have h1 : (⟨x, hx⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
  exact congrArg Subtype.val h1

theorem card_pow_set_le {G : Type*} [Group G] [Fintype G] [IsCyclic G] {n : ℕ} (hn : 0 < n) :
    Set.ncard {a : G | a ^ n = 1} ≤ n := by
  classical
  simpa [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
    using IsCyclic.card_pow_eq_one_le (α := G) hn

theorem eq_of_card_eq {G : Type*} [Group G] [Fintype G] [IsCyclic G] (H K : Subgroup G)
    (h : Nat.card H = Nat.card K) : H = K := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hS : ∀ L : Subgroup G, Nat.card L = Nat.card H →
      (L : Set G) = {a : G | a ^ Nat.card H = 1} := by
    intro L hL
    have hsub : (L : Set G) ⊆ {a : G | a ^ Nat.card H = 1} := by
      rw [← hL]
      exact subset_pow_eq_one L
    apply Set.eq_of_subset_of_ncard_le hsub
    have e : (L : Set G).ncard = Nat.card L := (Nat.card_coe_set_eq (L : Set G)).symm
    rw [e, hL]
    exact card_pow_set_le hpos
  apply SetLike.coe_injective
  rw [hS H rfl, hS K h.symm]

end OMA.P6

theorem OMA.solution : type_of% @LeinsterGroup.cyclic_of_perfect_is_leinster := by
  intro G _ _ _ hp
  classical
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  unfold LeinsterGroup.IsLeinster
  rw [← (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hp]
  refine Finset.sum_bij (fun H _ => Nat.card H.1) ?_ ?_ ?_ ?_
  · intro H _
    refine Nat.mem_divisors.2 ⟨?_, hpos.ne'⟩
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card H.1
  · intro H₁ _ H₂ _ h
    exact Subtype.ext (OMA.P6.eq_of_card_eq H₁.1 H₂.1 h)
  · intro d hd
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    have hdvd : d ∣ orderOf g := by
      rw [hg, Nat.card_eq_fintype_card]
      exact Nat.dvd_of_mem_divisors hd
    refine ⟨⟨Subgroup.zpowers (g ^ (orderOf g / d)), inferInstance⟩, Finset.mem_univ _, ?_⟩
    rw [Nat.card_zpowers, orderOf_pow_orderOf_div (by rw [hg]; exact Nat.card_pos.ne') hdvd]
  · intro H _
    rfl
