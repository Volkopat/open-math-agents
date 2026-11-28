import OMAStatements.S_mo_350448

/-!
# Sidon sets in finite groups

Splitting a Sidon set into two disjoint parts makes multiplication injective on their
Cartesian product. This gives a universal upper bound. For the lower bound, an abelian
subgroup of index at most two loses at most a constant factor when its Sidon sets are
included in the ambient group.
-/

namespace OMA.R_mo_350448_R1

open OMA.S_mo_350448 Finset

lemma attained_sizes_bounded (G : Type) [Group G] [Fintype G] :
    {k : ℕ | ∃ S : Finset G, S.card = k ∧ IsSidonSubset S} ⊆ Set.Iic (Fintype.card G) := by
  rintro _ ⟨S, rfl, _⟩
  exact S.card_le_univ

lemma exists_maximizer (G : Type) [Group G] [Fintype G] :
    ∃ S : Finset G, S.card = Sid G ∧ IsSidonSubset S := by
  let sizes := {k : ℕ | ∃ S : Finset G, S.card = k ∧ IsSidonSubset S}
  have hn : sizes.Nonempty := ⟨0, ∅, rfl, by simp [IsSidonSubset]⟩
  exact hn.csSup_mem ((Set.finite_Iic _).subset (attained_sizes_bounded G))

lemma sid_subgroup_le {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Sid H ≤ Sid G := by
  classical
  obtain ⟨S, hS, hsid⟩ := exists_maximizer H
  let e : H ↪ G := ⟨Subtype.val, Subtype.val_injective⟩
  have image_sidon : IsSidonSubset (S.map e) := by
    intro a ha b hb c hc d hd hab hac had hbc hbd hcd heq
    obtain ⟨a, has, rfl⟩ := mem_map.mp ha
    obtain ⟨b, hbs, rfl⟩ := mem_map.mp hb
    obtain ⟨c, hcs, rfl⟩ := mem_map.mp hc
    obtain ⟨d, hds, rfl⟩ := mem_map.mp hd
    exact hsid a has b hbs c hcs d hds (hab ∘ congrArg e) (hac ∘ congrArg e)
      (had ∘ congrArg e) (hbc ∘ congrArg e) (hbd ∘ congrArg e) (hcd ∘ congrArg e)
      (Subtype.ext heq)
  apply le_csSup (s := {k : ℕ | ∃ T : Finset G, T.card = k ∧ IsSidonSubset T})
  · exact ⟨Fintype.card G, fun _ hk => attained_sizes_bounded G hk⟩
  · exact ⟨S.map e, (card_map _).trans hS, image_sidon⟩

lemma sqrt_card_eq_index_mul {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Real.sqrt (Fintype.card G) = Real.sqrt (H.index : ℝ) * Real.sqrt (Fintype.card H) := by
  have h : Fintype.card G = H.index * Fintype.card H := by
    simpa only [Nat.card_eq_fintype_card] using H.index_mul_card.symm
  rw [h, Nat.cast_mul, Real.sqrt_mul (by positivity)]

lemma cross_product_bound {G : Type} [Group G] [Fintype G] {S A B : Finset G}
    (hs : IsSidonSubset S) (ha : A ⊆ S) (hb : B ⊆ S) (hd : Disjoint A B) :
    A.card * B.card ≤ Fintype.card G := by
  classical
  let f (p : A × B) : G := p.1.val * p.2.val
  have inj : Function.Injective f := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    change a.val * b.val = c.val * d.val at h
    by_cases ac : a.val = c.val
    · have bd : b.val = d.val := mul_left_cancel (ac ▸ h)
      exact Prod.ext (Subtype.ext ac) (Subtype.ext bd)
    by_cases bd : b.val = d.val
    · exact (ac (mul_right_cancel (bd ▸ h))).elim
    have diff (u : A) (v : B) : u.val ≠ v.val :=
      fun eq => Finset.disjoint_left.mp hd u.property (eq ▸ v.property)
    exact (hs a (ha a.property) b (hb b.property) c (ha c.property) d (hb d.property)
      (diff a b) ac (diff a d) (diff c b).symm bd (diff c d) h).elim
  simpa using Fintype.card_le_of_injective f inj

lemma upper_bound (G : Type) [Group G] [Fintype G] :
    (Sid G : ℝ) / Real.sqrt (Fintype.card G) ≤ 3 := by
  classical
  obtain ⟨S, hsize, hs⟩ := exists_maximizer G
  obtain ⟨A, ha, hhalf⟩ := exists_subset_card_eq (s := S) (Nat.div_le_self S.card 2)
  have hcross := cross_product_bound hs ha (sdiff_subset (s := S) (t := A)) disjoint_sdiff
  rw [card_sdiff_of_subset ha, hhalf] at hcross
  let k := S.card / 2
  have hh : k ≤ S.card - k := by dsimp [k]; omega
  have hsq : k*k ≤ Fintype.card G := (Nat.mul_le_mul_left k hh).trans hcross
  have hkr : (k:ℝ) ≤ Real.sqrt (Fintype.card G) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (by simpa [pow_two] using hsq : k^2 ≤ Fintype.card G)
  have hpos : (1:ℝ) ≤ Real.sqrt (Fintype.card G) := by
    apply Real.le_sqrt_of_sq_le
    simpa using (show (1:ℝ) ≤ Fintype.card G by exact_mod_cast Fintype.card_pos (α := G))
  have hsize' : Sid G ≤ 2*k+1 := by dsimp [k]; omega
  have hreal : (Sid G : ℝ) ≤ 2*(k:ℝ)+1 := by exact_mod_cast hsize'
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (Fintype.card G))).mpr
  linarith

/-- The square-root lower bound for finite abelian groups. -/
def H1 : Prop := ∃ c : ℝ, 0 < c ∧ ∀ (G : Type) [Group G] [Fintype G],
  (∀ x y : G, x*y = y*x) → c * Real.sqrt (Fintype.card G) ≤ (Sid G : ℝ)

/-- The square-root lower bound for groups with no abelian subgroup of index one or two. -/
def H2 : Prop := ∃ c : ℝ, 0 < c ∧ ∀ (G : Type) [Group G] [Fintype G],
  (∀ H : Subgroup G, H.index ≤ 2 → ¬ ∀ x y : H, x*y = y*x) →
    c * Real.sqrt (Fintype.card G) ≤ (Sid G : ℝ)

theorem main : H1 → H2 → type_of% @OMA.S_mo_350448.main := by
  classical
  rintro ⟨a, ha, abelian⟩ ⟨b, hb, other⟩
  let c := min (min (a/2) b) 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := min_le_right _ _
  have hca : c ≤ a/2 := (min_le_left _ _).trans (min_le_left _ _)
  have hcb : c ≤ b := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨c, 3, hc, by linarith, ?_⟩
  intro G _ _
  have hg : 0 < Real.sqrt (Fintype.card G) := by positivity
  refine ⟨(le_div_iff₀ hg).mpr ?_, upper_bound G⟩
  by_cases ex : ∃ H : Subgroup G, H.index ≤ 2 ∧ ∀ x y : H, x*y = y*x
  · obtain ⟨H, hi, hcomm⟩ := ex
    let _ : Fintype H := Fintype.ofFinite H
    have hsize : Real.sqrt (Fintype.card G) ≤ 2 * Real.sqrt (Fintype.card H) := by
      rw [sqrt_card_eq_index_mul H]
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by norm_num, by exact_mod_cast (show H.index ≤ 2^2 by omega)⟩
    calc c * Real.sqrt (Fintype.card G) ≤ (a/2) * Real.sqrt (Fintype.card G) :=
          mul_le_mul_of_nonneg_right hca hg.le
      _ ≤ (a/2) * (2 * Real.sqrt (Fintype.card H)) := mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = a * Real.sqrt (Fintype.card H) := by ring
      _ ≤ (Sid H : ℝ) := abelian H hcomm
      _ ≤ (Sid G : ℝ) := by exact_mod_cast sid_subgroup_le H
  · exact (mul_le_mul_of_nonneg_right hcb hg.le).trans (other G (fun H hi h => ex ⟨H, hi, h⟩))

end OMA.R_mo_350448_R1
