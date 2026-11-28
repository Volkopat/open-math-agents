import OMAStatements.S_opg_shuffle_exchange_conjecture

namespace ShuffleExchangeDisproof

open OMA.S_opg_shuffle_exchange_conjecture

abbrev W3 := Word 3 3

private def baseFun (w : W3) : W3
  | 0 => w 0
  | 1 => w 2
  | 2 => if w 0 = 2 then w 1 + 1 else w 1

private def baseInv (w : W3) : W3
  | 0 => w 0
  | 1 => if w 0 = 2 then w 2 - 1 else w 2
  | 2 => w 1

private def basePerm : Equiv.Perm W3 where
  toFun := baseFun
  invFun := baseInv
  left_inv w := by
    funext i
    fin_cases i
    · rfl
    · simp only [baseInv, baseFun]
      split_ifs <;> simp
    · rfl
  right_inv w := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · simp only [baseInv, baseFun]
      split_ifs <;> simp

private def wA : W3 := ![0, 2, 2]
private def wB : W3 := ![2, 0, 2]

private def counterPerm : Equiv.Perm W3 :=
  basePerm * Equiv.swap wA wB

private lemma shuffle_apply_0 (w : W3) : shuffle 3 3 w 0 = w 1 := by
  change w (finRotate 3 0) = w 1
  rfl

private lemma shuffle_apply_1 (w : W3) : shuffle 3 3 w 1 = w 2 := by
  change w (finRotate 3 1) = w 2
  rfl

private lemma shuffle_apply_2 (w : W3) : shuffle 3 3 w 2 = w 0 := by
  change w (finRotate 3 2) = w 0
  rfl

private lemma exchange_apply_0 {g : Equiv.Perm W3} (hg : g ∈ exchange 3 3) (w : W3) :
    g w 0 = w 0 :=
  hg w 0 (by decide)

private lemma exchange_apply_1 {g : Equiv.Perm W3} (hg : g ∈ exchange 3 3) (w : W3) :
    g w 1 = w 1 :=
  hg w 1 (by decide)

private lemma word3_ext {u v : W3} (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) : u = v := by
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private lemma exists_five_step_coords {p : Equiv.Perm W3} (hp : p ∈ shuffleExchangePow 3 3 5) :
    ∃ y₁ y₂ : W3 → Fin 3,
      (∀ u v : W3, u 0 = v 0 → u 1 = v 1 → y₁ u = y₁ v → u = v) ∧
      (∀ u v : W3, u 1 = v 1 → y₁ u = y₁ v → y₂ u = y₂ v → u = v) ∧
      (∀ u v : W3, p u 2 = p v 2 → y₁ u = y₁ v → y₂ u = y₂ v → u = v) ∧
      (∀ u v : W3, p u 2 = p v 2 → p u 0 = p v 0 → y₂ u = y₂ v → u = v) := by
  rcases hp with ⟨a4, ha4, g5, hg5, rfl⟩
  rcases ha4 with ⟨a3, ha3, g4, hg4, rfl⟩
  rcases ha3 with ⟨a2, ha2, g3, hg3, rfl⟩
  rcases ha2 with ⟨a1, ha1, g2, hg2, rfl⟩
  rcases ha1 with ⟨a0, ha0, g1, hg1, rfl⟩
  have ha0' : a0 = 1 := Set.mem_singleton_iff.mp ha0
  subst ha0'
  set σ : Equiv.Perm W3 := shuffle 3 3
  set t₁ : Equiv.Perm W3 := g5
  set t₂ : Equiv.Perm W3 := g4 * (σ * t₁)
  set t₃ : Equiv.Perm W3 := g3 * (σ * t₂)
  set t₄ : Equiv.Perm W3 := g2 * (σ * t₃)
  set t₅ : Equiv.Perm W3 := g1 * (σ * t₄)
  have hp_eq : 1 * (σ * g1) * (σ * g2) * (σ * g3) * (σ * g4) * (σ * g5) = σ * t₅ := by
    simp only [t₅, t₄, t₃, t₂, t₁, one_mul, mul_assoc]
  set y₁ : W3 → Fin 3 := fun w => t₁ w 2
  set y₂ : W3 → Fin 3 := fun w => t₂ w 2
  have ht1_0 : ∀ w, t₁ w 0 = w 0 := fun w => exchange_apply_0 hg5 w
  have ht1_1 : ∀ w, t₁ w 1 = w 1 := fun w => exchange_apply_1 hg5 w
  have ht2_0 : ∀ w, t₂ w 0 = w 1 := fun w => by
    simp only [t₂, σ, Equiv.Perm.mul_apply, exchange_apply_0 hg4, shuffle_apply_0, ht1_1]
  have ht2_1 : ∀ w, t₂ w 1 = y₁ w := fun w => by
    simp only [t₂, σ, Equiv.Perm.mul_apply, exchange_apply_1 hg4, shuffle_apply_1, y₁]
  have ht3_0 : ∀ w, t₃ w 0 = y₁ w := fun w => by
    simp only [t₃, σ, Equiv.Perm.mul_apply, exchange_apply_0 hg3, shuffle_apply_0, ht2_1]
  have ht3_1 : ∀ w, t₃ w 1 = y₂ w := fun w => by
    simp only [t₃, σ, Equiv.Perm.mul_apply, exchange_apply_1 hg3, shuffle_apply_1, y₂]
  have ht4_0 : ∀ w, t₄ w 0 = y₂ w := fun w => by
    simp only [t₄, σ, Equiv.Perm.mul_apply, exchange_apply_0 hg2, shuffle_apply_0, ht3_1]
  have ht4_1 : ∀ w, t₄ w 1 = t₃ w 2 := fun w => by
    simp only [t₄, σ, Equiv.Perm.mul_apply, exchange_apply_1 hg2, shuffle_apply_1]
  have ht5_0 : ∀ w, t₅ w 0 = t₃ w 2 := fun w => by
    simp only [t₅, σ, Equiv.Perm.mul_apply, exchange_apply_0 hg1, shuffle_apply_0, ht4_1]
  have ht5_1 : ∀ w, t₅ w 1 = t₄ w 2 := fun w => by
    simp only [t₅, σ, Equiv.Perm.mul_apply, exchange_apply_1 hg1, shuffle_apply_1]
  have hp_0 : ∀ w, (σ * t₅) w 0 = t₄ w 2 := fun w => by
    simp only [σ, Equiv.Perm.mul_apply, shuffle_apply_0, ht5_1]
  have hp_2 : ∀ w, (σ * t₅) w 2 = t₃ w 2 := fun w => by
    simp only [σ, Equiv.Perm.mul_apply, shuffle_apply_2, ht5_0]
  refine ⟨y₁, y₂, ?_, ?_, ?_, ?_⟩
  · intro u v h0 h1 hy1
    exact t₁.injective (word3_ext (by rw [ht1_0, ht1_0, h0]) (by rw [ht1_1, ht1_1, h1]) hy1)
  · intro u v h1 hy1 hy2
    exact t₂.injective (word3_ext (by rw [ht2_0, ht2_0, h1]) (by rw [ht2_1, ht2_1, hy1]) hy2)
  · intro u v hz2 hy1 hy2
    rw [hp_eq] at hz2
    exact t₃.injective (word3_ext (by rw [ht3_0, ht3_0, hy1]) (by rw [ht3_1, ht3_1, hy2])
      (by rw [← hp_2 u, ← hp_2 v, hz2]))
  · intro u v hz2 hz0 hy2
    rw [hp_eq] at hz2 hz0
    exact t₄.injective (word3_ext (by rw [ht4_0, ht4_0, hy2])
      (by rw [ht4_1, ht4_1, ← hp_2 u, ← hp_2 v, hz2]) (by rw [← hp_0 u, ← hp_0 v, hz0]))

private def LSet (a b : Fin 3) : Finset W3 :=
  Finset.univ.filter (fun w => w 0 = a ∧ w 1 = b)

private def RSet (c d : Fin 3) : Finset W3 :=
  Finset.univ.filter (fun w => counterPerm w 2 = c ∧ counterPerm w 0 = d)

private def IsMatching (M : Finset (Fin 3 × Fin 3)) : Prop :=
  M.card = 3 ∧
  (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧
  (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q)

private lemma fin3_third_unique {a b x y : Fin 3} (hab : a ≠ b)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) : x = y := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;> simp_all

private lemma matching_eq_of_two_common {M₁ M₂ : Finset (Fin 3 × Fin 3)}
    (h1 : IsMatching M₁) (h2 : IsMatching M₂) {p q : Fin 3 × Fin 3}
    (hpq : p ≠ q) (hp1 : p ∈ M₁) (hq1 : q ∈ M₁) (hp2 : p ∈ M₂) (hq2 : q ∈ M₂) :
    M₁ = M₂ := by
  have hpq1 : p.1 ≠ q.1 := fun h => hpq (h1.2.1 p hp1 q hq1 h)
  have hpq2 : p.2 ≠ q.2 := fun h => hpq (h1.2.2 p hp1 q hq1 h)
  have hcard_pq : ({p, q} : Finset (Fin 3 × Fin 3)).card = 2 := Finset.card_pair hpq
  have hsub2 : ({p, q} : Finset (Fin 3 × Fin 3)) ⊆ M₂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hex2 : (M₂ \ {p, q}).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub2, h2.1, hcard_pq]
    omega
  rcases hex2 with ⟨s, hs⟩
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  rcases hs with ⟨hs2, hsp, hsq⟩
  have hs1p : s.1 ≠ p.1 := fun h => hsp (h2.2.1 s hs2 p hp2 h)
  have hs1q : s.1 ≠ q.1 := fun h => hsq (h2.2.1 s hs2 q hq2 h)
  have hs2p : s.2 ≠ p.2 := fun h => hsp (h2.2.2 s hs2 p hp2 h)
  have hs2q : s.2 ≠ q.2 := fun h => hsq (h2.2.2 s hs2 q hq2 h)
  apply Finset.eq_of_subset_of_card_le _ (by rw [h1.1, h2.1])
  intro r hr1
  by_cases hrp : r = p
  · exact hrp ▸ hp2
  by_cases hrq : r = q
  · exact hrq ▸ hq2
  have hr1p : r.1 ≠ p.1 := fun h => hrp (h1.2.1 r hr1 p hp1 h)
  have hr1q : r.1 ≠ q.1 := fun h => hrq (h1.2.1 r hr1 q hq1 h)
  have hr2p : r.2 ≠ p.2 := fun h => hrp (h1.2.2 r hr1 p hp1 h)
  have hr2q : r.2 ≠ q.2 := fun h => hrq (h1.2.2 r hr1 q hq1 h)
  have hfst : r.1 = s.1 := fin3_third_unique hpq1 hr1p hr1q hs1p hs1q
  have hsnd : r.2 = s.2 := fin3_third_unique hpq2 hr2p hr2q hs2p hs2q
  have hrs : r = s := Prod.ext hfst hsnd
  exact hrs ▸ hs2

private lemma third_part_eq {α : Type*} [DecidableEq α] [Fintype α]
    {A B C C' : Finset α}
    (hU1 : A ∪ B ∪ C = Finset.univ) (hU2 : A ∪ B ∪ C' = Finset.univ)
    (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hAC' : Disjoint A C') (hBC' : Disjoint B C') : C = C' := by
  ext x
  constructor
  · intro hxC
    have hxA : x ∉ A := Finset.disjoint_right.mp hAC hxC
    have hxB : x ∉ B := Finset.disjoint_right.mp hBC hxC
    have hxU : x ∈ A ∪ B ∪ C' := by rw [hU2]; exact Finset.mem_univ x
    simp only [Finset.mem_union] at hxU
    tauto
  · intro hxC'
    have hxA : x ∉ A := Finset.disjoint_right.mp hAC' hxC'
    have hxB : x ∉ B := Finset.disjoint_right.mp hBC' hxC'
    have hxU : x ∈ A ∪ B ∪ C := by rw [hU1]; exact Finset.mem_univ x
    simp only [Finset.mem_union] at hxU
    tauto

private lemma counterPerm_not_mem_pow5 : counterPerm ∉ shuffleExchangePow 3 3 5 := by
  intro hmem
  rcases exists_five_step_coords hmem with ⟨y₁, y₂, h1, h2, h3, h4⟩
  let col : W3 → Fin 3 × Fin 3 := fun w => (y₁ w, y₂ w)
  let F : Fin 3 → Fin 3 → Finset (Fin 3 × Fin 3) := fun a b => (LSet a b).image col
  let H : Fin 3 → Fin 3 → Finset (Fin 3 × Fin 3) := fun c d => (RSet c d).image col
  -- Left block partition properties
  have hL_union : ∀ b : Fin 3, F 0 b ∪ F 1 b ∪ F 2 b = Finset.univ := by
    intro b
    let S : Finset W3 := Finset.univ.filter (fun w => w 1 = b)
    have hS_eq : LSet 0 b ∪ LSet 1 b ∪ LSet 2 b = S := by
      ext w
      simp only [Finset.mem_union, LSet, S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) <;> exact h
      · intro h
        have h3cases : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
        rcases h3cases (w 0) with h0 | h0 | h0 <;> simp [h, h0]
    have himg : F 0 b ∪ F 1 b ∪ F 2 b = S.image col := by
      simp only [F, ← Finset.image_union, hS_eq]
    rw [himg]
    apply Finset.eq_univ_of_card
    have hinj : Set.InjOn col (S : Set W3) := by
      intro u hu v hv huv
      simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      have hp1 : y₁ u = y₁ v := congrArg Prod.fst huv
      have hp2 : y₂ u = y₂ v := congrArg Prod.snd huv
      exact h2 u v (hu.trans hv.symm) hp1 hp2
    rw [Finset.card_image_of_injOn hinj]
    have hScard : S.card = 9 := by
      fin_cases b <;> decide
    rw [hScard]
    decide
  have hL_disj : ∀ b a₁ a₂ : Fin 3, a₁ ≠ a₂ → Disjoint (F a₁ b) (F a₂ b) := by
    intro b a₁ a₂ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨v, hv, huv⟩
    simp only [LSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    have heq : u = v := h2 u v (hu.2.trans hv.2.symm) (congrArg Prod.fst huv.symm)
      (congrArg Prod.snd huv.symm)
    subst heq
    exact hne (hu.1.symm.trans hv.1)
  -- Right block partition properties
  have hR_union : ∀ c : Fin 3, H c 0 ∪ H c 1 ∪ H c 2 = Finset.univ := by
    intro c
    let T : Finset W3 := Finset.univ.filter (fun w => counterPerm w 2 = c)
    have hT_eq : RSet c 0 ∪ RSet c 1 ∪ RSet c 2 = T := by
      ext w
      simp only [Finset.mem_union, RSet, T, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h
        have h3cases : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
        rcases h3cases (counterPerm w 0) with h0 | h0 | h0 <;> simp [h, h0]
    have himg : H c 0 ∪ H c 1 ∪ H c 2 = T.image col := by
      simp only [H, ← Finset.image_union, hT_eq]
    rw [himg]
    apply Finset.eq_univ_of_card
    have hinj : Set.InjOn col (T : Set W3) := by
      intro u hu v hv huv
      simp only [Finset.mem_coe, T, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      exact h3 u v (hu.trans hv.symm) (congrArg Prod.fst huv) (congrArg Prod.snd huv)
    rw [Finset.card_image_of_injOn hinj]
    have hTcard : T.card = 9 := by
      fin_cases c <;> decide
    rw [hTcard]
    decide
  have hR_disj : ∀ c d₁ d₂ : Fin 3, d₁ ≠ d₂ → Disjoint (H c d₁) (H c d₂) := by
    intro c d₁ d₂ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨v, hv, huv⟩
    simp only [RSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    have heq : u = v := h3 u v (hu.1.trans hv.1.symm) (congrArg Prod.fst huv.symm)
      (congrArg Prod.snd huv.symm)
    subst heq
    exact hne (hu.2.symm.trans hv.2)
  -- Full 3-bundle matches (each verified by decide on 27 elements)
  have hLR00 : LSet 0 0 = RSet 0 0 := by decide
  have hLR10 : LSet 1 0 = RSet 0 1 := by decide
  have hLR01 : LSet 0 1 = RSet 1 0 := by decide
  have hLR11 : LSet 1 1 = RSet 1 1 := by decide
  have hLR21 : LSet 2 1 = RSet 2 2 := by decide
  have hLR22 : LSet 2 2 = RSet 0 2 := by decide
  have hFH00 : F 0 0 = H 0 0 := congrArg (Finset.image col) hLR00
  have hFH10 : F 1 0 = H 0 1 := congrArg (Finset.image col) hLR10
  have hFH01 : F 0 1 = H 1 0 := congrArg (Finset.image col) hLR01
  have hFH11 : F 1 1 = H 1 1 := congrArg (Finset.image col) hLR11
  have hFH21 : F 2 1 = H 2 2 := congrArg (Finset.image col) hLR21
  have hFH22 : F 2 2 = H 0 2 := congrArg (Finset.image col) hLR22
  -- Helper: any coinciding LSet a b = RSet c d yields a matching
  have mk_matching : ∀ a b c d : Fin 3, LSet a b = RSet c d → IsMatching (F a b) := by
    intro a b c d hLR
    have hFH : F a b = H c d := congrArg (Finset.image col) hLR
    refine ⟨?_, ?_, ?_⟩
    · have hinj : Set.InjOn col (LSet a b : Set W3) := by
        intro u hu v hv huv
        simp only [Finset.mem_coe, LSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
        exact h1 u v (hu.1.trans hv.1.symm) (hu.2.trans hv.2.symm) (congrArg Prod.fst huv)
      rw [Finset.card_image_of_injOn hinj]
      fin_cases a <;> fin_cases b <;> decide
    · intro p hp q hq hpq1
      rcases Finset.mem_image.mp hp with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp hq with ⟨v, hv, rfl⟩
      simp only [LSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      have heq : u = v := h1 u v (hu.1.trans hv.1.symm) (hu.2.trans hv.2.symm) hpq1
      rw [heq]
    · intro p hp q hq hpq2
      rw [hFH] at hp hq
      rcases Finset.mem_image.mp hp with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp hq with ⟨v, hv, rfl⟩
      simp only [RSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      have heq : u = v := h4 u v (hu.1.trans hv.1.symm) (hu.2.trans hv.2.symm) hpq2
      rw [heq]
  have hM_X2 : IsMatching (H 0 2) := hFH22 ▸ mk_matching 2 2 0 2 hLR22
  have hM_X1 : IsMatching (F 2 1) := mk_matching 2 1 2 2 hLR21
  -- Block 0 comparison: F 2 0 = H 0 2
  have hF20 : F 2 0 = H 0 2 := by
    apply third_part_eq (A := F 0 0) (B := F 1 0)
    · exact hL_union 0
    · rw [hFH00, hFH10]; exact hR_union 0
    · exact hL_disj 0 0 2 (by decide)
    · exact hL_disj 0 1 2 (by decide)
    · rw [hFH00]; exact hR_disj 0 0 2 (by decide)
    · rw [hFH10]; exact hR_disj 0 1 2 (by decide)
  -- Block 1 comparison: F 2 1 = H 1 2
  have hH12 : F 2 1 = H 1 2 := by
    apply third_part_eq (A := F 0 1) (B := F 1 1)
    · exact hL_union 1
    · rw [hFH01, hFH11]; exact hR_union 1
    · exact hL_disj 1 0 2 (by decide)
    · exact hL_disj 1 1 2 (by decide)
    · rw [hFH01]; exact hR_disj 1 0 2 (by decide)
    · rw [hFH11]; exact hR_disj 1 1 2 (by decide)
  -- Two parallel edges from LSet 2 0 to RSet 1 2 force H 0 2 = F 2 1
  let u₁ : W3 := ![2, 0, 0]
  let u₂ : W3 := ![2, 0, 1]
  have hu₁L : u₁ ∈ LSet 2 0 := by decide
  have hu₂L : u₂ ∈ LSet 2 0 := by decide
  have hu₁R : u₁ ∈ RSet 1 2 := by decide
  have hu₂R : u₂ ∈ RSet 1 2 := by decide
  have hcol_ne : col u₁ ≠ col u₂ := by
    intro hcol
    have heq : u₁ = u₂ := h1 u₁ u₂ rfl rfl (congrArg Prod.fst hcol)
    have h01 : (0 : Fin 3) = 1 := congrFun heq 2
    exact absurd h01 (by decide)
  have hu₁_X2 : col u₁ ∈ H 0 2 := hF20 ▸ Finset.mem_image_of_mem col hu₁L
  have hu₂_X2 : col u₂ ∈ H 0 2 := hF20 ▸ Finset.mem_image_of_mem col hu₂L
  have hu₁_X1 : col u₁ ∈ F 2 1 := hH12 ▸ Finset.mem_image_of_mem col hu₁R
  have hu₂_X1 : col u₂ ∈ F 2 1 := hH12 ▸ Finset.mem_image_of_mem col hu₂R
  have hX_eq : H 0 2 = F 2 1 :=
    matching_eq_of_two_common hM_X2 hM_X1 hcol_ne hu₁_X2 hu₂_X2 hu₁_X1 hu₂_X1
  -- Final contradiction on wB = ![2, 0, 2] ∈ LSet 2 0 ∩ RSet 2 0
  have hwBL : wB ∈ LSet 2 0 := by decide
  have hwBR : wB ∈ RSet 2 0 := by decide
  have hcol_in_H22 : col wB ∈ H 2 2 := by
    rw [← hFH21, ← hX_eq, ← hF20]
    exact Finset.mem_image_of_mem col hwBL
  have hcol_in_H20 : col wB ∈ H 2 0 := Finset.mem_image_of_mem col hwBR
  exact Finset.disjoint_left.mp (hR_disj 2 0 2 (by decide)) hcol_in_H20 hcol_in_H22

end ShuffleExchangeDisproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_shuffle_exchange_conjecture.main) := by
  intro hmain
  have hd : OMA.S_opg_shuffle_exchange_conjecture.d 3 3 = 5 := hmain 3 3 (by decide) (by decide)
  let S : Set ℕ := {m : ℕ | 2 ≤ m ∧ OMA.S_opg_shuffle_exchange_conjecture.shuffleExchangePow 3 3 m = Set.univ}
  have hsInf : sInf S = 5 := hd
  have hne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, Nat.sInf_empty] at hsInf
    omega
  have h5 : 5 ∈ S := hsInf ▸ Nat.sInf_mem hne
  have huniv : OMA.S_opg_shuffle_exchange_conjecture.shuffleExchangePow 3 3 5 = Set.univ := h5.2
  have hmem : ShuffleExchangeDisproof.counterPerm ∈
      OMA.S_opg_shuffle_exchange_conjecture.shuffleExchangePow 3 3 5 := by
    rw [huniv]
    exact Set.mem_univ _
  exact ShuffleExchangeDisproof.counterPerm_not_mem_pow5 hmem
