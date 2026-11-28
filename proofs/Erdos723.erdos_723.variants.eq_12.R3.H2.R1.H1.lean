import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R3_H2_R1

/-!
# Step R3.H2.R1.H1: a Latin-square certificate gives 139 lines

Points (157): the 121 cells of the square, the three vertices of a triangle, and on the side
opposite vertex `d` the eleven points `(d, a)`, one for each value `a` of coordinate `d`
(row, column or symbol).

Lines (139): the 103 certificate lines (the ten cells of `B i` together with the three side
points of the values that `B i` omits), the three sides, and the 33 lines through a vertex
(vertex `d`, side point `(d, a)` and the eleven cells whose coordinate `d` equals `a`).

The three coordinates are handled uniformly: the only property of the Latin square that is
used is that any two coordinates determine the cell.
-/

namespace OMA.Seed139

open Finset

/-- Points: cells, vertices, side points. -/
abbrev Pt := (Fin 11 × Fin 11) ⊕ (Fin 3 ⊕ (Fin 3 × Fin 11))

/-- Lines: certificate lines, sides, lines through a vertex. -/
abbrev Ln := Fin 103 ⊕ (Fin 3 ⊕ (Fin 3 × Fin 11))

/-- The side points `(d, a)` such that the value `a` of coordinate `d` is omitted by `X`. -/
def miss (c : Fin 3 → Fin 11 × Fin 11 → Fin 11) (X : Finset (Fin 11 × Fin 11)) :
    Finset (Fin 3 × Fin 11) :=
  univ.filter (fun p => p.2 ∉ X.image (c p.1))

/-- The cells whose coordinate `d` equals `a`. -/
def fiber (c : Fin 3 → Fin 11 × Fin 11 → Fin 11) (d : Fin 3) (a : Fin 11) :
    Finset (Fin 11 × Fin 11) :=
  univ.filter (fun x => c d x = a)

/-- The 139 lines, each given by its cells, its vertices and its side points. -/
def line (c : Fin 3 → Fin 11 × Fin 11 → Fin 11) (B : Fin 103 → Finset (Fin 11 × Fin 11)) :
    Ln → Finset Pt
  | .inl i => (B i).disjSum ((∅ : Finset (Fin 3)).disjSum (miss c (B i)))
  | .inr (.inl d) => (∅ : Finset (Fin 11 × Fin 11)).disjSum
      ((univ.erase d).disjSum (({d} : Finset (Fin 3)) ×ˢ (univ : Finset (Fin 11))))
  | .inr (.inr (d, a)) => (fiber c d a).disjSum (({d} : Finset (Fin 3)).disjSum {(d, a)})

lemma disjSum_inter {α β : Type} [DecidableEq α] [DecidableEq β] (s₁ s₂ : Finset α)
    (t₁ t₂ : Finset β) : s₁.disjSum t₁ ∩ s₂.disjSum t₂ = (s₁ ∩ s₂).disjSum (t₁ ∩ t₂) := by
  ext x
  cases x <;> simp

/-- A ten-cell set on which coordinate `d` is injective omits exactly one value of it. -/
lemma missing (c : Fin 3 → Fin 11 × Fin 11 → Fin 11) (X : Finset (Fin 11 × Fin 11))
    (hX : X.card = 10) (d : Fin 3) (hinj : Set.InjOn (c d) (X : Set (Fin 11 × Fin 11))) :
    ∃ a, a ∉ X.image (c d) ∧ ∀ b, b ∉ X.image (c d) → b = a := by
  have h1 : (X.image (c d)).card = 10 := by rw [card_image_of_injOn hinj, hX]
  have h2 : (univ \ X.image (c d)).card = 1 := by
    rw [card_univ_sdiff, h1]
    simp
  obtain ⟨a, ha⟩ := card_eq_one.1 h2
  refine ⟨a, ?_, ?_⟩
  · have hmem : a ∈ univ \ X.image (c d) := by
      rw [ha]
      exact mem_singleton_self a
    exact (mem_sdiff.1 hmem).2
  · intro b hb
    have hmem : b ∈ univ \ X.image (c d) := mem_sdiff.2 ⟨mem_univ b, hb⟩
    rw [ha] at hmem
    exact mem_singleton.1 hmem

lemma card_miss (c : Fin 3 → Fin 11 × Fin 11 → Fin 11) (X : Finset (Fin 11 × Fin 11))
    (hX : X.card = 10) (hinj : ∀ d, Set.InjOn (c d) (X : Set (Fin 11 × Fin 11))) :
    (miss c X).card = 3 := by
  have hinjOn : Set.InjOn Prod.fst (miss c X : Set (Fin 3 × Fin 11)) := by
    rintro ⟨d, a⟩ ha ⟨e, b⟩ hb h
    have hde : d = e := h
    subst hde
    simp only [mem_coe, miss, mem_filter, mem_univ, true_and] at ha hb
    obtain ⟨a₀, -, huniq⟩ := missing c X hX d (hinj d)
    rw [huniq a ha, huniq b hb]
  have himg : (miss c X).image Prod.fst = univ := by
    apply eq_univ_of_forall
    intro d
    obtain ⟨a₀, ha₀, -⟩ := missing c X hX d (hinj d)
    exact mem_image.2 ⟨(d, a₀), mem_filter.2 ⟨mem_univ _, ha₀⟩, rfl⟩
  rw [← card_image_of_injOn hinjOn, himg]
  simp

lemma inter_miss (c : Fin 3 → Fin 11 × Fin 11 → Fin 11) (X Y : Finset (Fin 11 × Fin 11))
    (hX : X.card = 10) (hinj : ∀ d, Set.InjOn (c d) (X : Set (Fin 11 × Fin 11))) :
    (miss c X ∩ miss c Y).card =
      (univ.filter (fun d : Fin 3 => ∃ a : Fin 11, a ∉ X.image (c d) ∧ a ∉ Y.image (c d))).card := by
  have hinjOn : Set.InjOn Prod.fst ((miss c X ∩ miss c Y : Finset (Fin 3 × Fin 11)) :
      Set (Fin 3 × Fin 11)) := by
    rintro ⟨d, a⟩ ha ⟨e, b⟩ hb h
    have hde : d = e := h
    subst hde
    simp only [coe_inter, Set.mem_inter_iff, mem_coe, miss, mem_filter, mem_univ, true_and]
      at ha hb
    obtain ⟨a₀, -, huniq⟩ := missing c X hX d (hinj d)
    rw [huniq a ha.1, huniq b hb.1]
  rw [← card_image_of_injOn hinjOn]
  congr 1
  ext d
  simp only [mem_image, mem_inter, miss, mem_filter, mem_univ, true_and, Prod.exists,
    exists_and_right, exists_eq_right]

lemma inter_side (c : Fin 3 → Fin 11 × Fin 11 → Fin 11) (X : Finset (Fin 11 × Fin 11))
    (hX : X.card = 10) (hinj : ∀ d, Set.InjOn (c d) (X : Set (Fin 11 × Fin 11))) (d : Fin 3) :
    (miss c X ∩ (({d} : Finset (Fin 3)) ×ˢ (univ : Finset (Fin 11)))).card = 1 := by
  obtain ⟨a₀, ha₀, huniq⟩ := missing c X hX d (hinj d)
  rw [card_eq_one]
  refine ⟨(d, a₀), ?_⟩
  ext ⟨e, b⟩
  simp only [mem_inter, miss, mem_filter, mem_univ, true_and, mem_product, mem_singleton,
    and_true, Prod.mk.injEq]
  constructor
  · rintro ⟨hb, rfl⟩
    exact ⟨rfl, huniq b hb⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨ha₀, rfl⟩

lemma inter_pencil (c : Fin 3 → Fin 11 × Fin 11 → Fin 11) (X : Finset (Fin 11 × Fin 11))
    (hinj : ∀ d, Set.InjOn (c d) (X : Set (Fin 11 × Fin 11))) (d : Fin 3) (a : Fin 11) :
    (X ∩ fiber c d a).card + (miss c X ∩ {(d, a)}).card = 1 := by
  by_cases ha : a ∈ X.image (c d)
  · obtain ⟨x, hx, rfl⟩ := mem_image.1 ha
    have h1 : X ∩ fiber c d (c d x) = {x} := by
      ext y
      simp only [mem_inter, fiber, mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hy, hxy⟩
        exact hinj d hy hx hxy
      · rintro rfl
        exact ⟨hx, rfl⟩
    have h2 : miss c X ∩ {(d, c d x)} = ∅ := by
      apply inter_singleton_of_notMem
      simp only [miss, mem_filter, mem_univ, true_and, not_not]
      exact ha
    rw [h1, h2]
    simp
  · have h1 : X ∩ fiber c d a = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro y hy
      simp only [mem_inter, fiber, mem_filter, mem_univ, true_and] at hy
      exact ha (mem_image.2 ⟨y, hy.1, hy.2⟩)
    have h2 : miss c X ∩ {(d, a)} = {(d, a)} := by
      apply inter_singleton_of_mem
      simp only [miss, mem_filter, mem_univ, true_and]
      exact ha
    rw [h1, h2]
    simp

lemma card_fiber (c : Fin 3 → Fin 11 × Fin 11 → Fin 11)
    (hc : ∀ d e, d ≠ e → Function.Injective (fun x => (c d x, c e x))) (d : Fin 3) (a : Fin 11) :
    (fiber c d a).card = 11 := by
  have hde : d ≠ d + 1 := by
    revert d
    decide
  have hbij := Finite.injective_iff_bijective.1 (hc d (d + 1) hde)
  have hinjOn : Set.InjOn (c (d + 1)) (fiber c d a : Set (Fin 11 × Fin 11)) := by
    intro x hx y hy hxy
    simp only [fiber, mem_coe, mem_filter, mem_univ, true_and] at hx hy
    apply hc d (d + 1) hde
    exact Prod.ext (hx.trans hy.symm) hxy
  have himg : (fiber c d a).image (c (d + 1)) = univ := by
    apply eq_univ_of_forall
    intro b
    obtain ⟨x, hx⟩ := hbij.2 (a, b)
    simp only [Prod.mk.injEq] at hx
    exact mem_image.2 ⟨x, mem_filter.2 ⟨mem_univ _, hx.1⟩, hx.2⟩
  rw [← card_image_of_injOn hinjOn, himg]
  simp

lemma inter_fiber (c : Fin 3 → Fin 11 × Fin 11 → Fin 11)
    (hc : ∀ d e, d ≠ e → Function.Injective (fun x => (c d x, c e x))) (d e : Fin 3)
    (a b : Fin 11) (hde : d ≠ e) : (fiber c d a ∩ fiber c e b).card = 1 := by
  obtain ⟨x, hx⟩ := (Finite.injective_iff_bijective.1 (hc d e hde)).2 (a, b)
  simp only [Prod.mk.injEq] at hx
  rw [card_eq_one]
  refine ⟨x, ?_⟩
  ext y
  simp only [mem_inter, fiber, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    apply hc d e hde
    exact Prod.ext (h1.trans hx.1.symm) (h2.trans hx.2.symm)
  · rintro rfl
    exact hx

lemma card_line (c : Fin 3 → Fin 11 × Fin 11 → Fin 11)
    (hc : ∀ d e, d ≠ e → Function.Injective (fun x => (c d x, c e x)))
    (B : Fin 103 → Finset (Fin 11 × Fin 11))
    (hB : ∀ i, (B i).card = 10 ∧ ∀ d, Set.InjOn (c d) (B i : Set (Fin 11 × Fin 11)))
    (k : Ln) : (line c B k).card = 13 := by
  rcases k with i | d | ⟨d, a⟩
  · simp only [line, card_disjSum, card_empty, card_miss c (B i) (hB i).1 (hB i).2, (hB i).1]
  · simp only [line, card_disjSum, card_empty, card_product, card_singleton, card_univ,
      Fintype.card_fin, card_erase_of_mem (mem_univ d)]
  · simp only [line, card_disjSum, card_singleton, card_fiber c hc d a]

lemma meet_line (c : Fin 3 → Fin 11 × Fin 11 → Fin 11)
    (hc : ∀ d e, d ≠ e → Function.Injective (fun x => (c d x, c e x)))
    (B : Fin 103 → Finset (Fin 11 × Fin 11))
    (hB : ∀ i, (B i).card = 10 ∧ ∀ d, Set.InjOn (c d) (B i : Set (Fin 11 × Fin 11)))
    (hmeet : ∀ i j, i ≠ j →
      (B i ∩ B j).card + (univ.filter (fun d : Fin 3 =>
        ∃ a : Fin 11, a ∉ (B i).image (c d) ∧ a ∉ (B j).image (c d))).card = 1)
    (k l : Ln) (hkl : k ≠ l) : (line c B k ∩ line c B l).card = 1 := by
  rcases k with i | d | ⟨d, a⟩ <;> rcases l with j | e | ⟨e, b⟩ <;>
    simp only [line, disjSum_inter, card_disjSum, inter_empty, empty_inter, card_empty,
      zero_add]
  · -- two certificate lines
    have hij : i ≠ j := fun h => hkl (congrArg Sum.inl h)
    rw [inter_miss c (B i) (B j) (hB i).1 (hB i).2]
    exact hmeet i j hij
  · -- a certificate line and a side
    exact inter_side c (B i) (hB i).1 (hB i).2 e
  · -- a certificate line and a line through a vertex
    have h := inter_pencil c (B i) (hB i).2 e b
    omega
  · -- a side and a certificate line
    rw [inter_comm]
    exact inter_side c (B j) (hB j).1 (hB j).2 d
  · -- two sides
    have hde : d ≠ e := fun h => hkl (congrArg (fun t => Sum.inr (Sum.inl t)) h)
    have h1 : ((univ : Finset (Fin 3)).erase d ∩ univ.erase e).card = 1 := by
      revert d e
      decide
    have h2 : (({d} : Finset (Fin 3)) ×ˢ (univ : Finset (Fin 11)) ∩
        ({e} : Finset (Fin 3)) ×ˢ (univ : Finset (Fin 11))).card = 0 := by
      rw [product_inter_product, singleton_inter_of_notMem (by simpa using hde)]
      simp
    omega
  · -- a side and a line through a vertex
    by_cases h : e = d
    · subst h
      rw [inter_singleton_of_notMem (by simp), inter_singleton_of_mem (by simp)]
      simp
    · rw [inter_singleton_of_mem (by simpa using h),
        inter_singleton_of_notMem (by simpa using Ne.symm h)]
      simp
  · -- a line through a vertex and a certificate line
    have h := inter_pencil c (B j) (hB j).2 d a
    rw [inter_comm (fiber c d a), inter_comm {(d, a)}]
    omega
  · -- a line through a vertex and a side
    by_cases h : d = e
    · subst h
      rw [singleton_inter_of_notMem (by simp), singleton_inter_of_mem (by simp)]
      simp
    · rw [singleton_inter_of_mem (by simpa using h),
        singleton_inter_of_notMem (by simpa using Ne.symm h)]
      simp
  · -- two lines through vertices
    by_cases hde : d = e
    · subst hde
      have hab : a ≠ b := fun h => hkl (by rw [h])
      have h1 : fiber c d a ∩ fiber c d b = ∅ := by
        apply eq_empty_iff_forall_notMem.2
        intro x hx
        simp only [mem_inter, fiber, mem_filter, mem_univ, true_and] at hx
        exact hab (hx.1.symm.trans hx.2)
      have h2 : ({(d, a)} : Finset (Fin 3 × Fin 11)) ∩ {(d, b)} = ∅ :=
        singleton_inter_of_notMem (by simpa using hab)
      rw [h1, h2]
      simp
    · rw [inter_fiber c hc d e a b hde, singleton_inter_of_notMem (by simpa using hde),
        singleton_inter_of_notMem (by simp [hde])]
      simp

/-- Any two of row, column and symbol determine the cell. -/
lemma pair_inj (s : Fin 11 × Fin 11 → Fin 11)
    (rows : ∀ r : Fin 11, Function.Injective (fun k : Fin 11 => s (r, k)))
    (cols : ∀ k : Fin 11, Function.Injective (fun r : Fin 11 => s (r, k))) (d e : Fin 3)
    (hde : d ≠ e) :
    Function.Injective (fun x =>
      ((![Prod.fst, Prod.snd, s] : Fin 3 → Fin 11 × Fin 11 → Fin 11) d x,
        (![Prod.fst, Prod.snd, s] : Fin 3 → Fin 11 × Fin 11 → Fin 11) e x)) := by
  rintro ⟨r, k⟩ ⟨r', k'⟩ h
  simp only [Prod.mk.injEq] at h ⊢
  fin_cases d <;> fin_cases e <;> simp at hde h ⊢
  · exact h
  · exact ⟨h.1, rows r (h.1 ▸ h.2)⟩
  · exact ⟨h.2, h.1⟩
  · obtain ⟨rfl, h2⟩ := h
    exact ⟨cols k h2, rfl⟩
  · obtain ⟨h2, rfl⟩ := h
    exact ⟨rfl, rows r h2⟩
  · obtain ⟨h2, rfl⟩ := h
    exact ⟨cols k h2, rfl⟩

/-- The construction, for any three coordinates any two of which determine the cell. -/
theorem seed (c : Fin 3 → Fin 11 × Fin 11 → Fin 11)
    (hc : ∀ d e, d ≠ e → Function.Injective (fun x => (c d x, c e x)))
    (B : Fin 103 → Finset (Fin 11 × Fin 11))
    (hB : ∀ i, (B i).card = 10 ∧ ∀ d, Set.InjOn (c d) (B i : Set (Fin 11 × Fin 11)))
    (hmeet : ∀ i j, i ≠ j →
      (B i ∩ B j).card + (univ.filter (fun d : Fin 3 =>
        ∃ a : Fin 11, a ∉ (B i).image (c d) ∧ a ∉ (B j).image (c d))).card = 1) :
    ∃ M : Fin 139 → Finset (Fin 157), (∀ i, (M i).card = 13) ∧
      ∀ i j, i ≠ j → ∃! p, p ∈ M i ∧ p ∈ M j := by
  let eP : Pt ≃ Fin 157 := Fintype.equivFinOfCardEq (by simp)
  let eL : Ln ≃ Fin 139 := Fintype.equivFinOfCardEq (by simp)
  refine ⟨fun i => (line c B (eL.symm i)).map eP.toEmbedding, fun i => ?_, fun i j hij => ?_⟩
  · rw [card_map]
    exact card_line c hc B hB _
  · have hkl : eL.symm i ≠ eL.symm j := fun h => hij (eL.symm.injective h)
    obtain ⟨q, hq⟩ := card_eq_one.1 (meet_line c hc B hB hmeet _ _ hkl)
    have hqmem : q ∈ line c B (eL.symm i) ∩ line c B (eL.symm j) := by
      rw [hq]
      exact mem_singleton_self q
    refine ⟨eP q, ?_, ?_⟩
    · simp only [mem_map_equiv, Equiv.symm_apply_apply]
      exact mem_inter.1 hqmem
    · rintro p ⟨hp1, hp2⟩
      rw [mem_map_equiv] at hp1 hp2
      have hp : eP.symm p ∈ line c B (eL.symm i) ∩ line c B (eL.symm j) := mem_inter.2 ⟨hp1, hp2⟩
      rw [hq, mem_singleton] at hp
      rw [← hp, Equiv.apply_symm_apply]

end OMA.Seed139

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_eq_12_R3_H2_R1.H1 := by
  intro s B c rows cols hB hmeet
  exact OMA.Seed139.seed c (OMA.Seed139.pair_inj s rows cols) B hB hmeet
