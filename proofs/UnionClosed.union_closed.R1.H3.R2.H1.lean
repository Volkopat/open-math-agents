import OMAReductions.R_UnionClosed_union_closed_R1_H3_R2

-- Step UnionClosed.union_closed.R1.H3.R2.H1: hypothesis H1 of reduction
-- UnionClosed.union_closed.R1.H3.R2
-- Credit: @Ezekia1
-- Let X0 be a nonempty member whose upper corner has the smallest coordinate sum, and let p be the
-- element at that corner. If a member Y misses p then, because the union of X0 and Y is a box,
-- Y agrees with X0 in every coordinate but one, where it starts right after X0 ends. Two such
-- members with different exceptional coordinates would have a union that is not a box, so the
-- lower corner q of one of them lies in all of them. Hence every nonempty member contains p or q,
-- and union closure gives that p or q lies in at least half of the members.

namespace OMA.UCBox

open Finset

/-- Every point of the bounding box of two boxes lies in one of the two boxes. -/
def Hull {d : ℕ} (l1 h1 l2 h2 : Fin d → ℤ) : Prop :=
  ∀ z : Fin d → ℤ, (∀ k, (l1 k ≤ z k ∨ l2 k ≤ z k) ∧ (z k ≤ h1 k ∨ z k ≤ h2 k)) →
    ((∀ k, l1 k ≤ z k ∧ z k ≤ h1 k) ∨ (∀ k, l2 k ≤ z k ∧ z k ≤ h2 k))

theorem hull {d : ℕ} (l1 h1 l2 h2 l3 h3 : Fin d → ℤ)
    (n1 : ∀ k, l1 k ≤ h1 k) (n2 : ∀ k, l2 k ≤ h2 k)
    (hU : ∀ z : Fin d → ℤ, (∀ k, l3 k ≤ z k ∧ z k ≤ h3 k) ↔
      ((∀ k, l1 k ≤ z k ∧ z k ≤ h1 k) ∨ (∀ k, l2 k ≤ z k ∧ z k ≤ h2 k))) :
    Hull l1 h1 l2 h2 := by
  have a1 := (hU l1).mpr (Or.inl fun k => ⟨le_refl _, n1 k⟩)
  have a2 := (hU h1).mpr (Or.inl fun k => ⟨n1 k, le_refl _⟩)
  have b1 := (hU l2).mpr (Or.inr fun k => ⟨le_refl _, n2 k⟩)
  have b2 := (hU h2).mpr (Or.inr fun k => ⟨n2 k, le_refl _⟩)
  intro z hz
  refine (hU z).mp fun k => ⟨?_, ?_⟩
  · rcases (hz k).1 with h | h
    · exact le_trans (a1 k).1 h
    · exact le_trans (b1 k).1 h
  · rcases (hz k).2 with h | h
    · exact le_trans h (a2 k).2
    · exact le_trans h (b2 k).2

/-- Test point that differs from the upper corner of the first box in one coordinate. -/
theorem one {d : ℕ} {l1 h1 l2 h2 : Fin d → ℤ} (H : Hull l1 h1 l2 h2) (n1 : ∀ k, l1 k ≤ h1 k)
    (j : Fin d) (a : ℤ) (ha : (l1 j ≤ a ∨ l2 j ≤ a) ∧ (a ≤ h1 j ∨ a ≤ h2 j)) :
    (l1 j ≤ a ∧ a ≤ h1 j) ∨ (l2 j ≤ a ∧ a ≤ h2 j) := by
  have hz := H (fun i => if i = j then a else h1 i) (fun i => by
    by_cases hij : i = j
    · simpa [hij] using ha
    · simp [hij, n1 i])
  rcases hz with h | h
  · exact Or.inl (by simpa using h j)
  · exact Or.inr (by simpa using h j)

/-- Test point that differs from the upper corner of the first box in two coordinates. -/
theorem two {d : ℕ} {l1 h1 l2 h2 : Fin d → ℤ} (H : Hull l1 h1 l2 h2) (n1 : ∀ k, l1 k ≤ h1 k)
    (j k : Fin d) (hjk : j ≠ k) (a b : ℤ)
    (ha : (l1 j ≤ a ∨ l2 j ≤ a) ∧ (a ≤ h1 j ∨ a ≤ h2 j))
    (hb : (l1 k ≤ b ∨ l2 k ≤ b) ∧ (b ≤ h1 k ∨ b ≤ h2 k)) :
    (l1 j ≤ a ∧ a ≤ h1 j ∧ l1 k ≤ b ∧ b ≤ h1 k) ∨
      (l2 j ≤ a ∧ a ≤ h2 j ∧ l2 k ≤ b ∧ b ≤ h2 k) := by
  have hkj : k ≠ j := fun h => hjk h.symm
  have hz := H (fun i => if i = j then a else if i = k then b else h1 i) (fun i => by
    by_cases hij : i = j
    · simpa [hij] using ha
    · by_cases hik : i = k
      · simpa [hik, hkj] using hb
      · simp [hij, hik, n1 i])
  rcases hz with h | h
  · have hj : l1 j ≤ a ∧ a ≤ h1 j := by simpa using h j
    have hk : l1 k ≤ b ∧ b ≤ h1 k := by simpa [hkj] using h k
    exact Or.inl ⟨hj.1, hj.2, hk.1, hk.2⟩
  · have hj : l2 j ≤ a ∧ a ≤ h2 j := by simpa using h j
    have hk : l2 k ≤ b ∧ b ≤ h2 k := by simpa [hkj] using h k
    exact Or.inr ⟨hj.1, hj.2, hk.1, hk.2⟩

/-- If the second box misses the upper corner of the first and its own upper corner does not have
a smaller coordinate sum, it is the first box moved along one coordinate. -/
theorem shape {d : ℕ} {l1 h1 l2 h2 : Fin d → ℤ} (H : Hull l1 h1 l2 h2)
    (n1 : ∀ k, l1 k ≤ h1 k) (n2 : ∀ k, l2 k ≤ h2 k)
    (hsum : ∑ k, h1 k ≤ ∑ k, h2 k)
    (hu : ¬ ∀ k, l2 k ≤ h1 k ∧ h1 k ≤ h2 k) :
    ∃ j, h1 j + 1 = l2 j ∧ ∀ k, k ≠ j → l2 k = l1 k ∧ h2 k = h1 k := by
  obtain ⟨j, hj⟩ := not_forall.mp hu
  have n1j := n1 j
  have n2j := n2 j
  by_cases hα : h2 j < h1 j
  · exfalso
    have hex : ∃ k, h1 k < h2 k := by
      by_contra hno
      have hall : ∀ k, h2 k ≤ h1 k := fun k => not_lt.mp (fun h => hno ⟨k, h⟩)
      have hlt : ∑ k, h2 k < ∑ k, h1 k :=
        Finset.sum_lt_sum (fun k _ => hall k) ⟨j, Finset.mem_univ j, hα⟩
      exact absurd hlt (not_lt.mpr hsum)
    obtain ⟨k, hk⟩ := hex
    have hjk : j ≠ k := by
      rintro rfl
      omega
    have n2k := n2 k
    have t := two H n1 j k hjk (h1 j) (h2 k) ⟨Or.inl n1j, Or.inl le_rfl⟩
      ⟨Or.inr n2k, Or.inr le_rfl⟩
    omega
  · have hβ : h1 j < l2 j := by
      by_contra h
      exact hj ⟨not_lt.mp h, not_lt.mp hα⟩
    refine ⟨j, ?_, ?_⟩
    · have t := one H n1 j (h1 j + 1) ⟨Or.inl (by omega), Or.inr (by omega)⟩
      omega
    · intro k hk
      have hjk : j ≠ k := fun h => hk h.symm
      have n1k := n1 k
      have n2k := n2 k
      have t1 := two H n1 j k hjk (h1 j) (h2 k) ⟨Or.inl n1j, Or.inl le_rfl⟩
        ⟨Or.inr n2k, Or.inr le_rfl⟩
      have t2 := two H n1 j k hjk (h1 j) (l2 k) ⟨Or.inl n1j, Or.inl le_rfl⟩
        ⟨Or.inr le_rfl, Or.inr n2k⟩
      have t3 := two H n1 j k hjk (l2 j) (h1 k) ⟨Or.inr le_rfl, Or.inr n2j⟩
        ⟨Or.inl n1k, Or.inl le_rfl⟩
      have t4 := two H n1 j k hjk (l2 j) (l1 k) ⟨Or.inr le_rfl, Or.inr n2j⟩
        ⟨Or.inl le_rfl, Or.inl n1k⟩
      omega

/-- If two elements together meet every nonempty member of a union-closed family, one of them
lies in at least half of the members. -/
theorem count {m : ℕ} (A : Finset (Finset (Fin m))) (hU : UnionClosed.IsUnionClosed A)
    (p q : Fin m) (X0 : Finset (Fin m)) (hX0 : X0 ∈ A) (hX0n : X0.Nonempty)
    (cover : ∀ Y ∈ A, Y.Nonempty → p ∈ Y ∨ q ∈ Y) :
    A.card ≤ 2 * (A.filter (fun X => p ∈ X)).card ∨
      A.card ≤ 2 * (A.filter (fun X => q ∈ X)).card := by
  have hin : ∀ Y ∈ A, Y.Nonempty →
      Y ∈ A.filter (fun X => p ∈ X) ∪ A.filter (fun X => q ∈ X) := by
    intro Y hY h
    rcases cover Y hY h with hp | hq
    · exact mem_union_left _ (mem_filter.mpr ⟨hY, hp⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hY, hq⟩)
  have hsub : A ⊆ insert ∅ (A.filter (fun X => p ∈ X) ∪ A.filter (fun X => q ∈ X)) := by
    intro Y hY
    rcases Finset.eq_empty_or_nonempty Y with h | h
    · rw [h]
      exact mem_insert_self _ _
    · exact mem_insert_of_mem (hin Y hY h)
  have h1 : A.card ≤ (A.filter (fun X => p ∈ X) ∪ A.filter (fun X => q ∈ X)).card + 1 :=
    (card_le_card hsub).trans (card_insert_le _ _)
  have h2 := card_union_add_card_inter (A.filter (fun X => p ∈ X)) (A.filter (fun X => q ∈ X))
  have hX0PQ := hin X0 hX0 hX0n
  by_cases hI : (A.filter (fun X => p ∈ X) ∩ A.filter (fun X => q ∈ X)).Nonempty
  · have h3 := card_pos.mpr hI
    omega
  · rw [not_nonempty_iff_eq_empty] at hI
    have h3 : (A.filter (fun X => p ∈ X) ∩ A.filter (fun X => q ∈ X)).card = 0 := by
      rw [hI]
      exact card_empty
    by_cases hQ : (A.filter (fun X => q ∈ X)).Nonempty
    · have hP : A.filter (fun X => p ∈ X) = ∅ := by
        by_contra hne
        obtain ⟨X, hX⟩ := nonempty_iff_ne_empty.mpr hne
        obtain ⟨Y, hY⟩ := hQ
        have hXA := mem_filter.mp hX
        have hYA := mem_filter.mp hY
        have hXY : X ∪ Y ∈ A := hU X hXA.1 Y hYA.1
        have hmem : X ∪ Y ∈ A.filter (fun X => p ∈ X) ∩ A.filter (fun X => q ∈ X) :=
          mem_inter.mpr ⟨mem_filter.mpr ⟨hXY, mem_union_left _ hXA.2⟩,
            mem_filter.mpr ⟨hXY, mem_union_right _ hYA.2⟩⟩
        rw [hI] at hmem
        exact absurd hmem (notMem_empty _)
      have h4 : (A.filter (fun X => p ∈ X)).card = 0 := by
        rw [hP]
        exact card_empty
      have h5 := card_pos.mpr hQ
      omega
    · rw [not_nonempty_iff_eq_empty] at hQ
      have h4 : (A.filter (fun X => q ∈ X)).card = 0 := by
        rw [hQ]
        exact card_empty
      have h5 : 0 < (A.filter (fun X => p ∈ X)).card := by
        refine card_pos.mpr ⟨X0, ?_⟩
        rcases mem_union.mp hX0PQ with h | h
        · exact h
        · rw [hQ] at h
          exact absurd h (notMem_empty _)
      omega

end OMA.UCBox

open OMA.UCBox Finset in
theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1_H3_R2.H1 := by
  intro m d A e hU hne hbox
  choose! lo hi hb using hbox
  have nb : ∀ X ∈ A, X.Nonempty → ∀ k, lo X k ≤ hi X k := by
    intro X hX hXn k
    obtain ⟨x, hx⟩ := hXn
    have h := (hb X hX ⟨x, hx⟩ (e x)).mp ⟨x, hx, rfl⟩
    exact le_trans (h k).1 (h k).2
  have mem_iff : ∀ X ∈ A, X.Nonempty → ∀ x : Fin m,
      x ∈ X ↔ ∀ k, lo X k ≤ e x k ∧ e x k ≤ hi X k := by
    intro X hX hXn x
    constructor
    · intro hx
      exact (hb X hX hXn (e x)).mp ⟨x, hx, rfl⟩
    · intro h
      obtain ⟨y, hy, hye⟩ := (hb X hX hXn (e x)).mpr h
      rw [← e.injective hye]
      exact hy
  have hullA : ∀ Y1 ∈ A, Y1.Nonempty → ∀ Y2 ∈ A, Y2.Nonempty →
      Hull (lo Y1) (hi Y1) (lo Y2) (hi Y2) := by
    intro Y1 h1 n1 Y2 h2 n2
    have h3 : Y1 ∪ Y2 ∈ A := hU Y1 h1 Y2 h2
    have n3 : (Y1 ∪ Y2).Nonempty := n1.mono subset_union_left
    refine hull (lo Y1) (hi Y1) (lo Y2) (hi Y2) (lo (Y1 ∪ Y2)) (hi (Y1 ∪ Y2))
      (nb Y1 h1 n1) (nb Y2 h2 n2) ?_
    intro z
    rw [← hb (Y1 ∪ Y2) h3 n3 z, ← hb Y1 h1 n1 z, ← hb Y2 h2 n2 z]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases mem_union.mp hx with h | h
      · exact Or.inl ⟨x, h, rfl⟩
      · exact Or.inr ⟨x, h, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨x, mem_union_left _ hx, rfl⟩
      · exact ⟨x, mem_union_right _ hx, rfl⟩
  obtain ⟨X, hXA, hXne⟩ := hne
  have hXn : X.Nonempty := nonempty_iff_ne_empty.mpr hXne
  obtain ⟨X0, hX0f, hmin⟩ := exists_min_image (A.filter (fun Y => Y.Nonempty))
    (fun Y => ∑ k, hi Y k) ⟨X, mem_filter.mpr ⟨hXA, hXn⟩⟩
  obtain ⟨hX0, hX0n⟩ := mem_filter.mp hX0f
  obtain ⟨p, hp0, hpe⟩ := (hb X0 hX0 hX0n (hi X0)).mpr
    (fun k => ⟨nb X0 hX0 hX0n k, le_rfl⟩)
  have S : ∀ Y ∈ A, Y.Nonempty → p ∉ Y →
      ∃ j, hi X0 j + 1 = lo Y j ∧ ∀ k, k ≠ j → lo Y k = lo X0 k ∧ hi Y k = hi X0 k := by
    intro Y hY hYn hpY
    refine shape (hullA X0 hX0 hX0n Y hY hYn) (nb X0 hX0 hX0n) (nb Y hY hYn)
      (hmin Y (mem_filter.mpr ⟨hY, hYn⟩)) ?_
    intro h
    apply hpY
    rw [mem_iff Y hY hYn p, hpe]
    exact h
  have cover : ∃ q : Fin m, ∀ Y ∈ A, Y.Nonempty → p ∈ Y ∨ q ∈ Y := by
    by_cases hex : ∃ Y ∈ A, Y.Nonempty ∧ p ∉ Y
    · obtain ⟨Y1, hY1, hY1n, hpY1⟩ := hex
      obtain ⟨j1, hj1, hk1⟩ := S Y1 hY1 hY1n hpY1
      obtain ⟨q, hq1, hqe⟩ := (hb Y1 hY1 hY1n (lo Y1)).mpr
        (fun k => ⟨le_rfl, nb Y1 hY1 hY1n k⟩)
      refine ⟨q, fun Y hY hYn => ?_⟩
      by_cases hpY : p ∈ Y
      · exact Or.inl hpY
      · right
        obtain ⟨j2, hj2, hk2⟩ := S Y hY hYn hpY
        by_cases hjj : j1 = j2
        · rw [mem_iff Y hY hYn q, hqe]
          intro k
          have nk := nb Y hY hYn k
          by_cases hk : k = j1
          · rw [hk]
            rw [hk] at nk
            rw [← hjj] at hj2
            omega
          · have a := hk1 k hk
            have b := hk2 k (fun h => hk (h.trans hjj.symm))
            omega
        · exfalso
          have hz : ∀ k, (lo Y1 k ≤ hi X0 k ∨ lo Y k ≤ hi X0 k) ∧
              (hi X0 k ≤ hi Y1 k ∨ hi X0 k ≤ hi Y k) := by
            intro k
            have n0 := nb X0 hX0 hX0n k
            by_cases hk : k = j1
            · have b := hk2 k (fun h => hjj (hk.symm.trans h))
              omega
            · have a := hk1 k hk
              omega
          rcases hullA Y1 hY1 hY1n Y hY hYn (hi X0) hz with h | h
          · exact hpY1 ((mem_iff Y1 hY1 hY1n p).mpr (by rw [hpe]; exact h))
          · exact hpY ((mem_iff Y hY hYn p).mpr (by rw [hpe]; exact h))
    · refine ⟨p, fun Y hY hYn => Or.inl ?_⟩
      by_contra h
      exact hex ⟨Y, hY, hYn, h⟩
  obtain ⟨q, hq⟩ := cover
  rcases count A hU p q X0 hX0 hX0n hq with h | h
  · refine ⟨p, ?_⟩
    have h' : (A.card : ℚ) ≤ 2 * ((A.filter (fun X => p ∈ X)).card : ℚ) := by exact_mod_cast h
    linarith
  · refine ⟨q, ?_⟩
    have h' : (A.card : ℚ) ≤ 2 * ((A.filter (fun X => q ∈ X)).card : ℚ) := by exact_mod_cast h
    linarith
