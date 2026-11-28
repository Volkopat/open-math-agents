import FormalConjectures.ErdosProblems.«340»

-- Problem: Erdős Problem 340 — third
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/340.lean (declaration Erdos340.erdos_340.variants.third)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
The greedy Sidon sequence `g` satisfies `g c ≤ (c + 1) ^ 3 + (c + 1) ^ 2 + 1`: every integer in
`[1, g c)` outside `A c` is rejected by `A c`, hence by `Set.IsSidon.insert` equals either
`(a + b) / 2` or `b + k - a` for elements of `A c`. Since `A c` has size `c + 1` and lies in
`Set.range g ∩ [1, g c]`, the counting function `c` up to `n` satisfies `n < g c` and
`n ≤ (3 * c) ^ 3`.
-/

open Filter Asymptotics Finset in
theorem OMA.solution : type_of% @Erdos340.erdos_340.variants.third := by
  let A (k : ℕ) : Finset ℕ := (greedySidon.aux k).1.1
  let g := greedySidon
  have hinv (k : ℕ) :
      g k ∈ A k ∧ (A k).card = k + 1 ∧ (A k : Set ℕ) ⊆ Set.range g ∧
      (∀ a ∈ A k, 1 ≤ a ∧ a ≤ g k) ∧
      ∀ x, 1 ≤ x → x < g k → x ∉ A k → ¬ IsSidon ((A k : Set ℕ) ∪ {x}) := by
    induction k with
    | zero =>
      simp [A, g, greedySidon, greedySidon.aux]
      exact ⟨⟨0, rfl⟩, fun _ _ _ => by omega⟩
    | succ k ih =>
      obtain ⟨hmem, hcard, hsub, hbnd, hrej⟩ := ih
      have hne : (A k).Nonempty := ⟨g k, hmem⟩
      have hmax : (A k).max' hne = g k :=
        le_antisymm (max'_le _ _ _ fun a ha => (hbnd a ha).2) (le_max' _ _ hmem)
      have hA : A (k + 1) = A k ∪ {g (k + 1)} := rfl
      let s := greedySidon.go (A k) (greedySidon.aux k).1.2 (g k + 1)
      have hg : g (k + 1) = s.1 := by
        change (greedySidon.go _ _
          (if h : (A k).Nonempty then (A k).max' h + 1 else g k)).1 = _
        rw [dif_pos hne, hmax]
      have hgo := s.2
      rw [← hg] at hgo
      refine ⟨by rw [hA]; simp,
        by rw [hA, card_union_of_disjoint (disjoint_singleton_right.2 hgo.2.1), hcard,
            card_singleton],
        by simp [hA, Set.insert_subset_iff, hsub],
        fun a ha => by
          have := hbnd _ hmem
          rw [hA, mem_union, mem_singleton] at ha
          rcases ha with ha | rfl
          · have := hbnd a ha; omega
          · omega,
        fun x hx1 hlt hnx hS => ?_⟩
      have hnx' : x ∉ A k := fun h => hnx (by rw [hA]; exact mem_union_left _ h)
      have hS' : IsSidon ((A k : Set ℕ) ∪ {x}) :=
        Set.IsSidon.subset hS (Set.union_subset_union_left _ (by simp [hA]))
      rcases lt_or_ge x (g k) with h | h
      · exact hrej x hx1 h hnx' hS'
      · have hlt' : g k + 1 ≤ x := lt_of_le_of_ne h fun he => hnx' (he ▸ hmem)
        simp only [hg, s, greedySidon.go, dif_pos hne] at hlt
        exact Nat.find_min _ hlt ⟨hlt', hnx', by simpa using hS'⟩
  intro _ _
  refine IsBigO.of_bound 3 (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  set c := (Set.range g ∩ Set.Icc 1 n).ncard with hc
  obtain ⟨_, hcard, hsubg, hbnd, hrej⟩ := hinv c
  have hlt : n < g c := by
    by_contra! hle
    have hsub : (A c : Set ℕ) ⊆ Set.range g ∩ Set.Icc 1 n := fun a ha =>
      ⟨hsubg ha, (hbnd a ha).1, (hbnd a ha).2.trans hle⟩
    have := Set.ncard_le_ncard hsub ((Set.finite_Icc 1 n).subset Set.inter_subset_right)
    rw [Set.ncard_coe_finset, hcard, ← hc] at this
    omega
  have h1 : n ≤ (c + 1) * ((c + 1) * (c + 1)) + (c + 1) * (c + 1) := by
    let B := A c
    have hsub : Icc 1 n ⊆ (B ×ˢ B ×ˢ B).image (fun t => t.2.1 + t.2.2 - t.1) ∪
        (B ×ˢ B).image (fun t => (t.1 + t.2) / 2) := by
      intro x hx
      rw [mem_Icc] at hx
      simp only [mem_union, mem_image, mem_product, Prod.exists]
      by_cases hxB : x ∈ B
      · exact .inr ⟨x, x, ⟨hxB, hxB⟩, by omega⟩
      · have hns := hrej x hx.1 (by omega) hxB
        rw [Set.IsSidon.insert (greedySidon.aux c).1.2] at hns
        push Not at hns
        obtain ⟨_, a, ha, b, hb, h⟩ := hns
        by_cases h2 : x + x = a + b
        · exact .inr ⟨a, b, ⟨ha, hb⟩, by omega⟩
        · obtain ⟨k, hk, h3⟩ := h h2
          exact .inl ⟨a, b, k, ⟨ha, hb, hk⟩, by omega⟩
    have hle := (card_le_card hsub).trans ((card_union_le _ _).trans
      (add_le_add card_image_le card_image_le))
    simpa [B, Nat.card_Icc, card_product, hcard] using hle
  rcases hc0 : c with _ | d
  · simp [hc0, g, greedySidon, greedySidon.aux] at hlt; omega
  have hnat : n ≤ (3 * (d + 1)) ^ 3 := by
    rw [hc0] at h1
    ring_nf at h1 ⊢
    omega
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_div,
    Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by norm_num),
    show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  exact_mod_cast hnat
