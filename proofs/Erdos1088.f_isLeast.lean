import FormalConjectures.ErdosProblems.«1088»

/-! Proof of Erdos1088.f_isLeast via 4-uniform Ramsey and orthogonal vectors. -/

open Finset
open scoped RealInnerProductSpace EuclideanGeometry

private lemma ramsey {α C : Type*} [LinearOrder α] [Fintype C] [Nonempty C] :
    ∀ r k, ∃ N, ∀ s : Finset α, N ≤ s.card → ∀ f : (Fin r → α) → C,
      ∃ t ⊆ s, k ≤ t.card ∧ ∃ c, ∀ v : Fin r → α, StrictMono v → (∀ i, v i ∈ t) → f v = c := by
  classical
  intro r
  induction r with
  | zero =>
    exact fun k => ⟨k, fun s hs f =>
      ⟨s, Subset.rfl, hs, f Fin.elim0, fun v _ _ => congrArg f (Subsingleton.elim v _)⟩⟩
  | succ r ih =>
    have step : ∀ M, ∃ N, ∀ s : Finset α, N ≤ s.card → ∀ f : (Fin (r + 1) → α) → C,
        ∃ u ⊆ s, M ≤ u.card ∧ ∃ g : α → C,
          ∀ v : Fin (r + 1) → α, StrictMono v → (∀ i, v i ∈ u) → f v = g (v 0) := by
      intro M
      induction M with
      | zero => exact ⟨0, fun _ _ _ => ⟨∅, by simp, le_rfl, fun _ => Classical.arbitrary C, fun _ _ hv => by cases hv 0⟩⟩
      | succ M ihM =>
        obtain ⟨N₁, hN₁⟩ := ihM
        obtain ⟨N₂, hN₂⟩ := ih N₁
        refine ⟨N₂ + 1, fun s hs f => ?_⟩
        have hne : s.Nonempty := card_pos.mp (by omega)
        set x := s.min' hne
        have hx := min'_mem s hne
        obtain ⟨s₁, hs₁, hs₁c, c₀, hc₀⟩ :=
          hN₂ (s.erase x) (by rw [card_erase_of_mem hx]; omega) (fun w => f (Fin.cons x w))
        obtain ⟨u₁, hu₁, hu₁c, g₁, hg₁⟩ := hN₁ s₁ hs₁c f
        have hxlt {y} (hy : y ∈ u₁) : x < y := s.min'_lt_of_mem_erase_min' hne (hs₁ (hu₁ hy))
        refine ⟨insert x u₁, insert_subset hx (hu₁.trans (hs₁.trans (erase_subset x s))),
          by rw [card_insert_of_notMem (fun h => lt_irrefl x (hxlt h))]; omega,
          fun z => if z = x then c₀ else g₁ z, fun v hv hvu => ?_⟩
        dsimp only
        rcases mem_insert.mp (hvu 0) with h0 | h0
        · rw [if_pos h0, ← Fin.cons_self_tail v, h0]
          exact hc₀ _ (hv.comp Fin.strictMono_succ) (fun i =>
            hu₁ ((mem_insert.mp (hvu i.succ)).resolve_left (h0 ▸ (hv (Fin.succ_pos i)).ne')))
        · rw [if_neg (hxlt h0).ne']
          exact hg₁ v hv (fun i => (mem_insert.mp (hvu i)).resolve_left
            (lt_of_lt_of_le (hxlt h0) (hv.monotone (Fin.zero_le i))).ne')
    intro k
    obtain ⟨N, hN⟩ := step (Fintype.card C * k)
    refine ⟨N, fun s hs f => ?_⟩
    obtain ⟨u, hus, hu, g, hg⟩ := hN s hs f
    obtain ⟨c, -, hc⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to (s := u) (f := g) (n := k)
      (fun _ _ => mem_univ _) univ_nonempty (by rwa [card_univ])
    exact ⟨u.filter (g · = c), (filter_subset _ u).trans hus, hc, c, fun v hv hvt => by
      rw [hg v hv (fun i => filter_subset _ u (hvt i)), (mem_filter.mp (hvt 0)).2]⟩

private lemma no_pattern {d : ℕ} {z : Fin (4 * d + 8) → ℝ^d} (hz : Function.Injective z)
    {a b c g : Fin 4} (hab : a < b) (hcg : c < g) (hne : b = g → a ≠ c)
    (hdist : ∀ φ : Fin 4 → Fin (4 * d + 8), StrictMono φ →
      dist (z (φ a)) (z (φ b)) = dist (z (φ c)) (z (φ g))) : False := by
  wlog hne_bg : b ≠ g generalizing z a b c g
  · obtain rfl : b = g := not_ne_iff.mp hne_bg
    have hac := Fin.rev_injective.ne (hne rfl)
    exact this (hz.comp Fin.rev_injective) (Fin.rev_lt_rev.mpr hab) (Fin.rev_lt_rev.mpr hcg)
      (absurd · hac) (fun φ hφ => by
        dsimp; rw [dist_comm, dist_comm (z (φ b.rev).rev)]
        exact hdist (fun t => (φ t.rev).rev) (fun _ _ ht => Fin.rev_lt_rev.mpr (hφ (Fin.rev_lt_rev.mpr ht)))) hac
  wlog hbg : b < g generalizing a b c g
  · exact this hcg hab (fun h => absurd h.symm hne_bg) (fun φ hφ => (hdist φ hφ).symm)
      hne_bg.symm (lt_of_le_of_ne (not_lt.mp hbg) hne_bg.symm)
  have hconst (p q : ℕ) (h : 3 ≤ p ∧ p + 3 ≤ q ∧ q ≤ 4 * d + 4) :
      ‖z ⟨p, by omega⟩ - z ⟨q, by omega⟩‖ ^ 2 =
        ‖z ⟨p + a.1 - c.1, by omega⟩ - z ⟨p + b.1 - c.1, by omega⟩‖ ^ 2 := by
    have hφ := congrArg (· ^ 2) (hdist
      (fun t => ⟨if t < g then p + t.1 - c.1 else if t = g then q else 4 * d + 7, by split_ifs <;> omega⟩)
      (fun _ _ ht => by simp only [Fin.lt_def]; split_ifs <;> omega)).symm
    simpa only [hab.trans hbg, hbg, hcg, lt_irrefl, ↓reduceIte, Nat.add_sub_cancel, dist_eq_norm] using hφ
  let w : Fin (d + 1) → ℝ^d := fun r => z ⟨4 * r.1 + 4, by omega⟩ - z ⟨4 * r.1 + 3, by omega⟩
  have := (linearIndependent_of_ne_zero_of_inner_eq_zero (v := w)
    (fun r hr => by have := Fin.mk.inj (hz (sub_eq_zero.mp hr)); omega) (by
      intro r s hrs
      wlog h : r < s generalizing r s
      · rw [real_inner_comm]; exact this hrs.symm (lt_of_le_of_ne (not_lt.mp h) hrs.symm)
      have heq (p : ℕ) (hp : 3 ≤ p ∧ p + 3 ≤ 4 * s.1 + 3) :=
        (hconst p (4 * s.1 + 3) (by omega)).trans (hconst p (4 * s.1 + 4) (by omega)).symm
      have h1 := heq (4 * r.1 + 3) (by omega)
      have h2 := heq (4 * r.1 + 4) (by omega)
      simp only [norm_sub_sq_real] at h1 h2
      simp only [w, inner_sub_left, inner_sub_right]
      linarith)).fintype_card_le_finrank
  simp at this

theorem OMA.solution : type_of% @Erdos1088.f_isLeast := by
  intro d n
  suffices hne : (Erdos1088.cardSet d n).Nonempty from
    ⟨Nat.sInf_mem hne, fun _ => Nat.sInf_le⟩
  classical
  let : LinearOrder (ℝ^d) := linearOrderOfSTO WellOrderingRel
  obtain ⟨N, hN⟩ := ramsey (α := ℝ^d) (C := Fin 4 × Fin 4 × Fin 4 × Fin 4 → Bool) 4 (max n (4 * d + 8))
  refine ⟨max n N, le_max_left _ _, fun S hS => ?_⟩
  obtain ⟨t, hts, ht, _, hcol⟩ := hN S (by omega)
    (fun v q => decide (dist (v q.1) (v q.2.1) = dist (v q.2.2.1) (v q.2.2.2)))
  obtain ⟨u, hut, huc⟩ := exists_subset_card_eq (show n ≤ t.card by omega)
  refine ⟨u, hut.trans hts, huc, ?_⟩
  rw [Erdos1088.PairwiseDistancesDistinct, distinctDistances, ← Sym2.card_image_offDiag,
    show distanceSet u = (u.offDiag.image (Function.uncurry Sym2.mk)).image (Sym2.lift ⟨dist, dist_comm⟩)
      by rw [distanceSet, image_image]; rfl,
    card_image_of_injOn]
  intro p₁ hp₁ p₂ hp₂ hdeq
  simp only [mem_coe, mem_image, mem_offDiag, Prod.exists, Function.uncurry] at hp₁ hp₂
  rcases hp₁ with ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩
  rcases hp₂ with ⟨c, g, ⟨hc, hg, hcg⟩, rfl⟩
  dsimp only [Sym2.lift_mk] at hdeq
  wlog h1 : a < b generalizing a b
  · exact Sym2.eq_swap.trans (this b a hb ha hab.symm (by rwa [dist_comm]) (lt_of_le_of_ne (not_lt.mp h1) hab.symm))
  wlog h2 : c < g generalizing c g
  · exact (this g c hg hc hcg.symm (by rwa [dist_comm g]) (lt_of_le_of_ne (not_lt.mp h2) hcg.symm)).trans Sym2.eq_swap
  by_contra hne
  let v := univ.image ![a, b, c, g]
  have hvt : v ⊆ t := image_subset_iff.mpr fun i _ => by fin_cases i <;> exact hut ‹_›
  obtain ⟨e, hve, het, he⟩ := exists_subsuperset_card_eq (n := 4) hvt (card_image_le.trans (by simp)) (by omega)
  let φ := e.orderIsoOfFin he
  have hm (k : Fin 4) : ![a, b, c, g] k ∈ e := hve (mem_image_of_mem _ (mem_univ k))
  obtain ⟨t', ht', ht'c⟩ := exists_subset_card_eq (show 4 * d + 8 ≤ t.card by omega)
  let ψ := t'.orderEmbOfFin ht'c
  exact no_pattern ψ.injective (φ.symm.lt_iff_lt.mpr h1) (φ.symm.lt_iff_lt.mpr h2)
    (fun hbg hac => hne (by simp [Subtype.ext_iff] at hbg hac; rw [hac, hbg])) fun ρ hρ =>
    of_decide_eq_true ((congrFun ((hcol (ψ ∘ ρ) (ψ.strictMono.comp hρ)
      (fun _ => ht' (t'.orderEmbOfFin_mem ht'c _))).trans
      (hcol (fun i => (φ i : ℝ^d)) (fun _ _ h => φ.strictMono h) (fun i => het (φ i).2)).symm)
      (φ.symm ⟨a, hm 0⟩, φ.symm ⟨b, hm 1⟩, φ.symm ⟨c, hm 2⟩, φ.symm ⟨g, hm 3⟩)).trans
      (decide_eq_true (by simpa using hdeq)))
