import OMAReductions.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1_H2_R1


namespace E877Removal

open Finset SimpleGraph
open scoped Classical

/-- Ordered Schur triples `(a, b)` with `a ∈ A`, `b ∈ A`, `a + b ∈ A`. -/
def schurTriples (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun p => p.1 + p.2 ∈ A)

/-- Tripartite Cayley graph on `Fin 3 × ZMod M` from `A ⊆ [1, n]` where `M = 2*n + 1`. -/
def cayleyGraph (M : ℕ) (A : Finset ℕ) : SimpleGraph (Fin 3 × ZMod M) where
  Adj u v :=
    (u.1 = 0 ∧ v.1 = 1 ∧ ∃ a ∈ A, v.2 - u.2 = (a : ZMod M)) ∨
    (u.1 = 1 ∧ v.1 = 0 ∧ ∃ a ∈ A, u.2 - v.2 = (a : ZMod M)) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ ∃ b ∈ A, v.2 - u.2 = (b : ZMod M)) ∨
    (u.1 = 2 ∧ v.1 = 1 ∧ ∃ b ∈ A, u.2 - v.2 = (b : ZMod M)) ∨
    (u.1 = 0 ∧ v.1 = 2 ∧ ∃ c ∈ A, v.2 - u.2 = (c : ZMod M)) ∨
    (u.1 = 2 ∧ v.1 = 0 ∧ ∃ c ∈ A, u.2 - v.2 = (c : ZMod M))
  symm := ⟨fun u v h => by
    rcases h with h | h | h | h | h | h
    · exact Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)
    · exact Or.inl ⟨h.2.1, h.1, h.2.2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩))))⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
    omega⟩

lemma natCast_zmod_inj {M a b : ℕ} (ha : a < M) (hb : b < M) (h : (a : ZMod M) = (b : ZMod M)) :
    a = b := by
  have h1 := (ZMod.natCast_eq_natCast_iff' a b M).mp h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1

/-- Every 3-clique of `cayleyGraph (2*n+1) A` corresponds to a triple `(x, a, b)` with
`x : ZMod (2*n+1)` and `(a, b) ∈ schurTriples A`. -/
lemma card_cliqueFinset_cayleyGraph_le {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n) :
    ((cayleyGraph (2 * n + 1) A).cliqueFinset 3).card ≤ (2 * n + 1) * (schurTriples A).card := by
  set M := 2 * n + 1 with hM_def
  haveI : NeZero M := ⟨by omega⟩
  let f : ZMod M × (ℕ × ℕ) → Finset (Fin 3 × ZMod M) :=
    fun p => {(0, p.1), (1, p.1 + (p.2.1 : ZMod M)), (2, p.1 + (p.2.1 : ZMod M) + (p.2.2 : ZMod M))}
  have hsub : (cayleyGraph M A).cliqueFinset 3 ⊆
      (Finset.univ ×ˢ schurTriples A).image f := by
    intro t ht
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.mp hcard
    have hadj_uv : (cayleyGraph M A).Adj u v := hcl (by simp) (by simp) huv
    have hadj_uw : (cayleyGraph M A).Adj u w := hcl (by simp) (by simp) huw
    have hadj_vw : (cayleyGraph M A).Adj v w := hcl (by simp) (by simp) hvw
    -- Each pair has distinct first coordinates in `Fin 3`, so `{u.1, v.1, w.1} = {0, 1, 2}`
    have hne : ∀ x y : Fin 3 × ZMod M, (cayleyGraph M A).Adj x y → x.1 ≠ y.1 := by
      intro x y h
      dsimp only [cayleyGraph] at h
      rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
      omega
    have h1 : u.1 ≠ v.1 := hne u v hadj_uv
    have h2 : u.1 ≠ w.1 := hne u w hadj_uw
    have h3 : v.1 ≠ w.1 := hne v w hadj_vw
    -- Extract the vertices in parts 0, 1, 2
    have hex : ∃ p0 p1 p2 : Fin 3 × ZMod M,
        ({u, v, w} : Finset (Fin 3 × ZMod M)) = {p0, p1, p2} ∧
        p0.1 = 0 ∧ p1.1 = 1 ∧ p2.1 = 2 ∧
        (cayleyGraph M A).Adj p0 p1 ∧ (cayleyGraph M A).Adj p1 p2 ∧ (cayleyGraph M A).Adj p0 p2 := by
      have fin3_cases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
      rcases fin3_cases u.1 with hu0 | hu1 | hu2 <;>
      rcases fin3_cases v.1 with hv0 | hv1 | hv2 <;>
      rcases fin3_cases w.1 with hw0 | hw1 | hw2
      all_goals try (exfalso; first | exact h1 (by omega) | exact h2 (by omega) | exact h3 (by omega))
      · exact ⟨u, v, w, rfl, hu0, hv1, hw2, hadj_uv, hadj_vw, hadj_uw⟩
      · exact ⟨u, w, v, by ext z; simp [or_comm, or_left_comm], hu0, hw1, hv2, hadj_uw, hadj_vw.symm, hadj_uv⟩
      · exact ⟨v, u, w, by ext z; simp [or_comm, or_left_comm], hv0, hu1, hw2, hadj_uv.symm, hadj_uw, hadj_vw⟩
      · exact ⟨w, u, v, by ext z; simp [or_comm, or_left_comm], hw0, hu1, hv2, hadj_uw.symm, hadj_uv, hadj_vw.symm⟩
      · exact ⟨v, w, u, by ext z; simp [or_comm, or_left_comm], hv0, hw1, hu2, hadj_vw, hadj_uw.symm, hadj_uv.symm⟩
      · exact ⟨w, v, u, by ext z; simp [or_comm, or_left_comm], hw0, hv1, hu2, hadj_vw.symm, hadj_uv.symm, hadj_uw.symm⟩
    obtain ⟨p0, p1, p2, heq, hp0, hp1, hp2, h01, h12, h02⟩ := hex
    have ha : ∃ a ∈ A, p1.2 - p0.2 = (a : ZMod M) := by
      dsimp only [cayleyGraph] at h01
      rcases h01 with ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩
      · exact h
      all_goals omega
    have hb : ∃ b ∈ A, p2.2 - p1.2 = (b : ZMod M) := by
      dsimp only [cayleyGraph] at h12
      rcases h12 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · omega
      · omega
      · exact h
      all_goals omega
    have hc : ∃ c ∈ A, p2.2 - p0.2 = (c : ZMod M) := by
      dsimp only [cayleyGraph] at h02
      rcases h02 with ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩ | ⟨h, _⟩
      · omega
      · omega
      · omega
      · omega
      · exact h
      · omega
    obtain ⟨a, haA, ha_eq⟩ := ha
    obtain ⟨b, hbA, hb_eq⟩ := hb
    obtain ⟨c, hcA, hc_eq⟩ := hc
    have hsum_mod : ((a + b : ℕ) : ZMod M) = (c : ZMod M) := by
      push_cast
      rw [← ha_eq, ← hb_eq, ← hc_eq]
      ring
    have ha_le : a ≤ n := (Finset.mem_Icc.mp (hA haA)).2
    have hb_le : b ≤ n := (Finset.mem_Icc.mp (hA hbA)).2
    have hc_le : c ≤ n := (Finset.mem_Icc.mp (hA hcA)).2
    have hab_eq : a + b = c := natCast_zmod_inj (by omega) (by omega) hsum_mod
    have hab_mem : (a, b) ∈ schurTriples A := by
      rw [schurTriples, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨haA, hbA⟩, hab_eq ▸ hcA⟩
    rw [Finset.mem_image]
    refine ⟨(p0.2, (a, b)), Finset.mem_product.mpr ⟨Finset.mem_univ _, hab_mem⟩, ?_⟩
    rw [heq]
    have hp0_eq : p0 = (0, p0.2) := Prod.ext hp0 rfl
    have hp1_eq : p1 = (1, p0.2 + (a : ZMod M)) := Prod.ext hp1 (by rw [← ha_eq]; ring)
    have hp2_eq : p2 = (2, p0.2 + (a : ZMod M) + (b : ZMod M)) :=
      Prod.ext hp2 (by rw [← ha_eq, ← hb_eq]; ring)
    rw [hp0_eq, hp1_eq, hp2_eq]
  calc ((cayleyGraph M A).cliqueFinset 3).card
      ≤ ((Finset.univ ×ˢ schurTriples A).image f).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ ×ˢ schurTriples A).card := Finset.card_image_le
    _ = M * (schurTriples A).card := by rw [Finset.card_product, Finset.card_univ, ZMod.card]

/-- **Sum-Free Removal Lemma (Green 2005 / Král'–Serra–Vena 2009)** via Mathlib's
`SimpleGraph.triangle_removal`. -/
theorem schur_removal (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 ≤ n → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
      ((schurTriples A).card : ℝ) < ε * (n : ℝ) ^ 2 →
      ∃ B C : Finset ℕ, A = B ∪ C ∧ (∀ a ∈ B, ∀ b ∈ B, a + b ∉ B) ∧ (C.card : ℝ) ≤ η * (n : ℝ) := by
  set η' : ℝ := min (η / 150) (1 / 2) with hη'_def
  have hη'pos : 0 < η' := lt_min (by positivity) (by norm_num)
  have hη'le : η' ≤ η / 150 := min_le_left _ _
  refine ⟨SimpleGraph.triangleRemovalBound η' * 27, by positivity, ?_⟩
  intro n hn A hA htri
  set M := 2 * n + 1 with hM_def
  haveI : NeZero M := ⟨by omega⟩
  set G := cayleyGraph M A with hG_def
  have hcardV : Fintype.card (Fin 3 × ZMod M) = 3 * M := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]
  have hcl_lt : ((G.cliqueFinset 3).card : ℝ) <
      SimpleGraph.triangleRemovalBound η' * (Fintype.card (Fin 3 × ZMod M) : ℝ) ^ 3 := by
    have h1 : ((G.cliqueFinset 3).card : ℝ) ≤ (M : ℝ) * ((schurTriples A).card : ℝ) := by
      exact_mod_cast card_cliqueFinset_cayleyGraph_le hA
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
    have h2 : (M : ℝ) * ((schurTriples A).card : ℝ) <
        (M : ℝ) * (SimpleGraph.triangleRemovalBound η' * 27 * (n : ℝ) ^ 2) :=
      mul_lt_mul_of_pos_left htri hMpos
    have h3 : (M : ℝ) * (SimpleGraph.triangleRemovalBound η' * 27 * (n : ℝ) ^ 2) ≤
        SimpleGraph.triangleRemovalBound η' * (3 * (M : ℝ)) ^ 3 := by
      have htb : 0 ≤ SimpleGraph.triangleRemovalBound η' :=
        (SimpleGraph.triangleRemovalBound_pos hη'pos).le
      have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show n ≤ M by omega)
      have hsq : (n : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by nlinarith
      calc (M : ℝ) * (SimpleGraph.triangleRemovalBound η' * 27 * (n : ℝ) ^ 2)
          = SimpleGraph.triangleRemovalBound η' * 27 * ((M : ℝ) * (n : ℝ) ^ 2) := by ring
        _ ≤ SimpleGraph.triangleRemovalBound η' * 27 * ((M : ℝ) * (M : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hMpos.le) (by positivity)
        _ = SimpleGraph.triangleRemovalBound η' * (3 * (M : ℝ)) ^ 3 := by ring
    rw [hcardV]
    have hcast : ((3 * M : ℕ) : ℝ) = 3 * (M : ℝ) := by push_cast; ring
    rw [hcast]
    linarith
  obtain ⟨G', hG'le, _, hdel, hcf⟩ := SimpleGraph.triangle_removal hcl_lt
  -- Deleted edges set
  set D := G.edgeFinset \ G'.edgeFinset with hD_def
  have hG'sub : G'.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono hG'le he
  have hD_card : (D.card : ℝ) < η' * ((3 * M : ℕ) : ℝ) ^ 2 := by
    rw [Finset.card_sdiff_of_subset hG'sub]
    have hle_card : G'.edgeFinset.card ≤ G.edgeFinset.card := Finset.card_le_card hG'sub
    rw [Nat.cast_sub hle_card]
    simpa [hcardV] using hdel
  -- For each `a ∈ A`, count deleted edges of types 0-1, 1-2, 0-2 with difference `a`
  let del01 (a : ℕ) : Finset (ZMod M) :=
    Finset.univ.filter (fun x => s((0, x), (1, x + (a : ZMod M))) ∈ D)
  let del12 (a : ℕ) : Finset (ZMod M) :=
    Finset.univ.filter (fun x => s((1, x), (2, x + (a : ZMod M))) ∈ D)
  let del02 (a : ℕ) : Finset (ZMod M) :=
    Finset.univ.filter (fun x => s((0, x), (2, x + (a : ZMod M))) ∈ D)
  let delCount (a : ℕ) : ℕ := (del01 a).card + (del12 a).card + (del02 a).card
  let C : Finset ℕ := A.filter (fun a => M ≤ 3 * delCount a)
  let B : Finset ℕ := A \ C
  refine ⟨B, C, ?_, ?_, ?_⟩
  · ext x
    simp only [B, C, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
    tauto
  · -- `B` is sum-free
    intro a ha b hb hab
    have haC : a ∉ C := (Finset.mem_sdiff.mp ha).2
    have hbC : b ∉ C := (Finset.mem_sdiff.mp hb).2
    have hcC : a + b ∉ C := (Finset.mem_sdiff.mp hab).2
    have haA : a ∈ A := (Finset.mem_sdiff.mp ha).1
    have hbA : b ∈ A := (Finset.mem_sdiff.mp hb).1
    have hcA : a + b ∈ A := (Finset.mem_sdiff.mp hab).1
    have hca : 3 * delCount a < M := by
      by_contra h; exact haC (Finset.mem_filter.mpr ⟨haA, not_lt.mp h⟩)
    have hcb : 3 * delCount b < M := by
      by_contra h; exact hbC (Finset.mem_filter.mpr ⟨hbA, not_lt.mp h⟩)
    have hcc : 3 * delCount (a + b) < M := by
      by_contra h; exact hcC (Finset.mem_filter.mpr ⟨hcA, not_lt.mp h⟩)
    -- Bad `x : ZMod M` where at least one of the 3 edges of triangle `x` is in `D`
    let bad1 : Finset (ZMod M) := del01 a
    let bad2 : Finset (ZMod M) := (del12 b).image (fun y => y - (a : ZMod M))
    let bad3 : Finset (ZMod M) := del02 (a + b)
    have hbad_lt : (bad1 ∪ bad2 ∪ bad3).card < (Finset.univ : Finset (ZMod M)).card := by
      rw [Finset.card_univ, ZMod.card]
      have h1 : (bad1 ∪ bad2 ∪ bad3).card ≤ bad1.card + bad2.card + bad3.card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      have h2 : bad2.card ≤ (del12 b).card := Finset.card_image_le
      have h3 : bad1.card ≤ delCount a := by dsimp [bad1, delCount]; omega
      have h4 : (del12 b).card ≤ delCount b := by dsimp [delCount]; omega
      have h5 : bad3.card ≤ delCount (a + b) := by dsimp [bad3, delCount]; omega
      omega
    obtain ⟨x, -, hx_good⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
    have hx1 : x ∉ bad1 := fun h => hx_good (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hx2 : x ∉ bad2 := fun h => hx_good (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hx3 : x ∉ bad3 := fun h => hx_good (Finset.mem_union_right _ h)
    -- Then `{(0, x), (1, x + a), (2, x + a + b)}` is a 3-clique in `G'`!
    set v0 : Fin 3 × ZMod M := (0, x)
    set v1 : Fin 3 × ZMod M := (1, x + (a : ZMod M))
    set v2 : Fin 3 × ZMod M := (2, x + (a : ZMod M) + (b : ZMod M))
    have h01G : G.Adj v0 v1 := Or.inl ⟨rfl, rfl, a, haA, by ring⟩
    have h12G : G.Adj v1 v2 := Or.inr (Or.inr (Or.inl ⟨rfl, rfl, b, hbA, by ring⟩))
    have h02G : G.Adj v0 v2 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, a + b, hcA, by push_cast; ring⟩))))
    have h01G' : G'.Adj v0 v1 := by
      by_contra h
      have hmemD : s(v0, v1) ∈ D := Finset.mem_sdiff.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr h01G, fun h' => h (SimpleGraph.mem_edgeFinset.mp h')⟩
      exact hx1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmemD⟩)
    have h12G' : G'.Adj v1 v2 := by
      by_contra h
      have hmemD : s(v1, v2) ∈ D := Finset.mem_sdiff.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr h12G, fun h' => h (SimpleGraph.mem_edgeFinset.mp h')⟩
      have hmem_del : x + (a : ZMod M) ∈ del12 b :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmemD⟩
      exact hx2 (Finset.mem_image.mpr ⟨x + (a : ZMod M), hmem_del, by ring⟩)
    have h02G' : G'.Adj v0 v2 := by
      by_contra h
      have hmemD : s(v0, v2) ∈ D := Finset.mem_sdiff.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr h02G, fun h' => h (SimpleGraph.mem_edgeFinset.mp h')⟩
      have hv2_eq : v2 = (2, x + ((a + b : ℕ) : ZMod M)) := by
        dsimp [v2]; push_cast; ring_nf
      exact hx3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv2_eq ▸ hmemD⟩)
    have hne01 : v0 ≠ v1 := by intro h; have := congrArg Prod.fst h; simp [v0, v1] at this
    have hne02 : v0 ≠ v2 := by intro h; have := congrArg Prod.fst h; simp [v0, v2] at this
    have hne12 : v1 ≠ v2 := by intro h; have := congrArg Prod.fst h; simp [v1, v2] at this
    have hcl : G'.IsNClique 3 ({v0, v1, v2} : Finset (Fin 3 × ZMod M)) := by
      refine ⟨?_, Finset.card_eq_three.mpr ⟨v0, v1, v2, hne01, hne02, hne12, rfl⟩⟩
      intro u hu w hw huw
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hw
      rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
      all_goals try exact absurd rfl huw
      · exact h01G'
      · exact h02G'
      · exact h01G'.symm
      · exact h12G'
      · exact h02G'.symm
      · exact h12G'.symm
    exact hcf {v0, v1, v2} hcl
  · -- `|C| ≤ η * n` via `M * |C| ≤ 3 * ∑_{a ∈ A} delCount a ≤ 3 * |D|`
    -- Map `(t, a, x)` with `t ∈ {0, 1, 2}`, `a ∈ A`, `x ∈ del_t a` injectively into `D`!
    let e01 (a : ℕ) (x : ZMod M) : Sym2 (Fin 3 × ZMod M) := s((0, x), (1, x + (a : ZMod M)))
    let e12 (a : ℕ) (x : ZMod M) : Sym2 (Fin 3 × ZMod M) := s((1, x), (2, x + (a : ZMod M)))
    let e02 (a : ℕ) (x : ZMod M) : Sym2 (Fin 3 × ZMod M) := s((0, x), (2, x + (a : ZMod M)))
    let S01 : Finset (Sym2 (Fin 3 × ZMod M)) := A.biUnion (fun a => (del01 a).image (e01 a))
    let S12 : Finset (Sym2 (Fin 3 × ZMod M)) := A.biUnion (fun a => (del12 a).image (e12 a))
    let S02 : Finset (Sym2 (Fin 3 × ZMod M)) := A.biUnion (fun a => (del02 a).image (e02 a))
    have hdisj_S : Disjoint S01 S12 ∧ Disjoint S01 S02 ∧ Disjoint S12 S02 := by
      refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_⟩
      · intro e h1 h2
        rw [Finset.mem_biUnion] at h1 h2
        obtain ⟨a1, _, ha1⟩ := h1; obtain ⟨a2, _, ha2⟩ := h2
        rw [Finset.mem_image] at ha1 ha2
        obtain ⟨x1, _, rfl⟩ := ha1; obtain ⟨x2, _, hx2⟩ := ha2
        rw [Sym2.eq_iff] at hx2
        rcases hx2 with ⟨h, _⟩ | ⟨_, h⟩ <;> (have := congrArg Prod.fst h; simp at this)
      · intro e h1 h2
        rw [Finset.mem_biUnion] at h1 h2
        obtain ⟨a1, _, ha1⟩ := h1; obtain ⟨a2, _, ha2⟩ := h2
        rw [Finset.mem_image] at ha1 ha2
        obtain ⟨x1, _, rfl⟩ := ha1; obtain ⟨x2, _, hx2⟩ := ha2
        rw [Sym2.eq_iff] at hx2
        rcases hx2 with ⟨_, h⟩ | ⟨h, _⟩ <;> (have := congrArg Prod.fst h; simp at this)
      · intro e h1 h2
        rw [Finset.mem_biUnion] at h1 h2
        obtain ⟨a1, _, ha1⟩ := h1; obtain ⟨a2, _, ha2⟩ := h2
        rw [Finset.mem_image] at ha1 ha2
        obtain ⟨x1, _, rfl⟩ := ha1; obtain ⟨x2, _, hx2⟩ := ha2
        rw [Sym2.eq_iff] at hx2
        rcases hx2 with ⟨h, _⟩ | ⟨h, _⟩ <;> (have := congrArg Prod.fst h; simp at this)
    have hSsub : S01 ∪ S12 ∪ S02 ⊆ D := by
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · intro e he; rw [Finset.mem_biUnion] at he; obtain ⟨a, _, ha⟩ := he
        rw [Finset.mem_image] at ha; obtain ⟨x, hx, rfl⟩ := ha; exact (Finset.mem_filter.mp hx).2
      · intro e he; rw [Finset.mem_biUnion] at he; obtain ⟨a, _, ha⟩ := he
        rw [Finset.mem_image] at ha; obtain ⟨x, hx, rfl⟩ := ha; exact (Finset.mem_filter.mp hx).2
      · intro e he; rw [Finset.mem_biUnion] at he; obtain ⟨a, _, ha⟩ := he
        rw [Finset.mem_image] at ha; obtain ⟨x, hx, rfl⟩ := ha; exact (Finset.mem_filter.mp hx).2
    have hS01 : S01.card = ∑ a ∈ A, (del01 a).card := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun a _ => Finset.card_image_of_injective _ ?_
        intro x1 x2 h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩
        · exact congrArg Prod.snd h
        · have := congrArg Prod.fst h; simp at this
      · intro a1 ha1 a2 ha2 hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro e h1 h2
        rw [Finset.mem_image] at h1 h2
        obtain ⟨x1, _, rfl⟩ := h1; obtain ⟨x2, _, h⟩ := h2
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h1', h2'⟩ | ⟨h1', _⟩
        · have hx : x2 = x1 := congrArg Prod.snd h1'
          have ha_eq : (a2 : ZMod M) = (a1 : ZMod M) := by
            have := congrArg Prod.snd h2'; dsimp at this; rw [hx] at this; exact add_left_cancel this
          have h1lt : a1 < M := by have := (Finset.mem_Icc.mp (hA ha1)).2; omega
          have h2lt : a2 < M := by have := (Finset.mem_Icc.mp (hA ha2)).2; omega
          exact hne (natCast_zmod_inj h2lt h1lt ha_eq).symm
        · have := congrArg Prod.fst h1'; simp at this
    have hS12 : S12.card = ∑ a ∈ A, (del12 a).card := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun a _ => Finset.card_image_of_injective _ ?_
        intro x1 x2 h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩
        · exact congrArg Prod.snd h
        · have := congrArg Prod.fst h; simp at this
      · intro a1 ha1 a2 ha2 hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro e h1 h2
        rw [Finset.mem_image] at h1 h2
        obtain ⟨x1, _, rfl⟩ := h1; obtain ⟨x2, _, h⟩ := h2
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h1', h2'⟩ | ⟨h1', _⟩
        · have hx : x2 = x1 := congrArg Prod.snd h1'
          have ha_eq : (a2 : ZMod M) = (a1 : ZMod M) := by
            have := congrArg Prod.snd h2'; dsimp at this; rw [hx] at this; exact add_left_cancel this
          have h1lt : a1 < M := by have := (Finset.mem_Icc.mp (hA ha1)).2; omega
          have h2lt : a2 < M := by have := (Finset.mem_Icc.mp (hA ha2)).2; omega
          exact hne (natCast_zmod_inj h2lt h1lt ha_eq).symm
        · have := congrArg Prod.fst h1'; simp at this
    have hS02 : S02.card = ∑ a ∈ A, (del02 a).card := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun a _ => Finset.card_image_of_injective _ ?_
        intro x1 x2 h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩
        · exact congrArg Prod.snd h
        · have := congrArg Prod.fst h; simp at this
      · intro a1 ha1 a2 ha2 hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro e h1 h2
        rw [Finset.mem_image] at h1 h2
        obtain ⟨x1, _, rfl⟩ := h1; obtain ⟨x2, _, h⟩ := h2
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h1', h2'⟩ | ⟨h1', _⟩
        · have hx : x2 = x1 := congrArg Prod.snd h1'
          have ha_eq : (a2 : ZMod M) = (a1 : ZMod M) := by
            have := congrArg Prod.snd h2'; dsimp at this; rw [hx] at this; exact add_left_cancel this
          have h1lt : a1 < M := by have := (Finset.mem_Icc.mp (hA ha1)).2; omega
          have h2lt : a2 < M := by have := (Finset.mem_Icc.mp (hA ha2)).2; omega
          exact hne (natCast_zmod_inj h2lt h1lt ha_eq).symm
        · have := congrArg Prod.fst h1'; simp at this
    have hsum_le_D : ∑ a ∈ A, delCount a ≤ D.card := by
      have hunion : (S01 ∪ S12 ∪ S02).card = S01.card + S12.card + S02.card := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj_S.2.1, hdisj_S.2.2⟩),
            Finset.card_union_of_disjoint hdisj_S.1]
      have hsum_eq : ∑ a ∈ A, delCount a = S01.card + S12.card + S02.card := by
        simp only [delCount, Finset.sum_add_distrib, hS01, hS12, hS02]
      rw [hsum_eq, ← hunion]
      exact Finset.card_le_card hSsub
    have hMC : M * C.card ≤ 3 * D.card := by
      calc M * C.card = ∑ _a ∈ C, M := by simp [mul_comm]
        _ ≤ ∑ a ∈ C, 3 * delCount a := Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2
        _ = 3 * ∑ a ∈ C, delCount a := (Finset.mul_sum _ _ _).symm
        _ ≤ 3 * ∑ a ∈ A, delCount a := Nat.mul_le_mul_left 3
            (Finset.sum_le_sum_of_subset (Finset.filter_subset _ A))
        _ ≤ 3 * D.card := Nat.mul_le_mul_left 3 hsum_le_D
    have hMCR : (M : ℝ) * (C.card : ℝ) ≤ 3 * (D.card : ℝ) := by exact_mod_cast hMC
    have h3M : ((3 * M : ℕ) : ℝ) ≤ 9 * (n : ℝ) := by
      have : 3 * M ≤ 9 * n := by omega
      exact_mod_cast this
    have hMge : 2 * (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 2 * n ≤ M by omega)
    have hD_bd : (D.card : ℝ) ≤ (η / 150) * (81 * (n : ℝ) ^ 2) := by
      calc (D.card : ℝ) ≤ η' * ((3 * M : ℕ) : ℝ) ^ 2 := hD_card.le
        _ ≤ (η / 150) * (9 * (n : ℝ)) ^ 2 := by
            apply mul_le_mul hη'le _ (by positivity) (by positivity)
            nlinarith
        _ = (η / 150) * (81 * (n : ℝ) ^ 2) := by ring
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have h1 : 2 * (n : ℝ) * (C.card : ℝ) ≤ 3 * ((η / 150) * (81 * (n : ℝ) ^ 2)) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) C.card]
    nlinarith

end E877Removal


namespace E877Graphs

open Finset Real
open scoped Classical

/-- A graph possibly with loops on a finite vertex set `V : Finset ℕ`:
`adj` is a symmetric relation on `ℕ` (`adj u v → adj v u`), and `loop v` marks a self-loop at `v`.
A subset `I ⊆ V` is independent if no vertex in `I` has a loop and no two distinct vertices in `I`
are adjacent. -/
structure LGraph where
  adj : ℕ → ℕ → Prop
  symm : ∀ u v, adj u v → adj v u
  loop : ℕ → Prop

def LGraph.IsIndep (G : LGraph) (V I : Finset ℕ) : Prop :=
  I ⊆ V ∧ (∀ v ∈ I, ¬ G.loop v) ∧ (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.adj u v)

def LGraph.IsMIS (G : LGraph) (V I : Finset ℕ) : Prop :=
  G.IsIndep V I ∧ ∀ J, G.IsIndep V J → I ⊆ J → I = J

noncomputable def LGraph.misSet (G : LGraph) (V : Finset ℕ) : Finset (Finset ℕ) :=
  V.powerset.filter (G.IsMIS V)

/-- Open neighborhood of `v` in `G[V]` (excluding `v` itself). -/
noncomputable def LGraph.nbhd (G : LGraph) (V : Finset ℕ) (v : ℕ) : Finset ℕ :=
  (V.erase v).filter (G.adj v)

/-- Closed neighborhood of `v` in `G[V]`. -/
noncomputable def LGraph.cnbhd (G : LGraph) (V : Finset ℕ) (v : ℕ) : Finset ℕ :=
  insert v (G.nbhd V v)

/-- Degree in `G[V]` (loop contributes 2, as in BLST). -/
noncomputable def LGraph.deg (G : LGraph) (V : Finset ℕ) (v : ℕ) : ℕ :=
  (G.nbhd V v).card + if G.loop v then 2 else 0

lemma LGraph.isMIS_iff_maximal {G : LGraph} {V I : Finset ℕ} :
    G.IsMIS V I ↔ G.IsIndep V I ∧ ∀ v ∈ V, v ∉ I → G.loop v ∨ ∃ u ∈ I, G.adj u v := by
  constructor
  · rintro ⟨hI, hmax⟩
    refine ⟨hI, fun v hv hvI => ?_⟩
    by_contra h
    push_neg at h
    have hI' : G.IsIndep V (insert v I) := by
      refine ⟨Finset.insert_subset_iff.mpr ⟨hv, hI.1⟩, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxI
        · exact h.1
        · exact hI.2.1 x hxI
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hxI <;>
        rcases Finset.mem_insert.mp hy with rfl | hyI
        · exact absurd rfl hxy
        · exact fun hadj => h.2 y hyI (G.symm _ _ hadj)
        · exact h.2 x hxI
        · exact hI.2.2 x hxI y hyI hxy
    have heq := hmax (insert v I) hI' (Finset.subset_insert v I)
    exact hvI (heq ▸ Finset.mem_insert_self v I)
  · rintro ⟨hI, hcov⟩
    refine ⟨hI, fun J hJ hIJ => Finset.Subset.antisymm hIJ ?_⟩
    intro v hvJ
    by_contra hvI
    rcases hcov v (hJ.1 hvJ) hvI with hlp | ⟨u, huI, hadj⟩
    · exact hJ.2.1 v hvJ hlp
    · exact hJ.2.2 u (hIJ huI) v hvJ (fun h => hvI (h ▸ huI)) hadj

/-- Deleting looped vertices does not change the set of maximal independent sets. -/
lemma LGraph.misSet_erase_loop {G : LGraph} {V : Finset ℕ} {v : ℕ} (hv : G.loop v) :
    G.misSet V = G.misSet (V.erase v) := by
  ext I
  simp only [LGraph.misSet, Finset.mem_filter, Finset.mem_powerset, LGraph.isMIS_iff_maximal]
  constructor
  · rintro ⟨_, ⟨hIV, hnl, hna⟩, hcov⟩
    have hvI : v ∉ I := fun h => hnl v h hv
    have hsub : I ⊆ V.erase v := fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => hvI (h ▸ hx), hIV hx⟩
    exact ⟨hsub, ⟨hsub, hnl, hna⟩, fun w hw hwI => hcov w (Finset.mem_of_mem_erase hw) hwI⟩
  · rintro ⟨_, ⟨hIV, hnl, hna⟩, hcov⟩
    have hsub : I ⊆ V := hIV.trans (Finset.erase_subset v V)
    refine ⟨hsub, ⟨hsub, hnl, hna⟩, fun w hw hwI => ?_⟩
    by_cases hwv : w = v
    · exact Or.inl (hwv ▸ hv)
    · exact hcov w (Finset.mem_erase.mpr ⟨hwv, hw⟩) hwI

/-- If `I` is a MIS of `G[V]` with `v ∈ I`, then `I.erase v` is a MIS of `G[V \ cnbhd v]`. -/
lemma LGraph.erase_mem_misSet_sdiff_cnbhd {G : LGraph} {V I : Finset ℕ} {v : ℕ}
    (hI : I ∈ G.misSet V) (hvI : v ∈ I) :
    I.erase v ∈ G.misSet (V \ G.cnbhd V v) := by
  rw [LGraph.misSet, Finset.mem_filter, Finset.mem_powerset, LGraph.isMIS_iff_maximal] at hI ⊢
  obtain ⟨_, ⟨hIV, hnl, hna⟩, hcov⟩ := hI
  have hsub : I.erase v ⊆ V \ G.cnbhd V v := by
    intro x hx
    obtain ⟨hxv, hxI⟩ := Finset.mem_erase.mp hx
    refine Finset.mem_sdiff.mpr ⟨hIV hxI, ?_⟩
    simp only [LGraph.cnbhd, LGraph.nbhd, Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
    rintro (rfl | ⟨⟨_, _⟩, hadj⟩)
    · exact hxv rfl
    · exact hna v hvI x hxI (Ne.symm hxv) hadj
  refine ⟨hsub, ⟨hsub, fun x hx => hnl x (Finset.mem_of_mem_erase hx),
    fun x hx y hy hxy => hna x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy⟩, ?_⟩
  intro w hw hwI
  obtain ⟨hwV, hwc⟩ := Finset.mem_sdiff.mp hw
  have hwv : w ≠ v := fun h => hwc (h.symm ▸ Finset.mem_insert_self v _)
  have hwI' : w ∉ I := fun h => hwI (Finset.mem_erase.mpr ⟨hwv, h⟩)
  rcases hcov w hwV hwI' with hlp | ⟨u, huI, hadj⟩
  · exact Or.inl hlp
  · right
    have huv : u ≠ v := by
      rintro rfl
      exact hwc (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hwv, hwV⟩, hadj⟩))
    exact ⟨u, Finset.mem_erase.mpr ⟨huv, huI⟩, hadj⟩

/-- If `I` is a MIS of `G[V]` with `v ∉ I`, then `I` is a MIS of `G[V.erase v]`. -/
lemma LGraph.mem_misSet_erase {G : LGraph} {V I : Finset ℕ} {v : ℕ}
    (hI : I ∈ G.misSet V) (hvI : v ∉ I) :
    I ∈ G.misSet (V.erase v) := by
  rw [LGraph.misSet, Finset.mem_filter, Finset.mem_powerset, LGraph.isMIS_iff_maximal] at hI ⊢
  obtain ⟨_, ⟨hIV, hnl, hna⟩, hcov⟩ := hI
  have hsub : I ⊆ V.erase v := fun x hx =>
    Finset.mem_erase.mpr ⟨fun h => hvI (h ▸ hx), hIV hx⟩
  exact ⟨hsub, ⟨hsub, hnl, hna⟩, fun w hw hwI => hcov w (Finset.mem_of_mem_erase hw) hwI⟩

/-- Count of MIS containing `v` is at most `(G.misSet (V \ G.cnbhd V v)).card`. -/
lemma LGraph.card_misSet_filter_mem_le {G : LGraph} {V : Finset ℕ} (v : ℕ) :
    ((G.misSet V).filter (fun I => v ∈ I)).card ≤ (G.misSet (V \ G.cnbhd V v)).card := by
  refine Finset.card_le_card_of_injOn (fun I => I.erase v) ?_ ?_
  · intro I hI
    obtain ⟨hImis, hvI⟩ := Finset.mem_filter.mp hI
    exact G.erase_mem_misSet_sdiff_cnbhd hImis hvI
  · intro I hI J hJ heq
    dsimp only at heq
    have hvI : v ∈ I := (Finset.mem_filter.mp hI).2
    have hvJ : v ∈ J := (Finset.mem_filter.mp hJ).2
    rw [← Finset.insert_erase hvI, ← Finset.insert_erase hvJ, heq]

/-- Count of MIS not containing `v` is at most `(G.misSet (V.erase v)).card`. -/
lemma LGraph.card_misSet_filter_notMem_le {G : LGraph} {V : Finset ℕ} (v : ℕ) :
    ((G.misSet V).filter (fun I => v ∉ I)).card ≤ (G.misSet (V.erase v)).card :=
  Finset.card_le_card fun I hI => G.mem_misSet_erase (Finset.mem_filter.mp hI).1
    (Finset.mem_filter.mp hI).2

/-- **Moon–Moser (1965)** for graphs possibly with loops: `|MIS(G[V])| ≤ 3 ^ (|V| / 3)`. -/
theorem moon_moser (G : LGraph) (V : Finset ℕ) :
    ((G.misSet V).card : ℝ) ≤ (3 : ℝ) ^ ((V.card : ℝ) / 3) := by
  induction hn : V.card using Nat.strong_induction_on generalizing V with
  | _ n ih =>
    by_cases hne : V.Nonempty
    · -- First eliminate any looped vertex
      by_cases hlp : ∃ v ∈ V, G.loop v
      · obtain ⟨v, hvV, hvL⟩ := hlp
        rw [G.misSet_erase_loop hvL]
        have hVpos : 0 < V.card := Finset.card_pos.mpr hne
        have hlt : (V.erase v).card < n := by rw [Finset.card_erase_of_mem hvV]; omega
        have h1 := ih (V.erase v).card hlt (V.erase v) rfl
        have hle : ((V.erase v).card : ℝ) / 3 ≤ (n : ℝ) / 3 := by
          have : (V.erase v).card ≤ n := by omega
          have hR : ((V.erase v).card : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
          linarith
        exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle)
      · push_neg at hlp
        -- Pick vertex `v ∈ V` of minimum neighborhood size
        obtain ⟨v, hvV, hvmin⟩ := V.exists_min_image (fun u => (G.nbhd V u).card) hne
        -- Every MIS contains at least one vertex of `G.cnbhd V v`
        have hcov : G.misSet V ⊆ (G.cnbhd V v).biUnion (fun u => (G.misSet V).filter (fun I => u ∈ I)) := by
          intro I hI
          rw [Finset.mem_biUnion]
          by_cases hvI : v ∈ I
          · exact ⟨v, Finset.mem_insert_self v _, Finset.mem_filter.mpr ⟨hI, hvI⟩⟩
          · have hI' := (LGraph.isMIS_iff_maximal).mp (Finset.mem_filter.mp hI).2
            rcases hI'.2 v hvV hvI with hl | ⟨u, huI, hadj⟩
            · exact absurd hl (hlp v hvV)
            · have huv : u ≠ v := fun h => hvI (h ▸ huI)
              have huV : u ∈ V := hI'.1.1 huI
              refine ⟨u, Finset.mem_insert_of_mem (Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨huv, huV⟩, G.symm _ _ hadj⟩), Finset.mem_filter.mpr ⟨hI, huI⟩⟩
        have hcard_le : (G.misSet V).card ≤ ∑ u ∈ G.cnbhd V v, (G.misSet (V \ G.cnbhd V u)).card :=
          (Finset.card_le_card hcov).trans <| (Finset.card_biUnion_le).trans <|
            Finset.sum_le_sum fun u _ => G.card_misSet_filter_mem_le u
        set d := (G.nbhd V v).card
        have hcnbhd_card : (G.cnbhd V v).card = d + 1 := by
          rw [LGraph.cnbhd, Finset.card_insert_of_notMem]
          simp [LGraph.nbhd]
        have hsum_bd : ((G.misSet V).card : ℝ) ≤
            ((d + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (((n - (d + 1) : ℕ) : ℝ) / 3) := by
          have h1 : ((G.misSet V).card : ℝ) ≤ ∑ u ∈ G.cnbhd V v, ((G.misSet (V \ G.cnbhd V u)).card : ℝ) := by
            exact_mod_cast hcard_le
          refine h1.trans ?_
          calc ∑ u ∈ G.cnbhd V v, ((G.misSet (V \ G.cnbhd V u)).card : ℝ)
              ≤ ∑ _u ∈ G.cnbhd V v, (3 : ℝ) ^ (((n - (d + 1) : ℕ) : ℝ) / 3) := by
                apply Finset.sum_le_sum
                intro u hu
                have huV : u ∈ V := by
                  rcases Finset.mem_insert.mp hu with rfl | hu'
                  · exact hvV
                  · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hu').1
                have hu_sub : G.cnbhd V u ⊆ V := by
                  intro x hx
                  rcases Finset.mem_insert.mp hx with rfl | hx'
                  · exact huV
                  · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
                have hu_card : d + 1 ≤ (G.cnbhd V u).card := by
                  rw [LGraph.cnbhd, Finset.card_insert_of_notMem (by simp [LGraph.nbhd])]
                  have := hvmin u huV
                  omega
                have hdiff_card : (V \ G.cnbhd V u).card = n - (G.cnbhd V u).card := by
                  rw [Finset.card_sdiff_of_subset hu_sub, hn]
                have hn_pos : 0 < n := by rw [← hn]; exact Finset.card_pos.mpr hne
                have hlt : (V \ G.cnbhd V u).card < n := by omega
                have hih := ih (V \ G.cnbhd V u).card hlt (V \ G.cnbhd V u) rfl
                refine hih.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
                have hle : (V \ G.cnbhd V u).card ≤ n - (d + 1) := by omega
                have hR : ((V \ G.cnbhd V u).card : ℝ) ≤ ((n - (d + 1) : ℕ) : ℝ) := by exact_mod_cast hle
                linarith
            _ = ((d + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (((n - (d + 1) : ℕ) : ℝ) / 3) := by
                rw [Finset.sum_const, hcnbhd_card, nsmul_eq_mul]
        have hd_le : d + 1 ≤ n := by
          have : G.cnbhd V v ⊆ V := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact hvV
            · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
          have := Finset.card_le_card this
          omega
        -- Elementary inequality: `(k : ℝ) ≤ 3 ^ (k / 3)` for all `k : ℕ` (equivalently `k^3 ≤ 3^k`)
        have hk3 : ∀ k : ℕ, (k : ℝ) ≤ (3 : ℝ) ^ ((k : ℝ) / 3) := by
          intro k
          have hnat : k ^ 3 ≤ 3 ^ k := by
            induction k with
            | zero => norm_num
            | succ m ihm =>
              by_cases hm : m ≤ 2
              · interval_cases m <;> norm_num
              · have h1 : (m + 1) ^ 3 ≤ 3 * m ^ 3 := by
                  have hm3 : 3 ≤ m := by omega
                  nlinarith [sq_nonneg m]
                calc (m + 1) ^ 3 ≤ 3 * m ^ 3 := h1
                  _ ≤ 3 * 3 ^ m := Nat.mul_le_mul_left 3 ihm
                  _ = 3 ^ (m + 1) := by ring
          have hR : ((k : ℝ) ^ 3) ≤ ((3 : ℝ) ^ ((k : ℝ) / 3)) ^ 3 := by
            rw [← Real.rpow_natCast ((3 : ℝ) ^ ((k : ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
            have hexp : (k : ℝ) / 3 * (3 : ℕ) = (k : ℝ) := by push_cast; ring
            rw [hexp, Real.rpow_natCast]
            exact_mod_cast hnat
          by_contra hlt
          push_neg at hlt
          have hnn : 0 ≤ (3 : ℝ) ^ ((k : ℝ) / 3) := by positivity
          have hcube : ((3 : ℝ) ^ ((k : ℝ) / 3)) ^ 3 < (k : ℝ) ^ 3 :=
            pow_lt_pow_left₀ hlt hnn (by norm_num)
          linarith
        calc ((G.misSet V).card : ℝ)
            ≤ ((d + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (((n - (d + 1) : ℕ) : ℝ) / 3) := hsum_bd
          _ ≤ (3 : ℝ) ^ (((d + 1 : ℕ) : ℝ) / 3) * (3 : ℝ) ^ (((n - (d + 1) : ℕ) : ℝ) / 3) :=
              mul_le_mul_of_nonneg_right (hk3 (d + 1)) (by positivity)
          _ = (3 : ℝ) ^ ((n : ℝ) / 3) := by
              rw [← Real.rpow_add (by norm_num)]
              congr 1
              have hsub : ((n - (d + 1) : ℕ) : ℝ) = (n : ℝ) - ((d + 1 : ℕ) : ℝ) := Nat.cast_sub hd_le
              rw [hsub]; ring
    · have hVe : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst hVe
      have hn0 : n = 0 := by simpa using hn.symm
      subst hn0
      have hcard : (G.misSet ∅).card ≤ 1 := by
        have hsub : G.misSet ∅ ⊆ {∅} := by
          intro I hI
          have := (Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1)
          rw [Finset.subset_empty.mp this]
          exact Finset.mem_singleton_self ∅
        exact (Finset.card_le_card hsub).trans (by simp)
      have hR : ((G.misSet ∅).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      simpa using hR

/-- Triangle-free predicate for `LGraph` on vertex set `V`. -/
def LGraph.IsTriangleFree (G : LGraph) (V : Finset ℕ) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, ∀ w ∈ V, u ≠ v → u ≠ w → v ≠ w → G.adj u v → G.adj v w → ¬ G.adj u w

set_option maxHeartbeats 800000 in
/-- **Hujter–Tuza (1993)** for triangle-free graphs possibly with loops: `|MIS(G[V])| ≤ 2 ^ (|V| / 2)`. -/
theorem hujter_tuza (G : LGraph) (V : Finset ℕ) (htf : G.IsTriangleFree V) :
    ((G.misSet V).card : ℝ) ≤ (2 : ℝ) ^ ((V.card : ℝ) / 2) := by
  induction hn : V.card using Nat.strong_induction_on generalizing V with
  | _ n ih =>
    have htf_sub : ∀ W ⊆ V, G.IsTriangleFree W :=
      fun W hWV u hu v hv w hw => htf u (hWV hu) v (hWV hv) w (hWV hw)
    by_cases hne : V.Nonempty
    · -- Eliminate looped vertices first
      by_cases hlp : ∃ v ∈ V, G.loop v
      · obtain ⟨v, hvV, hvL⟩ := hlp
        rw [G.misSet_erase_loop hvL]
        have hVpos : 0 < V.card := Finset.card_pos.mpr hne
        have hlt : (V.erase v).card < n := by rw [Finset.card_erase_of_mem hvV]; omega
        have h1 := ih (V.erase v).card hlt (V.erase v) (htf_sub _ (Finset.erase_subset v V)) rfl
        have hle : ((V.erase v).card : ℝ) / 2 ≤ (n : ℝ) / 2 := by
          have : (V.erase v).card ≤ n := by omega
          have hR : ((V.erase v).card : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
          linarith
        exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle)
      · push_neg at hlp
        -- Helper: `2^((n - k)/2) = 2^(-k/2) * 2^(n/2)`
        have hrpow_sub : ∀ k : ℕ, k ≤ n →
            (2 : ℝ) ^ (((n - k : ℕ) : ℝ) / 2) = (2 : ℝ) ^ (-(k : ℝ) / 2) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
          intro k hk
          rw [← Real.rpow_add (by norm_num)]
          congr 1
          rw [Nat.cast_sub hk]; ring
        -- Case 1: Some vertex `v ∈ V` has degree 0 (isolated)
        by_cases hdeg0 : ∃ v ∈ V, (G.nbhd V v).card = 0
        · obtain ⟨v, hvV, hv0⟩ := hdeg0
          -- Every MIS must contain `v`
          have hsub : G.misSet V ⊆ (G.misSet V).filter (fun I => v ∈ I) := by
            intro I hI
            refine Finset.mem_filter.mpr ⟨hI, ?_⟩
            by_contra hvI
            have hI' := (LGraph.isMIS_iff_maximal).mp (Finset.mem_filter.mp hI).2
            rcases hI'.2 v hvV hvI with hl | ⟨u, huI, hadj⟩
            · exact hlp v hvV hl
            · have huv : u ≠ v := fun h => hvI (h ▸ huI)
              have hu_nb : u ∈ G.nbhd V v := Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨huv, hI'.1.1 huI⟩, G.symm _ _ hadj⟩
              have hpos : 0 < (G.nbhd V v).card := Finset.card_pos.mpr ⟨u, hu_nb⟩
              omega
          have hc1 : (G.misSet V).card ≤ (G.misSet (V \ G.cnbhd V v)).card :=
            (Finset.card_le_card hsub).trans (G.card_misSet_filter_mem_le v)
          have hvsub : V \ G.cnbhd V v ⊆ V := Finset.sdiff_subset
          have hvcard : (V \ G.cnbhd V v).card = n - 1 := by
            have hc : G.cnbhd V v ⊆ V := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hx'
              · exact hvV
              · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
            rw [Finset.card_sdiff_of_subset hc, LGraph.cnbhd,
                Finset.card_insert_of_notMem (by simp [LGraph.nbhd]), hv0, hn]
          have hlt : (V \ G.cnbhd V v).card < n := by
            have hn1 : 1 ≤ n := by rw [← hn]; exact Finset.card_pos.mpr hne
            omega
          have hih := ih _ hlt _ (htf_sub _ hvsub) rfl
          calc ((G.misSet V).card : ℝ) ≤ ((G.misSet (V \ G.cnbhd V v)).card : ℝ) := by exact_mod_cast hc1
            _ ≤ (2 : ℝ) ^ (((V \ G.cnbhd V v).card : ℝ) / 2) := hih
            _ ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
                apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
                have : (V \ G.cnbhd V v).card ≤ n := by omega
                have hR : ((V \ G.cnbhd V v).card : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
                linarith
        -- Case 2: Some vertex `v ∈ V` has degree 1
        · by_cases hdeg1 : ∃ v ∈ V, (G.nbhd V v).card = 1
          · obtain ⟨v, hvV, hv1⟩ := hdeg1
            obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hv1
            have hu_nb : u ∈ G.nbhd V v := hu_eq ▸ Finset.mem_singleton_self u
            have huv : u ≠ v := (Finset.mem_erase.mp (Finset.mem_filter.mp hu_nb).1).1
            have huV : u ∈ V := (Finset.mem_erase.mp (Finset.mem_filter.mp hu_nb).1).2
            have hadj_vu : G.adj v u := (Finset.mem_filter.mp hu_nb).2
            -- Every MIS contains either `v` or `u`
            have hcov : G.misSet V ⊆
                ((G.misSet V).filter (fun I => v ∈ I)) ∪ ((G.misSet V).filter (fun I => u ∈ I)) := by
              intro I hI
              by_cases hvI : v ∈ I
              · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hI, hvI⟩)
              · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hI, ?_⟩)
                have hI' := (LGraph.isMIS_iff_maximal).mp (Finset.mem_filter.mp hI).2
                rcases hI'.2 v hvV hvI with hl | ⟨w, hwI, hadj⟩
                · exact absurd hl (hlp v hvV)
                · have hwv : w ≠ v := fun h => hvI (h ▸ hwI)
                  have hw_nb : w ∈ G.nbhd V v := Finset.mem_filter.mpr
                    ⟨Finset.mem_erase.mpr ⟨hwv, hI'.1.1 hwI⟩, G.symm _ _ hadj⟩
                  rw [hu_eq, Finset.mem_singleton] at hw_nb
                  exact hw_nb ▸ hwI
            have hcard_le : (G.misSet V).card ≤
                (G.misSet (V \ G.cnbhd V v)).card + (G.misSet (V \ G.cnbhd V u)).card :=
              (Finset.card_le_card hcov).trans <| (Finset.card_union_le _ _).trans <|
                Nat.add_le_add (G.card_misSet_filter_mem_le v) (G.card_misSet_filter_mem_le u)
            have hv_sub : G.cnbhd V v ⊆ V := by
              intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
              · exact hvV
              · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
            have hu_sub : G.cnbhd V u ⊆ V := by
              intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
              · exact huV
              · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
            have hv_ge2 : 2 ≤ (G.cnbhd V v).card := by
              rw [LGraph.cnbhd, Finset.card_insert_of_notMem (by simp [LGraph.nbhd]), hv1]
            have hu_ge2 : 2 ≤ (G.cnbhd V u).card := by
              rw [LGraph.cnbhd, Finset.card_insert_of_notMem (by simp [LGraph.nbhd])]
              have hv_nbu : v ∈ G.nbhd V u := Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨huv.symm, hvV⟩, G.symm _ _ hadj_vu⟩
              have := Finset.card_pos.mpr ⟨v, hv_nbu⟩
              omega
            have hn2 : 2 ≤ n := by
              have := Finset.card_le_card hv_sub; omega
            have hv_card : (V \ G.cnbhd V v).card ≤ n - 2 := by
              rw [Finset.card_sdiff_of_subset hv_sub, hn]; omega
            have hu_card : (V \ G.cnbhd V u).card ≤ n - 2 := by
              rw [Finset.card_sdiff_of_subset hu_sub, hn]; omega
            have hih1 := ih _ (by omega) (V \ G.cnbhd V v) (htf_sub _ Finset.sdiff_subset) rfl
            have hih2 := ih _ (by omega) (V \ G.cnbhd V u) (htf_sub _ Finset.sdiff_subset) rfl
            have hb1 : ((G.misSet (V \ G.cnbhd V v)).card : ℝ) ≤ (2 : ℝ) ^ (((n - 2 : ℕ) : ℝ) / 2) :=
              hih1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
                have hR : ((V \ G.cnbhd V v).card : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast hv_card
                linarith))
            have hb2 : ((G.misSet (V \ G.cnbhd V u)).card : ℝ) ≤ (2 : ℝ) ^ (((n - 2 : ℕ) : ℝ) / 2) :=
              hih2.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
                have hR : ((V \ G.cnbhd V u).card : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast hu_card
                linarith))
            have htot : ((G.misSet V).card : ℝ) ≤ 2 * (2 : ℝ) ^ (((n - 2 : ℕ) : ℝ) / 2) := by
              have hR : ((G.misSet V).card : ℝ) ≤
                  ((G.misSet (V \ G.cnbhd V v)).card : ℝ) + ((G.misSet (V \ G.cnbhd V u)).card : ℝ) := by
                exact_mod_cast hcard_le
              linarith
            calc ((G.misSet V).card : ℝ) ≤ 2 * (2 : ℝ) ^ (((n - 2 : ℕ) : ℝ) / 2) := htot
              _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (((n - 2 : ℕ) : ℝ) / 2) := by rw [Real.rpow_one]
              _ = (2 : ℝ) ^ ((n : ℝ) / 2) := by
                  rw [← Real.rpow_add (by norm_num)]
                  congr 1; rw [Nat.cast_sub hn2]; push_cast; ring
          -- Case 3: Some vertex `v ∈ V` has degree ≥ 3
          · by_cases hdeg3 : ∃ v ∈ V, 3 ≤ (G.nbhd V v).card
            · obtain ⟨v, hvV, hv3⟩ := hdeg3
              have hcard_le : (G.misSet V).card ≤
                  (G.misSet (V \ G.cnbhd V v)).card + (G.misSet (V.erase v)).card := by
                have hpart := Finset.card_filter_add_card_filter_not (s := G.misSet V) (p := fun I => v ∈ I)
                rw [← hpart]
                exact Nat.add_le_add (G.card_misSet_filter_mem_le v) (G.card_misSet_filter_notMem_le v)
              have hv_sub : G.cnbhd V v ⊆ V := by
                intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
                · exact hvV
                · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
              have hv_ge4 : 4 ≤ (G.cnbhd V v).card := by
                rw [LGraph.cnbhd, Finset.card_insert_of_notMem (by simp [LGraph.nbhd])]; omega
              have hn4 : 4 ≤ n := by have := Finset.card_le_card hv_sub; omega
              have hv_card : (V \ G.cnbhd V v).card ≤ n - 4 := by
                rw [Finset.card_sdiff_of_subset hv_sub, hn]; omega
              have he_card : (V.erase v).card = n - 1 := by
                rw [Finset.card_erase_of_mem hvV, hn]
              have hih1 := ih _ (by omega) (V \ G.cnbhd V v) (htf_sub _ Finset.sdiff_subset) rfl
              have hih2 := ih _ (by omega) (V.erase v) (htf_sub _ (Finset.erase_subset v V)) rfl
              have hb1 : ((G.misSet (V \ G.cnbhd V v)).card : ℝ) ≤ (2 : ℝ) ^ (((n - 4 : ℕ) : ℝ) / 2) :=
                hih1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
                  have hR : ((V \ G.cnbhd V v).card : ℝ) ≤ ((n - 4 : ℕ) : ℝ) := by exact_mod_cast hv_card
                  linarith))
              have hb2 : ((G.misSet (V.erase v)).card : ℝ) ≤ (2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2) := by
                rwa [he_card] at hih2
              rw [hrpow_sub 4 hn4] at hb1
              rw [hrpow_sub 1 (by omega)] at hb2
              -- Show `2^(-2) + 2^(-1/2) ≤ 1` (since `2^(-1/2) = 1/√2 < 3/4`)
              have hconst : (2 : ℝ) ^ (-(4 : ℝ) / 2) + (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 := by
                have h2m2 : (2 : ℝ) ^ (-(4 : ℝ) / 2) = 1 / 4 := by
                  have : -(4 : ℝ) / 2 = -(2 : ℕ) := by norm_num
                  rw [this, Real.rpow_neg (by norm_num), Real.rpow_natCast]; norm_num
                have h2mhalf : (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ 3 / 4 := by
                  have hsq : ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = 1 / 2 := by
                    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num)]
                    norm_num
                  have hpos : 0 ≤ (2 : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
                  nlinarith
                linarith
              have hR : ((G.misSet V).card : ℝ) ≤
                  ((G.misSet (V \ G.cnbhd V v)).card : ℝ) + ((G.misSet (V.erase v)).card : ℝ) := by
                exact_mod_cast hcard_le
              calc ((G.misSet V).card : ℝ)
                  ≤ ((2 : ℝ) ^ (-(4 : ℝ) / 2) + (2 : ℝ) ^ (-(1 : ℝ) / 2)) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
                    nlinarith
                _ ≤ 1 * (2 : ℝ) ^ ((n : ℝ) / 2) :=
                    mul_le_mul_of_nonneg_right hconst (by positivity)
                _ = (2 : ℝ) ^ ((n : ℝ) / 2) := one_mul _
            -- Case 4: Every vertex in `V` has degree exactly 2 (2-regular triangle-free!)
            · push_neg at hdeg0 hdeg1 hdeg3
              have hdeg2 : ∀ x ∈ V, (G.nbhd V x).card = 2 := by
                intro x hx
                have h0 := hdeg0 x hx
                have h1 := hdeg1 x hx
                have h3 := hdeg3 x hx
                omega
              obtain ⟨v, hvV⟩ := hne
              obtain ⟨u, w, huw, hnb_v⟩ := Finset.card_eq_two.mp (hdeg2 v hvV)
              have hu_nb : u ∈ G.nbhd V v := hnb_v ▸ Finset.mem_insert_self u {w}
              have hw_nb : w ∈ G.nbhd V v := hnb_v ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self w)
              have huv : u ≠ v := (Finset.mem_erase.mp (Finset.mem_filter.mp hu_nb).1).1
              have huV : u ∈ V := (Finset.mem_erase.mp (Finset.mem_filter.mp hu_nb).1).2
              have hadj_vu : G.adj v u := (Finset.mem_filter.mp hu_nb).2
              have hwv : w ≠ v := (Finset.mem_erase.mp (Finset.mem_filter.mp hw_nb).1).1
              have hwV : w ∈ V := (Finset.mem_erase.mp (Finset.mem_filter.mp hw_nb).1).2
              have hadj_vw : G.adj v w := (Finset.mem_filter.mp hw_nb).2
              have hna_uw : ¬ G.adj u w := fun h => htf v hvV u huV w hwV huv.symm hwv.symm huw hadj_vu h hadj_vw
              -- Extract `u`'s other neighbor `u'`
              have hv_nbu : v ∈ G.nbhd V u := Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨huv.symm, hvV⟩, G.symm _ _ hadj_vu⟩
              have hu_er : ((G.nbhd V u).erase v).card = 1 := by
                rw [Finset.card_erase_of_mem hv_nbu, hdeg2 u huV]
              obtain ⟨u', hu'_eq⟩ := Finset.card_eq_one.mp hu_er
              have hu'_nb : u' ∈ (G.nbhd V u).erase v := hu'_eq ▸ Finset.mem_singleton_self u'
              have hu'v : u' ≠ v := (Finset.mem_erase.mp hu'_nb).1
              have hu'_nbu : u' ∈ G.nbhd V u := (Finset.mem_erase.mp hu'_nb).2
              have hu'u : u' ≠ u := (Finset.mem_erase.mp (Finset.mem_filter.mp hu'_nbu).1).1
              have hu'V : u' ∈ V := (Finset.mem_erase.mp (Finset.mem_filter.mp hu'_nbu).1).2
              have hadj_uu' : G.adj u u' := (Finset.mem_filter.mp hu'_nbu).2
              have hu'w : u' ≠ w := fun h => hna_uw (h ▸ hadj_uu')
              have hnb_u : G.nbhd V u = {v, u'} := by
                rw [← Finset.insert_erase hv_nbu, hu'_eq]
              -- Now split on whether `u'` is adjacent to `w` (`C_4` component) or not (`C_≥5`)
              by_cases hadj_u'w : G.adj u' w
              · -- `C_4 = {v, u, w, u'}`: every MIS contains either `v` (and `u'`) or `u` (and `w`)!
                have hC4_sub : ({v, u, w, u'} : Finset ℕ) ⊆ V := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl | rfl | rfl <;> assumption
                have hC4_card : ({v, u, w, u'} : Finset ℕ).card = 4 := by
                  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
                      Finset.card_insert_of_notMem, Finset.card_singleton]
                  · simp [hu'w.symm]
                  · simp [huw, hu'u.symm]
                  · simp [huv.symm, hwv.symm, hu'v.symm]
                have hn4 : 4 ≤ n := by have := Finset.card_le_card hC4_sub; omega
                -- Every MIS `I` has `I \ {v, u, w, u'} ∈ misSet (V \ {v, u, w, u'})`, and `I ∩ {v, u, w, u'}` is `{v, u'}` or `{u, w}`!
                have hmap : ∀ I ∈ G.misSet V,
                    (I \ {v, u, w, u'} ∈ G.misSet (V \ {v, u, w, u'})) ∧
                    (I ∩ {v, u, w, u'} = {v, u'} ∨ I ∩ {v, u, w, u'} = {u, w}) := by
                  intro I hI
                  have hI' := (LGraph.isMIS_iff_maximal).mp (Finset.mem_filter.mp hI).2
                  have hna_vu' : ¬ G.adj v u' := fun h =>
                    htf v hvV u huV u' hu'V huv.symm hu'v.symm hu'u.symm hadj_vu hadj_uu' h
                  -- First show `I ∩ {v, u, w, u'}` is `{v, u'}` or `{u, w}`
                  have hnb_w : G.nbhd V w = {v, u'} := by
                    have hv_nbw : v ∈ G.nbhd V w := Finset.mem_filter.mpr
                      ⟨Finset.mem_erase.mpr ⟨hwv.symm, hvV⟩, G.symm _ _ hadj_vw⟩
                    have hu'_nbw : u' ∈ G.nbhd V w := Finset.mem_filter.mpr
                      ⟨Finset.mem_erase.mpr ⟨hu'w, hu'V⟩, G.symm _ _ hadj_u'w⟩
                    have hsub2 : ({v, u'} : Finset ℕ) ⊆ G.nbhd V w := by
                      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
                      · exact hv_nbw
                      · rw [Finset.mem_singleton.mp hx']; exact hu'_nbw
                    have hcard2 : ({v, u'} : Finset ℕ).card = 2 := Finset.card_pair hu'v.symm
                    exact (Finset.eq_of_subset_of_card_le hsub2 (by rw [hdeg2 w hwV, hcard2])).symm
                  have hnb_u' : G.nbhd V u' = {u, w} := by
                    have hu_nbu' : u ∈ G.nbhd V u' := Finset.mem_filter.mpr
                      ⟨Finset.mem_erase.mpr ⟨hu'u.symm, huV⟩, G.symm _ _ hadj_uu'⟩
                    have hw_nbu' : w ∈ G.nbhd V u' := Finset.mem_filter.mpr
                      ⟨Finset.mem_erase.mpr ⟨hu'w.symm, hwV⟩, hadj_u'w⟩
                    have hsub2 : ({u, w} : Finset ℕ) ⊆ G.nbhd V u' := by
                      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
                      · exact hu_nbu'
                      · rw [Finset.mem_singleton.mp hx']; exact hw_nbu'
                    have hcard2 : ({u, w} : Finset ℕ).card = 2 := Finset.card_pair huw
                    exact (Finset.eq_of_subset_of_card_le hsub2 (by rw [hdeg2 u' hu'V, hcard2])).symm
                  -- No edges between `{v, u, w, u'}` and `V \ {v, u, w, u'}`!
                  have hno_cross : ∀ a ∈ ({v, u, w, u'} : Finset ℕ), ∀ b ∈ V \ {v, u, w, u'}, ¬ G.adj a b := by
                    intro a ha b hb hadj
                    obtain ⟨hbV, hbnot⟩ := Finset.mem_sdiff.mp hb
                    have hba : b ≠ a := fun h => hbnot (h ▸ ha)
                    have hb_nb : b ∈ G.nbhd V a := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hba, hbV⟩, hadj⟩
                    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hbnot
                    rcases ha with rfl | rfl | rfl | rfl
                    · rw [hnb_v] at hb_nb; simp at hb_nb; tauto
                    · rw [hnb_u] at hb_nb; simp at hb_nb; tauto
                    · rw [hnb_w] at hb_nb; simp at hb_nb; tauto
                    · rw [hnb_u'] at hb_nb; simp at hb_nb; tauto
                  constructor
                  · -- `I \ {v, u, w, u'}` is a MIS of `V \ {v, u, w, u'}`
                    rw [LGraph.misSet, Finset.mem_filter, Finset.mem_powerset, LGraph.isMIS_iff_maximal]
                    have hsub : I \ {v, u, w, u'} ⊆ V \ {v, u, w, u'} :=
                      Finset.sdiff_subset_sdiff hI'.1.1 (Subset.refl _)
                    refine ⟨hsub, ⟨hsub, fun x hx => hI'.1.2.1 x (Finset.mem_sdiff.mp hx).1,
                      fun x hx y hy hxy => hI'.1.2.2 x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).1 hxy⟩, ?_⟩
                    intro b hb hbI
                    have hbV : b ∈ V := (Finset.mem_sdiff.mp hb).1
                    have hbI' : b ∉ I := fun h => hbI (Finset.mem_sdiff.mpr ⟨h, (Finset.mem_sdiff.mp hb).2⟩)
                    rcases hI'.2 b hbV hbI' with hl | ⟨a, haI, hadj⟩
                    · exact Or.inl hl
                    · right
                      have ha_not : a ∉ ({v, u, w, u'} : Finset ℕ) := fun ha => hno_cross a ha b hb hadj
                      exact ⟨a, Finset.mem_sdiff.mpr ⟨haI, ha_not⟩, hadj⟩
                  · -- `I ∩ {v, u, w, u'}` is `{v, u'}` or `{u, w}`
                    by_cases hvI : v ∈ I
                    · left
                      have huI : u ∉ I := fun h => hI'.1.2.2 v hvI u h huv.symm hadj_vu
                      have hwI : w ∉ I := fun h => hI'.1.2.2 v hvI w h hwv.symm hadj_vw
                      have hu'I : u' ∈ I := by
                        by_contra h
                        rcases hI'.2 u' hu'V h with hl | ⟨a, haI, hadj⟩
                        · exact hlp u' hu'V hl
                        · have ha_nb : a ∈ G.nbhd V u' := Finset.mem_filter.mpr
                            ⟨Finset.mem_erase.mpr ⟨fun h' => h (h' ▸ haI), hI'.1.1 haI⟩, G.symm _ _ hadj⟩
                          rw [hnb_u'] at ha_nb
                          rcases Finset.mem_insert.mp ha_nb with rfl | ha'
                          · exact huI haI
                          · exact hwI (Finset.mem_singleton.mp ha' ▸ haI)
                      ext x
                      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
                      constructor
                      · rintro ⟨hxI, rfl | rfl | rfl | rfl⟩
                        · exact Or.inl rfl
                        · exact absurd hxI huI
                        · exact absurd hxI hwI
                        · exact Or.inr rfl
                      · rintro (rfl | rfl)
                        · exact ⟨hvI, Or.inl rfl⟩
                        · exact ⟨hu'I, Or.inr (Or.inr (Or.inr rfl))⟩
                    · right
                      -- `v ∉ I` forces `u ∈ I ∨ w ∈ I`; and if `u ∈ I`, `u' ∉ I` so `w ∈ I`, and vice versa!
                      have h_uw : u ∈ I ∨ w ∈ I := by
                        rcases hI'.2 v hvV hvI with hl | ⟨a, haI, hadj⟩
                        · exact absurd hl (hlp v hvV)
                        · have ha_nb : a ∈ G.nbhd V v := Finset.mem_filter.mpr
                            ⟨Finset.mem_erase.mpr ⟨fun h' => hvI (h' ▸ haI), hI'.1.1 haI⟩, G.symm _ _ hadj⟩
                          rw [hnb_v] at ha_nb
                          rcases Finset.mem_insert.mp ha_nb with rfl | ha'
                          · exact Or.inl haI
                          · exact Or.inr (Finset.mem_singleton.mp ha' ▸ haI)
                      have hu'I : u' ∉ I := by
                        rcases h_uw with huI | hwI
                        · exact fun h => hI'.1.2.2 u huI u' h hu'u.symm hadj_uu'
                        · exact fun h => hI'.1.2.2 u' h w hwI hu'w hadj_u'w
                      have huI : u ∈ I := by
                        by_contra h
                        rcases hI'.2 u huV h with hl | ⟨a, haI, hadj⟩
                        · exact hlp u huV hl
                        · have ha_nb : a ∈ G.nbhd V u := Finset.mem_filter.mpr
                            ⟨Finset.mem_erase.mpr ⟨fun h' => h (h' ▸ haI), hI'.1.1 haI⟩, G.symm _ _ hadj⟩
                          rw [hnb_u] at ha_nb
                          rcases Finset.mem_insert.mp ha_nb with rfl | ha'
                          · exact hvI haI
                          · exact hu'I (Finset.mem_singleton.mp ha' ▸ haI)
                      have hwI : w ∈ I := by
                        by_contra h
                        rcases hI'.2 w hwV h with hl | ⟨a, haI, hadj⟩
                        · exact hlp w hwV hl
                        · have ha_nb : a ∈ G.nbhd V w := Finset.mem_filter.mpr
                            ⟨Finset.mem_erase.mpr ⟨fun h' => h (h' ▸ haI), hI'.1.1 haI⟩, G.symm _ _ hadj⟩
                          rw [hnb_w] at ha_nb
                          rcases Finset.mem_insert.mp ha_nb with rfl | ha'
                          · exact hvI haI
                          · exact hu'I (Finset.mem_singleton.mp ha' ▸ haI)
                      ext x
                      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
                      constructor
                      · rintro ⟨hxI, rfl | rfl | rfl | rfl⟩
                        · exact absurd hxI hvI
                        · exact Or.inl rfl
                        · exact Or.inr rfl
                        · exact absurd hxI hu'I
                      · rintro (rfl | rfl)
                        · exact ⟨huI, Or.inr (Or.inl rfl)⟩
                        · exact ⟨hwI, Or.inr (Or.inr (Or.inl rfl))⟩
                -- Inject `G.misSet V` into `G.misSet (V \ {v,u,w,u'}) ×ˢ {{v, u'}, {u, w}}`
                have hcard_le : (G.misSet V).card ≤ 2 * (G.misSet (V \ {v, u, w, u'})).card := by
                  have hinj : (G.misSet V).card ≤
                      ((G.misSet (V \ {v, u, w, u'})) ×ˢ ({({v, u'} : Finset ℕ), {u, w}} : Finset (Finset ℕ))).card := by
                    refine Finset.card_le_card_of_injOn (fun I => (I \ {v, u, w, u'}, I ∩ {v, u, w, u'})) ?_ ?_
                    · intro I hI
                      obtain ⟨h1, h2⟩ := hmap I hI
                      exact Finset.mem_product.mpr ⟨h1, by rcases h2 with h2 | h2 <;> simp [h2]⟩
                    · intro I _ J _ heq
                      have h1 : I \ {v, u, w, u'} = J \ {v, u, w, u'} := congrArg Prod.fst heq
                      have h2 : I ∩ {v, u, w, u'} = J ∩ {v, u, w, u'} := congrArg Prod.snd heq
                      rw [← Finset.sdiff_union_inter I {v, u, w, u'},
                          ← Finset.sdiff_union_inter J {v, u, w, u'}, h1, h2]
                  have h2 : ({({v, u'} : Finset ℕ), {u, w}} : Finset (Finset ℕ)).card ≤ 2 :=
                    (Finset.card_insert_le _ _).trans (by simp)
                  calc (G.misSet V).card ≤ _ := hinj
                    _ = (G.misSet (V \ {v, u, w, u'})).card * ({({v, u'} : Finset ℕ), {u, w}} : Finset (Finset ℕ)).card :=
                        Finset.card_product _ _
                    _ ≤ (G.misSet (V \ {v, u, w, u'})).card * 2 := Nat.mul_le_mul_left _ h2
                    _ = 2 * (G.misSet (V \ {v, u, w, u'})).card := mul_comm _ _
                have hdiff : (V \ {v, u, w, u'}).card = n - 4 := by
                  rw [Finset.card_sdiff_of_subset hC4_sub, hn, hC4_card]
                have hih := ih _ (by omega) (V \ {v, u, w, u'}) (htf_sub _ Finset.sdiff_subset) rfl
                rw [hdiff, hrpow_sub 4 hn4] at hih
                have hR : ((G.misSet V).card : ℝ) ≤ 2 * ((G.misSet (V \ {v, u, w, u'})).card : ℝ) := by
                  exact_mod_cast hcard_le
                have h2m2 : (2 : ℝ) ^ (-(4 : ℕ) / 2 : ℝ) = 1 / 4 := by
                  have : -((4 : ℕ) : ℝ) / 2 = -(2 : ℕ) := by norm_num
                  rw [this, Real.rpow_neg (by norm_num), Real.rpow_natCast]; norm_num
                rw [h2m2] at hih
                nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((n : ℝ) / 2)]
              · -- `u' ≁ w`: extract `w`'s other neighbor `w'` (distinct from `v, u, w, u'`)
                have hv_nbw : v ∈ G.nbhd V w := Finset.mem_filter.mpr
                  ⟨Finset.mem_erase.mpr ⟨hwv.symm, hvV⟩, G.symm _ _ hadj_vw⟩
                have hw_er : ((G.nbhd V w).erase v).card = 1 := by
                  rw [Finset.card_erase_of_mem hv_nbw, hdeg2 w hwV]
                obtain ⟨w', hw'_eq⟩ := Finset.card_eq_one.mp hw_er
                have hw'_nb : w' ∈ (G.nbhd V w).erase v := hw'_eq ▸ Finset.mem_singleton_self w'
                have hw'v : w' ≠ v := (Finset.mem_erase.mp hw'_nb).1
                have hw'_nbw : w' ∈ G.nbhd V w := (Finset.mem_erase.mp hw'_nb).2
                have hw'w : w' ≠ w := (Finset.mem_erase.mp (Finset.mem_filter.mp hw'_nbw).1).1
                have hw'V : w' ∈ V := (Finset.mem_erase.mp (Finset.mem_filter.mp hw'_nbw).1).2
                have hadj_ww' : G.adj w w' := (Finset.mem_filter.mp hw'_nbw).2
                have hw'u : w' ≠ u := fun h => hna_uw (h ▸ G.symm _ _ hadj_ww')
                have hw'u' : w' ≠ u' := fun h => hadj_u'w (h ▸ G.symm _ _ hadj_ww')
                -- Partition `G.misSet V` into 3 cases:
                -- (1) `v ∈ I`, (2) `v ∉ I ∧ u ∈ I`, (3) `v ∉ I ∧ u ∉ I` (which forces `w ∈ I ∧ u' ∈ I`!)
                set S1 := (G.misSet V).filter (fun I => v ∈ I)
                set S2 := (G.misSet V).filter (fun I => v ∉ I ∧ u ∈ I)
                set S3 := (G.misSet V).filter (fun I => v ∉ I ∧ u ∉ I)
                have hcov : G.misSet V ⊆ S1 ∪ S2 ∪ S3 := by
                  intro I hI
                  by_cases hvI : v ∈ I
                  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hI, hvI⟩))
                  · by_cases huI : u ∈ I
                    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hI, hvI, huI⟩))
                    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hI, hvI, huI⟩)
                have hS1 : S1.card ≤ (G.misSet (V \ G.cnbhd V v)).card := G.card_misSet_filter_mem_le v
                have hS2 : S2.card ≤ (G.misSet (V \ G.cnbhd V u)).card :=
                  (Finset.card_le_card (fun I hI => Finset.mem_filter.mpr
                    ⟨(Finset.mem_filter.mp hI).1, (Finset.mem_filter.mp hI).2.2⟩)).trans
                    (G.card_misSet_filter_mem_le u)
                -- For `I ∈ S3`, `w ∈ I` and `u' ∈ I`, so `I \ {w, u'} ∈ G.misSet (V \ (G.cnbhd V w ∪ G.cnbhd V u'))`
                set Rem := G.cnbhd V w ∪ G.cnbhd V u'
                have h5_sub : ({v, u, w, u', w'} : Finset ℕ) ⊆ Rem := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl | rfl | rfl | rfl
                  · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hv_nbw)
                  · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
                      (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hu'u.symm, huV⟩, G.symm _ _ hadj_uu'⟩))
                  · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
                  · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
                  · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hw'_nbw)
                have hRem_sub : Rem ⊆ V := by
                  refine Finset.union_subset ?_ ?_
                  · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
                    · exact hwV
                    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
                  · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
                    · exact hu'V
                    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
                have h5_card : ({v, u, w, u', w'} : Finset ℕ).card = 5 := by
                  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
                      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                  · simp [hw'u'.symm]
                  · simp [hu'w.symm, hw'w.symm]
                  · simp [huw, hu'u.symm, hw'u.symm]
                  · simp [huv.symm, hwv.symm, hu'v.symm, hw'v.symm]
                have hRem_ge5 : 5 ≤ Rem.card := h5_card ▸ Finset.card_le_card h5_sub
                have hn5 : 5 ≤ n := by have := Finset.card_le_card hRem_sub; omega
                have hS3 : S3.card ≤ (G.misSet (V \ Rem)).card := by
                  refine Finset.card_le_card_of_injOn (fun I => (I.erase w).erase u') ?_ ?_
                  · intro I hI
                    obtain ⟨hImis, hvI, huI⟩ := Finset.mem_filter.mp hI
                    have hI' := (LGraph.isMIS_iff_maximal).mp (Finset.mem_filter.mp hImis).2
                    have hwI : w ∈ I := by
                      by_contra h
                      rcases hI'.2 v hvV hvI with hl | ⟨a, haI, hadj⟩
                      · exact hlp v hvV hl
                      · have ha_nb : a ∈ G.nbhd V v := Finset.mem_filter.mpr
                          ⟨Finset.mem_erase.mpr ⟨fun h' => hvI (h' ▸ haI), hI'.1.1 haI⟩, G.symm _ _ hadj⟩
                        rw [hnb_v] at ha_nb
                        rcases Finset.mem_insert.mp ha_nb with rfl | ha'
                        · exact huI haI
                        · exact h (Finset.mem_singleton.mp ha' ▸ haI)
                    have hu'I : u' ∈ I := by
                      by_contra h
                      rcases hI'.2 u huV huI with hl | ⟨a, haI, hadj⟩
                      · exact hlp u huV hl
                      · have ha_nb : a ∈ G.nbhd V u := Finset.mem_filter.mpr
                          ⟨Finset.mem_erase.mpr ⟨fun h' => huI (h' ▸ haI), hI'.1.1 haI⟩, G.symm _ _ hadj⟩
                        rw [hnb_u] at ha_nb
                        rcases Finset.mem_insert.mp ha_nb with rfl | ha'
                        · exact hvI haI
                        · exact h (Finset.mem_singleton.mp ha' ▸ haI)
                    -- Apply `erase_mem_misSet_sdiff_cnbhd` twice (first `w`, then `u'`)
                    have h1 := G.erase_mem_misSet_sdiff_cnbhd hImis hwI
                    have hu'I1 : u' ∈ I.erase w := Finset.mem_erase.mpr ⟨hu'w, hu'I⟩
                    have h2 := G.erase_mem_misSet_sdiff_cnbhd h1 hu'I1
                    -- Show `(V \ cnbhd V w) \ cnbhd (V \ cnbhd V w) u' = V \ Rem`
                    have hset_eq : (V \ G.cnbhd V w) \ G.cnbhd (V \ G.cnbhd V w) u' = V \ Rem := by
                      ext x
                      simp only [Rem, Finset.mem_sdiff, Finset.mem_union, LGraph.cnbhd, LGraph.nbhd,
                        Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
                      tauto
                    rwa [hset_eq] at h2
                  · intro I hI J hJ heq
                    obtain ⟨hImis, hvI, huI⟩ := Finset.mem_filter.mp hI
                    obtain ⟨hJmis, hvJ, huJ⟩ := Finset.mem_filter.mp hJ
                    have get_wu' : ∀ K, K ∈ G.misSet V → v ∉ K → u ∉ K → w ∈ K ∧ u' ∈ K := by
                      intro K hK hvK huK
                      have hK' := (LGraph.isMIS_iff_maximal).mp (Finset.mem_filter.mp hK).2
                      constructor
                      · by_contra h
                        rcases hK'.2 v hvV hvK with hl | ⟨a, haK, hadj⟩
                        · exact hlp v hvV hl
                        · have ha_nb : a ∈ G.nbhd V v := Finset.mem_filter.mpr
                            ⟨Finset.mem_erase.mpr ⟨fun h' => hvK (h' ▸ haK), hK'.1.1 haK⟩, G.symm _ _ hadj⟩
                          rw [hnb_v] at ha_nb
                          rcases Finset.mem_insert.mp ha_nb with rfl | ha'
                          · exact huK haK
                          · exact h (Finset.mem_singleton.mp ha' ▸ haK)
                      · by_contra h
                        rcases hK'.2 u huV huK with hl | ⟨a, haK, hadj⟩
                        · exact hlp u huV hl
                        · have ha_nb : a ∈ G.nbhd V u := Finset.mem_filter.mpr
                            ⟨Finset.mem_erase.mpr ⟨fun h' => huK (h' ▸ haK), hK'.1.1 haK⟩, G.symm _ _ hadj⟩
                          rw [hnb_u] at ha_nb
                          rcases Finset.mem_insert.mp ha_nb with rfl | ha'
                          · exact hvK haK
                          · exact h (Finset.mem_singleton.mp ha' ▸ haK)
                    obtain ⟨hwI, hu'I⟩ := get_wu' I hImis hvI huI
                    obtain ⟨hwJ, hu'J⟩ := get_wu' J hJmis hvJ huJ
                    have h1 : I.erase w = J.erase w := by
                      dsimp only at heq
                      rw [← Finset.insert_erase (Finset.mem_erase.mpr ⟨hu'w, hu'I⟩),
                          ← Finset.insert_erase (Finset.mem_erase.mpr ⟨hu'w, hu'J⟩), heq]
                    rw [← Finset.insert_erase hwI, ← Finset.insert_erase hwJ, h1]
                have hv_sub : G.cnbhd V v ⊆ V := by
                  intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
                  · exact hvV
                  · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
                have hu_sub : G.cnbhd V u ⊆ V := by
                  intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
                  · exact huV
                  · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
                have hv_c3 : (V \ G.cnbhd V v).card = n - 3 := by
                  rw [Finset.card_sdiff_of_subset hv_sub, LGraph.cnbhd,
                      Finset.card_insert_of_notMem (by simp [LGraph.nbhd]), hdeg2 v hvV, hn]
                have hu_c3 : (V \ G.cnbhd V u).card = n - 3 := by
                  rw [Finset.card_sdiff_of_subset hu_sub, LGraph.cnbhd,
                      Finset.card_insert_of_notMem (by simp [LGraph.nbhd]), hdeg2 u huV, hn]
                have hR_c5 : (V \ Rem).card ≤ n - 5 := by
                  rw [Finset.card_sdiff_of_subset hRem_sub, hn]; omega
                have hih1 := ih _ (by omega) (V \ G.cnbhd V v) (htf_sub _ Finset.sdiff_subset) rfl
                have hih2 := ih _ (by omega) (V \ G.cnbhd V u) (htf_sub _ Finset.sdiff_subset) rfl
                have hih3 := ih _ (by omega) (V \ Rem) (htf_sub _ Finset.sdiff_subset) rfl
                rw [hv_c3, hrpow_sub 3 (by omega)] at hih1
                rw [hu_c3, hrpow_sub 3 (by omega)] at hih2
                have h3eq : -((3 : ℕ) : ℝ) / 2 = -(3 : ℝ) / 2 := by norm_num
                rw [h3eq] at hih1 hih2
                have hb3 : ((G.misSet (V \ Rem)).card : ℝ) ≤
                    (2 : ℝ) ^ (-(5 : ℝ) / 2) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
                  have hr5 := hrpow_sub 5 hn5
                  have h5eq : -((5 : ℕ) : ℝ) / 2 = -(5 : ℝ) / 2 := by norm_num
                  rw [h5eq] at hr5
                  rw [← hr5]
                  exact hih3.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
                    have hR : ((V \ Rem).card : ℝ) ≤ ((n - 5 : ℕ) : ℝ) := by exact_mod_cast hR_c5
                    linarith))
                -- `2^(-3/2) + 2^(-3/2) + 2^(-5/2) = 5 / (4√2) < 1` (since `25 < 32`)!
                have hconst : (2 : ℝ) ^ (-(3 : ℝ) / 2) + (2 : ℝ) ^ (-(3 : ℝ) / 2) +
                    (2 : ℝ) ^ (-(5 : ℝ) / 2) ≤ 1 := by
                  have hhalf : (2 : ℝ) ^ (-(3 : ℝ) / 2) = 2 * (2 : ℝ) ^ (-(5 : ℝ) / 2) := by
                    rw [show (2 : ℝ) * (2 : ℝ) ^ (-(5 : ℝ) / 2) =
                        (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(5 : ℝ) / 2) by rw [Real.rpow_one],
                        ← Real.rpow_add (by norm_num)]
                    congr 1; norm_num
                  have hsq : ((2 : ℝ) ^ (-(5 : ℝ) / 2)) ^ 2 = 1 / 32 := by
                    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num)]
                    have : -(5 : ℝ) / 2 * (2 : ℕ) = -(5 : ℕ) := by push_cast; norm_num
                    rw [this, Real.rpow_neg (by norm_num), Real.rpow_natCast]; norm_num
                  have hpos : 0 ≤ (2 : ℝ) ^ (-(5 : ℝ) / 2) := by positivity
                  have h5 : 5 * (2 : ℝ) ^ (-(5 : ℝ) / 2) ≤ 1 := by nlinarith
                  linarith
                have hcard_tot : (G.misSet V).card ≤
                    (G.misSet (V \ G.cnbhd V v)).card + (G.misSet (V \ G.cnbhd V u)).card +
                    (G.misSet (V \ Rem)).card :=
                  (Finset.card_le_card hcov).trans <| (Finset.card_union_le _ _).trans <|
                    Nat.add_le_add ((Finset.card_union_le _ _).trans (Nat.add_le_add hS1 hS2)) hS3
                have hR : ((G.misSet V).card : ℝ) ≤
                    ((G.misSet (V \ G.cnbhd V v)).card : ℝ) + ((G.misSet (V \ G.cnbhd V u)).card : ℝ) +
                    ((G.misSet (V \ Rem)).card : ℝ) := by exact_mod_cast hcard_tot
                calc ((G.misSet V).card : ℝ)
                    ≤ ((2 : ℝ) ^ (-(3 : ℝ) / 2) + (2 : ℝ) ^ (-(3 : ℝ) / 2) + (2 : ℝ) ^ (-(5 : ℝ) / 2)) *
                        (2 : ℝ) ^ ((n : ℝ) / 2) := by nlinarith
                  _ ≤ 1 * (2 : ℝ) ^ ((n : ℝ) / 2) :=
                      mul_le_mul_of_nonneg_right hconst (by positivity)
                  _ = (2 : ℝ) ^ ((n : ℝ) / 2) := one_mul _
    · have hVe : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst hVe
      have hn0 : n = 0 := by simpa using hn.symm
      subst hn0
      have hcard : (G.misSet ∅).card ≤ 1 := by
        have hsub : G.misSet ∅ ⊆ {∅} := by
          intro I hI
          rw [Finset.subset_empty.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1)]
          exact Finset.mem_singleton_self ∅
        exact (Finset.card_le_card hsub).trans (by simp)
      have hR : ((G.misSet ∅).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      simpa using hR

/-- **BLST Lemma 2.3 (`lem-ht`)**: If `G[V \ T]` is triangle-free (with `T ⊆ V`), then
`|MIS(G[V])| ≤ 2 ^ (|V|/2 + |T|/2)`. -/
theorem hujter_tuza_with_triangles (G : LGraph) (V T : Finset ℕ) (hTV : T ⊆ V)
    (htf : G.IsTriangleFree (V \ T)) :
    ((G.misSet V).card : ℝ) ≤ (2 : ℝ) ^ (((V.card : ℝ) + (T.card : ℝ)) / 2) := by
  -- Group `I ∈ G.misSet V` by `S = I ∩ T ⊆ T`
  have hcov : G.misSet V ⊆ T.powerset.biUnion (fun S => (G.misSet V).filter (fun I => I ∩ T = S)) := by
    intro I hI
    exact Finset.mem_biUnion.mpr ⟨I ∩ T, Finset.mem_powerset.mpr Finset.inter_subset_right,
      Finset.mem_filter.mpr ⟨hI, rfl⟩⟩
  have hcard_le : (G.misSet V).card ≤
      ∑ S ∈ T.powerset, ((G.misSet V).filter (fun I => I ∩ T = S)).card :=
    (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  -- For fixed `S ⊆ T`, let `W = (V \ T).filter (fun x => ∀ s ∈ S, ¬ G.adj s x)`.
  -- If `I ∈ misSet V` and `I ∩ T = S`, then `I \ T ∈ misSet W`!
  have hfiber : ∀ S ∈ T.powerset,
      (((G.misSet V).filter (fun I => I ∩ T = S)).card : ℝ) ≤
        (2 : ℝ) ^ ((((V \ T).card : ℕ) : ℝ) / 2) := by
    intro S hS
    set W := (V \ T).filter (fun x => ∀ s ∈ S, ¬ G.adj s x)
    have hinj : ((G.misSet V).filter (fun I => I ∩ T = S)).card ≤ (G.misSet W).card := by
      refine Finset.card_le_card_of_injOn (fun I => I \ T) ?_ ?_
      · intro I hI
        rw [Finset.mem_coe] at hI ⊢
        dsimp only
        obtain ⟨hImis, hIT⟩ := Finset.mem_filter.mp hI
        have hI' := (LGraph.isMIS_iff_maximal).mp (Finset.mem_filter.mp hImis).2
        rw [LGraph.misSet, Finset.mem_filter, Finset.mem_powerset, LGraph.isMIS_iff_maximal]
        have hsub : I \ T ⊆ W := by
          intro x hx
          obtain ⟨hxI, hxT⟩ := Finset.mem_sdiff.mp hx
          refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hI'.1.1 hxI, hxT⟩, fun s hs => ?_⟩
          have hsI : s ∈ I := (Finset.mem_inter.mp (hIT.symm ▸ hs)).1
          have hsT : s ∈ T := (Finset.mem_inter.mp (hIT.symm ▸ hs)).2
          have hsx : s ≠ x := fun h => hxT (h ▸ hsT)
          exact hI'.1.2.2 s hsI x hxI hsx
        refine ⟨hsub, ⟨hsub, fun x hx => hI'.1.2.1 x (Finset.mem_sdiff.mp hx).1,
          fun x hx y hy hxy => hI'.1.2.2 x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).1 hxy⟩, ?_⟩
        intro x hxW hxIT
        have hxVT : x ∈ V \ T := (Finset.mem_filter.mp hxW).1
        have hxnoS : ∀ s ∈ S, ¬ G.adj s x := (Finset.mem_filter.mp hxW).2
        have hxI : x ∉ I := fun h => hxIT (Finset.mem_sdiff.mpr ⟨h, (Finset.mem_sdiff.mp hxVT).2⟩)
        rcases hI'.2 x (Finset.mem_sdiff.mp hxVT).1 hxI with hl | ⟨u, huI, hadj⟩
        · exact Or.inl hl
        · right
          have huT : u ∉ T := fun h => hxnoS u (hIT ▸ Finset.mem_inter.mpr ⟨huI, h⟩) hadj
          exact ⟨u, Finset.mem_sdiff.mpr ⟨huI, huT⟩, hadj⟩
      · intro I hI J hJ heq
        rw [Finset.mem_coe] at hI hJ
        dsimp only at heq
        have h1 : I ∩ T = S := (Finset.mem_filter.mp hI).2
        have h2 : J ∩ T = S := (Finset.mem_filter.mp hJ).2
        rw [← Finset.sdiff_union_inter I T, ← Finset.sdiff_union_inter J T, heq, h1, h2]
    have hW_tf : G.IsTriangleFree W := fun u hu v hv w hw =>
      htf u (Finset.filter_subset _ _ hu) v (Finset.filter_subset _ _ hv) w (Finset.filter_subset _ _ hw)
    have hht := hujter_tuza G W hW_tf
    have hWle : W.card ≤ (V \ T).card := Finset.card_le_card (Finset.filter_subset _ _)
    calc (((G.misSet V).filter (fun I => I ∩ T = S)).card : ℝ)
        ≤ ((G.misSet W).card : ℝ) := by exact_mod_cast hinj
      _ ≤ (2 : ℝ) ^ ((W.card : ℝ) / 2) := hht
      _ ≤ (2 : ℝ) ^ ((((V \ T).card : ℕ) : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            have hR : (W.card : ℝ) ≤ ((V \ T).card : ℝ) := by exact_mod_cast hWle
            linarith)
  have hsum : ((G.misSet V).card : ℝ) ≤
      (2 : ℝ) ^ T.card * (2 : ℝ) ^ ((((V \ T).card : ℕ) : ℝ) / 2) := by
    calc ((G.misSet V).card : ℝ)
        ≤ ∑ S ∈ T.powerset, (((G.misSet V).filter (fun I => I ∩ T = S)).card : ℝ) := by
          exact_mod_cast hcard_le
      _ ≤ ∑ _S ∈ T.powerset, (2 : ℝ) ^ ((((V \ T).card : ℕ) : ℝ) / 2) :=
          Finset.sum_le_sum hfiber
      _ = (2 : ℝ) ^ T.card * (2 : ℝ) ^ ((((V \ T).card : ℕ) : ℝ) / 2) := by
          rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc ((G.misSet V).card : ℝ)
      ≤ (2 : ℝ) ^ (T.card : ℝ) * (2 : ℝ) ^ ((((V \ T).card : ℕ) : ℝ) / 2) := by
        simpa [Real.rpow_natCast] using hsum
    _ = (2 : ℝ) ^ (((V.card : ℝ) + (T.card : ℝ)) / 2) := by
        rw [← Real.rpow_add (by norm_num), Finset.card_sdiff_of_subset hTV,
            Nat.cast_sub (Finset.card_le_card hTV)]
        congr 1; ring

/-- **Sapozhenko / Ilinca–Kahn (BLST Lemma 2.4)**:
Given `k ≥ 1`, `b ≥ 1`, and a graph `G[V]` with `δ ≤ deg(v) ≤ Δ` for all `v ∈ V` (with `2 * b ≤ δ`
and `Δ ≤ k * δ`):
`|MIS(G[V])| ≤ (∑_{i ≤ |V|/b} C(|V|, i)) * 3 ^ ((Δ * |V| / (δ + Δ - b)) / 3)`. -/
theorem sapozhenko_mis (G : LGraph) (V : Finset ℕ) (b δ Δ : ℕ)
    (hb : 1 ≤ b) (hδ : b < δ)
    (hmin : ∀ v ∈ V, δ ≤ G.deg V v) (hmax : ∀ v ∈ V, G.deg V v ≤ Δ) :
    ((G.misSet V).card : ℝ) ≤
      ((V.powerset.filter (fun S => S.card ≤ V.card / b)).card : ℝ) *
        (3 : ℝ) ^ (((Δ : ℝ) * (V.card : ℝ) / ((δ : ℝ) + (Δ : ℝ) - (b : ℝ))) / 3) := by
  -- Greedy extraction of a set `S ⊆ I` of size `≤ |V| / b` such that `I \ S ⊆ Z(S)` is a MIS of `G[Z(S)]`
  -- Define the canonical extraction step on `(U, S)` given `I`:
  -- While `∃ v ∈ U ∩ I, (G.nbhd U v).card ≥ b`, pick `v = (U ∩ I).filter (fun x => b ≤ (G.nbhd U x).card) |>.min'`,
  -- add `v` to `S`, and replace `U` by `U \ G.cnbhd U v`.
  -- Notice `U` is completely determined by `S`: `U = V \ S.biUnion (fun s => G.cnbhd V s)`!
  -- Wait: `I` is independent, so `v ∈ I` has NO neighbors in `S` and NO loop; so `U = V \ (S ∪ Γ_V(S))`!!
  let Uof (S : Finset ℕ) : Finset ℕ := V.filter (fun x => x ∉ S ∧ ∀ s ∈ S, ¬ G.adj s x)
  let Zof (S : Finset ℕ) : Finset ℕ :=
    (Uof S).filter (fun x => ¬ G.loop x ∧ (G.nbhd (Uof S) x).card < b)
  -- For any `I ∈ G.misSet V`, exist `S ⊆ I` with `|S| ≤ |V| / b` and `I \ S ∈ G.misSet (Zof S)`
  have hex_S : ∀ I ∈ G.misSet V, ∃ S ⊆ I, S.card ≤ V.card / b ∧ I \ S ∈ G.misSet (Zof S) := by
    intro I hI
    have hI' := (LGraph.isMIS_iff_maximal).mp (Finset.mem_filter.mp hI).2
    have hrec : ∀ m : ℕ, ∀ S : Finset ℕ, S ⊆ I → (Uof S).card = m →
        b * S.card ≤ V.card - (Uof S).card →
        ∃ S' ⊆ I, b * S'.card ≤ V.card ∧ I \ S' ⊆ Zof S' := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro S hSI hm hbudget
        by_cases hex : ∃ v ∈ I \ S, b ≤ (G.nbhd (Uof S) v).card
        · obtain ⟨v, hvIS, hvb⟩ := hex
          obtain ⟨hvI, hvS⟩ := Finset.mem_sdiff.mp hvIS
          have hvU : v ∈ Uof S := by
            refine Finset.mem_filter.mpr ⟨hI'.1.1 hvI, hvS, fun s hs => ?_⟩
            exact hI'.1.2.2 s (hSI hs) v hvI (fun h => hvS (h ▸ hs))
          let S1 := insert v S
          have hS1I : S1 ⊆ I := Finset.insert_subset_iff.mpr ⟨hvI, hSI⟩
          have hU1_eq : Uof S1 = Uof S \ G.cnbhd (Uof S) v := by
            ext x
            simp only [Uof, S1, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_insert,
              LGraph.cnbhd, LGraph.nbhd, Finset.mem_erase, not_or]
            constructor
            · rintro ⟨hxV, ⟨hxv, hxS⟩, hno⟩
              refine ⟨⟨hxV, hxS, fun s hs => hno s (Or.inr hs)⟩, hxv, ?_⟩
              rintro ⟨_, hadj⟩
              exact hno v (Or.inl rfl) hadj
            · rintro ⟨⟨hxV, hxS, hno⟩, hnot1, hnot2⟩
              refine ⟨hxV, ⟨hnot1, hxS⟩, fun s hs => ?_⟩
              rcases hs with rfl | hs
              · intro hadj
                exact hnot2 ⟨⟨hnot1, ⟨hxV, hxS, hno⟩⟩, hadj⟩
              · exact hno s hs
          have hc_sub : G.cnbhd (Uof S) v ⊆ Uof S := by
            intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact hvU
            · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx').1
          have hc_card : b + 1 ≤ (G.cnbhd (Uof S) v).card := by
            rw [LGraph.cnbhd, Finset.card_insert_of_notMem (by simp [LGraph.nbhd])]; omega
          have hU1_card : (Uof S1).card + (G.cnbhd (Uof S) v).card = (Uof S).card := by
            rw [hU1_eq]; exact Finset.card_sdiff_add_card_eq_card hc_sub
          have hlt : (Uof S1).card < m := by omega
          have hU_le_V : (Uof S).card ≤ V.card := Finset.card_le_card (Finset.filter_subset _ V)
          have hS1_card : S1.card = S.card + 1 := Finset.card_insert_of_notMem hvS
          have hbud1 : b * S1.card ≤ V.card - (Uof S1).card := by
            rw [hS1_card, Nat.mul_add, Nat.mul_one]
            omega
          exact ih (Uof S1).card hlt S1 hS1I rfl hbud1
        · push_neg at hex
          refine ⟨S, hSI, by omega, ?_⟩
          intro x hx
          obtain ⟨hxI, hxS⟩ := Finset.mem_sdiff.mp hx
          have hxU : x ∈ Uof S := Finset.mem_filter.mpr ⟨hI'.1.1 hxI, hxS, fun s hs =>
            hI'.1.2.2 s (hSI hs) x hxI (fun h => hxS (h ▸ hs))⟩
          exact Finset.mem_filter.mpr ⟨hxU, hI'.1.2.1 x hxI, hex x hx⟩
    obtain ⟨S, hSI, hbud, hsubZ⟩ := hrec (Uof ∅).card ∅ (Finset.empty_subset _) rfl (by simp)
    refine ⟨S, hSI, (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hbud), ?_⟩
    rw [LGraph.misSet, Finset.mem_filter, Finset.mem_powerset, LGraph.isMIS_iff_maximal]
    refine ⟨hsubZ, ⟨hsubZ, fun x hx => hI'.1.2.1 x (Finset.mem_sdiff.mp hx).1,
      fun x hx y hy hxy => hI'.1.2.2 x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).1 hxy⟩, ?_⟩
    intro x hxZ hxIS
    have hxU : x ∈ Uof S := (Finset.mem_filter.mp hxZ).1
    have hxV : x ∈ V := (Finset.mem_filter.mp hxU).1
    have hxS : x ∉ S := (Finset.mem_filter.mp hxU).2.1
    have hxnoS : ∀ s ∈ S, ¬ G.adj s x := (Finset.mem_filter.mp hxU).2.2
    have hxI : x ∉ I := fun h => hxIS (Finset.mem_sdiff.mpr ⟨h, hxS⟩)
    rcases hI'.2 x hxV hxI with hl | ⟨u, huI, hadj⟩
    · exact Or.inl hl
    · right
      have huS : u ∉ S := fun h => hxnoS u h hadj
      exact ⟨u, Finset.mem_sdiff.mpr ⟨huI, huS⟩, hadj⟩
  -- Degree-sum bound on `|Zof S|`
  have hZ_bound : ∀ S : Finset ℕ,
      ((Zof S).card : ℝ) ≤ (Δ : ℝ) * (V.card : ℝ) / ((δ : ℝ) + (Δ : ℝ) - (b : ℝ)) := by
    intro S
    set Z := Zof S
    have hZU : Z ⊆ Uof S := Finset.filter_subset _ _
    have hZV : Z ⊆ V := hZU.trans (Finset.filter_subset _ _)
    have hsum_deg : δ * Z.card ≤ b * Z.card + Δ * (V.card - Z.card) := by
      have h1 : δ * Z.card ≤ ∑ v ∈ Z, (G.nbhd V v).card := by
        calc δ * Z.card = ∑ _v ∈ Z, δ := by simp [mul_comm]
          _ ≤ ∑ v ∈ Z, G.deg V v := Finset.sum_le_sum fun v hv => hmin v (hZV hv)
          _ = ∑ v ∈ Z, (G.nbhd V v).card := by
              refine Finset.sum_congr rfl fun v hv => ?_
              have hnl : ¬ G.loop v := (Finset.mem_filter.mp hv).2.1
              simp [LGraph.deg, hnl]
      -- Split each `G.nbhd V v` into `Z` and `V \ Z`
      have hsplit : ∀ v ∈ Z, (G.nbhd V v).card ≤
          b + ((V \ Z).filter (G.adj v)).card := by
        intro v hv
        have hsub : G.nbhd V v ⊆ G.nbhd (Uof S) v ∪ (V \ Z).filter (G.adj v) := by
          intro w hw
          have hwV : w ∈ V := (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).2
          have hwv : w ≠ v := (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).1
          have hadj : G.adj v w := (Finset.mem_filter.mp hw).2
          by_cases hwZ : w ∈ Z
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
              ⟨Finset.mem_erase.mpr ⟨hwv, hZU hwZ⟩, hadj⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
              ⟨Finset.mem_sdiff.mpr ⟨hwV, hwZ⟩, hadj⟩)
        have hltb : (G.nbhd (Uof S) v).card < b := (Finset.mem_filter.mp hv).2.2
        have hu := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        omega
      -- Double-count edges between `Z` and `V \ Z`
      have hcross : ∑ v ∈ Z, ((V \ Z).filter (G.adj v)).card =
          ∑ w ∈ V \ Z, (Z.filter (G.adj w)).card := by
        simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
        by_cases h : G.adj v w
        · simp [h, G.symm v w h]
        · have h' : ¬ G.adj w v := fun h2 => h (G.symm w v h2)
          simp [h, h']
      have hcross_le : ∑ w ∈ V \ Z, (Z.filter (G.adj w)).card ≤ Δ * (V.card - Z.card) := by
        calc ∑ w ∈ V \ Z, (Z.filter (G.adj w)).card
            ≤ ∑ w ∈ V \ Z, G.deg V w := by
              apply Finset.sum_le_sum
              intro w hw
              have hwV : w ∈ V := (Finset.mem_sdiff.mp hw).1
              have hwZ : w ∉ Z := (Finset.mem_sdiff.mp hw).2
              have hsub : Z.filter (G.adj w) ⊆ G.nbhd V w := by
                intro v hv
                have hvZ : v ∈ Z := (Finset.mem_filter.mp hv).1
                have hadj : G.adj w v := (Finset.mem_filter.mp hv).2
                exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h => hwZ (h ▸ hvZ), hZV hvZ⟩, hadj⟩
              calc (Z.filter (G.adj w)).card ≤ (G.nbhd V w).card := Finset.card_le_card hsub
                _ ≤ G.deg V w := by dsimp [LGraph.deg]; omega
          _ ≤ ∑ _w ∈ V \ Z, Δ := Finset.sum_le_sum fun w hw => hmax w (Finset.mem_sdiff.mp hw).1
          _ = Δ * (V.card - Z.card) := by
              rw [Finset.sum_const, Finset.card_sdiff_of_subset hZV, smul_eq_mul, mul_comm]
      calc δ * Z.card ≤ ∑ v ∈ Z, (G.nbhd V v).card := h1
        _ ≤ ∑ v ∈ Z, (b + ((V \ Z).filter (G.adj v)).card) := Finset.sum_le_sum hsplit
        _ = b * Z.card + ∑ v ∈ Z, ((V \ Z).filter (G.adj v)).card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
        _ = b * Z.card + ∑ w ∈ V \ Z, (Z.filter (G.adj w)).card := by rw [hcross]
        _ ≤ b * Z.card + Δ * (V.card - Z.card) := Nat.add_le_add_left hcross_le _
    have hZleV : Z.card ≤ V.card := Finset.card_le_card hZV
    have hsumR : (δ : ℝ) * (Z.card : ℝ) ≤
        (b : ℝ) * (Z.card : ℝ) + (Δ : ℝ) * ((V.card : ℝ) - (Z.card : ℝ)) := by
      have h1 : ((δ * Z.card : ℕ) : ℝ) ≤ ((b * Z.card + Δ * (V.card - Z.card) : ℕ) : ℝ) := by
        exact_mod_cast hsum_deg
      push_cast [Nat.cast_sub hZleV] at h1
      exact h1
    have hden_pos : (0 : ℝ) < (δ : ℝ) + (Δ : ℝ) - (b : ℝ) := by
      have h1 : (b : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
      have h2 : (0 : ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg Δ
      linarith
    rw [le_div_iff₀ hden_pos]
    linarith
  -- Cover `G.misSet V` by pairs `(S, I \ S)` with `S ∈ Small`, `I \ S ∈ G.misSet (Zof S)`
  set Small := V.powerset.filter (fun S => S.card ≤ V.card / b)
  have hcov : G.misSet V ⊆ Small.biUnion (fun S => (G.misSet (Zof S)).image (fun R => S ∪ R)) := by
    intro I hI
    obtain ⟨S, hSI, hScard, hR⟩ := hex_S I hI
    have hSV : S ⊆ V := hSI.trans (Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1)
    refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSV, hScard⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨I \ S, hR, Finset.union_sdiff_of_subset hSI⟩
  have hcard_le : (G.misSet V).card ≤ ∑ S ∈ Small, (G.misSet (Zof S)).card :=
    (Finset.card_le_card hcov).trans <| Finset.card_biUnion_le.trans <|
      Finset.sum_le_sum fun S _ => Finset.card_image_le
  calc ((G.misSet V).card : ℝ)
      ≤ ∑ S ∈ Small, ((G.misSet (Zof S)).card : ℝ) := by exact_mod_cast hcard_le
    _ ≤ ∑ _S ∈ Small, (3 : ℝ) ^ (((Δ : ℝ) * (V.card : ℝ) / ((δ : ℝ) + (Δ : ℝ) - (b : ℝ))) / 3) := by
        apply Finset.sum_le_sum
        intro S _
        exact (moon_moser G (Zof S)).trans
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hZ_bound S]))
    _ = (Small.card : ℝ) * (3 : ℝ) ^ (((Δ : ℝ) * (V.card : ℝ) / ((δ : ℝ) + (Δ : ℝ) - (b : ℝ))) / 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end E877Graphs


namespace E877Container

open Finset Real
open scoped Classical

/-- Ordered Schur triples `(a, b)` with `a ∈ A`, `b ∈ A`, `a + b ∈ A`. -/
def schurTriples (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun p => p.1 + p.2 ∈ A)

/-- Predicate that `{x, y, z}` is a strict Schur triple (`x, y, z` pairwise distinct and one is the sum of the other two). -/
def IsSchur3 (x y z : ℕ) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ (x + y = z ∨ x + z = y ∨ y + z = x)

lemma isSchur3_symm12 {x y z : ℕ} (h : IsSchur3 x y z) : IsSchur3 y x z := by
  rcases h with ⟨h1, h2, h3, h4⟩
  refine ⟨h1.symm, h3, h2, ?_⟩
  rcases h4 with h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inl (by omega))

lemma isSchur3_symm23 {x y z : ℕ} (h : IsSchur3 x y z) : IsSchur3 x z y := by
  rcases h with ⟨h1, h2, h3, h4⟩
  refine ⟨h2, h1, h3.symm, ?_⟩
  rcases h4 with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (by omega))

/-- Codegree bound: for fixed `v` and `u`, at most 2 elements `w` satisfy `IsSchur3 v u w`. -/
lemma card_schur3_neighbors_le_two (A : Finset ℕ) (v u : ℕ) :
    (A.filter (fun w => IsSchur3 v u w)).card ≤ 2 := by
  by_cases hvu : v ≤ u
  · have hsub : A.filter (fun w => IsSchur3 v u w) ⊆ {v + u, u - v} := by
      intro w hw
      have h := (Finset.mem_filter.mp hw).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h.2.2.2 with h1 | h1 | h1 <;> omega
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
  · have hsub : A.filter (fun w => IsSchur3 v u w) ⊆ {v + u, v - u} := by
      intro w hw
      have h := (Finset.mem_filter.mp hw).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h.2.2.2 with h1 | h1 | h1 <;> omega
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))

/-- Number of ordered pairs `(u, w) ∈ A ×ˢ A` such that `IsSchur3 v u w`. -/
noncomputable def linkDeg (A : Finset ℕ) (v : ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun p => IsSchur3 v p.1 p.2)).card

/-- Number of ordered strict Schur triples `(v, u, w) ∈ A^3`. -/
noncomputable def strictSchurCount (A : Finset ℕ) : ℕ :=
  ∑ v ∈ A, linkDeg A v

/-- Link-multidegree of `u` in `A` with respect to `T₂`. -/
noncomputable def mdeg (A T₂ : Finset ℕ) (u : ℕ) : ℕ :=
  ∑ v ∈ T₂, (A.filter (fun w => IsSchur3 v u w)).card

/-- Total link-multidegree in `A` induced by `T₂`. -/
noncomputable def totalMdeg (A T₂ : Finset ℕ) : ℕ :=
  ∑ u ∈ A, mdeg A T₂ u

lemma totalMdeg_eq_sum_linkDeg (A T₂ : Finset ℕ) :
    totalMdeg A T₂ = ∑ v ∈ T₂, linkDeg A v := by
  dsimp [totalMdeg, mdeg, linkDeg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp_rw [Finset.card_filter]
  rw [Finset.sum_product]

lemma mdeg_mono {A₁ A₂ T₂ : Finset ℕ} (h : A₁ ⊆ A₂) (u : ℕ) :
    mdeg A₁ T₂ u ≤ mdeg A₂ T₂ u :=
  Finset.sum_le_sum fun v _ => Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma mdeg_insert_le (A T₂ : Finset ℕ) (v u : ℕ) :
    mdeg A (insert v T₂) u ≤ mdeg A T₂ u + 2 := by
  by_cases hv : v ∈ T₂
  · rw [Finset.insert_eq_of_mem hv]; omega
  · dsimp [mdeg]
    rw [Finset.sum_insert hv]
    have := card_schur3_neighbors_le_two A v u
    omega

lemma totalMdeg_erase_ge (A T₂ : Finset ℕ) (x : ℕ) (hx : x ∈ A) :
    totalMdeg A T₂ ≤ totalMdeg (A.erase x) T₂ + 2 * mdeg A T₂ x := by
  dsimp [totalMdeg, mdeg]
  have h1 : ∑ u ∈ A, ∑ v ∈ T₂, (A.filter (fun w => IsSchur3 v u w)).card =
      (∑ v ∈ T₂, (A.filter (fun w => IsSchur3 v x w)).card) +
      ∑ u ∈ A.erase x, ∑ v ∈ T₂, (A.filter (fun w => IsSchur3 v u w)).card := by
    rw [← Finset.add_sum_erase _ _ hx]
  rw [h1]
  have h2 : ∑ u ∈ A.erase x, ∑ v ∈ T₂, (A.filter (fun w => IsSchur3 v u w)).card ≤
      (∑ u ∈ A.erase x, ∑ v ∈ T₂, ((A.erase x).filter (fun w => IsSchur3 v u w)).card) +
      ∑ v ∈ T₂, (A.filter (fun w => IsSchur3 v x w)).card := by
    have hpt : ∀ u ∈ A.erase x, ∀ v ∈ T₂,
        (A.filter (fun w => IsSchur3 v u w)).card ≤
        ((A.erase x).filter (fun w => IsSchur3 v u w)).card + if IsSchur3 v u x then 1 else 0 := by
      intro u _ v _
      by_cases hp : IsSchur3 v u x
      · simp only [hp, if_true]
        have hsub : A.filter (fun w => IsSchur3 v u w) ⊆
            insert x ((A.erase x).filter (fun w => IsSchur3 v u w)) := by
          intro w hw
          obtain ⟨hwA, hwp⟩ := Finset.mem_filter.mp hw
          by_cases hwx : w = x
          · rw [hwx]; exact Finset.mem_insert_self x _
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwx, hwA⟩, hwp⟩)
        exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      · simp only [hp, if_false, add_zero]
        apply Finset.card_le_card
        intro w hw
        obtain ⟨hwA, hwp⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h => hp (h ▸ hwp), hwA⟩, hwp⟩
    have hsum1 := Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => hpt u hu v hv
    refine hsum1.trans ?_
    simp_rw [Finset.sum_add_distrib]
    apply Nat.add_le_add_left
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun v _ => ?_
    have hsub : (A.erase x).filter (fun u => IsSchur3 v u x) ⊆ A.filter (fun w => IsSchur3 v x w) := by
      intro u hu
      obtain ⟨huA, hup⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase huA, isSchur3_symm23 hup⟩
    rw [← Finset.card_filter]
    exact Finset.card_le_card hsub
  omega

lemma totalMdeg_sdiff_ge (A D T₂ : Finset ℕ) (M : ℕ)
    (hDA : D ⊆ A) (hM : ∀ u ∈ A, mdeg A T₂ u ≤ M) :
    totalMdeg A T₂ ≤ totalMdeg (A \ D) T₂ + 2 * M * D.card := by
  induction D using Finset.induction_on generalizing A with
  | empty => simp
  | @insert x D' hx ih =>
    have hxA : x ∈ A := hDA (Finset.mem_insert_self x D')
    have hD'sub : D' ⊆ A.erase x := fun y hy =>
      Finset.mem_erase.mpr ⟨fun h => hx (h ▸ hy), hDA (Finset.mem_insert_of_mem hy)⟩
    have hM' : ∀ u ∈ A.erase x, mdeg (A.erase x) T₂ u ≤ M := fun u hu =>
      (mdeg_mono (Finset.erase_subset x A) u).trans (hM u (Finset.mem_of_mem_erase hu))
    have hstep1 := totalMdeg_erase_ge A T₂ x hxA
    have hstep2 := ih (A.erase x) hD'sub hM'
    have hset : A.erase x \ D' = A \ insert x D' := by
      ext y; simp [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
    rw [hset] at hstep2
    have hmx : mdeg A T₂ x ≤ M := hM x hxA
    rw [Finset.card_insert_of_notMem hx]
    nlinarith

/-- Adding `v ∉ T₂` to `T₂` after erasing `v` from `A` adds `linkDeg A v` to `totalMdeg`. -/
lemma totalMdeg_insert_T₂_eq (A T₂ : Finset ℕ) (v : ℕ) (hvT₂ : v ∉ T₂) :
    totalMdeg (A.erase v) (insert v T₂) = totalMdeg (A.erase v) T₂ + linkDeg A v := by
  rw [totalMdeg_eq_sum_linkDeg, totalMdeg_eq_sum_linkDeg, Finset.sum_insert hvT₂, add_comm]
  congr 1
  dsimp [linkDeg]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_erase]
  constructor
  · rintro ⟨⟨⟨_, hp1⟩, ⟨_, hp2⟩⟩, hsch⟩
    exact ⟨⟨hp1, hp2⟩, hsch⟩
  · rintro ⟨⟨hp1, hp2⟩, hsch⟩
    exact ⟨⟨⟨hsch.1.symm, hp1⟩, ⟨hsch.2.1.symm, hp2⟩⟩, hsch⟩

/-- Deterministic BMS fingerprint-guided container algorithm for 3-uniform Schur triples. -/
noncomputable def bmsRun (d₂ thr : ℕ) (I : ℕ → Bool) :
    ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ × Finset ℕ × Finset ℕ
  | 0, A, T₁, T₂ => (A, T₁, T₂)
  | fuel + 1, A, T₁, T₂ =>
    if strictSchurCount A ≤ thr then
      (A, T₁, T₂)
    else
      let hi := A.filter (fun u => 2 * d₂ ≤ mdeg A T₂ u)
      if hhi : hi.Nonempty then
        let u := hi.min' hhi
        if I u then
          let nb := A.filter (fun w => w = u ∨ ∃ v ∈ T₂, IsSchur3 v u w)
          bmsRun d₂ thr I fuel (A \ nb) (insert u T₁) T₂
        else
          bmsRun d₂ thr I fuel (A.erase u) T₁ T₂
      else
        if hAne : A.Nonempty then
          let maxD := A.sup (linkDeg A)
          let cands := A.filter (fun v => linkDeg A v = maxD)
          if hc : cands.Nonempty then
            let v := cands.min' hc
            if I v then
              bmsRun d₂ thr I fuel (A.erase v) T₁ (insert v T₂)
            else
              bmsRun d₂ thr I fuel (A.erase v) T₁ T₂
          else (A, T₁, T₂)
        else (A, T₁, T₂)

set_option maxHeartbeats 800000 in
/-- Full specification of `bmsRun`: termination, container soundness, fingerprint size budgets,
and exact decoder determinism (`bmsRun` with `I' = (· ∈ T₁' ∪ T₂')` gives the identical output!). -/
lemma bmsRun_spec (d₂ thr n : ℕ) (hd₂ : 1 ≤ d₂) (hn : 1 ≤ n)
    (S : Finset ℕ) (hS_sf : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∀ fuel A T₁ T₂,
      A.card ≤ fuel →
      A ⊆ Finset.Icc 1 n →
      S ⊆ A ∪ T₁ ∪ T₂ →
      T₁ ⊆ S → T₂ ⊆ S →
      Disjoint A T₁ → Disjoint A T₂ →
      (∀ u ∈ A, mdeg A T₂ u ≤ 2 * d₂ + 1) →
      let res := bmsRun d₂ thr (fun x => decide (x ∈ S)) fuel A T₁ T₂
      let A' := res.1
      let T₁' := res.2.1
      let T₂' := res.2.2
      strictSchurCount A' ≤ thr ∧
      A' ⊆ A ∧
      S ⊆ A' ∪ T₁' ∪ T₂' ∧
      T₁ ⊆ T₁' ∧ T₂ ⊆ T₂' ∧
      T₁' ⊆ S ∧ T₂' ⊆ S ∧
      d₂ * (T₁'.card - T₁.card) ≤ A.card - A'.card ∧
      (thr / n) * (T₂'.card - T₂.card) + totalMdeg A T₂ ≤
        totalMdeg A' T₂' + 2 * (2 * d₂ + 1) * (A.card - A'.card) ∧
      (∀ u ∈ A', mdeg A' T₂' u ≤ 2 * d₂ + 1) ∧
      bmsRun d₂ thr (fun x => decide (x ∈ T₁' ∪ T₂')) fuel A T₁ T₂ = res := by
  intro fuel
  induction fuel with
  | zero =>
    intro A T₁ T₂ hle _ hScov hT₁S hT₂S _ _ hmdeg
    have hAe : A = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
    subst hAe
    simp only [Finset.empty_union] at hScov
    simp [bmsRun, strictSchurCount]
    exact ⟨hScov, hT₁S, hT₂S⟩
  | succ f ih =>
    intro A T₁ T₂ hle hAn hScov hT₁S hT₂S hAT₁ hAT₂ hmdeg
    dsimp only [bmsRun]
    by_cases hstop : strictSchurCount A ≤ thr
    · simp only [if_pos hstop]
      exact ⟨hstop, Subset.refl _, hScov, Subset.refl _, Subset.refl _, hT₁S, hT₂S,
        by simp, by simp, hmdeg, by simp⟩
    · simp only [if_neg hstop]
      set hi := A.filter (fun u => 2 * d₂ ≤ mdeg A T₂ u) with hhi_def
      by_cases hhi : hi.Nonempty
      · simp only [hhi, ↓reduceDIte]
        set u := hi.min' hhi with hu_def
        have hu_hi : u ∈ hi := Finset.min'_mem hi hhi
        have huA : u ∈ A := (Finset.mem_filter.mp hu_hi).1
        have hu_deg : 2 * d₂ ≤ mdeg A T₂ u := (Finset.mem_filter.mp hu_hi).2
        have hu_notT₁ : u ∉ T₁ := Finset.disjoint_left.mp hAT₁ huA
        have hu_notT₂ : u ∉ T₂ := Finset.disjoint_left.mp hAT₂ huA
        by_cases huS : u ∈ S
        · -- Case 1a: `u ∈ S`
          simp only [huS, decide_true, ↓reduceIte]
          set nb := A.filter (fun w => w = u ∨ ∃ v ∈ T₂, IsSchur3 v u w) with hnb_def
          have hnb_sub : nb ⊆ A := Finset.filter_subset _ A
          have hu_nb : u ∈ nb := Finset.mem_filter.mpr ⟨huA, Or.inl rfl⟩
          have hnb_ge : d₂ ≤ nb.card := by
            have h1 : mdeg A T₂ u ≤ ∑ w ∈ nb, (T₂.filter (fun v => IsSchur3 v u w)).card := by
              dsimp [mdeg]
              simp_rw [Finset.card_filter]
              rw [Finset.sum_comm]
              have hsub1 : ∑ w ∈ A, ∑ v ∈ T₂, (if IsSchur3 v u w then 1 else 0) =
                  ∑ w ∈ nb, ∑ v ∈ T₂, (if IsSchur3 v u w then 1 else 0) := by
                symm
                refine Finset.sum_subset hnb_sub fun w hwA hwnb => ?_
                refine Finset.sum_eq_zero fun v hvT₂ => ?_
                have hno : ¬ IsSchur3 v u w := fun h => hwnb (Finset.mem_filter.mpr ⟨hwA, Or.inr ⟨v, hvT₂, h⟩⟩)
                simp [hno]
              rw [hsub1]
            have h2 : ∑ w ∈ nb, (T₂.filter (fun v => IsSchur3 v u w)).card ≤ ∑ _w ∈ nb, 2 := by
              apply Finset.sum_le_sum
              intro w _
              have hsub2 : T₂.filter (fun v => IsSchur3 v u w) ⊆ T₂.filter (fun v => IsSchur3 u w v) := by
                intro v hv
                obtain ⟨hvT, hsch⟩ := Finset.mem_filter.mp hv
                exact Finset.mem_filter.mpr ⟨hvT, isSchur3_symm23 (isSchur3_symm12 hsch)⟩
              exact (Finset.card_le_card hsub2).trans (card_schur3_neighbors_le_two T₂ u w)
            rw [Finset.sum_const, smul_eq_mul] at h2
            omega
          have hnb_noS : ∀ w ∈ nb, w ∈ S → w = u := by
            intro w hwnb hwS
            rcases (Finset.mem_filter.mp hwnb).2 with rfl | ⟨v, hvT₂, hsch⟩
            · rfl
            · exfalso
              have hvS : v ∈ S := hT₂S hvT₂
              rcases hsch.2.2.2 with h | h | h
              · exact hS_sf v hvS u huS (h ▸ hwS)
              · exact hS_sf v hvS w hwS (h ▸ huS)
              · exact hS_sf u huS w hwS (h ▸ hvS)
          have hA1_card : (A \ nb).card + nb.card = A.card := Finset.card_sdiff_add_card_eq_card hnb_sub
          have hA1_le_f : (A \ nb).card ≤ f := by omega
          have hScov1 : S ⊆ (A \ nb) ∪ insert u T₁ ∪ T₂ := by
            intro x hxS
            have hx := hScov hxS
            simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert] at hx ⊢
            rcases hx with (hxA | hxT₁) | hxT₂
            · by_cases hxnb : x ∈ nb
              · exact Or.inl (Or.inr (Or.inl (hnb_noS x hxnb hxS)))
              · exact Or.inl (Or.inl ⟨hxA, hxnb⟩)
            · exact Or.inl (Or.inr (Or.inr hxT₁))
            · exact Or.inr hxT₂
          have hT₁1_S : insert u T₁ ⊆ S := Finset.insert_subset_iff.mpr ⟨huS, hT₁S⟩
          have hAT₁1 : Disjoint (A \ nb) (insert u T₁) := by
            rw [Finset.disjoint_left]
            intro x hx hx1
            have hxA : x ∈ A := (Finset.mem_sdiff.mp hx).1
            have hxnb : x ∉ nb := (Finset.mem_sdiff.mp hx).2
            rcases Finset.mem_insert.mp hx1 with rfl | hxT₁
            · exact hxnb hu_nb
            · exact Finset.disjoint_left.mp hAT₁ hxA hxT₁
          have hAT₂1 : Disjoint (A \ nb) T₂ := hAT₂.mono_left Finset.sdiff_subset
          have hmdeg1 : ∀ x ∈ A \ nb, mdeg (A \ nb) T₂ x ≤ 2 * d₂ + 1 := fun x hx =>
            (mdeg_mono Finset.sdiff_subset x).trans (hmdeg x (Finset.mem_sdiff.mp hx).1)
          have hrec := ih (A \ nb) (insert u T₁) T₂ hA1_le_f (Finset.sdiff_subset.trans hAn)
            hScov1 hT₁1_S hT₂S hAT₁1 hAT₂1 hmdeg1
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h9b, h10⟩ := hrec
          set res := bmsRun d₂ thr (fun x => decide (x ∈ S)) f (A \ nb) (insert u T₁) T₂
          have hT₁_sub : T₁ ⊆ res.2.1 := (Finset.subset_insert u T₁).trans h4
          have hT₁_c : (insert u T₁).card = T₁.card + 1 := Finset.card_insert_of_notMem hu_notT₁
          have hT₁_le : T₁.card + 1 ≤ res.2.1.card := hT₁_c ▸ Finset.card_le_card h4
          have hA'_le : res.1.card ≤ (A \ nb).card := Finset.card_le_card h2
          have hstep_mdeg := totalMdeg_sdiff_ge A nb T₂ (2 * d₂ + 1) hnb_sub hmdeg
          have hu_in_T : u ∈ res.2.1 ∪ res.2.2 := Finset.mem_union_left _ (h4 (Finset.mem_insert_self u T₁))
          refine ⟨h1, h2.trans Finset.sdiff_subset, h3, hT₁_sub, h5, h6, h7, ?_, ?_, h9b, ?_⟩
          · rw [hT₁_c] at h8
            have hsub1 : res.2.1.card - T₁.card = (res.2.1.card - (T₁.card + 1)) + 1 := by omega
            rw [hsub1, Nat.mul_add, Nat.mul_one]
            omega
          · have hdiff : A.card - res.1.card = ((A \ nb).card - res.1.card) + nb.card := by omega
            rw [hdiff, Nat.mul_add]
            omega
          · simp only [hu_in_T, decide_true, ↓reduceIte]
            exact h10
        · -- Case 1b: `u ∉ S`
          simp only [huS, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hA1_card : (A.erase u).card + 1 = A.card := by
            rw [Finset.card_erase_of_mem huA]
            have := Finset.card_pos.mpr ⟨u, huA⟩; omega
          have hA1_le_f : (A.erase u).card ≤ f := by omega
          have hScov1 : S ⊆ A.erase u ∪ T₁ ∪ T₂ := by
            intro x hxS
            have hx := hScov hxS
            simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
            rcases hx with (hxA | hxT₁) | hxT₂
            · exact Or.inl (Or.inl ⟨fun h => huS (h ▸ hxS), hxA⟩)
            · exact Or.inl (Or.inr hxT₁)
            · exact Or.inr hxT₂
          have hmdeg1 : ∀ x ∈ A.erase u, mdeg (A.erase u) T₂ x ≤ 2 * d₂ + 1 := fun x hx =>
            (mdeg_mono (Finset.erase_subset u A) x).trans (hmdeg x (Finset.mem_of_mem_erase hx))
          have hrec := ih (A.erase u) T₁ T₂ hA1_le_f ((Finset.erase_subset u A).trans hAn)
            hScov1 hT₁S hT₂S (hAT₁.mono_left (Finset.erase_subset u A))
            (hAT₂.mono_left (Finset.erase_subset u A)) hmdeg1
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h9b, h10⟩ := hrec
          set res := bmsRun d₂ thr (fun x => decide (x ∈ S)) f (A.erase u) T₁ T₂
          have hA'_le : res.1.card ≤ (A.erase u).card := Finset.card_le_card h2
          have hstep_mdeg := totalMdeg_erase_ge A T₂ u huA
          have hmu : mdeg A T₂ u ≤ 2 * d₂ + 1 := hmdeg u huA
          have hu_notT : u ∉ res.2.1 ∪ res.2.2 := by
            intro hu_mem
            rcases Finset.mem_union.mp hu_mem with h | h
            · exact huS (h6 h)
            · exact huS (h7 h)
          refine ⟨h1, h2.trans (Finset.erase_subset u A), h3, h4, h5, h6, h7, ?_, ?_, h9b, ?_⟩
          · omega
          · have hdiff : A.card - res.1.card = ((A.erase u).card - res.1.card) + 1 := by omega
            rw [hdiff, Nat.mul_add, Nat.mul_one]
            omega
          · simp only [hu_notT, decide_false, Bool.false_eq_true, ↓reduceIte]
            exact h10
      · -- Case 2: `hi` is empty, so `∀ u ∈ A, mdeg A T₂ u < 2 * d₂`!
        simp only [hhi, ↓reduceDIte]
        have hmdeg_lt : ∀ u ∈ A, mdeg A T₂ u < 2 * d₂ := by
          intro u huA
          by_contra hge
          exact hhi ⟨u, Finset.mem_filter.mpr ⟨huA, not_lt.mp hge⟩⟩
        have hAne : A.Nonempty := by
          by_contra h
          have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
          apply hstop; simp [hAe, strictSchurCount]
        simp only [hAne, ↓reduceDIte]
        set maxD := A.sup (linkDeg A) with hmaxD_def
        set cands := A.filter (fun v => linkDeg A v = maxD) with hcands_def
        have hc : cands.Nonempty := by
          obtain ⟨v, hvA, hvmax⟩ := A.exists_max_image (linkDeg A) hAne
          refine ⟨v, Finset.mem_filter.mpr ⟨hvA, le_antisymm (Finset.le_sup (f := linkDeg A) hvA) ?_⟩⟩
          exact Finset.sup_le fun w hw => hvmax w hw
        simp only [hc, ↓reduceDIte]
        set v := cands.min' hc with hv_def
        have hv_cands : v ∈ cands := Finset.min'_mem cands hc
        have hvA : v ∈ A := (Finset.mem_filter.mp hv_cands).1
        have hv_deg : linkDeg A v = maxD := (Finset.mem_filter.mp hv_cands).2
        have hv_notT₂ : v ∉ T₂ := Finset.disjoint_left.mp hAT₂ hvA
        -- Average degree bound: `strictSchurCount A ≤ A.card * maxD ≤ n * maxD`, so `thr / n ≤ maxD`!
        have hv_deg_ge : thr / n ≤ linkDeg A v := by
          have hsum_le : strictSchurCount A ≤ A.card * maxD := by
            dsimp [strictSchurCount]
            calc ∑ w ∈ A, linkDeg A w ≤ ∑ _w ∈ A, maxD :=
                  Finset.sum_le_sum fun w hw => Finset.le_sup (f := linkDeg A) hw
              _ = A.card * maxD := by rw [Finset.sum_const, smul_eq_mul]
          have hAn_card : A.card ≤ n := by
            have := Finset.card_le_card hAn; simpa using this
          have hlt : thr < n * maxD := by nlinarith
          rw [hv_deg]
          exact (Nat.div_le_iff_le_mul_add_pred (by omega)).mpr (by omega)
        have hA1_card : (A.erase v).card + 1 = A.card := by
          rw [Finset.card_erase_of_mem hvA]
          have := Finset.card_pos.mpr hAne; omega
        have hA1_le_f : (A.erase v).card ≤ f := by omega
        by_cases hvS : v ∈ S
        · -- Case 2a: `v ∈ S`, add `v` to `T₂`!
          simp only [hvS, decide_true, ↓reduceIte]
          have hScov1 : S ⊆ A.erase v ∪ T₁ ∪ insert v T₂ := by
            intro x hxS
            have hx := hScov hxS
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
            rcases hx with (hxA | hxT₁) | hxT₂
            · by_cases hxv : x = v
              · exact Or.inr (Or.inl hxv)
              · exact Or.inl (Or.inl ⟨hxv, hxA⟩)
            · exact Or.inl (Or.inr hxT₁)
            · exact Or.inr (Or.inr hxT₂)
          have hT₂1_S : insert v T₂ ⊆ S := Finset.insert_subset_iff.mpr ⟨hvS, hT₂S⟩
          have hAT₂1 : Disjoint (A.erase v) (insert v T₂) := by
            rw [Finset.disjoint_left]
            intro x hx hx1
            rcases Finset.mem_insert.mp hx1 with rfl | hxT₂
            · exact (Finset.mem_erase.mp hx).1 rfl
            · exact Finset.disjoint_left.mp hAT₂ (Finset.mem_of_mem_erase hx) hxT₂
          -- Key bound: since `mdeg A T₂ u < 2 * d₂` for all `u ∈ A`, adding `v` to `T₂` gives `≤ 2 * d₂ + 1`!
          have hmdeg1 : ∀ u ∈ A.erase v, mdeg (A.erase v) (insert v T₂) u ≤ 2 * d₂ + 1 := by
            intro u hu
            have h1 := mdeg_insert_le (A.erase v) T₂ v u
            have h2 := mdeg_mono (Finset.erase_subset v A) u (T₂ := T₂)
            have h3 := hmdeg_lt u (Finset.mem_of_mem_erase hu)
            omega
          have hrec := ih (A.erase v) T₁ (insert v T₂) hA1_le_f ((Finset.erase_subset v A).trans hAn)
            hScov1 hT₁S hT₂1_S (hAT₁.mono_left (Finset.erase_subset v A)) hAT₂1 hmdeg1
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h9b, h10⟩ := hrec
          set res := bmsRun d₂ thr (fun x => decide (x ∈ S)) f (A.erase v) T₁ (insert v T₂)
          have hT₂_sub : T₂ ⊆ res.2.2 := (Finset.subset_insert v T₂).trans h5
          have hT₂_c : (insert v T₂).card = T₂.card + 1 := Finset.card_insert_of_notMem hv_notT₂
          have hT₂_le : T₂.card + 1 ≤ res.2.2.card := hT₂_c ▸ Finset.card_le_card h5
          have hA'_le : res.1.card ≤ (A.erase v).card := Finset.card_le_card h2
          have hstep1 := totalMdeg_erase_ge A T₂ v hvA
          have hstep2 := totalMdeg_insert_T₂_eq A T₂ v hv_notT₂
          have hmv : mdeg A T₂ v ≤ 2 * d₂ + 1 := hmdeg v hvA
          have hv_in_T : v ∈ res.2.1 ∪ res.2.2 := Finset.mem_union_right _ (h5 (Finset.mem_insert_self v T₂))
          refine ⟨h1, h2.trans (Finset.erase_subset v A), h3, h4, hT₂_sub, h6, h7, ?_, ?_, h9b, ?_⟩
          · omega
          · rw [hT₂_c, hstep2] at h9
            have hsub2 : res.2.2.card - T₂.card = (res.2.2.card - (T₂.card + 1)) + 1 := by omega
            have hdiff : A.card - res.1.card = ((A.erase v).card - res.1.card) + 1 := by omega
            rw [hsub2, hdiff, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
            omega
          · simp only [hv_in_T, decide_true, ↓reduceIte]
            exact h10
        · -- Case 2b: `v ∉ S`
          simp only [hvS, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hScov1 : S ⊆ A.erase v ∪ T₁ ∪ T₂ := by
            intro x hxS
            have hx := hScov hxS
            simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
            rcases hx with (hxA | hxT₁) | hxT₂
            · exact Or.inl (Or.inl ⟨fun h => hvS (h ▸ hxS), hxA⟩)
            · exact Or.inl (Or.inr hxT₁)
            · exact Or.inr hxT₂
          have hmdeg1 : ∀ u ∈ A.erase v, mdeg (A.erase v) T₂ u ≤ 2 * d₂ + 1 := fun u hu =>
            (mdeg_mono (Finset.erase_subset v A) u).trans (hmdeg u (Finset.mem_of_mem_erase hu))
          have hrec := ih (A.erase v) T₁ T₂ hA1_le_f ((Finset.erase_subset v A).trans hAn)
            hScov1 hT₁S hT₂S (hAT₁.mono_left (Finset.erase_subset v A))
            (hAT₂.mono_left (Finset.erase_subset v A)) hmdeg1
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h9b, h10⟩ := hrec
          set res := bmsRun d₂ thr (fun x => decide (x ∈ S)) f (A.erase v) T₁ T₂
          have hA'_le : res.1.card ≤ (A.erase v).card := Finset.card_le_card h2
          have hstep1 := totalMdeg_erase_ge A T₂ v hvA
          have hmv : mdeg A T₂ v ≤ 2 * d₂ + 1 := hmdeg v hvA
          have hv_notT : v ∉ res.2.1 ∪ res.2.2 := by
            intro hv_mem
            rcases Finset.mem_union.mp hv_mem with h | h
            · exact hvS (h6 h)
            · exact hvS (h7 h)
          refine ⟨h1, h2.trans (Finset.erase_subset v A), h3, h4, h5, h6, h7, ?_, ?_, h9b, ?_⟩
          · omega
          · have hdiff : A.card - res.1.card = ((A.erase v).card - res.1.card) + 1 := by omega
            rw [hdiff, Nat.mul_add, Nat.mul_one]
            omega
          · simp only [hv_notT, decide_false, Bool.false_eq_true, ↓reduceIte]
            exact h10

/-- Relate `schurTriples A` (ordered `(a, b)` with `a + b ∈ A`) to `strictSchurCount A` plus diagonal triples. -/
lemma card_schurTriples_le_strictSchurCount (A : Finset ℕ) (h0 : 0 ∉ A) :
    (schurTriples A).card ≤ strictSchurCount A + A.card := by
  -- Split `schurTriples A` into `a = b` (at most `A.card`) and `a ≠ b` (injects into strict Schur triples `(a, b, a+b)`)
  have hpart : (schurTriples A).card =
      ((schurTriples A).filter (fun p => p.1 = p.2)).card +
      ((schurTriples A).filter (fun p => p.1 ≠ p.2)).card :=
    (Finset.card_filter_add_card_filter_not (s := schurTriples A) (p := fun p => p.1 = p.2)).symm
  rw [hpart, add_comm]
  apply Nat.add_le_add
  · -- Non-diagonal `(a, b)` maps into `Σ a ∈ A, (A ×ˢ A).filter (IsSchur3 a · ·)` via `(a, (b, a+b))`
    have hle : ((schurTriples A).filter (fun p => p.1 ≠ p.2)).card ≤
        (A.sigma (fun a => (A ×ˢ A).filter (fun q => IsSchur3 a q.1 q.2))).card := by
      refine Finset.card_le_card_of_injOn (fun p => ⟨p.1, (p.2, p.1 + p.2)⟩) ?_ ?_
      · intro p hp
        rw [Finset.mem_coe] at hp ⊢
        obtain ⟨hpS, hne⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpP, hsum⟩ := Finset.mem_filter.mp hpS
        obtain ⟨haA, hbA⟩ := Finset.mem_product.mp hpP
        have ha0 : p.1 ≠ 0 := fun h => h0 (h ▸ haA)
        have hb0 : p.2 ≠ 0 := fun h => h0 (h ▸ hbA)
        refine Finset.mem_sigma.mpr ⟨haA, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hbA, hsum⟩, ?_⟩⟩
        dsimp only
        exact ⟨hne, by omega, by omega, Or.inl rfl⟩
      · intro p1 _ p2 _ heq
        dsimp only at heq
        have h1 : p1.1 = p2.1 := congrArg Sigma.fst heq
        have h2 : p1.2 = p2.2 := by
          cases p1; cases p2; dsimp at h1 heq; subst h1
          have := eq_of_heq (Sigma.mk.inj heq).2
          exact congrArg Prod.fst this
        exact Prod.ext h1 h2
    rwa [Finset.card_sigma] at hle
  · -- Diagonal `(a, a)` injects into `A` via `Prod.fst`
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro p hp
      rw [Finset.mem_coe] at hp ⊢
      exact (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
    · intro p1 hp1 p2 hp2 heq
      rw [Finset.mem_coe] at hp1 hp2
      have h1 : p1.1 = p1.2 := (Finset.mem_filter.mp hp1).2
      have h2 : p2.1 = p2.2 := (Finset.mem_filter.mp hp2).2
      exact Prod.ext heq (by omega)

/-- Adding a small set `T` to `A` adds at most `3 * T.card * (A ∪ T).card` ordered Schur triples. -/
lemma card_schurTriples_union_le (A T : Finset ℕ) :
    (schurTriples (A ∪ T)).card ≤ (schurTriples A).card + 3 * T.card * (A ∪ T).card := by
  set U := A ∪ T
  have hcov : schurTriples U ⊆
      schurTriples A ∪
      (T ×ˢ U) ∪ (U ×ˢ T) ∪
      ((T ×ˢ U).image (fun p => (p.2, p.1 - p.2))) := by
    intro p hp
    obtain ⟨hpU, hsum⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpU
    by_cases h1 : p.1 ∈ T
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨h1, hp2⟩)))
    · by_cases h2 : p.2 ∈ T
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hp1, h2⟩))
      · by_cases h3 : p.1 + p.2 ∈ T
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨(p.1 + p.2, p.1), Finset.mem_product.mpr ⟨h3, hp1⟩, ?_⟩)
          exact Prod.ext rfl (by omega)
        · have h1A : p.1 ∈ A := (Finset.mem_union.mp hp1).resolve_right h1
          have h2A : p.2 ∈ A := (Finset.mem_union.mp hp2).resolve_right h2
          have h3A : p.1 + p.2 ∈ A := (Finset.mem_union.mp hsum).resolve_right h3
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1A, h2A⟩, h3A⟩)))
  have h1 := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have h2a := Finset.card_union_le (schurTriples A ∪ (T ×ˢ U)) (U ×ˢ T)
  have h2b := Finset.card_union_le (schurTriples A) (T ×ˢ U)
  have h3 : ((T ×ˢ U).image (fun p => (p.2, p.1 - p.2))).card ≤ T.card * U.card :=
    Finset.card_image_le.trans (by rw [Finset.card_product])
  have h4 : (T ×ˢ U).card = T.card * U.card := Finset.card_product _ _
  have h5 : (U ×ˢ T).card = U.card * T.card := Finset.card_product _ _
  nlinarith

/-- Elementary binomial tail bound (Chernoff / `(1 + x)^n`):
For `0 < x ≤ 1` and `k ≤ n`, `#({T ⊆ s | T.card ≤ k}) ≤ x ^ (-k) * (1 + x) ^ n`. -/
lemma card_powerset_card_le_chernoff (s : Finset ℕ) (k : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ((s.powerset.filter (fun T => T.card ≤ k)).card : ℝ) ≤
      x ^ (-(k : ℤ)) * (1 + x) ^ s.card := by
  have h1 : ∑ T ∈ s.powerset.filter (fun T => T.card ≤ k), x ^ k ≤
      ∑ T ∈ s.powerset, x ^ T.card := by
    calc ∑ T ∈ s.powerset.filter (fun T => T.card ≤ k), x ^ k
        ≤ ∑ T ∈ s.powerset.filter (fun T => T.card ≤ k), x ^ T.card := by
          apply Finset.sum_le_sum
          intro T hT
          exact pow_le_pow_of_le_one hx0.le hx1 (Finset.mem_filter.mp hT).2
      _ ≤ ∑ T ∈ s.powerset, x ^ T.card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
  have h2 : ∑ T ∈ s.powerset, x ^ T.card = (1 + x) ^ s.card := by
    have hbin : ∑ T ∈ s.powerset, x ^ T.card =
        ∑ i ∈ Finset.range (s.card + 1), (s.card.choose i : ℝ) * x ^ i := by
      simpa using (Finset.sum_powerset_apply_card (f := fun i => x ^ i) (x := s))
    rw [hbin, add_comm (1 : ℝ) x, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [Finset.sum_const, nsmul_eq_mul, h2] at h1
  have hxk_pos : 0 < x ^ k := pow_pos hx0 k
  calc ((s.powerset.filter (fun T => T.card ≤ k)).card : ℝ)
      = ((s.powerset.filter (fun T => T.card ≤ k)).card : ℝ) * x ^ k * (x ^ k)⁻¹ := by
        field_simp
    _ ≤ (1 + x) ^ s.card * (x ^ k)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = x ^ (-(k : ℤ)) * (1 + x) ^ s.card := by rw [zpow_neg, zpow_natCast, mul_comm]

/-- Corollary: for any `δ > 0`, there exists `α > 0` such that for all `n` and `s` with `s.card ≤ n`,
`#({T ⊆ s | T.card ≤ ⌊α n⌋}) ≤ 2 ^ (δ * n)`. -/
lemma exists_small_subset_exponent (δ : ℝ) (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ (n : ℕ) (s : Finset ℕ), s.card ≤ n →
      ∀ k : ℕ, (k : ℝ) ≤ α * (n : ℝ) →
      ((s.powerset.filter (fun T => T.card ≤ k)).card : ℝ) ≤ (2 : ℝ) ^ (δ * (n : ℝ)) := by
  -- Pick `x = min (1/2) (δ * log 2 / 4)` and `α = δ * log 2 / (4 * (-log x))`!
  set c := min (1 / 2 : ℝ) (δ * Real.log 2 / 4) with hc_def
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := lt_min (by norm_num) (by positivity)
  have hc_le_half : c ≤ 1 / 2 := min_le_left _ _
  have hc_le_δ : c ≤ δ * Real.log 2 / 4 := min_le_right _ _
  have hlogc_neg : Real.log c < 0 := Real.log_neg hc_pos (by linarith)
  set α := δ * Real.log 2 / (4 * (-Real.log c)) with hα_def
  have hα_pos : 0 < α := div_pos (by positivity) (by linarith)
  refine ⟨α, hα_pos, fun n s hsn k hk => ?_⟩
  have hch := card_powerset_card_le_chernoff s k c hc_pos (by linarith)
  -- Bound `c ^ (-k) * (1 + c) ^ s.card ≤ exp (k * (-log c) + n * c) ≤ exp (δ * log 2 * n) = 2 ^ (δ * n)`!
  have h1 : c ^ (-(k : ℤ)) = Real.exp ((k : ℝ) * (-Real.log c)) := by
    calc c ^ (-(k : ℤ)) = (c ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
      _ = ((Real.exp (Real.log c)) ^ k)⁻¹ := by rw [Real.exp_log hc_pos]
      _ = Real.exp ((k : ℝ) * (-Real.log c)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; ring
  have h2 : (1 + c) ^ s.card ≤ Real.exp ((n : ℝ) * c) := by
    have hstep : 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
    calc (1 + c) ^ s.card ≤ (Real.exp c) ^ s.card := pow_le_pow_left₀ (by linarith) hstep _
      _ = Real.exp ((s.card : ℝ) * c) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((n : ℝ) * c) := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hsn) hc_pos.le)
  have hexp_le : (k : ℝ) * (-Real.log c) + (n : ℝ) * c ≤ δ * Real.log 2 * (n : ℝ) := by
    have ht1 : (k : ℝ) * (-Real.log c) ≤ α * (n : ℝ) * (-Real.log c) :=
      mul_le_mul_of_nonneg_right hk (by linarith)
    have hlogc_ne : Real.log c ≠ 0 := ne_of_lt hlogc_neg
    have ht1' : α * (n : ℝ) * (-Real.log c) = δ * Real.log 2 / 4 * (n : ℝ) := by
      dsimp only [α]; field_simp [hlogc_ne]
    have ht2 : (n : ℝ) * c ≤ (n : ℝ) * (δ * Real.log 2 / 4) :=
      mul_le_mul_of_nonneg_left hc_le_δ (Nat.cast_nonneg n)
    have hnn : 0 ≤ δ * Real.log 2 * (n : ℝ) := by positivity
    linarith
  calc ((s.powerset.filter (fun T => T.card ≤ k)).card : ℝ)
      ≤ c ^ (-(k : ℤ)) * (1 + c) ^ s.card := hch
    _ ≤ Real.exp ((k : ℝ) * (-Real.log c)) * Real.exp ((n : ℝ) * c) := by
        rw [h1]; exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp ((k : ℝ) * (-Real.log c) + (n : ℝ) * c) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (δ * Real.log 2 * (n : ℝ)) := Real.exp_le_exp.mpr hexp_le
    _ = (2 : ℝ) ^ (δ * (n : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        congr 1; ring

set_option maxHeartbeats 800000 in
/-- **Sum-Free Container Lemma (Green 2004 / BMS 2015)** for `[1, n]`. -/
theorem schur_container (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ F : Finset (Finset ℕ),
        (F.card : ℝ) ≤ (2 : ℝ) ^ (δ * (n : ℝ)) ∧
        (∀ A ∈ F, A ⊆ Finset.Icc 1 n ∧ ((schurTriples A).card : ℝ) ≤ ε * (n : ℝ) ^ 2) ∧
        (∀ S ⊆ Finset.Icc 1 n, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → ∃ A ∈ F, S ⊆ A) := by
  obtain ⟨α, hα_pos, hα⟩ := exists_small_subset_exponent δ hδ
  -- Choose `d₂ : ℕ` large enough that `2 / d₂ ≤ α` and `12 / d₂ ≤ ε / 2`
  obtain ⟨d₂, hd₂_ge⟩ := exists_nat_ge (max (max (2 / α) (24 / ε)) 2)
  have hd₂_pos : 1 ≤ d₂ := by
    have : (2 : ℝ) ≤ (d₂ : ℝ) := (le_max_right _ _).trans hd₂_ge
    have : (2 : ℕ) ≤ d₂ := by exact_mod_cast this
    omega
  have hd₂_α : 2 / (d₂ : ℝ) ≤ α := by
    have h1 : 2 / α ≤ (d₂ : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hd₂_ge)
    have hdR : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast (show 0 < d₂ by omega)
    rw [div_le_iff₀ hdR]
    have := (div_le_iff₀ hα_pos).mp h1
    linarith
  have hd₂_ε : 24 / (d₂ : ℝ) ≤ ε := by
    have h1 : 24 / ε ≤ (d₂ : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hd₂_ge)
    have hdR : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast (show 0 < d₂ by omega)
    rw [div_le_iff₀ hdR]
    have := (div_le_iff₀ hε).mp h1
    linarith
  -- Choose `N₀` large enough so that `T₂` constant budget is `≤ n / d₂` and `1/n ≤ ε/4`
  set C₂ : ℝ := 48 * (2 * (d₂ : ℝ) + 1) / ε + 1
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max (max (C₂ * (d₂ : ℝ)) (16 / ε)) 10)
  filter_upwards [Filter.eventually_ge_atTop N₀] with n hn
  have hnR : max (max (C₂ * (d₂ : ℝ)) (16 / ε)) 10 ≤ (n : ℝ) := hN₀.trans (by exact_mod_cast hn)
  have hn10 : 10 ≤ n := by
    have : (10 : ℝ) ≤ (n : ℝ) := (le_max_right _ _).trans hnR
    exact_mod_cast this
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  set thr : ℕ := Nat.floor ((ε / 4) * (n : ℝ) ^ 2) with hthr_def
  have hthr_le : (thr : ℝ) ≤ (ε / 4) * (n : ℝ) ^ 2 := Nat.floor_le (by positivity)
  have hthr_ge : (ε / 8) * (n : ℝ) ^ 2 ≤ (thr : ℝ) := by
    have h1 : (ε / 4) * (n : ℝ) ^ 2 - 1 ≤ (thr : ℝ) := (Nat.sub_one_lt_floor _).le
    have h2 : 16 / ε ≤ (n : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hnR)
    have h3 : 16 ≤ ε * (n : ℝ) := by linarith [(div_le_iff₀ hε).mp h2]
    have hn10R : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10
    have h4 : 1 ≤ (ε / 8) * (n : ℝ) ^ 2 := by nlinarith
    linarith
  -- Bound `thr / n ≥ (ε / 16) * n`
  have hthrn_ge : (ε / 16) * (n : ℝ) ≤ ((thr / n : ℕ) : ℝ) := by
    have hdiv : (thr : ℝ) / (n : ℝ) - 1 ≤ ((thr / n : ℕ) : ℝ) := by
      have hnat : thr < (thr / n + 1) * n := by
        have := Nat.lt_div_mul_add (a := thr) (show 0 < n by omega)
        linarith
      have hR : (thr : ℝ) < (((thr / n : ℕ) : ℝ) + 1) * (n : ℝ) := by exact_mod_cast hnat
      rw [sub_le_iff_le_add]
      exact (div_le_iff₀ hn_pos).mpr hR.le
    have h2 : 16 / ε ≤ (n : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hnR)
    have h3 : 16 ≤ ε * (n : ℝ) := by linarith [(div_le_iff₀ hε).mp h2]
    have h4 : (ε / 8) * (n : ℝ) ≤ (thr : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hn_pos]; nlinarith
    linarith
  set kmax : ℕ := Nat.floor (α * (n : ℝ)) with hkmax_def
  set U := Finset.Icc 1 n
  have hUcard : U.card = n := by simp [U]
  -- Candidate fingerprints: subsets `T ⊆ Icc 1 n` of size `≤ kmax`
  set Seeds := U.powerset.filter (fun T => T.card ≤ kmax)
  -- Container decoder `decode T`: run `bmsRun d₂ thr (· ∈ T) n U ∅ ∅`, take `res.1 ∪ T`
  let decode (T : Finset ℕ) : Finset ℕ :=
    (bmsRun d₂ thr (fun x => decide (x ∈ T)) n U ∅ ∅).1 ∪ T
  -- Keep only decoded containers with `schurTriples ≤ ε n^2`
  set F := (Seeds.image decode).filter (fun A => ((schurTriples A).card : ℝ) ≤ ε * (n : ℝ) ^ 2)
  refine ⟨F, ?_, ?_, ?_⟩
  · -- `F.card ≤ Seeds.card ≤ 2 ^ (δ * n)`
    have h1 : F.card ≤ Seeds.card :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans Finset.card_image_le
    have h2 : (Seeds.card : ℝ) ≤ (2 : ℝ) ^ (δ * (n : ℝ)) :=
      hα n U (by rw [hUcard]) kmax (Nat.floor_le (by positivity))
    exact (by exact_mod_cast h1 : (F.card : ℝ) ≤ (Seeds.card : ℝ)).trans h2
  · -- Every `A ∈ F` is `⊆ Icc 1 n` and has `≤ ε n^2` Schur triples
    intro A hA
    obtain ⟨hAim, hAtri⟩ := Finset.mem_filter.mp hA
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hAim
    have hTU : T ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hres_sub : (bmsRun d₂ thr (fun x => decide (x ∈ T)) n U ∅ ∅).1 ⊆ U := by
      -- Prove `bmsRun` always returns a subset of its initial `A`!
      have hsub_gen : ∀ fuel A T₁ T₂, (bmsRun d₂ thr (fun x => decide (x ∈ T)) fuel A T₁ T₂).1 ⊆ A := by
        intro fuel
        induction fuel with
        | zero => intro A _ _; exact Subset.refl _
        | succ f ihf =>
          intro A T₁ T₂
          dsimp only [bmsRun]
          split_ifs
          · exact Subset.refl _
          · exact (ihf _ _ _).trans Finset.sdiff_subset
          · exact (ihf _ _ _).trans (Finset.erase_subset _ _)
          · exact (ihf _ _ _).trans (Finset.erase_subset _ _)
          · exact (ihf _ _ _).trans (Finset.erase_subset _ _)
          · exact Subset.refl _
          · exact Subset.refl _
      exact hsub_gen n U ∅ ∅
    exact ⟨Finset.union_subset hres_sub hTU, hAtri⟩
  · -- Every sum-free `S ⊆ Icc 1 n` is contained in some `A ∈ F`!
    intro S hSU hSsf
    have hspec := bmsRun_spec d₂ thr n hd₂_pos hn1 S hSsf n U ∅ ∅
      (by rw [hUcard]) (Subset.refl _) (by simpa using hSU) (Finset.empty_subset _)
      (Finset.empty_subset _) (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)
      (fun u _ => by simp [mdeg])
    obtain ⟨hstr, hA'U, hScov, _, _, hT₁S, hT₂S, hbud1, hbud2, hmdeg_end, hdec⟩ := hspec
    set res := bmsRun d₂ thr (fun x => decide (x ∈ S)) n U ∅ ∅
    set T := res.2.1 ∪ res.2.2
    -- Budget 1: `T₁.card ≤ n / d₂`
    have hT₁_le : (res.2.1.card : ℝ) ≤ (n : ℝ) / (d₂ : ℝ) := by
      simp only [Finset.card_empty, Nat.sub_zero] at hbud1
      have h1 : d₂ * res.2.1.card ≤ n := hbud1.trans (by rw [hUcard]; exact Nat.sub_le _ _)
      have hR : (d₂ : ℝ) * (res.2.1.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      have hdR : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast (show 0 < d₂ by omega)
      exact (le_div_iff₀ hdR).mpr (by linarith)
    -- Budget 2: `T₂.card ≤ C₂ ≤ n / d₂`
    have hT₂_le : (res.2.2.card : ℝ) ≤ (n : ℝ) / (d₂ : ℝ) := by
      have htot_end : totalMdeg res.1 res.2.2 ≤ (2 * d₂ + 1) * res.1.card := by
        dsimp [totalMdeg]
        calc ∑ u ∈ res.1, mdeg res.1 res.2.2 u ≤ ∑ _u ∈ res.1, (2 * d₂ + 1) :=
              Finset.sum_le_sum fun u hu => hmdeg_end u hu
          _ = res.1.card * (2 * d₂ + 1) := by rw [Finset.sum_const, smul_eq_mul]
          _ = (2 * d₂ + 1) * res.1.card := mul_comm _ _
      have hA'U_c : res.1.card ≤ n := by rw [← hUcard]; exact Finset.card_le_card hA'U
      have hbud2' : (thr / n) * res.2.2.card ≤ 3 * (2 * d₂ + 1) * n := by
        simp only [Finset.card_empty, Nat.sub_zero, totalMdeg, mdeg, Finset.sum_empty,
          Finset.sum_const_zero, add_zero] at hbud2
        have htot_le : ∑ u ∈ res.1, ∑ v ∈ res.2.2, (res.1.filter (fun w => IsSchur3 v u w)).card ≤
            (2 * d₂ + 1) * n := by
          calc _ = totalMdeg res.1 res.2.2 := rfl
            _ ≤ (2 * d₂ + 1) * res.1.card := htot_end
            _ ≤ (2 * d₂ + 1) * n := Nat.mul_le_mul_left _ hA'U_c
        have hdiff_le : U.card - res.1.card ≤ n := by rw [hUcard]; exact Nat.sub_le _ _
        have h2le : 2 * (2 * d₂ + 1) * (U.card - res.1.card) ≤ 2 * (2 * d₂ + 1) * n :=
          Nat.mul_le_mul_left _ hdiff_le
        have h3eq : (2 * d₂ + 1) * n + 2 * (2 * d₂ + 1) * n = 3 * (2 * d₂ + 1) * n := by ring
        linarith
      have hbud2R : ((thr / n : ℕ) : ℝ) * (res.2.2.card : ℝ) ≤ 3 * (2 * (d₂ : ℝ) + 1) * (n : ℝ) := by
        exact_mod_cast hbud2'
      have hmul : (ε / 16) * (n : ℝ) * (res.2.2.card : ℝ) ≤ 3 * (2 * (d₂ : ℝ) + 1) * (n : ℝ) := by
        calc (ε / 16) * (n : ℝ) * (res.2.2.card : ℝ)
            ≤ ((thr / n : ℕ) : ℝ) * (res.2.2.card : ℝ) :=
              mul_le_mul_of_nonneg_right hthrn_ge (Nat.cast_nonneg _)
          _ ≤ 3 * (2 * (d₂ : ℝ) + 1) * (n : ℝ) := hbud2R
      have hT₂_C₂ : (res.2.2.card : ℝ) ≤ C₂ := by
        have hcancel : (ε / 16) * (res.2.2.card : ℝ) ≤ 3 * (2 * (d₂ : ℝ) + 1) := by nlinarith
        have hdiv : (res.2.2.card : ℝ) ≤ 48 * (2 * (d₂ : ℝ) + 1) / ε := by
          rw [le_div_iff₀ hε]; linarith
        dsimp only [C₂]; linarith
      have hdR : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast (show 0 < d₂ by omega)
      have hC₂_le : C₂ * (d₂ : ℝ) ≤ (n : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hnR)
      exact hT₂_C₂.trans ((le_div_iff₀ hdR).mpr hC₂_le)
    -- Total fingerprint size `|T| ≤ 2 n / d₂ ≤ α n`, so `T ∈ Seeds`
    have hT_le_2 : (T.card : ℝ) ≤ 2 * (n : ℝ) / (d₂ : ℝ) := by
      have h1 : (T.card : ℝ) ≤ (res.2.1.card : ℝ) + (res.2.2.card : ℝ) := by
        exact_mod_cast Finset.card_union_le res.2.1 res.2.2
      have h2eq : (n : ℝ) / (d₂ : ℝ) + (n : ℝ) / (d₂ : ℝ) = 2 * (n : ℝ) / (d₂ : ℝ) := by ring
      linarith
    have hT_card_le : T.card ≤ kmax := by
      apply Nat.le_floor
      have h1 : 2 * (n : ℝ) / (d₂ : ℝ) = (2 / (d₂ : ℝ)) * (n : ℝ) := by ring
      calc (T.card : ℝ) ≤ (2 / (d₂ : ℝ)) * (n : ℝ) := h1 ▸ hT_le_2
        _ ≤ α * (n : ℝ) := mul_le_mul_of_nonneg_right hd₂_α hn_pos.le
    have hTU : T ⊆ U := Finset.union_subset (hT₁S.trans hSU) (hT₂S.trans hSU)
    have hT_mem : T ∈ Seeds := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTU, hT_card_le⟩
    -- Decoded container `A := decode T = res.1 ∪ T`
    have hdec_eq : decode T = res.1 ∪ T := by dsimp [decode]; rw [hdec]
    -- Show `schurTriples (decode T) ≤ ε * n^2`
    have htri_le : ((schurTriples (decode T)).card : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
      rw [hdec_eq]
      have h0A' : 0 ∉ res.1 := fun h => by
        have := (Finset.mem_Icc.mp (hA'U h)).1; omega
      have h1 : (schurTriples (res.1 ∪ T)).card ≤
          strictSchurCount res.1 + res.1.card + 3 * T.card * (res.1 ∪ T).card :=
        (card_schurTriples_union_le res.1 T).trans
          (Nat.add_le_add_right (card_schurTriples_le_strictSchurCount res.1 h0A') _)
      have hU1 : (res.1 ∪ T).card ≤ n := by
        rw [← hUcard]; exact Finset.card_le_card (Finset.union_subset hA'U hTU)
      have hA'n : res.1.card ≤ n := by rw [← hUcard]; exact Finset.card_le_card hA'U
      have h2 : ((schurTriples (res.1 ∪ T)).card : ℝ) ≤
          (thr : ℝ) + (n : ℝ) + 3 * (T.card : ℝ) * (n : ℝ) := by
        have hnat : (schurTriples (res.1 ∪ T)).card ≤ thr + n + 3 * T.card * n :=
          h1.trans (Nat.add_le_add (Nat.add_le_add hstr hA'n) (Nat.mul_le_mul_left _ hU1))
        exact_mod_cast hnat
      have hn_eps : (n : ℝ) ≤ (ε / 4) * (n : ℝ) ^ 2 := by
        have h16 : 16 / ε ≤ (n : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hnR)
        have h16' : 16 ≤ ε * (n : ℝ) := by linarith [(div_le_iff₀ hε).mp h16]
        nlinarith
      have h3T : 3 * (T.card : ℝ) * (n : ℝ) ≤ (ε / 4) * (n : ℝ) ^ 2 := by
        have h3a : 3 * (T.card : ℝ) ≤ 6 * (n : ℝ) / (d₂ : ℝ) := by
          have : 3 * (2 * (n : ℝ) / (d₂ : ℝ)) = 6 * (n : ℝ) / (d₂ : ℝ) := by ring
          linarith
        have h3b : 6 * (n : ℝ) / (d₂ : ℝ) = (6 / (d₂ : ℝ)) * (n : ℝ) := by ring
        have h3c : 6 / (d₂ : ℝ) ≤ ε / 4 := by
          have : 6 / (d₂ : ℝ) = (24 / (d₂ : ℝ)) / 4 := by ring
          linarith
        have h3d : 3 * (T.card : ℝ) ≤ (ε / 4) * (n : ℝ) := by
          calc 3 * (T.card : ℝ) ≤ (6 / (d₂ : ℝ)) * (n : ℝ) := h3b ▸ h3a
            _ ≤ (ε / 4) * (n : ℝ) := mul_le_mul_of_nonneg_right h3c hn_pos.le
        nlinarith
      linarith
    refine ⟨decode T, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨T, hT_mem, rfl⟩, htri_le⟩, ?_⟩
    rw [hdec_eq]
    intro x hxS
    have hx := hScov hxS
    simp only [T, Finset.mem_union] at hx ⊢
    tauto

end E877Container


namespace E877Structure

open Finset
open scoped Pointwise

/-! ## Part 1: Full Kneser's Theorem via Matt DeVos's short proof (arXiv:1303.3539) -/

/-- Additive stabilizer of a finite subset `C` of a finite abelian group `G`. -/
def addStab {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] (C : Finset G) : AddSubgroup G where
  carrier := {g : G | g +ᵥ C = C}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    show (a + b) +ᵥ C = C
    rw [add_vadd, hb, ha]
  neg_mem' {a} ha := by
    show (-a) +ᵥ C = C
    have h1 : (-a) +ᵥ (a +ᵥ C) = (-a) +ᵥ C := congrArg ((-a) +ᵥ ·) ha
    simpa [← add_vadd] using h1.symm

lemma mem_addStab_iff {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] {C : Finset G} {g : G} :
    g ∈ addStab C ↔ g +ᵥ C = C := Iff.rfl

/-- Finset of elements of an `AddSubgroup` in a finite abelian group. -/
noncomputable def subFinset {G : Type*} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) : Finset G :=
  letI := Classical.decPred (· ∈ H)
  Finset.univ.filter (fun x => x ∈ H)

lemma mem_subFinset {G : Type*} [AddCommGroup G] [Fintype G] {H : AddSubgroup G} {x : G} :
    x ∈ subFinset H ↔ x ∈ H := by
  simp [subFinset]

lemma subFinset_nonempty {G : Type*} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) :
    (subFinset H).Nonempty := ⟨0, mem_subFinset.mpr H.zero_mem⟩

lemma card_subFinset {G : Type*} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) :
    letI := Classical.decPred (· ∈ H)
    (subFinset H).card = Fintype.card H := by
  classical
  rw [subFinset, ← Fintype.card_subtype]

lemma card_subFinset_pos {G : Type*} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) :
    0 < (subFinset H).card := (subFinset_nonempty H).card_pos

lemma subFinset_bot {G : Type*} [AddCommGroup G] [Fintype G] :
    subFinset (⊥ : AddSubgroup G) = {0} := by
  ext x; simp [mem_subFinset]

lemma add_subFinset_bot {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] (A : Finset G) :
    A + subFinset (⊥ : AddSubgroup G) = A := by
  rw [subFinset_bot]
  ext x; simp [Finset.mem_add]

lemma subset_add_subFinset {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : Finset G) (H : AddSubgroup G) : A ⊆ A + subFinset H := by
  intro a ha
  exact Finset.mem_add.mpr ⟨a, ha, 0, mem_subFinset.mpr H.zero_mem, add_zero a⟩

lemma card_le_card_add_subFinset {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : Finset G) (H : AddSubgroup G) : A.card ≤ (A + subFinset H).card :=
  Finset.card_le_card (subset_add_subFinset A H)

lemma add_subFinset_mono {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : Finset G) {H₁ H₂ : AddSubgroup G} (hle : H₁ ≤ H₂) :
    A + subFinset H₁ ⊆ A + subFinset H₂ :=
  Finset.add_subset_add_left (fun _ hx => mem_subFinset.mpr (hle (mem_subFinset.mp hx)))

lemma add_subFinset_eq_self_of_le_addStab {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    {C : Finset G} {H : AddSubgroup G} (hle : H ≤ addStab C) :
    C + subFinset H = C := by
  apply Finset.Subset.antisymm _ (subset_add_subFinset C H)
  intro x hx
  obtain ⟨c, hc, h, hh, rfl⟩ := Finset.mem_add.mp hx
  have hstab : h +ᵥ C = C := mem_addStab_iff.mp (hle (mem_subFinset.mp hh))
  rw [← hstab]
  exact Finset.mem_vadd_finset.mpr ⟨c, hc, add_comm h c⟩

lemma card_add_subFinset_eq_quot {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : Finset G) (H : AddSubgroup G) [DecidableEq (G ⧸ H)] :
    (A + subFinset H).card = (A.image (QuotientAddGroup.mk' H)).card * (subFinset H).card := by
  set φ := QuotientAddGroup.mk' H
  have hmem : ∀ g : G, g ∈ A + subFinset H ↔ φ g ∈ A.image φ := by
    intro g
    constructor
    · intro hg
      obtain ⟨a, ha, h, hh, rfl⟩ := Finset.mem_add.mp hg
      refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
      have hh' : h ∈ H := mem_subFinset.mp hh
      have h0 : φ h = 0 := (QuotientAddGroup.eq_zero_iff h).mpr hh'
      rw [map_add, h0, add_zero]
    · intro hg
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hg
      have hdiff : g - a ∈ H := by
        rw [← QuotientAddGroup.eq_zero_iff]
        show φ (g - a) = 0
        rw [map_sub, heq, sub_self]
      exact Finset.mem_add.mpr ⟨a, ha, g - a, mem_subFinset.mpr hdiff, add_sub_cancel a g⟩
  have hfiber : ∀ q ∈ A.image φ,
      ((A + subFinset H).filter (fun g => φ g = q)).card = (subFinset H).card := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    have hset : (A + subFinset H).filter (fun g => φ g = φ a) = a +ᵥ subFinset H := by
      ext g
      simp only [Finset.mem_filter, hmem, Finset.mem_vadd_finset, mem_subFinset, vadd_eq_add]
      constructor
      · rintro ⟨_, hφ⟩
        have hdiff : g - a ∈ H := by
          rw [← QuotientAddGroup.eq_zero_iff]
          show φ (g - a) = 0
          rw [map_sub, hφ, sub_self]
        exact ⟨g - a, hdiff, add_sub_cancel a g⟩
      · rintro ⟨h, hh, rfl⟩
        have h0 : φ h = 0 := (QuotientAddGroup.eq_zero_iff h).mpr hh
        have hφ : φ (a + h) = φ a := by
          rw [map_add, h0, add_zero]
        exact ⟨hφ ▸ Finset.mem_image_of_mem φ ha, hφ⟩
    rw [hset, Finset.card_vadd_finset]
  have hpart := Finset.card_eq_sum_card_fiberwise (f := φ) (s := A + subFinset H) (t := A.image φ)
    (fun g hg => (hmem g).mp hg)
  rw [hpart, Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]

lemma card_subFinset_dvd_card_add_subFinset {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : Finset G) (H : AddSubgroup G) :
    (subFinset H).card ∣ (A + subFinset H).card := by
  letI := Classical.decEq (G ⧸ H)
  rw [card_add_subFinset_eq_quot]
  exact dvd_mul_left _ _

lemma card_subFinset_dvd_of_le {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    {H₁ H₂ : AddSubgroup G} (hle : H₁ ≤ H₂) :
    (subFinset H₁).card ∣ (subFinset H₂).card := by
  have heq : subFinset H₂ + subFinset H₁ = subFinset H₂ := by
    apply Finset.Subset.antisymm _ (subset_add_subFinset _ _)
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    exact mem_subFinset.mpr (H₂.add_mem (mem_subFinset.mp ha) (hle (mem_subFinset.mp hb)))
  rw [← heq]
  exact card_subFinset_dvd_card_add_subFinset _ _

lemma addStab_le_addStab_add {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] (A B : Finset G) :
    addStab B ≤ addStab (A + B) := by
  intro g hg
  rw [mem_addStab_iff] at hg ⊢
  rw [add_comm A B, ← vadd_add_assoc, hg, add_comm]

lemma addStab_vadd {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] (g : G) (C : Finset G) :
    addStab (g +ᵥ C) = addStab C := by
  ext x
  simp only [mem_addStab_iff]
  constructor
  · intro h
    have h1 : (-g) +ᵥ (x +ᵥ (g +ᵥ C)) = (-g) +ᵥ (g +ᵥ C) := congrArg ((-g) +ᵥ ·) h
    have h2 : (-g) +ᵥ (x +ᵥ (g +ᵥ C)) = x +ᵥ C := by
      rw [← add_vadd, ← add_vadd]; congr 1; abel
    have h3 : (-g) +ᵥ (g +ᵥ C) = C := by rw [← add_vadd, neg_add_cancel, zero_vadd]
    rw [← h2, h1, h3]
  · intro h
    rw [← add_vadd, add_comm x g, add_vadd, h]

lemma card_le_card_sdiff_add {α : Type*} [DecidableEq α] (s t : Finset α) :
    s.card ≤ (s \ t).card + t.card := by
  have h : s ⊆ (s \ t) ∪ t := fun x hx => by
    by_cases ht : x ∈ t
    · exact Finset.mem_union_right _ ht
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, ht⟩)
  exact (Finset.card_le_card h).trans (Finset.card_union_le _ _)

set_option maxHeartbeats 1200000 in
/-- **Full Kneser's Theorem** (DeVos 2014 short proof):
For nonempty `A, B : Finset G` in a finite abelian group `G` and `K = addStab (A + B)`:
`|A + K| + |B + K| ≤ |A + B| + |K|`. -/
theorem kneser_strong.{u} :
    ∀ m : ℕ, ∀ {G : Type u} [AddCommGroup G] [DecidableEq G] [Fintype G] (A B : Finset G),
      A.Nonempty → B.Nonempty → (A + B).card + A.card = m →
      let K := addStab (A + B)
      (A + subFinset K).card + (B + subFinset K).card ≤ (A + B).card + (subFinset K).card := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro G _ _ _ A B hA hB hm
    dsimp only
    set K := addStab (A + B) with hK_def
    -- Step 1: If `K ≠ ⊥`, pass to the quotient `G ⧸ K` and apply IH!
    by_cases hKbot : K ≠ ⊥
    · letI : DecidableEq (G ⧸ K) := Classical.decEq (G ⧸ K)
      letI : Fintype (G ⧸ K) := Fintype.ofFinite (G ⧸ K)
      set φ := QuotientAddGroup.mk' K
      have hKcard_ge2 : 2 ≤ (subFinset K).card := by
        have hne : ∃ g ∈ K, g ≠ 0 := by
          by_contra h
          push Not at h
          apply hKbot
          ext x; simp only [AddSubgroup.mem_bot]
          exact ⟨fun hx => h x hx, fun hx => hx ▸ K.zero_mem⟩
        obtain ⟨g, hgK, hg0⟩ := hne
        have hsub : ({0, g} : Finset G) ⊆ subFinset K := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact mem_subFinset.mpr K.zero_mem
          · exact mem_subFinset.mpr hgK
        have h2 : ({0, g} : Finset G).card = 2 := Finset.card_pair hg0.symm
        exact h2 ▸ Finset.card_le_card hsub
      have hAB_K : (A + B) + subFinset K = A + B :=
        add_subFinset_eq_self_of_le_addStab (le_refl K)
      have hAB_card : (A + B).card = ((A + B).image φ).card * (subFinset K).card := by
        conv_lhs => rw [← hAB_K]
        exact card_add_subFinset_eq_quot (A + B) K
      have himg_add : A.image φ + B.image φ = (A + B).image φ := by
        ext q
        simp only [Finset.mem_add, Finset.mem_image]
        constructor
        · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
          exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, map_add φ a b⟩
        · rintro ⟨x, ⟨a, ha, b, hb, rfl⟩, rfl⟩
          exact ⟨φ a, ⟨a, ha, rfl⟩, φ b, ⟨b, hb, rfl⟩, (map_add φ a b).symm⟩
      have hAB_pos : 0 < ((A + B).image φ).card := ((hA.add hB).image φ).card_pos
      have hlt : (A.image φ + B.image φ).card + (A.image φ).card < m := by
        rw [himg_add, ← hm, hAB_card]
        have h1 : (A.image φ).card ≤ A.card := Finset.card_image_le
        nlinarith
      have hstab_quot : addStab (A.image φ + B.image φ) = ⊥ := by
        ext q
        simp only [mem_addStab_iff, AddSubgroup.mem_bot]
        constructor
        · intro hq
          obtain ⟨g, rfl⟩ := QuotientAddGroup.mk'_surjective K q
          have hgK : g ∈ K := by
            rw [hK_def, mem_addStab_iff]
            apply Finset.eq_of_subset_of_card_le _ (by rw [Finset.card_vadd_finset])
            intro x hx
            obtain ⟨y, hy, rfl⟩ := Finset.mem_vadd_finset.mp hx
            have hmem1 : φ (g +ᵥ y) ∈ φ g +ᵥ (A.image φ + B.image φ) := by
              rw [himg_add]
              exact Finset.mem_vadd_finset.mpr ⟨φ y, Finset.mem_image_of_mem φ hy, by
                simp [vadd_eq_add, map_add]⟩
            change φ g +ᵥ (A.image φ + B.image φ) = A.image φ + B.image φ at hq
            rw [hq, himg_add] at hmem1
            obtain ⟨z, hz, hφ⟩ := Finset.mem_image.mp hmem1
            have hdiff : (g +ᵥ y) - z ∈ K := by
              rw [← QuotientAddGroup.eq_zero_iff]
              show φ ((g +ᵥ y) - z) = 0
              rw [map_sub, hφ, sub_self]
            rw [← hAB_K]
            exact Finset.mem_add.mpr ⟨z, hz, (g +ᵥ y) - z, mem_subFinset.mpr hdiff, add_sub_cancel z _⟩
          exact (QuotientAddGroup.eq_zero_iff g).mpr hgK
        · rintro rfl; rw [zero_vadd]
      have hih := ih ((A.image φ + B.image φ).card + (A.image φ).card) hlt
        (A.image φ) (B.image φ) (hA.image φ) (hB.image φ) rfl
      dsimp only at hih
      rw [hstab_quot, add_subFinset_bot, add_subFinset_bot, subFinset_bot, Finset.card_singleton] at hih
      rw [card_add_subFinset_eq_quot, card_add_subFinset_eq_quot, hAB_card, ← himg_add]
      nlinarith
    -- Step 2: Now `K = ⊥`!
    push Not at hKbot
    rw [hKbot, add_subFinset_bot, add_subFinset_bot, subFinset_bot, Finset.card_singleton]
    -- Base case `A.card = 1`
    by_cases hA1 : A.card ≤ 1
    · obtain ⟨a₀, ha₀⟩ := hA
      have hB_le : B.card ≤ (A + B).card := by
        calc B.card = (a₀ +ᵥ B).card := (Finset.card_vadd_finset a₀ B).symm
          _ ≤ (A + B).card := Finset.card_le_card fun x hx => by
              obtain ⟨b, hb, rfl⟩ := Finset.mem_vadd_finset.mp hx
              exact Finset.mem_add.mpr ⟨a₀, ha₀, b, hb, rfl⟩
      omega
    -- Now `A.card ≥ 2`: translate `B` so that `0 < |A ∩ B| < |A|`!
    have hA_gt1 : 1 < A.card := by omega
    obtain ⟨a₀, ha₀, a₁, ha₁, hne⟩ := Finset.one_lt_card.mp hA_gt1
    have hnotStabB : a₁ - a₀ ∉ addStab B := by
      intro hmem
      have h1 : a₁ - a₀ ∈ K := addStab_le_addStab_add A B hmem
      rw [hKbot, AddSubgroup.mem_bot] at h1
      exact hne (sub_eq_zero.mp h1).symm
    have hex_b : ∃ b₀ ∈ B, b₀ + (a₁ - a₀) ∉ B := by
      by_contra h
      push Not at h
      apply hnotStabB
      rw [mem_addStab_iff]
      apply Finset.eq_of_subset_of_card_le _ (by rw [Finset.card_vadd_finset])
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_vadd_finset.mp hx
      have := h b hb
      rwa [show (a₁ - a₀) +ᵥ b = b + (a₁ - a₀) by simp [vadd_eq_add, add_comm]]
    obtain ⟨b₀, hb₀, hb₀_not⟩ := hex_b
    -- Replace `B` by `B' := (a₀ - b₀) +ᵥ B`
    set B' := (a₀ - b₀) +ᵥ B with hB'_def
    have hB'_card : B'.card = B.card := Finset.card_vadd_finset _ B
    have hAB'_eq : A + B' = (a₀ - b₀) +ᵥ (A + B) := by
      rw [hB'_def, add_comm A, vadd_add_assoc, add_comm]
    have hAB'_card : (A + B').card = (A + B).card := by
      rw [hAB'_eq, Finset.card_vadd_finset]
    have hK'_bot : addStab (A + B') = ⊥ := by
      rw [hAB'_eq, addStab_vadd]; exact hKbot
    have hAB'_ne : (A ∩ B').Nonempty := by
      refine ⟨a₀, Finset.mem_inter.mpr ⟨ha₀, Finset.mem_vadd_finset.mpr ⟨b₀, hb₀, ?_⟩⟩⟩
      simp [vadd_eq_add]
    have ha₁_notB' : a₁ ∉ B' := by
      intro hmem
      obtain ⟨b, hb, heq⟩ := Finset.mem_vadd_finset.mp hmem
      have : b = b₀ + (a₁ - a₀) := by
        simp only [vadd_eq_add] at heq
        rw [← heq]; abel
      exact hb₀_not (this ▸ hb)
    have hAB'_ltA : (A ∩ B').card < A.card := by
      apply Finset.card_lt_card
      exact Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.inter_subset_left, fun h => ha₁_notB' ((Finset.mem_inter.mp (h.symm ▸ ha₁)).2)⟩
    -- Prove `A.card + B'.card ≤ (A + B').card + 1` (equivalent to goal!)
    suffices hstep : ∀ B : Finset G, B.Nonempty → (A + B).card + A.card = m →
        addStab (A + B) = ⊥ → (A ∩ B).Nonempty → (A ∩ B).card < A.card →
        A.card + B.card ≤ (A + B).card + 1 by
      have := hstep B' (hAB'_ne.mono Finset.inter_subset_right) (by omega) hK'_bot hAB'_ne hAB'_ltA
      omega
    intro B hB_ne hm' hK'_bot hAB'_ne hAB'_ltA
    -- Define convergents: nonempty `C ⊆ A + B` with `|A ∩ B| + |(A ∪ B) + H| ≤ |C| + |H|` (`H = addStab C`)
    let IsConv (C : Finset G) : Prop :=
      C.Nonempty ∧ C ⊆ A + B ∧
      (A ∩ B).card + ((A ∪ B) + subFinset (addStab C)).card ≤ C.card + (subFinset (addStab C)).card
    -- `C₀ = (A ∩ B) + (A ∪ B)` is a convergent!
    have hC₀_conv : IsConv ((A ∩ B) + (A ∪ B)) := by
      have hC₀_sub : (A ∩ B) + (A ∪ B) ⊆ A + B := by
        intro x hx
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
        obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
        rcases Finset.mem_union.mp hv with hvA | hvB
        · exact Finset.mem_add.mpr ⟨v, hvA, u, huB, add_comm v u⟩
        · exact Finset.mem_add.mpr ⟨u, huA, v, hvB, rfl⟩
      have hC₀_lt : ((A ∩ B) + (A ∪ B)).card + (A ∩ B).card < m := by
        have h1 : ((A ∩ B) + (A ∪ B)).card ≤ (A + B).card := Finset.card_le_card hC₀_sub
        omega
      have hih0 := ih _ hC₀_lt (A ∩ B) (A ∪ B) hAB'_ne (hA.mono Finset.subset_union_left) rfl
      refine ⟨hAB'_ne.add (hA.mono Finset.subset_union_left), hC₀_sub, ?_⟩
      have hle0 := card_le_card_add_subFinset (A ∩ B) (addStab ((A ∩ B) + (A ∪ B)))
      omega
    -- Choose a convergent `C` with minimal `(subFinset (addStab C)).card`!
    letI := Classical.decPred IsConv
    set Convs := (A + B).powerset.filter IsConv
    have hConvs_ne : Convs.Nonempty :=
      ⟨(A ∩ B) + (A ∪ B), Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC₀_conv.2.1, hC₀_conv⟩⟩
    obtain ⟨C, hC_mem, hC_min⟩ := Finset.exists_min_image Convs (fun D => (subFinset (addStab D)).card) hConvs_ne
    have hC_conv : IsConv C := (Finset.mem_filter.mp hC_mem).2
    obtain ⟨hC_ne, hC_sub, hC_ineq⟩ := hC_conv
    set H := addStab C with hH_def
    -- If `H = ⊥`, we are done immediately!
    by_cases hHbot : H = ⊥
    · rw [hHbot, add_subFinset_bot, subFinset_bot, Finset.card_singleton] at hC_ineq
      have hC_le : C.card ≤ (A + B).card := Finset.card_le_card hC_sub
      have hunion : (A ∪ B).card + (A ∩ B).card = A.card + B.card := Finset.card_union_add_card_inter A B
      omega
    -- Otherwise `H ≠ ⊥` (`|H| ≥ 2`); derive a contradiction!
    exfalso
    have hH_gt1 : 1 < (subFinset H).card := by
      have hne : ∃ g ∈ H, g ≠ 0 := by
        by_contra h; push Not at h; apply hHbot
        ext x; simp only [AddSubgroup.mem_bot]
        exact ⟨fun hx => h x hx, fun hx => hx ▸ H.zero_mem⟩
      obtain ⟨g, hgH, hg0⟩ := hne
      have hsub : ({0, g} : Finset G) ⊆ subFinset H := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_subFinset.mpr H.zero_mem
        · exact mem_subFinset.mpr hgH
      have h2 := Finset.card_pair hg0.symm
      have := Finset.card_le_card hsub
      omega
    -- `A + B` is NOT a convergent (since `addStab (A + B) = ⊥` has card `1 < |H|`)!
    have hAB_not_conv : (A + B).card + 1 < (A ∩ B).card + (A ∪ B).card := by
      by_contra hle
      push Not at hle
      have hmem : A + B ∈ Convs := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Subset.refl _),
          hA.add hB_ne, Subset.refl _, ?_⟩
        rw [hK'_bot, add_subFinset_bot, subFinset_bot, Finset.card_singleton]
        exact hle
      have hmin := hC_min (A + B) hmem
      rw [hK'_bot, subFinset_bot, Finset.card_singleton] at hmin
      omega
    -- Pick `a ∈ A, b ∈ B` such that `(a + b) +ᵥ subFinset H ⊄ A + B`!
    have hex_ab : ∃ a ∈ A, ∃ b ∈ B, ¬ ((a + b) +ᵥ subFinset H ⊆ A + B) := by
      by_contra h
      push Not at h
      have hHle : H ≤ addStab (A + B) := by
        intro g hg
        rw [mem_addStab_iff]
        apply Finset.eq_of_subset_of_card_le _ (by rw [Finset.card_vadd_finset])
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_vadd_finset.mp hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hy
        have hsub := h a ha b hb
        exact hsub (Finset.mem_vadd_finset.mpr ⟨g, mem_subFinset.mpr hg, by
          simp [vadd_eq_add]; abel⟩)
      rw [hK'_bot] at hHle
      exact hHbot (le_bot_iff.mp hHle)
    obtain ⟨a, haA, b, hbB, hab_not⟩ := hex_ab
    -- `C` is disjoint from `(a + b) +ᵥ subFinset H`!
    have hC_disj_coset : Disjoint C ((a + b) +ᵥ subFinset H) := by
      rw [Finset.disjoint_left]
      intro x hxC hxcos
      obtain ⟨h₀, hh₀, rfl⟩ := Finset.mem_vadd_finset.mp hxcos
      apply hab_not
      intro y hy
      obtain ⟨h₁, hh₁, rfl⟩ := Finset.mem_vadd_finset.mp hy
      have hdiff : h₁ - h₀ ∈ H := H.sub_mem (mem_subFinset.mp hh₁) (mem_subFinset.mp hh₀)
      have hstab : (h₁ - h₀) +ᵥ C = C := mem_addStab_iff.mp hdiff
      have hyC : (a + b) +ᵥ h₁ ∈ C := by
        rw [← hstab]
        refine Finset.mem_vadd_finset.mpr ⟨(a + b) +ᵥ h₀, hxC, ?_⟩
        simp only [vadd_eq_add]; abel
      exact hC_sub hyC
    -- Define `A₁, A₂, B₁, B₂`
    set A₁ := A ∩ (a +ᵥ subFinset H)
    set A₂ := A ∩ (b +ᵥ subFinset H)
    set B₁ := B ∩ (b +ᵥ subFinset H)
    set B₂ := B ∩ (a +ᵥ subFinset H)
    have hA₁_ne : A₁.Nonempty :=
      ⟨a, Finset.mem_inter.mpr ⟨haA, Finset.mem_vadd_finset.mpr ⟨0, mem_subFinset.mpr H.zero_mem, by simp⟩⟩⟩
    have hB₁_ne : B₁.Nonempty :=
      ⟨b, Finset.mem_inter.mpr ⟨hbB, Finset.mem_vadd_finset.mpr ⟨0, mem_subFinset.mpr H.zero_mem, by simp⟩⟩⟩
    -- Key lemma for `(X, Y)` with `X ⊆ A`, `Y ⊆ B`, `X, Y` nonempty, and `X + Y ⊆ (a + b) +ᵥ subFinset H`:
    -- Gives `H' = addStab (X + Y) < H`, `addStab (C ∪ (X + Y)) = H'`, and DeVos's equations (1), (2), (3)!
    have hdevos_pair : ∀ (X Y : Finset G), X ⊆ A → Y ⊆ B → X.Nonempty → Y.Nonempty →
        X + Y ⊆ (a + b) +ᵥ subFinset H →
        let H' := addStab (X + Y)
        H' ≤ H ∧
        (subFinset H').card < (subFinset H).card ∧
        ((A ∪ B) + subFinset H).card + (X + subFinset H').card + (Y + subFinset H').card <
          ((A ∪ B) + subFinset H').card + (subFinset H).card ∧
        X.card + Y.card + (subFinset H').card ≤ (subFinset H).card ∧
        ((A ∪ B) + subFinset H).card + X.card + Y.card <
          (A ∪ B).card + (subFinset H).card + (subFinset H').card := by
      intro X Y hXA hYB hXne hYne hXYcos
      dsimp only
      set H' := addStab (X + Y) with hH'_def
      have hXY_sub_AB : X + Y ⊆ A + B := Finset.add_subset_add hXA hYB
      have hXY_disj_C : Disjoint C (X + Y) := hC_disj_coset.mono_right hXYcos
      have hXY_ne_cos : X + Y ≠ (a + b) +ᵥ subFinset H := fun h => hab_not (h ▸ hXY_sub_AB)
      -- `H' ≤ H` and `|H'| < |H|`
      have hH'_le_H : H' ≤ H := by
        intro g hg
        obtain ⟨z, hz⟩ := hXne.add hYne
        have hgz : g +ᵥ z ∈ X + Y := by
          have := mem_addStab_iff.mp hg
          rw [← this]; exact Finset.mem_vadd_finset.mpr ⟨z, hz, rfl⟩
        obtain ⟨h₁, hh₁, hz_eq⟩ := Finset.mem_vadd_finset.mp (hXYcos hz)
        obtain ⟨h₂, hh₂, hgz_eq⟩ := Finset.mem_vadd_finset.mp (hXYcos hgz)
        have hg_eq : g = h₂ - h₁ := by
          simp only [vadd_eq_add] at hz_eq hgz_eq
          rw [← hz_eq] at hgz_eq
          have hsub_eq : g = (a + b + h₂) - (a + b + h₁) := eq_sub_of_add_eq hgz_eq.symm
          rw [hsub_eq]; abel
        rw [hg_eq]
        exact H.sub_mem (mem_subFinset.mp hh₂) (mem_subFinset.mp hh₁)
      have hH'_lt_H : (subFinset H').card < (subFinset H).card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨fun x hx => mem_subFinset.mpr (hH'_le_H (mem_subFinset.mp hx)), ?_⟩
        intro heq
        apply hXY_ne_cos
        apply Finset.Subset.antisymm hXYcos
        obtain ⟨z, hz⟩ := hXne.add hYne
        obtain ⟨h₀, hh₀, rfl⟩ := Finset.mem_vadd_finset.mp (hXYcos hz)
        intro y hy
        obtain ⟨h₁, hh₁, rfl⟩ := Finset.mem_vadd_finset.mp hy
        have hdiff : h₁ - h₀ ∈ H' :=
          mem_subFinset.mp (heq ▸ mem_subFinset.mpr (H.sub_mem (mem_subFinset.mp hh₁) (mem_subFinset.mp hh₀)))
        have hstab : (h₁ - h₀) +ᵥ (X + Y) = X + Y := mem_addStab_iff.mp hdiff
        rw [← hstab]
        refine Finset.mem_vadd_finset.mpr ⟨(a + b) +ᵥ h₀, hz, ?_⟩
        simp only [vadd_eq_add]; abel
      -- `addStab (C ∪ (X + Y)) = H'`
      have hstab_Ci : addStab (C ∪ (X + Y)) = H' := by
        ext g
        simp only [mem_addStab_iff]
        constructor
        · intro hg
          have hgH : g ∈ H := by
            by_contra hgnotH
            -- `g +ᵥ (X + Y)` is disjoint from `(a + b) +ᵥ subFinset H`, hence `⊆ C`!
            obtain ⟨z, hz⟩ := hXne.add hYne
            obtain ⟨h₀, hh₀, hz_eq⟩ := Finset.mem_vadd_finset.mp (hXYcos hz)
            have hgz_mem : g +ᵥ z ∈ C ∪ (X + Y) := by
              rw [← hg]; exact Finset.mem_vadd_finset.mpr ⟨z, Finset.mem_union_right _ hz, rfl⟩
            have hgz_not_cos : g +ᵥ z ∉ (a + b) +ᵥ subFinset H := by
              intro hmem
              obtain ⟨h₁, hh₁, heq1⟩ := Finset.mem_vadd_finset.mp hmem
              apply hgnotH
              have : g = h₁ - h₀ := by
                simp only [vadd_eq_add] at hz_eq heq1
                rw [← hz_eq] at heq1
                have hsub_eq : g = (a + b + h₁) - (a + b + h₀) := eq_sub_of_add_eq heq1.symm
                rw [hsub_eq]; abel
              rw [this]; exact H.sub_mem (mem_subFinset.mp hh₁) (mem_subFinset.mp hh₀)
            have hgzC : g +ᵥ z ∈ C :=
              (Finset.mem_union.mp hgz_mem).resolve_right (fun h => hgz_not_cos (hXYcos h))
            -- Therefore `g +ᵥ ((a + b) +ᵥ subFinset H) ⊆ C`!
            -- Then `(-g) +ᵥ (g +ᵥ ((a + b) +ᵥ subFinset H)) = (a + b) +ᵥ subFinset H ⊆ C ∪ (X + Y)`,
            -- contradicting `hC_disj_coset` and `hXY_ne_cos`!
            apply hXY_ne_cos
            apply Finset.Subset.antisymm hXYcos
            intro y hy
            obtain ⟨h₁, hh₁, rfl⟩ := Finset.mem_vadd_finset.mp hy
            have hgyC : g +ᵥ ((a + b) +ᵥ h₁) ∈ C := by
              have hdiff : h₁ - h₀ ∈ H := H.sub_mem (mem_subFinset.mp hh₁) (mem_subFinset.mp hh₀)
              have hst : (h₁ - h₀) +ᵥ C = C := mem_addStab_iff.mp hdiff
              rw [← hst]
              refine Finset.mem_vadd_finset.mpr ⟨g +ᵥ z, hgzC, ?_⟩
              simp only [vadd_eq_add] at hz_eq ⊢
              rw [← hz_eq]; abel
            have hng : (-g) +ᵥ (C ∪ (X + Y)) = C ∪ (X + Y) :=
              mem_addStab_iff.mp ((addStab (C ∪ (X + Y))).neg_mem (mem_addStab_iff.mpr hg))
            have hyCi : (a + b) +ᵥ h₁ ∈ C ∪ (X + Y) := by
              rw [← hng]
              refine Finset.mem_vadd_finset.mpr ⟨g +ᵥ ((a + b) +ᵥ h₁), Finset.mem_union_left _ hgyC, ?_⟩
              simp only [vadd_eq_add]; abel
            exact (Finset.mem_union.mp hyCi).resolve_left
              (fun hc => Finset.disjoint_left.mp hC_disj_coset hc hy)
          -- Now `g ∈ H`, so `g +ᵥ C = C` and `g +ᵥ (X + Y) = X + Y`!
          have hgC : g +ᵥ C = C := mem_addStab_iff.mp hgH
          rw [Finset.vadd_finset_union, hgC] at hg
          ext x
          constructor
          · intro hx
            have hx1 : x ∈ C ∪ (X + Y) := by rw [← hg]; exact Finset.mem_union_right _ hx
            have hxnotC : x ∉ C := by
              intro hxC
              obtain ⟨y, hy, rfl⟩ := Finset.mem_vadd_finset.mp hx
              have hyC : y ∈ C := by
                have hngC : (-g) +ᵥ C = C := mem_addStab_iff.mp (H.neg_mem hgH)
                rw [← hngC]
                exact Finset.mem_vadd_finset.mpr ⟨g +ᵥ y, hxC, by simp [vadd_eq_add]⟩
              exact Finset.disjoint_left.mp hXY_disj_C hyC hy
            exact (Finset.mem_union.mp hx1).resolve_left hxnotC
          · intro hx
            have hx1 : x ∈ C ∪ (g +ᵥ (X + Y)) := by rw [hg]; exact Finset.mem_union_right _ hx
            exact (Finset.mem_union.mp hx1).resolve_left (fun hc => Finset.disjoint_left.mp hXY_disj_C hc hx)
        · intro hg
          have hgH : g ∈ H := hH'_le_H (mem_addStab_iff.mpr hg)
          rw [Finset.vadd_finset_union, mem_addStab_iff.mp hgH, hg]
      -- Apply IH to `(X, Y)` (`|X + Y| < |A + B|` since `C` is nonempty and disjoint from `X + Y`)
      have hXY_lt_AB : (X + Y).card < (A + B).card := by
        have h1 : (C ∪ (X + Y)).card ≤ (A + B).card := Finset.card_le_card (Finset.union_subset hC_sub hXY_sub_AB)
        rw [Finset.card_union_of_disjoint hXY_disj_C] at h1
        have := hC_ne.card_pos
        omega
      have hih_XY := ih ((X + Y).card + X.card) (by have := Finset.card_le_card hXA; omega) X Y hXne hYne rfl
      change (X + subFinset H').card + (Y + subFinset H').card ≤ (X + Y).card + (subFinset H').card at hih_XY
      -- Since `C ∪ (X + Y)` is NOT a convergent (by minimality of `|H|`):
      have hCi_not_conv : (C ∪ (X + Y)).card + (subFinset H').card <
          (A ∩ B).card + ((A ∪ B) + subFinset H').card := by
        by_contra hle; push Not at hle
        have hmem : C ∪ (X + Y) ∈ Convs := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.union_subset hC_sub hXY_sub_AB),
            hC_ne.mono Finset.subset_union_left, Finset.union_subset hC_sub hXY_sub_AB, ?_⟩
          rwa [hstab_Ci]
        have hmin := hC_min (C ∪ (X + Y)) hmem
        rw [hstab_Ci] at hmin
        omega
      rw [Finset.card_union_of_disjoint hXY_disj_C] at hCi_not_conv
      -- Equation (1) without subtraction!
      have heq1 : ((A ∪ B) + subFinset H).card + (X + subFinset H').card + (Y + subFinset H').card <
          ((A ∪ B) + subFinset H').card + (subFinset H).card := by omega
      -- Equation (2): using divisibility by `|H'|`!
      have heq2 : X.card + Y.card + (subFinset H').card ≤ (subFinset H).card := by
        have hmono : ((A ∪ B) + subFinset H').card ≤ ((A ∪ B) + subFinset H).card :=
          Finset.card_le_card (add_subFinset_mono (A ∪ B) hH'_le_H)
        have hlt_sum : (X + subFinset H').card + (Y + subFinset H').card < (subFinset H).card := by omega
        obtain ⟨q₁, hq₁⟩ := card_subFinset_dvd_card_add_subFinset X H'
        obtain ⟨q₂, hq₂⟩ := card_subFinset_dvd_card_add_subFinset Y H'
        obtain ⟨q₃, hq₃⟩ := card_subFinset_dvd_of_le hH'_le_H
        have hd_pos : 0 < (subFinset H').card := card_subFinset_pos H'
        have hq_lt : q₁ + q₂ < q₃ := by nlinarith
        have hq_le : (X + subFinset H').card + (Y + subFinset H').card + (subFinset H').card ≤ (subFinset H).card := by
          nlinarith
        have hXle := card_le_card_add_subFinset X H'
        have hYle := card_le_card_add_subFinset Y H'
        omega
      -- Equation (3): `|(A ∪ B) + H| + |X| + |Y| < |A ∪ B| + |H| + |H'|`
      have heq3 : ((A ∪ B) + subFinset H).card + X.card + Y.card <
          (A ∪ B).card + (subFinset H).card + (subFinset H').card := by
        have hCu_le : C.card + (X + Y).card ≤ (A + B).card := by
          rw [← Finset.card_union_of_disjoint hXY_disj_C]
          exact Finset.card_le_card (Finset.union_subset hC_sub hXY_sub_AB)
        have hXle := card_le_card_add_subFinset X H'
        have hYle := card_le_card_add_subFinset Y H'
        omega
      exact ⟨hH'_le_H, hH'_lt_H, heq1, heq2, heq3⟩
    -- Check `A₁ + B₁ ⊆ (a + b) +ᵥ subFinset H` and `A₂ + B₂ ⊆ (a + b) +ᵥ subFinset H`
    have hA₁B₁_cos : A₁ + B₁ ⊆ (a + b) +ᵥ subFinset H := by
      intro x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨h₁, hh₁, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_inter.mp hu).2
      obtain ⟨h₂, hh₂, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_inter.mp hv).2
      refine Finset.mem_vadd_finset.mpr ⟨h₁ + h₂, mem_subFinset.mpr (H.add_mem (mem_subFinset.mp hh₁) (mem_subFinset.mp hh₂)), ?_⟩
      simp only [vadd_eq_add]; abel
    have hA₂B₂_cos : A₂ + B₂ ⊆ (a + b) +ᵥ subFinset H := by
      intro x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨h₁, hh₁, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_inter.mp hu).2
      obtain ⟨h₂, hh₂, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_inter.mp hv).2
      refine Finset.mem_vadd_finset.mpr ⟨h₁ + h₂, mem_subFinset.mpr (H.add_mem (mem_subFinset.mp hh₁) (mem_subFinset.mp hh₂)), ?_⟩
      simp only [vadd_eq_add]; abel
    -- Apply `hdevos_pair` to `(A₁, B₁)`!
    have h1 := hdevos_pair A₁ B₁ Finset.inter_subset_left Finset.inter_subset_left hA₁_ne hB₁_ne hA₁B₁_cos
    obtain ⟨hH₁_le, _, heq1_1, heq2_1, heq3_1⟩ := h1
    set H₁ := addStab (A₁ + B₁)
    -- Helper: `(c +ᵥ subFinset H) ∩ ((A ∪ B) + subFinset H₁) ⊆ ((A ∪ B) ∩ (c +ᵥ subFinset H)) + subFinset H₁`
    have hcos_inter : ∀ c : G, c ∈ A ∪ B →
        (c +ᵥ subFinset H) ⊆ (A ∪ B) + subFinset H ∧
        ((c +ᵥ subFinset H) \ (((A ∪ B) ∩ (c +ᵥ subFinset H)) + subFinset H₁)).card +
          ((A ∪ B) + subFinset H₁).card ≤ ((A ∪ B) + subFinset H).card := by
      intro c hc
      have hsub1 : c +ᵥ subFinset H ⊆ (A ∪ B) + subFinset H := by
        intro x hx
        obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hx
        exact Finset.mem_add.mpr ⟨c, hc, h, hh, rfl⟩
      refine ⟨hsub1, ?_⟩
      have hdisj : Disjoint ((c +ᵥ subFinset H) \ (((A ∪ B) ∩ (c +ᵥ subFinset H)) + subFinset H₁))
          ((A ∪ B) + subFinset H₁) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨hxcos, hxnot⟩ := Finset.mem_sdiff.mp hx1
        obtain ⟨y, hyAB, h', hh', rfl⟩ := Finset.mem_add.mp hx2
        obtain ⟨h, hh, heq⟩ := Finset.mem_vadd_finset.mp hxcos
        have hycos : y ∈ c +ᵥ subFinset H := by
          refine Finset.mem_vadd_finset.mpr ⟨h - h',
            mem_subFinset.mpr (H.sub_mem (mem_subFinset.mp hh) (hH₁_le (mem_subFinset.mp hh'))), ?_⟩
          simp only [vadd_eq_add] at heq ⊢
          have : y = c + h - h' := eq_sub_of_add_eq heq.symm
          rw [this]; abel
        exact hxnot (Finset.mem_add.mpr ⟨y, Finset.mem_inter.mpr ⟨hyAB, hycos⟩, h', hh', rfl⟩)
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset
        (Finset.sdiff_subset.trans hsub1) (add_subFinset_mono (A ∪ B) hH₁_le))
    -- Prove `B₂.Nonempty`
    have hB₂_ne : B₂.Nonempty := by
      by_contra hB₂e
      rw [Finset.not_nonempty_iff_eq_empty] at hB₂e
      have heq_inter : (A ∪ B) ∩ (a +ᵥ subFinset H) = A₁ := by
        ext x; simp only [Finset.mem_inter, Finset.mem_union, A₁]
        constructor
        · rintro ⟨hxA | hxB, hxcos⟩
          · exact ⟨hxA, hxcos⟩
          · exfalso; have : x ∈ B₂ := Finset.mem_inter.mpr ⟨hxB, hxcos⟩
            rw [hB₂e] at this; exact Finset.notMem_empty x this
        · rintro ⟨hxA, hxcos⟩; exact ⟨Or.inl hxA, hxcos⟩
      have hci := (hcos_inter a (Finset.mem_union_left _ haA)).2
      rw [heq_inter] at hci
      have hcard_sdiff : (subFinset H).card ≤
          ((a +ᵥ subFinset H) \ (A₁ + subFinset H₁)).card + (A₁ + subFinset H₁).card := by
        simpa [Finset.card_vadd_finset] using card_le_card_sdiff_add (a +ᵥ subFinset H) (A₁ + subFinset H₁)
      omega
    -- Prove `A₂.Nonempty`
    have hA₂_ne : A₂.Nonempty := by
      by_contra hA₂e
      rw [Finset.not_nonempty_iff_eq_empty] at hA₂e
      have heq_inter : (A ∪ B) ∩ (b +ᵥ subFinset H) = B₁ := by
        ext x; simp only [Finset.mem_inter, Finset.mem_union, B₁]
        constructor
        · rintro ⟨hxA | hxB, hxcos⟩
          · exfalso; have : x ∈ A₂ := Finset.mem_inter.mpr ⟨hxA, hxcos⟩
            rw [hA₂e] at this; exact Finset.notMem_empty x this
          · exact ⟨hxB, hxcos⟩
        · rintro ⟨hxB, hxcos⟩; exact ⟨Or.inr hxB, hxcos⟩
      have hci := (hcos_inter b (Finset.mem_union_right _ hbB)).2
      rw [heq_inter] at hci
      have hcard_sdiff : (subFinset H).card ≤
          ((b +ᵥ subFinset H) \ (B₁ + subFinset H₁)).card + (B₁ + subFinset H₁).card := by
        simpa [Finset.card_vadd_finset] using card_le_card_sdiff_add (b +ᵥ subFinset H) (B₁ + subFinset H₁)
      omega
    -- Prove `a +ᵥ subFinset H ≠ b +ᵥ subFinset H` (i.e. disjoint cosets!)
    have hcos_disj : Disjoint (a +ᵥ subFinset H) (b +ᵥ subFinset H) := by
      by_contra hnd
      rw [Finset.not_disjoint_iff] at hnd
      obtain ⟨z, hza, hzb⟩ := hnd
      obtain ⟨h₁, hh₁, hza_eq⟩ := Finset.mem_vadd_finset.mp hza
      obtain ⟨h₂, hh₂, hzb_eq⟩ := Finset.mem_vadd_finset.mp hzb
      have hcos_eq : a +ᵥ subFinset H = b +ᵥ subFinset H := by
        ext x
        simp only [Finset.mem_vadd_finset, mem_subFinset, vadd_eq_add] at hza_eq hzb_eq ⊢
        constructor
        · rintro ⟨h, hh, rfl⟩
          refine ⟨h + (h₂ - h₁), H.add_mem hh (H.sub_mem (mem_subFinset.mp hh₂) (mem_subFinset.mp hh₁)), ?_⟩
          have hab : a - b = h₂ - h₁ := by
            have : a + h₁ = b + h₂ := hza_eq.trans hzb_eq.symm
            have h1 : a = b + h₂ - h₁ := eq_sub_of_add_eq this
            rw [h1]; abel
          have : b + (h + (a - b)) = a + h := by abel
          rwa [← hab]
        · rintro ⟨h, hh, rfl⟩
          refine ⟨h + (h₁ - h₂), H.add_mem hh (H.sub_mem (mem_subFinset.mp hh₁) (mem_subFinset.mp hh₂)), ?_⟩
          have hba : b - a = h₁ - h₂ := by
            have : b + h₂ = a + h₁ := hzb_eq.trans hza_eq.symm
            have h1 : b = a + h₁ - h₂ := eq_sub_of_add_eq this
            rw [h1]; abel
          have : a + (h + (b - a)) = b + h := by abel
          rwa [← hba]
      have hB₁_eq : B₁ = B₂ := by simp only [B₁, B₂, hcos_eq]
      have heq_inter : (A ∪ B) ∩ (a +ᵥ subFinset H) = A₁ ∪ B₁ := by
        ext x; simp only [Finset.mem_inter, Finset.mem_union, A₁, B₁, hcos_eq]; tauto
      have hci := (hcos_inter a (Finset.mem_union_left _ haA)).2
      rw [heq_inter] at hci
      have hsub_u : (A₁ ∪ B₁) + subFinset H₁ ⊆ (A₁ + subFinset H₁) ∪ (B₁ + subFinset H₁) := by
        intro x hx
        obtain ⟨u, hu, h', hh', rfl⟩ := Finset.mem_add.mp hx
        rcases Finset.mem_union.mp hu with hu1 | hu2
        · exact Finset.mem_union_left _ (Finset.mem_add.mpr ⟨u, hu1, h', hh', rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_add.mpr ⟨u, hu2, h', hh', rfl⟩)
      have hcard_u : ((A₁ ∪ B₁) + subFinset H₁).card ≤ (A₁ + subFinset H₁).card + (B₁ + subFinset H₁).card :=
        (Finset.card_le_card hsub_u).trans (Finset.card_union_le _ _)
      have hcard_sdiff : (subFinset H).card ≤
          ((a +ᵥ subFinset H) \ ((A₁ ∪ B₁) + subFinset H₁)).card + ((A₁ ∪ B₁) + subFinset H₁).card := by
        simpa [Finset.card_vadd_finset] using card_le_card_sdiff_add (a +ᵥ subFinset H) ((A₁ ∪ B₁) + subFinset H₁)
      omega
    -- Apply `hdevos_pair` to `(A₂, B₂)`!
    have h2 := hdevos_pair A₂ B₂ Finset.inter_subset_left Finset.inter_subset_left hA₂_ne hB₂_ne hA₂B₂_cos
    obtain ⟨_, _, _, heq2_2, heq3_2⟩ := h2
    -- Let `S = (a +ᵥ subFinset H) \ (A₁ ∪ B₂)` and `T = (b +ᵥ subFinset H) \ (A₂ ∪ B₁)`!
    set S := (a +ᵥ subFinset H) \ (A₁ ∪ B₂)
    set T := (b +ᵥ subFinset H) \ (A₂ ∪ B₁)
    have hST_disj : Disjoint S T := hcos_disj.mono Finset.sdiff_subset Finset.sdiff_subset
    have hS_disj_AB : Disjoint S (A ∪ B) := by
      rw [Finset.disjoint_left]
      intro x hxS hxAB
      obtain ⟨hxcos, hxnot⟩ := Finset.mem_sdiff.mp hxS
      apply hxnot
      rcases Finset.mem_union.mp hxAB with hxA | hxB
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxA, hxcos⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxB, hxcos⟩)
    have hT_disj_AB : Disjoint T (A ∪ B) := by
      rw [Finset.disjoint_left]
      intro x hxT hxAB
      obtain ⟨hxcos, hxnot⟩ := Finset.mem_sdiff.mp hxT
      apply hxnot
      rcases Finset.mem_union.mp hxAB with hxA | hxB
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxA, hxcos⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxB, hxcos⟩)
    have hST_sub : S ∪ T ∪ (A ∪ B) ⊆ (A ∪ B) + subFinset H :=
      Finset.union_subset
        (Finset.union_subset
          (Finset.sdiff_subset.trans (hcos_inter a (Finset.mem_union_left _ haA)).1)
          (Finset.sdiff_subset.trans (hcos_inter b (Finset.mem_union_right _ hbB)).1))
        (subset_add_subFinset (A ∪ B) H)
    have hST_card : S.card + T.card + (A ∪ B).card ≤ ((A ∪ B) + subFinset H).card := by
      have h1 := Finset.card_le_card hST_sub
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hS_disj_AB, hT_disj_AB⟩),
          Finset.card_union_of_disjoint hST_disj] at h1
      exact h1
    have hcos_a : (subFinset H).card ≤ S.card + A₁.card + B₂.card := by
      have h1 : (subFinset H).card ≤ S.card + (A₁ ∪ B₂).card := by
        simpa [S, Finset.card_vadd_finset] using card_le_card_sdiff_add (a +ᵥ subFinset H) (A₁ ∪ B₂)
      have h2 := Finset.card_union_le A₁ B₂
      omega
    have hcos_b : (subFinset H).card ≤ T.card + A₂.card + B₁.card := by
      have h1 : (subFinset H).card ≤ T.card + (A₂ ∪ B₁).card := by
        simpa [T, Finset.card_vadd_finset] using card_le_card_sdiff_add (b +ᵥ subFinset H) (A₂ ∪ B₁)
      have h2 := Finset.card_union_le A₂ B₁
      omega
    -- Summing `heq2_1, heq3_1, heq2_2, heq3_2` gives `2 * |H| > |S| + |A₁| + |B₂| + |T| + |A₂| + |B₁| ≥ 2 * |H|`!
    omega

/-- Standard form of Kneser's theorem: `|A| + |B| ≤ |A + B| + |addStab (A + B)|`. -/
theorem kneser {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] (A B : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card ≤ (A + B).card + (subFinset (addStab (A + B))).card := by
  have h := kneser_strong ((A + B).card + A.card) A B hA hB rfl
  have h1 := card_le_card_add_subFinset A (addStab (A + B))
  have h2 := card_le_card_add_subFinset B (addStab (A + B))
  omega

/-! ## Part 2: Structure of large sum-free subsets of `[1, n]` (Deshouillers–Freiman–Sós–Temkin / BLST) -/

/-- Pairing bound: any sum-free `B ⊆ [1, M]` with `M ∈ B` has `2 * B.card ≤ M + 2`. -/
lemma sumfree_card_le_half_max (B : Finset ℕ) (M : ℕ)
    (hBsub : B ⊆ Finset.Icc 1 M) (hM : M ∈ B)
    (hBsf : ∀ a ∈ B, ∀ b ∈ B, a + b ∉ B) :
    2 * B.card ≤ M + 2 := by
  -- Map `B.erase M` into `Icc 1 (M - 1)` by `x ↦ M - x`; its image is disjoint from `B.erase M`!
  set B' := B.erase M
  set R := B'.image (fun x => M - x)
  have hRcard : R.card = B'.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy heq
    dsimp only at heq
    have hxM : x ≤ M := (Finset.mem_Icc.mp (hBsub (Finset.mem_of_mem_erase hx))).2
    have hyM : y ≤ M := (Finset.mem_Icc.mp (hBsub (Finset.mem_of_mem_erase hy))).2
    omega
  have hdisj : Disjoint B' R := by
    rw [Finset.disjoint_left]
    intro x hxB' hxR
    obtain ⟨y, hyB', hxy⟩ := Finset.mem_image.mp hxR
    have hyM : y ≤ M := (Finset.mem_Icc.mp (hBsub (Finset.mem_of_mem_erase hyB'))).2
    have hsum : x + y = M := by omega
    exact hBsf x (Finset.mem_of_mem_erase hxB') y (Finset.mem_of_mem_erase hyB') (hsum ▸ hM)
  have hsub : B' ∪ R ⊆ Finset.Icc 1 M := by
    refine Finset.union_subset ((Finset.erase_subset M B).trans hBsub) ?_
    intro x hxR
    obtain ⟨y, hyB', rfl⟩ := Finset.mem_image.mp hxR
    have hyne : y ≠ M := (Finset.mem_erase.mp hyB').1
    have hyI := Finset.mem_Icc.mp (hBsub (Finset.mem_of_mem_erase hyB'))
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcard : (B' ∪ R).card ≤ M := by
    calc (B' ∪ R).card ≤ (Finset.Icc 1 M).card := Finset.card_le_card hsub
      _ = M := by simp
  rw [Finset.card_union_of_disjoint hdisj, hRcard] at hcard
  have hB'card : B'.card + 1 = B.card := Finset.card_erase_add_one hM
  omega

/-- Elementary shift lemma: if `B ⊆ [m, M]` is sum-free with `m ∈ B` and `3 * m > M`, then `B.card ≤ m`. -/
lemma sumfree_card_le_min_of_three_min_gt_max (B : Finset ℕ) (m M : ℕ)
    (hBsub : B ⊆ Finset.Icc m M) (hm : m ∈ B) (h3m : M < 3 * m)
    (hBsf : ∀ a ∈ B, ∀ b ∈ B, a + b ∉ B) :
    B.card ≤ m := by
  -- Split `B = B_lo ∪ B_hi` where `B_lo = {x ∈ B | x ≤ M - m}` and `B_hi = {x ∈ B | M - m < x}`!
  -- `x ↦ x + m` injects `B_lo` into `Icc (M - m + 1) M \ B_hi`!
  set Blo := B.filter (fun x => x ≤ M - m)
  set Bhi := B.filter (fun x => ¬ (x ≤ M - m))
  have hcard_split : Blo.card + Bhi.card = B.card := by
    have hd : Disjoint Blo Bhi := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).2
    rw [← Finset.card_union_of_disjoint hd]
    congr 1; ext x; simp only [Blo, Bhi, Finset.mem_union, Finset.mem_filter]; tauto
  set Sh := Blo.image (fun x => x + m)
  have hSh_card : Sh.card = Blo.card :=
    Finset.card_image_of_injOn fun x _ y _ h => by omega
  have hSh_sub : Sh ⊆ Finset.Icc (M - m + 1) M := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxB, hxle⟩ := Finset.mem_filter.mp hx
    have hxI := Finset.mem_Icc.mp (hBsub hxB)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hBhi_sub : Bhi ⊆ Finset.Icc (M - m + 1) M := by
    intro x hx
    obtain ⟨hxB, hxgt⟩ := Finset.mem_filter.mp hx
    have hxI := Finset.mem_Icc.mp (hBsub hxB)
    exact Finset.mem_Icc.mpr ⟨by omega, hxI.2⟩
  have hdisj : Disjoint Sh Bhi := by
    rw [Finset.disjoint_left]
    intro y hySh hyBhi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hySh
    exact hBsf x (Finset.mem_filter.mp hx).1 m hm (Finset.mem_filter.mp hyBhi).1
  have htot : (Sh ∪ Bhi).card ≤ (Finset.Icc (M - m + 1) M).card :=
    Finset.card_le_card (Finset.union_subset hSh_sub hBhi_sub)
  rw [Finset.card_union_of_disjoint hdisj, hSh_card, Nat.card_Icc] at htot
  have hm_le_M : m ≤ M := (Finset.mem_Icc.mp (hBsub hm)).2
  omega

/-- Index-2 subgroup of `ZMod t` (when `2 ∣ t`) is the set of even residue classes. -/
lemma zmod_index_two_eq_evens {t : ℕ} [NeZero t] (H : AddSubgroup (ZMod t))
    (hidx : 2 * (subFinset H).card = t) :
    ∀ x : ZMod t, x ∈ H ↔ Even x.val := by
  have ht_even : 2 ∣ t := ⟨(subFinset H).card, hidx.symm⟩
  -- For any `x : ZMod t`, `2 • x ∈ H` because `G / H` has order `2`!
  have h2mem : ∀ x : ZMod t, (2 : ℕ) • x ∈ H := by
    intro x
    let : Fintype (ZMod t ⧸ H) := Fintype.ofFinite (ZMod t ⧸ H)
    let : DecidablePred (· ∈ H) := Classical.decPred (· ∈ H)
    have hcard_quot : Fintype.card (ZMod t ⧸ H) = 2 := by
      have h1 := AddSubgroup.card_mul_index H
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card t] at h1
      have h3 : Fintype.card H = (subFinset H).card := by
        simpa using (card_subFinset H).symm
      have h4 : H.index = Fintype.card (ZMod t ⧸ H) := by
        rw [AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
      have h5 : (subFinset H).card * Fintype.card (ZMod t ⧸ H) = t := by
        rw [← h3, ← h4]; exact h1
      have hpos : 0 < (subFinset H).card := card_subFinset_pos H
      nlinarith
    have hq0 : (2 : ℕ) • (QuotientAddGroup.mk x : ZMod t ⧸ H) = 0 := by
      obtain ⟨c, hc⟩ := addOrderOf_dvd_card (x := (QuotientAddGroup.mk x : ZMod t ⧸ H))
      rw [hcard_quot] at hc
      rw [hc, mul_nsmul, addOrderOf_nsmul_eq_zero, smul_zero]
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hq0
    exact hq0
  -- So `2 • (1 : ZMod t) ∈ H`, hence every even `x.val` has `x ∈ H`!
  have heven_sub : Finset.univ.filter (fun x : ZMod t => Even x.val) ⊆ subFinset H := by
    intro x hx
    rw [mem_subFinset]
    obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hx).2
    have hx_eq : x = k • ((2 : ℕ) • (1 : ZMod t)) := by
      have h1 : (x.val : ZMod t) = x := ZMod.natCast_zmod_val x
      rw [← h1, hk, ← two_mul]
      simp [nsmul_eq_mul, mul_comm]
    rw [hx_eq]
    exact H.nsmul_mem (h2mem 1) k
  -- Count `|{x : ZMod t | Even x.val}| = t / 2 = |subFinset H|`!
  have heven_card : (Finset.univ.filter (fun x : ZMod t => Even x.val)).card = (subFinset H).card := by
    obtain ⟨k, hk⟩ := ht_even
    have hk_eq : k = (subFinset H).card := by omega
    rw [← hk_eq]
    have hbij : (Finset.range k).image (fun i => ((2 * i : ℕ) : ZMod t)) =
        Finset.univ.filter (fun x : ZMod t => Even x.val) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hlt : 2 * i < t := by omega
        rw [ZMod.val_natCast_of_lt hlt]
        exact ⟨i, by omega⟩
      · rintro ⟨i, hi⟩
        have hxlt : x.val < t := ZMod.val_lt x
        refine ⟨i, by omega, ?_⟩
        have h1 : (x.val : ZMod t) = x := ZMod.natCast_zmod_val x
        rw [← h1, hi, ← two_mul]
    rw [← hbij, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj heq
    have hilt : 2 * i < t := by simp only [Finset.mem_coe, Finset.mem_range] at hi; omega
    have hjlt : 2 * j < t := by simp only [Finset.mem_coe, Finset.mem_range] at hj; omega
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt hilt, ZMod.val_natCast_of_lt hjlt] at hval
    omega
  have heq : Finset.univ.filter (fun x : ZMod t => Even x.val) = subFinset H :=
    Finset.eq_of_subset_of_card_le heven_sub (by omega)
  intro x
  rw [← mem_subFinset, ← heq]
  simp

/-- **Structure Theorem for Large Sum-Free Sets** (BLST / Deshouillers–Freiman–Sós–Temkin):
If `B ⊆ [1, n]` is sum-free and `15 * B.card > 7 * n + 9`, then EITHER every element of `B` is odd,
OR `∀ x ∈ B, B.card ≤ x` (i.e. `B.card ≤ min B`). -/
theorem sumfree_structure (n : ℕ) (B : Finset ℕ)
    (hBsub : B ⊆ Finset.Icc 1 n)
    (hBsf : ∀ a ∈ B, ∀ b ∈ B, a + b ∉ B)
    (hBbig : 7 * n + 9 < 15 * B.card) :
    (∀ x ∈ B, Odd x) ∨ (∀ x ∈ B, B.card ≤ x) := by
  have hBne : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.card_empty] at hBbig; omega
  have hBn : B.card ≤ n := by
    calc B.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hBsub
      _ = n := by simp
  have hBge2 : 2 ≤ B.card := by omega
  set m := B.min' hBne
  set M := B.max' hBne
  have hmB : m ∈ B := Finset.min'_mem B hBne
  have hMB : M ∈ B := Finset.max'_mem B hBne
  have hm_le : ∀ x ∈ B, m ≤ x := fun x hx => Finset.min'_le B x hx
  have hM_ge : ∀ x ∈ B, x ≤ M := fun x hx => Finset.le_max' B x hx
  have hMn : M ≤ n := (Finset.mem_Icc.mp (hBsub hMB)).2
  have hm_lt_M : m < M := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
    have h1 := hm_le x hx; have h2 := hM_ge x hx
    have h3 := hm_le y hy; have h4 := hM_ge y hy
    omega
  -- `B ⊆ Icc m M` and `2 * B.card ≤ M + 2`
  have hBmM : B ⊆ Finset.Icc m M := fun x hx => Finset.mem_Icc.mpr ⟨hm_le x hx, hM_ge x hx⟩
  have hpair : 2 * B.card ≤ M + 2 := sumfree_card_le_half_max B M
    (fun x hx => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hBsub hx)).1, hM_ge x hx⟩) hMB hBsf
  -- Define `t = M - m > 0` and the Lev–Smeliansky projection `π : ℤ → ZMod t`!
  set t := M - m with ht_def
  have ht_pos : 0 < t := by omega
  haveI : NeZero t := ⟨by omega⟩
  set Bz : Finset ℤ := B.image (fun x : ℕ => (x : ℤ))
  have hBz_card : Bz.card = B.card :=
    Finset.card_image_of_injOn fun _ _ _ _ h => by exact_mod_cast h
  set D : Finset ℤ := Bz - Bz
  -- Upper bound on `|D|`: `D ⊆ Icc (-n : ℤ) n \ (Bz ∪ (-Bz))`, so `|D| ≤ 2 * n - 2 * B.card + 1`!
  have hD_le : D.card + 2 * B.card ≤ 2 * n + 1 := by
    have hD_sub : D ⊆ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      intro d hd
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hd
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
      have haI := Finset.mem_Icc.mp (hBsub ha)
      have hbI := Finset.mem_Icc.mp (hBsub hb)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hBz_sub : Bz ⊆ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      intro u hu
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      have haI := Finset.mem_Icc.mp (hBsub ha)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hnBz_sub : (-Bz) ⊆ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_neg.mp hu
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      have haI := Finset.mem_Icc.mp (hBsub ha)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hD_disj_Bz : Disjoint D Bz := by
      rw [Finset.disjoint_left]
      intro d hd hdb
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hd
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨c, hc, hce⟩ := Finset.mem_image.mp hdb
      have hsum : b + c = a := by omega
      exact hBsf b hb c hc (hsum ▸ ha)
    have hD_disj_nBz : Disjoint D (-Bz) := by
      rw [Finset.disjoint_left]
      intro d hd hdb
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hd
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨w, hw, hwe⟩ := Finset.mem_neg.mp hdb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
      have hsum : a + c = b := by omega
      exact hBsf a ha c hc (hsum ▸ hb)
    have hBz_disj_nBz : Disjoint Bz (-Bz) := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu1
      obtain ⟨w, hw, hwe⟩ := Finset.mem_neg.mp hu2
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
      have haI := Finset.mem_Icc.mp (hBsub ha)
      have hbI := Finset.mem_Icc.mp (hBsub hb)
      omega
    have htot := Finset.card_le_card (Finset.union_subset (Finset.union_subset hD_sub hBz_sub) hnBz_sub)
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hD_disj_nBz, hBz_disj_nBz⟩),
        Finset.card_union_of_disjoint hD_disj_Bz, Finset.card_neg, hBz_card] at htot
    have hIcc : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
      rw [Int.card_Icc]; omega
    omega
  -- Project `B` to `X : Finset (ZMod t)`: `|X| = B.card - 1` (only `m` and `M` collide mod `t`)!
  set X : Finset (ZMod t) := B.image (fun x : ℕ => (x : ZMod t))
  have hX_card : X.card = B.card - 1 := by
    have hX_eq : X = (B.erase M).image (fun x : ℕ => (x : ZMod t)) := by
      apply Finset.Subset.antisymm
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        by_cases hxM : x = M
        · refine Finset.mem_image.mpr ⟨m, Finset.mem_erase.mpr ⟨by omega, hmB⟩, ?_⟩
          rw [hxM, show M = m + t by omega, Nat.cast_add, ZMod.natCast_self, add_zero]
        · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxM, hx⟩, rfl⟩
      · exact Finset.image_subset_image (Finset.erase_subset M B)
    rw [hX_eq, Finset.card_image_of_injOn, Finset.card_erase_of_mem hMB]
    intro x hx y hy heq
    dsimp only at heq
    have hxM : x ≠ M := (Finset.mem_erase.mp hx).1
    have hyM : y ≠ M := (Finset.mem_erase.mp hy).1
    have hxI := Finset.mem_Icc.mp (hBmM (Finset.mem_of_mem_erase hx))
    have hyI := Finset.mem_Icc.mp (hBmM (Finset.mem_of_mem_erase hy))
    have hdiff : ((x - m : ℕ) : ZMod t) = ((y - m : ℕ) : ZMod t) := by
      rw [Nat.cast_sub hxI.1, Nat.cast_sub hyI.1, heq]
    have hval := congrArg ZMod.val hdiff
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
    omega
  have hX_ne : X.Nonempty := hBne.image _
  -- Lower bound on `|D|` via fiber counting of `π : ℤ → ZMod t` from `D` onto `X - X`:
  -- Every `z ∈ X - X` has ≥ 1 lift in `D`; `0` has ≥ 3 lifts `{0, t, -t}`; each `(b - m : ZMod t)` for
  -- `b ∈ B \ {m, M}` has ≥ 2 lifts `{b - m, b - M}` (distinct and nonzero mod `t`)!
  have hD_ge : (X - X).card + B.card ≤ D.card := by
    set π : ℤ → ZMod t := fun z => (z : ZMod t)
    have hD_onto : D.image π = X - X := by
      ext q
      simp only [Finset.mem_image, Finset.mem_sub, D, Bz, X]
      constructor
      · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
        exact ⟨(a : ZMod t), ⟨a, ha, rfl⟩, (b : ZMod t), ⟨b, hb, rfl⟩, by simp [π]⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨(a : ℤ) - (b : ℤ), ⟨(a : ℤ), ⟨a, ha, rfl⟩, (b : ℤ), ⟨b, hb, rfl⟩, rfl⟩, by simp [π]⟩
    -- Partition `D` by `π` over `X - X`
    have hpart := Finset.card_eq_sum_card_fiberwise (f := π) (s := D) (t := X - X)
      (fun d hd => hD_onto ▸ Finset.mem_image_of_mem π hd)
    -- Every fiber has size `≥ 1`
    have hfib1 : ∀ q ∈ X - X, 1 ≤ (D.filter (fun d => π d = q)).card := by
      intro q hq
      rw [← hD_onto] at hq
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, rfl⟩⟩
    -- Fiber over `0` has size `≥ 3` (`0, t, -t ∈ D`)
    have h0_mem : (0 : ZMod t) ∈ X - X :=
      Finset.mem_sub.mpr ⟨(m : ZMod t), Finset.mem_image_of_mem _ hmB,
        (m : ZMod t), Finset.mem_image_of_mem _ hmB, sub_self _⟩
    have hfib0 : 3 ≤ (D.filter (fun d => π d = 0)).card := by
      have hsub3 : ({(0 : ℤ), (t : ℤ), -(t : ℤ)} : Finset ℤ) ⊆ D.filter (fun d => π d = 0) := by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rcases hd with rfl | rfl | rfl
          · exact Finset.mem_sub.mpr ⟨(m : ℤ), Finset.mem_image_of_mem _ hmB,
              (m : ℤ), Finset.mem_image_of_mem _ hmB, sub_self _⟩
          · exact Finset.mem_sub.mpr ⟨(M : ℤ), Finset.mem_image_of_mem _ hMB,
              (m : ℤ), Finset.mem_image_of_mem _ hmB, by omega⟩
          · exact Finset.mem_sub.mpr ⟨(m : ℤ), Finset.mem_image_of_mem _ hmB,
              (M : ℤ), Finset.mem_image_of_mem _ hMB, by omega⟩
        · rcases hd with rfl | rfl | rfl <;> simp [π]
      have h3 : ({(0 : ℤ), (t : ℤ), -(t : ℤ)} : Finset ℤ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair] <;> simp <;> omega
      exact h3 ▸ Finset.card_le_card hsub3
    -- Set of interior elements `Bmid = (B.erase m).erase M`, size `B.card - 2`
    set Bmid := (B.erase m).erase M
    have hBmid_card : Bmid.card = B.card - 2 := by
      have hM_in : M ∈ B.erase m := Finset.mem_erase.mpr ⟨by omega, hMB⟩
      rw [Finset.card_erase_of_mem hM_in, Finset.card_erase_of_mem hmB]
      omega
    -- Image `Qmid := Bmid.image (fun b => ((b : ℤ) - (m : ℤ) : ZMod t))` is `⊆ (X - X).erase 0` and has card `Bmid.card`!
    set Qmid := Bmid.image (fun b : ℕ => ((b : ZMod t) - (m : ZMod t)))
    have hQmid_sub : Qmid ⊆ (X - X).erase 0 := by
      intro q hq
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
      have hbM : b ≠ M := (Finset.mem_erase.mp hb).1
      have hbm : b ≠ m := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
      have hbB : b ∈ B := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)
      have hbI := Finset.mem_Icc.mp (hBmM hbB)
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_sub.mpr ⟨(b : ZMod t), Finset.mem_image_of_mem _ hbB,
        (m : ZMod t), Finset.mem_image_of_mem _ hmB, rfl⟩⟩
      intro h0
      have hdiff : ((b - m : ℕ) : ZMod t) = 0 := by rw [Nat.cast_sub hbI.1]; exact h0
      have hval := congrArg ZMod.val hdiff
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
      omega
    have hQmid_card : Qmid.card = B.card - 2 := by
      rw [← hBmid_card]
      apply Finset.card_image_of_injOn
      intro x hx y hy heq
      have hxM : x ≠ M := (Finset.mem_erase.mp hx).1
      have hyM : y ≠ M := (Finset.mem_erase.mp hy).1
      have hxB : x ∈ B := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
      have hyB : y ∈ B := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
      have hxI := Finset.mem_Icc.mp (hBmM hxB)
      have hyI := Finset.mem_Icc.mp (hBmM hyB)
      have hdiff : ((x - m : ℕ) : ZMod t) = ((y - m : ℕ) : ZMod t) := by
        rw [Nat.cast_sub hxI.1, Nat.cast_sub hyI.1]; exact heq
      have hval := congrArg ZMod.val hdiff
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
      omega
    -- Every `q ∈ Qmid` has fiber size `≥ 2` (`b - m` and `b - M` are distinct elements of `D`)!
    have hfib_mid : ∀ q ∈ Qmid, 2 ≤ (D.filter (fun d => π d = q)).card := by
      intro q hq
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
      have hbB : b ∈ B := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)
      have hsub2 : ({(b : ℤ) - (m : ℤ), (b : ℤ) - (M : ℤ)} : Finset ℤ) ⊆
          D.filter (fun d => π d = (b : ZMod t) - (m : ZMod t)) := by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rcases hd with rfl | rfl
          · exact Finset.mem_sub.mpr ⟨(b : ℤ), Finset.mem_image_of_mem _ hbB,
              (m : ℤ), Finset.mem_image_of_mem _ hmB, rfl⟩
          · exact Finset.mem_sub.mpr ⟨(b : ℤ), Finset.mem_image_of_mem _ hbB,
              (M : ℤ), Finset.mem_image_of_mem _ hMB, rfl⟩
        · rcases hd with rfl | rfl
          · simp [π]
          · simp only [π, Int.cast_sub, Int.cast_natCast]
            rw [show M = m + t by omega, Nat.cast_add, ZMod.natCast_self, add_zero]
      have h2 : ({(b : ℤ) - (m : ℤ), (b : ℤ) - (M : ℤ)} : Finset ℤ).card = 2 :=
        Finset.card_pair (by omega)
      exact h2 ▸ Finset.card_le_card hsub2
    -- Sum fiber lower bounds over `X - X`:
    have hsum_lb : ∑ q ∈ X - X, (1 + (if q = 0 then 2 else 0) + (if q ∈ Qmid then 1 else 0)) ≤ D.card := by
      rw [hpart]
      apply Finset.sum_le_sum
      intro q hq
      by_cases hq0 : q = 0
      · subst hq0
        have hnot : (0 : ZMod t) ∉ Qmid := fun h => (Finset.mem_erase.mp (hQmid_sub h)).1 rfl
        simp only [↓reduceIte, hnot]
        exact hfib0
      · by_cases hqm : q ∈ Qmid
        · simp only [hq0, hqm, ↓reduceIte]
          exact hfib_mid q hqm
        · simp only [hq0, hqm, ↓reduceIte]
          exact hfib1 q hq
    simp_rw [Finset.sum_add_distrib] at hsum_lb
    rw [Finset.sum_const, smul_eq_mul, mul_one,
        Finset.sum_ite_eq' (X - X) 0, if_pos h0_mem,
        ← Finset.card_filter,
        show (X - X).filter (· ∈ Qmid) = Qmid by
          ext q; simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨Finset.mem_of_mem_erase (hQmid_sub h), h⟩⟩,
        hQmid_card] at hsum_lb
    omega
  -- Combine `hD_le` and `hD_ge`: `|X - X| + 3 * B.card ≤ 2 * n + 1`!
  have hXX_le : (X - X).card + 3 * B.card ≤ 2 * n + 1 := by omega
  -- Apply FULL KNESER to `(X, -X)` in `ZMod t`!
  set H := addStab (X + (-X))
  have hXX_eq : X + (-X) = X - X := (sub_eq_add_neg X X).symm
  have hknes : 2 * (B.card - 1) ≤ (X - X).card + (subFinset H).card := by
    have h0 := kneser X (-X) hX_ne hX_ne.neg
    rw [Finset.card_neg, hX_card] at h0
    have h1 : (X + -X).card = (X - X).card := congrArg Finset.card hXX_eq
    change (B.card - 1) + (B.card - 1) ≤ (X + -X).card + (subFinset H).card at h0
    omega
  -- Analyze index `k := t / |H|` (since `|H| ∣ t`)!
  have hH_dvd : (subFinset H).card ∣ t := by
    let : DecidablePred (· ∈ H) := Classical.decPred (· ∈ H)
    have h1 := AddSubgroup.card_mul_index H
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card t] at h1
    have h3 : Fintype.card H = (subFinset H).card := by
      simpa using (card_subFinset H).symm
    rw [h3] at h1
    exact ⟨H.index, h1.symm⟩
  obtain ⟨k, hk⟩ := hH_dvd
  have hH_pos : 0 < (subFinset H).card := card_subFinset_pos H
  have hk_pos : 0 < k := by nlinarith
  -- Case 1: `k = 1` (`H = ⊤`, so `X - X = univ` and `|X - X| = t`)!
  by_cases hk1 : k = 1
  · have hH_eq_t : (subFinset H).card = t := by rw [hk1, mul_one] at hk; omega
    have hXX_eq_t : (X - X).card = t := by
      have h1 : (X - X) + subFinset H = X - X := by
        rw [← hXX_eq]; exact add_subFinset_eq_self_of_le_addStab (le_refl H)
      have h2 : (subFinset H).card ≤ (X - X).card := by
        obtain ⟨z, hz⟩ := hX_ne.sub hX_ne
        calc (subFinset H).card = (z +ᵥ subFinset H).card := (Finset.card_vadd_finset z _).symm
          _ ≤ ((X - X) + subFinset H).card := Finset.card_le_card fun y hy => by
              obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hy
              exact Finset.mem_add.mpr ⟨z, hz, h, hh, rfl⟩
          _ = (X - X).card := by rw [h1]
      have h3 : (X - X).card ≤ t := by
        calc (X - X).card ≤ Fintype.card (ZMod t) := Finset.card_le_univ _
          _ = t := ZMod.card t
      omega
    -- `t ≤ 2*n + 1 - 3*B.card` and `2*B.card ≤ M + 2`, so `3*m > M` → `B.card ≤ m`!
    have h3m : M < 3 * m := by omega
    have hBm : B.card ≤ m := sumfree_card_le_min_of_three_min_gt_max B m M hBmM hmB h3m hBsf
    exact Or.inr fun x hx => hBm.trans (hm_le x hx)
  -- Case 2: `k ≥ 3` (`3 * |H| ≤ t ≤ n`) → contradiction with `15 * B.card > 7 * n + 9`!
  by_cases hk2 : k = 2
  · -- Case 3: `k = 2` (`2 * |H| = t`): `X - X` is a union of `H`-cosets!
    have h2H : 2 * (subFinset H).card = t := by rw [hk2] at hk; omega
    have hH_evens : ∀ x : ZMod t, x ∈ H ↔ Even x.val := zmod_index_two_eq_evens H h2H
    -- Either `X - X ⊆ H` or `(X - X).card = t` (in which case same as Case 1!)
    by_cases hsubH : X - X ⊆ subFinset H
    · -- All differences `b - m` are even mod `t` (with `t` even), so all `x ∈ B` have the SAME parity!
      have hsame_par : ∀ x ∈ B, Even x ↔ Even m := by
        intro x hx
        have hmem : (x : ZMod t) - (m : ZMod t) ∈ H :=
          mem_subFinset.mp (hsubH (Finset.mem_sub.mpr
            ⟨(x : ZMod t), Finset.mem_image_of_mem _ hx, (m : ZMod t), Finset.mem_image_of_mem _ hmB, rfl⟩))
        have hxI := Finset.mem_Icc.mp (hBmM hx)
        have hdiff_eq : (x : ZMod t) - (m : ZMod t) = ((x - m : ℕ) : ZMod t) := (Nat.cast_sub hxI.1).symm
        rw [hdiff_eq, hH_evens] at hmem
        have ht_ev : Even t := ⟨(subFinset H).card, by omega⟩
        have hval_ev : Even (x - m) := by
          rw [ZMod.val_natCast] at hmem
          have hdiv := Nat.mod_add_div (x - m) t
          obtain ⟨r, hr⟩ := hmem
          obtain ⟨s, hs⟩ := ht_ev
          exact ⟨r + s * ((x - m) / t), by nlinarith⟩
        obtain ⟨r, hr⟩ := hval_ev
        constructor
        · rintro ⟨a, ha⟩; exact ⟨a - r, by omega⟩
        · rintro ⟨a, ha⟩; exact ⟨a + r, by omega⟩
      by_cases hm_ev : Even m
      · -- All elements of `B` are even → `B.image (· / 2) ⊆ Icc 1 (n / 2)` is sum-free, so `B.card ≤ n / 4 + 1`, contradiction!
        set B2 := B.image (· / 2)
        have hB2_card : B2.card = B.card := by
          apply Finset.card_image_of_injOn
          intro x hx y hy heq
          dsimp only at heq
          obtain ⟨a, ha⟩ := (hsame_par x hx).mpr hm_ev
          obtain ⟨b, hb⟩ := (hsame_par y hy).mpr hm_ev
          omega
        have hB2_sub : B2 ⊆ Finset.Icc 1 (n / 2) := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          have hxI := Finset.mem_Icc.mp (hBsub hx)
          obtain ⟨a, ha⟩ := (hsame_par x hx).mpr hm_ev
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hB2_sf : ∀ a ∈ B2, ∀ b ∈ B2, a + b ∉ B2 := by
          intro a ha b hb hab
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
          obtain ⟨z, hz, hze⟩ := Finset.mem_image.mp hab
          obtain ⟨px, hpx⟩ := (hsame_par x hx).mpr hm_ev
          obtain ⟨py, hpy⟩ := (hsame_par y hy).mpr hm_ev
          obtain ⟨pz, hpz⟩ := (hsame_par z hz).mpr hm_ev
          have : x + y = z := by omega
          exact hBsf x hx y hy (this ▸ hz)
        have hB2_ne : B2.Nonempty := hBne.image _
        set M2 := B2.max' hB2_ne
        have hM2_in : M2 ∈ B2 := Finset.max'_mem B2 hB2_ne
        have hM2_le : M2 ≤ n / 2 := (Finset.mem_Icc.mp (hB2_sub hM2_in)).2
        have hpair2 := sumfree_card_le_half_max B2 M2
          (fun y hy => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hB2_sub hy)).1, Finset.le_max' B2 y hy⟩)
          hM2_in hB2_sf
        omega
      · -- All elements of `B` are odd!
        refine Or.inl fun x hx => ?_
        rw [← Nat.not_even_iff_odd]
        exact fun hxe => hm_ev ((hsame_par x hx).mp hxe)
    · -- `X - X` hits the other `H`-coset too, so `X - X = univ` (`|X - X| = t`)!
      have hnot_sub : ∃ z ∈ X - X, z ∉ subFinset H := Finset.not_subset.mp hsubH
      obtain ⟨z₁, hz₁, hz₁_not⟩ := hnot_sub
      have h0_in : (0 : ZMod t) ∈ X - X :=
        Finset.mem_sub.mpr ⟨(m : ZMod t), Finset.mem_image_of_mem _ hmB,
          (m : ZMod t), Finset.mem_image_of_mem _ hmB, sub_self _⟩
      have h1 : (X - X) + subFinset H = X - X := by
        rw [← hXX_eq]; exact add_subFinset_eq_self_of_le_addStab (le_refl H)
      have hsub1 : subFinset H ⊆ X - X := by
        intro h hh
        rw [← h1]; exact Finset.mem_add.mpr ⟨0, h0_in, h, hh, zero_add h⟩
      have hsub2 : z₁ +ᵥ subFinset H ⊆ X - X := by
        intro y hy
        obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hy
        rw [← h1]; exact Finset.mem_add.mpr ⟨z₁, hz₁, h, hh, rfl⟩
      have hdisj_cos : Disjoint (subFinset H) (z₁ +ᵥ subFinset H) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hx2
        have hz1H : z₁ ∈ H := by
          have : z₁ = (z₁ + h) - h := by abel
          rw [this]; exact H.sub_mem (mem_subFinset.mp hx1) (mem_subFinset.mp hh)
        exact hz₁_not (mem_subFinset.mpr hz1H)
      have hXX_ge_t : t ≤ (X - X).card := by
        have hu := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
        rw [Finset.card_union_of_disjoint hdisj_cos, Finset.card_vadd_finset] at hu
        omega
      have h3m : M < 3 * m := by omega
      have hBm : B.card ≤ m := sumfree_card_le_min_of_three_min_gt_max B m M hBmM hmB h3m hBsf
      exact Or.inr fun x hx => hBm.trans (hm_le x hx)
  · -- Case `k ≥ 3`: `3 * |H| ≤ t ≤ n`, contradicting `15 * B.card > 7 * n + 9`!
    have hk3 : 3 ≤ k := by omega
    have ht_le_n : t ≤ n := by omega
    have h3H : 3 * (subFinset H).card ≤ n := by nlinarith
    omega

end E877Structure


namespace E877Main

open Finset Filter
open scoped Classical
open E877Removal E877Graphs E877Container E877Structure

/-! ## BLST Section 3: Link graphs, container case split, and the `2^((1/4 + δ) n)` bound -/

/-- Sum-free predicate on a `Finset ℕ`. -/
def IsSF (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A

/-- Maximal sum-free subset of `Icc 1 n`. -/
def IsMaxSF (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ IsSF A ∧ ∀ B ⊆ Finset.Icc 1 n, IsSF B → A ⊆ B → A = B

/-- Family of maximal sum-free subsets of `Icc 1 n` contained in a container `A`. -/
noncomputable def maxSFIn (n : ℕ) (A : Finset ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter (IsMaxSF n)

/-- BLST link graph `L_S`: vertices `x, y` are adjacent iff `∃ z ∈ S` with `{x, y, z}` a Schur triple;
a vertex `x` has a loop iff `{x, x, z}` or `{x, z, z'}` is a Schur triple for `z, z' ∈ S`. -/
def linkGraph (S : Finset ℕ) : LGraph where
  adj x y := ∃ z ∈ S, x + y = z ∨ x + z = y ∨ y + z = x
  symm _ _ := fun ⟨z, hz, h⟩ => ⟨z, hz, by rcases h with h | h | h; exact Or.inl (by omega); exact Or.inr (Or.inr h); exact Or.inr (Or.inl h)⟩
  loop x := (∃ z ∈ S, x + x = z ∨ x + z = x) ∨ (∃ z ∈ S, ∃ z' ∈ S, z + z' = x ∨ x + z = z')

/-- **BLST Lemma 3.1**: If `B, S ⊆ Icc 1 n` are disjoint sum-free sets and `I ⊆ B` has `S ∪ I`
maximal sum-free in `Icc 1 n`, then `I` is a maximal independent set of `(linkGraph S)[B]`. -/
lemma claim_mis (n : ℕ) (B S I : Finset ℕ)
    (hBn : B ⊆ Finset.Icc 1 n) (hSn : S ⊆ Finset.Icc 1 n)
    (hBsf : IsSF B) (hSsf : IsSF S) (hdisj : Disjoint B S)
    (hIB : I ⊆ B) (hmax : IsMaxSF n (S ∪ I)) :
    I ∈ (linkGraph S).misSet B := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hIB, ?_, ?_⟩
  · -- `I` is independent in `(linkGraph S)[B]`
    refine ⟨hIB, ?_, ?_⟩
    · intro v hv hloop
      have hvU : v ∈ S ∪ I := Finset.mem_union_right _ hv
      rcases hloop with ⟨z, hz, h | h⟩ | ⟨z, hz, z', hz', h | h⟩
      · exact hmax.2.1 v hvU v hvU (h ▸ Finset.mem_union_left _ hz)
      · exact hmax.2.1 v hvU z (Finset.mem_union_left _ hz) (by rw [h]; exact hvU)
      · exact hmax.2.1 z (Finset.mem_union_left _ hz) z' (Finset.mem_union_left _ hz') (h ▸ hvU)
      · exact hmax.2.1 v hvU z (Finset.mem_union_left _ hz) (h ▸ Finset.mem_union_left _ hz')
    · intro u hu v hv _ hadj
      obtain ⟨z, hz, h | h | h⟩ := hadj
      · exact hmax.2.1 u (Finset.mem_union_right _ hu) v (Finset.mem_union_right _ hv)
          (h ▸ Finset.mem_union_left _ hz)
      · exact hmax.2.1 u (Finset.mem_union_right _ hu) z (Finset.mem_union_left _ hz)
          (h ▸ Finset.mem_union_right _ hv)
      · exact hmax.2.1 v (Finset.mem_union_right _ hv) z (Finset.mem_union_left _ hz)
          (h ▸ Finset.mem_union_right _ hu)
  · -- `I` is maximal independent in `(linkGraph S)[B]`
    intro J hJ hIJ
    obtain ⟨hJB, hJloop, hJadj⟩ := hJ
    have hSJ_sf : IsSF (S ∪ J) := by
      intro a ha b hb hab
      rcases Finset.mem_union.mp ha with haS | haJ <;>
      rcases Finset.mem_union.mp hb with hbS | hbJ <;>
      rcases Finset.mem_union.mp hab with hcS | hcJ
      · exact hSsf a haS b hbS hcS
      · exact hJloop (a + b) hcJ (Or.inr ⟨a, haS, b, hbS, Or.inl rfl⟩)
      · exact hJloop b hbJ (Or.inr ⟨a, haS, a + b, hcS, Or.inr (add_comm b a)⟩)
      · by_cases hbc : b = a + b
        · exact hJloop b hbJ (Or.inl ⟨a, haS, Or.inr (by omega)⟩)
        · exact hJadj b hbJ (a + b) hcJ hbc ⟨a, haS, Or.inr (Or.inl (add_comm b a))⟩
      · exact hJloop a haJ (Or.inr ⟨b, hbS, a + b, hcS, Or.inr rfl⟩)
      · by_cases hac : a = a + b
        · exact hJloop a haJ (Or.inl ⟨b, hbS, Or.inr (by omega)⟩)
        · exact hJadj a haJ (a + b) hcJ hac ⟨b, hbS, Or.inr (Or.inl rfl)⟩
      · by_cases hab_eq : a = b
        · subst hab_eq; exact hJloop a haJ (Or.inl ⟨a + a, hcS, Or.inl rfl⟩)
        · exact hJadj a haJ b hbJ hab_eq ⟨a + b, hcS, Or.inl rfl⟩
      · exact hBsf a (hJB haJ) b (hJB hbJ) (hJB hcJ)
    have hSJ_eq : S ∪ I = S ∪ J :=
      hmax.2.2 (S ∪ J) (Finset.union_subset hSn (hJB.trans hBn)) hSJ_sf
        (Finset.union_subset_union_right hIJ)
    ext x
    constructor
    · intro hx; exact hIJ hx
    · intro hxJ
      have hxU : x ∈ S ∪ I := hSJ_eq ▸ Finset.mem_union_right _ hxJ
      have hxnotS : x ∉ S := Finset.disjoint_left.mp hdisj (hJB hxJ)
      exact (Finset.mem_union.mp hxU).resolve_left hxnotS

/-- Splitting count: for disjoint `B, C ⊆ Icc 1 n` with `B` sum-free, if every sum-free `S ⊆ C`
has `MIS(L_S[B]) ≤ K`, then `|maxSFIn n (B ∪ C)| ≤ 2^|C| * K`. -/
lemma card_maxSFIn_split (n : ℕ) (B C : Finset ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hBn : B ⊆ Finset.Icc 1 n) (hCn : C ⊆ Finset.Icc 1 n)
    (hBsf : IsSF B) (hdisj : Disjoint B C)
    (hMIS : ∀ S ⊆ C, IsSF S → (((linkGraph S).misSet B).card : ℝ) ≤ K) :
    ((maxSFIn n (B ∪ C)).card : ℝ) ≤ (2 : ℝ) ^ (C.card : ℝ) * K := by
  -- Map `M ∈ maxSFIn n (B ∪ C)` to `⟨M ∩ C, M ∩ B⟩` in `Sigma (S ∈ C.powerset.filter IsSF), (linkGraph S).misSet B`!
  set GoodC := C.powerset.filter IsSF
  have hinj : (maxSFIn n (B ∪ C)).card ≤ (GoodC.sigma (fun S => (linkGraph S).misSet B)).card := by
    refine Finset.card_le_card_of_injOn (fun M => ⟨M ∩ C, M ∩ B⟩) ?_ ?_
    · intro M hM
      rw [Finset.mem_coe] at hM ⊢
      obtain ⟨hMsub, hMmax⟩ := Finset.mem_filter.mp hM
      have hMsub' : M ⊆ B ∪ C := Finset.mem_powerset.mp hMsub
      have hMC_sub : M ∩ C ⊆ C := Finset.inter_subset_right
      have hMC_sf : IsSF (M ∩ C) := fun a ha b hb hab =>
        hMmax.2.1 a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1 (Finset.mem_inter.mp hab).1
      have hMC_mem : M ∩ C ∈ GoodC := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hMC_sub, hMC_sf⟩
      have hM_eq : (M ∩ C) ∪ (M ∩ B) = M := by
        ext x; simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        · intro hx
          rcases Finset.mem_union.mp (hMsub' hx) with hxB | hxC
          · exact Or.inr ⟨hx, hxB⟩
          · exact Or.inl ⟨hx, hxC⟩
      refine Finset.mem_sigma.mpr ⟨hMC_mem, ?_⟩
      exact claim_mis n B (M ∩ C) (M ∩ B) hBn (hMC_sub.trans hCn) hBsf hMC_sf
        (hdisj.mono_right hMC_sub) Finset.inter_subset_right (hM_eq.symm ▸ hMmax)
    · intro M₁ hM₁ M₂ hM₂ heq
      rw [Finset.mem_coe] at hM₁ hM₂
      have h1 : M₁ ⊆ B ∪ C := Finset.mem_powerset.mp (Finset.mem_filter.mp hM₁).1
      have h2 : M₂ ⊆ B ∪ C := Finset.mem_powerset.mp (Finset.mem_filter.mp hM₂).1
      have heqC : M₁ ∩ C = M₂ ∩ C := congrArg Sigma.fst heq
      have heqB : M₁ ∩ B = M₂ ∩ B := by
        have h' := Sigma.mk.inj heq
        exact eq_of_heq h'.2
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp (h1 hx) with hxB | hxC
        · exact (Finset.mem_inter.mp (heqB ▸ Finset.mem_inter.mpr ⟨hx, hxB⟩)).1
        · exact (Finset.mem_inter.mp (heqC ▸ Finset.mem_inter.mpr ⟨hx, hxC⟩)).1
      · intro hx
        rcases Finset.mem_union.mp (h2 hx) with hxB | hxC
        · exact (Finset.mem_inter.mp (heqB.symm ▸ Finset.mem_inter.mpr ⟨hx, hxB⟩)).1
        · exact (Finset.mem_inter.mp (heqC.symm ▸ Finset.mem_inter.mpr ⟨hx, hxC⟩)).1
  rw [Finset.card_sigma] at hinj
  have hR : ((maxSFIn n (B ∪ C)).card : ℝ) ≤ ∑ S ∈ GoodC, (((linkGraph S).misSet B).card : ℝ) := by
    exact_mod_cast hinj
  have hsum : ∑ S ∈ GoodC, (((linkGraph S).misSet B).card : ℝ) ≤ ∑ _S ∈ GoodC, K :=
    Finset.sum_le_sum fun S hS => hMIS S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
      (Finset.mem_filter.mp hS).2
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hGood_le : (GoodC.card : ℝ) ≤ (2 : ℝ) ^ (C.card : ℝ) := by
    have hnat : GoodC.card ≤ 2 ^ C.card := by
      calc GoodC.card ≤ C.powerset.card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2 ^ C.card := Finset.card_powerset C
    rw [Real.rpow_natCast]
    exact_mod_cast hnat
  exact (hR.trans hsum).trans (mul_le_mul_of_nonneg_right hGood_le hK)

/-- Numeric helper: `3 ^ (7 / 45 : ℝ) ≤ 2 ^ (1 / 4 : ℝ)` (since `3^28 < 2^45`). -/
lemma three_rpow_seven_over_45_le : (3 : ℝ) ^ (7 / 45 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := by
  have hpow : ((3 : ℝ) ^ (7 / 45 : ℝ)) ^ (180 : ℕ) ≤ ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (180 : ℕ) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ _), ← Real.rpow_natCast ((2 : ℝ) ^ _),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpos1 : (0 : ℝ) ≤ (3 : ℝ) ^ (7 / 45 : ℝ) := by positivity
  have hpos2 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := by positivity
  by_contra hlt
  push Not at hlt
  have hstrict : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (180 : ℕ) < ((3 : ℝ) ^ (7 / 45 : ℝ)) ^ (180 : ℕ) :=
    pow_lt_pow_left₀ hlt hpos2 (by norm_num)
  linarith

/-- Numeric helper: `3 ^ (1 / 7 : ℝ) ≤ 2 ^ (1 / 4 : ℝ)` (since `3^4 = 81 < 128 = 2^7`). -/
lemma three_rpow_one_over_7_le : (3 : ℝ) ^ (1 / 7 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := by
  have hpow : ((3 : ℝ) ^ (1 / 7 : ℝ)) ^ (28 : ℕ) ≤ ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (28 : ℕ) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ _), ← Real.rpow_natCast ((2 : ℝ) ^ _),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpos2 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := by positivity
  by_contra hlt
  push Not at hlt
  have hstrict : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (28 : ℕ) < ((3 : ℝ) ^ (1 / 7 : ℝ)) ^ (28 : ℕ) :=
    pow_lt_pow_left₀ hlt hpos2 (by norm_num)
  linarith

/-- **BLST Lemma 3.2 (Small container)**: If `B, C ⊆ Icc 1 n` are disjoint, `B` is sum-free,
and `15 * B.card ≤ 7 * n + 9`, then `|maxSFIn n (B ∪ C)| ≤ 2 ^ (n / 4 + C.card + 1)`. -/
lemma lem_non_ext (n : ℕ) (B C : Finset ℕ)
    (hBn : B ⊆ Finset.Icc 1 n) (hCn : C ⊆ Finset.Icc 1 n)
    (hBsf : IsSF B) (hdisj : Disjoint B C) (hBsmall : 15 * B.card ≤ 7 * n + 9) :
    ((maxSFIn n (B ∪ C)).card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4 + (C.card : ℝ) + 1) := by
  have hB_exp : (B.card : ℝ) / 3 ≤ (7 / 45 : ℝ) * (n : ℝ) + 1 / 5 := by
    have hR : 15 * (B.card : ℝ) ≤ 7 * (n : ℝ) + 9 := by exact_mod_cast hBsmall
    linarith
  have hK : (3 : ℝ) ^ ((B.card : ℝ) / 3) ≤ (2 : ℝ) ^ ((n : ℝ) / 4 + 1) := by
    calc (3 : ℝ) ^ ((B.card : ℝ) / 3)
        ≤ (3 : ℝ) ^ ((7 / 45 : ℝ) * (n : ℝ) + 1 / 5) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hB_exp
      _ = ((3 : ℝ) ^ (7 / 45 : ℝ)) ^ (n : ℝ) * (3 : ℝ) ^ (1 / 5 : ℝ) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num)]
      _ ≤ ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (n : ℝ) * (2 : ℝ) ^ (1 : ℝ) := by
          apply mul_le_mul
          · exact Real.rpow_le_rpow (by positivity) three_rpow_seven_over_45_le (Nat.cast_nonneg n)
          · have h1 : (3 : ℝ) ^ (1 / 5 : ℝ) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            have h2 : ((3 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) ≤ (2 : ℝ) ^ (2 : ℕ) := by
              rw [← Real.rpow_natCast ((3 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]; norm_num
            have h3 : (3 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
              by_contra hlt; push Not at hlt
              have := pow_lt_pow_left₀ hlt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : 2 ≠ 0)
              linarith
            simpa using h1.trans h3
          · positivity
          · positivity
      _ = (2 : ℝ) ^ ((n : ℝ) / 4 + 1) := by
          rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
          congr 1; ring
  have h1 := card_maxSFIn_split n B C ((2 : ℝ) ^ ((n : ℝ) / 4 + 1)) (by positivity) hBn hCn hBsf hdisj
    fun S _ _ => (moon_moser (linkGraph S) B).trans hK
  calc ((maxSFIn n (B ∪ C)).card : ℝ)
      ≤ (2 : ℝ) ^ (C.card : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 4 + 1) := h1
    _ = (2 : ℝ) ^ ((n : ℝ) / 4 + (C.card : ℝ) + 1) := by
        rw [← Real.rpow_add (by norm_num)]; congr 1; ring

/-- **BLST Lemma 3.3 (Interval container)**: If `B, C ⊆ Icc 1 n` are disjoint, `B` is sum-free,
and `∀ x ∈ B, B.card ≤ x`, then `|maxSFIn n (B ∪ C)| ≤ 2 ^ (n / 4 + C.card + 1)`. -/
lemma lem_interval (n : ℕ) (B C : Finset ℕ)
    (hBn : B ⊆ Finset.Icc 1 n) (hCn : C ⊆ Finset.Icc 1 n)
    (hBsf : IsSF B) (hdisj : Disjoint B C) (hBmin : ∀ x ∈ B, B.card ≤ x) :
    ((maxSFIn n (B ∪ C)).card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4 + (C.card : ℝ) + 1) := by
  set A := B ∪ C
  set A₁ := A.filter (fun x => x ≤ n / 2)
  set A₂ := A \ A₁
  have hA_eq : A₂ ∪ A₁ = A := Finset.sdiff_union_of_subset (Finset.filter_subset _ A)
  have hA_disj : Disjoint A₂ A₁ := Finset.sdiff_disjoint
  have hA₁n : A₁ ⊆ Finset.Icc 1 n := (Finset.filter_subset _ A).trans (Finset.union_subset hBn hCn)
  have hA₂n : A₂ ⊆ Finset.Icc 1 n := Finset.sdiff_subset.trans (Finset.union_subset hBn hCn)
  have hA₂_gt : ∀ x ∈ A₂, n / 2 < x := by
    intro x hx
    obtain ⟨hxA, hxnot⟩ := Finset.mem_sdiff.mp hx
    by_contra hle; push Not at hle
    exact hxnot (Finset.mem_filter.mpr ⟨hxA, hle⟩)
  have hA₂_sf : IsSF A₂ := by
    intro a ha b hb hab
    have ha1 := hA₂_gt a ha
    have hb1 := hA₂_gt b hb
    have habn := (Finset.mem_Icc.mp (hA₂n hab)).2
    omega
  -- `linkGraph S` is triangle-free on `A₂` for any sum-free `S ⊆ Icc 1 n`!
  have htf : ∀ S ⊆ A₁, IsSF S → (linkGraph S).IsTriangleFree A₂ := by
    intro S hSA₁ hSsf u hu v hv w hw huv huw hvw hadj1 hadj2 hadj3
    -- Helper: for any `x < y` in `A₂`, `adj x y` implies `y - x ∈ S` (since `x + y > n`)!
    have hdiff : ∀ x ∈ A₂, ∀ y ∈ A₂, x < y → (linkGraph S).adj x y → y - x ∈ S := by
      intro x hx y hy hxy hadj
      obtain ⟨z, hz, h | h | h⟩ := hadj
      · have hxn := hA₂_gt x hx; have hyn := hA₂_gt y hy
        have hzn := (Finset.mem_Icc.mp (hA₁n (hSA₁ hz))).2
        omega
      · have : y - x = z := by omega
        exact this ▸ hz
      · omega
    -- Sort `{u, v, w}` into `x < y < z`!
    have hordered : ∀ x ∈ A₂, ∀ y ∈ A₂, ∀ z ∈ A₂, x < y → y < z →
        (linkGraph S).adj x y → (linkGraph S).adj y z → (linkGraph S).adj x z → False := by
      intro x hx y hy z hz hxy hyz h1 h2 h3
      have s1 := hdiff x hx y hy hxy h1
      have s2 := hdiff y hy z hz hyz h2
      have s3 := hdiff x hx z hz (lt_trans hxy hyz) h3
      have hsum : (y - x) + (z - y) = z - x := by omega
      exact hSsf (y - x) s1 (z - y) s2 (hsum ▸ s3)
    rcases lt_or_gt_of_ne huv with h1 | h1 <;>
    rcases lt_or_gt_of_ne hvw with h2 | h2 <;>
    rcases lt_or_gt_of_ne huw with h3 | h3
    · exact hordered u hu v hv w hw h1 h2 hadj1 hadj2 hadj3
    · omega
    · exact hordered u hu w hw v hv h3 h2 hadj3 ((linkGraph S).symm v w hadj2) hadj1
    · exact hordered w hw u hu v hv h3 h1 ((linkGraph S).symm u w hadj3) hadj1 ((linkGraph S).symm v w hadj2)
    · exact hordered v hv u hu w hw h1 h3 ((linkGraph S).symm u v hadj1) hadj3 hadj2
    · exact hordered v hv w hw u hu h2 h3 hadj2 ((linkGraph S).symm u w hadj3) ((linkGraph S).symm u v hadj1)
    · omega
    · exact hordered w hw v hv u hu h2 h1 ((linkGraph S).symm v w hadj2) ((linkGraph S).symm u v hadj1)
        ((linkGraph S).symm u w hadj3)
  -- Cardinality inequality: `2 * A₁.card + A₂.card ≤ n / 2 + 1 + 2 * C.card`!
  have hcard_comb : 2 * A₁.card + A₂.card ≤ n / 2 + 1 + 2 * C.card := by
    have hA_card : A₁.card + A₂.card = B.card + C.card := by
      rw [add_comm A₁.card, ← Finset.card_union_of_disjoint hA_disj, hA_eq,
          Finset.card_union_of_disjoint hdisj]
    have hA₁_le : A₁.card ≤ (B.filter (fun x => x ≤ n / 2)).card + C.card := by
      have hsub : A₁ ⊆ B.filter (fun x => x ≤ n / 2) ∪ C := by
        intro x hx
        obtain ⟨hxA, hxle⟩ := Finset.mem_filter.mp hx
        rcases Finset.mem_union.mp hxA with hxB | hxC
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxB, hxle⟩)
        · exact Finset.mem_union_right _ hxC
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    by_cases hBhalf : B.card ≤ n / 2
    · have hBfilt : (B.filter (fun x => x ≤ n / 2)).card ≤ n / 2 + 1 - B.card := by
        have hsub : B.filter (fun x => x ≤ n / 2) ⊆ Finset.Icc B.card (n / 2) := by
          intro x hx
          obtain ⟨hxB, hxle⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_Icc.mpr ⟨hBmin x hxB, hxle⟩
        calc (B.filter (fun x => x ≤ n / 2)).card ≤ (Finset.Icc B.card (n / 2)).card :=
              Finset.card_le_card hsub
          _ = n / 2 + 1 - B.card := Nat.card_Icc _ _
      omega
    · have hBfilt : B.filter (fun x => x ≤ n / 2) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx; have := hBmin x hx; omega
      have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
      set M := B.max' hBne
      have hMn : M ≤ n := (Finset.mem_Icc.mp (hBn (Finset.max'_mem B hBne))).2
      have hpair := sumfree_card_le_half_max B M
        (fun x hx => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hBn hx)).1, Finset.le_max' B x hx⟩)
        (Finset.max'_mem B hBne) hBsf
      rw [hBfilt, Finset.card_empty] at hA₁_le
      omega
  have h1 := card_maxSFIn_split n A₂ A₁ ((2 : ℝ) ^ ((A₂.card : ℝ) / 2)) (by positivity)
    hA₂n hA₁n hA₂_sf hA_disj fun S hS hSsf => hujter_tuza (linkGraph S) A₂ (htf S hS hSsf)
  rw [hA_eq] at h1
  calc ((maxSFIn n (B ∪ C)).card : ℝ)
      ≤ (2 : ℝ) ^ (A₁.card : ℝ) * (2 : ℝ) ^ ((A₂.card : ℝ) / 2) := h1
    _ = (2 : ℝ) ^ ((A₁.card : ℝ) + (A₂.card : ℝ) / 2) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ ((n : ℝ) / 4 + (C.card : ℝ) + 1) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hR : 2 * (A₁.card : ℝ) + (A₂.card : ℝ) ≤ ((n / 2 : ℕ) : ℝ) + 1 + 2 * (C.card : ℝ) := by
          exact_mod_cast hcard_comb
        have hhalf : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
          have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
          have h2 : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
          linarith
        linarith

/-- Helper for `lem_odd` Case 1: degree bounds in `(linkGraph S)[O]` when `S ⊆ Evens ∩ [1, n]`. -/
lemma linkGraph_odd_deg_bounds (n : ℕ) (S : Finset ℕ)
    (hSn : S ⊆ Finset.Icc 1 n) (hSev : ∀ s ∈ S, Even s) :
    let O := (Finset.Icc 1 n).filter Odd
    (∀ x ∈ O, (S.card - 1) / 2 ≤ (linkGraph S).deg O x) ∧
    (∀ x ∈ O, (linkGraph S).deg O x ≤ 2 * S.card + 2) := by
  dsimp only
  set O := (Finset.Icc 1 n).filter Odd
  constructor
  · -- Lower bound: `((S.erase (2 * x)).card) ≤ 2 * (linkGraph S).deg O x`!
    intro x hxO
    obtain ⟨hxI, hxOdd⟩ := Finset.mem_filter.mp hxO
    have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hxI).1
    have hxn : x ≤ n := (Finset.mem_Icc.mp hxI).2
    let f : ℕ → ℕ := fun s => if s < x then x - s else if x + s ≤ n then x + s else s - x
    have hf_mem : ∀ s ∈ S.erase (2 * x), f s ∈ (linkGraph S).nbhd O x := by
      intro s hs
      have hsne2x : s ≠ 2 * x := (Finset.mem_erase.mp hs).1
      have hsS : s ∈ S := Finset.mem_of_mem_erase hs
      have hsI := Finset.mem_Icc.mp (hSn hsS)
      obtain ⟨r, hr⟩ := hSev s hsS
      obtain ⟨k, hk⟩ := hxOdd
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩, ?_⟩
      · dsimp only [f]; split_ifs <;> omega
      · dsimp only [f]; split_ifs <;> exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · dsimp only [f]; split_ifs
        · exact ⟨k - r, by omega⟩
        · exact ⟨k + r, by omega⟩
        · exact ⟨r - k - 1, by omega⟩
      · dsimp only [f]; split_ifs
        · exact ⟨s, hsS, Or.inr (Or.inr (by omega))⟩
        · exact ⟨s, hsS, Or.inr (Or.inl rfl)⟩
        · exact ⟨s, hsS, Or.inl (by omega)⟩
    -- Every `y ∈ nbhd O x` has at most 2 preimages under `f` in `S.erase (2 * x)`!
    have hfib : ∀ y ∈ (linkGraph S).nbhd O x,
        ((S.erase (2 * x)).filter (fun s => f s = y)).card ≤ 2 := by
      intro y hy
      have hyx : y ≠ x := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
      have hsub : (S.erase (2 * x)).filter (fun s => f s = y) ⊆
          ({if x < y then y - x else x - y, x + y} : Finset ℕ) := by
        intro s hs
        obtain ⟨_, hfs⟩ := Finset.mem_filter.mp hs
        simp only [Finset.mem_insert, Finset.mem_singleton]
        dsimp only [f] at hfs
        split_ifs at hfs ⊢ <;> omega
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    have hpart := Finset.card_eq_sum_card_fiberwise (f := f) (s := S.erase (2 * x))
      (t := (linkGraph S).nbhd O x) hf_mem
    have hnbhd_le_deg : ((linkGraph S).nbhd O x).card ≤ (linkGraph S).deg O x := by
      dsimp only [LGraph.deg]; omega
    have hle : (S.erase (2 * x)).card ≤ 2 * (linkGraph S).deg O x := by
      rw [hpart]
      calc ∑ y ∈ (linkGraph S).nbhd O x, ((S.erase (2 * x)).filter (fun s => f s = y)).card
          ≤ ∑ _y ∈ (linkGraph S).nbhd O x, 2 := Finset.sum_le_sum hfib
        _ = ((linkGraph S).nbhd O x).card * 2 := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 2 * (linkGraph S).deg O x := by omega
    have herase : S.card - 1 ≤ (S.erase (2 * x)).card := Finset.pred_card_le_card_erase
    omega
  · -- Upper bound: `nbhd O x ⊆ S.image (fun s => if s < x then x - s else s - x) ∪ S.image (x + ·)`!
    intro x hxO
    have hsub : (linkGraph S).nbhd O x ⊆
        S.image (fun s => if s < x then x - s else s - x) ∪ S.image (fun s => x + s) := by
      intro y hy
      obtain ⟨hyO, ⟨s, hsS, h | h | h⟩⟩ := Finset.mem_filter.mp hy
      have hyI := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hyO)).1
      · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hsS, ?_⟩)
        split_ifs <;> omega
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hsS, h⟩)
      · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hsS, ?_⟩)
        split_ifs <;> omega
    have hnbhd_le : ((linkGraph S).nbhd O x).card ≤ 2 * S.card := by
      calc ((linkGraph S).nbhd O x).card
          ≤ (S.image (fun s => if s < x then x - s else s - x) ∪ S.image (fun s => x + s)).card :=
            Finset.card_le_card hsub
        _ ≤ (S.image (fun s => if s < x then x - s else s - x)).card + (S.image (fun s => x + s)).card :=
            Finset.card_union_le _ _
        _ ≤ S.card + S.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ = 2 * S.card := by omega
    dsimp only [LGraph.deg]
    split_ifs <;> omega

/-- Helper for `lem_odd` Case 2: if `S ⊆ Evens ∩ [1, n]` is sum-free, the vertices of `O` belonging
to at least one triangle in `(linkGraph S)[O]` form a set `T ⊆ O` with `T.card ≤ 12 * S.card ^ 3`! -/
lemma linkGraph_odd_triangles_le (n : ℕ) (S : Finset ℕ) (hSsf : IsSF S) :
    let O := (Finset.Icc 1 n).filter Odd
    ∃ T ⊆ O, T.card ≤ 12 * S.card ^ 3 ∧ (linkGraph S).IsTriangleFree (O \ T) := by
  dsimp only
  set O := (Finset.Icc 1 n).filter Odd
  set G := linkGraph S
  -- Ordered triangles `x < y < z` in `G[O]`
  set Tri := (O ×ˢ O ×ˢ O).filter (fun p =>
    p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ G.adj p.1 p.2.1 ∧ G.adj p.2.1 p.2.2 ∧ G.adj p.1 p.2.2)
  set T := (Tri.image (fun p => p.1)) ∪ (Tri.image (fun p => p.2.1)) ∪ (Tri.image (fun p => p.2.2))
  have hTO : T ⊆ O := by
    refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
    · intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2).1
    · intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2).2
  have htf : G.IsTriangleFree (O \ T) := by
    intro u hu v hv w hw huv huw hvw h1 h2 h3
    have hord : ∀ x ∈ O \ T, ∀ y ∈ O \ T, ∀ z ∈ O \ T, x < y → y < z →
        G.adj x y → G.adj y z → G.adj x z → False := by
      intro x hx y hy z hz hxy hyz ha1 ha2 ha3
      have hmem : (x, (y, z)) ∈ Tri := Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp hx).1,
          Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp hy).1, (Finset.mem_sdiff.mp hz).1⟩⟩,
         hxy, hyz, ha1, ha2, ha3⟩
      have hxT : x ∈ T := Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨(x, (y, z)), hmem, rfl⟩))
      exact (Finset.mem_sdiff.mp hx).2 hxT
    rcases lt_or_gt_of_ne huv with c1 | c1 <;>
    rcases lt_or_gt_of_ne hvw with c2 | c2 <;>
    rcases lt_or_gt_of_ne huw with c3 | c3
    · exact hord u hu v hv w hw c1 c2 h1 h2 h3
    · omega
    · exact hord u hu w hw v hv c3 c2 h3 (G.symm v w h2) h1
    · exact hord w hw u hu v hv c3 c1 (G.symm u w h3) h1 (G.symm v w h2)
    · exact hord v hv u hu w hw c1 c3 (G.symm u v h1) h3 h2
    · exact hord v hv w hw u hu c2 c3 h2 (G.symm u w h3) (G.symm u v h1)
    · omega
    · exact hord w hw v hv u hu c2 c1 (G.symm v w h2) (G.symm u v h1) (G.symm u w h3)
  -- Bound `Tri.card ≤ 4 * S.card ^ 3` by injecting `Tri` into `Fin 4 ×ˢ (S ×ˢ S ×ˢ S)`!
  have hTri_le : Tri.card ≤ 4 * S.card ^ 3 := by
    let encode : ℕ × ℕ × ℕ → Fin 4 × (ℕ × ℕ × ℕ) := fun p =>
      let x := p.1; let y := p.2.1; let z := p.2.2
      if y - x ∈ S then
        if z - y ∈ S then (3, (y - x, z - y, x + z))
        else (2, (y - x, y + z, z - x))
      else
        if z - y ∈ S then (1, (x + y, z - y, z - x))
        else (0, (x + y, y + z, x + z))
    have hadj_iff : ∀ a b : ℕ, a < b → G.adj a b → b - a ∈ S ∨ a + b ∈ S := by
      intro a b hab hadj
      obtain ⟨z, hz, h | h | h⟩ := hadj
      · exact Or.inr (h ▸ hz)
      · exact Or.inl (show b - a = z by omega ▸ hz)
      · omega
    have hinj : Tri.card ≤ ((Finset.univ : Finset (Fin 4)) ×ˢ (S ×ˢ S ×ˢ S)).card := by
      refine Finset.card_le_card_of_injOn encode ?_ ?_
      · intro p hp
        rw [Finset.mem_coe] at hp ⊢
        obtain ⟨_, hxy, hyz, ha1, ha2, ha3⟩ := Finset.mem_filter.mp hp
        have he1 := hadj_iff p.1 p.2.1 hxy ha1
        have he2 := hadj_iff p.2.1 p.2.2 hyz ha2
        have he3 := hadj_iff p.1 p.2.2 (lt_trans hxy hyz) ha3
        simp only [encode, Finset.mem_product, Finset.mem_univ, true_and]
        by_cases b1 : p.2.1 - p.1 ∈ S <;> by_cases b2 : p.2.2 - p.2.1 ∈ S
        · -- `(T, T)`: `p.2.2 - p.1 ∉ S` (by `hSsf`), so `p.1 + p.2.2 ∈ S`!
          have hn3 : p.2.2 - p.1 ∉ S := fun h3 =>
            hSsf (p.2.1 - p.1) b1 (p.2.2 - p.2.1) b2 (show (p.2.1 - p.1) + (p.2.2 - p.2.1) = p.2.2 - p.1 by omega ▸ h3)
          simp only [if_pos b1, if_pos b2]
          exact ⟨b1, b2, he3.resolve_left hn3⟩
        · -- `(T, F)`: `p.2.1 + p.2.2 ∈ S`, so `p.1 + p.2.2 ∉ S` (else `(y-x)+(x+z)=y+z`), hence `p.2.2 - p.1 ∈ S`!
          have hs2 : p.2.1 + p.2.2 ∈ S := he2.resolve_left b2
          have hn3 : p.1 + p.2.2 ∉ S := fun h3 =>
            hSsf (p.2.1 - p.1) b1 (p.1 + p.2.2) h3 (show (p.2.1 - p.1) + (p.1 + p.2.2) = p.2.1 + p.2.2 by omega ▸ hs2)
          simp only [if_pos b1, if_neg b2]
          exact ⟨b1, hs2, he3.resolve_right hn3⟩
        · -- `(F, T)`: `p.1 + p.2.1 ∈ S`, so `p.1 + p.2.2 ∉ S` (else `(z-y)+(x+y)=x+z`), hence `p.2.2 - p.1 ∈ S`!
          have hs1 : p.1 + p.2.1 ∈ S := he1.resolve_left b1
          have hn3 : p.1 + p.2.2 ∉ S := fun h3 =>
            hSsf (p.2.2 - p.2.1) b2 (p.1 + p.2.1) hs1 (show (p.2.2 - p.2.1) + (p.1 + p.2.1) = p.1 + p.2.2 by omega ▸ h3)
          simp only [if_neg b1, if_pos b2]
          exact ⟨hs1, b2, he3.resolve_right hn3⟩
        · -- `(F, F)`: `p.1 + p.2.1 ∈ S`, `p.2.1 + p.2.2 ∈ S`, so `p.2.2 - p.1 ∉ S` (else `(z-x)+(x+y)=y+z`), hence `p.1 + p.2.2 ∈ S`!
          have hs1 : p.1 + p.2.1 ∈ S := he1.resolve_left b1
          have hs2 : p.2.1 + p.2.2 ∈ S := he2.resolve_left b2
          have hn3 : p.2.2 - p.1 ∉ S := fun h3 =>
            hSsf (p.2.2 - p.1) h3 (p.1 + p.2.1) hs1 (show (p.2.2 - p.1) + (p.1 + p.2.1) = p.2.1 + p.2.2 by omega ▸ hs2)
          simp only [if_neg b1, if_neg b2]
          exact ⟨hs1, hs2, he3.resolve_left hn3⟩
      · intro p hp q hq heq
        rw [Finset.mem_coe] at hp hq
        have hp_lt := (Finset.mem_filter.mp hp).2
        have hq_lt := (Finset.mem_filter.mp hq).2
        dsimp only [encode] at heq
        split_ifs at heq <;> simp only [Prod.mk.injEq] at heq
        all_goals
          first
          | (rcases heq with ⟨h0, _⟩; simp at h0)
          | (rcases heq with ⟨_, h1, h2, h3⟩; exact Prod.ext (by omega) (Prod.ext (by omega) (by omega)))
    calc Tri.card ≤ ((Finset.univ : Finset (Fin 4)) ×ˢ (S ×ˢ S ×ˢ S)).card := hinj
      _ = 4 * S.card ^ 3 := by simp [Finset.card_product]; ring
  have hT_card : T.card ≤ 12 * S.card ^ 3 := by
    have hT_eq : T.card = ((Tri.image (fun p => p.1)) ∪ (Tri.image (fun p => p.2.1)) ∪
        (Tri.image (fun p => p.2.2))).card := rfl
    have h1 := Finset.card_union_le ((Tri.image (fun p => p.1)) ∪ (Tri.image (fun p => p.2.1)))
      (Tri.image (fun p => p.2.2))
    have h2 := Finset.card_union_le (Tri.image (fun p => p.1)) (Tri.image (fun p => p.2.1))
    have hi1 : (Tri.image (fun p => p.1)).card ≤ Tri.card := Finset.card_image_le
    have hi2 : (Tri.image (fun p => p.2.1)).card ≤ Tri.card := Finset.card_image_le
    have hi3 : (Tri.image (fun p => p.2.2)).card ≤ Tri.card := Finset.card_image_le
    omega
  exact ⟨T, hTO, hT_card, htf⟩

/-- **BLST Lemma 3.4 (Odd container)**: For any `δ > 0`, eventually in `n`, if `B, C ⊆ Icc 1 n` are
disjoint, every element of `B` is odd, and `C.card ≤ (δ / 8) * n`, then
`|maxSFIn n (B ∪ C)| ≤ 2 ^ ((1 / 4 + δ / 2) * n)`. -/
lemma lem_odd (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ B C : Finset ℕ, B ⊆ Finset.Icc 1 n → C ⊆ Finset.Icc 1 n →
        Disjoint B C → (∀ x ∈ B, Odd x) → (C.card : ℝ) ≤ (δ / 8) * (n : ℝ) →
        ((maxSFIn n (B ∪ C)).card : ℝ) ≤ (2 : ℝ) ^ ((1 / 4 + δ / 2) * (n : ℝ)) := by
  obtain ⟨α, hα_pos, hα⟩ := exists_small_subset_exponent (δ / 8) (by positivity)
  -- Pick `K₀` large enough that for `S.card ≥ K₀`: `δ_deg ≥ 100`, `b = √δ_deg ≥ max (1/α) 10`, and `Δ/(δ+Δ-b) ≤ 6/7`!
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge (max (1 / α) 100)
  -- Also require `n` large enough for both Case 1 (`n ≥ (2 * K₀^2 + 10)^4`) and Case 2 (`12 * n^(3/4) ≤ (δ/8) * n` i.e. `n ≥ (96/δ)^4` and `4 / δ ≤ n`)!
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (max (max ((96 / δ) ^ 4) (16 / δ)) (((2 * K₀ ^ 2 + 10) ^ 4 : ℕ) : ℝ))
  filter_upwards [Filter.eventually_ge_atTop (max N₁ 100)] with n hn
  have hn100 : 100 ≤ n := le_trans (le_max_right _ _) hn
  have hnN₁ : (N₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hnR : max (max ((96 / δ) ^ 4) (16 / δ)) (((2 * K₀ ^ 2 + 10) ^ 4 : ℕ) : ℝ) ≤ (n : ℝ) := hN₁.trans hnN₁
  intro B C hBn hCn _ hBodd hCsmall
  -- Enlarge `B ∪ C` to `O ∪ C'` where `O = (Icc 1 n).filter Odd` and `C' = C \ O` (`⊆ Evens`)!
  set O := (Finset.Icc 1 n).filter Odd
  set C' := C \ O
  have hBC_sub : B ∪ C ⊆ O ∪ C' := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxB | hxC
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hBn hxB, hBodd x hxB⟩)
    · by_cases hxO : x ∈ O
      · exact Finset.mem_union_left _ hxO
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxC, hxO⟩)
  have hOn : O ⊆ Finset.Icc 1 n := Finset.filter_subset _ _
  have hC'n : C' ⊆ Finset.Icc 1 n := Finset.sdiff_subset.trans hCn
  have hOsf : IsSF O := by
    intro a ha b hb hab
    obtain ⟨k₁, hk₁⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨k₂, hk₂⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨k₃, hk₃⟩ := (Finset.mem_filter.mp hab).2
    omega
  have hOC'_disj : Disjoint O C' := Finset.disjoint_sdiff
  have hC'_ev : ∀ s ∈ C', Even s := by
    intro s hs
    obtain ⟨hsC, hsnotO⟩ := Finset.mem_sdiff.mp hs
    have hnotOdd : ¬ Odd s := fun h => hsnotO (Finset.mem_filter.mpr ⟨hCn hsC, h⟩)
    rwa [← Nat.not_even_iff_odd, not_not] at hnotOdd
  have hO_card : O.card ≤ n / 2 + 1 := by
    -- `x ↦ (x - 1) / 2` injects `O` into `Finset.range (n / 2 + 1)`
    have hinj : O.card ≤ (Finset.range (n / 2 + 1)).card := by
      refine Finset.card_le_card_of_injOn (fun x => (x - 1) / 2) ?_ ?_
      · intro x hx
        rw [Finset.mem_coe] at hx ⊢
        dsimp only
        obtain ⟨hxI, ⟨k, hk⟩⟩ := Finset.mem_filter.mp hx
        have := Finset.mem_Icc.mp hxI
        exact Finset.mem_range.mpr (by omega)
      · intro x hx y hy heq
        rw [Finset.mem_coe] at hx hy
        dsimp only at heq
        obtain ⟨_, ⟨k₁, hk₁⟩⟩ := Finset.mem_filter.mp hx
        obtain ⟨_, ⟨k₂, hk₂⟩⟩ := Finset.mem_filter.mp hy
        omega
    rwa [Finset.card_range] at hinj
  have hO_cardR : (O.card : ℝ) ≤ (n : ℝ) / 2 + 1 := by
    have h1 : (O.card : ℝ) ≤ ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hO_card
    have h2 : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.mul_div_le n 2
    linarith
  have hmono : (maxSFIn n (B ∪ C)).card ≤ (maxSFIn n (O ∪ C')).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.powerset_mono.mpr hBC_sub))
  -- Show for every sum-free `S ⊆ C'`, `MIS((linkGraph S)[O]) ≤ 2 ^ ((1 / 4 + 3 * δ / 8) * n)`!
  have hMIS_bd : ∀ S ⊆ C', IsSF S →
      (((linkGraph S).misSet O).card : ℝ) ≤ (2 : ℝ) ^ ((1 / 4 + 3 * δ / 8) * (n : ℝ)) := by
    intro S hSC' hSsf
    by_cases hSbig : n ≤ S.card ^ 4
    · -- **Case 1**: `S.card ^ 4 ≥ n` → Sapozhenko (`sapozhenko_mis`)!
      have hS_ge : 2 * K₀ ^ 2 + 10 ≤ S.card := by
        have hnat : (2 * K₀ ^ 2 + 10) ^ 4 ≤ n := by
          have : (((2 * K₀ ^ 2 + 10) ^ 4 : ℕ) : ℝ) ≤ (n : ℝ) := (le_max_right _ _).trans hnR
          exact_mod_cast this
        by_contra hlt; push Not at hlt
        have h4 : S.card ^ 4 < (2 * K₀ ^ 2 + 10) ^ 4 := Nat.pow_lt_pow_left hlt (by norm_num)
        omega
      have hdeg := linkGraph_odd_deg_bounds n S (hSC'.trans hC'n) (fun s hs => hC'_ev s (hSC' hs))
      set δd := (S.card - 1) / 2
      set Δd := 2 * S.card + 2
      set b := Nat.sqrt δd
      have hK₀100 : 100 ≤ K₀ := by
        have : (100 : ℝ) ≤ (K₀ : ℝ) := (le_max_right _ _).trans hK₀
        exact_mod_cast this
      have hδd_ge : K₀ ^ 2 ≤ δd := by omega
      have hb_ge_K₀ : K₀ ≤ b := Nat.le_sqrt.mpr (by nlinarith)
      have hb_pos : 1 ≤ b := by omega
      have hb_sq : b * b ≤ δd := Nat.sqrt_le δd
      have hb_lt_δd : b < δd := by nlinarith
      have hsap := sapozhenko_mis (linkGraph S) O b δd Δd hb_pos hb_lt_δd hdeg.1 hdeg.2
      -- Bound small subsets factor `≤ 2 ^ ((δ / 8) * n)` via `exists_small_subset_exponent`
      have hsmall_le : ((O.powerset.filter (fun T => T.card ≤ O.card / b)).card : ℝ) ≤
          (2 : ℝ) ^ ((δ / 8) * (n : ℝ)) := by
        apply hα n O (by calc O.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hOn
                            _ = n := by simp) (O.card / b)
        have h1 : (O.card / b : ℕ) * b ≤ O.card := Nat.div_mul_le_self _ _
        have h1R : ((O.card / b : ℕ) : ℝ) * (b : ℝ) ≤ (O.card : ℝ) := by exact_mod_cast h1
        have hinv : 1 / α ≤ (b : ℝ) := by
          have : 1 / α ≤ (K₀ : ℝ) := (le_max_left _ _).trans hK₀
          exact this.trans (by exact_mod_cast hb_ge_K₀)
        have hbR_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
        have h2 : 1 ≤ α * (b : ℝ) := by linarith [(div_le_iff₀ hα_pos).mp hinv]
        have hO_le_n : (O.card : ℝ) ≤ (n : ℝ) := by
          have : O.card ≤ n := by calc O.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hOn
                                    _ = n := by simp
          exact_mod_cast this
        nlinarith
      -- Bound `Δd / (δd + Δd - b) ≤ 6 / 7`!
      have hfrac : (Δd : ℝ) / ((δd : ℝ) + (Δd : ℝ) - (b : ℝ)) ≤ 6 / 7 := by
        have hdenom_pos : (0 : ℝ) < (δd : ℝ) + (Δd : ℝ) - (b : ℝ) := by
          have : (b : ℝ) < (δd : ℝ) := by exact_mod_cast hb_lt_δd
          have : (0 : ℝ) ≤ (Δd : ℝ) := Nat.cast_nonneg _
          linarith
        rw [div_le_iff₀ hdenom_pos]
        have h10b : 10 * b ≤ δd := by nlinarith
        have hδ_big : 2 * δd + 2 ≥ S.card := by omega
        have h10bR : 10 * (b : ℝ) ≤ (δd : ℝ) := by exact_mod_cast h10b
        have hδR : (S.card : ℝ) ≤ 2 * (δd : ℝ) + 2 := by exact_mod_cast hδ_big
        have hΔR : (Δd : ℝ) = 2 * (S.card : ℝ) + 2 := by exact_mod_cast (rfl : Δd = 2 * S.card + 2)
        have hS100 : (100 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast (show 100 ≤ S.card by nlinarith)
        linarith
      -- Therefore `3 ^ ((Δd * O.card / (δd + Δd - b)) / 3) ≤ 2 ^ (n / 4 + 1)`!
      have h3pow : (3 : ℝ) ^ (((Δd : ℝ) * (O.card : ℝ) / ((δd : ℝ) + (Δd : ℝ) - (b : ℝ))) / 3) ≤
          (2 : ℝ) ^ ((n : ℝ) / 4 + 1) := by
        have hexp : ((Δd : ℝ) * (O.card : ℝ) / ((δd : ℝ) + (Δd : ℝ) - (b : ℝ))) / 3 ≤
            (1 / 7 : ℝ) * (n : ℝ) + 2 / 7 := by
          have hrew : ((Δd : ℝ) * (O.card : ℝ) / ((δd : ℝ) + (Δd : ℝ) - (b : ℝ))) / 3 =
              ((Δd : ℝ) / ((δd : ℝ) + (Δd : ℝ) - (b : ℝ))) * ((O.card : ℝ) / 3) := by ring
          rw [hrew]
          calc ((Δd : ℝ) / ((δd : ℝ) + (Δd : ℝ) - (b : ℝ))) * ((O.card : ℝ) / 3)
              ≤ (6 / 7 : ℝ) * ((O.card : ℝ) / 3) := mul_le_mul_of_nonneg_right hfrac (by positivity)
            _ ≤ (6 / 7 : ℝ) * (((n : ℝ) / 2 + 1) / 3) := by linarith
            _ = (1 / 7 : ℝ) * (n : ℝ) + 2 / 7 := by ring
        calc (3 : ℝ) ^ (((Δd : ℝ) * (O.card : ℝ) / ((δd : ℝ) + (Δd : ℝ) - (b : ℝ))) / 3)
            ≤ (3 : ℝ) ^ ((1 / 7 : ℝ) * (n : ℝ) + 2 / 7) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
          _ = ((3 : ℝ) ^ (1 / 7 : ℝ)) ^ (n : ℝ) * (3 : ℝ) ^ (2 / 7 : ℝ) := by
              rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num)]
          _ ≤ ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (n : ℝ) * (2 : ℝ) ^ (1 : ℝ) := by
              apply mul_le_mul
              · exact Real.rpow_le_rpow (by positivity) three_rpow_one_over_7_le (Nat.cast_nonneg n)
              · have h1 : (3 : ℝ) ^ (2 / 7 : ℝ) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                have h2 : ((3 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) ≤ (2 : ℝ) ^ (2 : ℕ) := by
                  rw [← Real.rpow_natCast ((3 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]; norm_num
                have h3 : (3 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
                  by_contra hlt; push Not at hlt
                  have := pow_lt_pow_left₀ hlt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : 2 ≠ 0)
                  linarith
                simpa using h1.trans h3
              · positivity
              · positivity
          _ = (2 : ℝ) ^ ((n : ℝ) / 4 + 1) := by
              rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
              congr 1; ring
      have h16 : 16 / δ ≤ (n : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hnR)
      have h16' : 16 ≤ δ * (n : ℝ) := by linarith [(div_le_iff₀ hδ).mp h16]
      calc (((linkGraph S).misSet O).card : ℝ)
          ≤ (2 : ℝ) ^ ((δ / 8) * (n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 4 + 1) :=
            hsap.trans (mul_le_mul hsmall_le h3pow (by positivity) (by positivity))
        _ = (2 : ℝ) ^ ((δ / 8) * (n : ℝ) + ((n : ℝ) / 4 + 1)) :=
            (Real.rpow_add (by norm_num) _ _).symm
        _ ≤ (2 : ℝ) ^ ((1 / 4 + 3 * δ / 8) * (n : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num); linarith
    · -- **Case 2**: `S.card ^ 4 < n` → few triangles (`|T| ≤ 12 |S|^3`) + `hujter_tuza_with_triangles`!
      push Not at hSbig
      obtain ⟨T, hTO, hT_le, htf⟩ := linkGraph_odd_triangles_le n S hSsf
      have hht := hujter_tuza_with_triangles (linkGraph S) O T hTO htf
      -- Show `(T.card : ℝ) ≤ (δ / 8) * n` from `S.card ^ 4 < n` and `(96 / δ) ^ 4 ≤ n`!
      have hT_small : (T.card : ℝ) ≤ (δ / 8) * (n : ℝ) := by
        have h96 : (96 / δ) ^ 4 ≤ (n : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hnR)
        have hS4 : ((S.card : ℝ)) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hSbig.le
        have hpow4 : (12 * (S.card : ℝ) ^ 3) ^ 4 ≤ ((δ / 8) * (n : ℝ)) ^ 4 := by
          have h1 : (12 * (S.card : ℝ) ^ 3) ^ 4 = (12 : ℝ) ^ 4 * ((S.card : ℝ) ^ 4) ^ 3 := by ring
          have h2 : (12 : ℝ) ^ 4 ≤ (δ / 8) ^ 4 * (n : ℝ) := by
            have h3 : (96 : ℝ) ^ 4 / δ ^ 4 ≤ (n : ℝ) := by rwa [div_pow] at h96
            have h4 : (96 : ℝ) ^ 4 ≤ (n : ℝ) * δ ^ 4 := (div_le_iff₀ (by positivity)).mp h3
            have h5 : (12 : ℝ) ^ 4 = (96 : ℝ) ^ 4 / (8 : ℝ) ^ 4 := by norm_num
            have h6 : (δ / 8) ^ 4 = δ ^ 4 / (8 : ℝ) ^ 4 := by ring
            rw [h5, h6]; linarith
          rw [h1]
          calc (12 : ℝ) ^ 4 * ((S.card : ℝ) ^ 4) ^ 3
              ≤ ((δ / 8) ^ 4 * (n : ℝ)) * (n : ℝ) ^ 3 := by
                apply mul_le_mul h2 (pow_le_pow_left₀ (by positivity) hS4 3) (by positivity) (by positivity)
            _ = ((δ / 8) * (n : ℝ)) ^ 4 := by ring
        have h12le : 12 * (S.card : ℝ) ^ 3 ≤ (δ / 8) * (n : ℝ) := by
          by_contra hlt; push Not at hlt
          have := pow_lt_pow_left₀ hlt (by positivity) (by norm_num : 4 ≠ 0)
          linarith
        exact (by exact_mod_cast hT_le : (T.card : ℝ) ≤ 12 * (S.card : ℝ) ^ 3).trans h12le
      have h16 : 16 / δ ≤ (n : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hnR)
      have h16' : 16 ≤ δ * (n : ℝ) := by linarith [(div_le_iff₀ hδ).mp h16]
      calc (((linkGraph S).misSet O).card : ℝ)
          ≤ (2 : ℝ) ^ (((O.card : ℝ) + (T.card : ℝ)) / 2) := hht
        _ ≤ (2 : ℝ) ^ ((1 / 4 + 3 * δ / 8) * (n : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num); linarith
  have hsplit := card_maxSFIn_split n O C' ((2 : ℝ) ^ ((1 / 4 + 3 * δ / 8) * (n : ℝ))) (by positivity)
    hOn hC'n hOsf hOC'_disj hMIS_bd
  have hC'_le : (C'.card : ℝ) ≤ (δ / 8) * (n : ℝ) :=
    (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : C' ⊆ C) : (C'.card : ℝ) ≤ C.card).trans hCsmall
  calc ((maxSFIn n (B ∪ C)).card : ℝ)
      ≤ ((maxSFIn n (O ∪ C')).card : ℝ) := by exact_mod_cast hmono
    _ ≤ (2 : ℝ) ^ (C'.card : ℝ) * (2 : ℝ) ^ ((1 / 4 + 3 * δ / 8) * (n : ℝ)) := hsplit
    _ = (2 : ℝ) ^ ((C'.card : ℝ) + (1 / 4 + 3 * δ / 8) * (n : ℝ)) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ ((1 / 4 + δ / 2) * (n : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num); linarith

/-- **BLST Main Upper Bound Theorem (2015)**:
For every `δ > 0`, eventually in `n`, the total number of maximal sum-free subsets of `[1, n]`
is at most `2 ^ ((1 / 4 + δ) * n)`. -/
theorem blst_upper_bound :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop,
      (((Finset.Icc 1 n).powerset.filter (IsMaxSF n)).card : ℝ) ≤
        (2 : ℝ) ^ ((1 / 4 + δ) * (n : ℝ)) := by
  intro δ hδ
  -- Set removal tolerance `η := δ / 8` and container exponent `δ / 2`!
  obtain ⟨ε, hε, hrem⟩ := schur_removal (δ / 8) (by positivity)
  have hcont := schur_container (ε / 2) (δ / 2) (by positivity) (by positivity)
  have hodd := lem_odd δ hδ
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (16 / δ)
  filter_upwards [hcont, hodd, Filter.eventually_ge_atTop (max N₀ 10)] with n hcont_n hodd_n hn
  obtain ⟨F, hFcard, hFprop, hFcov⟩ := hcont_n
  have hn1 : 1 ≤ n := by have : 10 ≤ n := le_trans (le_max_right _ _) hn; omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn16 : 16 ≤ δ * (n : ℝ) := by
    have h1 : 16 / δ ≤ (n : ℝ) := hN₀.trans (by exact_mod_cast le_trans (le_max_left _ _) hn)
    linarith [(div_le_iff₀ hδ).mp h1]
  -- Every maximal sum-free set `S ⊆ Icc 1 n` is contained in some container `A ∈ F`!
  have hcov_all : (Finset.Icc 1 n).powerset.filter (IsMaxSF n) ⊆ F.biUnion (maxSFIn n) := by
    intro S hS
    obtain ⟨hSpow, hSmax⟩ := Finset.mem_filter.mp hS
    obtain ⟨A, hAF, hSA⟩ := hFcov S (Finset.mem_powerset.mp hSpow) hSmax.2.1
    exact Finset.mem_biUnion.mpr ⟨A, hAF, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSA, hSmax⟩⟩
  -- For EVERY container `A ∈ F`, `|maxSFIn n A| ≤ 2 ^ ((1 / 4 + δ / 2) * n)`!
  have hper_container : ∀ A ∈ F,
      ((maxSFIn n A).card : ℝ) ≤ (2 : ℝ) ^ ((1 / 4 + δ / 2) * (n : ℝ)) := by
    intro A hAF
    obtain ⟨hAn, hAtri⟩ := hFprop A hAF
    -- Apply `schur_removal` to `A` (`schurTriples A` has `≤ (ε / 2) * n^2 < ε * n^2` pairs)
    have hrem_tri : ((E877Removal.schurTriples A).card : ℝ) < ε * (n : ℝ) ^ 2 := by
      have heq : E877Removal.schurTriples A = E877Container.schurTriples A := rfl
      rw [heq]
      have hpos : (0 : ℝ) < (ε / 2) * (n : ℝ) ^ 2 := by positivity
      linarith
    obtain ⟨B, C₀, hA_eq₀, hBsf, hC₀_card⟩ := hrem n hn1 A hAn hrem_tri
    have hBA : B ⊆ A := by rw [hA_eq₀]; exact Finset.subset_union_left
    set C := A \ B
    have hA_eq : B ∪ C = A := Finset.union_sdiff_of_subset hBA
    have hdisj : Disjoint B C := Finset.disjoint_sdiff
    have hBn : B ⊆ Finset.Icc 1 n := hBA.trans hAn
    have hCn : C ⊆ Finset.Icc 1 n := Finset.sdiff_subset.trans hAn
    have hC_sub_C₀ : C ⊆ C₀ := by
      intro x hx
      obtain ⟨hxA, hxnotB⟩ := Finset.mem_sdiff.mp hx
      rw [hA_eq₀] at hxA
      exact (Finset.mem_union.mp hxA).resolve_left hxnotB
    have hC_le : (C.card : ℝ) ≤ (δ / 8) * (n : ℝ) :=
      (by exact_mod_cast Finset.card_le_card hC_sub_C₀ : (C.card : ℝ) ≤ (C₀.card : ℝ)).trans hC₀_card
    rw [← hA_eq]
    by_cases hBsmall : 15 * B.card ≤ 7 * n + 9
    · -- Small container (`|B| ≤ (7/15) n + 9/15`) → `lem_non_ext`!
      have h1 := lem_non_ext n B C hBn hCn hBsf hdisj hBsmall
      exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    · -- Large container (`15 * |B| > 7 * n + 9`) → `sumfree_structure`!
      push Not at hBsmall
      rcases sumfree_structure n B hBn hBsf hBsmall with hBodd | hBmin
      · exact hodd_n B C hBn hCn hdisj hBodd hC_le
      · have h1 := lem_interval n B C hBn hCn hBsf hdisj hBmin
        exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  -- Sum over all `A ∈ F`!
  have hsum_nat : ((Finset.Icc 1 n).powerset.filter (IsMaxSF n)).card ≤
      ∑ A ∈ F, (maxSFIn n A).card :=
    (Finset.card_le_card hcov_all).trans Finset.card_biUnion_le
  have hsum_R : (((Finset.Icc 1 n).powerset.filter (IsMaxSF n)).card : ℝ) ≤
      ∑ A ∈ F, ((maxSFIn n A).card : ℝ) := by exact_mod_cast hsum_nat
  calc (((Finset.Icc 1 n).powerset.filter (IsMaxSF n)).card : ℝ)
      ≤ ∑ A ∈ F, ((maxSFIn n A).card : ℝ) := hsum_R
    _ ≤ ∑ _A ∈ F, (2 : ℝ) ^ ((1 / 4 + δ / 2) * (n : ℝ)) := Finset.sum_le_sum hper_container
    _ = (F.card : ℝ) * (2 : ℝ) ^ ((1 / 4 + δ / 2) * (n : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ ((δ / 2) * (n : ℝ)) * (2 : ℝ) ^ ((1 / 4 + δ / 2) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hFcard (by positivity)
    _ = (2 : ℝ) ^ ((1 / 4 + δ) * (n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]; congr 1; ring

end E877Main


open scoped Pointwise in
lemma isMaximalSumFree_iff_isMaxSF (n : ℕ) (A : Finset ℕ) :
    Erdos877.IsMaximalSumFree n A ↔ E877Main.IsMaxSF n A := by
  have hsf : ∀ S : Finset ℕ, IsSumFree (S : Set ℕ) ↔ E877Main.IsSF S := fun S => by
    unfold IsSumFree
    constructor
    · intro h a ha b hb hab
      have hmem : a + b ∈ (S : Set ℕ) + (S : Set ℕ) := Set.add_mem_add ha hb
      exact Set.disjoint_left.mp h hmem hab
    · intro h
      rw [Set.disjoint_left]
      intro x hx1 hx2
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx1
      exact h a ha b hb hx2
  constructor
  · rintro ⟨hsub, h1, h2⟩
    exact ⟨hsub, (hsf A).mp h1, fun B hBn hBsf hAB => h2 B hBn ((hsf B).mpr hBsf) hAB⟩
  · rintro ⟨hsub, h1, h2⟩
    exact ⟨hsub, (hsf A).mpr h1, fun B hBn hBsf hAB => h2 B hBn ((hsf B).mp hBsf) hAB⟩

theorem OMA.solution :
    OMA.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1_H2_R1.H2 := by
  classical
  intro δ hδ
  filter_upwards [E877Main.blst_upper_bound δ hδ] with n hn
  have hsub :
      (((Finset.Icc 1 n).powerset.filter (Erdos877.IsMaximalSumFree n)).filter
        (fun A => ¬ 64 * A.card ≤ n)) ⊆
      (Finset.Icc 1 n).powerset.filter (E877Main.IsMaxSF n) := by
    intro A hA
    obtain ⟨h1, _⟩ := Finset.mem_filter.mp hA
    obtain ⟨hp, hmax⟩ := Finset.mem_filter.mp h1
    exact Finset.mem_filter.mpr ⟨hp, (isMaximalSumFree_iff_isMaxSF n A).mp hmax⟩
  exact (by exact_mod_cast Finset.card_le_card hsub :
    ((((Finset.Icc 1 n).powerset.filter (Erdos877.IsMaximalSumFree n)).filter
      (fun A => ¬ 64 * A.card ≤ n)).card : ℝ) ≤
    (((Finset.Icc 1 n).powerset.filter (E877Main.IsMaxSF n)).card : ℝ)).trans hn
