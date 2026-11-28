import FormalConjectures.Paper.BollobasEldridgeCatlinConjecture

/-!
Reduction of `BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_three_large_n`

We reduce the large-`n`, maximum-degree-at-most-3 Bollobas-Eldridge-Catlin graph packing theorem
to two canonical `Fin n` minimum-degree host embedding theorems:

- `H1`: Aigner-Brandt (1993) embedding of any graph `F` on `Fin n` (`1 ≤ n`) with `F.maxDegree = 2`
  into any host graph `H` on `Fin n` satisfying `∀ v, 2 * n ≤ 3 * H.degree v + 1`.
- `H2`: Csaba-Shokoufandeh-Szemeredi (2003) embedding of any graph `F` on `Fin n` (`n₀ ≤ n`) with
  `F.maxDegree = 3` into any host graph `H` on `Fin n` satisfying `∀ v, 3 * n ≤ 4 * H.degree v + 1`.

Inside this file we prove completely from scratch:
1. The Sauer-Spencer packing theorem (1978): `2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V`
   implies `BollobasEldridgeCatlinConjecture.Packs G₁ G₂`, proved via a minimum-conflict
   permutation and a single transposition swap avoiding the forbidden partner neighborhood.
2. All `G₁.maxDegree ≤ 1` cases (`Δ₁ = 0` and `Δ₁ = 1`) for `1 ≤ Fintype.card V` directly from
   our proof of Sauer-Spencer.
3. Canonical `Fin n` transport via `Fintype.equivFin V`, preservation of vertex degrees and
   maximum degrees under `SimpleGraph.comap`, exact complement-host minimum-degree conversion
   `(k + 1) * (G₂.maxDegree + 1) ≤ n + 1 → ∀ v, k * n ≤ (k + 1) * H.degree v + 1` for
   `k ∈ {2, 3}`, and lifting any injective embedding into the complement host to a packing
   permutation `Equiv.Perm V`.
-/

namespace OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_three_large_n_R1

/-- Aigner-Brandt (1993): every graph `F` on `Fin n` (`1 ≤ n`) of maximum degree `2` embeds into
every host graph `H` on `Fin n` satisfying `∀ v, 2 * n ≤ 3 * H.degree v + 1`. -/
def H1 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (F H : SimpleGraph (Fin n)) [DecidableRel F.Adj] [DecidableRel H.Adj],
    F.maxDegree = 2 → (∀ v : Fin n, 2 * n ≤ 3 * H.degree v + 1) →
    ∃ f : Fin n → Fin n, Function.Injective f ∧ ∀ u v : Fin n, F.Adj u v → H.Adj (f u) (f v)

/-- Csaba-Shokoufandeh-Szemeredi (2003): for sufficiently large `n`, every graph `F` on `Fin n`
of maximum degree `3` embeds into every host graph `H` on `Fin n` satisfying
`∀ v, 3 * n ≤ 4 * H.degree v + 1`. -/
def H2 : Prop :=
  ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ (F H : SimpleGraph (Fin n)) [DecidableRel F.Adj] [DecidableRel H.Adj],
      F.maxDegree = 3 → (∀ v : Fin n, 3 * n ≤ 4 * H.degree v + 1) →
      ∃ f : Fin n → Fin n, Function.Injective f ∧ ∀ u v : Fin n, F.Adj u v → H.Adj (f u) (f v)

lemma sauer_spencer_from_scratch
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) :
    BollobasEldridgeCatlinConjecture.Packs G₁ G₂ := by
  let bad : Equiv.Perm V → Finset (V × V) := fun σ =>
    Finset.univ.filter (fun p : V × V => G₁.Adj p.1 p.2 ∧ G₂.Adj (σ p.1) (σ p.2))
  have hne : (Finset.univ : Finset (Equiv.Perm V)).Nonempty := ⟨1, Finset.mem_univ _⟩
  obtain ⟨σ, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Equiv.Perm V)) (fun τ => (bad τ).card) hne
  refine ⟨σ, ?_⟩
  intro u v h1 h2
  have huv : u ≠ v := G₁.ne_of_adj h1
  let B₁ : Finset V :=
    (G₁.neighborFinset u).biUnion (fun x => (G₂.neighborFinset (σ x)).image σ.symm)
  let B₂ : Finset V :=
    (G₂.neighborFinset (σ u)).biUnion (fun z => G₁.neighborFinset (σ.symm z))
  have huB₁ : u ∈ B₁ := by
    rw [Finset.mem_biUnion]
    refine ⟨v, by rw [SimpleGraph.mem_neighborFinset]; exact h1, ?_⟩
    exact Finset.mem_image.mpr ⟨σ u, by rw [SimpleGraph.mem_neighborFinset]; exact h2.symm, σ.symm_apply_apply u⟩
  have huB₂ : u ∈ B₂ := by
    rw [Finset.mem_biUnion]
    refine ⟨σ v, by rw [SimpleGraph.mem_neighborFinset]; exact h2, ?_⟩
    rw [σ.symm_apply_apply, SimpleGraph.mem_neighborFinset]
    exact h1.symm
  have hinter : 1 ≤ (B₁ ∩ B₂).card :=
    Finset.one_le_card.mpr ⟨u, Finset.mem_inter.mpr ⟨huB₁, huB₂⟩⟩
  have hcardB₁ : B₁.card ≤ G₁.maxDegree * G₂.maxDegree := by
    calc
      B₁.card
          ≤ ∑ x ∈ G₁.neighborFinset u, ((G₂.neighborFinset (σ x)).image σ.symm).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ G₁.neighborFinset u, G₂.maxDegree := by
            refine Finset.sum_le_sum fun x _ => ?_
            exact Finset.card_image_le.trans
              (by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact G₂.degree_le_maxDegree (σ x))
      _ = G₁.degree u * G₂.maxDegree := by
            rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul]
      _ ≤ G₁.maxDegree * G₂.maxDegree :=
            Nat.mul_le_mul_right _ (G₁.degree_le_maxDegree u)
  have hcardB₂ : B₂.card ≤ G₁.maxDegree * G₂.maxDegree := by
    calc
      B₂.card
          ≤ ∑ z ∈ G₂.neighborFinset (σ u), (G₁.neighborFinset (σ.symm z)).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ G₂.neighborFinset (σ u), G₁.maxDegree := by
            refine Finset.sum_le_sum fun z _ => ?_
            rw [SimpleGraph.card_neighborFinset_eq_degree]
            exact G₁.degree_le_maxDegree (σ.symm z)
      _ = G₂.degree (σ u) * G₁.maxDegree := by
            rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul]
      _ ≤ G₂.maxDegree * G₁.maxDegree :=
            Nat.mul_le_mul_right _ (G₂.degree_le_maxDegree (σ u))
      _ = G₁.maxDegree * G₂.maxDegree := Nat.mul_comm _ _
  have hunion_card : (insert v (B₁ ∪ B₂)).card < (Finset.univ : Finset V).card := by
    have h12 : (B₁ ∪ B₂).card + (B₁ ∩ B₂).card = B₁.card + B₂.card :=
      Finset.card_union_add_card_inter B₁ B₂
    have hins : (insert v (B₁ ∪ B₂)).card ≤ (B₁ ∪ B₂).card + 1 :=
      Finset.card_insert_le v (B₁ ∪ B₂)
    have h2mul :
        2 * G₁.maxDegree * G₂.maxDegree =
          G₁.maxDegree * G₂.maxDegree + G₁.maxDegree * G₂.maxDegree := by
      ring
    rw [Finset.card_univ]
    omega
  have hssub : insert v (B₁ ∪ B₂) ⊂ (Finset.univ : Finset V) := by
    rw [Finset.ssubset_univ_iff]
    intro heq
    rw [heq] at hunion_card
    exact lt_irrefl _ hunion_card
  obtain ⟨w, -, hw⟩ := Finset.exists_of_ssubset hssub
  have hwv : w ≠ v := fun hEq => hw (by rw [hEq]; exact Finset.mem_insert_self v _)
  have hwB₁ : w ∉ B₁ := fun hmem =>
    hw (Finset.mem_insert_of_mem (Finset.mem_union_left B₂ hmem))
  have hwB₂ : w ∉ B₂ := fun hmem =>
    hw (Finset.mem_insert_of_mem (Finset.mem_union_right B₁ hmem))
  have hmemB₁ : ∀ x, G₁.Adj u x → G₂.Adj (σ x) (σ w) → False := by
    intro x hux hxw
    apply hwB₁
    rw [Finset.mem_biUnion]
    refine ⟨x, by rw [SimpleGraph.mem_neighborFinset]; exact hux, ?_⟩
    exact Finset.mem_image.mpr ⟨σ w, by rw [SimpleGraph.mem_neighborFinset]; exact hxw, σ.symm_apply_apply w⟩
  have hmemB₂ : ∀ y, G₂.Adj (σ u) (σ y) → G₁.Adj y w → False := by
    intro y huy hyw
    apply hwB₂
    rw [Finset.mem_biUnion]
    refine ⟨σ y, by rw [SimpleGraph.mem_neighborFinset]; exact huy, ?_⟩
    rw [σ.symm_apply_apply, SimpleGraph.mem_neighborFinset]
    exact hyw
  let σ' : Equiv.Perm V := σ * Equiv.swap u w
  have hσ'_u : σ' u = σ w := by
    simp [σ', Equiv.Perm.mul_apply]
  have hσ'_w : σ' w = σ u := by
    simp [σ', Equiv.Perm.mul_apply]
  have hσ'_other : ∀ x, x ≠ u → x ≠ w → σ' x = σ x := by
    intro x hxu hxw
    simp [σ', Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxu hxw]
  have hsub_bad : bad σ' ⊆ bad σ := by
    intro p hp
    rcases p with ⟨a, b⟩
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rcases hp with ⟨hab₁, hab₂⟩
    refine ⟨hab₁, ?_⟩
    by_cases hau : a = u
    · subst a
      by_cases hbw : b = w
      · subst b
        rw [hσ'_u, hσ'_w] at hab₂
        exact hab₂.symm
      · have hbu : b ≠ u := (G₁.ne_of_adj hab₁).symm
        rw [hσ'_u, hσ'_other b hbu hbw] at hab₂
        exact False.elim (hmemB₁ b hab₁ hab₂.symm)
    · by_cases haw : a = w
      · subst a
        by_cases hbu : b = u
        · subst b
          rw [hσ'_w, hσ'_u] at hab₂
          exact hab₂.symm
        · have hbw : b ≠ w := (G₁.ne_of_adj hab₁).symm
          rw [hσ'_w, hσ'_other b hbu hbw] at hab₂
          exact False.elim (hmemB₂ b hab₂ hab₁.symm)
      · by_cases hbu : b = u
        · subst b
          rw [hσ'_other a hau haw, hσ'_u] at hab₂
          exact False.elim (hmemB₁ a hab₁.symm hab₂)
        · by_cases hbw : b = w
          · subst b
            rw [hσ'_other a hau haw, hσ'_w] at hab₂
            exact False.elim (hmemB₂ a hab₂.symm hab₁)
          · rw [hσ'_other a hau haw, hσ'_other b hbu hbw] at hab₂
            exact hab₂
  have huv_in : (u, v) ∈ bad σ := by
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h1, h2⟩
  have huv_not_in : (u, v) ∉ bad σ' := by
    intro hmem
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hvu : v ≠ u := huv.symm
    have hvw : v ≠ w := hwv.symm
    rw [hσ'_u, hσ'_other v hvu hvw] at hmem
    exact hmemB₁ v h1 hmem.2.symm
  have hlt_bad : (bad σ').card < (bad σ).card := by
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsub_bad, ?_⟩
    intro heq
    exact huv_not_in (heq ▸ huv_in)
  exact not_le_of_gt hlt_bad (hmin σ' (Finset.mem_univ _))

lemma degree_comap_equiv
    {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : V ≃ W) [DecidableRel (G.comap e.symm).Adj] (w : W) :
    (G.comap e.symm).degree w = G.degree (e.symm w) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_nbij' (fun x => e.symm x) (fun y => e y) ?_ ?_ ?_ ?_
  · intro x hx
    dsimp only
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hx ⊢
    exact hx
  · intro y hy
    dsimp only
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy ⊢
    change G.Adj (e.symm w) (e.symm (e y))
    simpa using hy
  · intro x _
    exact e.apply_symm_apply x
  · intro y _
    exact e.symm_apply_apply y

lemma maxDegree_comap_equiv
    {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : V ≃ W) [DecidableRel (G.comap e.symm).Adj] :
    (G.comap e.symm).maxDegree = G.maxDegree := by
  have himg :
      Finset.univ.image (fun w => (G.comap e.symm).degree w) =
        Finset.univ.image (fun v => G.degree v) := by
    ext d
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨e.symm w, (degree_comap_equiv G e w).symm⟩
    · rintro ⟨v, rfl⟩
      refine ⟨e v, ?_⟩
      rw [degree_comap_equiv G e (e v), e.symm_apply_apply]
  unfold SimpleGraph.maxDegree
  rw [himg]

lemma compl_degree_bound_of_bec
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (k : ℕ) (hn : 1 ≤ n)
    (hbec : (k + 1) * (G.maxDegree + 1) ≤ n + 1) (v : Fin n) :
    k * n ≤ (k + 1) * Gᶜ.degree v + 1 := by
  have hdeg_compl : Gᶜ.degree v = n - 1 - G.degree v := by
    simpa only [Fintype.card_fin] using SimpleGraph.degree_compl (G := G) (v := v)
  have hdeg_lt : G.degree v < n := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ x⟩
      intro hxv
      rw [hxv, SimpleGraph.mem_neighborFinset] at hx
      exact G.ne_of_adj hx rfl
    calc
      (G.neighborFinset v).card
          ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
      _ = n - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
      _ < n := by omega
  have hdeg_max : G.degree v ≤ G.maxDegree := G.degree_le_maxDegree v
  have hsum : Gᶜ.degree v + G.degree v + 1 = n := by omega
  have hmul : (k + 1) * (G.degree v + 1) ≤ n + 1 :=
    le_trans (Nat.mul_le_mul_left (k + 1) (Nat.add_le_add_right hdeg_max 1)) hbec
  have hlin : (k + 1) * Gᶜ.degree v + (k + 1) * (G.degree v + 1) = (k + 1) * n := by
    calc
      (k + 1) * Gᶜ.degree v + (k + 1) * (G.degree v + 1)
          = (k + 1) * (Gᶜ.degree v + G.degree v + 1) := by ring
      _ = (k + 1) * n := by rw [hsum]
  have hkn : (k + 1) * n = k * n + n := by ring
  omega

lemma packs_of_fin_compl_embedding
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    {n : ℕ} (e : V ≃ Fin n)
    (f : Fin n → Fin n) (hf_inj : Function.Injective f)
    (hf_adj : ∀ u v : Fin n, (G₁.comap e.symm).Adj u v → (G₂.comap e.symm)ᶜ.Adj (f u) (f v)) :
    BollobasEldridgeCatlinConjecture.Packs G₁ G₂ := by
  have hf_bij : Function.Bijective f := Finite.injective_iff_bijective.mp hf_inj
  let φ : Equiv.Perm (Fin n) := Equiv.ofBijective f hf_bij
  refine ⟨e.trans (φ.trans e.symm), ?_⟩
  intro u v huv
  have hF : (G₁.comap e.symm).Adj (e u) (e v) := by
    change G₁.Adj (e.symm (e u)) (e.symm (e v))
    simpa using huv
  have hH : (G₂.comap e.symm)ᶜ.Adj (f (e u)) (f (e v)) := hf_adj (e u) (e v) hF
  have hnot : ¬ (G₂.comap e.symm).Adj (f (e u)) (f (e v)) := by
    rw [SimpleGraph.compl_adj] at hH
    exact hH.2
  simpa [φ] using hnot

lemma packs_via_fin_complement
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (e : V ≃ Fin (Fintype.card V))
    [DecidableRel (G₁.comap e.symm).Adj]
    [DecidableRel (G₂.comap e.symm).Adj]
    [DecidableRel (G₂.comap e.symm)ᶜ.Adj]
    (h1 : H1)
    {n₀ : ℕ}
    (hn₀ : ∀ (n : ℕ), n₀ ≤ n →
      ∀ (F H : SimpleGraph (Fin n)) [DecidableRel F.Adj] [DecidableRel H.Adj],
        F.maxDegree = 3 → (∀ v : Fin n, 3 * n ≤ 4 * H.degree v + 1) →
        ∃ f : Fin n → Fin n, Function.Injective f ∧ ∀ u v : Fin n, F.Adj u v → H.Adj (f u) (f v))
    (hn1 : 1 ≤ Fintype.card V) (hn2 : n₀ ≤ Fintype.card V)
    (h23 : G₁.maxDegree = 2 ∨ G₁.maxDegree = 3)
    (hbec : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    BollobasEldridgeCatlinConjecture.Packs G₁ G₂ := by
  have hFmax : (G₁.comap e.symm).maxDegree = G₁.maxDegree := maxDegree_comap_equiv G₁ e
  have hG₂max : (G₂.comap e.symm).maxDegree = G₂.maxDegree := maxDegree_comap_equiv G₂ e
  rcases h23 with hΔ2 | hΔ3
  · have hF2 : (G₁.comap e.symm).maxDegree = 2 := hFmax.trans hΔ2
    have hbec2 : (2 + 1) * ((G₂.comap e.symm).maxDegree + 1) ≤ Fintype.card V + 1 := by
      rw [hG₂max, ← hΔ2]
      exact hbec
    have hdeg2 : ∀ v : Fin (Fintype.card V), 2 * Fintype.card V ≤ 3 * (G₂.comap e.symm)ᶜ.degree v + 1 :=
      fun v => compl_degree_bound_of_bec (G₂.comap e.symm) 2 hn1 hbec2 v
    obtain ⟨f, hf_inj, hf_adj⟩ :=
      h1 (Fintype.card V) hn1 (G₁.comap e.symm) (G₂.comap e.symm)ᶜ hF2 hdeg2
    exact packs_of_fin_compl_embedding G₁ G₂ e f hf_inj hf_adj
  · have hF3 : (G₁.comap e.symm).maxDegree = 3 := hFmax.trans hΔ3
    have hbec3 : (3 + 1) * ((G₂.comap e.symm).maxDegree + 1) ≤ Fintype.card V + 1 := by
      rw [hG₂max, ← hΔ3]
      exact hbec
    have hdeg3 : ∀ v : Fin (Fintype.card V), 3 * Fintype.card V ≤ 4 * (G₂.comap e.symm)ᶜ.degree v + 1 :=
      fun v => compl_degree_bound_of_bec (G₂.comap e.symm) 3 hn1 hbec3 v
    obtain ⟨f, hf_inj, hf_adj⟩ :=
      hn₀ (Fintype.card V) hn2 (G₁.comap e.symm) (G₂.comap e.symm)ᶜ hF3 hdeg3
    exact packs_of_fin_compl_embedding G₁ G₂ e f hf_inj hf_adj

theorem main :
    H1 → H2 →
      type_of% @BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_three_large_n := by
  intro h1 h2
  rcases h2 with ⟨n₀, hn₀⟩
  refine ⟨max 1 n₀, ?_⟩
  intro V _ _ G₁ G₂ _ _ hcard hΔ₁ hbec
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_max_left 1 n₀) hcard
  have hn2 : n₀ ≤ Fintype.card V := le_trans (le_max_right 1 n₀) hcard
  by_cases h01 : G₁.maxDegree ≤ 1
  · refine sauer_spencer_from_scratch G₁ G₂ ?_
    have h01' : G₁.maxDegree = 0 ∨ G₁.maxDegree = 1 := by omega
    rcases h01' with h0 | h1'
    · rw [h0]
      omega
    · rw [h1'] at hbec ⊢
      omega
  · have h23 : G₁.maxDegree = 2 ∨ G₁.maxDegree = 3 := by omega
    let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    let instF : DecidableRel (G₁.comap e.symm).Adj :=
      fun i j => ‹DecidableRel G₁.Adj› (e.symm i) (e.symm j)
    let instG₂' : DecidableRel (G₂.comap e.symm).Adj :=
      fun i j => ‹DecidableRel G₂.Adj› (e.symm i) (e.symm j)
    let instH : DecidableRel (G₂.comap e.symm)ᶜ.Adj :=
      fun i j =>
        decidable_of_iff (i ≠ j ∧ ¬ G₂.Adj (e.symm i) (e.symm j))
          (by rw [SimpleGraph.compl_adj]; rfl)
    exact @packs_via_fin_complement V _ _ G₁ G₂ _ _ e instF instG₂' instH h1 n₀ hn₀ hn1 hn2 h23 hbec

end OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_three_large_n_R1
