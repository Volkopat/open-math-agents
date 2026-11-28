import OMAReductions.R_Erdos81_erdos_81_R1
import Mathlib

/-!
# Proof of Step H3: Core-Edge Triangle Saturation via Galvin's Theorem

We prove `OMA.R_Erdos81_erdos_81_R1.H3` (Okechukwu 2026, Lemma 4.1): given disjoint vertex sets
`C, R` with `|C| ≥ 3`, if every vertex in `C` misses at most `τ` vertices of `R` and
`|R| ≥ 3 * ⌈|C|/2⌉ - 3 + 4 * τ`, then every edge of `G[C]` can be assigned a common neighbor in `R`
so that incident edges of `G[C]` receive distinct vertices of `R`.

The proof proceeds in three self-contained parts:
1. Gale--Shapley deferred acceptance (`exists_stable_matching`): every bipartite subgraph with
   strict linear preferences admits a stable matching (kernel of the Galvin orientation).
2. Galvin's list edge-coloring theorem for `K_{a,a}` (`galvin_list_coloring`, *J. Combin. Theory
   Ser. B* 63 (1995), 153--158): every `a`-list assignment on `Fin a × Fin a` admits a proper list
   edge-coloring.
3. Splitting `C = C₁ ⊔ C₂` into balanced halves (`|C₁| = a = ⌈|C|/2⌉`, `|C₂| ≤ a`) and `R` into
   disjoint palettes `R₁` (`|R₁| = a + 2τ`) and `R₂` (`|R₂| = 2a - 3 + 2τ`), we color crossing
   pairs via Galvin's theorem using `R₁` and internal pairs of `C₁` and `C₂` greedily using `R₂`.
-/

-- Credit: @preternatural-tocsin

namespace Galvin95

open SimpleGraph Finset

lemma exists_stable_matching {a : ℕ} (S : Finset (Fin a × Fin a))
    (rRow : Fin a → Fin a → ℕ) (rCol : Fin a → Fin a → ℕ)
    (hRow_inj : ∀ i j₁ j₂, j₁ ≠ j₂ → rRow i j₁ ≠ rRow i j₂)
    (hCol_inj : ∀ j i₁ i₂, i₁ ≠ i₂ → rCol j i₁ ≠ rCol j i₂) :
    ∃ K ⊆ S,
      (∀ i j₁ j₂, (i, j₁) ∈ K → (i, j₂) ∈ K → j₁ = j₂) ∧
      (∀ i₁ i₂ j, (i₁, j) ∈ K → (i₂, j) ∈ K → i₁ = i₂) ∧
      (∀ e ∈ S \ K,
        (∃ j', (e.1, j') ∈ K ∧ rRow e.1 e.2 < rRow e.1 j') ∨
        (∃ i', (i', e.2) ∈ K ∧ rCol e.2 e.1 < rCol e.2 i')) := by
  let topProp : Finset (Fin a × Fin a) → Finset (Fin a × Fin a) := fun A ↦
    A.filter (fun e ↦ ∀ j', (e.1, j') ∈ A → rRow e.1 j' ≤ rRow e.1 e.2)
  have htop_sub : ∀ A, topProp A ⊆ A := fun A ↦ filter_subset _ _
  have htop_row_uniq : ∀ A i j₁ j₂, (i, j₁) ∈ topProp A → (i, j₂) ∈ topProp A → j₁ = j₂ := by
    intro A i j₁ j₂ h1 h2
    rw [mem_filter] at h1 h2
    have hle1 : rRow i j₂ ≤ rRow i j₁ := h1.2 j₂ h2.1
    have hle2 : rRow i j₁ ≤ rRow i j₂ := h2.2 j₁ h1.1
    by_contra hne
    exact hRow_inj i j₁ j₂ hne (le_antisymm hle2 hle1)
  have htop_exists : ∀ A i j, (i, j) ∈ A →
      ∃ j', (i, j') ∈ topProp A ∧ rRow i j ≤ rRow i j' := by
    intro A i j hij
    let rowA := (Finset.univ : Finset (Fin a)).filter (fun j' ↦ (i, j') ∈ A)
    have hne : rowA.Nonempty := ⟨j, mem_filter.mpr ⟨mem_univ j, hij⟩⟩
    obtain ⟨j', hj'mem, hj'max⟩ := Finset.exists_max_image rowA (fun j' ↦ rRow i j') hne
    rw [mem_filter] at hj'mem
    refine ⟨j', mem_filter.mpr ⟨hj'mem.2, fun j'' hj'' ↦ hj'max j'' (mem_filter.mpr ⟨mem_univ _, hj''⟩)⟩,
      hj'max j (mem_filter.mpr ⟨mem_univ _, hij⟩)⟩
  have hiter : ∀ t : ℕ, ∀ A ⊆ S, A.card = t →
      (∀ e ∈ S \ A, ∃ i', (i', e.2) ∈ topProp A ∧ rCol e.2 e.1 < rCol e.2 i') →
      ∃ K ⊆ S,
        (∀ i j₁ j₂, (i, j₁) ∈ K → (i, j₂) ∈ K → j₁ = j₂) ∧
        (∀ i₁ i₂ j, (i₁, j) ∈ K → (i₂, j) ∈ K → i₁ = i₂) ∧
        (∀ e ∈ S \ K,
          (∃ j', (e.1, j') ∈ K ∧ rRow e.1 e.2 < rRow e.1 j') ∨
          (∃ i', (i', e.2) ∈ K ∧ rCol e.2 e.1 < rCol e.2 i')) := by
    intro t
    induction t with
    | zero =>
      intro A hAS hA0 hInv
      have hAe : A = ∅ := card_eq_zero.mp hA0
      subst hAe
      refine ⟨∅, empty_subset S, by simp, by simp, ?_⟩
      intro e he
      rw [sdiff_empty] at he
      have h1 := hInv e (by simpa using he)
      rcases h1 with ⟨i', hi', _⟩
      simp [topProp] at hi'
    | succ t ih =>
      intro A hAS hAc hInv
      by_cases hcol : ∀ i₁ i₂ j, (i₁, j) ∈ topProp A → (i₂, j) ∈ topProp A → i₁ = i₂
      · refine ⟨topProp A, (htop_sub A).trans hAS, htop_row_uniq A, hcol, ?_⟩
        intro e he
        rw [mem_sdiff] at he
        by_cases heA : e ∈ A
        · left
          obtain ⟨j', hj'top, hle⟩ := htop_exists A e.1 e.2 heA
          have hne : e.2 ≠ j' := fun h ↦ he.2 (by rwa [← h] at hj'top)
          have hlt : rRow e.1 e.2 < rRow e.1 j' :=
            lt_of_le_of_ne hle (hRow_inj e.1 e.2 j' hne)
          exact ⟨j', hj'top, hlt⟩
        · right
          exact hInv e (mem_sdiff.mpr ⟨he.1, heA⟩)
      · push Not at hcol
        rcases hcol with ⟨i₁, i₂, j₀, h1, h2, hne⟩
        -- Choose the loser `(ilo, j₀)` and winner `(iwin, j₀)` with `rCol j₀ ilo < rCol j₀ iwin`.
        have hlt_or : rCol j₀ i₁ < rCol j₀ i₂ ∨ rCol j₀ i₂ < rCol j₀ i₁ := by
          have := hCol_inj j₀ i₁ i₂ hne
          omega
        have hstep : ∀ ilo iwin : Fin a,
            (ilo, j₀) ∈ topProp A → (iwin, j₀) ∈ topProp A →
            rCol j₀ ilo < rCol j₀ iwin →
            ∃ K ⊆ S,
              (∀ i j₁ j₂, (i, j₁) ∈ K → (i, j₂) ∈ K → j₁ = j₂) ∧
              (∀ i₁ i₂ j, (i₁, j) ∈ K → (i₂, j) ∈ K → i₁ = i₂) ∧
              (∀ e ∈ S \ K,
                (∃ j', (e.1, j') ∈ K ∧ rRow e.1 e.2 < rRow e.1 j') ∨
                (∃ i', (i', e.2) ∈ K ∧ rCol e.2 e.1 < rCol e.2 i')) := by
          intro ilo iwin hlo hwin hlt
          have hne_lw : ilo ≠ iwin := fun h ↦ by subst h; omega
          let A' := A.erase (ilo, j₀)
          have hA'sub : A' ⊆ S := (erase_subset _ _).trans hAS
          have hA'card : A'.card = t := by
            rw [card_erase_of_mem (htop_sub A hlo), hAc]; omega
          have hkeep : ∀ e ∈ topProp A, e ≠ (ilo, j₀) → e ∈ topProp A' := by
            intro e he hne_e
            rw [mem_filter] at he ⊢
            exact ⟨mem_erase.mpr ⟨hne_e, he.1⟩, fun j' hj' ↦ he.2 j' (erase_subset _ _ hj')⟩
          have hwin' : (iwin, j₀) ∈ topProp A' :=
            hkeep (iwin, j₀) hwin (fun h ↦ hne_lw (Prod.mk.inj h).1.symm)
          refine ih A' hA'sub hA'card ?_
          intro e he
          rw [mem_sdiff] at he
          by_cases he_eq : e = (ilo, j₀)
          · rw [he_eq]
            exact ⟨iwin, hwin', hlt⟩
          · have heNotA : e ∉ A := fun h ↦ he.2 (mem_erase.mpr ⟨he_eq, h⟩)
            obtain ⟨i', hi'top, hi'lt⟩ := hInv e (mem_sdiff.mpr ⟨he.1, heNotA⟩)
            by_cases hi'_eq : (i', e.2) = (ilo, j₀)
            · have hi'lo : i' = ilo := (Prod.mk.inj hi'_eq).1
              have hej0 : e.2 = j₀ := (Prod.mk.inj hi'_eq).2
              rw [hej0]
              exact ⟨iwin, hwin', lt_trans (by rwa [hej0, hi'lo] at hi'lt) hlt⟩
            · exact ⟨i', hkeep (i', e.2) hi'top hi'_eq, hi'lt⟩
        rcases hlt_or with h | h
        · exact hstep i₁ i₂ h1 h2 h
        · exact hstep i₂ i₁ h2 h1 h
  exact hiter S.card S Subset.rfl rfl (by simp)

lemma galvin_list_coloring {α : Type*} [DecidableEq α] {a : ℕ} (ha : 1 ≤ a)
    (L : Fin a × Fin a → Finset α) (hL : ∀ e : Fin a × Fin a, a ≤ (L e).card) :
    ∃ f : Fin a × Fin a → α,
      (∀ e : Fin a × Fin a, f e ∈ L e) ∧
      (∀ i j₁ j₂ : Fin a, j₁ ≠ j₂ → f (i, j₁) ≠ f (i, j₂)) ∧
      (∀ i₁ i₂ j : Fin a, i₁ ≠ i₂ → f (i₁, j) ≠ f (i₂, j)) := by
  let rRow : Fin a → Fin a → ℕ := fun i j ↦ (i.val + j.val) % a
  let rCol : Fin a → Fin a → ℕ := fun j i ↦ a - 1 - (i.val + j.val) % a
  have hRow_inj : ∀ i j₁ j₂ : Fin a, j₁ ≠ j₂ → rRow i j₁ ≠ rRow i j₂ := by
    intro i j₁ j₂ hne hEq
    dsimp [rRow] at hEq
    have h1 := j₁.isLt
    have h2 := j₂.isLt
    have h3 : (i.val + j₁.val) % a = (i.val + j₂.val) % a := hEq
    have hne_v : j₁.val ≠ j₂.val := fun h ↦ hne (Fin.ext h)
    have hlt : i.val + j₁.val < 2 * a := by omega
    have hlt2 : i.val + j₂.val < 2 * a := by omega
    have hmod : ∀ x : ℕ, x < 2 * a → x % a = if x < a then x else x - a := by
      intro x hx
      split_ifs with hxa
      · exact Nat.mod_eq_of_lt hxa
      · have hsum : x = a + (x - a) := by omega
        conv_lhs => rw [hsum]
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod _ hlt, hmod _ hlt2] at h3
    split_ifs at h3 <;> omega
  have hCol_inj : ∀ j i₁ i₂ : Fin a, i₁ ≠ i₂ → rCol j i₁ ≠ rCol j i₂ := by
    intro j i₁ i₂ hne hEq
    dsimp [rCol] at hEq
    have hm1 : (i₁.val + j.val) % a < a := Nat.mod_lt _ (by omega)
    have hm2 : (i₂.val + j.val) % a < a := Nat.mod_lt _ (by omega)
    have heq_mod : (j.val + i₁.val) % a = (j.val + i₂.val) % a := by
      rw [add_comm j.val i₁.val, add_comm j.val i₂.val]; omega
    exact hRow_inj j i₁ i₂ hne heq_mod
  let outN : Finset (Fin a × Fin a) → (Fin a × Fin a) → Finset (Fin a × Fin a) := fun S e ↦
    S.filter (fun e' ↦
      (e'.1 = e.1 ∧ rRow e.1 e.2 < rRow e.1 e'.2) ∨
      (e'.2 = e.2 ∧ rCol e.2 e.1 < rCol e.2 e'.1))
  have hout_univ : ∀ e : Fin a × Fin a, (outN Finset.univ e).card < a := by
    intro ⟨i, j⟩
    let c := rRow i j
    have hc_lt : c < a := Nat.mod_lt _ (by omega)
    have hsub : outN Finset.univ (i, j) ⊆
        ((Finset.univ : Finset (Fin a)).filter (fun j' ↦ c < rRow i j')).image (fun j' ↦ (i, j')) ∪
        ((Finset.univ : Finset (Fin a)).filter (fun i' ↦ rRow i' j < c)).image (fun i' ↦ (i', j)) := by
      intro ⟨i', j'⟩ hmem
      rw [mem_filter] at hmem
      rcases hmem.2 with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩
      · exact mem_union_left _ (mem_image.mpr ⟨j', mem_filter.mpr ⟨mem_univ _, hlt⟩, rfl⟩)
      · have hlt' : rRow i' j' < c := by
          dsimp [rCol, c, rRow] at hlt ⊢
          have hm1 : (i.val + j'.val) % a < a := Nat.mod_lt _ (by omega)
          have hm2 : (i'.val + j'.val) % a < a := Nat.mod_lt _ (by omega)
          omega
        exact mem_union_right _ (mem_image.mpr ⟨i', mem_filter.mpr ⟨mem_univ _, hlt'⟩, rfl⟩)
    have hrow_card : ((Finset.univ : Finset (Fin a)).filter (fun j' ↦ c < rRow i j')).card ≤ a - 1 - c := by
      have hinj : (((Finset.univ : Finset (Fin a)).filter (fun j' ↦ c < rRow i j')).image (rRow i)).card =
          ((Finset.univ : Finset (Fin a)).filter (fun j' ↦ c < rRow i j')).card :=
        card_image_of_injOn (fun j₁ _ j₂ _ hEq ↦ by by_contra hne; exact hRow_inj i j₁ j₂ hne hEq)
      rw [← hinj]
      have hsub_ico : ((Finset.univ : Finset (Fin a)).filter (fun j' ↦ c < rRow i j')).image (rRow i) ⊆
          Finset.Ico (c + 1) a := by
        intro x hx
        rcases mem_image.mp hx with ⟨j', hj', rfl⟩
        rw [mem_filter] at hj'
        rw [Finset.mem_Ico]
        exact ⟨by omega, Nat.mod_lt _ (by omega)⟩
      exact le_trans (card_le_card hsub_ico) (by rw [Nat.card_Ico]; omega)
    have hcol_card : ((Finset.univ : Finset (Fin a)).filter (fun i' ↦ rRow i' j < c)).card ≤ c := by
      have hinj : (((Finset.univ : Finset (Fin a)).filter (fun i' ↦ rRow i' j < c)).image (fun i' ↦ rRow i' j)).card =
          ((Finset.univ : Finset (Fin a)).filter (fun i' ↦ rRow i' j < c)).card :=
        card_image_of_injOn (fun i₁ _ i₂ _ hEq ↦ by
          by_contra hne
          have : rRow j i₁ = rRow j i₂ := by dsimp [rRow] at hEq ⊢; rw [add_comm j.val i₁.val, add_comm j.val i₂.val]; exact hEq
          exact hRow_inj j i₁ i₂ hne this)
      rw [← hinj]
      have hsub_rg : ((Finset.univ : Finset (Fin a)).filter (fun i' ↦ rRow i' j < c)).image (fun i' ↦ rRow i' j) ⊆
          Finset.range c := by
        intro x hx
        rcases mem_image.mp hx with ⟨i', hi', rfl⟩
        exact mem_range.mpr (mem_filter.mp hi').2
      exact le_trans (card_le_card hsub_rg) (by rw [card_range])
    have h1 := card_le_card hsub
    have h2 := card_union_le
      (((Finset.univ : Finset (Fin a)).filter (fun j' ↦ c < rRow i j')).image (fun j' ↦ (i, j')))
      (((Finset.univ : Finset (Fin a)).filter (fun i' ↦ rRow i' j < c)).image (fun i' ↦ (i', j)))
    have h3 : (((Finset.univ : Finset (Fin a)).filter (fun j' ↦ c < rRow i j')).image (fun j' ↦ (i, j'))).card ≤ a - 1 - c :=
      le_trans card_image_le hrow_card
    have h4 : (((Finset.univ : Finset (Fin a)).filter (fun i' ↦ rRow i' j < c)).image (fun i' ↦ (i', j))).card ≤ c :=
      le_trans card_image_le hcol_card
    omega
  -- Bondy--Boppana--Siegel / Galvin kernel-coloring induction on `|S|`:
  have hmain : ∀ m : ℕ, ∀ S : Finset (Fin a × Fin a), S.card = m →
      ∀ Ls : Fin a × Fin a → Finset α,
        (∀ e ∈ S, (outN S e).card < (Ls e).card) →
        ∃ f : Fin a × Fin a → α,
          (∀ e ∈ S, f e ∈ Ls e) ∧
          (∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ → f e₁ = f e₂ → e₁.1 ≠ e₂.1 ∧ e₁.2 ≠ e₂.2) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro S hSm Ls hLs
      by_cases hSe : S = ∅
      · subst hSe
        have hex_col : Nonempty α := by
          have hpos : 0 < (L (⟨0, ha⟩, ⟨0, ha⟩)).card := by
            have := hL (⟨0, ha⟩, ⟨0, ha⟩); omega
          obtain ⟨γ, _⟩ := card_pos.mp hpos
          exact ⟨γ⟩
        exact ⟨fun _ ↦ hex_col.some, by simp, by simp⟩
      · obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
        have hpos₀ : 0 < (Ls e₀).card := by have := hLs e₀ he₀; omega
        obtain ⟨γ, hγ⟩ := card_pos.mp hpos₀
        let Sγ := S.filter (fun e ↦ γ ∈ Ls e)
        have he₀Sγ : e₀ ∈ Sγ := mem_filter.mpr ⟨he₀, hγ⟩
        obtain ⟨K, hKSγ, hKrow, hKcol, hKker⟩ := exists_stable_matching Sγ rRow rCol hRow_inj hCol_inj
        have hKS : K ⊆ S := hKSγ.trans (filter_subset _ _)
        have hKne : K.Nonempty := by
          by_contra hKe
          rw [not_nonempty_iff_eq_empty] at hKe
          have hker0 := hKker e₀ (by rw [hKe, sdiff_empty]; exact he₀Sγ)
          rcases hker0 with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> simp [hKe] at h
        let S' := S \ K
        have hS'lt : S'.card < m := by
          rw [card_sdiff_of_subset hKS, hSm]
          have h1 : 0 < K.card := card_pos.mpr hKne
          have h2 : K.card ≤ S.card := card_le_card hKS
          omega
        let Ls' : Fin a × Fin a → Finset α := fun e ↦ (Ls e).erase γ
        have hLs' : ∀ e ∈ S', (outN S' e).card < (Ls' e).card := by
          intro e heS'
          have heS : e ∈ S := (mem_sdiff.mp heS').1
          have henotK : e ∉ K := (mem_sdiff.mp heS').2
          by_cases hγe : γ ∈ Ls e
          · have heSγ : e ∈ Sγ \ K := mem_sdiff.mpr ⟨mem_filter.mpr ⟨heS, hγe⟩, henotK⟩
            have hex_out : ∃ e' ∈ K, e' ∈ outN S e := by
              rcases hKker e heSγ with ⟨j', hj'K, hlt⟩ | ⟨i', hi'K, hlt⟩
              · exact ⟨(e.1, j'), hj'K, mem_filter.mpr ⟨hKS hj'K, Or.inl ⟨rfl, hlt⟩⟩⟩
              · exact ⟨(i', e.2), hi'K, mem_filter.mpr ⟨hKS hi'K, Or.inr ⟨rfl, hlt⟩⟩⟩
            obtain ⟨e', he'K, he'out⟩ := hex_out
            have hsub : outN S' e ⊆ (outN S e).erase e' := by
              intro z hz
              rw [mem_filter] at hz
              refine mem_erase.mpr ⟨fun hze' ↦ (mem_sdiff.mp hz.1).2 (hze' ▸ he'K),
                mem_filter.mpr ⟨(mem_sdiff.mp hz.1).1, hz.2⟩⟩
            have hle := card_le_card hsub
            rw [card_erase_of_mem he'out] at hle
            have hcard_L : (Ls' e).card = (Ls e).card - 1 := card_erase_of_mem hγe
            have hlt0 := hLs e heS
            have hout_pos : 1 ≤ (outN S e).card := card_pos.mpr ⟨e', he'out⟩
            omega
          · have hsub : outN S' e ⊆ outN S e := filter_subset_filter _ sdiff_subset
            have hle := card_le_card hsub
            have hcard_L : Ls' e = Ls e := erase_eq_of_notMem hγe
            rw [hcard_L]
            have := hLs e heS
            omega
        obtain ⟨f', hf'L, hf'prop⟩ := ih S'.card hS'lt S' rfl Ls' hLs'
        let f : Fin a × Fin a → α := fun e ↦ if e ∈ K then γ else f' e
        refine ⟨f, ?_, ?_⟩
        · intro e heS
          dsimp [f]
          split_ifs with heK
          · exact (mem_filter.mp (hKSγ heK)).2
          · exact erase_subset _ _ (hf'L e (mem_sdiff.mpr ⟨heS, heK⟩))
        · intro e₁ he₁ e₂ he₂ hne hfeq
          dsimp [f] at hfeq
          by_cases h1K : e₁ ∈ K <;> by_cases h2K : e₂ ∈ K
          · constructor
            · intro hrow
              have : e₁.2 = e₂.2 := hKrow e₁.1 e₁.2 e₂.2 h1K (hrow ▸ h2K)
              exact hne (Prod.ext hrow this)
            · intro hcol
              have : e₁.1 = e₂.1 := hKcol e₁.1 e₂.1 e₁.2 h1K (hcol ▸ h2K)
              exact hne (Prod.ext this hcol)
          · simp only [h1K, h2K, ↓reduceIte] at hfeq
            have hmem := hf'L e₂ (mem_sdiff.mpr ⟨he₂, h2K⟩)
            rw [← hfeq] at hmem
            exact absurd hmem (notMem_erase γ (Ls e₂))
          · simp only [h1K, h2K, ↓reduceIte] at hfeq
            have hmem := hf'L e₁ (mem_sdiff.mpr ⟨he₁, h1K⟩)
            rw [hfeq] at hmem
            exact absurd hmem (notMem_erase γ (Ls e₁))
          · simp only [h1K, h2K, ↓reduceIte] at hfeq
            exact hf'prop e₁ (mem_sdiff.mpr ⟨he₁, h1K⟩) e₂ (mem_sdiff.mpr ⟨he₂, h2K⟩) hne hfeq
  obtain ⟨f, hfL, hfprop⟩ := hmain (Finset.univ : Finset (Fin a × Fin a)).card Finset.univ rfl L
    (fun e _ ↦ lt_of_lt_of_le (hout_univ e) (hL e))
  refine ⟨f, fun e ↦ hfL e (mem_univ e), ?_, ?_⟩
  · intro i j₁ j₂ hne hfeq
    exact (hfprop (i, j₁) (mem_univ _) (i, j₂) (mem_univ _)
      (fun h ↦ hne (Prod.mk.inj h).2) hfeq).1 rfl
  · intro i₁ i₂ j hne hfeq
    exact (hfprop (i₁, j) (mem_univ _) (i₂, j) (mem_univ _)
      (fun h ↦ hne (Prod.mk.inj h).1) hfeq).2 rfl

lemma greedy_clique_list_coloring {n a : ℕ} (ha : 2 ≤ a) (A : Finset (Fin n)) (hAa : A.card ≤ a)
    (L : Sym2 (Fin n) → Finset (Fin n))
    (hL : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → 2 * a - 3 ≤ (L s(u, v)).card) :
    ∃ ψ : Sym2 (Fin n) → Fin n,
      (∀ u ∈ A, ∀ v ∈ A, u ≠ v → ψ s(u, v) ∈ L s(u, v)) ∧
      (∀ u ∈ A, ∀ v ∈ A, ∀ w ∈ A, u ≠ v → u ≠ w → v ≠ w → ψ s(u, v) ≠ ψ s(u, w)) := by
  let E0 : Finset (Sym2 (Fin n)) := A.offDiag.image (fun p ↦ s(p.1, p.2))
  have hE0_mem : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → s(u, v) ∈ E0 := fun u hu v hv huv ↦
    mem_image.mpr ⟨(u, v), mem_offDiag.mpr ⟨hu, hv, huv⟩, rfl⟩
  have hE0_spec : ∀ e ∈ E0, ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ e = s(u, v) := by
    intro e he
    rcases mem_image.mp he with ⟨⟨u, v⟩, huv, rfl⟩
    rw [mem_offDiag] at huv
    exact ⟨u, huv.1, v, huv.2.1, huv.2.2, rfl⟩
  have hE0_inc : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      ((E0.erase s(u, v)).filter (fun e ↦ u ∈ e ∨ v ∈ e)).card ≤ 2 * a - 4 := by
    intro u hu v hv huv
    have hsub : (E0.erase s(u, v)).filter (fun e ↦ u ∈ e ∨ v ∈ e) ⊆
        ((A.erase u).erase v).image (fun w ↦ s(u, w)) ∪
        ((A.erase u).erase v).image (fun w ↦ s(v, w)) := by
      intro e he
      rw [mem_filter, mem_erase] at he
      obtain ⟨x, hxA, y, hyA, hxy, rfl⟩ := hE0_spec e he.1.2
      rcases he.2 with hu' | hv'
      · rcases Sym2.mem_iff.mp hu' with rfl | rfl
        · have hyne : y ≠ v := fun h ↦ he.1.1 (by rw [h])
          exact mem_union_left _ (mem_image.mpr ⟨y, mem_erase.mpr ⟨hyne, mem_erase.mpr ⟨hxy.symm, hyA⟩⟩, rfl⟩)
        · have hxne : x ≠ v := fun h ↦ he.1.1 (by rw [h, Sym2.eq_swap])
          exact mem_union_left _ (mem_image.mpr ⟨x, mem_erase.mpr ⟨hxne, mem_erase.mpr ⟨hxy, hxA⟩⟩, Sym2.eq_swap⟩)
      · rcases Sym2.mem_iff.mp hv' with rfl | rfl
        · have hyne : y ≠ u := fun h ↦ he.1.1 (by rw [h, Sym2.eq_swap])
          exact mem_union_right _ (mem_image.mpr ⟨y, mem_erase.mpr ⟨hxy.symm, mem_erase.mpr ⟨hyne, hyA⟩⟩, rfl⟩)
        · have hxne : x ≠ u := fun h ↦ he.1.1 (by rw [h])
          exact mem_union_right _ (mem_image.mpr ⟨x, mem_erase.mpr ⟨hxy, mem_erase.mpr ⟨hxne, hxA⟩⟩, Sym2.eq_swap⟩)
    have hcard_er : ((A.erase u).erase v).card = A.card - 2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨huv.symm, hv⟩), card_erase_of_mem hu]
      omega
    have hle1 := card_le_card hsub
    have hle2 := card_union_le (((A.erase u).erase v).image (fun w ↦ s(u, w)))
      (((A.erase u).erase v).image (fun w ↦ s(v, w)))
    have hle3 : (((A.erase u).erase v).image (fun w ↦ s(u, w))).card ≤ A.card - 2 :=
      le_trans card_image_le (by omega)
    have hle4 : (((A.erase u).erase v).image (fun w ↦ s(v, w))).card ≤ A.card - 2 :=
      le_trans card_image_le (by omega)
    omega
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨Sym2.lift ⟨fun u _ ↦ Fin.elim0 u, fun u _ ↦ Fin.elim0 u⟩,
      fun u _ ↦ Fin.elim0 u, fun u _ ↦ Fin.elim0 u⟩
  have hn_pos : 0 < n := by omega
  have hind : ∀ m : ℕ, ∀ E ⊆ E0, E.card = m →
      ∃ ψ : Sym2 (Fin n) → Fin n,
        (∀ e ∈ E, ψ e ∈ L e) ∧
        (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → (∃ x, x ∈ e₁ ∧ x ∈ e₂) → ψ e₁ ≠ ψ e₂) := by
    intro m
    induction m with
    | zero =>
      intro E _ hE0'
      have hEe : E = ∅ := card_eq_zero.mp hE0'
      subst hEe
      exact ⟨fun _ ↦ ⟨0, hn_pos⟩, by simp, by simp⟩
    | succ m ih =>
      intro E hEE0 hEm
      obtain ⟨e, heE⟩ := card_pos.mp (by omega : 0 < E.card)
      obtain ⟨u, huA, v, hvA, huv, rfl⟩ := hE0_spec e (hEE0 heE)
      let E' := E.erase s(u, v)
      have hE'sub : E' ⊆ E0 := (erase_subset _ _).trans hEE0
      have hE'card : E'.card = m := by rw [card_erase_of_mem heE, hEm]; omega
      obtain ⟨ψ₀, hψ₀L, hψ₀prop⟩ := ih E' hE'sub hE'card
      let inc := E'.filter (fun e' ↦ u ∈ e' ∨ v ∈ e')
      have hinc_sub : inc ⊆ (E0.erase s(u, v)).filter (fun e' ↦ u ∈ e' ∨ v ∈ e') :=
        filter_subset_filter _ (erase_subset_erase _ hEE0)
      have hforb_card : (inc.image ψ₀).card ≤ 2 * a - 4 :=
        le_trans card_image_le (le_trans (card_le_card hinc_sub) (hE0_inc u huA v hvA huv))
      have hL_card := hL u huA v hvA huv
      have hex_c : ∃ c ∈ L s(u, v), c ∉ inc.image ψ₀ := by
        by_contra hall
        push Not at hall
        have hle := card_le_card (show L s(u, v) ⊆ inc.image ψ₀ from hall)
        omega
      obtain ⟨c, hcL, hcnot⟩ := hex_c
      let ψ : Sym2 (Fin n) → Fin n := fun e' ↦ if e' = s(u, v) then c else ψ₀ e'
      refine ⟨ψ, ?_, ?_⟩
      · intro e' he'
        dsimp [ψ]
        split_ifs with heq
        · rwa [heq]
        · exact hψ₀L e' (mem_erase.mpr ⟨heq, he'⟩)
      · intro e₁ he₁ e₂ he₂ hne ⟨x, hx₁, hx₂⟩
        by_cases h1 : e₁ = s(u, v)
        · subst h1
          have h2ne : e₂ ≠ s(u, v) := hne.symm
          have h2E' : e₂ ∈ E' := mem_erase.mpr ⟨h2ne, he₂⟩
          have h2inc : e₂ ∈ inc := by
            rw [mem_filter]
            refine ⟨h2E', ?_⟩
            rcases Sym2.mem_iff.mp hx₁ with rfl | rfl
            · exact Or.inl hx₂
            · exact Or.inr hx₂
          dsimp [ψ]
          simp only [↓reduceIte, h2ne]
          intro hceq
          exact hcnot (mem_image.mpr ⟨e₂, h2inc, hceq.symm⟩)
        · by_cases h2 : e₂ = s(u, v)
          · subst h2
            have h1E' : e₁ ∈ E' := mem_erase.mpr ⟨h1, he₁⟩
            have h1inc : e₁ ∈ inc := by
              rw [mem_filter]
              refine ⟨h1E', ?_⟩
              rcases Sym2.mem_iff.mp hx₂ with rfl | rfl
              · exact Or.inl hx₁
              · exact Or.inr hx₁
            dsimp [ψ]
            simp only [h1, ↓reduceIte]
            intro hceq
            exact hcnot (mem_image.mpr ⟨e₁, h1inc, hceq⟩)
          · dsimp [ψ]
            simp only [h1, h2, ↓reduceIte]
            exact hψ₀prop e₁ (mem_erase.mpr ⟨h1, he₁⟩) e₂ (mem_erase.mpr ⟨h2, he₂⟩) hne ⟨x, hx₁, hx₂⟩
  obtain ⟨ψ, hψL, hψprop⟩ := hind E0.card E0 Subset.rfl rfl
  refine ⟨ψ, fun u hu v hv huv ↦ hψL s(u, v) (hE0_mem u hu v hv huv), ?_⟩
  intro u hu v hv w hw huv huw hvw
  have hne : s(u, v) ≠ s(u, w) := fun h ↦ by
    rcases Sym2.eq_iff.mp h with ⟨_, h1⟩ | ⟨h1, _⟩
    · exact hvw h1
    · exact huw h1
  exact hψprop s(u, v) (hE0_mem u hu v hv huv) s(u, w) (hE0_mem u hu w hw huw) hne ⟨u, by simp, by simp⟩

end Galvin95

theorem OMA.solution : OMA.R_Erdos81_erdos_81_R1.H3 := by
  intro n G _ C R τ hdisj hC3 hτ hRcard
  open Finset in
  let a : ℕ := (C.card + 1) / 2
  have ha2 : 2 ≤ a := by dsimp [a]; omega
  have ha_le_C : a ≤ C.card := by dsimp [a]; omega
  obtain ⟨C₁, hC₁sub, hC₁card⟩ := Finset.exists_subset_card_eq ha_le_C
  let C₂ := C \ C₁
  have hC₂card : C₂.card ≤ a := by
    rw [card_sdiff_of_subset hC₁sub, hC₁card]; dsimp [a]; omega
  have hC₁₂_disj : Disjoint C₁ C₂ := disjoint_sdiff
  have hC₁₂_union : C₁ ∪ C₂ = C := union_sdiff_of_subset hC₁sub
  -- Split `R` into disjoint palettes `R₁` (`|R₁| = a + 2 * τ`) and `R₂` (`|R₂| = 2 * a - 3 + 2 * τ`).
  have hR₁_le : a + 2 * τ ≤ R.card := by dsimp [a] at *; omega
  obtain ⟨R₁, hR₁sub, hR₁card⟩ := Finset.exists_subset_card_eq hR₁_le
  have hR₂_le : 2 * a - 3 + 2 * τ ≤ (R \ R₁).card := by
    rw [card_sdiff_of_subset hR₁sub, hR₁card]; dsimp [a] at *; omega
  obtain ⟨R₂, hR₂sub', hR₂card⟩ := Finset.exists_subset_card_eq hR₂_le
  have hR₂sub : R₂ ⊆ R := hR₂sub'.trans sdiff_subset
  have hR₁₂_disj : Disjoint R₁ R₂ := disjoint_sdiff.mono_right hR₂sub'
  -- Common-neighbor list sizes in `R₁` and `R₂`:
  have hCN_size : ∀ (P : Finset (Fin n)), P ⊆ R → ∀ u ∈ C, ∀ v ∈ C,
      P.card - 2 * τ ≤ (P.filter (fun r ↦ G.Adj u r ∧ G.Adj v r)).card := by
    intro P hPR u hu v hv
    have hmiss : (P.filter (fun r ↦ ¬ (G.Adj u r ∧ G.Adj v r))).card ≤ 2 * τ := by
      have hsub : P.filter (fun r ↦ ¬ (G.Adj u r ∧ G.Adj v r)) ⊆
          R.filter (fun r ↦ ¬ G.Adj u r) ∪ R.filter (fun r ↦ ¬ G.Adj v r) := by
        intro r hr
        rw [mem_filter] at hr
        by_cases h1 : G.Adj u r
        · exact mem_union_right _ (mem_filter.mpr ⟨hPR hr.1, fun h2 ↦ hr.2 ⟨h1, h2⟩⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨hPR hr.1, h1⟩)
      have h1 := card_le_card hsub
      have h2 := card_union_le (R.filter (fun r ↦ ¬ G.Adj u r)) (R.filter (fun r ↦ ¬ G.Adj v r))
      have h3 := hτ u hu
      have h4 := hτ v hv
      omega
    have htot : (P.filter (fun r ↦ G.Adj u r ∧ G.Adj v r)).card +
        (P.filter (fun r ↦ ¬ (G.Adj u r ∧ G.Adj v r))).card = P.card := by
      simpa using Finset.sum_filter_add_sum_filter_not P (fun r ↦ G.Adj u r ∧ G.Adj v r) (fun _ ↦ (1 : ℕ))
    omega
  -- Step 1: Crossing pairs `C₁ × C₂` via Galvin's theorem using palette `R₁`.
  let e1 : Fin a ≃ C₁ := (Fintype.equivFinOfCardEq (by simp [hC₁card])).symm
  let e2 : Fin C₂.card ≃ C₂ := (Fintype.equivFinOfCardEq (by simp)).symm
  let Lcross : Fin a × Fin a → Finset (Fin n) := fun p ↦
    if h : p.2.val < C₂.card then
      R₁.filter (fun r ↦ G.Adj (e1 p.1).1 r ∧ G.Adj (e2 ⟨p.2.val, h⟩).1 r)
    else R₁
  have hLcross : ∀ p : Fin a × Fin a, a ≤ (Lcross p).card := by
    intro p
    dsimp [Lcross]
    split_ifs with h
    · have := hCN_size R₁ hR₁sub (e1 p.1).1 (hC₁sub (e1 p.1).2) (e2 ⟨p.2.val, h⟩).1 (sdiff_subset (e2 ⟨p.2.val, h⟩).2)
      omega
    · omega
  obtain ⟨fcross, hfcrossL, hfcrossRow, hfcrossCol⟩ := Galvin95.galvin_list_coloring (by omega) Lcross hLcross
  -- Step 2: Internal pairs of `C₁` and `C₂` greedily using palette `R₂`.
  let L2 : Sym2 (Fin n) → Finset (Fin n) := fun e ↦
    R₂.filter (fun r ↦ ∀ x ∈ e, G.Adj x r)
  have hL2_card : ∀ u ∈ C, ∀ v ∈ C, 2 * a - 3 ≤ (L2 s(u, v)).card := by
    intro u hu v hv
    have heq : L2 s(u, v) = R₂.filter (fun r ↦ G.Adj u r ∧ G.Adj v r) := by
      ext r; simp only [L2, mem_filter, Sym2.mem_iff]
      exact ⟨fun ⟨hr, h⟩ ↦ ⟨hr, h u (Or.inl rfl), h v (Or.inr rfl)⟩,
             fun ⟨hr, h1, h2⟩ ↦ ⟨hr, fun x hx ↦ by rcases hx with rfl | rfl <;> assumption⟩⟩
    rw [heq]
    have := hCN_size R₂ hR₂sub u hu v hv
    omega
  obtain ⟨ψ₁, hψ₁L, hψ₁prop⟩ := Galvin95.greedy_clique_list_coloring ha2 C₁ (by omega) L2
    (fun u hu v hv _ ↦ hL2_card u (hC₁sub hu) v (hC₁sub hv))
  obtain ⟨ψ₂, hψ₂L, hψ₂prop⟩ := Galvin95.greedy_clique_list_coloring ha2 C₂ hC₂card L2
    (fun u hu v hv _ ↦ hL2_card u (sdiff_subset hu) v (sdiff_subset hv))
  -- Step 3: Combine `fcross`, `ψ₁`, `ψ₂` into `φ : Sym2 (Fin n) → Fin n`.
  have hn_pos : 0 < n := by
    have := card_le_univ C; simp at this; omega
  let crossVal : Fin n → Fin n → Fin n := fun x y ↦
    if hx : x ∈ C₁ then
      if hy : y ∈ C₂ then
        fcross (e1.symm ⟨x, hx⟩, ⟨(e2.symm ⟨y, hy⟩).val, lt_of_lt_of_le (e2.symm ⟨y, hy⟩).isLt hC₂card⟩)
      else ⟨0, hn_pos⟩
    else if hy : y ∈ C₁ then
      if hx2 : x ∈ C₂ then
        fcross (e1.symm ⟨y, hy⟩, ⟨(e2.symm ⟨x, hx2⟩).val, lt_of_lt_of_le (e2.symm ⟨x, hx2⟩).isLt hC₂card⟩)
      else ⟨0, hn_pos⟩
    else ⟨0, hn_pos⟩
  have hcross_symm : ∀ x y, crossVal x y = crossVal y x := by
    intro x y
    dsimp [crossVal]
    by_cases hx1 : x ∈ C₁ <;> by_cases hy1 : y ∈ C₁
    · have hx2 : x ∉ C₂ := Finset.disjoint_left.mp hC₁₂_disj hx1
      have hy2 : y ∉ C₂ := Finset.disjoint_left.mp hC₁₂_disj hy1
      simp [hx1, hy1, hx2, hy2]
    · simp [hx1, hy1]
    · simp [hx1, hy1]
    · simp [hx1, hy1]
  let φ : Sym2 (Fin n) → Fin n := fun e ↦
    if ∀ x ∈ e, x ∈ C₁ then ψ₁ e
    else if ∀ x ∈ e, x ∈ C₂ then ψ₂ e
    else Sym2.lift ⟨crossVal, hcross_symm⟩ e
  have hφ_C1 : ∀ u ∈ C₁, ∀ v ∈ C₁, φ s(u, v) = ψ₁ s(u, v) := by
    intro u hu v hv
    dsimp [φ]
    rw [if_pos (fun x hx ↦ by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption)]
  have hφ_C2 : ∀ u ∈ C₂, ∀ v ∈ C₂, φ s(u, v) = ψ₂ s(u, v) := by
    intro u hu v hv
    dsimp [φ]
    have hnot1 : ¬ ∀ x ∈ s(u, v), x ∈ C₁ := fun h ↦
      Finset.disjoint_right.mp hC₁₂_disj hu (h u (by simp))
    rw [if_neg hnot1, if_pos (fun x hx ↦ by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption)]
  have hφ_cross : ∀ (u : Fin n) (hu : u ∈ C₁) (v : Fin n) (hv : v ∈ C₂),
      φ s(u, v) = fcross (e1.symm ⟨u, hu⟩,
        ⟨(e2.symm ⟨v, hv⟩).val, lt_of_lt_of_le (e2.symm ⟨v, hv⟩).isLt hC₂card⟩) := by
    intro u hu v hv
    dsimp [φ]
    have hnot1 : ¬ ∀ x ∈ s(u, v), x ∈ C₁ := fun h ↦
      Finset.disjoint_right.mp hC₁₂_disj hv (h v (by simp))
    have hnot2 : ¬ ∀ x ∈ s(u, v), x ∈ C₂ := fun h ↦
      Finset.disjoint_left.mp hC₁₂_disj hu (h u (by simp))
    rw [if_neg hnot1, if_neg hnot2]
    change crossVal u v = _
    dsimp [crossVal]
    rw [dif_pos hu, dif_pos hv]
  have hφ_R1_cross : ∀ u ∈ C₁, ∀ v ∈ C₂,
      φ s(u, v) ∈ R₁ ∧ G.Adj u (φ s(u, v)) ∧ G.Adj v (φ s(u, v)) := by
    intro u hu v hv
    rw [hφ_cross u hu v hv]
    let p : Fin a × Fin a := (e1.symm ⟨u, hu⟩,
      ⟨(e2.symm ⟨v, hv⟩).val, lt_of_lt_of_le (e2.symm ⟨v, hv⟩).isLt hC₂card⟩)
    have hmem := hfcrossL p
    dsimp [Lcross, p] at hmem
    rw [dif_pos (e2.symm ⟨v, hv⟩).isLt] at hmem
    rw [mem_filter] at hmem
    have he1 : (e1 (e1.symm ⟨u, hu⟩)).1 = u := by simp
    have he2 : (e2 ⟨(e2.symm ⟨v, hv⟩).val, (e2.symm ⟨v, hv⟩).isLt⟩).1 = v := by simp
    rw [he1, he2] at hmem
    exact ⟨hmem.1, hmem.2.1, hmem.2.2⟩
  refine ⟨φ, ?_, ?_⟩
  · intro u hu v hv huv
    have hu12 : u ∈ C₁ ∨ u ∈ C₂ := mem_union.mp (hC₁₂_union.symm ▸ hu)
    have hv12 : v ∈ C₁ ∨ v ∈ C₂ := mem_union.mp (hC₁₂_union.symm ▸ hv)
    rcases hu12 with hu1 | hu2 <;> rcases hv12 with hv1 | hv2
    · rw [hφ_C1 u hu1 v hv1]
      have hmem := hψ₁L u hu1 v hv1 huv.ne
      rw [mem_filter] at hmem
      exact ⟨hR₂sub hmem.1, hmem.2 u (by simp), hmem.2 v (by simp)⟩
    · have h := hφ_R1_cross u hu1 v hv2
      exact ⟨hR₁sub h.1, h.2.1, h.2.2⟩
    · rw [Sym2.eq_swap]
      have h := hφ_R1_cross v hv1 u hu2
      exact ⟨hR₁sub h.1, h.2.2, h.2.1⟩
    · rw [hφ_C2 u hu2 v hv2]
      have hmem := hψ₂L u hu2 v hv2 huv.ne
      rw [mem_filter] at hmem
      exact ⟨hR₂sub hmem.1, hmem.2 u (by simp), hmem.2 v (by simp)⟩
  · intro u hu v hv w hw hvw huv huw
    have hu12 : u ∈ C₁ ∨ u ∈ C₂ := mem_union.mp (hC₁₂_union.symm ▸ hu)
    have hv12 : v ∈ C₁ ∨ v ∈ C₂ := mem_union.mp (hC₁₂_union.symm ▸ hv)
    have hw12 : w ∈ C₁ ∨ w ∈ C₂ := mem_union.mp (hC₁₂_union.symm ▸ hw)
    rcases hu12 with hu1 | hu2 <;> rcases hv12 with hv1 | hv2 <;> rcases hw12 with hw1 | hw2
    · rw [hφ_C1 u hu1 v hv1, hφ_C1 u hu1 w hw1]
      exact hψ₁prop u hu1 v hv1 w hw1 huv.ne huw.ne hvw
    · have h1 : φ s(u, v) ∈ R₂ := by
        rw [hφ_C1 u hu1 v hv1]; exact (mem_filter.mp (hψ₁L u hu1 v hv1 huv.ne)).1
      have h2 : φ s(u, w) ∈ R₁ := (hφ_R1_cross u hu1 w hw2).1
      exact fun hEq ↦ Finset.disjoint_left.mp hR₁₂_disj h2 (hEq ▸ h1)
    · have h1 : φ s(u, v) ∈ R₁ := (hφ_R1_cross u hu1 v hv2).1
      have h2 : φ s(u, w) ∈ R₂ := by
        rw [hφ_C1 u hu1 w hw1]; exact (mem_filter.mp (hψ₁L u hu1 w hw1 huw.ne)).1
      exact fun hEq ↦ Finset.disjoint_left.mp hR₁₂_disj h1 (hEq ▸ h2)
    · rw [hφ_cross u hu1 v hv2, hφ_cross u hu1 w hw2]
      refine hfcrossRow (e1.symm ⟨u, hu1⟩) _ _ ?_
      intro hEq
      have hval : (e2.symm ⟨v, hv2⟩).val = (e2.symm ⟨w, hw2⟩).val := congrArg (Fin.val (n := a)) hEq
      exact hvw (congrArg Subtype.val (e2.symm.injective (Fin.ext hval)))
    · rw [Sym2.eq_swap (a := u) (b := v), Sym2.eq_swap (a := u) (b := w),
          hφ_cross v hv1 u hu2, hφ_cross w hw1 u hu2]
      refine hfcrossCol _ _ _ ?_
      intro hEq
      exact hvw (congrArg Subtype.val (e1.symm.injective hEq))
    · have h1 : φ s(u, v) ∈ R₁ := by rw [Sym2.eq_swap]; exact (hφ_R1_cross v hv1 u hu2).1
      have h2 : φ s(u, w) ∈ R₂ := by
        rw [hφ_C2 u hu2 w hw2]; exact (mem_filter.mp (hψ₂L u hu2 w hw2 huw.ne)).1
      exact fun hEq ↦ Finset.disjoint_left.mp hR₁₂_disj h1 (hEq ▸ h2)
    · have h1 : φ s(u, v) ∈ R₂ := by
        rw [hφ_C2 u hu2 v hv2]; exact (mem_filter.mp (hψ₂L u hu2 v hv2 huv.ne)).1
      have h2 : φ s(u, w) ∈ R₁ := by rw [Sym2.eq_swap]; exact (hφ_R1_cross w hw1 u hu2).1
      exact fun hEq ↦ Finset.disjoint_left.mp hR₁₂_disj h2 (hEq ▸ h1)
    · rw [hφ_C2 u hu2 v hv2, hφ_C2 u hu2 w hw2]
      exact hψ₂prop u hu2 v hv2 w hw2 huv.ne huw.ne hvw
