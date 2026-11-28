import OMAStatements.S_mo_88547
import Mathlib

namespace OMA.Mo88547

open OMA.S_mo_88547

lemma matchingCount_one {A B : Type} [DecidableEq A] [DecidableEq B] (E : Finset (A × B)) :
    matchingCount E 1 = E.card := by
  unfold matchingCount
  have h : (E.powersetCard 1).filter (fun M =>
      (M.image Prod.fst).card = 1 ∧ (M.image Prod.snd).card = 1) = E.powersetCard 1 := by
    rw [Finset.filter_eq_self]
    intro M hM
    rw [Finset.mem_powersetCard] at hM
    rcases Finset.card_eq_one.mp hM.2 with ⟨e, rfl⟩
    simp
  rw [h, Finset.card_powersetCard, Nat.choose_one_right]

lemma matchingCount_image_inj {A B A' B' : Type} [DecidableEq A] [DecidableEq B]
    [DecidableEq A'] [DecidableEq B']
    (E : Finset (A × B)) (fA : A → A') (fB : B → B')
    (hfA : Set.InjOn fA (E.image Prod.fst : Set A))
    (hfB : Set.InjOn fB (E.image Prod.snd : Set B)) (i : ℕ) :
    matchingCount (E.image (Prod.map fA fB)) i = matchingCount E i := by
  unfold matchingCount
  have hmapInj : Set.InjOn (Prod.map fA fB) (E : Set (A × B)) := by
    intro e₁ he₁ e₂ he₂ heq
    have h1 : fA e₁.1 = fA e₂.1 := congrArg Prod.fst heq
    have h2 : fB e₁.2 = fB e₂.2 := congrArg Prod.snd heq
    have hf1 : e₁.1 = e₂.1 := hfA (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ he₁))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ he₂)) h1
    have hf2 : e₁.2 = e₂.2 := hfB (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ he₁))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ he₂)) h2
    exact Prod.ext hf1 hf2
  refine Finset.card_bij (fun M _ => M.image (Prod.map fA fB)) ?_ ?_ ?_ |>.symm
  · intro M hM
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hM ⊢
    rcases hM with ⟨⟨hME, hMcard⟩, hfst, hsnd⟩
    have hMinj : Set.InjOn (Prod.map fA fB) (M : Set (A × B)) := hmapInj.mono hME
    refine ⟨⟨Finset.image_subset_image hME, ?_⟩, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn hMinj, hMcard]
    · have himg : (M.image (Prod.map fA fB)).image Prod.fst = (M.image Prod.fst).image fA := by
        simp only [Finset.image_image]; rfl
      rw [himg, Finset.card_image_of_injOn (hfA.mono (Finset.coe_subset.mpr (Finset.image_subset_image hME))), hfst]
    · have himg : (M.image (Prod.map fA fB)).image Prod.snd = (M.image Prod.snd).image fB := by
        simp only [Finset.image_image]; rfl
      rw [himg, Finset.card_image_of_injOn (hfB.mono (Finset.coe_subset.mpr (Finset.image_subset_image hME))), hsnd]
  · intro M₁ hM₁ M₂ hM₂ heq
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hM₁ hM₂
    ext e
    constructor
    · intro he
      have hmem : Prod.map fA fB e ∈ M₂.image (Prod.map fA fB) :=
        heq ▸ Finset.mem_image_of_mem _ he
      rcases Finset.mem_image.mp hmem with ⟨e', he', heq'⟩
      have : e' = e := hmapInj (hM₂.1.1 he') (hM₁.1.1 he) heq'
      exact this ▸ he'
    · intro he
      have hmem : Prod.map fA fB e ∈ M₁.image (Prod.map fA fB) :=
        heq.symm ▸ Finset.mem_image_of_mem _ he
      rcases Finset.mem_image.mp hmem with ⟨e', he', heq'⟩
      have : e' = e := hmapInj (hM₁.1.1 he') (hM₂.1.1 he) heq'
      exact this ▸ he'
  · intro N hN
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hN
    rcases hN with ⟨⟨hNE, hNcard⟩, hfst, hsnd⟩
    let M : Finset (A × B) := E.filter (fun e => Prod.map fA fB e ∈ N)
    have hMimg : M.image (Prod.map fA fB) = N := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, M]
      constructor
      · rintro ⟨e, ⟨_, heN⟩, rfl⟩
        exact heN
      · intro hx
        rcases Finset.mem_image.mp (hNE hx) with ⟨e, heE, rfl⟩
        exact ⟨e, ⟨heE, hx⟩, rfl⟩
    refine ⟨M, ?_, hMimg⟩
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    have hME : M ⊆ E := Finset.filter_subset _ _
    have hMinj : Set.InjOn (Prod.map fA fB) (M : Set (A × B)) := hmapInj.mono hME
    refine ⟨⟨hME, ?_⟩, ?_, ?_⟩
    · rw [← Finset.card_image_of_injOn hMinj, hMimg, hNcard]
    · have himg : N.image Prod.fst = (M.image Prod.fst).image fA := by
        rw [← hMimg]; simp only [Finset.image_image]; rfl
      rw [← Finset.card_image_of_injOn (hfA.mono (Finset.coe_subset.mpr (Finset.image_subset_image hME))), ← himg, hfst]
    · have himg : N.image Prod.snd = (M.image Prod.snd).image fB := by
        rw [← hMimg]; simp only [Finset.image_image]; rfl
      rw [← Finset.card_image_of_injOn (hfB.mono (Finset.coe_subset.mpr (Finset.image_subset_image hME))), ← himg, hsnd]

lemma matchingCount_equiv {A B A' B' : Type} [DecidableEq A] [DecidableEq B]
    [DecidableEq A'] [DecidableEq B']
    (E : Finset (A × B)) (eA : A ≃ A') (eB : B ≃ B') (i : ℕ) :
    matchingCount (E.image (Prod.map eA eB)) i = matchingCount E i :=
  matchingCount_image_inj E eA eB (fun _ _ _ _ h => eA.injective h)
    (fun _ _ _ _ h => eB.injective h) i

lemma matching_card_le_cover {A B : Type} [DecidableEq A] [DecidableEq B]
    {E : Finset (A × B)} {CA : Finset A} {CB : Finset B}
    (hcov : ∀ e ∈ E, e.1 ∈ CA ∨ e.2 ∈ CB) {r : ℕ} (hr : 0 < matchingCount E r) :
    r ≤ CA.card + CB.card := by
  unfold matchingCount at hr
  rcases Finset.card_pos.mp hr with ⟨M, hM⟩
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hM
  rcases hM with ⟨⟨hME, hMcard⟩, hfst, hsnd⟩
  let M1 := M.filter (fun e => e.1 ∈ CA)
  let M2 := M.filter (fun e => e.1 ∉ CA)
  have hsplit : M.card = M1.card + M2.card := (Finset.card_filter_add_card_filter_not (fun e : A × B => e.1 ∈ CA)).symm
  have hfst_inj : Set.InjOn Prod.fst (M : Set (A × B)) :=
    Finset.injOn_of_card_image_eq (by rw [hfst, hMcard])
  have hsnd_inj : Set.InjOn Prod.snd (M : Set (A × B)) :=
    Finset.injOn_of_card_image_eq (by rw [hsnd, hMcard])
  have h1 : M1.card ≤ CA.card := by
    have hsub : M1.image Prod.fst ⊆ CA := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
      exact (Finset.mem_filter.mp he).2
    calc
      M1.card = (M1.image Prod.fst).card :=
        (Finset.card_image_of_injOn (hfst_inj.mono (Finset.filter_subset _ _))).symm
      _ ≤ CA.card := Finset.card_le_card hsub
  have h2 : M2.card ≤ CB.card := by
    have hsub : M2.image Prod.snd ⊆ CB := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨e, he, rfl⟩
      rcases Finset.mem_filter.mp he with ⟨heM, henot⟩
      exact (hcov e (hME heM)).resolve_left henot
    calc
      M2.card = (M2.image Prod.snd).card :=
        (Finset.card_image_of_injOn (hsnd_inj.mono (Finset.filter_subset _ _))).symm
      _ ≤ CB.card := Finset.card_le_card hsub
  omega

lemma konig_vertex_cover {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) {r : ℕ} (hzero : matchingCount E (r + 1) = 0) :
    ∃ (CA : Finset A) (CB : Finset B),
      CA.card + CB.card ≤ r ∧ ∀ e ∈ E, e.1 ∈ CA ∨ e.2 ∈ CB := by
  classical
  let covers : Finset (Finset A × Finset B) :=
    Finset.univ.filter fun p => ∀ e ∈ E, e.1 ∈ p.1 ∨ e.2 ∈ p.2
  have hne : covers.Nonempty := by
    refine ⟨(Finset.univ, ∅), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro e _
    exact Or.inl (Finset.mem_univ e.1)
  obtain ⟨⟨CA, CB⟩, hmem, hmin⟩ := Finset.exists_min_image covers (fun p => p.1.card + p.2.card) hne
  have hcov : ∀ e ∈ E, e.1 ∈ CA ∨ e.2 ∈ CB := (Finset.mem_filter.mp hmem).2
  refine ⟨CA, CB, ?_, hcov⟩
  by_contra hgt
  have hge : r + 1 ≤ CA.card + CB.card := by omega
  let N1 : ↥CA → Finset B := fun u => (Finset.univ \ CB).filter fun v => (u.1, v) ∈ E
  have hHall1 : ∀ S : Finset ↥CA, S.card ≤ (S.biUnion N1).card := by
    intro S
    let CA' : Finset A := CA \ S.image Subtype.val
    let CB' : Finset B := CB ∪ S.biUnion N1
    have hcov' : (CA', CB') ∈ covers := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e he => ?_⟩
      by_cases hCB : e.2 ∈ CB
      · exact Or.inr (Finset.mem_union_left _ hCB)
      · have hCA : e.1 ∈ CA := (hcov e he).resolve_right hCB
        by_cases hS : (⟨e.1, hCA⟩ : ↥CA) ∈ S
        · refine Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨e.1, hCA⟩, hS, ?_⟩))
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hCB⟩, he⟩
        · refine Or.inl (Finset.mem_sdiff.mpr ⟨hCA, ?_⟩)
          intro himg
          rcases Finset.mem_image.mp himg with ⟨u, huS, huEq⟩
          have : u = ⟨e.1, hCA⟩ := Subtype.ext huEq
          exact hS (this ▸ huS)
    have hle : CA.card + CB.card ≤ CA'.card + CB'.card := hmin (CA', CB') hcov'
    have hSsub : S.image Subtype.val ⊆ CA := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨u, _, rfl⟩
      exact u.2
    have hcardA : CA'.card + S.card = CA.card := by
      have hsd : CA'.card = CA.card - (S.image Subtype.val).card := Finset.card_sdiff_of_subset hSsub
      rw [hsd, Finset.card_image_of_injective _ Subtype.val_injective]
      have : S.card ≤ CA.card := by
        simpa [Finset.card_image_of_injective _ Subtype.val_injective] using Finset.card_le_card hSsub
      omega
    have hcardB : CB'.card ≤ CB.card + (S.biUnion N1).card := Finset.card_union_le _ _
    omega
  obtain ⟨f1, hf1_inj, hf1_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N1).mp hHall1
  let N2 : ↥CB → Finset A := fun v => (Finset.univ \ CA).filter fun u => (u, v.1) ∈ E
  have hHall2 : ∀ S : Finset ↥CB, S.card ≤ (S.biUnion N2).card := by
    intro S
    let CA' : Finset A := CA ∪ S.biUnion N2
    let CB' : Finset B := CB \ S.image Subtype.val
    have hcov' : (CA', CB') ∈ covers := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e he => ?_⟩
      by_cases hCA : e.1 ∈ CA
      · exact Or.inl (Finset.mem_union_left _ hCA)
      · have hCB : e.2 ∈ CB := (hcov e he).resolve_left hCA
        by_cases hS : (⟨e.2, hCB⟩ : ↥CB) ∈ S
        · refine Or.inl (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨e.2, hCB⟩, hS, ?_⟩))
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hCA⟩, he⟩
        · refine Or.inr (Finset.mem_sdiff.mpr ⟨hCB, ?_⟩)
          intro himg
          rcases Finset.mem_image.mp himg with ⟨v, hvS, hvEq⟩
          have : v = ⟨e.2, hCB⟩ := Subtype.ext hvEq
          exact hS (this ▸ hvS)
    have hle : CA.card + CB.card ≤ CA'.card + CB'.card := hmin (CA', CB') hcov'
    have hSsub : S.image Subtype.val ⊆ CB := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨v, _, rfl⟩
      exact v.2
    have hcardB : CB'.card + S.card = CB.card := by
      have hsd : CB'.card = CB.card - (S.image Subtype.val).card := Finset.card_sdiff_of_subset hSsub
      rw [hsd, Finset.card_image_of_injective _ Subtype.val_injective]
      have : S.card ≤ CB.card := by
        simpa [Finset.card_image_of_injective _ Subtype.val_injective] using Finset.card_le_card hSsub
      omega
    have hcardA : CA'.card ≤ CA.card + (S.biUnion N2).card := Finset.card_union_le _ _
    omega
  obtain ⟨f2, hf2_inj, hf2_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N2).mp hHall2
  let M1 : Finset (A × B) := Finset.univ.image fun u : ↥CA => (u.1, f1 u)
  let M2 : Finset (A × B) := Finset.univ.image fun v : ↥CB => (f2 v, v.1)
  let M : Finset (A × B) := M1 ∪ M2
  have hMsub : M ⊆ E := by
    intro e he
    rcases Finset.mem_union.mp he with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨u, _, rfl⟩
      exact (Finset.mem_filter.mp (hf1_mem u)).2
    · rcases Finset.mem_image.mp h2 with ⟨v, _, rfl⟩
      exact (Finset.mem_filter.mp (hf2_mem v)).2
  have hdisj : Disjoint M1 M2 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rcases Finset.mem_image.mp h1 with ⟨u, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨v, _, heq⟩
    have hf2not : f2 v ∉ CA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hf2_mem v)).1).2
    have : f2 v = u.1 := congrArg Prod.fst heq
    exact hf2not (this ▸ u.2)
  have hM1card : M1.card = CA.card := by
    rw [Finset.card_image_of_injective _ (fun u₁ u₂ h => Subtype.ext (congrArg Prod.fst h))]
    simp
  have hM2card : M2.card = CB.card := by
    rw [Finset.card_image_of_injective _ (fun v₁ v₂ h => Subtype.ext (congrArg Prod.snd h))]
    simp
  have hMcard : M.card = CA.card + CB.card := by
    rw [Finset.card_union_of_disjoint hdisj, hM1card, hM2card]
  have hMfst : Set.InjOn Prod.fst (M : Set (A × B)) := by
    intro e₁ he₁ e₂ he₂ heq
    rcases Finset.mem_union.mp he₁ with h1 | h1 <;> rcases Finset.mem_union.mp he₂ with h2 | h2
    · rcases Finset.mem_image.mp h1 with ⟨u₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨u₂, _, rfl⟩
      dsimp only at heq
      have : u₁ = u₂ := Subtype.ext heq
      rw [this]
    · rcases Finset.mem_image.mp h1 with ⟨u₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨v₂, _, rfl⟩
      dsimp only at heq
      have hnot : f2 v₂ ∉ CA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hf2_mem v₂)).1).2
      exact absurd (heq ▸ u₁.2) hnot
    · rcases Finset.mem_image.mp h1 with ⟨v₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨u₂, _, rfl⟩
      dsimp only at heq
      have hnot : f2 v₁ ∉ CA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hf2_mem v₁)).1).2
      exact absurd (heq.symm ▸ u₂.2) hnot
    · rcases Finset.mem_image.mp h1 with ⟨v₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨v₂, _, rfl⟩
      dsimp only at heq
      have : v₁ = v₂ := hf2_inj heq
      rw [this]
  have hMsnd : Set.InjOn Prod.snd (M : Set (A × B)) := by
    intro e₁ he₁ e₂ he₂ heq
    rcases Finset.mem_union.mp he₁ with h1 | h1 <;> rcases Finset.mem_union.mp he₂ with h2 | h2
    · rcases Finset.mem_image.mp h1 with ⟨u₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨u₂, _, rfl⟩
      dsimp only at heq
      have : u₁ = u₂ := hf1_inj heq
      rw [this]
    · rcases Finset.mem_image.mp h1 with ⟨u₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨v₂, _, rfl⟩
      dsimp only at heq
      have hnot : f1 u₁ ∉ CB := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hf1_mem u₁)).1).2
      exact absurd (heq.symm ▸ v₂.2) hnot
    · rcases Finset.mem_image.mp h1 with ⟨v₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨u₂, _, rfl⟩
      dsimp only at heq
      have hnot : f1 u₂ ∉ CB := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hf1_mem u₂)).1).2
      exact absurd (heq ▸ v₁.2) hnot
    · rcases Finset.mem_image.mp h1 with ⟨v₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨v₂, _, rfl⟩
      dsimp only at heq
      have : v₁ = v₂ := Subtype.ext heq
      rw [this]
  have hleM : r + 1 ≤ M.card := by omega
  obtain ⟨M', hM'sub, hM'card⟩ := Finset.exists_subset_card_eq hleM
  have hM'mem : M' ∈ (E.powersetCard (r + 1)).filter fun N =>
      (N.image Prod.fst).card = r + 1 ∧ (N.image Prod.snd).card = r + 1 := by
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨hM'sub.trans hMsub, hM'card⟩, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn (hMfst.mono (Finset.coe_subset.mpr hM'sub)), hM'card]
    · rw [Finset.card_image_of_injOn (hMsnd.mono (Finset.coe_subset.mpr hM'sub)), hM'card]
  have hpos : 0 < matchingCount E (r + 1) := Finset.card_pos.mpr ⟨M', hM'mem⟩
  omega

lemma mem_of_if_neg {α : Type*} {P : Prop} [Decidable P] {s t : Finset α} {x : α}
    (h : ¬ P) (hx : x ∈ if P then s else t) : x ∈ t := by
  simpa [h] using hx

lemma forward {k : ℕ} {m : Fin (k + 1) → ℕ} (hm : ∀ i, 0 < m i)
    {A B : ℕ} {E : Finset (Fin A × Fin B)} (hreal : realizes E m) :
    ∃ (a b : ℕ) (H : Finset (Fin a × Fin b))
      (p : Finset (Fin a) → ℕ) (q : Finset (Fin b) → ℕ),
      a + b = k + 1 ∧ p ∅ = 0 ∧ q ∅ = 0 ∧
      (∀ S, p S ≤ m 0) ∧ (∀ S, q S ≤ m 0) ∧ realizes (coverEdges H p q) m := by
  classical
  have hzero : matchingCount E (k + 2) = 0 := hreal.2
  obtain ⟨CA, CB, hle, hcov⟩ := konig_vertex_cover E hzero
  have hlast_pos : 0 < matchingCount E (k + 1) := by
    have h1 : matchingCount E (k + 1) = m ⟨k, Nat.lt_succ_self k⟩ := hreal.1 ⟨k, Nat.lt_succ_self k⟩
    have hp := hm ⟨k, Nat.lt_succ_self k⟩
    omega
  have hge : k + 1 ≤ CA.card + CB.card := matching_card_le_cover hcov hlast_pos
  have hab : CA.card + CB.card = k + 1 := le_antisymm hle hge
  let a := CA.card
  let b := CB.card
  let eA : ↥CA ≃ Fin a := Fintype.equivFinOfCardEq (Fintype.card_coe CA)
  let eB : ↥CB ≃ Fin b := Fintype.equivFinOfCardEq (Fintype.card_coe CB)
  let H : Finset (Fin a × Fin b) := Finset.univ.filter fun uv =>
    ((eA.symm uv.1).1, (eB.symm uv.2).1) ∈ E
  let nbR : Fin B → Finset (Fin a) := fun v =>
    Finset.univ.filter fun i : Fin a => ((eA.symm i).1, v) ∈ E
  let nbL : Fin A → Finset (Fin b) := fun u =>
    Finset.univ.filter fun j : Fin b => (u, (eB.symm j).1) ∈ E
  let fiberR : Finset (Fin a) → Finset (Fin B) := fun S =>
    (Finset.univ \ CB).filter fun v => nbR v = S
  let fiberL : Finset (Fin b) → Finset (Fin A) := fun S =>
    (Finset.univ \ CA).filter fun u => nbL u = S
  let p : Finset (Fin a) → ℕ := fun S => if S = ∅ then 0 else (fiberR S).card
  let q : Finset (Fin b) → ℕ := fun S => if S = ∅ then 0 else (fiberL S).card
  have hp0 : p ∅ = 0 := by simp [p]
  have hq0 : q ∅ = 0 := by simp [q]
  have hEcard : E.card = m 0 := by
    have h1 := hreal.1 ⟨0, Nat.zero_lt_succ k⟩
    simpa [matchingCount_one] using h1
  have hp_le : ∀ S, p S ≤ m 0 := by
    intro S
    dsimp only [p]
    split_ifs with hS
    · exact Nat.zero_le _
    · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      rw [← hEcard]
      have hsub : (fiberR S).image (fun v => ((eA.symm i₀).1, v)) ⊆ E := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨v, hv, rfl⟩
        have hnb : nbR v = S := (Finset.mem_filter.mp hv).2
        have hi : i₀ ∈ nbR v := hnb.symm ▸ hi₀
        exact (Finset.mem_filter.mp hi).2
      calc
        (fiberR S).card = ((fiberR S).image (fun v => ((eA.symm i₀).1, v))).card :=
          (Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)).symm
        _ ≤ E.card := Finset.card_le_card hsub
  have hq_le : ∀ S, q S ≤ m 0 := by
    intro S
    dsimp only [q]
    split_ifs with hS
    · exact Nat.zero_le _
    · obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      rw [← hEcard]
      have hsub : (fiberL S).image (fun u => (u, (eB.symm j₀).1)) ⊆ E := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨u, hu, rfl⟩
        have hnb : nbL u = S := (Finset.mem_filter.mp hu).2
        have hj : j₀ ∈ nbL u := hnb.symm ▸ hj₀
        exact (Finset.mem_filter.mp hj).2
      calc
        (fiberL S).card = ((fiberL S).image (fun u => (u, (eB.symm j₀).1))).card :=
          (Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)).symm
        _ ≤ E.card := Finset.card_le_card hsub
  let eL : ∀ S : Finset (Fin b), ↥(if S = ∅ then (∅ : Finset (Fin A)) else fiberL S) ≃ Fin (q S) :=
    fun S => Fintype.equivFinOfCardEq (by
      rw [Fintype.card_coe]
      dsimp only [q]
      split_ifs <;> simp)
  let eR : ∀ S : Finset (Fin a), ↥(if S = ∅ then (∅ : Finset (Fin B)) else fiberR S) ≃ Fin (p S) :=
    fun S => Fintype.equivFinOfCardEq (by
      rw [Fintype.card_coe]
      dsimp only [p]
      split_ifs <;> simp)
  let LeftT := Fin a ⊕ (Σ S : Finset (Fin b), Fin (q S))
  let RightT := Fin b ⊕ (Σ S : Finset (Fin a), Fin (p S))
  let gA : LeftT → Fin A := fun x =>
    match x with
    | Sum.inl i => (eA.symm i).1
    | Sum.inr ⟨S, idx⟩ => ((eL S).symm idx).1
  let gB : RightT → Fin B := fun y =>
    match y with
    | Sum.inl j => (eB.symm j).1
    | Sum.inr ⟨S, idx⟩ => ((eR S).symm idx).1
  have hgA_inj : Function.Injective gA := by
    intro x₁ x₂ heq
    cases x₁ with
    | inl i₁ =>
      cases x₂ with
      | inl i₂ =>
        dsimp only [gA] at heq
        exact congrArg Sum.inl (eA.symm.injective (Subtype.ext heq))
      | inr p₂ =>
        rcases p₂ with ⟨S₂, idx₂⟩
        dsimp only [gA] at heq
        have hmem := ((eL S₂).symm idx₂).2
        by_cases hS₂ : S₂ = ∅
        · simp [hS₂] at hmem
        · have hmem' := mem_of_if_neg hS₂ hmem
          have hnot : ((eL S₂).symm idx₂).1 ∉ CA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hmem').1).2
          exact absurd (heq ▸ (eA.symm i₁).2) hnot
    | inr p₁ =>
      rcases p₁ with ⟨S₁, idx₁⟩
      cases x₂ with
      | inl i₂ =>
        dsimp only [gA] at heq
        have hmem := ((eL S₁).symm idx₁).2
        by_cases hS₁ : S₁ = ∅
        · simp [hS₁] at hmem
        · have hmem' := mem_of_if_neg hS₁ hmem
          have hnot : ((eL S₁).symm idx₁).1 ∉ CA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hmem').1).2
          exact absurd (heq.symm ▸ (eA.symm i₂).2) hnot
      | inr p₂ =>
        rcases p₂ with ⟨S₂, idx₂⟩
        dsimp only [gA] at heq
        have hmem₁ := ((eL S₁).symm idx₁).2
        have hmem₂ := ((eL S₂).symm idx₂).2
        have hS₁ : S₁ ≠ ∅ := fun h => by simp [h] at hmem₁
        have hS₂ : S₂ ≠ ∅ := fun h => by simp [h] at hmem₂
        have hnb₁ : nbL ((eL S₁).symm idx₁).1 = S₁ := (Finset.mem_filter.mp (mem_of_if_neg hS₁ hmem₁)).2
        have hnb₂ : nbL ((eL S₂).symm idx₂).1 = S₂ := (Finset.mem_filter.mp (mem_of_if_neg hS₂ hmem₂)).2
        have hSeq : S₁ = S₂ := by rw [← hnb₁, heq, hnb₂]
        subst hSeq
        have hidx : idx₁ = idx₂ := (eL S₁).symm.injective (Subtype.ext heq)
        rw [hidx]
  have hgB_inj : Function.Injective gB := by
    intro y₁ y₂ heq
    cases y₁ with
    | inl j₁ =>
      cases y₂ with
      | inl j₂ =>
        dsimp only [gB] at heq
        exact congrArg Sum.inl (eB.symm.injective (Subtype.ext heq))
      | inr p₂ =>
        rcases p₂ with ⟨S₂, idx₂⟩
        dsimp only [gB] at heq
        have hmem := ((eR S₂).symm idx₂).2
        by_cases hS₂ : S₂ = ∅
        · simp [hS₂] at hmem
        · have hmem' := mem_of_if_neg hS₂ hmem
          have hnot : ((eR S₂).symm idx₂).1 ∉ CB := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hmem').1).2
          exact absurd (heq ▸ (eB.symm j₁).2) hnot
    | inr p₁ =>
      rcases p₁ with ⟨S₁, idx₁⟩
      cases y₂ with
      | inl j₂ =>
        dsimp only [gB] at heq
        have hmem := ((eR S₁).symm idx₁).2
        by_cases hS₁ : S₁ = ∅
        · simp [hS₁] at hmem
        · have hmem' := mem_of_if_neg hS₁ hmem
          have hnot : ((eR S₁).symm idx₁).1 ∉ CB := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hmem').1).2
          exact absurd (heq.symm ▸ (eB.symm j₂).2) hnot
      | inr p₂ =>
        rcases p₂ with ⟨S₂, idx₂⟩
        dsimp only [gB] at heq
        have hmem₁ := ((eR S₁).symm idx₁).2
        have hmem₂ := ((eR S₂).symm idx₂).2
        have hS₁ : S₁ ≠ ∅ := fun h => by simp [h] at hmem₁
        have hS₂ : S₂ ≠ ∅ := fun h => by simp [h] at hmem₂
        have hnb₁ : nbR ((eR S₁).symm idx₁).1 = S₁ := (Finset.mem_filter.mp (mem_of_if_neg hS₁ hmem₁)).2
        have hnb₂ : nbR ((eR S₂).symm idx₂).1 = S₂ := (Finset.mem_filter.mp (mem_of_if_neg hS₂ hmem₂)).2
        have hSeq : S₁ = S₂ := by rw [← hnb₁, heq, hnb₂]
        subst hSeq
        have hidx : idx₁ = idx₂ := (eR S₁).symm.injective (Subtype.ext heq)
        rw [hidx]
  have himgE : (coverEdges H p q).image (Prod.map gA gB) = E := by
    ext ⟨u, v⟩
    simp only [Finset.mem_image, coverEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨x, y⟩, hxy, heq⟩
      have hu : gA x = u := congrArg Prod.fst heq
      have hv : gB y = v := congrArg Prod.snd heq
      subst hu; subst hv
      cases x with
      | inl i =>
        cases y with
        | inl j =>
          simp only [decide_eq_true_eq, H, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
          exact hxy
        | inr pr =>
          rcases pr with ⟨S, idx⟩
          simp only [decide_eq_true_eq] at hxy
          have hmem := ((eR S).symm idx).2
          have hS : S ≠ ∅ := fun h => by simp [h] at hmem
          have hnb : nbR ((eR S).symm idx).1 = S := (Finset.mem_filter.mp (mem_of_if_neg hS hmem)).2
          have hi : i ∈ nbR ((eR S).symm idx).1 := hnb.symm ▸ hxy
          exact (Finset.mem_filter.mp hi).2
      | inr pl =>
        rcases pl with ⟨S, idx⟩
        cases y with
        | inl j =>
          simp only [decide_eq_true_eq] at hxy
          have hmem := ((eL S).symm idx).2
          have hS : S ≠ ∅ := fun h => by simp [h] at hmem
          have hnb : nbL ((eL S).symm idx).1 = S := (Finset.mem_filter.mp (mem_of_if_neg hS hmem)).2
          have hj : j ∈ nbL ((eL S).symm idx).1 := hnb.symm ▸ hxy
          exact (Finset.mem_filter.mp hj).2
        | inr pr =>
          simp at hxy
    · intro huv
      by_cases huCA : u ∈ CA
      · by_cases hvCB : v ∈ CB
        · refine ⟨(Sum.inl (eA ⟨u, huCA⟩), Sum.inl (eB ⟨v, hvCB⟩)), ?_, ?_⟩
          · simp only [decide_eq_true_eq, H, Finset.mem_filter, Finset.mem_univ, true_and,
              Equiv.symm_apply_apply]
            exact huv
          · simp [gA, gB]
        · let S := nbR v
          have hiS : eA ⟨u, huCA⟩ ∈ S := by
            simp only [S, nbR, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
            exact huv
          have hSne : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨_, hiS⟩
          have hvmem : v ∈ (if S = ∅ then (∅ : Finset (Fin B)) else fiberR S) := by
            rw [if_neg hSne]
            exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvCB⟩, rfl⟩
          refine ⟨(Sum.inl (eA ⟨u, huCA⟩), Sum.inr ⟨S, eR S ⟨v, hvmem⟩⟩), ?_, ?_⟩
          · simp [hiS]
          · simp [gA, gB]
      · have hvCB : v ∈ CB := (hcov (u, v) huv).resolve_left huCA
        let S := nbL u
        have hjS : eB ⟨v, hvCB⟩ ∈ S := by
          simp only [S, nbL, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
          exact huv
        have hSne : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨_, hjS⟩
        have humem : u ∈ (if S = ∅ then (∅ : Finset (Fin A)) else fiberL S) := by
          rw [if_neg hSne]
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huCA⟩, rfl⟩
        refine ⟨(Sum.inr ⟨S, eL S ⟨u, humem⟩⟩, Sum.inl (eB ⟨v, hvCB⟩)), ?_, ?_⟩
        · simp [hjS]
        · simp [gA, gB]
  have hmc : ∀ i, matchingCount (coverEdges H p q) i = matchingCount E i := by
    intro i
    rw [← himgE]
    exact (matchingCount_image_inj (coverEdges H p q) gA gB
      (fun _ _ _ _ h => hgA_inj h) (fun _ _ _ _ h => hgB_inj h) i).symm
  refine ⟨a, b, H, p, q, hab, hp0, hq0, hp_le, hq_le, ?_⟩
  exact ⟨fun i => by rw [hmc, hreal.1 i], by rw [hmc, hreal.2]⟩

lemma backward {k : ℕ} {m : Fin (k + 1) → ℕ}
    {a b : ℕ} {H : Finset (Fin a × Fin b)}
    {p : Finset (Fin a) → ℕ} {q : Finset (Fin b) → ℕ}
    (hreal : realizes (coverEdges H p q) m) :
    ∃ (A B : ℕ) (E : Finset (Fin A × Fin B)), realizes E m := by
  classical
  let LeftT := Fin a ⊕ (Σ S : Finset (Fin b), Fin (q S))
  let RightT := Fin b ⊕ (Σ S : Finset (Fin a), Fin (p S))
  let eL : LeftT ≃ Fin (Fintype.card LeftT) := Fintype.equivFin LeftT
  let eR : RightT ≃ Fin (Fintype.card RightT) := Fintype.equivFin RightT
  refine ⟨Fintype.card LeftT, Fintype.card RightT,
    (coverEdges H p q).image (Prod.map eL eR), ?_⟩
  refine ⟨fun i => ?_, ?_⟩
  · rw [matchingCount_equiv]
    exact hreal.1 i
  · rw [matchingCount_equiv]
    exact hreal.2

end OMA.Mo88547

theorem OMA.solution : type_of% @OMA.S_mo_88547.main := by
  intro k m hm
  exact ⟨fun ⟨_, _, _, h⟩ => OMA.Mo88547.forward hm h,
    fun ⟨_, _, _, _, _, _, _, _, _, _, h⟩ => OMA.Mo88547.backward h⟩
