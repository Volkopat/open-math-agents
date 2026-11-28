import OMAReductions.R_Erdos1183_erdos_1183_parts_iii_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Exponential upper bound for Erdos Problem 1183 part iii (H2)

We prove that for every `ε > 0`, eventually `(Erdos1183.F n : ℝ) < (1 + ε) ^ n`.

The proof combines a self-contained Sauer-Shelah lemma with a first-moment
probabilistic-method count over 2-colorings of `Finset (Fin n)`:
1. Any family `ℱ` of subsets of `Fin n` with `∑ j ∈ range d, n.choose j < ℱ.card`
   shatters some `d`-element subset `S`.
2. If `ℱ` is also union-closed (`SupClosed`), picking `f i ∈ ℱ` with `f i ∩ S = {i}`
   yields `2 ^ d - 1` pairwise distinct nonempty unions inside `ℱ`.
3. Counting 2-colorings `c : Finset (Fin n) → Bool` for which some tuple `f` produces
   a monochromatic union-cube of size `2 ^ d - 1` shows that whenever `1 ≤ d ≤ n` and
   `n * d + 2 < 2 ^ d`, a good coloring exists, whence `Erdos1183.F n ≤ (n + 1) ^ d`.
4. Taking `d = 2 * Nat.log 2 n + 4` and comparing `(n + 1) ^ d` with `2 ^ (n / M)`
   (where `(1 + ε) ^ M ≥ 2` by Bernoulli's inequality) yields `(F n : ℝ) < (1 + ε) ^ n`
   for all sufficiently large `n`.
-/

namespace Erdos1183H2

open Finset

private lemma sum_choose_succ (n d : ℕ) :
    ∑ j ∈ Finset.range (d + 1), (n + 1).choose j =
      (∑ j ∈ Finset.range (d + 1), n.choose j) + ∑ j ∈ Finset.range d, n.choose j := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun j => n.choose j) (d + 1),
      Finset.sum_range_succ (fun j => n.choose j) d, Nat.choose_succ_succ]
    simp only [Nat.succ_eq_add_one]
    omega

private lemma sum_choose_le_pow (n d : ℕ) :
    ∑ j ∈ Finset.range d, n.choose j ≤ (n + 1) ^ d := by
  induction n generalizing d with
  | zero =>
    cases d with
    | zero => simp
    | succ d =>
      rw [Finset.sum_range_succ']
      simp
  | succ n ih =>
    cases d with
    | zero => simp
    | succ d =>
      rw [sum_choose_succ]
      have h1 := ih (d + 1)
      have h2 := ih d
      have h3 : (n + 1) ^ d ≤ (n + 2) ^ d := Nat.pow_le_pow_left (by omega) d
      calc
        (∑ j ∈ Finset.range (d + 1), n.choose j) + ∑ j ∈ Finset.range d, n.choose j
            ≤ (n + 1) ^ (d + 1) + (n + 1) ^ d := Nat.add_le_add h1 h2
        _ = (n + 2) * (n + 1) ^ d := by rw [pow_succ']; ring
        _ ≤ (n + 2) * (n + 2) ^ d := Nat.mul_le_mul_left _ h3
        _ = (n + 2) ^ (d + 1) := by rw [pow_succ']

/-- Self-contained Sauer-Shelah lemma over a finite ground set `U`. -/
private lemma sauer_shelah {α : Type*} [DecidableEq α] :
    ∀ (U : Finset α) (ℱ : Finset (Finset α)),
      (∀ A ∈ ℱ, A ⊆ U) →
      ∀ d : ℕ, (∑ j ∈ Finset.range d, U.card.choose j) < ℱ.card →
        ∃ S ⊆ U, S.card = d ∧ ∀ T ⊆ S, ∃ A ∈ ℱ, A ∩ S = T := by
  intro U
  induction U using Finset.induction_on with
  | empty =>
    intro ℱ hℱ d hcard
    cases d with
    | zero =>
      obtain ⟨A, hA⟩ := Finset.card_pos.mp (by simpa using hcard)
      refine ⟨∅, Finset.Subset.refl _, rfl, fun T hT => ?_⟩
      refine ⟨A, hA, ?_⟩
      rw [Finset.subset_empty.mp hT, Finset.inter_empty]
    | succ d =>
      have hle : ℱ.card ≤ 1 := by
        have hsub : ℱ ⊆ {∅} := by
          intro A hA
          exact Finset.mem_singleton.mpr (Finset.subset_empty.mp (hℱ A hA))
        simpa using Finset.card_le_card hsub
      have hsum : 1 ≤ ∑ j ∈ Finset.range (d + 1), (∅ : Finset α).card.choose j := by
        rw [Finset.sum_range_succ']
        simp
      omega
  | @insert x U' hx ih =>
    intro ℱ hℱ d hcard
    cases d with
    | zero =>
      obtain ⟨A, hA⟩ := Finset.card_pos.mp (by simpa using hcard)
      refine ⟨∅, Finset.empty_subset _, rfl, fun T hT => ?_⟩
      refine ⟨A, hA, ?_⟩
      rw [Finset.subset_empty.mp hT, Finset.inter_empty]
    | succ d =>
      let ℱ_in := ℱ.filter (fun A => x ∈ A)
      let ℱ_out := ℱ.filter (fun A => x ∉ A)
      let G_in := ℱ_in.image (fun A => A.erase x)
      let G_out := ℱ_out
      let ℱ₀ := G_in ∪ G_out
      let ℱ₁ := G_in ∩ G_out
      have hsplit : ℱ_in.card + ℱ_out.card = ℱ.card :=
        Finset.card_filter_add_card_filter_not (fun A => x ∈ A)
      have hGin_card : G_in.card = ℱ_in.card := by
        refine Finset.card_image_of_injOn ?_
        intro A hA B hB heq
        dsimp only at heq
        have hxA : x ∈ A := (Finset.mem_filter.mp hA).2
        have hxB : x ∈ B := (Finset.mem_filter.mp hB).2
        rw [← Finset.insert_erase hxA, ← Finset.insert_erase hxB, heq]
      have hcard_sum : ℱ₀.card + ℱ₁.card = ℱ.card := by
        change (G_in ∪ G_out).card + (G_in ∩ G_out).card = ℱ.card
        rw [Finset.card_union_add_card_inter, hGin_card]
        exact hsplit
      have hG_in_sub : ∀ B ∈ G_in, B ⊆ U' := by
        intro B hB
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
        intro y hy
        obtain ⟨hne, hyA⟩ := Finset.mem_erase.mp hy
        rcases Finset.mem_insert.mp (hℱ A (Finset.mem_filter.mp hA).1 hyA) with rfl | hyU
        · exact absurd rfl hne
        · exact hyU
      have hG_out_sub : ∀ B ∈ G_out, B ⊆ U' := by
        intro B hB
        obtain ⟨hBℱ, hxB⟩ := Finset.mem_filter.mp hB
        intro y hy
        rcases Finset.mem_insert.mp (hℱ B hBℱ hy) with rfl | hyU
        · exact absurd hy hxB
        · exact hyU
      have hℱ₀_sub : ∀ B ∈ ℱ₀, B ⊆ U' := by
        intro B hB
        rcases Finset.mem_union.mp hB with h | h
        · exact hG_in_sub B h
        · exact hG_out_sub B h
      have hℱ₁_sub : ∀ B ∈ ℱ₁, B ⊆ U' := fun B hB =>
        hG_out_sub B (Finset.mem_inter.mp hB).2
      rw [Finset.card_insert_of_notMem hx, sum_choose_succ] at hcard
      by_cases h0 : (∑ j ∈ Finset.range (d + 1), U'.card.choose j) < ℱ₀.card
      · obtain ⟨S, hSU, hScard, hSshat⟩ := ih ℱ₀ hℱ₀_sub (d + 1) h0
        refine ⟨S, hSU.trans (Finset.subset_insert x U'), hScard, fun T hT => ?_⟩
        obtain ⟨B, hB, hBT⟩ := hSshat T hT
        have hxS : x ∉ S := fun hxS => hx (hSU hxS)
        rcases Finset.mem_union.mp hB with hBin | hBout
        · obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hBin
          refine ⟨A, (Finset.mem_filter.mp hA).1, ?_⟩
          rw [← hBT]
          ext y
          simp only [Finset.mem_inter, Finset.mem_erase]
          constructor
          · intro ⟨hyA, hyS⟩
            exact ⟨⟨fun hxy => hxS (hxy ▸ hyS), hyA⟩, hyS⟩
          · intro ⟨⟨_, hyA⟩, hyS⟩
            exact ⟨hyA, hyS⟩
        · exact ⟨B, (Finset.mem_filter.mp hBout).1, hBT⟩
      · have h1 : (∑ j ∈ Finset.range d, U'.card.choose j) < ℱ₁.card := by omega
        obtain ⟨S', hS'U, hS'card, hS'shat⟩ := ih ℱ₁ hℱ₁_sub d h1
        have hxS' : x ∉ S' := fun hxS' => hx (hS'U hxS')
        refine ⟨insert x S', Finset.insert_subset_insert x hS'U,
          by rw [Finset.card_insert_of_notMem hxS', hS'card], fun T hT => ?_⟩
        have hTe : T.erase x ⊆ S' := by
          intro y hy
          obtain ⟨hne, hyT⟩ := Finset.mem_erase.mp hy
          rcases Finset.mem_insert.mp (hT hyT) with rfl | hyS'
          · exact absurd rfl hne
          · exact hyS'
        obtain ⟨B, hB, hBT⟩ := hS'shat (T.erase x) hTe
        obtain ⟨hBin, hBout⟩ := Finset.mem_inter.mp hB
        have hBℱ : B ∈ ℱ := (Finset.mem_filter.mp hBout).1
        have hxB : x ∉ B := (Finset.mem_filter.mp hBout).2
        by_cases hxT : x ∈ T
        · obtain ⟨A, hA, hAB⟩ := Finset.mem_image.mp hBin
          have hxA : x ∈ A := (Finset.mem_filter.mp hA).2
          have hAeq : A = insert x B := by rw [← hAB, Finset.insert_erase hxA]
          refine ⟨A, (Finset.mem_filter.mp hA).1, ?_⟩
          have hins : insert x B ∩ insert x S' = insert x (B ∩ S') := by
            ext y
            simp [or_and_left]
          rw [hAeq, hins, hBT, Finset.insert_erase hxT]
        · refine ⟨B, hBℱ, ?_⟩
          have hTeq : T.erase x = T := Finset.erase_eq_of_notMem hxT
          rw [hTeq] at hBT
          rw [← hBT]
          ext y
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨hyB, rfl | hyS'⟩
            · exact absurd hyB hxB
            · exact ⟨hyB, hyS'⟩
          · rintro ⟨hyB, hyS'⟩
            exact ⟨hyB, Or.inr hyS'⟩

/-- Nonempty union-cube generated by a `d`-tuple of subsets of `Fin n`. -/
private def cube {n d : ℕ} (f : Fin d → Finset (Fin n)) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin d)).powerset.erase ∅).image (fun I => I.biUnion f)

/-- A shattered `d`-set inside a union-closed family yields a union-cube of size `2 ^ d - 1`. -/
private lemma exists_cube_of_shattered {n d : ℕ} {ℱ : Finset (Finset (Fin n))}
    (hsup : SupClosed (ℱ : Set (Finset (Fin n)))) {S : Finset (Fin n)}
    (hScard : S.card = d) (hshat : ∀ T ⊆ S, ∃ A ∈ ℱ, A ∩ S = T) :
    ∃ f : Fin d → Finset (Fin n), cube f ⊆ ℱ ∧ (cube f).card = 2 ^ d - 1 := by
  classical
  let e : Fin d ≃ S := (S.equivFinOfCardEq hScard).symm
  have hex : ∀ i : Fin d, ∃ A ∈ ℱ, A ∩ S = {(e i).1} := fun i =>
    hshat {(e i).1} (Finset.singleton_subset_iff.mpr (e i).2)
  choose f hf_mem hf_inter using hex
  refine ⟨f, ?_, ?_⟩
  · intro X hX
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hX
    have hIne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hI).1
    clear hX hI
    induction I using Finset.induction_on with
    | empty => exact absurd hIne Finset.not_nonempty_empty
    | @insert i I' hi ih =>
      rw [Finset.biUnion_insert]
      rcases I'.eq_empty_or_nonempty with rfl | hI'
      · simpa using hf_mem i
      · exact hsup (hf_mem i) (ih hI')
  · have hU_inter : ∀ I : Finset (Fin d), I.biUnion f ∩ S = I.image (fun i => (e i).1) := by
      intro I
      ext y
      simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨⟨i, hiI, hyf⟩, hyS⟩
        have hy : y ∈ f i ∩ S := Finset.mem_inter.mpr ⟨hyf, hyS⟩
        rw [hf_inter i, Finset.mem_singleton] at hy
        exact ⟨i, hiI, hy.symm⟩
      · rintro ⟨i, hiI, rfl⟩
        have hy : (e i).1 ∈ f i ∩ S := by rw [hf_inter i]; exact Finset.mem_singleton_self _
        obtain ⟨hyf, hyS⟩ := Finset.mem_inter.mp hy
        exact ⟨⟨i, hiI, hyf⟩, hyS⟩
    have hinj : Function.Injective (fun I : Finset (Fin d) => I.biUnion f) := by
      intro I₁ I₂ h
      dsimp only at h
      have h1 : I₁.image (fun i => (e i).1) = I₂.image (fun i => (e i).1) := by
        rw [← hU_inter I₁, ← hU_inter I₂, h]
      ext i
      have he_inj : Function.Injective (fun j : Fin d => (e j).1) :=
        Subtype.val_injective.comp e.injective
      constructor
      · intro hi
        have : (e i).1 ∈ I₂.image (fun j => (e j).1) := h1 ▸ Finset.mem_image_of_mem _ hi
        obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp this
        exact he_inj heq ▸ hj
      · intro hi
        have : (e i).1 ∈ I₁.image (fun j => (e j).1) := h1.symm ▸ Finset.mem_image_of_mem _ hi
        obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp this
        exact he_inj heq ▸ hj
    rw [cube, Finset.card_image_of_injective _ hinj,
      Finset.card_erase_of_mem (Finset.empty_mem_powerset _),
      Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

/-- Count of colorings making a fixed family `G` monochromatic. -/
private lemma card_mono_colorings {n : ℕ} (G : Finset (Finset (Fin n))) :
    ({c : Finset (Fin n) → Bool | Erdos1183.IsMonochromatic c G}).ncard ≤
      2 * 2 ^ (2 ^ n - G.card) := by
  have hconst : ∀ b : Bool,
      ({c : Finset (Fin n) → Bool | ∀ A ∈ G, c A = b}).ncard = 2 ^ (2 ^ n - G.card) := by
    intro b
    let e : {c : Finset (Fin n) → Bool // ∀ A ∈ G, c A = b} ≃
        ({A : Finset (Fin n) // A ∉ G} → Bool) :=
      { toFun := fun c A => c.1 A.1
        invFun := fun g => ⟨fun A => if h : A ∈ G then b else g ⟨A, h⟩, fun A hA => by simp [hA]⟩
        left_inv := fun c => by
          apply Subtype.ext
          funext A
          by_cases hA : A ∈ G
          · simp [hA, c.2 A hA]
          · simp [hA]
        right_inv := fun g => by
          funext ⟨A, hA⟩
          simp [hA] }
    have hcard_compl : Nat.card {A : Finset (Fin n) // A ∉ G} = 2 ^ n - G.card := by
      let eG : {A : Finset (Fin n) // A ∉ G} ≃ (Gᶜ : Finset (Finset (Fin n))) :=
        { toFun := fun A => ⟨A.1, Finset.mem_compl.mpr A.2⟩
          invFun := fun A => ⟨A.1, Finset.mem_compl.mp A.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr eG, Nat.card_eq_fintype_card, Fintype.card_coe]
      have hadd := Finset.card_compl_add_card G
      have huniv : Fintype.card (Finset (Fin n)) = 2 ^ n := by
        rw [Fintype.card_finset, Fintype.card_fin]
      rw [huniv] at hadd
      omega
    rw [← Nat.card_coe_set_eq]
    change Nat.card {c : Finset (Fin n) → Bool // ∀ A ∈ G, c A = b} = 2 ^ (2 ^ n - G.card)
    rw [Nat.card_congr e, Nat.card_fun, hcard_compl, Nat.card_eq_fintype_card, Fintype.card_bool]
  have hsub : {c : Finset (Fin n) → Bool | Erdos1183.IsMonochromatic c G} ⊆
      {c | ∀ A ∈ G, c A = true} ∪ {c | ∀ A ∈ G, c A = false} := by
    rintro c ⟨b, hb⟩
    cases b
    · exact Or.inr hb
    · exact Or.inl hb
  calc
    ({c : Finset (Fin n) → Bool | Erdos1183.IsMonochromatic c G}).ncard
        ≤ ({c : Finset (Fin n) → Bool | ∀ A ∈ G, c A = true} ∪
            {c : Finset (Fin n) → Bool | ∀ A ∈ G, c A = false}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({c : Finset (Fin n) → Bool | ∀ A ∈ G, c A = true}).ncard +
          ({c : Finset (Fin n) → Bool | ∀ A ∈ G, c A = false}).ncard :=
          Set.ncard_union_le _ _
    _ = 2 * 2 ^ (2 ^ n - G.card) := by rw [hconst true, hconst false, two_mul]

private lemma ncard_biUnion_le {α β : Type*} [DecidableEq α] (s : Finset α) (f : α → Set β) :
    (⋃ a ∈ s, f a).ncard ≤ ∑ a ∈ s, (f a).ncard := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert has]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- First-moment upper bound on `Erdos1183.F n`. -/
private lemma F_le_pow {n d : ℕ} (hdn : d ≤ n) (hsmall : n * d + 2 < 2 ^ d) :
    Erdos1183.F n ≤ (n + 1) ^ d := by
  let GoodF : Finset (Fin d → Finset (Fin n)) :=
    Finset.univ.filter (fun f => (cube f).card = 2 ^ d - 1)
  let BadCol : Set (Finset (Fin n) → Bool) :=
    ⋃ f ∈ GoodF, {c | Erdos1183.IsMonochromatic c (cube f)}
  have h2d_le : 2 ^ d - 1 ≤ 2 ^ n := by
    have : 2 ^ d ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hdn
    omega
  have hexp_lt : n * d + 1 + (2 ^ n - (2 ^ d - 1)) < 2 ^ n := by
    have h2d_pos : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
    omega
  have hBad_lt : BadCol.ncard < (Set.univ : Set (Finset (Fin n) → Bool)).ncard := by
    have hcardF : Fintype.card (Fin d → Finset (Fin n)) = 2 ^ (n * d) := by
      rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    have hcardC : (Set.univ : Set (Finset (Fin n) → Bool)).ncard = 2 ^ (2 ^ n) := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_finset, Fintype.card_fin]
    rw [hcardC]
    calc
      BadCol.ncard
          ≤ ∑ f ∈ GoodF, ({c : Finset (Fin n) → Bool | Erdos1183.IsMonochromatic c (cube f)}).ncard :=
            ncard_biUnion_le GoodF _
      _ ≤ ∑ _f ∈ GoodF, 2 * 2 ^ (2 ^ n - (2 ^ d - 1)) := by
            apply Finset.sum_le_sum
            intro f hf
            have hcf : (cube f).card = 2 ^ d - 1 := (Finset.mem_filter.mp hf).2
            simpa [hcf] using card_mono_colorings (cube f)
      _ = GoodF.card * (2 * 2 ^ (2 ^ n - (2 ^ d - 1))) := by simp
      _ ≤ 2 ^ (n * d) * (2 * 2 ^ (2 ^ n - (2 ^ d - 1))) := by
            apply Nat.mul_le_mul_right
            calc
              GoodF.card ≤ (Finset.univ : Finset (Fin d → Finset (Fin n))).card :=
                Finset.card_le_univ _
              _ = 2 ^ (n * d) := by rw [Finset.card_univ, hcardF]
      _ = 2 ^ (n * d + 1 + (2 ^ n - (2 ^ d - 1))) := by
            rw [← mul_assoc, ← pow_succ, ← pow_add]
      _ < 2 ^ (2 ^ n) := Nat.pow_lt_pow_right (by decide) hexp_lt
  have hgood_ex : ∃ c₀ : Finset (Fin n) → Bool, c₀ ∉ BadCol := by
    by_contra hall
    have huniv : BadCol = Set.univ := by
      ext c
      simp only [Set.mem_univ, iff_true]
      by_contra hc
      exact hall ⟨c, hc⟩
    rw [huniv] at hBad_lt
    exact lt_irrefl _ hBad_lt
  obtain ⟨c₀, hc₀_not_bad⟩ := hgood_ex
  have hF_le_sum : Erdos1183.F n ≤ ∑ j ∈ Finset.range d, n.choose j := by
    unfold Erdos1183.F
    apply csSup_le
    · refine ⟨0, fun c => ⟨∅, le_rfl, ⟨true, by simp⟩, fun _ ha => by simp at ha⟩⟩
    · intro m hm
      obtain ⟨ℱ, hmℱ, hmono, hsup⟩ := hm c₀
      by_contra hgt
      have hlt : ∑ j ∈ Finset.range d, (Finset.univ : Finset (Fin n)).card.choose j < ℱ.card := by
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨S, -, hScard, hSshat⟩ := sauer_shelah Finset.univ ℱ (fun _ _ => Finset.subset_univ _) d hlt
      obtain ⟨f, hf_sub, hf_card⟩ := exists_cube_of_shattered hsup hScard hSshat
      have hmono_f : Erdos1183.IsMonochromatic c₀ (cube f) := by
        obtain ⟨b, hb⟩ := hmono
        exact ⟨b, fun A hA => hb A (hf_sub hA)⟩
      exact hc₀_not_bad (Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf_card⟩) hmono_f)
  exact hF_le_sum.trans (sum_choose_le_pow n d)

private lemma cube_le_two_pow {L : ℕ} (hL : 10 ≤ L) : L ^ 3 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : (k + 1) ^ 3 ≤ 2 * k ^ 3 := by
      have hk2 : 10 * k ^ 2 ≤ k ^ 3 := by
        have := Nat.mul_le_mul_right (k ^ 2) hk
        linarith [show k * k ^ 2 = k ^ 3 by ring]
      have hk1 : 10 * k ≤ k ^ 2 := by
        have := Nat.mul_le_mul_right k hk
        linarith [show k * k = k ^ 2 by ring]
      nlinarith
    calc
      (k + 1) ^ 3 ≤ 2 * k ^ 3 := h1
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [pow_succ']

theorem main_H2 :
    ∀ ε : ℝ, 0 < ε →
      Filter.Eventually (fun n : ℕ => (Erdos1183.F n : ℝ) < (1 + ε) ^ n) Filter.atTop := by
  intro ε hε
  let M : ℕ := Nat.ceil (1 / ε) + 1
  have hMpos : 0 < M := Nat.succ_pos _
  have hMε : (1 : ℝ) ≤ (M : ℝ) * ε := by
    have h1 : 1 / ε ≤ (Nat.ceil (1 / ε) : ℝ) := Nat.le_ceil (1 / ε)
    have h2 : (1 : ℝ) ≤ (Nat.ceil (1 / ε) : ℝ) * ε := (div_le_iff₀ hε).mp h1
    have h3 : (Nat.ceil (1 / ε) : ℝ) ≤ (M : ℝ) := by
      dsimp [M]
      push_cast
      linarith
    nlinarith
  have h2_le_pow : (2 : ℝ) ≤ (1 + ε) ^ M := by
    have hbern := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ ε) M
    linarith
  let L₀ : ℕ := max 10 (13 * M)
  refine Filter.eventually_atTop.mpr ⟨2 ^ L₀, fun n hn => ?_⟩
  let L : ℕ := Nat.log 2 n
  have hL0 : L₀ ≤ L := Nat.le_log_of_pow_le (by decide) hn
  have hL10 : 10 ≤ L := le_trans (le_max_left _ _) hL0
  have hLM : 13 * M ≤ L := le_trans (le_max_right _ _) hL0
  have hn_pos : 0 < n := lt_of_lt_of_le (Nat.pow_pos (by decide)) hn
  have hpowL : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn_pos.ne'
  have hn_lt : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hL3 : L ^ 3 ≤ 2 ^ L := cube_le_two_pow hL10
  let d : ℕ := 2 * L + 4
  have hL2_ge : 10 * L ≤ L ^ 2 := by nlinarith
  have hL3_ge : 10 * L ^ 2 ≤ L ^ 3 := by
    have := Nat.mul_le_mul_right (L ^ 2) hL10
    linarith [show L * L ^ 2 = L ^ 3 by ring]
  have hd_lt_L3 : d < L ^ 3 := by dsimp [d]; nlinarith
  have hdn : d ≤ n := by omega
  have hsmall : n * d + 2 < 2 ^ d := by
    have hd_lt : d < 2 ^ (L + 1) := by
      have : 2 ^ L < 2 ^ (L + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self L)
      omega
    have hmul : n * d < 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_lt_mul'' hn_lt hd_lt
    have h4 : 2 ^ d = 4 * (2 ^ (L + 1) * 2 ^ (L + 1)) := by
      dsimp [d]
      rw [← pow_add, show (L + 1) + (L + 1) = 2 * L + 2 by omega,
        show 2 * L + 4 = (2 * L + 2) + 2 by omega, pow_add]
      ring
    have hpos : 1 ≤ 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.one_le_pow _ 2 (by decide) |> fun h =>
      Nat.mul_le_mul h h
    omega
  have hF : Erdos1183.F n ≤ (n + 1) ^ d := F_le_pow hdn hsmall
  have hquad : M * ((L + 1) * d + 1) ≤ n := by
    have h1 : (L + 1) * d + 1 ≤ 13 * L ^ 2 := by
      dsimp [d]
      nlinarith
    have h2 : M * ((L + 1) * d + 1) ≤ (13 * M) * L ^ 2 := by
      calc
        M * ((L + 1) * d + 1) ≤ M * (13 * L ^ 2) := Nat.mul_le_mul_left M h1
        _ = (13 * M) * L ^ 2 := by ring
    have h3 : (13 * M) * L ^ 2 ≤ L ^ 3 := by
      calc
        (13 * M) * L ^ 2 ≤ L * L ^ 2 := Nat.mul_le_mul_right (L ^ 2) hLM
        _ = L ^ 3 := by ring
    omega
  have hexp : (L + 1) * d < n / M := by
    have hquad' : ((L + 1) * d + 1) * M ≤ n := by rw [mul_comm]; exact hquad
    have hdiv : (L + 1) * d + 1 ≤ n / M := (Nat.le_div_iff_mul_le hMpos).mpr hquad'
    omega
  have hnat_lt : Erdos1183.F n < 2 ^ (n / M) := by
    calc
      Erdos1183.F n ≤ (n + 1) ^ d := hF
      _ ≤ (2 ^ (L + 1)) ^ d := Nat.pow_le_pow_left (by omega) d
      _ = 2 ^ ((L + 1) * d) := by rw [← pow_mul]
      _ < 2 ^ (n / M) := Nat.pow_lt_pow_right (by decide) hexp
  have hreal_lt : (Erdos1183.F n : ℝ) < (2 : ℝ) ^ (n / M) := by exact_mod_cast hnat_lt
  have hreal_le : (2 : ℝ) ^ (n / M) ≤ (1 + ε) ^ n := by
    calc
      (2 : ℝ) ^ (n / M) ≤ ((1 + ε) ^ M) ^ (n / M) :=
        pow_le_pow_left₀ (by norm_num) h2_le_pow (n / M)
      _ = (1 + ε) ^ (M * (n / M)) := by rw [← pow_mul]
      _ ≤ (1 + ε) ^ n := pow_le_pow_right₀ (by linarith) (Nat.mul_div_le n M)
  linarith

end Erdos1183H2

theorem OMA.solution : OMA.R_Erdos1183_erdos_1183_parts_iii_R1.H2 := by
  exact Erdos1183H2.main_H2
