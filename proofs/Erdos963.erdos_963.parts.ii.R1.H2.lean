import OMAReductions.R_Erdos963_erdos_963_parts_ii_R1

/-!
Proof of `OMA.R_Erdos963_erdos_963_parts_ii_R1.H2` (affine extraction and common triple subsums
for finite subsets of `ℤ`).

We establish the three parts of `H2`:
1. Existence of affine-dissociated subsets of size `4` (from `≥ 5`), `5` (from `≥ 8`),
   and `6` (from `≥ 14`), via 2-adic splitting, an explicit pair analysis for `4 + 4`,
   a self-contained classification of 7-element sets without affine 5-subsets, and an
   explicit `3 + 3` construction for two such 7-element classes.
2. Existence of two affine-dissociated subsets of size `4` (from `≥ 5`) and `5` (from `≥ 9`)
   with distinct sums.
3. Upper bounds on common triple sums across all affine 4-subsets (`≤ 3` for `|X| ≥ 5`,
   and `≤ 2` for `|X| ≥ 6` via double counting and an injection into `Y` minus its top two elements).
-/

open Finset

namespace Erdos963H2

private def Aff (M : Finset ℤ) : Prop :=
  ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S

private def Triples (M : Finset ℤ) : Finset ℤ :=
  (M.powersetCard 3).image (fun S ↦ S.sum id)

/- Section 1: Basic properties of `Aff` and sorted tuples -/

private lemma aff_of_card_le_three {M : Finset ℤ} (hM : M.card ≤ 3) : Aff M := by
  intro T hT S hS hdisj hc hsum
  have hle : T.card + S.card ≤ M.card := by
    rw [← card_union_of_disjoint hdisj]
    exact card_le_card (union_subset hT hS)
  by_cases h0 : T.card = 0
  · rw [card_eq_zero.mp h0, card_eq_zero.mp (by omega : S.card = 0)]
  · have h1 : T.card = 1 := by omega
    obtain ⟨x, rfl⟩ := card_eq_one.mp h1
    obtain ⟨y, rfl⟩ := card_eq_one.mp (by omega : S.card = 1)
    simp only [sum_singleton, id_eq] at hsum
    rw [hsum]

private lemma aff_neg {M : Finset ℤ} (hM : Aff M) : Aff (M.image Neg.neg) := by
  intro T hT S hS hdisj hc hsum
  have hinj : Function.Injective (Neg.neg : ℤ → ℤ) := neg_injective
  let T' := T.image Neg.neg
  let S' := S.image Neg.neg
  have hT' : T' ⊆ M := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp (hT hy)
    simpa using hz
  have hS' : S' ⊆ M := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp (hS hy)
    simpa using hz
  have hd' : Disjoint T' S' := by
    rw [disjoint_left]
    intro x hxT hxS
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hxT
    obtain ⟨z, hz, hzy⟩ := mem_image.mp hxS
    have : y = z := neg_injective hzy.symm
    exact disjoint_left.mp hdisj hy (this ▸ hz)
  have hc' : T'.card = S'.card := by
    simp only [T', S', card_image_of_injective _ hinj, hc]
  have hs' : T'.sum id = S'.sum id := by
    simp only [T', S', sum_image (fun _ _ _ _ h ↦ hinj h), id_eq]
    have h1 : (∑ x ∈ T, -x) = -(∑ x ∈ T, x) := sum_neg_distrib (f := fun x : ℤ ↦ x)
    have h2 : (∑ x ∈ S, -x) = -(∑ x ∈ S, x) := sum_neg_distrib (f := fun x : ℤ ↦ x)
    change (∑ x ∈ T, x) = (∑ x ∈ S, x) at hsum
    omega
  have heq := hM T' hT' S' hS' hd' hc' hs'
  ext x
  have : -x ∈ T' ↔ -x ∈ S' := by rw [heq]
  simp only [T', S', mem_image] at this
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := this.mp ⟨x, hx, rfl⟩
    exact (neg_injective hyx) ▸ hy
  · intro hx
    obtain ⟨y, hy, hyx⟩ := this.mpr ⟨x, hx, rfl⟩
    exact (neg_injective hyx) ▸ hy

private lemma aff_four_iff {a b c d : ℤ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    Aff ({a, b, c, d} : Finset ℤ) ↔ a + d ≠ b + c := by
  constructor
  · intro haff heq
    have hdisj : Disjoint ({a, d} : Finset ℤ) ({b, c} : Finset ℤ) := by
      rw [disjoint_left]
      intro x hx1 hx2
      simp only [mem_insert, mem_singleton] at hx1 hx2
      omega
    have hT : ({a, d} : Finset ℤ) ⊆ {a, b, c, d} := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
    have hS : ({b, c} : Finset ℤ) ⊆ {a, b, c, d} := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
    have hc : ({a, d} : Finset ℤ).card = ({b, c} : Finset ℤ).card := by
      rw [card_pair (by omega), card_pair (by omega)]
    have hs : ({a, d} : Finset ℤ).sum id = ({b, c} : Finset ℤ).sum id := by
      rw [sum_pair (by omega), sum_pair (by omega)]
      simpa using heq
    have hEq := haff _ hT _ hS hdisj hc hs
    have ha : a ∈ ({b, c} : Finset ℤ) := hEq ▸ (by simp)
    simp only [mem_insert, mem_singleton] at ha
    omega
  · intro hne T hT S hS hdisj hc hsum
    have hMcard : ({a, b, c, d} : Finset ℤ).card = 4 := by
      simp [show a ≠ b by omega, show a ≠ c by omega, show a ≠ d by omega,
        show b ≠ c by omega, show b ≠ d by omega, show c ≠ d by omega]
    have hle : T.card + S.card ≤ 4 := by
      rw [← card_union_of_disjoint hdisj, ← hMcard]
      exact card_le_card (union_subset hT hS)
    by_cases h0 : T.card = 0
    · rw [card_eq_zero.mp h0, card_eq_zero.mp (by omega : S.card = 0)]
    by_cases h1 : T.card = 1
    · obtain ⟨x, rfl⟩ := card_eq_one.mp h1
      obtain ⟨y, rfl⟩ := card_eq_one.mp (by omega : S.card = 1)
      simp only [sum_singleton, id_eq] at hsum
      rw [hsum]
    · have h2T : T.card = 2 := by omega
      have h2S : S.card = 2 := by omega
      obtain ⟨x₁, x₂, hxne, rfl⟩ := card_eq_two.mp h2T
      obtain ⟨y₁, y₂, hyne, rfl⟩ := card_eq_two.mp h2S
      have hx₁ : x₁ ∈ ({a, b, c, d} : Finset ℤ) := hT (by simp)
      have hx₂ : x₂ ∈ ({a, b, c, d} : Finset ℤ) := hT (by simp)
      have hy₁ : y₁ ∈ ({a, b, c, d} : Finset ℤ) := hS (by simp)
      have hy₂ : y₂ ∈ ({a, b, c, d} : Finset ℤ) := hS (by simp)
      have hd11 : x₁ ≠ y₁ := fun h ↦ by subst h; exact (disjoint_left.mp hdisj) (by simp : x₁ ∈ ({x₁, x₂} : Finset ℤ)) (by simp)
      have hd12 : x₁ ≠ y₂ := fun h ↦ by subst h; exact (disjoint_left.mp hdisj) (by simp : x₁ ∈ ({x₁, x₂} : Finset ℤ)) (by simp)
      have hd21 : x₂ ≠ y₁ := fun h ↦ by subst h; exact (disjoint_left.mp hdisj) (by simp : x₂ ∈ ({x₁, x₂} : Finset ℤ)) (by simp)
      have hd22 : x₂ ≠ y₂ := fun h ↦ by subst h; exact (disjoint_left.mp hdisj) (by simp : x₂ ∈ ({x₁, x₂} : Finset ℤ)) (by simp)
      rw [sum_pair hxne, sum_pair hyne] at hsum
      simp only [id_eq] at hsum
      simp only [mem_insert, mem_singleton] at hx₁ hx₂ hy₁ hy₂
      exfalso
      rcases hx₁ with rfl | rfl | rfl | rfl <;>
        rcases hx₂ with rfl | rfl | rfl | rfl <;>
        rcases hy₁ with rfl | rfl | rfl | rfl <;>
        rcases hy₂ with rfl | rfl | rfl | rfl <;>
        omega

private lemma sorted_list_strict {M : Finset ℤ} :
    (M.sort (· ≤ ·)).length = M.card ∧
    (M.sort (· ≤ ·)).Pairwise (· < ·) ∧
    ∀ x, x ∈ M.sort (· ≤ ·) ↔ x ∈ M := by
  refine ⟨length_sort (· ≤ ·), ?_, fun x ↦ mem_sort (· ≤ ·)⟩
  have hp := pairwise_sort M (· ≤ ·)
  have hnd := sort_nodup M (· ≤ ·)
  exact (hp.and hnd).imp (fun h ↦ lt_of_le_of_ne h.1 h.2)

private lemma finset_card_three_sorted {M : Finset ℤ} (hM : M.card = 3) :
    ∃ a b c : ℤ, a < b ∧ b < c ∧ M = {a, b, c} := by
  obtain ⟨hlen, hp, hmem⟩ := sorted_list_strict (M := M)
  rw [hM] at hlen
  match hl : M.sort (· ≤ ·) with
  | [a, b, c] =>
    rw [hl] at hp hmem
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true] at hp
    refine ⟨a, b, c, hp.1.1, hp.2.1, ?_⟩
    ext x
    rw [← hmem]
    simp [List.mem_cons]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ =>
    rw [hl] at hlen; simp at hlen

private lemma finset_card_four_sorted {M : Finset ℤ} (hM : M.card = 4) :
    ∃ a b c d : ℤ, a < b ∧ b < c ∧ c < d ∧ M = {a, b, c, d} := by
  obtain ⟨hlen, hp, hmem⟩ := sorted_list_strict (M := M)
  rw [hM] at hlen
  match hl : M.sort (· ≤ ·) with
  | [a, b, c, d] =>
    rw [hl] at hp hmem
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true] at hp
    refine ⟨a, b, c, d, hp.1.1, hp.2.1.1, hp.2.2.1, ?_⟩
    ext x
    rw [← hmem]
    simp [List.mem_cons]
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ =>
    rw [hl] at hlen; simp at hlen

private lemma finset_card_five_sorted {M : Finset ℤ} (hM : M.card = 5) :
    ∃ a b c d e : ℤ, a < b ∧ b < c ∧ c < d ∧ d < e ∧ M = {a, b, c, d, e} := by
  obtain ⟨hlen, hp, hmem⟩ := sorted_list_strict (M := M)
  rw [hM] at hlen
  match hl : M.sort (· ≤ ·) with
  | [a, b, c, d, e] =>
    rw [hl] at hp hmem
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true] at hp
    refine ⟨a, b, c, d, e, hp.1.1, hp.2.1.1, hp.2.2.1.1, hp.2.2.2.1, ?_⟩
    ext x
    rw [← hmem]
    simp [List.mem_cons]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ =>
    rw [hl] at hlen; simp at hlen

/- Section 2: 2-adic splitting and parity lemmas -/

private lemma mod_two_split {x r q : ℤ} (h : x ≡ r [ZMOD q]) :
    (x ≡ r [ZMOD 2 * q]) ∨ (x ≡ r + q [ZMOD 2 * q]) := by
  obtain ⟨k, hk⟩ := h.symm.dvd
  by_cases hk0 : k % 2 = 0
  · left
    refine Int.modEq_iff_dvd.mpr ⟨-(k / 2), ?_⟩
    have he : k = 2 * (k / 2) := by omega
    rw [show r - x = -(x - r) by ring, hk]
    nth_rw 1 [he]
    ring
  · right
    refine Int.modEq_iff_dvd.mpr ⟨-(k / 2), ?_⟩
    have he : k = 2 * (k / 2) + 1 := by omega
    rw [show r + q - x = q - (x - r) by ring, hk]
    nth_rw 1 [he]
    ring

private lemma two_adic_split {X : Finset ℤ} (hX : 2 ≤ X.card) :
    ∃ (X₀ X₁ : Finset ℤ) (q r : ℤ), 0 < q ∧ X₀ ⊆ X ∧ X₁ ⊆ X ∧ Disjoint X₀ X₁ ∧
      X₀ ∪ X₁ = X ∧ X₀.Nonempty ∧ X₁.Nonempty ∧ X₁.card ≤ X₀.card ∧
      (∀ x ∈ X₀, x ≡ r [ZMOD 2 * q]) ∧ (∀ x ∈ X₁, x ≡ r + q [ZMOD 2 * q]) := by
  classical
  obtain ⟨x₀, hx₀, x₁, hx₁, hne⟩ := one_lt_card.mp (show 1 < X.card by omega)
  let bad (m : ℕ) : Prop := ¬ (∀ x ∈ X, x ≡ x₀ [ZMOD (2 : ℤ) ^ m])
  have hex : ∃ m, bad m := by
    refine ⟨(x₀ - x₁).natAbs, ?_⟩
    intro hall
    have hd := (hall x₁ hx₁).dvd
    have hd' : (2 : ℕ) ^ (x₀ - x₁).natAbs ∣ (x₀ - x₁).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hd
    have hp : 0 < (x₀ - x₁).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
    have hle := Nat.le_of_dvd hp hd'
    have hlt : (x₀ - x₁).natAbs < 2 ^ (x₀ - x₁).natAbs := Nat.lt_two_pow_self
    omega
  let m := Nat.find hex
  have hm0 : 0 < m := by
    by_contra h
    have hm : m = 0 := by omega
    have hf : bad m := Nat.find_spec hex
    rw [hm] at hf
    exact hf (fun x _ ↦ by simp [Int.ModEq])
  let q : ℤ := (2 : ℤ) ^ (m - 1)
  have hq : 0 < q := by positivity
  have hXq : ∀ x ∈ X, x ≡ x₀ [ZMOD q] := by
    by_contra hh
    exact Nat.find_min hex (show m - 1 < m by omega) hh
  have hnot : ¬ (∀ x ∈ X, x ≡ x₀ [ZMOD 2 * q]) := by
    have hpow : 2 * q = (2 : ℤ) ^ m := by
      dsimp only [q]
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    exact Nat.find_spec hex
  let A := X.filter (fun x ↦ x ≡ x₀ [ZMOD 2 * q])
  let B := X.filter (fun x ↦ ¬ (x ≡ x₀ [ZMOD 2 * q]))
  have hA : A ⊆ X := filter_subset _ _
  have hB : B ⊆ X := filter_subset _ _
  have hdisj : Disjoint A B := disjoint_filter.mpr (fun _ _ h1 h2 ↦ h2 h1)
  have hunion : A ∪ B = X := filter_union_filter_not_eq _ _
  have hAne : A.Nonempty := ⟨x₀, mem_filter.mpr ⟨hx₀, Int.ModEq.refl _⟩⟩
  have hBne : B.Nonempty := by
    push Not at hnot
    obtain ⟨y, hyX, hyn⟩ := hnot
    exact ⟨y, mem_filter.mpr ⟨hyX, hyn⟩⟩
  have hAmod : ∀ x ∈ A, x ≡ x₀ [ZMOD 2 * q] := fun x hx ↦ (mem_filter.mp hx).2
  have hBmod : ∀ x ∈ B, x ≡ x₀ + q [ZMOD 2 * q] := fun x hx ↦
    (mod_two_split (hXq x (hB hx))).resolve_left (mem_filter.mp hx).2
  by_cases hle : B.card ≤ A.card
  · exact ⟨A, B, q, x₀, hq, hA, hB, hdisj, hunion, hAne, hBne, hle, hAmod, hBmod⟩
  · refine ⟨B, A, q, x₀ + q, hq, hB, hA, hdisj.symm, by rw [union_comm, hunion],
      hBne, hAne, by omega, hBmod, ?_⟩
    intro x hx
    exact (hAmod x hx).trans (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩)

private lemma subset_sum_congr {F T : Finset ℤ} (hT : T ⊆ F) {q r : ℤ}
    (hF : ∀ x ∈ F, x ≡ r [ZMOD q]) : T.sum id ≡ (T.card : ℤ) * r [ZMOD q] := by
  simpa using (Int.ModEq.sum (s := T) (f := id) (g := fun _ ↦ r)
    (fun x hx ↦ hF x (hT hx)))

private lemma split_parity {A B : Finset ℤ} {q r : ℤ} (hq : 0 < q)
    (hA : ∀ x ∈ A, x ≡ r [ZMOD 2 * q]) (hB : ∀ x ∈ B, x ≡ r + q [ZMOD 2 * q]) :
    Disjoint A B ∧
    ∀ T ⊆ A ∪ B, ∀ S ⊆ A ∪ B, T.card = S.card → T.sum id = S.sum id →
      (T ∩ B).card % 2 = (S ∩ B).card % 2 := by
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    intro x hxA hxB
    have h := (hA x hxA).symm.trans (hB x hxB)
    obtain ⟨k, hk⟩ := h.dvd
    have : q = 2 * q * k := by linarith
    have : 2 * k = 1 := mul_left_cancel₀ (ne_of_gt hq) (by linarith)
    omega
  refine ⟨hAB, ?_⟩
  have hdecomp : ∀ U ⊆ A ∪ B, U.sum id ≡ (U.card : ℤ) * r + ((U ∩ B).card : ℤ) * q [ZMOD 2 * q] := by
    intro U hU
    have he : (U ∩ A) ∪ (U ∩ B) = U := by
      ext z
      simp only [mem_union, mem_inter]
      constructor
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
      · intro hz
        rcases mem_union.mp (hU hz) with h1 | h1
        · exact Or.inl ⟨hz, h1⟩
        · exact Or.inr ⟨hz, h1⟩
    have hd : Disjoint (U ∩ A) (U ∩ B) := hAB.mono inter_subset_right inter_subset_right
    have hsumU : U.sum id = (U ∩ A).sum id + (U ∩ B).sum id := by
      rw [← sum_union hd, he]
    have hcardU : U.card = (U ∩ A).card + (U ∩ B).card := by
      rw [← card_union_of_disjoint hd, he]
    have h1 := subset_sum_congr (inter_subset_right : U ∩ A ⊆ A) hA
    have h2 := subset_sum_congr (inter_subset_right : U ∩ B ⊆ B) hB
    have h3 := h1.add h2
    rw [← hsumU] at h3
    convert h3 using 1
    rw [hcardU]
    push_cast
    ring
  intro T hT S hS hc hsum
  have h1 := (hdecomp T hT).symm.trans (hsum ▸ hdecomp S hS)
  rw [hc] at h1
  have h2 := Int.ModEq.add_left_cancel' ((S.card : ℤ) * r) h1
  obtain ⟨k, hk⟩ := h2.dvd
  have hmul : ((S ∩ B).card : ℤ) - ((T ∩ B).card : ℤ) = 2 * k := by
    apply mul_left_cancel₀ (ne_of_gt hq)
    linarith
  omega

private lemma aff_insert_of_split {F : Finset ℤ} {a q r : ℤ} (hq : 0 < q)
    (hF : ∀ x ∈ F, x ≡ r [ZMOD 2 * q]) (hA : a ≡ r + q [ZMOD 2 * q]) (haff : Aff F) :
    a ∉ F ∧ Aff (insert a F) := by
  have hB : ∀ x ∈ ({a} : Finset ℤ), x ≡ r + q [ZMOD 2 * q] := by
    intro x hx; rw [mem_singleton.mp hx]; exact hA
  obtain ⟨hdisj, hpar⟩ := split_parity hq hF hB
  have hna : a ∉ F := fun hm ↦ disjoint_left.mp hdisj hm (mem_singleton_self a)
  refine ⟨hna, ?_⟩
  intro T hT S hS hTS hc hsum
  have hU : insert a F = F ∪ {a} := by rw [union_comm, singleton_union]
  rw [hU] at hT hS
  have hp := hpar T hT S hS hc hsum
  have hle : (T ∩ {a}).card + (S ∩ {a}).card ≤ 1 := by
    rw [← card_union_of_disjoint (hTS.mono inter_subset_left inter_subset_left)]
    exact (card_le_card (union_subset inter_subset_right inter_subset_right)).trans (by simp)
  have hT0 : (T ∩ {a}).card = 0 := by omega
  have hS0 : (S ∩ {a}).card = 0 := by omega
  have hTa : a ∉ T := by
    intro hm
    have : a ∈ T ∩ {a} := mem_inter.mpr ⟨hm, mem_singleton_self a⟩
    rw [card_eq_zero.mp hT0] at this
    exact notMem_empty a this
  have hSa : a ∉ S := by
    intro hm
    have : a ∈ S ∩ {a} := mem_inter.mpr ⟨hm, mem_singleton_self a⟩
    rw [card_eq_zero.mp hS0] at this
    exact notMem_empty a this
  have hT' : T ⊆ F := fun x hx ↦
    (mem_union.mp (hT hx)).resolve_right (fun h ↦ hTa (mem_singleton.mp h ▸ hx))
  have hS' : S ⊆ F := fun x hx ↦
    (mem_union.mp (hS hx)).resolve_right (fun h ↦ hSa (mem_singleton.mp h ▸ hx))
  exact haff T hT' S hS' hTS hc hsum

private lemma aff_union_of_split_le_three {T₀ T₁ : Finset ℤ} {q r : ℤ} (hq : 0 < q)
    (h0 : ∀ x ∈ T₀, x ≡ r [ZMOD 2 * q]) (h1 : ∀ y ∈ T₁, y ≡ r + q [ZMOD 2 * q])
    (hc0 : T₀.card ≤ 3) (hc1 : T₁.card ≤ 3)
    (hdiff : ∀ x ∈ T₀, ∀ x' ∈ T₀, x ≠ x' → ∀ y ∈ T₁, ∀ y' ∈ T₁, y ≠ y' → |x - x'| ≠ |y - y'|)
    (hsum : ∀ x ∈ T₀, ∀ x' ∈ T₀, x ≠ x' → ∀ y ∈ T₁, ∀ y' ∈ T₁, y ≠ y' → x + x' ≠ y + y') :
    Disjoint T₀ T₁ ∧ Aff (T₀ ∪ T₁) := by
  obtain ⟨hdisj, hpar⟩ := split_parity hq h0 h1
  refine ⟨hdisj, ?_⟩
  intro U hU V hV hUV hc hs
  have hp := hpar U hU V hV hc hs
  have hsplit : ∀ W ⊆ T₀ ∪ T₁, W.card = (W ∩ T₀).card + (W ∩ T₁).card ∧
      W.sum id = (W ∩ T₀).sum id + (W ∩ T₁).sum id := by
    intro W hW
    have he : (W ∩ T₀) ∪ (W ∩ T₁) = W := by
      ext z
      simp only [mem_union, mem_inter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hz
        rcases mem_union.mp (hW hz) with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
    have hd := hdisj.mono (inter_subset_right (s₁ := W)) (inter_subset_right (s₁ := W))
    exact ⟨by rw [← card_union_of_disjoint hd, he], by rw [← sum_union hd, he]⟩
  obtain ⟨hUc, hUs⟩ := hsplit U hU
  obtain ⟨hVc, hVs⟩ := hsplit V hV
  have hle0 : (U ∩ T₀).card + (V ∩ T₀).card ≤ T₀.card := by
    rw [← card_union_of_disjoint (hUV.mono inter_subset_left inter_subset_left)]
    exact card_le_card (union_subset inter_subset_right inter_subset_right)
  have hle1 : (U ∩ T₁).card + (V ∩ T₁).card ≤ T₁.card := by
    rw [← card_union_of_disjoint (hUV.mono inter_subset_left inter_subset_left)]
    exact card_le_card (union_subset inter_subset_right inter_subset_right)
  by_cases hcard0 : U.card = 0
  · rw [card_eq_zero.mp hcard0, card_eq_zero.mp (by omega : V.card = 0)]
  by_cases hcard1 : U.card = 1
  · obtain ⟨x, rfl⟩ := card_eq_one.mp hcard1
    obtain ⟨y, rfl⟩ := card_eq_one.mp (by omega : V.card = 1)
    simp only [sum_singleton, id_eq] at hs
    rw [hs]
  · have hcard2 : U.card = 2 := by omega
    exfalso
    by_cases hu1 : (U ∩ T₁).card = 1
    · have hv1 : (V ∩ T₁).card = 1 := by omega
      have hu0 : (U ∩ T₀).card = 1 := by omega
      have hv0 : (V ∩ T₀).card = 1 := by omega
      obtain ⟨x, hx⟩ := card_eq_one.mp hu0
      obtain ⟨x', hx'⟩ := card_eq_one.mp hv0
      obtain ⟨y, hy⟩ := card_eq_one.mp hu1
      obtain ⟨y', hy'⟩ := card_eq_one.mp hv1
      have hxU : x ∈ U ∩ T₀ := hx ▸ mem_singleton_self x
      have hx'V : x' ∈ V ∩ T₀ := hx' ▸ mem_singleton_self x'
      have hyU : y ∈ U ∩ T₁ := hy ▸ mem_singleton_self y
      have hy'V : y' ∈ V ∩ T₁ := hy' ▸ mem_singleton_self y'
      have hxx' : x ≠ x' := fun h ↦
        disjoint_left.mp hUV (mem_inter.mp hxU).1 (h ▸ (mem_inter.mp hx'V).1)
      have hyy' : y ≠ y' := fun h ↦
        disjoint_left.mp hUV (mem_inter.mp hyU).1 (h ▸ (mem_inter.mp hy'V).1)
      rw [hx, hy] at hUs
      rw [hx', hy'] at hVs
      simp only [sum_singleton, id_eq] at hUs hVs hs
      have heq : x - x' = -(y - y') := by omega
      exact hdiff x (mem_inter.mp hxU).2 x' (mem_inter.mp hx'V).2 hxx'
        y (mem_inter.mp hyU).2 y' (mem_inter.mp hy'V).2 hyy' (by rw [heq, abs_neg])
    · by_cases hu2 : (U ∩ T₁).card = 0
      · have hv1 : (V ∩ T₁).card = 2 := by omega
        have hu0 : (U ∩ T₀).card = 2 := by omega
        have hv0 : (V ∩ T₀).card = 0 := by omega
        obtain ⟨x, x', hxx', hx⟩ := card_eq_two.mp hu0
        obtain ⟨y, y', hyy', hy⟩ := card_eq_two.mp hv1
        have hx0 : x ∈ T₀ := (mem_inter.mp (hx ▸ (by simp : x ∈ ({x, x'} : Finset ℤ)))).2
        have hx'0 : x' ∈ T₀ := (mem_inter.mp (hx ▸ (by simp : x' ∈ ({x, x'} : Finset ℤ)))).2
        have hy1 : y ∈ T₁ := (mem_inter.mp (hy ▸ (by simp : y ∈ ({y, y'} : Finset ℤ)))).2
        have hy'1 : y' ∈ T₁ := (mem_inter.mp (hy ▸ (by simp : y' ∈ ({y, y'} : Finset ℤ)))).2
        rw [hx, card_eq_zero.mp hu2, sum_pair hxx', sum_empty, add_zero] at hUs
        rw [hy, card_eq_zero.mp hv0, sum_pair hyy', sum_empty, zero_add] at hVs
        simp only [id_eq] at hUs hVs hs
        exact hsum x hx0 x' hx'0 hxx' y hy1 y' hy'1 hyy' (by omega)
      · have hu1' : (U ∩ T₁).card = 2 := by omega
        have hv1 : (V ∩ T₁).card = 0 := by omega
        have hu0 : (U ∩ T₀).card = 0 := by omega
        have hv0 : (V ∩ T₀).card = 2 := by omega
        obtain ⟨x, x', hxx', hx⟩ := card_eq_two.mp hv0
        obtain ⟨y, y', hyy', hy⟩ := card_eq_two.mp hu1'
        have hx0 : x ∈ T₀ := (mem_inter.mp (hx ▸ (by simp : x ∈ ({x, x'} : Finset ℤ)))).2
        have hx'0 : x' ∈ T₀ := (mem_inter.mp (hx ▸ (by simp : x' ∈ ({x, x'} : Finset ℤ)))).2
        have hy1 : y ∈ T₁ := (mem_inter.mp (hy ▸ (by simp : y ∈ ({y, y'} : Finset ℤ)))).2
        have hy'1 : y' ∈ T₁ := (mem_inter.mp (hy ▸ (by simp : y' ∈ ({y, y'} : Finset ℤ)))).2
        rw [hy, card_eq_zero.mp hu0, sum_pair hyy', sum_empty, zero_add] at hUs
        rw [hx, card_eq_zero.mp hv1, sum_pair hxx', sum_empty, add_zero] at hVs
        simp only [id_eq] at hUs hVs hs
        exact hsum x hx0 x' hx'0 hxx' y hy1 y' hy'1 hyy' (by omega)

/- Section 3: Conjunct 1 — Affine subsets of sizes 4, 5, 6 -/

private lemma exists_aff_four {X : Finset ℤ} (hX : 5 ≤ X.card) :
    ∃ D ⊆ X, D.card = 4 ∧ Aff D := by
  obtain ⟨X₀, X₁, q, r, hq, hX₀, hX₁, hdisj, hunion, _, hX₁ne, hle, h0, h1⟩ :=
    two_adic_split (by omega : 2 ≤ X.card)
  have hcard : X₀.card + X₁.card = X.card := by rw [← card_union_of_disjoint hdisj, hunion]
  obtain ⟨F, hF, hFc⟩ := exists_subset_card_eq (show 3 ≤ X₀.card by omega)
  obtain ⟨a, ha⟩ := hX₁ne
  obtain ⟨hna, haff⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF hx)) (h1 a ha)
    (aff_of_card_le_three (by omega))
  exact ⟨insert a F, insert_subset (hX₁ ha) (hF.trans hX₀),
    by rw [card_insert_of_notMem hna, hFc], haff⟩

private lemma pair_diff_sum_three {x y z u v : ℤ} (h1 : x < y) (h2 : y < z)
    (hu : u ∈ ({x, y, z} : Finset ℤ)) (hv : v ∈ ({x, y, z} : Finset ℤ)) (hne : u ≠ v) :
    (|u - v| = y - x ∨ |u - v| = z - y ∨ |u - v| = z - x) ∧
    (u + v = x + y ∨ u + v = x + z ∨ u + v = y + z) := by
  simp only [mem_insert, mem_singleton] at hu hv
  have hxy : |x - y| = y - x := by rw [abs_of_nonpos (by omega)]; ring
  have hyx : |y - x| = y - x := abs_of_nonneg (by omega)
  have hxz : |x - z| = z - x := by rw [abs_of_nonpos (by omega)]; ring
  have hzx : |z - x| = z - x := abs_of_nonneg (by omega)
  have hyz : |y - z| = z - y := by rw [abs_of_nonpos (by omega)]; ring
  have hzy : |z - y| = z - y := abs_of_nonneg (by omega)
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    (try exact absurd rfl hne) <;>
    exact ⟨by omega, by omega⟩

private lemma pair_diff_sum_two {x y u v : ℤ} (h1 : x < y)
    (hu : u ∈ ({x, y} : Finset ℤ)) (hv : v ∈ ({x, y} : Finset ℤ)) (hne : u ≠ v) :
    |u - v| = y - x ∧ u + v = x + y := by
  simp only [mem_insert, mem_singleton] at hu hv
  have hxy : |x - y| = y - x := by rw [abs_of_nonpos (by omega)]; ring
  have hyx : |y - x| = y - x := abs_of_nonneg (by omega)
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    (try exact absurd rfl hne) <;>
    exact ⟨by omega, by omega⟩

private lemma exists_aff_five_of_four_four_aux {X₀ X₁ : Finset ℤ} {q r : ℤ}
    (hq : 0 < q) (h0 : ∀ x ∈ X₀, x ≡ r [ZMOD 2 * q]) (h1 : ∀ y ∈ X₁, y ≡ r + q [ZMOD 2 * q])
    {p₀ a b q₀ c d : ℤ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d)
    (hX₀ : X₀ = {p₀, p₀ + a, p₀ + b, p₀ + a + b})
    (hX₁ : X₁ = {q₀, q₀ + c, q₀ + d, q₀ + c + d})
    (hord : 2 * p₀ + a + b < 2 * q₀ + c + d ∨
      (2 * p₀ + a + b = 2 * q₀ + c + d ∧ a + b ≤ c + d)) :
    ∃ D ⊆ X₀ ∪ X₁, D.card = 5 ∧ Aff D := by
  have hdisj : Disjoint X₀ X₁ := (split_parity hq h0 h1).1
  have finish (u₁ u₂ u₃ v₁ v₂ : ℤ)
      (hu12 : u₁ < u₂) (hu23 : u₂ < u₃) (hv12 : v₁ < v₂)
      (hU : ({u₁, u₂, u₃} : Finset ℤ) ⊆ X₀) (hV : ({v₁, v₂} : Finset ℤ) ⊆ X₁)
      (hd1 : u₂ - u₁ ≠ v₂ - v₁) (hd2 : u₃ - u₂ ≠ v₂ - v₁) (hd3 : u₃ - u₁ ≠ v₂ - v₁)
      (hs1 : u₁ + u₂ ≠ v₁ + v₂) (hs2 : u₁ + u₃ ≠ v₁ + v₂) (hs3 : u₂ + u₃ ≠ v₁ + v₂) :
      ∃ D ⊆ X₀ ∪ X₁, D.card = 5 ∧ Aff D := by
    have hUc : ({u₁, u₂, u₃} : Finset ℤ).card = 3 := by
      simp [show u₁ ≠ u₂ by omega, show u₁ ≠ u₃ by omega, show u₂ ≠ u₃ by omega]
    have hVc : ({v₁, v₂} : Finset ℤ).card = 2 := card_pair (by omega)
    obtain ⟨hUVd, haff⟩ := aff_union_of_split_le_three hq
      (fun x hx ↦ h0 x (hU hx)) (fun y hy ↦ h1 y (hV hy)) (by omega) (by omega)
      (by
        intro x hx x' hx' hxx' y hy y' hy' hyy'
        have hpx := (pair_diff_sum_three hu12 hu23 hx hx' hxx').1
        have hpy := (pair_diff_sum_two hv12 hy hy' hyy').1
        omega)
      (by
        intro x hx x' hx' hxx' y hy y' hy' hyy'
        have hpx := (pair_diff_sum_three hu12 hu23 hx hx' hxx').2
        have hpy := (pair_diff_sum_two hv12 hy hy' hyy').2
        omega)
    refine ⟨{u₁, u₂, u₃} ∪ {v₁, v₂}, union_subset_union hU hV, ?_, haff⟩
    rw [card_union_of_disjoint hUVd, hUc, hVc]
  have hTa : ({p₀, p₀ + a, p₀ + b} : Finset ℤ) ⊆ X₀ := by
    rw [hX₀]; intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
  have hTb : ({p₀, p₀ + a, p₀ + a + b} : Finset ℤ) ⊆ X₀ := by
    rw [hX₀]; intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
  have hV13 : ({q₀ + c, q₀ + c + d} : Finset ℤ) ⊆ X₁ := by
    rw [hX₁]; intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
  have hV23 : ({q₀ + d, q₀ + c + d} : Finset ℤ) ⊆ X₁ := by
    rw [hX₁]; intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
  have hV03 : ({q₀, q₀ + c + d} : Finset ℤ) ⊆ X₁ := by
    rw [hX₁]; intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
  by_cases hd : d ≠ a ∧ d ≠ b - a ∧ d ≠ b
  · exact finish p₀ (p₀ + a) (p₀ + b) (q₀ + c) (q₀ + c + d) (by omega) (by omega) (by omega)
      hTa hV13 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  by_cases hc' : c ≠ a ∧ c ≠ b - a ∧ c ≠ b
  · exact finish p₀ (p₀ + a) (p₀ + b) (q₀ + d) (q₀ + c + d) (by omega) (by omega) (by omega)
      hTa hV23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  by_cases hcab : c = a ∧ d = b
  · have hlt : 2 * p₀ + a + b < 2 * q₀ + c + d := by
      rcases hord with h | ⟨heq, _⟩
      · exact h
      · exfalso
        have hpq : p₀ = q₀ := by omega
        have hp : p₀ ∈ X₀ := by rw [hX₀]; simp
        have hq' : p₀ ∈ X₁ := by rw [hX₁, hpq]; simp
        exact disjoint_left.mp hdisj hp hq'
    exact finish p₀ (p₀ + a) (p₀ + b) q₀ (q₀ + c + d) (by omega) (by omega) (by omega)
      hTa hV03 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  by_cases hcbab : c = b - a ∧ d = b
  · exact finish p₀ (p₀ + a) (p₀ + a + b) (q₀ + d) (q₀ + c + d) (by omega) (by omega) (by omega)
      hTb hV23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  by_cases hcaba : c = a ∧ d = b - a
  · exact finish p₀ (p₀ + a) (p₀ + a + b) (q₀ + c) (q₀ + c + d) (by omega) (by omega) (by omega)
      hTb hV13 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have hcb : c = b - a ∧ d = a := by omega
    exact finish p₀ (p₀ + a) (p₀ + a + b) (q₀ + d) (q₀ + c + d) (by omega) (by omega) (by omega)
      hTb hV23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

private lemma exists_aff_five {X : Finset ℤ} (hX : 8 ≤ X.card) :
    ∃ D ⊆ X, D.card = 5 ∧ Aff D := by
  obtain ⟨X₀, X₁, q, r, hq, hX₀, hX₁, hdisj, hunion, hX₀ne, hX₁ne, hle, h0, h1⟩ :=
    two_adic_split (by omega : 2 ≤ X.card)
  have hcard : X₀.card + X₁.card = X.card := by rw [← card_union_of_disjoint hdisj, hunion]
  by_cases h5 : 5 ≤ X₀.card
  · obtain ⟨F, hF, hFc, hFaff⟩ := exists_aff_four h5
    obtain ⟨a, ha⟩ := hX₁ne
    obtain ⟨hna, haff⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF hx)) (h1 a ha) hFaff
    exact ⟨insert a F, insert_subset (hX₁ ha) (hF.trans hX₀),
      by rw [card_insert_of_notMem hna, hFc], haff⟩
  · have hc0 : X₀.card = 4 := by omega
    have hc1 : X₁.card = 4 := by omega
    by_cases haff0 : Aff X₀
    · obtain ⟨a, ha⟩ := hX₁ne
      obtain ⟨hna, haff⟩ := aff_insert_of_split hq h0 (h1 a ha) haff0
      exact ⟨insert a X₀, insert_subset (hX₁ ha) hX₀,
        by rw [card_insert_of_notMem hna, hc0], haff⟩
    by_cases haff1 : Aff X₁
    · obtain ⟨a, ha⟩ := hX₀ne
      have h0' : ∀ x ∈ X₀, x ≡ (r + q) + q [ZMOD 2 * q] := fun x hx ↦
        (h0 x hx).trans (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩)
      obtain ⟨hna, haff⟩ := aff_insert_of_split hq h1 (h0' a ha) haff1
      exact ⟨insert a X₁, insert_subset (hX₀ ha) hX₁,
        by rw [card_insert_of_notMem hna, hc1], haff⟩
    · obtain ⟨p₀, p₁, p₂, p₃, hp1, hp2, hp3, hpEq⟩ := finset_card_four_sorted hc0
      obtain ⟨q₀, q₁, q₂, q₃, hq1, hq2, hq3, hqEq⟩ := finset_card_four_sorted hc1
      have hpeq : p₀ + p₃ = p₁ + p₂ := by
        by_contra hne
        exact haff0 (hpEq ▸ (aff_four_iff hp1 hp2 hp3).mpr hne)
      have hqeq : q₀ + q₃ = q₁ + q₂ := by
        by_contra hne
        exact haff1 (hqEq ▸ (aff_four_iff hq1 hq2 hq3).mpr hne)
      let a := p₁ - p₀
      let b := p₂ - p₀
      let c := q₁ - q₀
      let d := q₂ - q₀
      have hpEq' : X₀ = {p₀, p₀ + a, p₀ + b, p₀ + a + b} := by
        have h1 : p₁ = p₀ + a := by omega
        have h2 : p₂ = p₀ + b := by omega
        have h3 : p₃ = p₀ + a + b := by omega
        rw [hpEq, h1, h2, h3]
      have hqEq' : X₁ = {q₀, q₀ + c, q₀ + d, q₀ + c + d} := by
        have h1 : q₁ = q₀ + c := by omega
        have h2 : q₂ = q₀ + d := by omega
        have h3 : q₃ = q₀ + c + d := by omega
        rw [hqEq, h1, h2, h3]
      by_cases hord : 2 * p₀ + a + b < 2 * q₀ + c + d ∨
          (2 * p₀ + a + b = 2 * q₀ + c + d ∧ a + b ≤ c + d)
      · obtain ⟨D, hD, hDc, hDa⟩ := exists_aff_five_of_four_four_aux hq h0 h1
          (by omega) (by omega) (by omega) (by omega) hpEq' hqEq' hord
        exact ⟨D, hD.trans (by rw [hunion]), hDc, hDa⟩
      · have h0' : ∀ x ∈ X₀, x ≡ (r + q) + q [ZMOD 2 * q] := fun x hx ↦
          (h0 x hx).trans (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩)
        have hord' : 2 * q₀ + c + d < 2 * p₀ + a + b ∨
            (2 * q₀ + c + d = 2 * p₀ + a + b ∧ c + d ≤ a + b) := by omega
        obtain ⟨D, hD, hDc, hDa⟩ := exists_aff_five_of_four_four_aux hq h1 h0'
          (by omega) (by omega) (by omega) (by omega) hqEq' hpEq' hord'
        exact ⟨D, hD.trans (by rw [union_comm, hunion]), hDc, hDa⟩

/- Classification of 7-element sets without affine 5-subsets -/

private lemma classify_seven_no_aff_five {X : Finset ℤ} (hXc : X.card = 7)
    (hno : ∀ F ⊆ X, F.card = 5 → ¬ Aff F) :
    ∃ x a b : ℤ, 0 < a ∧ a < b ∧
      X = {x, x - a, x + a, x - b, x + b, x - (a + b), x + (a + b)} := by
  obtain ⟨X₀, X₁, q, r, hq, hX₀, hX₁, hdisj, hunion, _, hX₁ne, hle, h0, h1⟩ :=
    two_adic_split (by omega : 2 ≤ X.card)
  have hcard : X₀.card + X₁.card = 7 := by rw [← card_union_of_disjoint hdisj, hunion, hXc]
  have hnot5 : ¬ (5 ≤ X₀.card) := by
    intro h5
    obtain ⟨F, hF, hFc, hFaff⟩ := exists_aff_four h5
    obtain ⟨a, ha⟩ := hX₁ne
    obtain ⟨hna, haff⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF hx)) (h1 a ha) hFaff
    exact hno (insert a F) (insert_subset (hX₁ ha) (hF.trans hX₀))
      (by rw [card_insert_of_notMem hna, hFc]) haff
  have hc0 : X₀.card = 4 := by omega
  have hc1 : X₁.card = 3 := by omega
  have haff0 : ¬ Aff X₀ := by
    intro haff
    obtain ⟨a, ha⟩ := hX₁ne
    obtain ⟨hna, haff'⟩ := aff_insert_of_split hq h0 (h1 a ha) haff
    exact hno (insert a X₀) (insert_subset (hX₁ ha) hX₀)
      (by rw [card_insert_of_notMem hna, hc0]) haff'
  obtain ⟨p₀, p₁, p₂, p₃, hp1, hp2, hp3, hpEq⟩ := finset_card_four_sorted hc0
  obtain ⟨y₀, y₁, y₂, hy1, hy2, hyEq⟩ := finset_card_three_sorted hc1
  have hpeq : p₀ + p₃ = p₁ + p₂ := by
    by_contra hne
    exact haff0 (hpEq ▸ (aff_four_iff hp1 hp2 hp3).mpr hne)
  let a := p₁ - p₀
  let b := p₂ - p₀
  have ha : 0 < a := by omega
  have hab : a < b := by omega
  have hp1' : p₁ = p₀ + a := by omega
  have hp2' : p₂ = p₀ + b := by omega
  have hp3' : p₃ = p₀ + a + b := by omega
  have hpair_bad : ∀ u v : ℤ, u < v → u ∈ X₁ → v ∈ X₁ →
      u + v = 2 * p₀ + a + b ∨ v - u = a ∨ v - u = b := by
    intro u v huv hu hv
    by_contra hbad
    push Not at hbad
    obtain ⟨hs, hda, hdb⟩ := hbad
    have check_triple (u₁ u₂ u₃ : ℤ) (h12 : u₁ < u₂) (h23 : u₂ < u₃)
        (hU : ({u₁, u₂, u₃} : Finset ℤ) ⊆ X₀) :
        (v - u = u₂ - u₁ ∨ v - u = u₃ - u₂ ∨ v - u = u₃ - u₁) ∨
        (u + v = u₁ + u₂ ∨ u + v = u₁ + u₃ ∨ u + v = u₂ + u₃) := by
      by_contra hok
      push Not at hok
      have hUc : ({u₁, u₂, u₃} : Finset ℤ).card = 3 := by
        simp [show u₁ ≠ u₂ by omega, show u₁ ≠ u₃ by omega, show u₂ ≠ u₃ by omega]
      have hVc : ({u, v} : Finset ℤ).card = 2 := card_pair (by omega)
      have hV : ({u, v} : Finset ℤ) ⊆ X₁ := by
        intro z hz; simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
      obtain ⟨hUVd, haff⟩ := aff_union_of_split_le_three hq
        (fun x hx ↦ h0 x (hU hx)) (fun y hy ↦ h1 y (hV hy)) (by omega) (by omega)
        (by
          intro x hx x' hx' hxx' y hy y' hy' hyy'
          have hpx := (pair_diff_sum_three h12 h23 hx hx' hxx').1
          have hpy := (pair_diff_sum_two huv hy hy' hyy').1
          omega)
        (by
          intro x hx x' hx' hxx' y hy y' hy' hyy'
          have hpx := (pair_diff_sum_three h12 h23 hx hx' hxx').2
          have hpy := (pair_diff_sum_two huv hy hy' hyy').2
          omega)
      exact hno ({u₁, u₂, u₃} ∪ {u, v})
        ((union_subset_union hU hV).trans (by rw [hunion]))
        (by rw [card_union_of_disjoint hUVd, hUc, hVc]) haff
    have hTa : ({p₀, p₁, p₂} : Finset ℤ) ⊆ X₀ := by
      rw [hpEq]; intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
    have hTd : ({p₁, p₂, p₃} : Finset ℤ) ⊆ X₀ := by
      rw [hpEq]; intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
    have hTb : ({p₀, p₁, p₃} : Finset ℤ) ⊆ X₀ := by
      rw [hpEq]; intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
    have hTc : ({p₀, p₂, p₃} : Finset ℤ) ⊆ X₀ := by
      rw [hpEq]; intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
    have c1 := check_triple p₀ p₁ p₂ hp1 hp2 hTa
    have c2 := check_triple p₁ p₂ p₃ hp2 hp3 hTd
    have c3 := check_triple p₀ p₁ p₃ hp1 (by omega) hTb
    have c4 := check_triple p₀ p₂ p₃ (by omega) hp3 hTc
    omega
  have hy0X : y₀ ∈ X₁ := by rw [hyEq]; simp
  have hy1X : y₁ ∈ X₁ := by rw [hyEq]; simp
  have hy2X : y₂ ∈ X₁ := by rw [hyEq]; simp
  have h01 := hpair_bad y₀ y₁ hy1 hy0X hy1X
  have h12 := hpair_bad y₁ y₂ hy2 hy1X hy2X
  have h02 := hpair_bad y₀ y₂ (by omega) hy0X hy2X
  have hnot_in : ∀ y ∈ X₁, y ≠ p₀ ∧ y ≠ p₁ ∧ y ≠ p₂ ∧ y ≠ p₃ := by
    intro y hy
    have hn : y ∉ X₀ := fun hm ↦ disjoint_left.mp hdisj hm hy
    rw [hpEq] at hn
    simp only [mem_insert, mem_singleton, not_or] at hn
    exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩
  obtain ⟨hn00, hn01, hn02, hn03⟩ := hnot_in y₀ hy0X
  obtain ⟨hn10, hn11, hn12, hn13⟩ := hnot_in y₁ hy1X
  obtain ⟨hn20, hn21, hn22, hn23⟩ := hnot_in y₂ hy2X
  have h_center_a : y₁ - y₀ = a → y₂ - y₁ = a → y₀ + y₂ = 2 * p₀ + a + b →
      ∃ x a' b' : ℤ, 0 < a' ∧ a' < b' ∧
        X = {x, x - a', x + a', x - b', x + b', x - (a' + b'), x + (a' + b')} := by
    intro hd1 hd2 hsum
    have h2y1 : 2 * y₁ = 2 * p₀ + a + b := by omega
    have heven : (b - a) % 2 = 0 := by omega
    let u := (b - a) / 2
    have hu : 2 * u = b - a := by omega
    have hu_pos : 0 < u := by omega
    have hu_ne : u ≠ a := by
      intro heq
      have : y₀ = p₁ := by omega
      exact hn01 this
    by_cases hua : u < a
    · refine ⟨y₁, u, a, hu_pos, hua, ?_⟩
      have ep0 : p₀ = y₁ - (u + a) := by omega
      have ep1 : p₁ = y₁ - u := by omega
      have ep2 : p₂ = y₁ + u := by omega
      have ep3 : p₃ = y₁ + (u + a) := by omega
      have ey0 : y₀ = y₁ - a := by omega
      have ey2 : y₂ = y₁ + a := by omega
      rw [← hunion, hpEq, hyEq, ep0, ep1, ep2, ep3, ey0, ey2]
      ext z; simp only [mem_union, mem_insert, mem_singleton]
      constructor
      · rintro ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) <;> simp
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
    · refine ⟨y₁, a, u, ha, by omega, ?_⟩
      have ep0 : p₀ = y₁ - (a + u) := by omega
      have ep1 : p₁ = y₁ - u := by omega
      have ep2 : p₂ = y₁ + u := by omega
      have ep3 : p₃ = y₁ + (a + u) := by omega
      have ey0 : y₀ = y₁ - a := by omega
      have ey2 : y₂ = y₁ + a := by omega
      rw [← hunion, hpEq, hyEq, ep0, ep1, ep2, ep3, ey0, ey2]
      ext z; simp only [mem_union, mem_insert, mem_singleton]
      constructor
      · rintro ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) <;> simp
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  have h_center_b : y₁ - y₀ = b → y₂ - y₁ = b → y₀ + y₂ = 2 * p₀ + a + b →
      ∃ x a' b' : ℤ, 0 < a' ∧ a' < b' ∧
        X = {x, x - a', x + a', x - b', x + b', x - (a' + b'), x + (a' + b')} := by
    intro hd1 hd2 hsum
    have h2y1 : 2 * y₁ = 2 * p₀ + a + b := by omega
    let u := (b - a) / 2
    let v := (b + a) / 2
    have hu : 2 * u = b - a := by omega
    have hv : 2 * v = b + a := by omega
    refine ⟨y₁, u, v, by omega, by omega, ?_⟩
    have ep0 : p₀ = y₁ - v := by omega
    have ep1 : p₁ = y₁ - u := by omega
    have ep2 : p₂ = y₁ + u := by omega
    have ep3 : p₃ = y₁ + v := by omega
    have ey0 : y₀ = y₁ - (u + v) := by omega
    have ey2 : y₂ = y₁ + (u + v) := by omega
    rw [← hunion, hpEq, hyEq, ep0, ep1, ep2, ep3, ey0, ey2]
    ext z; simp only [mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  rcases h01 with hs01 | hd01a | hd01b <;>
    rcases h12 with hs12 | hd12a | hd12b <;>
    rcases h02 with hs02 | hd02a | hd02b <;>
    (try (exfalso; first | omega | exact hn00 (by omega) | exact hn11 (by omega) | exact hn12 (by omega)))
  · exact h_center_a hd01a hd12a hs02
  · have h0' : ∀ x ∈ X₀, x ≡ (r + q) + q [ZMOD 2 * q] := fun x hx ↦
      (h0 x hx).trans (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩)
    have hV : ({p₀, p₃} : Finset ℤ) ⊆ X₀ := by
      rw [hpEq]; intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
    have hbad03 : y₀ + y₂ = 2 * p₀ + a + b := by
      by_contra hne
      have hVc : ({p₀, p₃} : Finset ℤ).card = 2 := card_pair (by omega)
      obtain ⟨hUVd, haff⟩ := aff_union_of_split_le_three hq
        h1 (fun x hx ↦ h0' x (hV hx)) (by omega) (by omega)
        (by
          intro x hx x' hx' hxx' y hy y' hy' hyy'
          rw [hyEq] at hx hx'
          have hpx := (pair_diff_sum_three hy1 hy2 hx hx' hxx').1
          have hpy := (pair_diff_sum_two (by omega : p₀ < p₃) hy hy' hyy').1
          omega)
        (by
          intro x hx x' hx' hxx' y hy y' hy' hyy'
          rw [hyEq] at hx hx'
          have hpx := (pair_diff_sum_three hy1 hy2 hx hx' hxx').2
          have hpy := (pair_diff_sum_two (by omega : p₀ < p₃) hy hy' hyy').2
          intro hsumEq
          rcases hpx with h | h | h
          · exact hn01 (by omega)
          · exact hne (by omega)
          · exact hn00 (by omega))
      exact hno (X₁ ∪ {p₀, p₃})
        ((union_subset_union (Subset.refl X₁) hV).trans (by rw [union_comm, hunion]))
        (by rw [card_union_of_disjoint hUVd, hc1, hVc]) haff
    exact h_center_a hd01a hd12a hbad03
  · exact h_center_b hd01b hd12b hs02

/- Explicit 3 + 3 construction for two 7-element extremizers -/

private lemma exists_aff_six_of_h3_pair_aux {X₀ X₁ : Finset ℤ} {q r : ℤ}
    (hq : 0 < q) (h0 : ∀ x ∈ X₀, x ≡ r [ZMOD 2 * q]) (h1 : ∀ y ∈ X₁, y ≡ r + q [ZMOD 2 * q])
    {x a b y c d : ℤ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d)
    (hX₀ : X₀ = {x, x - a, x + a, x - b, x + b, x - (a + b), x + (a + b)})
    (hX₁ : X₁ = {y, y - c, y + c, y - d, y + d, y - (c + d), y + (c + d)})
    (hle : a + b ≤ c + d) (hxy : x < y) :
    ∃ D ⊆ X₀ ∪ X₁, D.card = 6 ∧ Aff D := by
  have finish (u₁ u₂ u₃ v₁ v₂ v₃ : ℤ)
      (hu12 : u₁ < u₂) (hu23 : u₂ < u₃) (hv12 : v₁ < v₂) (hv23 : v₂ < v₃)
      (hU : ({u₁, u₂, u₃} : Finset ℤ) ⊆ X₀) (hV : ({v₁, v₂, v₃} : Finset ℤ) ⊆ X₁)
      (hdiff : ∀ du dv : ℤ,
        (du = u₂ - u₁ ∨ du = u₃ - u₂ ∨ du = u₃ - u₁) →
        (dv = v₂ - v₁ ∨ dv = v₃ - v₂ ∨ dv = v₃ - v₁) → du ≠ dv)
      (hsum : ∀ su sv : ℤ,
        (su = u₁ + u₂ ∨ su = u₁ + u₃ ∨ su = u₂ + u₃) →
        (sv = v₁ + v₂ ∨ sv = v₁ + v₃ ∨ sv = v₂ + v₃) → su ≠ sv) :
      ∃ D ⊆ X₀ ∪ X₁, D.card = 6 ∧ Aff D := by
    have hUc : ({u₁, u₂, u₃} : Finset ℤ).card = 3 := by
      simp [show u₁ ≠ u₂ by omega, show u₁ ≠ u₃ by omega, show u₂ ≠ u₃ by omega]
    have hVc : ({v₁, v₂, v₃} : Finset ℤ).card = 3 := by
      simp [show v₁ ≠ v₂ by omega, show v₁ ≠ v₃ by omega, show v₂ ≠ v₃ by omega]
    obtain ⟨hUVd, haff⟩ := aff_union_of_split_le_three hq
      (fun z hz ↦ h0 z (hU hz)) (fun z hz ↦ h1 z (hV hz)) (by omega) (by omega)
      (by
        intro z₁ hz₁ z₂ hz₂ hne w₁ hw₁ w₂ hw₂ hne'
        exact hdiff _ _ (pair_diff_sum_three hu12 hu23 hz₁ hz₂ hne).1
          (pair_diff_sum_three hv12 hv23 hw₁ hw₂ hne').1)
      (by
        intro z₁ hz₁ z₂ hz₂ hne w₁ hw₁ w₂ hw₂ hne'
        exact hsum _ _ (pair_diff_sum_three hu12 hu23 hz₁ hz₂ hne).2
          (pair_diff_sum_three hv12 hv23 hw₁ hw₂ hne').2)
    refine ⟨{u₁, u₂, u₃} ∪ {v₁, v₂, v₃}, union_subset_union hU hV, ?_, haff⟩
    rw [card_union_of_disjoint hUVd, hUc, hVc]
  have hT1 : ({y - (c + d), y, y + (c + d)} : Finset ℤ) ⊆ X₁ := by
    rw [hX₁]; intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢; tauto
  have hU_bot : ({x - (a + b), x - b, x - a} : Finset ℤ) ⊆ X₀ := by
    rw [hX₀]; intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢; tauto
  by_cases hneq : 2 * y - (c + d) ≠ 2 * x - (a + b)
  · by_cases heq : a + b = c + d
    · exact finish (x - (a + b)) (x - b) (x - a) (y - (c + d)) y (y + (c + d))
        (by omega) (by omega) (by omega) (by omega) hU_bot hT1
        (fun _ _ h1 h2 ↦ by omega) (fun _ _ h1 h2 ↦ by omega)
    · have hlt : a + b < c + d := by omega
      let s := 2 * y - (c + d)
      have hU1 : ({x - (a + b), x - b, x} : Finset ℤ) ⊆ X₀ := by
        rw [hX₀]; intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢; tauto
      have hU2 : ({x - (a + b), x - a, x} : Finset ℤ) ⊆ X₀ := by
        rw [hX₀]; intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢; tauto
      have hU3 : ({x - b, x - a, x} : Finset ℤ) ⊆ X₀ := by
        rw [hX₀]; intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢; tauto
      by_cases hs1 : s ≠ 2 * x - (a + 2 * b) ∧ s ≠ 2 * x - (2 * a + b)
      · exact finish (x - (a + b)) (x - b) (x - a) (y - (c + d)) y (y + (c + d))
          (by omega) (by omega) (by omega) (by omega) hU_bot hT1
          (fun _ _ h1 h2 ↦ by omega) (fun _ _ h1 h2 ↦ by omega)
      · exact finish (x - b) (x - a) x (y - (c + d)) y (y + (c + d))
          (by omega) (by omega) (by omega) (by omega) hU3 hT1
          (fun _ _ h1 h2 ↦ by omega) (fun _ _ h1 h2 ↦ by omega)
  · push Not at hneq
    by_cases h2k : 2 * (y - x) ≠ a
    · have hUa : ({x - a, x, x + a} : Finset ℤ) ⊆ X₀ := by
        rw [hX₀]; intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢; tauto
      exact finish (x - a) x (x + a) (y - (c + d)) y (y + (c + d))
        (by omega) (by omega) (by omega) (by omega) hUa hT1
        (fun _ _ h1 h2 ↦ by omega) (fun _ _ h1 h2 ↦ by omega)
    · push Not at h2k
      by_cases hb2a : b ≠ 2 * a
      · have hUb : ({x - b, x, x + b} : Finset ℤ) ⊆ X₀ := by
          rw [hX₀]; intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢; tauto
        exact finish (x - b) x (x + b) (y - (c + d)) y (y + (c + d))
          (by omega) (by omega) (by omega) (by omega) hUb hT1
          (fun _ _ h1 h2 ↦ by omega) (fun _ _ h1 h2 ↦ by omega)
      · push Not at hb2a
        have hT1' : ({y - d, y, y + (c + d)} : Finset ℤ) ⊆ X₁ := by
          rw [hX₁]; intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢; tauto
        exact finish (x - (a + b)) (x - b) (x - a) (y - d) y (y + (c + d))
          (by omega) (by omega) (by omega) (by omega) hU_bot hT1'
          (fun _ _ h1 h2 ↦ by omega) (fun _ _ h1 h2 ↦ by omega)

private lemma exists_aff_six_of_h3_pair {X₀ X₁ : Finset ℤ} {q r : ℤ}
    (hq : 0 < q) (h0 : ∀ x ∈ X₀, x ≡ r [ZMOD 2 * q]) (h1 : ∀ y ∈ X₁, y ≡ r + q [ZMOD 2 * q])
    {x a b y c d : ℤ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d)
    (hX₀ : X₀ = {x, x - a, x + a, x - b, x + b, x - (a + b), x + (a + b)})
    (hX₁ : X₁ = {y, y - c, y + c, y - d, y + d, y - (c + d), y + (c + d)}) :
    ∃ D ⊆ X₀ ∪ X₁, D.card = 6 ∧ Aff D := by
  have hdisj : Disjoint X₀ X₁ := (split_parity hq h0 h1).1
  have hxy_ne : x ≠ y := by
    intro h
    have hx : x ∈ X₀ := by rw [hX₀]; simp
    have hy : x ∈ X₁ := by rw [hX₁, h]; simp
    exact disjoint_left.mp hdisj hx hy
  have solve_ordered {A B : Finset ℤ} {r' : ℤ}
      (hA : ∀ z ∈ A, z ≡ r' [ZMOD 2 * q]) (hB : ∀ z ∈ B, z ≡ r' + q [ZMOD 2 * q])
      {x' a' b' y' c' d' : ℤ} (ha' : 0 < a') (hab' : a' < b') (hc' : 0 < c') (hcd' : c' < d')
      (hAeq : A = {x', x' - a', x' + a', x' - b', x' + b', x' - (a' + b'), x' + (a' + b')})
      (hBeq : B = {y', y' - c', y' + c', y' - d', y' + d', y' - (c' + d'), y' + (c' + d')})
      (hle : a' + b' ≤ c' + d') (hne : x' ≠ y') :
      ∃ D ⊆ A ∪ B, D.card = 6 ∧ Aff D := by
    by_cases hlt : x' < y'
    · exact exists_aff_six_of_h3_pair_aux hq hA hB ha' hab' hc' hcd' hAeq hBeq hle hlt
    · have hgt : -x' < -y' := by omega
      let A' := A.image Neg.neg
      let B' := B.image Neg.neg
      have hA' : ∀ z ∈ A', z ≡ -r' [ZMOD 2 * q] := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
        exact (hA w hw).neg
      have hB' : ∀ z ∈ B', z ≡ -r' + q [ZMOD 2 * q] := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
        exact (hB w hw).neg.trans (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩)
      have hA'eq : A' = {-x', -x' - a', -x' + a', -x' - b', -x' + b',
          -x' - (a' + b'), -x' + (a' + b')} := by
        dsimp only [A']; rw [hAeq]
        ext z; simp only [mem_image, mem_insert, mem_singleton]
        constructor
        · rintro ⟨w, hw, rfl⟩
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inl (by ring)))
          · exact Or.inr (Or.inl (by ring))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ring)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by ring))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by ring))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ring))))))
        · intro hz
          rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨x', Or.inl rfl, by ring⟩
          · exact ⟨x' + a', Or.inr (Or.inr (Or.inl rfl)), by ring⟩
          · exact ⟨x' - a', Or.inr (Or.inl rfl), by ring⟩
          · exact ⟨x' + b', Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by ring⟩
          · exact ⟨x' - b', Or.inr (Or.inr (Or.inr (Or.inl rfl))), by ring⟩
          · exact ⟨x' + (a' + b'), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), by ring⟩
          · exact ⟨x' - (a' + b'), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), by ring⟩
      have hB'eq : B' = {-y', -y' - c', -y' + c', -y' - d', -y' + d',
          -y' - (c' + d'), -y' + (c' + d')} := by
        dsimp only [B']; rw [hBeq]
        ext z; simp only [mem_image, mem_insert, mem_singleton]
        constructor
        · rintro ⟨w, hw, rfl⟩
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inl (by ring)))
          · exact Or.inr (Or.inl (by ring))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ring)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by ring))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by ring))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ring))))))
        · intro hz
          rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨y', Or.inl rfl, by ring⟩
          · exact ⟨y' + c', Or.inr (Or.inr (Or.inl rfl)), by ring⟩
          · exact ⟨y' - c', Or.inr (Or.inl rfl), by ring⟩
          · exact ⟨y' + d', Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by ring⟩
          · exact ⟨y' - d', Or.inr (Or.inr (Or.inr (Or.inl rfl))), by ring⟩
          · exact ⟨y' + (c' + d'), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), by ring⟩
          · exact ⟨y' - (c' + d'), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), by ring⟩
      obtain ⟨D', hD', hD'c, hD'a⟩ :=
        exists_aff_six_of_h3_pair_aux hq hA' hB' ha' hab' hc' hcd' hA'eq hB'eq hle hgt
      refine ⟨D'.image Neg.neg, ?_, ?_, aff_neg hD'a⟩
      · intro z hz
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
        rcases mem_union.mp (hD' hw) with hwA | hwB
        · obtain ⟨u, hu, rfl⟩ := mem_image.mp hwA
          simpa using mem_union_left B hu
        · obtain ⟨u, hu, rfl⟩ := mem_image.mp hwB
          simpa using mem_union_right A hu
      · rw [card_image_of_injective _ neg_injective, hD'c]
  by_cases hle : a + b ≤ c + d
  · exact solve_ordered h0 h1 ha hab hc hcd hX₀ hX₁ hle hxy_ne
  · have h0' : ∀ z ∈ X₀, z ≡ (r + q) + q [ZMOD 2 * q] := fun z hz ↦
      (h0 z hz).trans (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩)
    obtain ⟨D, hD, hDc, hDa⟩ := solve_ordered h1 h0' hc hcd ha hab hX₁ hX₀ (by omega) hxy_ne.symm
    exact ⟨D, by rwa [union_comm] at hD, hDc, hDa⟩

private lemma exists_aff_six {X : Finset ℤ} (hX : 14 ≤ X.card) :
    ∃ D ⊆ X, D.card = 6 ∧ Aff D := by
  obtain ⟨X₀, X₁, q, r, hq, hX₀, hX₁, hdisj, hunion, hX₀ne, hX₁ne, hle, h0, h1⟩ :=
    two_adic_split (by omega : 2 ≤ X.card)
  have hcard : X₀.card + X₁.card = X.card := by rw [← card_union_of_disjoint hdisj, hunion]
  by_cases h8 : 8 ≤ X₀.card
  · obtain ⟨F, hF, hFc, hFaff⟩ := exists_aff_five h8
    obtain ⟨a, ha⟩ := hX₁ne
    obtain ⟨hna, haff⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF hx)) (h1 a ha) hFaff
    exact ⟨insert a F, insert_subset (hX₁ ha) (hF.trans hX₀),
      by rw [card_insert_of_notMem hna, hFc], haff⟩
  · have hc0 : X₀.card = 7 := by omega
    have hc1 : X₁.card = 7 := by omega
    by_cases h50 : ∃ F ⊆ X₀, F.card = 5 ∧ Aff F
    · obtain ⟨F, hF, hFc, hFaff⟩ := h50
      obtain ⟨a, ha⟩ := hX₁ne
      obtain ⟨hna, haff⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF hx)) (h1 a ha) hFaff
      exact ⟨insert a F, insert_subset (hX₁ ha) (hF.trans hX₀),
        by rw [card_insert_of_notMem hna, hFc], haff⟩
    by_cases h51 : ∃ F ⊆ X₁, F.card = 5 ∧ Aff F
    · obtain ⟨F, hF, hFc, hFaff⟩ := h51
      obtain ⟨a, ha⟩ := hX₀ne
      have h0' : ∀ x ∈ X₀, x ≡ (r + q) + q [ZMOD 2 * q] := fun x hx ↦
        (h0 x hx).trans (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩)
      obtain ⟨hna, haff⟩ := aff_insert_of_split hq (fun x hx ↦ h1 x (hF hx)) (h0' a ha) hFaff
      exact ⟨insert a F, insert_subset (hX₀ ha) (hF.trans hX₁),
        by rw [card_insert_of_notMem hna, hFc], haff⟩
    · push Not at h50 h51
      obtain ⟨x, a, b, ha, hab, hX₀eq⟩ := classify_seven_no_aff_five hc0 h50
      obtain ⟨y, c, d, hc, hcd, hX₁eq⟩ := classify_seven_no_aff_five hc1 h51
      obtain ⟨D, hD, hDc, hDa⟩ :=
        exists_aff_six_of_h3_pair hq h0 h1 ha hab hc hcd hX₀eq hX₁eq
      exact ⟨D, hD.trans (by rw [hunion]), hDc, hDa⟩

/- Section 4: Conjunct 2 — Two affine subsets with distinct sums -/

private lemma exists_two_aff_four {X : Finset ℤ} (hX : 5 ≤ X.card) :
    ∃ D ⊆ X, ∃ E ⊆ X, D.card = 4 ∧ E.card = 4 ∧ Aff D ∧ Aff E ∧ D.sum id ≠ E.sum id := by
  obtain ⟨X₀, X₁, q, r, hq, hX₀, hX₁, hdisj, hunion, _, hX₁ne, hle, h0, h1⟩ :=
    two_adic_split (by omega : 2 ≤ X.card)
  have hcard : X₀.card + X₁.card = X.card := by rw [← card_union_of_disjoint hdisj, hunion]
  by_cases h2 : 2 ≤ X₁.card
  · obtain ⟨F, hF, hFc⟩ := exists_subset_card_eq (show 3 ≤ X₀.card by omega)
    obtain ⟨a₁, ha₁, a₂, ha₂, hne⟩ := one_lt_card.mp (show 1 < X₁.card by omega)
    have hFaff := aff_of_card_le_three (by omega : F.card ≤ 3)
    obtain ⟨hn1, haff1⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF hx)) (h1 a₁ ha₁) hFaff
    obtain ⟨hn2, haff2⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF hx)) (h1 a₂ ha₂) hFaff
    refine ⟨insert a₁ F, insert_subset (hX₁ ha₁) (hF.trans hX₀),
      insert a₂ F, insert_subset (hX₁ ha₂) (hF.trans hX₀),
      by rw [card_insert_of_notMem hn1, hFc], by rw [card_insert_of_notMem hn2, hFc],
      haff1, haff2, ?_⟩
    rw [sum_insert hn1, sum_insert hn2]
    simp only [id_eq]
    omega
  · obtain ⟨a, ha⟩ := hX₁ne
    obtain ⟨G, hG, hGc⟩ := exists_subset_card_eq (show 4 ≤ X₀.card by omega)
    obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := one_lt_card.mp (show 1 < G.card by omega)
    let F₁ := G.erase x₁
    let F₂ := G.erase x₂
    have hF₁c : F₁.card = 3 := by rw [card_erase_of_mem hx₁, hGc]
    have hF₂c : F₂.card = 3 := by rw [card_erase_of_mem hx₂, hGc]
    have hF₁ : F₁ ⊆ X₀ := (erase_subset _ _).trans hG
    have hF₂ : F₂ ⊆ X₀ := (erase_subset _ _).trans hG
    obtain ⟨hn1, haff1⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF₁ hx)) (h1 a ha)
      (aff_of_card_le_three (by omega))
    obtain ⟨hn2, haff2⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF₂ hx)) (h1 a ha)
      (aff_of_card_le_three (by omega))
    have hs1 := sum_erase_add G id hx₁
    have hs2 := sum_erase_add G id hx₂
    refine ⟨insert a F₁, insert_subset (hX₁ ha) (hF₁.trans hX₀),
      insert a F₂, insert_subset (hX₁ ha) (hF₂.trans hX₀),
      by rw [card_insert_of_notMem hn1, hF₁c], by rw [card_insert_of_notMem hn2, hF₂c],
      haff1, haff2, ?_⟩
    rw [sum_insert hn1, sum_insert hn2]
    dsimp only [F₁, F₂]
    simp only [id_eq] at hs1 hs2 ⊢
    omega

private lemma exists_two_aff_five {X : Finset ℤ} (hX : 9 ≤ X.card) :
    ∃ D ⊆ X, ∃ E ⊆ X, D.card = 5 ∧ E.card = 5 ∧ Aff D ∧ Aff E ∧ D.sum id ≠ E.sum id := by
  obtain ⟨X₀, X₁, q, r, hq, hX₀, hX₁, hdisj, hunion, _, hX₁ne, hle, h0, h1⟩ :=
    two_adic_split (by omega : 2 ≤ X.card)
  have hcard : X₀.card + X₁.card = X.card := by rw [← card_union_of_disjoint hdisj, hunion]
  by_cases h2 : 2 ≤ X₁.card
  · obtain ⟨F, hF, hFc, hFaff⟩ := exists_aff_four (show 5 ≤ X₀.card by omega)
    obtain ⟨a₁, ha₁, a₂, ha₂, hne⟩ := one_lt_card.mp (show 1 < X₁.card by omega)
    obtain ⟨hn1, haff1⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF hx)) (h1 a₁ ha₁) hFaff
    obtain ⟨hn2, haff2⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF hx)) (h1 a₂ ha₂) hFaff
    refine ⟨insert a₁ F, insert_subset (hX₁ ha₁) (hF.trans hX₀),
      insert a₂ F, insert_subset (hX₁ ha₂) (hF.trans hX₀),
      by rw [card_insert_of_notMem hn1, hFc], by rw [card_insert_of_notMem hn2, hFc],
      haff1, haff2, ?_⟩
    rw [sum_insert hn1, sum_insert hn2]
    simp only [id_eq]
    omega
  · obtain ⟨a, ha⟩ := hX₁ne
    obtain ⟨F₁, hF₁, F₂, hF₂, hF₁c, hF₂c, hF₁a, hF₂a, hFsum⟩ :=
      exists_two_aff_four (show 5 ≤ X₀.card by omega)
    obtain ⟨hn1, haff1⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF₁ hx)) (h1 a ha) hF₁a
    obtain ⟨hn2, haff2⟩ := aff_insert_of_split hq (fun x hx ↦ h0 x (hF₂ hx)) (h1 a ha) hF₂a
    refine ⟨insert a F₁, insert_subset (hX₁ ha) (hF₁.trans hX₀),
      insert a F₂, insert_subset (hX₁ ha) (hF₂.trans hX₀),
      by rw [card_insert_of_notMem hn1, hF₁c], by rw [card_insert_of_notMem hn2, hF₂c],
      haff1, haff2, ?_⟩
    rw [sum_insert hn1, sum_insert hn2]
    simp only [id_eq] at hFsum ⊢
    omega

/- Section 5: Conjunct 3 — Common triple subsums -/

private lemma triples_eq_image {F : Finset ℤ} (hc : F.card = 4) :
    Triples F = F.image (fun x ↦ F.sum id - x) := by
  ext b
  constructor
  · intro hb
    obtain ⟨T, hT, heq⟩ := mem_image.mp hb
    obtain ⟨ht, htc⟩ := mem_powersetCard.mp hT
    have hcard := card_sdiff_add_card_eq_card ht
    obtain ⟨x, hx⟩ := card_eq_one.mp (show (F \ T).card = 1 by omega)
    have hxf : x ∈ F := (mem_sdiff.mp (hx ▸ mem_singleton_self x)).1
    have htf : T = F.erase x := by
      ext y
      constructor
      · intro hy
        refine mem_erase.mpr ⟨?_, ht hy⟩
        rintro rfl
        exact (mem_sdiff.mp (hx ▸ mem_singleton_self y)).2 hy
      · intro hy
        by_contra h
        have hm : y ∈ F \ T := mem_sdiff.mpr ⟨(mem_erase.mp hy).2, h⟩
        rw [hx, mem_singleton] at hm
        exact (mem_erase.mp hy).1 hm
    have hs : (F.erase x).sum id + x = F.sum id := sum_erase_add F id hxf
    refine mem_image.mpr ⟨x, hxf, ?_⟩
    rw [htf] at heq
    omega
  · intro hb
    obtain ⟨x, hx, heq⟩ := mem_image.mp hb
    have hs : (F.erase x).sum id + x = F.sum id := sum_erase_add F id hx
    refine mem_image.mpr ⟨F.erase x, mem_powersetCard.mpr ⟨erase_subset _ _, ?_⟩, ?_⟩
    · rw [card_erase_of_mem hx, hc]
    · omega

private lemma triples_card_sum {F : Finset ℤ} (hc : F.card = 4) :
    (Triples F).card = 4 ∧ (Triples F).sum id = 3 * F.sum id := by
  have hinj : Set.InjOn (fun x : ℤ ↦ F.sum id - x) F := fun _ _ _ _ h ↦ sub_right_inj.mp h
  rw [triples_eq_image hc]
  refine ⟨by rw [card_image_of_injOn hinj, hc], ?_⟩
  rw [sum_image hinj]
  change (∑ x ∈ F, (F.sum id - x)) = 3 * F.sum id
  rw [sum_sub_distrib, sum_const, hc]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  change 4 * F.sum id - F.sum id = 3 * F.sum id
  ring

private lemma common_triples_le_three {X W : Finset ℤ} (hX : 5 ≤ X.card)
    (hW : ∀ F ⊆ X, F.card = 4 → Aff F → W ⊆ Triples F) : W.card ≤ 3 := by
  obtain ⟨F₁, hF₁, F₂, hF₂, hF₁c, hF₂c, hF₁a, hF₂a, hne⟩ := exists_two_aff_four hX
  have h1 := hW F₁ hF₁ hF₁c hF₁a
  have h2 := hW F₂ hF₂ hF₂c hF₂a
  obtain ⟨hc1, hs1⟩ := triples_card_sum hF₁c
  obtain ⟨hc2, hs2⟩ := triples_card_sum hF₂c
  have hTne : Triples F₁ ≠ Triples F₂ := fun h ↦ hne (by rw [h] at hs1; omega)
  by_contra hbig
  have hle := card_le_card h1
  have heq1 : W = Triples F₁ := eq_of_subset_of_card_le h1 (by omega)
  have heq2 : W = Triples F₂ := eq_of_subset_of_card_le h2 (by omega)
  exact hTne (heq1.symm.trans heq2)

open Classical in
private lemma five_has_two_aff_four {Z : Finset ℤ} (hZ : Z.card = 5) :
    2 ≤ ((Z.powersetCard 4).filter Aff).card := by
  classical
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, rfl⟩ := finset_card_five_sorted hZ
  let F₁ : Finset ℤ := {a, b, c, e}
  let F₂ : Finset ℤ := {a, b, d, e}
  let F₃ : Finset ℤ := {a, c, d, e}
  have hF₁c : F₁.card = 4 := by
    simp [F₁, show a ≠ b by omega, show a ≠ c by omega, show a ≠ e by omega,
      show b ≠ c by omega, show b ≠ e by omega, show c ≠ e by omega]
  have hF₂c : F₂.card = 4 := by
    simp [F₂, show a ≠ b by omega, show a ≠ d by omega, show a ≠ e by omega,
      show b ≠ d by omega, show b ≠ e by omega, show d ≠ e by omega]
  have hF₃c : F₃.card = 4 := by
    simp [F₃, show a ≠ c by omega, show a ≠ d by omega, show a ≠ e by omega,
      show c ≠ d by omega, show c ≠ e by omega, show d ≠ e by omega]
  have hF₁sub : F₁ ⊆ {a, b, c, d, e} := by
    intro x hx; simp only [F₁, mem_insert, mem_singleton] at hx ⊢; tauto
  have hF₂sub : F₂ ⊆ {a, b, c, d, e} := by
    intro x hx; simp only [F₂, mem_insert, mem_singleton] at hx ⊢; tauto
  have hF₃sub : F₃ ⊆ {a, b, c, d, e} := by
    intro x hx; simp only [F₃, mem_insert, mem_singleton] at hx ⊢; tauto
  have h12 : F₁ ≠ F₂ := by
    intro h
    have : c ∈ F₂ := h ▸ (by simp [F₁])
    simp only [F₂, mem_insert, mem_singleton] at this
    omega
  have h13 : F₁ ≠ F₃ := by
    intro h
    have : b ∈ F₃ := h ▸ (by simp [F₁])
    simp only [F₃, mem_insert, mem_singleton] at this
    omega
  have h23 : F₂ ≠ F₃ := by
    intro h
    have : b ∈ F₃ := h ▸ (by simp [F₂])
    simp only [F₃, mem_insert, mem_singleton] at this
    omega
  have haff1 : a + e ≠ b + c → Aff F₁ := (aff_four_iff hab hbc (by omega)).mpr
  have haff2 : a + e ≠ b + d → Aff F₂ := (aff_four_iff hab (by omega) hde).mpr
  have haff3 : a + e ≠ c + d → Aff F₃ := (aff_four_iff (by omega) hcd hde).mpr
  have mem_of {F : Finset ℤ} (hs : F ⊆ {a, b, c, d, e}) (hc : F.card = 4) (ha : Aff F) :
      F ∈ (({a, b, c, d, e} : Finset ℤ).powersetCard 4).filter Aff :=
    mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hs, hc⟩, ha⟩
  by_cases h : a + e = b + c
  · have hsub : ({F₂, F₃} : Finset (Finset ℤ)) ⊆
        (({a, b, c, d, e} : Finset ℤ).powersetCard 4).filter Aff := by
      intro F hF
      rcases mem_insert.mp hF with rfl | hF
      · exact mem_of hF₂sub hF₂c (haff2 (by omega))
      · rw [mem_singleton.mp hF]; exact mem_of hF₃sub hF₃c (haff3 (by omega))
    have := card_le_card hsub
    rw [card_pair h23] at this
    exact this
  · by_cases h' : a + e = b + d
    · have hsub : ({F₁, F₃} : Finset (Finset ℤ)) ⊆
          (({a, b, c, d, e} : Finset ℤ).powersetCard 4).filter Aff := by
        intro F hF
        rcases mem_insert.mp hF with rfl | hF
        · exact mem_of hF₁sub hF₁c (haff1 h)
        · rw [mem_singleton.mp hF]; exact mem_of hF₃sub hF₃c (haff3 (by omega))
      have := card_le_card hsub
      rw [card_pair h13] at this
      exact this
    · have hsub : ({F₁, F₂} : Finset (Finset ℤ)) ⊆
          (({a, b, c, d, e} : Finset ℤ).powersetCard 4).filter Aff := by
        intro F hF
        rcases mem_insert.mp hF with rfl | hF
        · exact mem_of hF₁sub hF₁c (haff1 h)
        · rw [mem_singleton.mp hF]; exact mem_of hF₂sub hF₂c (haff2 h')
      have := card_le_card hsub
      rw [card_pair h12] at this
      exact this

open Classical in
private lemma six_has_six_aff_four {Y : Finset ℤ} (hY : Y.card = 6) :
    6 ≤ ((Y.powersetCard 4).filter Aff).card := by
  classical
  let A := (Y.powersetCard 4).filter Aff
  let B := Y.powersetCard 5
  have hleft : 12 ≤ ∑ Z ∈ B, (A.filter (fun F ↦ F ⊆ Z)).card := by
    have h1 : ∀ Z ∈ B, 2 ≤ (A.filter (fun F ↦ F ⊆ Z)).card := by
      intro Z hZ
      obtain ⟨hZY, hZc⟩ := mem_powersetCard.mp hZ
      have heq : A.filter (fun F ↦ F ⊆ Z) = (Z.powersetCard 4).filter Aff := by
        ext F
        simp only [A, mem_filter, mem_powersetCard]
        constructor
        · rintro ⟨⟨⟨_, hFc⟩, hFa⟩, hFZ⟩
          exact ⟨⟨hFZ, hFc⟩, hFa⟩
        · rintro ⟨⟨hFZ, hFc⟩, hFa⟩
          exact ⟨⟨⟨hFZ.trans hZY, hFc⟩, hFa⟩, hFZ⟩
      rw [heq]
      exact five_has_two_aff_four hZc
    have hsum := sum_le_sum h1
    rw [sum_const, smul_eq_mul] at hsum
    have hBc : B.card = 6 := by
      dsimp only [B]
      rw [card_powersetCard, hY]
      decide
    rw [hBc] at hsum
    omega
  have hright : ∑ F ∈ A, (B.filter (fun Z ↦ F ⊆ Z)).card = 2 * A.card := by
    have h2 : ∀ F ∈ A, (B.filter (fun Z ↦ F ⊆ Z)).card = 2 := by
      intro F hF
      obtain ⟨hFp, _⟩ := mem_filter.mp hF
      obtain ⟨hFY, hFc⟩ := mem_powersetCard.mp hFp
      have hbij : B.filter (fun Z ↦ F ⊆ Z) = (Y \ F).image (fun y ↦ insert y F) := by
        ext Z
        simp only [B, mem_filter, mem_powersetCard, mem_image, mem_sdiff]
        constructor
        · rintro ⟨⟨hZY, hZc⟩, hFZ⟩
          have hcard := card_sdiff_add_card_eq_card hFZ
          obtain ⟨y, hy⟩ := card_eq_one.mp (show (Z \ F).card = 1 by omega)
          have hyZ : y ∈ Z := (mem_sdiff.mp (hy ▸ mem_singleton_self y)).1
          have hyF : y ∉ F := (mem_sdiff.mp (hy ▸ mem_singleton_self y)).2
          refine ⟨y, ⟨hZY hyZ, hyF⟩, ?_⟩
          ext z
          simp only [mem_insert]
          constructor
          · rintro (rfl | hz)
            · exact hyZ
            · exact hFZ hz
          · intro hz
            by_cases hzF : z ∈ F
            · exact Or.inr hzF
            · left
              have : z ∈ Z \ F := mem_sdiff.mpr ⟨hz, hzF⟩
              rw [hy, mem_singleton] at this
              exact this
        · rintro ⟨y, ⟨hyY, hyF⟩, rfl⟩
          exact ⟨⟨insert_subset hyY hFY, by rw [card_insert_of_notMem hyF, hFc]⟩, subset_insert y F⟩
      rw [hbij, card_image_of_injOn]
      · have := card_sdiff_add_card_eq_card hFY
        omega
      · intro y₁ hy₁ y₂ hy₂ heq
        have hy₁F : y₁ ∉ F := (mem_sdiff.mp hy₁).2
        have heq' : insert y₁ F = insert y₂ F := heq
        have : y₁ ∈ insert y₂ F := heq' ▸ mem_insert_self y₁ F
        exact (mem_insert.mp this).resolve_right hy₁F
    rw [sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]
  have hswap : ∑ Z ∈ B, (A.filter (fun F ↦ F ⊆ Z)).card =
      ∑ F ∈ A, (B.filter (fun Z ↦ F ⊆ Z)).card := by
    simp only [card_filter]
    rw [sum_comm]
  change 6 ≤ A.card
  omega

private lemma common_triples_le_two {X W : Finset ℤ} (hX : 6 ≤ X.card)
    (hW : ∀ F ⊆ X, F.card = 4 → Aff F → W ⊆ Triples F) : W.card ≤ 2 := by
  classical
  by_contra hbig
  obtain ⟨Y, hYX, hYc⟩ := exists_subset_card_eq hX
  obtain ⟨W₃, hW₃W, hW₃c⟩ := exists_subset_card_eq (show 3 ≤ W.card by omega)
  obtain ⟨w₁, w₂, w₃, hw12, hw23, hW₃eq⟩ := finset_card_three_sorted hW₃c
  have hw1 : w₁ ∈ W := hW₃W (hW₃eq ▸ (by simp))
  have hw2 : w₂ ∈ W := hW₃W (hW₃eq ▸ (by simp))
  have hw3 : w₃ ∈ W := hW₃W (hW₃eq ▸ (by simp))
  let A := (Y.powersetCard 4).filter Aff
  have hA6 : 6 ≤ A.card := six_has_six_aff_four hYc
  have hYne : Y.Nonempty := card_pos.mp (by omega)
  let m₁ := Y.max' hYne
  have hm₁ : m₁ ∈ Y := max'_mem Y hYne
  have hY1c : (Y.erase m₁).card = 5 := by rw [card_erase_of_mem hm₁, hYc]
  have hY1ne : (Y.erase m₁).Nonempty := card_pos.mp (by omega)
  let m₂ := (Y.erase m₁).max' hY1ne
  have hm₂ : m₂ ∈ Y.erase m₁ := max'_mem (Y.erase m₁) hY1ne
  let Y' := (Y.erase m₁).erase m₂
  have hY'c : Y'.card = 4 := by rw [card_erase_of_mem hm₂, hY1c]
  have hmem_F : ∀ F ∈ A, ∀ w ∈ W, F.sum id - w ∈ F := by
    intro F hF w hw
    obtain ⟨hFp, hFa⟩ := mem_filter.mp hF
    obtain ⟨hFY, hFc⟩ := mem_powersetCard.mp hFp
    have hwt : w ∈ Triples F := hW F (hFY.trans hYX) hFc hFa hw
    rw [triples_eq_image hFc] at hwt
    obtain ⟨x, hxF, hxw⟩ := mem_image.mp hwt
    have : F.sum id - w = x := by omega
    rw [this]
    exact hxF
  have hmaps : ∀ F ∈ A, F.sum id - w₃ ∈ Y' := by
    intro F hF
    have hFY : F ⊆ Y := (mem_powersetCard.mp (mem_filter.mp hF).1).1
    have hx₁ : F.sum id - w₁ ∈ Y := hFY (hmem_F F hF w₁ hw1)
    have hx₂ : F.sum id - w₂ ∈ Y := hFY (hmem_F F hF w₂ hw2)
    have hx₃ : F.sum id - w₃ ∈ Y := hFY (hmem_F F hF w₃ hw3)
    have hlt1 : F.sum id - w₃ < m₁ := lt_of_lt_of_le (by omega) (le_max' Y _ hx₁)
    have hx₂_ne : F.sum id - w₂ ≠ m₁ :=
      ne_of_lt (lt_of_lt_of_le (by omega) (le_max' Y _ hx₁))
    have hx₂' : F.sum id - w₂ ∈ Y.erase m₁ := mem_erase.mpr ⟨hx₂_ne, hx₂⟩
    have hlt2 : F.sum id - w₃ < m₂ := lt_of_lt_of_le (by omega) (le_max' (Y.erase m₁) _ hx₂')
    exact mem_erase.mpr ⟨ne_of_lt hlt2, mem_erase.mpr ⟨ne_of_lt hlt1, hx₃⟩⟩
  have hinj : Set.InjOn (fun F : Finset ℤ ↦ F.sum id - w₃) A := by
    intro F hF G hG heq
    dsimp only at heq
    have hsum_eq : F.sum id = G.sum id := by omega
    have hFc : F.card = 4 := (mem_powersetCard.mp (mem_filter.mp hF).1).2
    have hGc : G.card = 4 := (mem_powersetCard.mp (mem_filter.mp hG).1).2
    let x₁ := F.sum id - w₁
    let x₂ := F.sum id - w₂
    let x₃ := F.sum id - w₃
    let T : Finset ℤ := {x₁, x₂, x₃}
    have hTF : T ⊆ F := by
      intro z hz
      simp only [T, mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hmem_F F hF w₁ hw1
      · exact hmem_F F hF w₂ hw2
      · exact hmem_F F hF w₃ hw3
    have hTG : T ⊆ G := by
      intro z hz
      simp only [T, mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · dsimp only [x₁]; rw [hsum_eq]; exact hmem_F G hG w₁ hw1
      · dsimp only [x₂]; rw [hsum_eq]; exact hmem_F G hG w₂ hw2
      · dsimp only [x₃]; rw [hsum_eq]; exact hmem_F G hG w₃ hw3
    have h12 : x₁ ≠ x₂ := by dsimp only [x₁, x₂]; omega
    have h13 : x₁ ≠ x₃ := by dsimp only [x₁, x₃]; omega
    have h23 : x₂ ≠ x₃ := by dsimp only [x₂, x₃]; omega
    have hTc : T.card = 3 := by simp [T, h12, h13, h23]
    have hFdiff := card_sdiff_add_card_eq_card hTF
    have hGdiff := card_sdiff_add_card_eq_card hTG
    obtain ⟨u, hu⟩ := card_eq_one.mp (show (F \ T).card = 1 by omega)
    obtain ⟨v, hv⟩ := card_eq_one.mp (show (G \ T).card = 1 by omega)
    have hFu : F = insert u T := by
      rw [← sdiff_union_of_subset hTF, hu, singleton_union]
    have hGv : G = insert v T := by
      rw [← sdiff_union_of_subset hTG, hv, singleton_union]
    have huT : u ∉ T := (mem_sdiff.mp (hu ▸ mem_singleton_self u)).2
    have hvT : v ∉ T := (mem_sdiff.mp (hv ▸ mem_singleton_self v)).2
    have hsu : F.sum id = u + T.sum id := by
      rw [hFu, sum_insert huT]; rfl
    have hsv : G.sum id = v + T.sum id := by
      rw [hGv, sum_insert hvT]; rfl
    have huv : u = v := by omega
    rw [hFu, hGv, huv]
  have hle : A.card ≤ Y'.card := by
    rw [← card_image_of_injOn hinj]
    exact card_le_card (image_subset_iff.mpr hmaps)
  omega

end Erdos963H2

theorem OMA.solution : OMA.R_Erdos963_erdos_963_parts_ii_R1.H2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro X k hk
    rcases hk with ⟨rfl, hX⟩ | ⟨rfl, hX⟩ | ⟨rfl, hX⟩
    · exact Erdos963H2.exists_aff_four hX
    · exact Erdos963H2.exists_aff_five hX
    · exact Erdos963H2.exists_aff_six hX
  · intro X k hk
    rcases hk with ⟨rfl, hX⟩ | ⟨rfl, hX⟩
    · exact Erdos963H2.exists_two_aff_four hX
    · exact Erdos963H2.exists_two_aff_five hX
  · intro X W hX hW
    by_cases h6 : 6 ≤ X.card
    · rw [if_pos h6]
      exact Erdos963H2.common_triples_le_two h6 hW
    · rw [if_neg h6]
      exact Erdos963H2.common_triples_le_three hX hW
