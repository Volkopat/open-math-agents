import OMAReductions.R_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1

/-!
# Proof of `Erdos601.erdos_601.variants.erdos_hajnal_milner_1970.R1.H1`

We prove Erdős–Hajnal–Milner (1970), Theorem 5 for multiples of `ω_ 1`:
for every ordinal `γ` with `ω_ 1 * γ < ω_ 1 ^ (ω + 2)` and every finite set mapping
`F : (ω_ 1 * γ).ToType → Finset (ω_ 1 * γ).ToType` with `∀ x, x ∉ F x`, there exists
an `F`-free subset `s ⊆ (ω_ 1 * γ).ToType` of order type `ω_ 1 * γ`.

Proof outline:
1. **Clubs, stationary sets, Fodor's lemma, and Ulam's matrix on `ω_ 1`**:
   We define closed unbounded (`IsClub`) and stationary (`IsStationary`) subsets of
   `W1 := (ω_ 1).ToType`, prove countable club intersection, Fodor's pressing down lemma
   via diagonal intersection, and Ulam's matrix giving `ℵ₁` pairwise disjoint stationary
   subsets of `W1`.
2. **Miracle partition lemma for finite powers `ω_ 1 ^ r`**:
   For any `r : ℕ` and any map `B : (ω_ 1 ^ r).ToType → Finset W1`, only finitely many
   `ζ : W1` fail to admit an order-embedding of `(ω_ 1 ^ r).ToType` avoiding `ζ ∈ B x`.
3. **Countable disjoint union engine (`free_set_countable_pow_union`)**:
   For any countable family of finite powers `ω_ 1 ^ (m i)` (`1 ≤ m i`) and any finite set
   mapping `F` on `Σ i, (ω_ 1 ^ (m i)).ToType`, an `ω`-stage lifting recursion using
   `F`-closed countable filtrations, Ulam's pairwise disjoint stationary sets, Fodor +
   countable pigeonhole, and the miracle partition lemma produces an `F`-free subset
   preserving the order type `ω_ 1 ^ (m i)` on every piece simultaneously.
4. **Reordering lift for `ω_ 1 ^ (ω + 1)`**:
   Viewing `ω_ 1 ^ (ω + 1) = (∑ n, ω_ 1 ^ (n + 1)) * ω_ 1` as the countable disjoint union
   of its horizontal slices `W n ≃o ω_ 1 ^ (n + 2)` (`n : ℕ`), any subset preserving
   `ω_ 1 ^ (n + 2)` on every slice `W n` embeds `ω_ 1 ^ (ω + 1)` by diagonal transfinite
   recursion.
5. **Base-`ω_ 1` decomposition of `ω_ 1 * γ < ω_ 1 ^ (ω + 2)`**:
   Every such ordinal splits into a countable well-ordered sum of copies of `ω_ 1 ^ (ω + 1)`
   and finite powers `ω_ 1 ^ m` (`1 ≤ m`). Applying the countable union engine once and
   lifting each `ω_ 1 ^ (ω + 1)` block gives an `F`-free subset of full order type `ω_ 1 * γ`.
-/

-- Credit: @skhakim

namespace OMA.P_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1_H1

open Ordinal Cardinal Erdos601
open scoped Classical

/- ### Helper order-type lemmas -/

private def orderIso_of_relIso {α β : Type} [LinearOrder α] [LinearOrder β]
    (e : ((· < · : α → α → Prop) ≃r (· < · : β → β → Prop))) : α ≃o β where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact le_of_lt (e.map_rel_iff.mp hlt)
      · exact le_of_eq (e.injective heq)
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact le_of_lt (e.map_rel_iff.mpr hlt)
      · exact le_of_eq (congrArg e heq)

private def relEmbedding_of_orderEmbedding {α β : Type} [LinearOrder α] [LinearOrder β]
    (e : α ↪o β) : ((· < · : α → α → Prop) ↪r (· < · : β → β → Prop)) where
  toEmbedding := e.toEmbedding
  map_rel_iff' := e.lt_iff_lt

private lemma typeLT_le_of_orderEmbedding {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (e : α ↪o β) : typeLT α ≤ typeLT β :=
  Ordinal.type_le_iff'.mpr ⟨relEmbedding_of_orderEmbedding e⟩

private lemma typeLT_eq_of_orderIso {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (e : α ≃o β) : typeLT α = typeLT β :=
  le_antisymm (typeLT_le_of_orderEmbedding e.toOrderEmbedding)
    (typeLT_le_of_orderEmbedding e.symm.toOrderEmbedding)

private lemma typeLT_eq_of_emb_toType {α : Ordinal.{0}} {s : Set α.ToType}
    (e : α.ToType ↪o s) : typeLT s = α := by
  apply le_antisymm
  · have hsub : s ↪o α.ToType := ⟨⟨Subtype.val, Subtype.val_injective⟩, Iff.rfl⟩
    simpa only [Ordinal.type_toType] using typeLT_le_of_orderEmbedding hsub
  · simpa only [Ordinal.type_toType] using typeLT_le_of_orderEmbedding e

private lemma orderIso_of_typeLT_eq {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (h : typeLT α = typeLT β) : Nonempty (α ≃o β) := by
  obtain ⟨e⟩ := Ordinal.type_eq.mp h
  exact ⟨orderIso_of_relIso e⟩

private instance sumLexWellFoundedLT {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] : WellFoundedLT (α ⊕ₗ β) := by
  have hAccL : ∀ a : α, Acc (· < · : (α ⊕ₗ β) → _ → Prop) (toLex (Sum.inl a)) := fun a =>
    wellFounded_lt.induction a fun a ih =>
      Acc.intro (toLex (Sum.inl a)) fun v hv => by
        cases hv' : ofLex v with
        | inl a' =>
          have hlt : a' < a := by
            have h : Sum.Lex (· < ·) (· < ·) (ofLex v) (Sum.inl a) := hv
            rw [hv'] at h; cases h; assumption
          have hvEq : v = toLex (Sum.inl a') := ofLex.injective (by simp [hv'])
          rw [hvEq]; exact ih a' hlt
        | inr b' =>
          have h : Sum.Lex (· < ·) (· < ·) (ofLex v) (Sum.inl a) := hv
          rw [hv'] at h; cases h
  have hAccR : ∀ b : β, Acc (· < · : (α ⊕ₗ β) → _ → Prop) (toLex (Sum.inr b)) := fun b =>
    wellFounded_lt.induction b fun b ih =>
      Acc.intro (toLex (Sum.inr b)) fun v hv => by
        cases hv' : ofLex v with
        | inl a' =>
          have hvEq : v = toLex (Sum.inl a') := ofLex.injective (by simp [hv'])
          rw [hvEq]; exact hAccL a'
        | inr b' =>
          have hlt : b' < b := by
            have h : Sum.Lex (· < ·) (· < ·) (ofLex v) (Sum.inr b) := hv
            rw [hv'] at h; cases h; assumption
          have hvEq : v = toLex (Sum.inr b') := ofLex.injective (by simp [hv'])
          rw [hvEq]; exact ih b' hlt
  refine ⟨⟨fun u => ?_⟩⟩
  cases hu : ofLex u with
  | inl a =>
    have : u = toLex (Sum.inl a) := ofLex.injective (by simp [hu])
    rw [this]; exact hAccL a
  | inr b =>
    have : u = toLex (Sum.inr b) := ofLex.injective (by simp [hu])
    rw [this]; exact hAccR b

private lemma sumLex_lt_inl_inl {α β : Type} [LinearOrder α] [LinearOrder β] (a₁ a₂ : α) :
    (toLex (Sum.inl a₁) : α ⊕ₗ β) < toLex (Sum.inl a₂) ↔ a₁ < a₂ :=
  ⟨fun h => by cases h; assumption, fun h => Sum.Lex.inl h⟩

private lemma sumLex_lt_inr_inr {α β : Type} [LinearOrder α] [LinearOrder β] (b₁ b₂ : β) :
    (toLex (Sum.inr b₁) : α ⊕ₗ β) < toLex (Sum.inr b₂) ↔ b₁ < b₂ :=
  ⟨fun h => by cases h; assumption, fun h => Sum.Lex.inr h⟩

private lemma sumLex_lt_inl_inr {α β : Type} [LinearOrder α] [LinearOrder β] (a : α) (b : β) :
    (toLex (Sum.inl a) : α ⊕ₗ β) < toLex (Sum.inr b) :=
  Sum.Lex.sep a b

private lemma sumLex_not_lt_inr_inl {α β : Type} [LinearOrder α] [LinearOrder β] (b : β) (a : α) :
    ¬ (toLex (Sum.inr b) : α ⊕ₗ β) < toLex (Sum.inl a) :=
  fun h => by cases h

private lemma sumLex_le_inl_inl {α β : Type} [LinearOrder α] [LinearOrder β] (a₁ a₂ : α) :
    (toLex (Sum.inl a₁) : α ⊕ₗ β) ≤ toLex (Sum.inl a₂) ↔ a₁ ≤ a₂ := by
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt, sumLex_lt_inl_inl]
  simp

private lemma sumLex_le_inr_inr {α β : Type} [LinearOrder α] [LinearOrder β] (b₁ b₂ : β) :
    (toLex (Sum.inr b₁) : α ⊕ₗ β) ≤ toLex (Sum.inr b₂) ↔ b₁ ≤ b₂ := by
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt, sumLex_lt_inr_inr]
  simp

private lemma sumLex_le_inl_inr {α β : Type} [LinearOrder α] [LinearOrder β] (a : α) (b : β) :
    (toLex (Sum.inl a) : α ⊕ₗ β) ≤ toLex (Sum.inr b) :=
  le_of_lt (sumLex_lt_inl_inr a b)

private lemma sumLex_not_le_inr_inl {α β : Type} [LinearOrder α] [LinearOrder β] (b : β) (a : α) :
    ¬ (toLex (Sum.inr b) : α ⊕ₗ β) ≤ toLex (Sum.inl a) :=
  not_le_of_gt (sumLex_lt_inl_inr a b)

private lemma set_countable_iff_card_lt_aleph1 {α : Type} (s : Set α) :
    s.Countable ↔ #s < ℵ₁ := by
  rw [Cardinal.lt_aleph_one_iff, Cardinal.le_aleph0_iff_set_countable]

private lemma omega0_lt_omega1 : (ω : Ordinal.{0}) < ω_ 1 := by
  simpa only [Ordinal.omega_zero] using Ordinal.omega_lt_omega.mpr zero_lt_one

private lemma mul_toType_iso (a b : Ordinal.{0}) :
    Nonempty ((a * b).ToType ≃o (b.ToType ×ₗ a.ToType)) := by
  have h : typeLT (a * b).ToType = typeLT (b.ToType ×ₗ a.ToType) := by
    rw [Ordinal.type_toType]
    have hlex : typeLT (b.ToType ×ₗ a.ToType) =
        Ordinal.type (Prod.Lex (· < · : b.ToType → _ → Prop) (· < · : a.ToType → _ → Prop)) :=
      Ordinal.type_eq.mpr ⟨⟨ofLex, Iff.rfl⟩⟩
    rw [hlex, Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_toType]
  exact orderIso_of_typeLT_eq h

private lemma add_toType_iso (a b : Ordinal.{0}) :
    Nonempty ((a + b).ToType ≃o (a.ToType ⊕ₗ b.ToType)) := by
  have h : typeLT (a + b).ToType = typeLT (a.ToType ⊕ₗ b.ToType) := by
    rw [Ordinal.type_toType]
    have hlex : typeLT (a.ToType ⊕ₗ b.ToType) =
        Ordinal.type (Sum.Lex (· < · : a.ToType → _ → Prop) (· < · : b.ToType → _ → Prop)) :=
      Ordinal.type_eq.mpr ⟨⟨ofLex, Iff.rfl⟩⟩
    rw [hlex, Ordinal.type_sum_lex, Ordinal.type_toType, Ordinal.type_toType]
  exact orderIso_of_typeLT_eq h

private lemma typeLT_le_of_forall_Iio_lt {V : Type} [LinearOrder V] [WellFoundedLT V]
    {α : Ordinal.{0}} (h : ∀ a : V, typeLT (Set.Iio a) < α) :
    typeLT V ≤ α := by
  by_contra hgt
  push Not at hgt
  let a : V := Ordinal.enum (· < · : V → V → Prop) ⟨α, hgt⟩
  have ha_lt : typeLT (Set.Iio a) < α := h a
  have htype_eq : typeLT (Set.Iio a) = α := by
    rw [Ordinal.type_Iio_lt]
    exact Ordinal.typein_enum (· < · : V → V → Prop) hgt
  exact lt_irrefl α (htype_eq ▸ ha_lt)

/- ### Section 1: Clubs, stationary sets, Fodor's lemma, and Ulam's matrix on `ω_ 1` -/

private abbrev W1 : Type := (ω_ 1).ToType

private lemma mk_W1 : #W1 = ℵ₁ := by
  rw [Cardinal.mk_toType, Ordinal.card_omega]

private lemma w1_uncountable : ¬ Countable W1 := by
  intro h
  have hle : #W1 ≤ ℵ₀ := Cardinal.mk_le_aleph0
  rw [mk_W1] at hle
  exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hle

private lemma w1_nonempty : Nonempty W1 := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact w1_uncountable inferInstance

private noncomputable def w1Bot : W1 :=
  WellFounded.min wellFounded_lt Set.univ ⟨Classical.choice w1_nonempty, trivial⟩

private lemma w1Bot_le (x : W1) : w1Bot ≤ x :=
  not_lt.mp fun h => WellFounded.not_lt_min wellFounded_lt Set.univ trivial h

private lemma w1_Iio_countable (x : W1) : (Set.Iio x).Countable := by
  rw [set_countable_iff_card_lt_aleph1]
  have htype : typeLT (Set.Iio x) < ω_ 1 := by
    rw [Ordinal.type_Iio_lt]
    simpa only [Ordinal.type_toType] using Ordinal.typein_lt_type (· < · : W1 → W1 → Prop) x
  have hcard : #(Set.Iio x) = (typeLT (Set.Iio x)).card := (Ordinal.card_type _).symm
  rw [hcard]
  exact Cardinal.lt_omega_iff_card_lt.mp htype

private lemma w1_Iic_countable (x : W1) : (Set.Iic x).Countable := by
  have heq : Set.Iic x = insert x (Set.Iio x) := by
    ext y; simp [le_iff_eq_or_lt]
  rw [heq]
  exact (w1_Iio_countable x).insert x

private lemma w1_exists_gt_of_countable {s : Set W1} (hs : s.Countable) :
    ∃ b : W1, ∀ x ∈ s, x < b := by
  by_contra h
  push Not at h
  have hcov : (Set.univ : Set W1) ⊆ ⋃ x ∈ s, Set.Iic x := by
    intro b _
    obtain ⟨x, hxs, hbx⟩ := h b
    exact Set.mem_biUnion hxs hbx
  have hc : (Set.univ : Set W1).Countable :=
    (hs.biUnion fun x _ => w1_Iic_countable x).mono hcov
  exact w1_uncountable (Set.countable_univ_iff.mp hc)

private lemma w1_exists_gt (a : W1) : ∃ b : W1, a < b := by
  obtain ⟨b, hb⟩ := w1_exists_gt_of_countable (Set.countable_singleton a)
  exact ⟨b, hb a rfl⟩

private lemma w1_typeLT_eq_of_uncountable {s : Set W1} (hs : ¬ s.Countable) :
    typeLT s = ω_ 1 := by
  apply le_antisymm
  · have hsub : s ↪o W1 := ⟨⟨Subtype.val, Subtype.val_injective⟩, Iff.rfl⟩
    simpa only [Ordinal.type_toType] using typeLT_le_of_orderEmbedding hsub
  · by_contra hlt
    push Not at hlt
    have hcard : #s < ℵ₁ := by
      rw [← Ordinal.card_type (· < · : s → s → Prop)]
      exact Cardinal.lt_omega_iff_card_lt.mp hlt
    exact hs ((set_countable_iff_card_lt_aleph1 s).mpr hcard)

private lemma w1_uncountable_of_unbounded {s : Set W1} (hs : ∀ a : W1, ∃ b ∈ s, a < b) :
    ¬ s.Countable := by
  intro hc
  obtain ⟨b, hb⟩ := w1_exists_gt_of_countable hc
  obtain ⟨x, hxs, hbx⟩ := hs b
  exact lt_asymm hbx (hb x hxs)

private lemma w1_emb_of_uncountable {s : Set W1} (hs : ¬ s.Countable) :
    Nonempty (W1 ↪o s) := by
  obtain ⟨e⟩ := orderIso_of_typeLT_eq (α := W1) (β := s)
    (by rw [Ordinal.type_toType, w1_typeLT_eq_of_uncountable hs])
  exact ⟨e.toOrderEmbedding⟩

private noncomputable def w1Sup (s : Set W1) (hs : s.Countable) : W1 :=
  WellFounded.min wellFounded_lt {u : W1 | ∀ x ∈ s, x ≤ u} (by
    obtain ⟨b, hb⟩ := w1_exists_gt_of_countable hs
    exact ⟨b, fun x hx => le_of_lt (hb x hx)⟩)

private lemma le_w1Sup {s : Set W1} (hs : s.Countable) {x : W1} (hx : x ∈ s) :
    x ≤ w1Sup s hs :=
  WellFounded.min_mem wellFounded_lt {u : W1 | ∀ y ∈ s, y ≤ u} _ x hx

private lemma w1Sup_le {s : Set W1} (hs : s.Countable) {u : W1} (hu : ∀ x ∈ s, x ≤ u) :
    w1Sup s hs ≤ u :=
  not_lt.mp fun h => WellFounded.not_lt_min wellFounded_lt {v : W1 | ∀ x ∈ s, x ≤ v} hu h

private lemma lt_w1Sup_iff {s : Set W1} (hs : s.Countable) {a : W1} :
    a < w1Sup s hs ↔ ∃ x ∈ s, a < x := by
  constructor
  · intro h
    by_contra hall
    push Not at hall
    exact not_le_of_gt h (w1Sup_le hs hall)
  · rintro ⟨x, hxs, hax⟩
    exact lt_of_lt_of_le hax (le_w1Sup hs hxs)

private lemma w1Sup_eq_of_cofinal {s t : Set W1} (hs : s.Countable) (ht : t.Countable)
    (hst : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) (hts : ∀ y ∈ t, ∃ x ∈ s, y ≤ x) :
    w1Sup s hs = w1Sup t ht := by
  apply le_antisymm
  · refine w1Sup_le hs fun x hx => ?_
    obtain ⟨y, hyt, hxy⟩ := hst x hx
    exact hxy.trans (le_w1Sup ht hyt)
  · refine w1Sup_le ht fun y hy => ?_
    obtain ⟨x, hxs, hyx⟩ := hts y hy
    exact hyx.trans (le_w1Sup hs hxs)

/-- A closed unbounded (club) subset of `ω_ 1`. -/
private def IsClub (C : Set W1) : Prop :=
  (∀ a : W1, ∃ b ∈ C, a < b) ∧
  (∀ f : ℕ → W1, StrictMono f → (∀ n, f n ∈ C) →
    w1Sup (Set.range f) (Set.countable_range f) ∈ C)

private lemma isClub_tail (a : W1) : IsClub {x : W1 | a < x} := by
  refine ⟨fun b => ?_, fun f _ hf => ?_⟩
  · obtain ⟨c, hc⟩ := w1_exists_gt (max a b)
    exact ⟨c, lt_of_le_of_lt (le_max_left _ _) hc, lt_of_le_of_lt (le_max_right _ _) hc⟩
  · exact lt_of_lt_of_le (hf 0) (le_w1Sup (Set.countable_range f) ⟨0, rfl⟩)

private lemma isClub_lim :
    IsClub {x : W1 | (∃ y, y < x) ∧ ∀ y < x, ∃ z, y < z ∧ z < x} := by
  refine ⟨fun a => ?_, fun f hmono _ => ?_⟩
  · choose g hg using w1_exists_gt
    let seq : ℕ → W1 := Nat.rec a (fun _ x => g x)
    have hseq_mono : StrictMono seq := strictMono_nat_of_lt_succ fun n => hg (seq n)
    let L := w1Sup (Set.range seq) (Set.countable_range seq)
    refine ⟨L, ⟨⟨a, lt_of_lt_of_le (hseq_mono (by omega : 0 < 1))
        (le_w1Sup (Set.countable_range seq) ⟨1, rfl⟩)⟩, ?_⟩,
      lt_of_lt_of_le (hseq_mono (by omega : 0 < 1))
        (le_w1Sup (Set.countable_range seq) ⟨1, rfl⟩)⟩
    intro y hy
    obtain ⟨_, ⟨n, rfl⟩, hyn⟩ := (lt_w1Sup_iff _).mp hy
    exact ⟨seq (n + 1), hyn.trans (hseq_mono (Nat.lt_succ_self n)),
      lt_of_lt_of_le (hseq_mono (Nat.lt_succ_self (n + 1)))
        (le_w1Sup (Set.countable_range seq) ⟨n + 2, rfl⟩)⟩
  · refine ⟨⟨f 0, lt_of_lt_of_le (hmono (by omega : 0 < 1))
        (le_w1Sup (Set.countable_range f) ⟨1, rfl⟩)⟩, ?_⟩
    intro y hy
    obtain ⟨_, ⟨n, rfl⟩, hyn⟩ := (lt_w1Sup_iff _).mp hy
    exact ⟨f (n + 1), hyn.trans (hmono (Nat.lt_succ_self n)),
      lt_of_lt_of_le (hmono (Nat.lt_succ_self (n + 1)))
        (le_w1Sup (Set.countable_range f) ⟨n + 2, rfl⟩)⟩

private lemma isClub_iInter_nat (C : ℕ → Set W1) (hC : ∀ k, IsClub (C k)) :
    IsClub (⋂ k, C k) := by
  refine ⟨fun a => ?_, fun f hmono hf => ?_⟩
  · have next : ∀ (n : ℕ) (x : W1), ∃ y ∈ C n.unpair.1, x < y :=
      fun n x => (hC n.unpair.1).1 x
    choose g hgC hglt using next
    let seq : ℕ → W1 := Nat.rec a (fun n x => g n x)
    have hseq_mono : StrictMono seq := strictMono_nat_of_lt_succ fun n => hglt n (seq n)
    let L := w1Sup (Set.range seq) (Set.countable_range seq)
    refine ⟨L, Set.mem_iInter.mpr fun k => ?_,
      lt_of_lt_of_le (hseq_mono (by omega : 0 < 1))
        (le_w1Sup (Set.countable_range seq) ⟨1, rfl⟩)⟩
    let sub (m : ℕ) : W1 := seq (Nat.pair k m + 1)
    have hsub_mono : StrictMono sub := fun m₁ m₂ hm => by
      have hlt : Nat.pair k m₁ < Nat.pair k m₂ := by
        simp only [Nat.pair]
        split_ifs <;> nlinarith
      exact hseq_mono (show Nat.pair k m₁ + 1 < Nat.pair k m₂ + 1 by omega)
    have hsub_mem : ∀ m, sub m ∈ C k := fun m => by
      have h := hgC (Nat.pair k m) (seq (Nat.pair k m))
      simpa only [Nat.unpair_pair] using h
    have hsup_eq : L = w1Sup (Set.range sub) (Set.countable_range sub) := by
      refine w1Sup_eq_of_cofinal _ _ ?_ ?_
      · rintro _ ⟨n, rfl⟩
        exact ⟨sub n, ⟨n, rfl⟩, hseq_mono.monotone ((Nat.right_le_pair k n).trans (Nat.le_succ _))⟩
      · rintro _ ⟨m, rfl⟩
        exact ⟨seq (Nat.pair k m + 1), ⟨Nat.pair k m + 1, rfl⟩, le_rfl⟩
    rw [hsup_eq]
    exact (hC k).2 sub hsub_mono hsub_mem
  · exact Set.mem_iInter.mpr fun k => (hC k).2 f hmono fun n => Set.mem_iInter.mp (hf n) k

private lemma isClub_iInter {ι : Type} [Countable ι] (C : ι → Set W1) (hC : ∀ i, IsClub (C i)) :
    IsClub (⋂ i, C i) := by
  by_cases hne : Nonempty ι
  · obtain ⟨e, he⟩ := exists_surjective_nat ι
    have heq : (⋂ i, C i) = ⋂ n : ℕ, C (e n) := by
      ext x; simp only [Set.mem_iInter]
      exact ⟨fun h n => h (e n), fun h i => by obtain ⟨n, rfl⟩ := he i; exact h n⟩
    rw [heq]
    exact isClub_iInter_nat (fun n => C (e n)) (fun n => hC (e n))
  · rw [not_nonempty_iff] at hne
    have heq : (⋂ i, C i) = Set.univ := by ext x; simp
    rw [heq]
    exact ⟨fun a => by obtain ⟨b, hb⟩ := w1_exists_gt a; exact ⟨b, trivial, hb⟩,
      fun _ _ _ => trivial⟩

private lemma isClub_inter {C₁ C₂ : Set W1} (h₁ : IsClub C₁) (h₂ : IsClub C₂) :
    IsClub (C₁ ∩ C₂) := by
  have heq : C₁ ∩ C₂ = ⋂ b : Bool, if b then C₁ else C₂ := by
    ext x; simp [Bool.forall_bool, and_comm]
  rw [heq]
  exact isClub_iInter _ fun b => by cases b <;> assumption

/-- A stationary subset of `ω_ 1`. -/
private def IsStationary (S : Set W1) : Prop :=
  ∀ C : Set W1, IsClub C → (S ∩ C).Nonempty

private lemma isStationary_of_isClub {C : Set W1} (hC : IsClub C) : IsStationary C :=
  fun D hD => by
    obtain ⟨b, hb, _⟩ := (isClub_inter hC hD).1 w1Bot
    exact ⟨b, hb⟩

private lemma IsStationary.inter_club {S C : Set W1} (hS : IsStationary S) (hC : IsClub C) :
    IsStationary (S ∩ C) :=
  fun D hD => by
    obtain ⟨x, hxS, hxC, hxD⟩ := hS (C ∩ D) (isClub_inter hC hD)
    exact ⟨x, ⟨hxS, hxC⟩, hxD⟩

private lemma IsStationary.unbounded {S : Set W1} (hS : IsStationary S) :
    ∀ a : W1, ∃ b ∈ S, a < b :=
  fun a => by
    obtain ⟨b, hbS, hba⟩ := hS {x | a < x} (isClub_tail a)
    exact ⟨b, hbS, hba⟩

private lemma IsStationary.uncountable {S : Set W1} (hS : IsStationary S) : ¬ S.Countable :=
  w1_uncountable_of_unbounded hS.unbounded

private lemma exists_stationary_of_iUnion {ι : Type} [Countable ι] {S : ι → Set W1}
    (hS : IsStationary (⋃ i, S i)) : ∃ i, IsStationary (S i) := by
  by_contra h
  push Not at h
  have hex : ∀ i, ∃ C : Set W1, IsClub C ∧ Disjoint (S i) C := by
    intro i
    have hi := h i
    unfold IsStationary at hi
    push Not at hi
    obtain ⟨C, hC, hempty⟩ := hi
    exact ⟨C, hC, Set.disjoint_iff_inter_eq_empty.mpr hempty⟩
  choose C hC hdisj using hex
  obtain ⟨x, hxU, hxI⟩ := hS (⋂ i, C i) (isClub_iInter C hC)
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
  exact Set.disjoint_left.mp (hdisj i) hxi (Set.mem_iInter.mp hxI i)

/-- Fodor's pressing down lemma on `ω_ 1`. -/
private theorem fodor {S : Set W1} (hS : IsStationary S) (f : W1 → W1)
    (hreg : ∀ x ∈ S, f x < x) : ∃ γ : W1, IsStationary {x ∈ S | f x = γ} := by
  by_contra h
  push Not at h
  have hex : ∀ γ : W1, ∃ C : Set W1, IsClub C ∧ Disjoint {x ∈ S | f x = γ} C := by
    intro γ
    have hγ := h γ
    unfold IsStationary at hγ
    push Not at hγ
    obtain ⟨C, hC, hempty⟩ := hγ
    exact ⟨C, hC, Set.disjoint_iff_inter_eq_empty.mpr hempty⟩
  choose C hC hdisj using hex
  let D : Set W1 := {x : W1 | ∀ γ < x, x ∈ C γ}
  have hD : IsClub D := by
    refine ⟨fun a => ?_, fun g hmono hg => ?_⟩
    · have step : ∀ x : W1, ∃ y : W1, (∀ γ ≤ x, y ∈ C γ) ∧ x < y := by
        intro x
        have : Countable (Set.Iic x) := Set.countable_coe_iff.mpr (w1_Iic_countable x)
        have hclub : IsClub (⋂ γ : Set.Iic x, C γ.1) :=
          isClub_iInter (fun γ : Set.Iic x => C γ.1) (fun γ => hC γ.1)
        obtain ⟨y, hy, hxy⟩ := hclub.1 x
        exact ⟨y, fun γ hγ => Set.mem_iInter.mp hy ⟨γ, hγ⟩, hxy⟩
      choose next hnextC hnextlt using step
      let seq : ℕ → W1 := Nat.rec a (fun _ x => next x)
      have hseq_mono : StrictMono seq := strictMono_nat_of_lt_succ fun n => hnextlt (seq n)
      let L := w1Sup (Set.range seq) (Set.countable_range seq)
      refine ⟨L, ?_, lt_of_lt_of_le (hseq_mono (by omega : 0 < 1)) (le_w1Sup _ ⟨1, rfl⟩)⟩
      intro γ hγL
      obtain ⟨_, ⟨N, rfl⟩, hγN⟩ := (lt_w1Sup_iff _).mp hγL
      let tail (m : ℕ) : W1 := seq (N + 1 + m)
      have htail_mono : StrictMono tail := fun m₁ m₂ hm => hseq_mono (by omega)
      have htail_mem : ∀ m, tail m ∈ C γ := fun m => by
        change seq (N + 1 + m) ∈ C γ
        rw [show N + 1 + m = (N + m) + 1 by omega]
        exact hnextC (seq (N + m)) γ (hγN.le.trans (hseq_mono.monotone (by omega)))
      have hsup_eq : L = w1Sup (Set.range tail) (Set.countable_range tail) := by
        refine w1Sup_eq_of_cofinal _ _ ?_ ?_
        · rintro _ ⟨n, rfl⟩
          exact ⟨tail n, ⟨n, rfl⟩, hseq_mono.monotone (by omega)⟩
        · rintro _ ⟨m, rfl⟩
          exact ⟨seq (N + 1 + m), ⟨N + 1 + m, rfl⟩, le_rfl⟩
      rw [hsup_eq]
      exact (hC γ).2 tail htail_mono htail_mem
    · intro γ hγL
      obtain ⟨_, ⟨N, rfl⟩, hγN⟩ := (lt_w1Sup_iff _).mp hγL
      let tail (m : ℕ) : W1 := g (N + m)
      have htail_mono : StrictMono tail := fun m₁ m₂ hm => hmono (by omega)
      have htail_mem : ∀ m, tail m ∈ C γ := fun m =>
        hg (N + m) γ (hγN.trans_le (hmono.monotone (by omega)))
      have hsup_eq : w1Sup (Set.range g) (Set.countable_range g) =
          w1Sup (Set.range tail) (Set.countable_range tail) := by
        refine w1Sup_eq_of_cofinal _ _ ?_ ?_
        · rintro _ ⟨n, rfl⟩
          exact ⟨tail n, ⟨n, rfl⟩, hmono.monotone (by omega)⟩
        · rintro _ ⟨m, rfl⟩
          exact ⟨g (N + m), ⟨N + m, rfl⟩, le_rfl⟩
      rw [hsup_eq]
      exact (hC γ).2 tail htail_mono htail_mem
  obtain ⟨x, hxS, hxD⟩ := hS D hD
  exact Set.disjoint_left.mp (hdisj (f x)) ⟨hxS, rfl⟩ (hxD (f x) (hreg x hxS))

/-- Ulam's matrix: there exist `ℵ₁` pairwise disjoint stationary subsets of `ω_ 1`. -/
private theorem ulam_disjoint_stationary :
    ∃ T : W1 → Set W1, (∀ α, IsStationary (T α)) ∧ Pairwise (fun α β => Disjoint (T α) (T β)) := by
  have hex_inj : ∀ ξ : W1, ∃ g : Set.Iio ξ → ℕ, Function.Injective g := by
    intro ξ
    have : Countable (Set.Iio ξ) := Set.countable_coe_iff.mpr (w1_Iio_countable ξ)
    exact exists_injective_nat (Set.Iio ξ)
  choose g hg_inj using hex_inj
  let U (α : W1) (n : ℕ) : Set W1 := {ξ : W1 | ∃ h : α < ξ, g ξ ⟨α, h⟩ = n}
  have hU_stat : ∀ α : W1, ∃ n : ℕ, IsStationary (U α n) := by
    intro α
    apply exists_stationary_of_iUnion
    have hcov : (⋃ n : ℕ, U α n) = {ξ : W1 | α < ξ} := by
      ext ξ
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, U]
      exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨g ξ ⟨α, h⟩, h, rfl⟩⟩
    rw [hcov]
    exact isStationary_of_isClub (isClub_tail α)
  choose n_of hn_stat using hU_stat
  have hex_uncount : ∃ n₀ : ℕ, ¬ ({α : W1 | n_of α = n₀}).Countable := by
    by_contra hall
    push Not at hall
    have hcov : (Set.univ : Set W1) ⊆ ⋃ n : ℕ, {α : W1 | n_of α = n} :=
      fun α _ => Set.mem_iUnion.mpr ⟨n_of α, rfl⟩
    exact w1_uncountable (Set.countable_univ_iff.mp ((Set.countable_iUnion hall).mono hcov))
  obtain ⟨n₀, hn₀⟩ := hex_uncount
  obtain ⟨e⟩ := w1_emb_of_uncountable hn₀
  refine ⟨fun α => U (e α).1 n₀, fun α => ?_, fun α β hne => ?_⟩
  · have heq : n_of (e α).1 = n₀ := (e α).2
    simpa only [← heq] using hn_stat (e α).1
  · dsimp only
    rw [Set.disjoint_left]
    rintro ξ ⟨h1, hg1⟩ ⟨h2, hg2⟩
    have hval : (⟨(e α).1, h1⟩ : Set.Iio ξ) = ⟨(e β).1, h2⟩ := hg_inj ξ (hg1.trans hg2.symm)
    exact hne (e.injective (Subtype.ext (congrArg (fun z : Set.Iio ξ => z.1) hval)))

/- ### Section 2: Finite powers `ω_ 1 ^ n` and the Miracle Partition Lemma -/

private abbrev PowW1 (n : ℕ) : Type := (ω_ 1 ^ (n : Ordinal.{0})).ToType

private noncomputable def powW1Cast {a b : ℕ} (h : a = b) : PowW1 a ≃o PowW1 b := by
  subst h; exact OrderIso.refl _

private lemma powW1Cast_apply {a b : ℕ} (h : a = b) (x : PowW1 a) :
    powW1Cast h x = cast (by rw [h]) x := by
  subst h; rfl

private lemma powW1Cast_symm_apply {a b : ℕ} (h : a = b) (x : PowW1 b) :
    (powW1Cast h).symm x = cast (by rw [h]) x := by
  subst h; rfl

private lemma powW1_zero_iso : Nonempty (PowW1 0 ≃o Unit) := by
  have hunit : typeLT Unit = 1 := by
    have e : Unit ≃o Fin 1 :=
      { toFun := fun _ => 0, invFun := fun _ => (), left_inv := fun _ => rfl,
        right_inv := fun i => Fin.ext (by omega), map_rel_iff' := fun {_ _} => by simp }
    rw [typeLT_eq_of_orderIso e, Ordinal.type_fin, Nat.cast_one]
  have h : typeLT (PowW1 0) = typeLT Unit := by
    rw [Ordinal.type_toType, Nat.cast_zero, Ordinal.opow_zero, hunit]
  exact orderIso_of_typeLT_eq h

private lemma powW1_one_iso : Nonempty (PowW1 1 ≃o W1) := by
  have h : typeLT (PowW1 1) = typeLT W1 := by
    rw [Ordinal.type_toType, Ordinal.type_toType, Nat.cast_one, Ordinal.opow_one]
  exact orderIso_of_typeLT_eq h

private lemma powW1_succ_iso (n : ℕ) :
    Nonempty (PowW1 (n + 1) ≃o (W1 ×ₗ PowW1 n)) := by
  have heq : (ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0})) = (ω_ 1 ^ (n : Ordinal.{0})) * ω_ 1 := by
    rw [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one]
  have h : typeLT (PowW1 (n + 1)) = typeLT (W1 ×ₗ PowW1 n) := by
    rw [Ordinal.type_toType, heq]
    have hlex : typeLT (W1 ×ₗ PowW1 n) =
        Ordinal.type (Prod.Lex (· < · : W1 → _ → Prop) (· < · : PowW1 n → _ → Prop)) :=
      Ordinal.type_eq.mpr ⟨⟨ofLex, Iff.rfl⟩⟩
    rw [hlex, Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_toType]
  exact orderIso_of_typeLT_eq h

private lemma powW1_succ_left_iso (n : ℕ) :
    Nonempty (PowW1 (n + 1) ≃o (PowW1 n ×ₗ W1)) := by
  have heq : (ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0})) = ω_ 1 * (ω_ 1 ^ (n : Ordinal.{0})) := by
    have h1n : ((n + 1 : ℕ) : Ordinal.{0}) = (1 : Ordinal.{0}) + (n : Ordinal.{0}) := by
      rw [add_comm, Nat.cast_add, Nat.cast_one]
    rw [h1n, Ordinal.opow_add, Ordinal.opow_one]
  have h : typeLT (PowW1 (n + 1)) = typeLT (PowW1 n ×ₗ W1) := by
    rw [Ordinal.type_toType, heq]
    have hlex : typeLT (PowW1 n ×ₗ W1) =
        Ordinal.type (Prod.Lex (· < · : PowW1 n → _ → Prop) (· < · : W1 → _ → Prop)) :=
      Ordinal.type_eq.mpr ⟨⟨ofLex, Iff.rfl⟩⟩
    rw [hlex, Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_toType]
  exact orderIso_of_typeLT_eq h

private lemma powW1_card_le (n : ℕ) : #(PowW1 n) ≤ ℵ₁ := by
  induction n with
  | zero =>
    obtain ⟨e⟩ := powW1_zero_iso
    rw [Cardinal.mk_congr e.toEquiv, Cardinal.mk_punit]
    exact (Cardinal.one_lt_aleph0.le).trans Cardinal.aleph0_lt_aleph_one.le
  | succ n ih =>
    obtain ⟨e⟩ := powW1_succ_iso n
    rw [Cardinal.mk_congr e.toEquiv]
    have hmk : #(W1 ×ₗ PowW1 n) = #W1 * #(PowW1 n) := by
      rw [Cardinal.mk_congr ofLex, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    rw [hmk, mk_W1]
    calc ℵ₁ * #(PowW1 n) ≤ ℵ₁ * ℵ₁ := by gcongr
      _ = ℵ₁ := Cardinal.mul_eq_self Cardinal.aleph0_lt_aleph_one.le

private lemma powW1_emb_sdiff_countable (n : ℕ) (hn : 1 ≤ n) (D : Set (PowW1 n))
    (hD : D.Countable) : Nonempty (PowW1 n ↪o {x : PowW1 n // x ∉ D}) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨iso⟩ := powW1_succ_left_iso m
  have hfiber : ∀ q : PowW1 m, Nonempty (W1 ↪o {δ : W1 // iso.symm (toLex (q, δ)) ∉ D}) := by
    intro q
    apply w1_emb_of_uncountable
    intro hc
    have hbad : ({δ : W1 | iso.symm (toLex (q, δ)) ∈ D}).Countable := by
      refine hD.preimage fun δ₁ δ₂ h => ?_
      have h' := congrArg (fun z => (ofLex (iso z)).2) h
      simpa using h'
    have hall : (Set.univ : Set W1) ⊆
        {δ : W1 | iso.symm (toLex (q, δ)) ∉ D} ∪ {δ : W1 | iso.symm (toLex (q, δ)) ∈ D} := by
      intro δ _; by_cases h : iso.symm (toLex (q, δ)) ∈ D
      · exact Or.inr h
      · exact Or.inl h
    exact w1_uncountable (Set.countable_univ_iff.mp ((hc.union hbad).mono hall))
  let emb (q : PowW1 m) := Classical.choice (hfiber q)
  refine ⟨⟨⟨fun x =>
      let p := ofLex (iso x)
      ⟨iso.symm (toLex (p.1, (emb p.1 p.2).1)), (emb p.1 p.2).2⟩, ?_⟩, ?_⟩⟩
  · intro x₁ x₂ h
    have h' := congrArg (fun z => ofLex (iso z.1)) h
    simp only [OrderIso.apply_symm_apply, ofLex_toLex, Prod.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    have h2' : (ofLex (iso x₁)).2 = (ofLex (iso x₂)).2 := by
      rw [← h1] at h2
      exact (emb (ofLex (iso x₁)).1).injective (Subtype.ext h2)
    have hpair : ofLex (iso x₁) = ofLex (iso x₂) := Prod.ext h1 h2'
    exact iso.injective (ofLex.injective hpair)
  · intro x₁ x₂
    change iso.symm (toLex ((ofLex (iso x₁)).1, (emb (ofLex (iso x₁)).1 (ofLex (iso x₁)).2).1)) ≤
        iso.symm (toLex ((ofLex (iso x₂)).1, (emb (ofLex (iso x₂)).1 (ofLex (iso x₂)).2).1)) ↔
        x₁ ≤ x₂
    rw [iso.symm.le_iff_le]
    have hiff : ∀ a b : PowW1 m × W1,
        toLex a ≤ toLex b ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) :=
      fun a b => Prod.Lex.le_iff
    rw [hiff]
    have hiff2 : x₁ ≤ x₂ ↔
        (ofLex (iso x₁)).1 < (ofLex (iso x₂)).1 ∨
        ((ofLex (iso x₁)).1 = (ofLex (iso x₂)).1 ∧ (ofLex (iso x₁)).2 ≤ (ofLex (iso x₂)).2) := by
      rw [← iso.le_iff_le]
      simpa using hiff (ofLex (iso x₁)) (ofLex (iso x₂))
    rw [hiff2]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · refine Or.inr ⟨h1, ?_⟩
        rw [← h1] at h2
        exact (emb (ofLex (iso x₁)).1).le_iff_le.mp h2
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · refine Or.inr ⟨h1, ?_⟩
        rw [← h1]
        exact (emb (ofLex (iso x₁)).1).le_iff_le.mpr h2

/-- Partition any uncountable subset of `W1` into `ℵ₁` pairwise disjoint uncountable subsets. -/
private lemma w1_partition_aleph1 {Y : Set W1} (hY : ¬ Y.Countable) :
    ∃ P : W1 → Set W1, (∀ ζ, P ζ ⊆ Y) ∧ (∀ ζ, ¬ (P ζ).Countable) ∧
      Pairwise (fun ζ₁ ζ₂ => Disjoint (P ζ₁) (P ζ₂)) := by
  obtain ⟨eY⟩ := w1_emb_of_uncountable hY
  have hmk : #W1 = #(W1 × W1) := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, mk_W1,
      Cardinal.mul_eq_self Cardinal.aleph0_lt_aleph_one.le]
  obtain ⟨eProd⟩ := Cardinal.eq.mp hmk
  let P (ζ : W1) : Set W1 := {y : W1 | ∃ η : W1, (eY (eProd.symm (ζ, η))).1 = y}
  refine ⟨P, ?_, ?_, ?_⟩
  · rintro ζ y ⟨η, rfl⟩
    exact (eY _).2
  · intro ζ hc
    let f : W1 → P ζ := fun η => ⟨(eY (eProd.symm (ζ, η))).1, ⟨η, rfl⟩⟩
    have hf : Function.Injective f := fun η₁ η₂ h => by
      have h1 := eY.injective (Subtype.ext (congrArg (fun z : P ζ => z.1) h))
      have h2 := eProd.symm.injective h1
      exact congrArg Prod.snd h2
    have : Countable (P ζ) := Set.countable_coe_iff.mpr hc
    exact w1_uncountable hf.countable
  · intro ζ₁ ζ₂ hne
    rw [Set.disjoint_left]
    rintro y ⟨η₁, rfl⟩ ⟨η₂, h2⟩
    have h3 := eProd.symm.injective (eY.injective (Subtype.ext h2))
    exact hne (congrArg Prod.fst h3).symm

/-- **Miracle Partition Lemma:** for any `r : ℕ` and any map `B : PowW1 r → Finset W1`,
only finitely many `ζ : W1` fail to admit an order-embedding `PowW1 r ↪o {x // ζ ∉ B x}`. -/
private theorem miracle_partition (r : ℕ) (B : PowW1 r → Finset W1) :
    {ζ : W1 | ¬ Nonempty (PowW1 r ↪o {x : PowW1 r // ζ ∉ B x})}.Finite := by
  induction r with
  | zero =>
    obtain ⟨iso⟩ := powW1_zero_iso
    let x₀ : PowW1 0 := iso.symm ()
    refine (B x₀).finite_toSet.subset fun ζ hζ => ?_
    by_contra hnot
    apply hζ
    refine ⟨⟨⟨fun _ => ⟨x₀, hnot⟩, fun a b _ => iso.injective (Subsingleton.elim _ _)⟩, ?_⟩⟩
    intro a b
    have ha : a = b := iso.injective (Subsingleton.elim _ _)
    subst ha
    simp
  | succ r ih =>
    obtain ⟨iso⟩ := powW1_succ_iso r
    let B' (β : W1) (z : PowW1 r) : Finset W1 := B (iso.symm (toLex (β, z)))
    have hgood_step : ∀ ζ : W1,
        ¬ ({β : W1 | Nonempty (PowW1 r ↪o {z : PowW1 r // ζ ∉ B' β z})}).Countable →
        Nonempty (PowW1 (r + 1) ↪o {x : PowW1 (r + 1) // ζ ∉ B x}) := by
      intro ζ hunc
      obtain ⟨eβ⟩ := w1_emb_of_uncountable hunc
      let ez (α : W1) := Classical.choice (eβ α).2
      refine ⟨⟨⟨fun x =>
          let p := ofLex (iso x)
          ⟨iso.symm (toLex ((eβ p.1).1, (ez p.1 p.2).1)), (ez p.1 p.2).2⟩, ?_⟩, ?_⟩⟩
      · intro x₁ x₂ h
        have h' := congrArg (fun z => ofLex (iso z.1)) h
        simp only [OrderIso.apply_symm_apply, ofLex_toLex, Prod.mk.injEq] at h'
        obtain ⟨h1, h2⟩ := h'
        have h1' : (ofLex (iso x₁)).1 = (ofLex (iso x₂)).1 :=
          eβ.injective (Subtype.ext h1)
        have h2' : (ofLex (iso x₁)).2 = (ofLex (iso x₂)).2 := by
          rw [← h1'] at h2
          exact (ez (ofLex (iso x₁)).1).injective (Subtype.ext h2)
        exact iso.injective (ofLex.injective (Prod.ext h1' h2'))
      · intro x₁ x₂
        change iso.symm (toLex ((eβ (ofLex (iso x₁)).1).1, (ez (ofLex (iso x₁)).1 (ofLex (iso x₁)).2).1)) ≤
            iso.symm (toLex ((eβ (ofLex (iso x₂)).1).1, (ez (ofLex (iso x₂)).1 (ofLex (iso x₂)).2).1)) ↔
            x₁ ≤ x₂
        rw [iso.symm.le_iff_le]
        have hiff : ∀ a b : W1 × PowW1 r,
            toLex a ≤ toLex b ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) :=
          fun a b => Prod.Lex.le_iff
        rw [hiff]
        have hiff2 : x₁ ≤ x₂ ↔
            (ofLex (iso x₁)).1 < (ofLex (iso x₂)).1 ∨
            ((ofLex (iso x₁)).1 = (ofLex (iso x₂)).1 ∧ (ofLex (iso x₁)).2 ≤ (ofLex (iso x₂)).2) := by
          rw [← iso.le_iff_le]
          simpa using hiff (ofLex (iso x₁)) (ofLex (iso x₂))
        rw [hiff2]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · exact Or.inl (eβ.lt_iff_lt.mp h)
          · have h1' : (ofLex (iso x₁)).1 = (ofLex (iso x₂)).1 :=
              eβ.injective (Subtype.ext h1)
            refine Or.inr ⟨h1', ?_⟩
            rw [← h1'] at h2
            exact (ez (ofLex (iso x₁)).1).le_iff_le.mp h2
        · rintro (h | ⟨h1, h2⟩)
          · exact Or.inl (eβ.lt_iff_lt.mpr h)
          · refine Or.inr ⟨congrArg (fun a => (eβ a).1) h1, ?_⟩
            rw [← h1]
            exact (ez (ofLex (iso x₁)).1).le_iff_le.mpr h2
    by_contra hinf
    have hinf' : {ζ : W1 | ¬ Nonempty (PowW1 (r + 1) ↪o {x : PowW1 (r + 1) // ζ ∉ B x})}.Infinite :=
      hinf
    let ζemb := hinf'.natEmbedding
    let ζseq : ℕ → W1 := fun k => (ζemb k).1
    have hζinj : Function.Injective ζseq := Subtype.val_injective.comp ζemb.injective
    have hζbad : ∀ k : ℕ, ¬ Nonempty (PowW1 (r + 1) ↪o {x : PowW1 (r + 1) // ζseq k ∉ B x}) :=
      fun k => (ζemb k).2
    have hE_count : ∀ k : ℕ,
        ({β : W1 | Nonempty (PowW1 r ↪o {z : PowW1 r // ζseq k ∉ B' β z})}).Countable := by
      intro k
      by_contra hunc
      exact hζbad k (hgood_step (ζseq k) hunc)
    have hU_count :
        (⋃ k : ℕ, {β : W1 | Nonempty (PowW1 r ↪o {z : PowW1 r // ζseq k ∉ B' β z})}).Countable :=
      Set.countable_iUnion hE_count
    have hex_β : ∃ β : W1,
        β ∉ ⋃ k : ℕ, {β : W1 | Nonempty (PowW1 r ↪o {z : PowW1 r // ζseq k ∉ B' β z})} := by
      by_contra hall
      push Not at hall
      exact w1_uncountable (Set.countable_univ_iff.mp (hU_count.mono fun β _ => hall β))
    obtain ⟨β, hβ⟩ := hex_β
    have hfin := ih (B' β)
    have hsub : Set.range ζseq ⊆
        {ζ : W1 | ¬ Nonempty (PowW1 r ↪o {z : PowW1 r // ζ ∉ B' β z})} := by
      rintro _ ⟨k, rfl⟩
      intro hgood
      exact hβ (Set.mem_iUnion.mpr ⟨k, hgood⟩)
    exact (Set.infinite_range_of_injective hζinj) (hfin.subset hsub)

/- ### Section 3: Countable Disjoint Union Engine -/

section CountablePowerUnion

variable {ι : Type} [Countable ι] (m : ι → ℕ) (hm : ∀ i, 1 ≤ m i)
variable (F : (Σ i : ι, PowW1 (m i)) → Finset (Σ i : ι, PowW1 (m i)))
variable (hF : ∀ x, x ∉ F x)

/-- State at stage `k` of the `ω`-stage lifting construction. -/
private structure StageState (k : ℕ) where
  fiber : ∀ i : {i : ι // k < m i}, PowW1 (m i - k) → (PowW1 k ↪o PowW1 (m i))
  fiber_lt : ∀ (i : {i : ι // k < m i}) {q₁ q₂ : PowW1 (m i - k)}, q₁ < q₂ →
    ∀ u v : PowW1 k, fiber i q₁ u < fiber i q₂ v
  G : (Σ i : {i : ι // k < m i}, PowW1 (m i - k)) →
      Finset (Σ i : {i : ι // k < m i}, PowW1 (m i - k))
  G_irrefl : ∀ q, q ∉ G q
  fiber_free : ∀ (i : {i : ι // k < m i}) (q : PowW1 (m i - k)) (u v : PowW1 k),
    u ≠ v → (⟨i.1, fiber i q v⟩ : Σ i : ι, PowW1 (m i)) ∉ F ⟨i.1, fiber i q u⟩
  fiber_compat : ∀ (i₁ : {i : ι // k < m i}) (q₁ : PowW1 (m i₁ - k))
    (i₂ : {i : ι // k < m i}) (q₂ : PowW1 (m i₂ - k)),
    (⟨i₁, q₁⟩ : Σ i : {i : ι // k < m i}, PowW1 (m i - k)) ≠ ⟨i₂, q₂⟩ →
    ⟨i₁, q₁⟩ ∉ G ⟨i₂, q₂⟩ → ⟨i₂, q₂⟩ ∉ G ⟨i₁, q₁⟩ →
    ∀ u v : PowW1 k, (⟨i₂.1, fiber i₂ q₂ v⟩ : Σ i : ι, PowW1 (m i)) ∉ F ⟨i₁.1, fiber i₁ q₁ u⟩
  committed : ∀ i : {i : ι // m i ≤ k}, (PowW1 (m i) ↪o PowW1 (m i))
  committed_free : ∀ (i₁ : {i : ι // m i ≤ k}) (u₁ : PowW1 (m i₁))
    (i₂ : {i : ι // m i ≤ k}) (u₂ : PowW1 (m i₂)),
    (⟨i₁.1, committed i₁ u₁⟩ : Σ i : ι, PowW1 (m i)) ≠ ⟨i₂.1, committed i₂ u₂⟩ →
    (⟨i₂.1, committed i₂ u₂⟩ : Σ i : ι, PowW1 (m i)) ∉ F ⟨i₁.1, committed i₁ u₁⟩
  committed_vs_fiber : ∀ (i₁ : {i : ι // m i ≤ k}) (u₁ : PowW1 (m i₁))
    (i₂ : {i : ι // k < m i}) (q₂ : PowW1 (m i₂ - k)) (v₂ : PowW1 k),
    (⟨i₂.1, fiber i₂ q₂ v₂⟩ : Σ i : ι, PowW1 (m i)) ∉ F ⟨i₁.1, committed i₁ u₁⟩ ∧
    (⟨i₁.1, committed i₁ u₁⟩ : Σ i : ι, PowW1 (m i)) ∉ F ⟨i₂.1, fiber i₂ q₂ v₂⟩

/-- Base state at stage `k = 0`. -/
private noncomputable def stageZero : StageState m F 0 := by
  let iso0 : PowW1 0 ≃o Unit := Classical.choice powW1_zero_iso
  let eIdx : (Σ i : {i : ι // 0 < m i}, PowW1 (m i - 0)) ≃ (Σ i : ι, PowW1 (m i)) :=
    { toFun := fun ⟨i, q⟩ => ⟨i.1, q⟩
      invFun := fun ⟨i, q⟩ => ⟨⟨i, hm i⟩, q⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  exact
    { fiber := fun i q =>
        ⟨⟨fun _ => q, fun a b _ => iso0.injective (Subsingleton.elim _ _)⟩, by
          intro a b
          have : a = b := iso0.injective (Subsingleton.elim _ _)
          subst this; simp⟩
      fiber_lt := fun _ _ _ hlt _ _ => hlt
      G := fun p => (F (eIdx p)).map eIdx.symm.toEmbedding
      G_irrefl := fun p hp => by
        rw [Finset.mem_map] at hp
        obtain ⟨y, hyF, hyEq⟩ := hp
        have hy : y = eIdx p := eIdx.symm.injective hyEq
        rw [hy] at hyF
        exact hF (eIdx p) hyF
      fiber_free := fun _ _ u v huv => (huv (iso0.injective (Subsingleton.elim _ _))).elim
      fiber_compat := fun i₁ q₁ i₂ q₂ _ _ h21 _ _ hmem => by
        apply h21
        rw [Finset.mem_map]
        exact ⟨⟨i₂.1, q₂⟩, hmem, rfl⟩
      committed := fun i => absurd (hm i.1) (by omega)
      committed_free := fun i₁ => absurd (hm i₁.1) (by omega)
      committed_vs_fiber := fun i₁ => absurd (hm i₁.1) (by omega) }

/-- Standalone fiber-gluing order embedding used by `stageStep`. -/
private noncomputable def stageMkFiber {k : ℕ} (st : StageState m F k)
    (iso_split : ∀ i : {i : ι // k < m i},
      PowW1 (m i.1 - k) ≃o (PowW1 (m i.1 - (k + 1)) ×ₗ W1))
    (isoK : PowW1 (k + 1) ≃o (W1 ×ₗ PowW1 k))
    (i : {i : ι // k < m i}) (q : PowW1 (m i.1 - (k + 1))) (eδ : W1 ↪o W1) :
    PowW1 (k + 1) ↪o PowW1 (m i.1) :=
  let hlt_iff : ∀ a b : PowW1 (k + 1), a < b →
      st.fiber i ((iso_split i).symm (toLex (q, eδ (ofLex (isoK a)).1))) (ofLex (isoK a)).2 <
      st.fiber i ((iso_split i).symm (toLex (q, eδ (ofLex (isoK b)).1))) (ofLex (isoK b)).2 := by
    intro a b hab
    have hab' : isoK a < isoK b := isoK.lt_iff_lt.mpr hab
    rw [Prod.Lex.lt_iff] at hab'
    rcases hab' with h1 | ⟨h1, h2⟩
    · apply st.fiber_lt i
      rw [(iso_split i).symm.lt_iff_lt, Prod.Lex.lt_iff]
      exact Or.inr ⟨rfl, eδ.lt_iff_lt.mpr h1⟩
    · rw [h1]
      exact (st.fiber i _).lt_iff_lt.mpr h2
  ⟨⟨fun w =>
      let p := ofLex (isoK w)
      st.fiber i ((iso_split i).symm (toLex (q, eδ p.1))) p.2,
    fun w₁ w₂ h => by
      rcases lt_trichotomy w₁ w₂ with hlt | hEq | hgt
      · exact (ne_of_lt (hlt_iff w₁ w₂ hlt) h).elim
      · exact hEq
      · exact (ne_of_gt (hlt_iff w₂ w₁ hgt) h).elim⟩,
    fun {w₁ w₂} => by
      constructor
      · intro hle
        by_contra hgt
        push Not at hgt
        exact not_le_of_gt (hlt_iff w₂ w₁ hgt) hle
      · intro hle
        rcases lt_or_eq_of_le hle with hlt | rfl
        · exact le_of_lt (hlt_iff w₁ w₂ hlt)
        · exact le_rfl⟩

/-- Advance from stage `k` to stage `k + 1`, preserving `committed` for `m i ≤ k`. -/
private noncomputable def stageStep (k : ℕ) (st : StageState m F k) :
    { st' : StageState m F (k + 1) //
      ∀ (i : ι) (hi : m i ≤ k),
        st'.committed ⟨i, Nat.le_succ_of_le hi⟩ = st.committed ⟨i, hi⟩ } := by
  let Act := {i : ι // k < m i}
  let J := Σ i : Act, PowW1 (m i.1 - (k + 1))
  let iso_split : ∀ i : Act, PowW1 (m i.1 - k) ≃o (PowW1 (m i.1 - (k + 1)) ×ₗ W1) := fun i =>
    (powW1Cast (by have := i.2; omega)).trans
      (Classical.choice (powW1_succ_left_iso (m i.1 - (k + 1))))
  let pack : J × W1 ≃ (Σ i : Act, PowW1 (m i.1 - k)) :=
    { toFun := fun ⟨⟨i, q⟩, δ⟩ => ⟨i, (iso_split i).symm (toLex (q, δ))⟩
      invFun := fun ⟨i, x⟩ =>
        let p := ofLex (iso_split i x)
        (⟨i, p.1⟩, p.2)
      left_inv := fun ⟨⟨i, q⟩, δ⟩ => by simp
      right_inv := fun ⟨i, x⟩ => by simp }
  let H : J × W1 → Finset (J × W1) := fun x => (st.G (pack x)).map pack.symm.toEmbedding
  have hH_mem : ∀ x y, y ∈ H x ↔ pack y ∈ st.G (pack x) := fun x y => by
    simp only [H, Finset.mem_map, Equiv.toEmbedding_apply]
    exact ⟨fun ⟨z, hz, heq⟩ => (pack.symm_apply_eq.mp heq) ▸ hz,
      fun h => ⟨pack y, h, pack.symm_apply_apply y⟩⟩
  -- Step 1: Injection `ιJ : J ↪ W1` since `#J ≤ ℵ₁`.
  have hJ_card : #J ≤ ℵ₁ := by
    rw [Cardinal.mk_sigma]
    calc Cardinal.sum (fun i : Act => #(PowW1 (m i.1 - (k + 1))))
        ≤ #Act * ⨆ i : Act, #(PowW1 (m i.1 - (k + 1))) := Cardinal.sum_le_mk_mul_iSup _
      _ ≤ ℵ₀ * ℵ₁ := by
          refine mul_le_mul' Cardinal.mk_le_aleph0 ?_
          exact ciSup_le' fun i => powW1_card_le _
      _ ≤ ℵ₁ * ℵ₁ := by gcongr; exact Cardinal.aleph0_lt_aleph_one.le
      _ = ℵ₁ := Cardinal.mul_eq_self Cardinal.aleph0_lt_aleph_one.le
  rw [← mk_W1] at hJ_card
  let ιJ : J ↪ W1 := Classical.choice hJ_card
  -- Step 2: Countable `H`-closed filtration `X δ` and club `C`.
  let X (δ : W1) : Set (J × W1) := {x : J × W1 | ιJ x.1 < δ ∧ x.2 < δ}
  have hX_count : ∀ δ : W1, (X δ).Countable := by
    intro δ
    have h1 : ({p : J | ιJ p < δ}).Countable :=
      (w1_Iio_countable δ).preimage ιJ.injective
    exact h1.prod (w1_Iio_countable δ)
  let C_cl : Set W1 := {δ : W1 | ∀ x ∈ X δ, ∀ y ∈ H x, y ∈ X δ}
  have hC_cl : IsClub C_cl := by
    refine ⟨fun a => ?_, fun f hmono hf => ?_⟩
    · have step : ∀ δ : W1, ∃ δ' : W1, δ < δ' ∧ ∀ x ∈ X δ, ∀ y ∈ H x, y ∈ X δ' := by
        intro δ
        let pts : Set W1 :=
          insert δ (⋃ x ∈ X δ, ⋃ y ∈ (H x : Set (J × W1)), {ιJ y.1, y.2})
        have hpts : pts.Countable := by
          refine ((hX_count δ).biUnion fun x _ => ?_).insert δ
          refine (H x).countable_toSet.biUnion fun y _ => ?_
          exact (Set.countable_singleton _).insert _
        obtain ⟨δ', hδ'⟩ := w1_exists_gt_of_countable hpts
        refine ⟨δ', hδ' δ (Set.mem_insert _ _), fun x hx y hy => ?_⟩
        refine ⟨hδ' (ιJ y.1) (Set.mem_insert_of_mem _ (Set.mem_biUnion hx
          (Set.mem_biUnion hy (Set.mem_insert _ _)))),
          hδ' y.2 (Set.mem_insert_of_mem _ (Set.mem_biUnion hx
          (Set.mem_biUnion hy (Set.mem_insert_of_mem _ rfl))))⟩
      choose nxt hnxt_lt hnxt_cl using step
      let seq : ℕ → W1 := Nat.rec a (fun _ d => nxt d)
      have hseq_mono : StrictMono seq := strictMono_nat_of_lt_succ fun n => hnxt_lt (seq n)
      let L := w1Sup (Set.range seq) (Set.countable_range seq)
      refine ⟨L, ?_, lt_of_lt_of_le (hseq_mono (by omega : 0 < 1)) (le_w1Sup _ ⟨1, rfl⟩)⟩
      intro x ⟨hx1, hx2⟩ y hy
      obtain ⟨_, ⟨n1, rfl⟩, hn1⟩ := (lt_w1Sup_iff _).mp hx1
      obtain ⟨_, ⟨n2, rfl⟩, hn2⟩ := (lt_w1Sup_iff _).mp hx2
      let n := max n1 n2
      have hxN : x ∈ X (seq n) :=
        ⟨hn1.trans_le (hseq_mono.monotone (le_max_left _ _)),
         hn2.trans_le (hseq_mono.monotone (le_max_right _ _))⟩
      have hyN : y ∈ X (seq (n + 1)) := hnxt_cl (seq n) x hxN y hy
      exact ⟨hyN.1.trans_le (le_w1Sup _ ⟨n + 1, rfl⟩), hyN.2.trans_le (le_w1Sup _ ⟨n + 1, rfl⟩)⟩
    · intro x ⟨hx1, hx2⟩ y hy
      obtain ⟨_, ⟨n1, rfl⟩, hn1⟩ := (lt_w1Sup_iff _).mp hx1
      obtain ⟨_, ⟨n2, rfl⟩, hn2⟩ := (lt_w1Sup_iff _).mp hx2
      let n := max n1 n2
      have hxN : x ∈ X (f n) :=
        ⟨hn1.trans_le (hmono.monotone (le_max_left _ _)),
         hn2.trans_le (hmono.monotone (le_max_right _ _))⟩
      have hyN : y ∈ X (f n) := hf n x hxN y hy
      exact ⟨hyN.1.trans_le (le_w1Sup _ ⟨n, rfl⟩), hyN.2.trans_le (le_w1Sup _ ⟨n, rfl⟩)⟩
  let C : Set W1 := C_cl ∩ {δ : W1 | (∃ y, y < δ) ∧ ∀ y < δ, ∃ z, y < z ∧ z < δ}
  have hC : IsClub C := isClub_inter hC_cl isClub_lim
  -- Step 3: Pairwise disjoint stationary sets `T p ⊆ C ∩ {δ | ιJ p < δ}`.
  let T₀ : W1 → Set W1 := Classical.choose ulam_disjoint_stationary
  have hT₀_stat : ∀ α, IsStationary (T₀ α) := (Classical.choose_spec ulam_disjoint_stationary).1
  have hT₀_disj : Pairwise (fun α β => Disjoint (T₀ α) (T₀ β)) :=
    (Classical.choose_spec ulam_disjoint_stationary).2
  let T (p : J) : Set W1 := (T₀ (ιJ p) ∩ C) ∩ {δ : W1 | ιJ p < δ}
  have hT_stat : ∀ p : J, IsStationary (T p) := fun p =>
    ((hT₀_stat (ιJ p)).inter_club hC).inter_club (isClub_tail (ιJ p))
  have hT_disj : Pairwise (fun p₁ p₂ => Disjoint (T p₁) (T p₂)) := fun p₁ p₂ hne =>
    (hT₀_disj (fun h => hne (ιJ.injective h))).mono
      (Set.inter_subset_left.trans Set.inter_subset_left)
      (Set.inter_subset_left.trans Set.inter_subset_left)
  -- Step 4: Fodor + countable pigeonhole gives `ξ' p`, finite `A p ⊆ X (ξ' p)`, and stationary `S' p`.
  have hstep4 : ∀ p : J, ∃ (ξ' : W1) (A : Finset (J × W1)) (S' : Set W1),
      (A : Set (J × W1)) ⊆ X ξ' ∧ IsStationary S' ∧ S' ⊆ T p ∧
      (∀ δ ∈ S', ξ' < δ) ∧
      (∀ δ ∈ S', ∀ y ∈ X δ, y ∈ H (p, δ) ↔ y ∈ A) := by
    intro p
    let reg (δ : W1) : W1 :=
      let s := ((H (p, δ)).filter (fun y => y ∈ X δ)).image (fun y => max (ιJ y.1) y.2)
      if hs : s.Nonempty then s.max' hs else w1Bot
    have hreg : ∀ δ ∈ T p, reg δ < δ := by
      intro δ hδ
      have hlim : (∃ y, y < δ) ∧ ∀ y < δ, ∃ z, y < z ∧ z < δ := hδ.1.2.2
      dsimp only [reg]
      split_ifs with hs
      · rw [Finset.max'_lt_iff]
        intro u hu
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu
        have hyX : y ∈ X δ := (Finset.mem_filter.mp hy).2
        exact max_lt hyX.1 hyX.2
      · obtain ⟨y, hy⟩ := hlim.1
        exact lt_of_le_of_lt (w1Bot_le y) hy
    obtain ⟨ξ, hS₁⟩ := fodor (hT_stat p) reg hreg
    obtain ⟨ξ', hξ'⟩ := w1_exists_gt ξ
    let FinSub := {A : Finset (J × W1) // (A : Set (J × W1)) ⊆ X ξ'}
    have : Countable (X ξ') := Set.countable_coe_iff.mpr (hX_count ξ')
    have : Countable FinSub := by
      let toF : FinSub → Finset (X ξ') := fun A =>
        A.1.attach.map ⟨fun (y : {x // x ∈ A.1}) => (⟨y.1, A.2 y.2⟩ : X ξ'),
          fun _ _ h => Subtype.ext (congrArg (fun z : X ξ' => z.1) h)⟩
      have htoF_inj : Function.Injective toF := fun A B h => by
        apply Subtype.ext
        ext y
        constructor
        · intro hy
          have hmem : (⟨y, A.2 hy⟩ : X ξ') ∈ toF A := by
            simp only [toF, Finset.mem_map, Finset.mem_attach, true_and]
            exact ⟨⟨y, hy⟩, rfl⟩
          rw [h] at hmem
          simp only [toF, Finset.mem_map, Finset.mem_attach, true_and] at hmem
          obtain ⟨⟨z, hz⟩, hzy⟩ := hmem
          have : z = y := congrArg (fun u : X ξ' => u.1) hzy
          exact this ▸ hz
        · intro hy
          have hmem : (⟨y, B.2 hy⟩ : X ξ') ∈ toF B := by
            simp only [toF, Finset.mem_map, Finset.mem_attach, true_and]
            exact ⟨⟨y, hy⟩, rfl⟩
          rw [← h] at hmem
          simp only [toF, Finset.mem_map, Finset.mem_attach, true_and] at hmem
          obtain ⟨⟨z, hz⟩, hzy⟩ := hmem
          have : z = y := congrArg (fun u : X ξ' => u.1) hzy
          exact this ▸ hz
      exact htoF_inj.countable
    let piece (A : FinSub) : Set W1 :=
      {δ : W1 | δ ∈ {x ∈ T p | reg x = ξ} ∧ (H (p, δ)).filter (fun y => y ∈ X δ) = A.1}
    have hcov : {x ∈ T p | reg x = ξ} = ⋃ A : FinSub, piece A := by
      ext δ
      simp only [Set.mem_iUnion, piece, Set.mem_ofPred_eq]
      constructor
      · intro hδ
        have hsub : (((H (p, δ)).filter (fun y => y ∈ X δ) : Finset (J × W1)) : Set (J × W1)) ⊆ X ξ' := by
          intro y hy
          simp only [Finset.mem_coe, Finset.mem_filter] at hy
          let s := ((H (p, δ)).filter (fun y => y ∈ X δ)).image (fun y => max (ιJ y.1) y.2)
          have hmem_s : max (ιJ y.1) y.2 ∈ s := Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr hy, rfl⟩
          have hs_ne : s.Nonempty := ⟨_, hmem_s⟩
          have hle : max (ιJ y.1) y.2 ≤ reg δ := by
            dsimp only [reg]
            rw [dif_pos hs_ne]
            exact Finset.le_max' s _ hmem_s
          rw [hδ.2] at hle
          exact ⟨(le_max_left _ _).trans_lt (hle.trans_lt hξ'),
                 (le_max_right _ _).trans_lt (hle.trans_lt hξ')⟩
        exact ⟨⟨(H (p, δ)).filter (fun y => y ∈ X δ), hsub⟩, hδ, rfl⟩
      · rintro ⟨_, hδ, _⟩
        exact hδ
    rw [hcov] at hS₁
    obtain ⟨A, hA_stat⟩ := exists_stationary_of_iUnion hS₁
    refine ⟨ξ', A.1, piece A ∩ {δ : W1 | ξ' < δ}, A.2, hA_stat.inter_club (isClub_tail ξ'),
      fun δ hδ => hδ.1.1.1, fun δ hδ => hδ.2, fun δ hδ y hyX => ?_⟩
    have heq := hδ.1.2
    rw [← heq, Finset.mem_filter]
    exact ⟨fun h => ⟨h, hyX⟩, fun h => h.1⟩
  choose ξ' A S' hA_sub hS'_stat hS'_sub hS'_gt hS'_eq using hstep4
  -- Fundamental edge-elimination property on `(p, δ)` with `δ ∈ S' p`:
  have hno_H : ∀ (p₁ p₂ : J) (δ₁ δ₂ : W1), δ₁ ∈ S' p₁ → δ₂ ∈ S' p₂ →
      (p₁, δ₁) ≠ (p₂, δ₂) →
      (p₁ = p₂ ∨ ((p₁, δ₁) ∉ A p₂ ∧ (p₂, δ₂) ∉ A p₁)) →
      (p₂, δ₂) ∉ H (p₁, δ₁) ∧ (p₁, δ₁) ∉ H (p₂, δ₂) := by
    intro p₁ p₂ δ₁ δ₂ h1 h2 hne hcond
    have hδne : δ₁ ≠ δ₂ := by
      intro hEq
      subst hEq
      by_cases hp : p₁ = p₂
      · exact hne (Prod.ext hp rfl)
      · exact Set.disjoint_left.mp (hT_disj hp) (hS'_sub p₁ h1) (hS'_sub p₂ h2)
    have hdir : ∀ (a b : J) (d₁ d₂ : W1), d₁ ∈ S' a → d₂ ∈ S' b → d₁ < d₂ →
        (a = b ∨ (a, d₁) ∉ A b) → (b, d₂) ∉ H (a, d₁) ∧ (a, d₁) ∉ H (b, d₂) := by
      intro a b d₁ d₂ ha hb hlt hc
      have hX12 : (a, d₁) ∈ X d₂ := ⟨(hS'_sub a ha).2.trans hlt, hlt⟩
      constructor
      · intro hmem
        have hcl := (hS'_sub b hb).1.2.1 (a, d₁) hX12 (b, d₂) hmem
        exact lt_irrefl d₂ hcl.2
      · intro hmem
        have hmemA : (a, d₁) ∈ A b := (hS'_eq b d₂ hb (a, d₁) hX12).mp hmem
        rcases hc with rfl | hnot
        · have hltξ : d₁ < ξ' a := (hA_sub a hmemA).2
          exact lt_asymm hltξ (hS'_gt a d₁ ha)
        · exact hnot hmemA
    rcases lt_or_gt_of_ne hδne with hlt | hgt
    · exact hdir p₁ p₂ δ₁ δ₂ h1 h2 hlt (hcond.imp id And.left)
    · exact (hdir p₂ p₁ δ₂ δ₁ h2 h1 hgt (hcond.imp Eq.symm And.right)).symm
  -- Step 5: Split `Act` into `Act0` (`m i = k + 1`) and `Act1` (`k + 1 < m i`).
  let Act0 := {i : ι // m i = k + 1}
  let Act1 := {i : ι // k + 1 < m i}
  let q0 (i : Act0) : PowW1 (m i.1 - (k + 1)) := by
    have h0 : m i.1 - (k + 1) = 0 := by have := i.2; omega
    rw [h0]
    exact (Classical.choice powW1_zero_iso).symm ()
  let p0 (i : Act0) : J := ⟨⟨i.1, by have := i.2; omega⟩, q0 i⟩
  have hp0_inj : Function.Injective p0 := fun i₁ i₂ h => by
    have h1 : i₁.1 = i₂.1 := congrArg (fun p : J => p.1.1) h
    exact Subtype.ext h1
  -- Clear `Act0 → Act0`:
  let bad0 (i : Act0) : Set W1 := {η : W1 | ∃ j : Act0, (p0 i, η) ∈ A (p0 j)}
  have hbad0_count : ∀ i : Act0, (bad0 i).Countable := by
    intro i
    have heq : bad0 i = ⋃ j : Act0, {η : W1 | (p0 i, η) ∈ A (p0 j)} := by
      ext η; simp [bad0]
    rw [heq]
    refine Set.countable_iUnion fun j => ?_
    exact (A (p0 j)).countable_toSet.preimage fun η₁ η₂ h => congrArg Prod.snd h
  let Y (i : Act0) : Set W1 := S' (p0 i) \ bad0 i
  have hY_unc : ∀ i : Act0, ¬ (Y i).Countable := fun i hc =>
    (hS'_stat (p0 i)).uncountable ((hc.union (hbad0_count i)).mono fun δ hδ =>
      if h : δ ∈ bad0 i then Or.inr h else Or.inl ⟨hδ, h⟩)
  -- Step 6: Clear `Act0 → Act1`:
  let D1 (j : Act1) : Set (PowW1 (m j.1 - (k + 1))) :=
    {q | ∃ (i : Act0) (η : W1), (⟨⟨j.1, by have := j.2; omega⟩, q⟩, η) ∈ A (p0 i)}
  have hD1_count : ∀ j : Act1, (D1 j).Countable := by
    intro j
    have heq : D1 j = ⋃ i : Act0,
        {q | ∃ y ∈ (A (p0 i) : Set (J × W1)), y.1 = ⟨⟨j.1, by have := j.2; omega⟩, q⟩} := by
      ext q; simp only [D1, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe]
      constructor
      · rintro ⟨i, η, hmem⟩
        exact ⟨i, (⟨⟨j.1, by have := j.2; omega⟩, q⟩, η), hmem, rfl⟩
      · rintro ⟨i, ⟨p, η⟩, hmem, hp⟩
        exact ⟨i, η, hp ▸ hmem⟩
    rw [heq]
    refine Set.countable_iUnion fun i => ?_
    have hfin : ({q : PowW1 (m j.1 - (k + 1)) |
        ∃ y ∈ (A (p0 i) : Set (J × W1)), y.1 = ⟨⟨j.1, by have := j.2; omega⟩, q⟩}).Finite := by
      let f : J × W1 → Option (PowW1 (m j.1 - (k + 1))) := fun y =>
        if h : y.1.1.1 = j.1 then
          some (cast (by rw [h]) y.1.2)
        else none
      have hsub : {q : PowW1 (m j.1 - (k + 1)) |
          ∃ y ∈ (A (p0 i) : Set (J × W1)), y.1 = ⟨⟨j.1, by have := j.2; omega⟩, q⟩} ⊆
          Option.some ⁻¹' (f '' (A (p0 i) : Set (J × W1))) := by
        rintro q ⟨y, hyA, hy1⟩
        refine ⟨y, hyA, ?_⟩
        have hj : y.1.1.1 = j.1 := congrArg (fun p : J => p.1.1) hy1
        simp only [f, dif_pos hj]
        congr 1
        cases y with | mk yp yη =>
        dsimp only at hy1 hj ⊢
        subst hy1
        rfl
      exact (((A (p0 i)).finite_toSet.image f).preimage (fun _ _ _ _ h => Option.some.inj h)).subset hsub
    exact hfin.countable
  have he1_ex : ∀ j : Act1, Nonempty (PowW1 (m j.1 - (k + 1)) ↪o
      {q : PowW1 (m j.1 - (k + 1)) // q ∉ D1 j}) := fun j =>
    powW1_emb_sdiff_countable (m j.1 - (k + 1)) (by have := j.2; omega) (D1 j) (hD1_count j)
  let e1 (j : Act1) := Classical.choice (he1_ex j)
  -- Step 7: Clear `Act1 → Act0` via the Miracle Partition Lemma!
  have hP_ex : ∀ i : Act0, ∃ P : W1 → Set W1,
      (∀ ζ, P ζ ⊆ Y i) ∧ (∀ ζ, ¬ (P ζ).Countable) ∧
      Pairwise (fun ζ₁ ζ₂ => Disjoint (P ζ₁) (P ζ₂)) :=
    fun i => w1_partition_aleph1 (hY_unc i)
  choose P hP_sub hP_unc hP_disj using hP_ex
  let B (j : Act1) (q : PowW1 (m j.1 - (k + 1))) : Finset W1 :=
    (A ⟨⟨j.1, by have := j.2; omega⟩, (e1 j q).1⟩).biUnion fun y =>
      if h : ∃ (i : Act0) (ζ : W1), y.1 = p0 i ∧ y.2 ∈ P i ζ then
        {Classical.choose (Classical.choose_spec h)}
      else ∅
  have hB_mem : ∀ (j : Act1) (q : PowW1 (m j.1 - (k + 1))) (i : Act0) (ζ : W1) (η : W1),
      η ∈ P i ζ → (p0 i, η) ∈ A ⟨⟨j.1, by have := j.2; omega⟩, (e1 j q).1⟩ →
      ζ ∈ B j q := by
    intro j q i ζ η hη hmemA
    rw [Finset.mem_biUnion]
    refine ⟨(p0 i, η), hmemA, ?_⟩
    have hex : ∃ (i' : Act0) (ζ' : W1), (p0 i, η).1 = p0 i' ∧ (p0 i, η).2 ∈ P i' ζ' :=
      ⟨i, ζ, rfl, hη⟩
    rw [dif_pos hex, Finset.mem_singleton]
    have hspec := Classical.choose_spec (Classical.choose_spec hex)
    have hi_eq : Classical.choose hex = i := hp0_inj hspec.1.symm
    let ζ' : W1 := Classical.choose (Classical.choose_spec hex)
    have hη' : η ∈ P i ζ' :=
      (congrArg (fun a => η ∈ P a ζ') hi_eq).mp hspec.2
    by_contra hne
    exact Set.disjoint_left.mp (hP_disj i hne) hη hη'
  let Bad (j : Act1) : Set W1 :=
    {ζ : W1 | ¬ Nonempty (PowW1 (m j.1 - (k + 1)) ↪o
      {q : PowW1 (m j.1 - (k + 1)) // ζ ∉ B j q})}
  have hBad_count : (⋃ j : Act1, Bad j).Countable :=
    Set.countable_iUnion fun j => (miracle_partition (m j.1 - (k + 1)) (B j)).countable
  have hex_ζ : ∃ ζ : W1, ζ ∉ ⋃ j : Act1, Bad j := by
    by_contra hall
    push Not at hall
    exact w1_uncountable (Set.countable_univ_iff.mp (hBad_count.mono fun ζ _ => hall ζ))
  let ζ₀ : W1 := Classical.choose hex_ζ
  have hζ₀ : ζ₀ ∉ ⋃ j : Act1, Bad j := Classical.choose_spec hex_ζ
  have he2_ex : ∀ j : Act1, Nonempty (PowW1 (m j.1 - (k + 1)) ↪o
      {q : PowW1 (m j.1 - (k + 1)) // ζ₀ ∉ B j q}) := fun j => by
    by_contra hnot
    exact hζ₀ (Set.mem_iUnion.mpr ⟨j, hnot⟩)
  let e2 (j : Act1) := Classical.choice (he2_ex j)
  -- Build embeddings for `Act0` (`S''_i = P i ζ₀`) and `Act1` (`embQ j` + `S'`).
  have heS0_ex : ∀ i : Act0, Nonempty (W1 ↪o P i ζ₀) :=
    fun i => w1_emb_of_uncountable (hP_unc i ζ₀)
  let eS0 (i : Act0) := Classical.choice (heS0_ex i)
  let embQ (j : Act1) : PowW1 (m j.1 - (k + 1)) ↪o PowW1 (m j.1 - (k + 1)) :=
    (e2 j).trans ((OrderEmbedding.subtype _).trans ((e1 j).trans (OrderEmbedding.subtype _)))
  have heS1_ex : ∀ (j : Act1) (q : PowW1 (m j.1 - (k + 1))),
      Nonempty (W1 ↪o S' ⟨⟨j.1, by have := j.2; omega⟩, embQ j q⟩) :=
    fun j q => w1_emb_of_uncountable (hS'_stat _).uncountable
  let eS1 (j : Act1) (q : PowW1 (m j.1 - (k + 1))) := Classical.choice (heS1_ex j q)
  -- Common fiber-gluing helper: `PowW1 (k + 1) ≃o W1 ×ₗ PowW1 k`.
  let isoK : PowW1 (k + 1) ≃o (W1 ×ₗ PowW1 k) := Classical.choice (powW1_succ_iso k)
  let mkFiber := stageMkFiber m F st iso_split isoK
  -- Define `newFiber`, `newG`, `newCommitted`.
  let newFiber (j : Act1) (q : PowW1 (m j.1 - (k + 1))) : PowW1 (k + 1) ↪o PowW1 (m j.1) :=
    mkFiber ⟨j.1, by have := j.2; omega⟩ (embQ j q) ((eS1 j q).trans (OrderEmbedding.subtype _))
  have hnewFiber_eq : ∀ (j : Act1) (q : PowW1 (m j.1 - (k + 1))) (u : PowW1 (k + 1)),
      newFiber j q u = st.fiber ⟨j.1, by have := j.2; omega⟩
        ((iso_split ⟨j.1, by have := j.2; omega⟩).symm
          (toLex (embQ j q, (eS1 j q (ofLex (isoK u)).1).1)))
        (ofLex (isoK u)).2 := fun _ _ _ => rfl
  let fJ1 : (Σ j : Act1, PowW1 (m j.1 - (k + 1))) → J :=
    fun ⟨j, q⟩ => ⟨⟨j.1, by have := j.2; omega⟩, embQ j q⟩
  have hfJ1_inj : Function.Injective fJ1 := by
    rintro ⟨⟨j₁, hj₁⟩, q₁⟩ ⟨⟨j₂, hj₂⟩, q₂⟩ h
    have h1 : j₁ = j₂ := congrArg (fun p : J => p.1.1) h
    subst h1
    have h2 : embQ ⟨j₁, hj₁⟩ q₁ = embQ ⟨j₁, hj₂⟩ q₂ := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact Sigma.ext rfl (heq_of_eq ((embQ ⟨j₁, hj₁⟩).injective h2))
  let newG (x : Σ j : Act1, PowW1 (m j.1 - (k + 1))) :
      Finset (Σ j : Act1, PowW1 (m j.1 - (k + 1))) :=
    (((A (fJ1 x)).image Prod.fst).preimage fJ1 hfJ1_inj.injOn).erase x
  have hnewG_mem : ∀ x y : Σ j : Act1, PowW1 (m j.1 - (k + 1)),
      y ∈ newG x ↔ y ≠ x ∧ ∃ η : W1, (fJ1 y, η) ∈ A (fJ1 x) := by
    intro x y
    dsimp only [newG]
    rw [Finset.mem_erase, Finset.mem_preimage, Finset.mem_image]
    constructor
    · rintro ⟨hne, ⟨p, η⟩, hmem, hp⟩
      exact ⟨hne, η, hp ▸ hmem⟩
    · rintro ⟨hne, η, hmem⟩
      exact ⟨hne, (fJ1 y, η), hmem, rfl⟩
  let comm0 (i : Act0) : PowW1 (m i.1) ↪o PowW1 (m i.1) :=
    (powW1Cast i.2).toOrderEmbedding.trans
      (mkFiber ⟨i.1, by have := i.2; omega⟩ (q0 i) ((eS0 i).trans (OrderEmbedding.subtype _)))
  let newCommitted (i : {i : ι // m i ≤ k + 1}) : PowW1 (m i.1) ↪o PowW1 (m i.1) :=
    if h : m i.1 ≤ k then st.committed ⟨i.1, h⟩
    else comm0 ⟨i.1, by have := i.2; omega⟩
  -- Key helper: `F`-freeness between two `mkFiber` points given `(p₁, δ₁)` and `(p₂, δ₂)` in `S'`.
  have hmkFiber_free : ∀ (i₁ i₂ : Act) (q₁ : PowW1 (m i₁.1 - (k + 1))) (q₂ : PowW1 (m i₂.1 - (k + 1)))
      (δ₁ δ₂ : W1) (u₁ u₂ : PowW1 k),
      δ₁ ∈ S' ⟨i₁, q₁⟩ → δ₂ ∈ S' ⟨i₂, q₂⟩ →
      (⟨i₁.1, st.fiber i₁ ((iso_split i₁).symm (toLex (q₁, δ₁))) u₁⟩ : Σ i, PowW1 (m i)) ≠
        ⟨i₂.1, st.fiber i₂ ((iso_split i₂).symm (toLex (q₂, δ₂))) u₂⟩ →
      ((⟨i₁, q₁⟩ : J) = ⟨i₂, q₂⟩ ∨
        ((⟨i₁, q₁⟩, δ₁) ∉ A ⟨i₂, q₂⟩ ∧ (⟨i₂, q₂⟩, δ₂) ∉ A ⟨i₁, q₁⟩)) →
      (⟨i₂.1, st.fiber i₂ ((iso_split i₂).symm (toLex (q₂, δ₂))) u₂⟩ : Σ i, PowW1 (m i)) ∉
        F ⟨i₁.1, st.fiber i₁ ((iso_split i₁).symm (toLex (q₁, δ₁))) u₁⟩ := by
    intro i₁ i₂ q₁ q₂ δ₁ δ₂ u₁ u₂ h1 h2 hne hcond
    by_cases hpair : ((⟨i₁, q₁⟩ : J), δ₁) = (⟨i₂, q₂⟩, δ₂)
    · have hp : (⟨i₁, q₁⟩ : J) = ⟨i₂, q₂⟩ := congrArg Prod.fst hpair
      have hδ : δ₁ = δ₂ := congrArg Prod.snd hpair
      have hi : i₁ = i₂ := congrArg Sigma.fst hp
      subst hi; subst hδ
      have hq : q₁ = q₂ := eq_of_heq (Sigma.mk.inj_iff.mp hp).2
      subst hq
      have hu : u₁ ≠ u₂ := fun h => hne (by rw [h])
      exact st.fiber_free i₁ _ u₁ u₂ hu
    · have ⟨h12, h21⟩ := hno_H ⟨i₁, q₁⟩ ⟨i₂, q₂⟩ δ₁ δ₂ h1 h2 hpair hcond
      have hpack_ne : pack (⟨i₁, q₁⟩, δ₁) ≠ pack (⟨i₂, q₂⟩, δ₂) := fun h =>
        hpair (pack.injective h)
      exact st.fiber_compat i₁ _ i₂ _ hpack_ne
        (fun h => h21 ((hH_mem _ _).mpr h))
        (fun h => h12 ((hH_mem _ _).mpr h))
        u₁ u₂
  -- Helper unpacking `comm0 i u` into `st.fiber`.
  have hcomm0_eq : ∀ (i : Act0) (u : PowW1 (m i.1)),
      ∃ (δ : W1) (v : PowW1 k), δ ∈ P i ζ₀ ∧
        comm0 i u = st.fiber ⟨i.1, by have := i.2; omega⟩
          ((iso_split ⟨i.1, by have := i.2; omega⟩).symm (toLex (q0 i, δ))) v := by
    intro i u
    let w : PowW1 (k + 1) := powW1Cast i.2 u
    refine ⟨(eS0 i (ofLex (isoK w)).1).1, (ofLex (isoK w)).2, (eS0 i _).2, rfl⟩
  -- Assemble `StageState m F (k + 1)`:
  refine ⟨{
    fiber := newFiber
    fiber_lt := fun j q₁ q₂ hlt u v => by
      rw [hnewFiber_eq, hnewFiber_eq]
      apply st.fiber_lt ⟨j.1, by have := j.2; omega⟩
      rw [(iso_split _).symm.lt_iff_lt, Prod.Lex.lt_iff]
      exact Or.inl ((embQ j).lt_iff_lt.mpr hlt)
    G := newG
    G_irrefl := fun x hx => ((hnewG_mem x x).mp hx).1 rfl
    fiber_free := fun j q u v huv => by
      rw [hnewFiber_eq, hnewFiber_eq]
      refine hmkFiber_free ⟨j.1, by have := j.2; omega⟩ ⟨j.1, by have := j.2; omega⟩
        (embQ j q) (embQ j q) _ _ _ _ (eS1 j q _).2 (eS1 j q _).2 ?_ (Or.inl rfl)
      intro hEq
      have hval : newFiber j q u = newFiber j q v := by
        rw [hnewFiber_eq, hnewFiber_eq]
        exact eq_of_heq (Sigma.mk.inj_iff.mp hEq).2
      exact huv ((newFiber j q).injective hval)
    fiber_compat := fun j₁ q₁ j₂ q₂ hne h12 h21 u v => by
      rw [hnewFiber_eq, hnewFiber_eq]
      refine hmkFiber_free ⟨j₁.1, by have := j₁.2; omega⟩ ⟨j₂.1, by have := j₂.2; omega⟩
        (embQ j₁ q₁) (embQ j₂ q₂) _ _ _ _ (eS1 j₁ q₁ _).2 (eS1 j₂ q₂ _).2 ?_ (Or.inr ⟨?_, ?_⟩)
      · intro hEq
        have hj : j₁.1 = j₂.1 := congrArg Sigma.fst hEq
        have hj' : j₁ = j₂ := Subtype.ext hj
        subst hj'
        have hq : q₁ ≠ q₂ := fun h => hne (by rw [h])
        have hval : newFiber j₁ q₁ u = newFiber j₁ q₂ v := by
          rw [hnewFiber_eq, hnewFiber_eq]
          exact eq_of_heq (Sigma.mk.inj_iff.mp hEq).2
        rcases lt_or_gt_of_ne hq with hlt | hgt
        · have hlt' : newFiber j₁ q₁ u < newFiber j₁ q₂ v := by
            rw [hnewFiber_eq, hnewFiber_eq]
            apply st.fiber_lt ⟨j₁.1, by have := j₁.2; omega⟩
            rw [(iso_split _).symm.lt_iff_lt, Prod.Lex.lt_iff]
            exact Or.inl ((embQ j₁).lt_iff_lt.mpr hlt)
          exact ne_of_lt hlt' hval
        · have hgt' : newFiber j₁ q₂ v < newFiber j₁ q₁ u := by
            rw [hnewFiber_eq, hnewFiber_eq]
            apply st.fiber_lt ⟨j₁.1, by have := j₁.2; omega⟩
            rw [(iso_split _).symm.lt_iff_lt, Prod.Lex.lt_iff]
            exact Or.inl ((embQ j₁).lt_iff_lt.mpr hgt)
          exact ne_of_gt hgt' hval
      · intro hmem
        exact h12 ((hnewG_mem ⟨j₂, q₂⟩ ⟨j₁, q₁⟩).mpr ⟨hne, _, hmem⟩)
      · intro hmem
        exact h21 ((hnewG_mem ⟨j₁, q₁⟩ ⟨j₂, q₂⟩).mpr ⟨hne.symm, _, hmem⟩)
    committed := newCommitted
    committed_free := fun i₁ u₁ i₂ u₂ hne => by
      dsimp only [newCommitted] at hne ⊢
      split_ifs at hne ⊢ with h1 h2 h2
      · exact st.committed_free ⟨i₁.1, h1⟩ u₁ ⟨i₂.1, h2⟩ u₂ hne
      · obtain ⟨δ₂, v₂, _, heq₂⟩ := hcomm0_eq ⟨i₂.1, by have := i₂.2; omega⟩ u₂
        rw [heq₂]
        exact (st.committed_vs_fiber ⟨i₁.1, h1⟩ u₁ ⟨i₂.1, by omega⟩ _ v₂).1
      · obtain ⟨δ₁, v₁, _, heq₁⟩ := hcomm0_eq ⟨i₁.1, by have := i₁.2; omega⟩ u₁
        rw [heq₁]
        exact (st.committed_vs_fiber ⟨i₂.1, h2⟩ u₂ ⟨i₁.1, by omega⟩ _ v₁).2
      · obtain ⟨δ₁, v₁, hP1, heq₁⟩ := hcomm0_eq ⟨i₁.1, by have := i₁.2; omega⟩ u₁
        obtain ⟨δ₂, v₂, hP2, heq₂⟩ := hcomm0_eq ⟨i₂.1, by have := i₂.2; omega⟩ u₂
        rw [heq₁, heq₂] at hne ⊢
        have hY1 : δ₁ ∈ Y ⟨i₁.1, by have := i₁.2; omega⟩ := hP_sub _ ζ₀ hP1
        have hY2 : δ₂ ∈ Y ⟨i₂.1, by have := i₂.2; omega⟩ := hP_sub _ ζ₀ hP2
        refine hmkFiber_free ⟨i₁.1, by omega⟩ ⟨i₂.1, by omega⟩ _ _ δ₁ δ₂ v₁ v₂
          hY1.1 hY2.1 hne (Or.inr ⟨?_, ?_⟩)
        · exact fun hmem => hY1.2 ⟨⟨i₂.1, by have := i₂.2; omega⟩, hmem⟩
        · exact fun hmem => hY2.2 ⟨⟨i₁.1, by have := i₁.2; omega⟩, hmem⟩
    committed_vs_fiber := fun i₁ u₁ j₂ q₂ v₂ => by
      rw [hnewFiber_eq]
      dsimp only [newCommitted]
      split_ifs with h1
      · exact st.committed_vs_fiber ⟨i₁.1, h1⟩ u₁ ⟨j₂.1, by have := j₂.2; omega⟩ _ _
      · obtain ⟨δ₁, v₁, hP1, heq₁⟩ := hcomm0_eq ⟨i₁.1, by have := i₁.2; omega⟩ u₁
        rw [heq₁]
        let i₁Act0 : Act0 := ⟨i₁.1, by have := i₁.2; omega⟩
        let i₁Act : Act := ⟨i₁.1, by have := i₁.2; omega⟩
        let j₂Act : Act := ⟨j₂.1, by have := j₂.2; omega⟩
        let δ₂ : W1 := (eS1 j₂ q₂ (ofLex (isoK v₂)).1).1
        let v₂' : PowW1 k := (ofLex (isoK v₂)).2
        have hY1 : δ₁ ∈ Y i₁Act0 := hP_sub i₁Act0 ζ₀ hP1
        have hδ₂ : δ₂ ∈ S' ⟨j₂Act, embQ j₂ q₂⟩ := (eS1 j₂ q₂ (ofLex (isoK v₂)).1).2
        have hne_i : i₁.1 ≠ j₂.1 := fun h => by
          have h1' := i₁.2; have h2' := j₂.2; rw [h] at h1'; omega
        have hne1 : (⟨i₁Act.1, st.fiber i₁Act ((iso_split i₁Act).symm (toLex (q0 i₁Act0, δ₁))) v₁⟩ :
              Σ i, PowW1 (m i)) ≠
            ⟨j₂Act.1, st.fiber j₂Act ((iso_split j₂Act).symm (toLex (embQ j₂ q₂, δ₂))) v₂'⟩ :=
          fun h => hne_i (congrArg Sigma.fst h)
        have hnotA21 : (⟨i₁Act, q0 i₁Act0⟩, δ₁) ∉ A ⟨j₂Act, embQ j₂ q₂⟩ := fun hmem =>
          (e2 j₂ q₂).2 (hB_mem j₂ (e2 j₂ q₂).1 i₁Act0 ζ₀ δ₁ hP1 hmem)
        have hnotA12 : (⟨j₂Act, embQ j₂ q₂⟩, δ₂) ∉ A ⟨i₁Act, q0 i₁Act0⟩ := fun hmem =>
          (e1 j₂ (e2 j₂ q₂).1).2 ⟨i₁Act0, δ₂, hmem⟩
        exact ⟨hmkFiber_free i₁Act j₂Act (q0 i₁Act0) (embQ j₂ q₂) δ₁ δ₂ v₁ v₂'
            hY1.1 hδ₂ hne1 (Or.inr ⟨hnotA21, hnotA12⟩),
          hmkFiber_free j₂Act i₁Act (embQ j₂ q₂) (q0 i₁Act0) δ₂ δ₁ v₂' v₁
            hδ₂ hY1.1 hne1.symm (Or.inr ⟨hnotA12, hnotA21⟩)⟩
  }, fun i hi => by
    dsimp only [newCommitted]
    rw [dif_pos hi]⟩

end CountablePowerUnion

private theorem free_set_countable_pow_union {ι : Type} [Countable ι]
    (m : ι → ℕ) (hm : ∀ i, 1 ≤ m i)
    (F : (Σ i : ι, PowW1 (m i)) → Finset (Σ i : ι, PowW1 (m i))) (hF : ∀ x, x ∉ F x) :
    ∃ emb : ∀ i : ι, PowW1 (m i) ↪o PowW1 (m i),
      ∀ (i₁ : ι) (u₁ : PowW1 (m i₁)) (i₂ : ι) (u₂ : PowW1 (m i₂)),
        (⟨i₁, emb i₁ u₁⟩ : Σ i : ι, PowW1 (m i)) ≠ ⟨i₂, emb i₂ u₂⟩ →
        (⟨i₂, emb i₂ u₂⟩ : Σ i : ι, PowW1 (m i)) ∉ F ⟨i₁, emb i₁ u₁⟩ := by
  let st : ∀ k : ℕ, StageState m F k := Nat.rec (stageZero m hm F hF) (fun k s => (stageStep m F k s).1)
  have hst_agree : ∀ (k₁ k₂ : ℕ) (h12 : k₁ ≤ k₂) (i : ι) (hi : m i ≤ k₁),
      (st k₂).committed ⟨i, hi.trans h12⟩ = (st k₁).committed ⟨i, hi⟩ := by
    intro k₁ k₂ h12
    induction h12 with
    | refl => intro i hi; rfl
    | @step k₂ hk ih =>
      intro i hi
      have hstep := (stageStep m F k₂ (st k₂)).2 i (hi.trans hk)
      exact hstep.trans (ih i hi)
  refine ⟨fun i => (st (m i)).committed ⟨i, le_rfl⟩, fun i₁ u₁ i₂ u₂ hne => ?_⟩
  let K := max (m i₁) (m i₂)
  have h1 : (st K).committed ⟨i₁, le_max_left _ _⟩ = (st (m i₁)).committed ⟨i₁, le_rfl⟩ :=
    hst_agree (m i₁) K (le_max_left _ _) i₁ le_rfl
  have h2 : (st K).committed ⟨i₂, le_max_right _ _⟩ = (st (m i₂)).committed ⟨i₂, le_rfl⟩ :=
    hst_agree (m i₂) K (le_max_right _ _) i₂ le_rfl
  dsimp only at hne ⊢
  rw [← h1, ← h2] at hne ⊢
  exact (st K).committed_free ⟨i₁, le_max_left _ _⟩ u₁ ⟨i₂, le_max_right _ _⟩ u₂ hne

/- ### Section 4: Reordering lift for `ω_ 1 ^ (ω + 1)` -/

/-- Lexicographic dependent sum over a well-ordered index type. -/
private structure LexSigma {α : Type} (β : α → Type) where
  fst : α
  snd : β fst

private noncomputable instance lexSigmaLinearOrder {α : Type} [LinearOrder α] {β : α → Type}
    [∀ a, LinearOrder (β a)] : LinearOrder (LexSigma β) where
  lt x y := x.fst < y.fst ∨ ∃ h : x.fst = y.fst, cast (by rw [h]) x.snd < y.snd
  le x y := x = y ∨ x.fst < y.fst ∨ ∃ h : x.fst = y.fst, cast (by rw [h]) x.snd < y.snd
  le_refl x := Or.inl rfl
  le_trans := by
    intro a b c hab hbc
    rcases hab with rfl | h1 | ⟨h1, hs1⟩
    · exact hbc
    · rcases hbc with rfl | h2 | ⟨h2, _⟩
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inl (h1.trans h2))
      · exact Or.inr (Or.inl (h2 ▸ h1))
    · rcases hbc with rfl | h2 | ⟨h2, hs2⟩
      · exact Or.inr (Or.inr ⟨h1, hs1⟩)
      · exact Or.inr (Or.inl (h1.symm ▸ h2))
      · refine Or.inr (Or.inr ⟨h1.trans h2, ?_⟩)
        cases a with | mk a1 a2 =>
        cases b with | mk b1 b2 =>
        cases c with | mk c1 c2 =>
        dsimp only at h1 h2 hs1 hs2 ⊢
        subst h1; subst h2
        exact hs1.trans hs2
  le_antisymm := by
    intro a b hab hba
    rcases hab with rfl | h1 | ⟨h1, hs1⟩
    · rfl
    · rcases hba with hEq | h2 | ⟨h2, _⟩
      · exact hEq.symm
      · exact (lt_asymm h1 h2).elim
      · exact (lt_irrefl _ (h2 ▸ h1)).elim
    · rcases hba with hEq | h2 | ⟨h2, hs2⟩
      · exact hEq.symm
      · exact (lt_irrefl _ (h1 ▸ h2)).elim
      · cases a with | mk a1 a2 =>
        cases b with | mk b1 b2 =>
        dsimp only at h1 h2 hs1 hs2
        subst h1
        exact (lt_asymm hs1 hs2).elim
  le_total := by
    intro a b
    rcases lt_trichotomy a.fst b.fst with hlt | hEq | hgt
    · exact Or.inl (Or.inr (Or.inl hlt))
    · cases a with | mk a1 a2 =>
      cases b with | mk b1 b2 =>
      dsimp only at hEq
      subst hEq
      rcases lt_trichotomy a2 b2 with hlt | rfl | hgt
      · exact Or.inl (Or.inr (Or.inr ⟨rfl, hlt⟩))
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, hgt⟩))
    · exact Or.inr (Or.inr (Or.inl hgt))
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro hlt
      refine ⟨Or.inr hlt, ?_⟩
      rintro (rfl | h2 | ⟨h2, hs2⟩)
      · rcases hlt with h | ⟨_, hs⟩
        · exact lt_irrefl _ h
        · exact lt_irrefl _ hs
      · rcases hlt with h1 | ⟨h1, _⟩
        · exact lt_asymm h1 h2
        · exact lt_irrefl _ (h1 ▸ h2)
      · rcases hlt with h1 | ⟨h1, hs1⟩
        · exact lt_irrefl _ (h2 ▸ h1)
        · cases a with | mk a1 a2 =>
          cases b with | mk b1 b2 =>
          dsimp only at h1 h2 hs1 hs2
          subst h1
          exact lt_asymm hs1 hs2
    · rintro ⟨rfl | hlt, hnot⟩
      · exact (hnot (Or.inl rfl)).elim
      · exact hlt
  toDecidableLE := Classical.decRel _

private lemma lexSigma_snd_eq {α : Type} {β : α → Type} {a : α} {b₁ b₂ : β a}
    (h : (⟨a, b₁⟩ : LexSigma β) = ⟨a, b₂⟩) : b₁ = b₂ := by
  cases h; rfl

private lemma lexSigma_le_iff {α : Type} [LinearOrder α] {β : α → Type}
    [∀ a, LinearOrder (β a)] (x y : LexSigma β) :
    x ≤ y ↔ x.fst < y.fst ∨ ∃ h : x.fst = y.fst, cast (by rw [h]) x.snd ≤ y.snd := by
  rcases x with ⟨a₁, b₁⟩; rcases y with ⟨a₂, b₂⟩
  constructor
  · rintro (hEq | hlt | ⟨h, hs⟩)
    · cases hEq; exact Or.inr ⟨rfl, le_rfl⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨h, le_of_lt hs⟩
  · rintro (hlt | ⟨h, hs⟩)
    · exact Or.inr (Or.inl hlt)
    · dsimp only at h hs; subst h
      rw [cast_eq] at hs
      rcases lt_or_eq_of_le hs with hlt | rfl
      · exact Or.inr (Or.inr ⟨rfl, hlt⟩)
      · exact Or.inl rfl

private instance lexSigmaWellFoundedLT {α : Type} [LinearOrder α] [WellFoundedLT α]
    {β : α → Type} [∀ a, LinearOrder (β a)] [∀ a, WellFoundedLT (β a)] :
    WellFoundedLT (LexSigma β) := by
  have hAcc : ∀ (a : α) (b : β a), Acc (· < · : LexSigma β → _ → Prop) ⟨a, b⟩ := fun a =>
    wellFounded_lt.induction
      (C := fun a => ∀ b : β a, Acc (· < · : LexSigma β → _ → Prop) ⟨a, b⟩) a fun a iha b =>
      wellFounded_lt.induction
        (C := fun b => Acc (· < · : LexSigma β → _ → Prop) ⟨a, b⟩) b fun b ihb =>
        Acc.intro (⟨a, b⟩ : LexSigma β) fun x hlt => by
          rcases x with ⟨a', b'⟩
          rcases hlt with h1 | ⟨h1, hs⟩
          · exact iha a' h1 b'
          · dsimp only at h1 hs
            subst h1
            exact ihb b' hs
  exact ⟨⟨fun ⟨a, b⟩ => hAcc a b⟩⟩

private abbrev NatPowSum : Type := LexSigma (fun n : ℕ => PowW1 (n + 1))

private lemma powW1_le_emb {a b : ℕ} (h : a ≤ b) : Nonempty (PowW1 a ↪o PowW1 b) := by
  have hle : ω_ 1 ^ (a : Ordinal.{0}) ≤ ω_ 1 ^ (b : Ordinal.{0}) :=
    Ordinal.opow_le_opow_right (Ordinal.omega_pos 1) (Nat.cast_le.mpr h)
  rw [← Ordinal.type_toType (ω_ 1 ^ (a : Ordinal.{0})),
      ← Ordinal.type_toType (ω_ 1 ^ (b : Ordinal.{0}))] at hle
  obtain ⟨e⟩ := Ordinal.type_le_iff'.mp hle
  exact ⟨⟨e.toEmbedding, by
    intro x y
    constructor
    · intro hxy
      rcases lt_or_eq_of_le hxy with hlt | heq
      · exact le_of_lt (e.map_rel_iff.mp hlt)
      · exact le_of_eq (e.injective heq)
    · intro hxy
      rcases lt_or_eq_of_le hxy with hlt | heq
      · exact le_of_lt (e.map_rel_iff.mpr hlt)
      · exact le_of_eq (congrArg e heq)⟩⟩

private lemma typeLT_natPowSum : typeLT NatPowSum = ω_ 1 ^ ω := by
  apply le_antisymm
  · apply typeLT_le_of_forall_Iio_lt
    rintro ⟨n, z⟩
    have hemb_all : ∀ k : Fin (n + 1), Nonempty (PowW1 (k.1 + 1) ↪o PowW1 (n + 1)) :=
      fun k => powW1_le_emb (by omega)
    let ePow (k : Fin (n + 1)) := Classical.choice (hemb_all k)
    have hlt_le : ∀ {x : NatPowSum}, x < ⟨n, z⟩ → x.fst < n + 1 := by
      rintro ⟨k, y⟩ hlt
      change k < n + 1
      rcases hlt with h1 | ⟨h1, _⟩ <;> (dsimp only at h1; omega)
    let emb : Set.Iio (⟨n, z⟩ : NatPowSum) ↪o (Fin (n + 1) ×ₗ PowW1 (n + 1)) :=
      ⟨⟨fun ⟨⟨k, y⟩, hlt⟩ =>
          have hk : k < n + 1 := hlt_le hlt
          toLex (⟨k, hk⟩, ePow ⟨k, hk⟩ y),
        by
          rintro ⟨⟨k₁, y₁⟩, h1⟩ ⟨⟨k₂, y₂⟩, h2⟩ hEq
          have h' := congrArg ofLex hEq
          simp only [ofLex_toLex, Prod.mk.injEq, Fin.mk.injEq] at h'
          obtain ⟨hk, hy⟩ := h'
          subst hk
          have hy' := (ePow ⟨k₁, _⟩).injective hy
          exact Subtype.ext (by simp [hy'])⟩,
        by
          rintro ⟨⟨k₁, y₁⟩, h1⟩ ⟨⟨k₂, y₂⟩, h2⟩
          change (toLex (⟨k₁, hlt_le h1⟩, ePow ⟨k₁, hlt_le h1⟩ y₁) :
              Fin (n + 1) ×ₗ PowW1 (n + 1)) ≤
            toLex (⟨k₂, hlt_le h2⟩, ePow ⟨k₂, hlt_le h2⟩ y₂) ↔
            (⟨⟨k₁, y₁⟩, h1⟩ : Set.Iio (⟨n, z⟩ : NatPowSum)) ≤ ⟨⟨k₂, y₂⟩, h2⟩
          rw [Prod.Lex.le_iff]
          simp only [ofLex_toLex, Fin.lt_def, Fin.mk.injEq]
          constructor
          · rintro (h | ⟨rfl, h⟩)
            · exact Or.inr (Or.inl h)
            · rcases lt_or_eq_of_le ((ePow ⟨k₁, _⟩).le_iff_le.mp h) with hlt | rfl
              · exact Or.inr (Or.inr ⟨rfl, hlt⟩)
              · exact Or.inl rfl
          · rintro (hEq | h | ⟨h, hs⟩)
            · cases hEq; exact Or.inr ⟨rfl, le_rfl⟩
            · exact Or.inl h
            · dsimp only at h hs; subst h
              exact Or.inr ⟨rfl, (ePow ⟨k₁, _⟩).le_iff_le.mpr hs.le⟩⟩
    have hle := typeLT_le_of_orderEmbedding emb
    have hprod : typeLT (Fin (n + 1) ×ₗ PowW1 (n + 1)) =
        (ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0})) * ((n + 1 : ℕ) : Ordinal.{0}) := by
      have hlex : typeLT (Fin (n + 1) ×ₗ PowW1 (n + 1)) =
          Ordinal.type (Prod.Lex (· < · : Fin (n + 1) → _ → Prop)
            (· < · : PowW1 (n + 1) → _ → Prop)) :=
        Ordinal.type_eq.mpr ⟨⟨ofLex, Iff.rfl⟩⟩
      rw [hlex, Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_fin]
    rw [hprod] at hle
    refine hle.trans_lt ?_
    have h1 : (ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0})) * ((n + 1 : ℕ) : Ordinal.{0}) <
        ω_ 1 ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
      have hnat : ((n + 1 : ℕ) : Ordinal.{0}) < ω_ 1 :=
        (Ordinal.natCast_lt_omega0 (n + 1)).trans omega0_lt_omega1
      have h2 : (ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0})) * ω_ 1 =
          ω_ 1 ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
        rw [← Ordinal.opow_add_one, ← Nat.cast_one, ← Nat.cast_add]
      rw [← h2]
      exact mul_lt_mul_of_pos_left hnat (Ordinal.opow_pos _ (Ordinal.omega_pos 1))
    exact h1.trans ((Ordinal.isNormal_opow
      (lt_trans Ordinal.one_lt_omega0 omega0_lt_omega1)).strictMono
      (Ordinal.natCast_lt_omega0 (n + 2)))
  · have hsup : ω_ 1 ^ ω = ⨆ n : ℕ, ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0}) := by
      apply le_antisymm
      · rw [← Ordinal.iSup_pow_natCast (Ordinal.omega_pos 1)]
        refine ciSup_le' fun n => ?_
        rw [← Ordinal.opow_natCast]
        refine le_trans (Ordinal.opow_le_opow_right (Ordinal.omega_pos 1)
          (Nat.cast_le.mpr (Nat.le_succ n))) ?_
        exact le_ciSup Ordinal.bddAbove_of_small n
      · refine ciSup_le' fun n => ?_
        exact Ordinal.opow_le_opow_right (Ordinal.omega_pos 1)
          (Ordinal.natCast_lt_omega0 (n + 1)).le
    rw [hsup]
    refine ciSup_le' fun n => ?_
    let emb : PowW1 (n + 1) ↪o NatPowSum :=
      ⟨⟨fun y => ⟨n, y⟩, fun y₁ y₂ h => by cases h; rfl⟩, by
        intro y₁ y₂
        constructor
        · rintro (hEq | h | ⟨_, hs⟩)
          · cases hEq; exact le_rfl
          · exact (lt_irrefl n h).elim
          · exact le_of_lt hs
        · intro hle
          rcases lt_or_eq_of_le hle with hlt | rfl
          · exact Or.inr (Or.inr ⟨rfl, hlt⟩)
          · exact Or.inl rfl⟩
    simpa only [Ordinal.type_toType] using typeLT_le_of_orderEmbedding emb

private lemma omega1_pow_omega_succ_iso :
    Nonempty (((ω_ 1 ^ (ω + 1) : Ordinal.{0})).ToType ≃o (W1 ×ₗ NatPowSum)) := by
  have h : typeLT ((ω_ 1 ^ (ω + 1) : Ordinal.{0})).ToType = typeLT (W1 ×ₗ NatPowSum) := by
    rw [Ordinal.type_toType, Ordinal.opow_add_one]
    have hlex : typeLT (W1 ×ₗ NatPowSum) =
        Ordinal.type (Prod.Lex (· < · : W1 → _ → Prop) (· < · : NatPowSum → _ → Prop)) :=
      Ordinal.type_eq.mpr ⟨⟨ofLex, Iff.rfl⟩⟩
    rw [hlex, Ordinal.type_prod_lex, Ordinal.type_toType, typeLT_natPowSum]
  exact orderIso_of_typeLT_eq h

/-- Helper: if `S ⊆ W1 ×ₗ NatPowSum` preserves `PowW1 (n + 2)` on slice `n`, then cofinally many
rows `ξ : W1` embed `PowW1 (n + 1)` inside slice `n`. -/
private lemma omega1_pow_omega_succ_cofinal (S : Set (W1 ×ₗ NatPowSum)) (n : ℕ)
    (hSn : Nonempty (PowW1 (n + 2) ↪o
      {p : W1 ×ₗ PowW1 (n + 1) // toLex ((ofLex p).1, ⟨n, (ofLex p).2⟩) ∈ S}))
    (ξ₀ : W1) :
    ∃ ξ : W1, ξ₀ < ξ ∧
      Nonempty (PowW1 (n + 1) ↪o {y : PowW1 (n + 1) // toLex (ξ, ⟨n, y⟩) ∈ S}) := by
  by_contra hall
  push Not at hall
  let P := {p : W1 ×ₗ PowW1 (n + 1) // toLex ((ofLex p).1, ⟨n, (ofLex p).2⟩) ∈ S}
  let P_lo := {p : P // (ofLex p.1).1 ≤ ξ₀}
  let P_hi := {p : P // ξ₀ < (ofLex p.1).1}
  have hsplit : typeLT P ≤ typeLT P_lo + typeLT P_hi := by
    let f : P → (P_lo ⊕ₗ P_hi) := fun p =>
      if h : (ofLex p.1).1 ≤ ξ₀ then toLex (Sum.inl ⟨p, h⟩)
      else toLex (Sum.inr ⟨p, not_le.mp h⟩)
    have hle : typeLT P ≤ typeLT (P_lo ⊕ₗ P_hi) := by
      refine Ordinal.type_le_iff'.mpr ⟨⟨⟨f, by
          intro p₁ p₂ h
          dsimp only [f] at h
          split_ifs at h with h1 h2 h2
          · exact congrArg Subtype.val (Sum.inl.inj (toLex.injective h))
          · exact (Sum.inl_ne_inr (toLex.injective h)).elim
          · exact (Sum.inr_ne_inl (toLex.injective h)).elim
          · exact congrArg Subtype.val (Sum.inr.inj (toLex.injective h))⟩,
        fun {p₁ p₂} => by
          change f p₁ < f p₂ ↔ p₁ < p₂
          dsimp only [f]
          split_ifs with h1 h2 h2
          · rw [sumLex_lt_inl_inl]; exact Iff.rfl
          · simp only [sumLex_lt_inl_inr, true_iff]
            have hlt : (ofLex p₁.1).1 < (ofLex p₂.1).1 := lt_of_le_of_lt h1 (not_le.mp h2)
            exact Prod.Lex.lt_iff.mpr (Or.inl hlt)
          · simp only [sumLex_not_lt_inr_inl, false_iff]
            have hlt : (ofLex p₂.1).1 < (ofLex p₁.1).1 := lt_of_le_of_lt h2 (not_le.mp h1)
            exact not_lt_of_gt (Prod.Lex.lt_iff.mpr (Or.inl hlt))
          · rw [sumLex_lt_inr_inr]; exact Iff.rfl⟩⟩
    have hsum : typeLT (P_lo ⊕ₗ P_hi) = typeLT P_lo + typeLT P_hi := by
      have hlex : typeLT (P_lo ⊕ₗ P_hi) =
          Ordinal.type (Sum.Lex (· < · : P_lo → _ → Prop) (· < · : P_hi → _ → Prop)) :=
        Ordinal.type_eq.mpr ⟨⟨ofLex, Iff.rfl⟩⟩
      rw [hlex, Ordinal.type_sum_lex]
    exact hsum ▸ hle
  -- Bound `typeLT P_lo < ω_ 1 ^ (n + 2)`:
  have hlo_lt : typeLT P_lo < ω_ 1 ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
    let emb : P_lo ↪o (Set.Iic ξ₀ ×ₗ PowW1 (n + 1)) :=
      ⟨⟨fun ⟨⟨p, _⟩, hp⟩ => toLex (⟨(ofLex p).1, hp⟩, (ofLex p).2),
        by
          rintro ⟨⟨p₁, hp₁⟩, hle₁⟩ ⟨⟨p₂, hp₂⟩, hle₂⟩ h
          have h' := congrArg ofLex h
          simp only [ofLex_toLex, Prod.mk.injEq] at h'
          exact Subtype.ext (Subtype.ext (ofLex.injective (Prod.ext (congrArg Subtype.val h'.1) h'.2)))⟩,
        by
          rintro ⟨⟨p₁, hp₁⟩, hle₁⟩ ⟨⟨p₂, hp₂⟩, hle₂⟩
          change (toLex (⟨(ofLex p₁).1, hle₁⟩, (ofLex p₁).2) : Set.Iic ξ₀ ×ₗ PowW1 (n + 1)) ≤
              toLex (⟨(ofLex p₂).1, hle₂⟩, (ofLex p₂).2) ↔ p₁ ≤ p₂
          rw [Prod.Lex.le_iff, Prod.Lex.le_iff]
          simp only [ofLex_toLex]
          exact or_congr Iff.rfl (and_congr
            ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩ Iff.rfl)⟩
    have hle := typeLT_le_of_orderEmbedding emb
    have hprod : typeLT (Set.Iic ξ₀ ×ₗ PowW1 (n + 1)) =
        (ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0})) * typeLT (Set.Iic ξ₀) := by
      have hlex : typeLT (Set.Iic ξ₀ ×ₗ PowW1 (n + 1)) =
          Ordinal.type (Prod.Lex (· < · : Set.Iic ξ₀ → _ → Prop)
            (· < · : PowW1 (n + 1) → _ → Prop)) :=
        Ordinal.type_eq.mpr ⟨⟨ofLex, Iff.rfl⟩⟩
      rw [hlex, Ordinal.type_prod_lex, Ordinal.type_toType]
    rw [hprod] at hle
    have hIic_lt : typeLT (Set.Iic ξ₀) < ω_ 1 := by
      have hcard : #(Set.Iic ξ₀) = (typeLT (Set.Iic ξ₀)).card := (Ordinal.card_type _).symm
      rw [Cardinal.lt_omega_iff_card_lt, ← hcard]
      exact (set_countable_iff_card_lt_aleph1 (Set.Iic ξ₀)).mp (w1_Iic_countable ξ₀)
    have hmul : (ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0})) * ω_ 1 =
        ω_ 1 ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
      rw [← Ordinal.opow_add_one, ← Nat.cast_one, ← Nat.cast_add]
    rw [← hmul]
    exact hle.trans_lt (mul_lt_mul_of_pos_left hIic_lt
      (Ordinal.opow_pos _ (Ordinal.omega_pos 1)))
  -- Bound `typeLT P_hi ≤ ω_ 1 ^ (n + 1)`:
  have hhi_le : typeLT P_hi ≤ ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0}) := by
    apply typeLT_le_of_forall_Iio_lt
    intro pstar
    let ξstar : W1 := (ofLex pstar.1.1).1
    have hfib_lt : ∀ ξ : Set.Iic ξstar,
        ∃ η : Ordinal.{0}, η < ω_ 1 ∧
          (ξ₀ < ξ.1 → typeLT {y : PowW1 (n + 1) // toLex (ξ.1, ⟨n, y⟩) ∈ S} ≤
            (ω_ 1 ^ (n : Ordinal.{0})) * η) := by
      intro ξ
      by_cases hgt : ξ₀ < ξ.1
      · have hlt_pow : typeLT {y : PowW1 (n + 1) // toLex (ξ.1, ⟨n, y⟩) ∈ S} <
            ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0}) := by
          by_contra hge
          push Not at hge
          have hge' : typeLT (PowW1 (n + 1)) ≤
              typeLT {y : PowW1 (n + 1) // toLex (ξ.1, ⟨n, y⟩) ∈ S} := by
            rwa [Ordinal.type_toType]
          obtain ⟨e⟩ := Ordinal.type_le_iff'.mp hge'
          exact (hall ξ.1 hgt).false ⟨e.toEmbedding, by
            intro a b
            constructor
            · intro hab
              rcases lt_or_eq_of_le hab with hlt | hEq
              · exact le_of_lt (e.map_rel_iff.mp hlt)
              · exact le_of_eq (e.injective hEq)
            · intro hab
              rcases lt_or_eq_of_le hab with hlt | hEq
              · exact le_of_lt (e.map_rel_iff.mpr hlt)
              · exact le_of_eq (congrArg e hEq)⟩
        let α := typeLT {y : PowW1 (n + 1) // toLex (ξ.1, ⟨n, y⟩) ∈ S}
        let q := α / (ω_ 1 ^ (n : Ordinal.{0})) + 1
        have hq_lt : q < ω_ 1 := by
          have hdiv_lt : α / (ω_ 1 ^ (n : Ordinal.{0})) < ω_ 1 := by
            rw [← Ordinal.lt_mul_iff_div_lt (Ordinal.opow_pos _ (Ordinal.omega_pos 1)).ne']
            simpa only [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one] using hlt_pow
          have h1lt : (1 : Ordinal.{0}) < ω_ 1 := by
            simpa only [Nat.cast_one] using (Ordinal.natCast_lt_omega0 1).trans omega0_lt_omega1
          rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_add]
          have hc1 : (α / (ω_ 1 ^ (n : Ordinal.{0}))).card < ℵ₁ :=
            Cardinal.lt_omega_iff_card_lt.mp hdiv_lt
          have hc2 : (1 : Ordinal.{0}).card < ℵ₁ :=
            Cardinal.lt_omega_iff_card_lt.mp h1lt
          exact Cardinal.add_lt_of_lt Cardinal.aleph0_lt_aleph_one.le hc1 hc2
        refine ⟨q, hq_lt, fun _ => ?_⟩
        have hdiv_add := Ordinal.div_add_mod α (ω_ 1 ^ (n : Ordinal.{0}))
        have hmod_lt := Ordinal.mod_lt α (Ordinal.opow_pos (n : Ordinal.{0}) (Ordinal.omega_pos 1)).ne'
        calc α = (ω_ 1 ^ (n : Ordinal.{0})) * (α / (ω_ 1 ^ (n : Ordinal.{0}))) +
              α % (ω_ 1 ^ (n : Ordinal.{0})) := hdiv_add.symm
          _ ≤ (ω_ 1 ^ (n : Ordinal.{0})) * (α / (ω_ 1 ^ (n : Ordinal.{0}))) +
              (ω_ 1 ^ (n : Ordinal.{0})) := add_le_add_right hmod_lt.le _
          _ = (ω_ 1 ^ (n : Ordinal.{0})) * q := by dsimp only [q]; rw [mul_add, mul_one]
      · exact ⟨0, Ordinal.omega_pos 1, fun h => (hgt h).elim⟩
    choose η hη_lt hη_le using hfib_lt
    have : Countable (Set.Iic ξstar) := Set.countable_coe_iff.mpr (w1_Iic_countable ξstar)
    let ηstar : Ordinal.{0} := ⨆ ξ : Set.Iic ξstar, η ξ
    have hηstar_lt : ηstar < ω_ 1 := Ordinal.iSup_lt_omega_one hη_lt
    have hemb_fib : ∀ ξ : Set.Iic ξstar, ξ₀ < ξ.1 →
        Nonempty ({y : PowW1 (n + 1) // toLex (ξ.1, ⟨n, y⟩) ∈ S} ↪o
          ((ω_ 1 ^ (n : Ordinal.{0})) * ηstar).ToType) := by
      intro ξ hgt
      have hle : typeLT {y : PowW1 (n + 1) // toLex (ξ.1, ⟨n, y⟩) ∈ S} ≤
          typeLT ((ω_ 1 ^ (n : Ordinal.{0})) * ηstar).ToType := by
        rw [Ordinal.type_toType]
        refine (hη_le ξ hgt).trans ?_
        have hsup := le_ciSup (f := η) Ordinal.bddAbove_of_small ξ
        gcongr
      obtain ⟨e⟩ := Ordinal.type_le_iff'.mp hle
      exact ⟨⟨e.toEmbedding, by
        intro a b
        constructor
        · intro hab
          rcases lt_or_eq_of_le hab with hlt | hEq
          · exact le_of_lt (e.map_rel_iff.mp hlt)
          · exact le_of_eq (e.injective hEq)
        · intro hab
          rcases lt_or_eq_of_le hab with hlt | hEq
          · exact le_of_lt (e.map_rel_iff.mpr hlt)
          · exact le_of_eq (congrArg e hEq)⟩⟩
    let efib (ξ : Set.Iic ξstar) (hgt : ξ₀ < ξ.1) := Classical.choice (hemb_fib ξ hgt)
    have hle_of_Iio : ∀ {p : P_hi}, p < pstar → (ofLex p.1.1).1 ≤ ξstar := fun hp => by
      rcases Prod.Lex.lt_iff.mp hp with h1 | ⟨h1, _⟩
      · exact le_of_lt h1
      · exact le_of_eq h1
    let embIio : Set.Iio pstar ↪o
        (Set.Iic ξstar ×ₗ ((ω_ 1 ^ (n : Ordinal.{0})) * ηstar).ToType) :=
      ⟨⟨fun ⟨p, hp⟩ =>
          let ξ : Set.Iic ξstar := ⟨(ofLex p.1.1).1, hle_of_Iio hp⟩
          toLex (ξ, efib ξ p.2 ⟨(ofLex p.1.1).2, p.1.2⟩),
        by
          rintro ⟨⟨⟨ap, hap⟩, ha''⟩, ha⟩ ⟨⟨⟨bp, hbp⟩, hb''⟩, hb⟩ hEq
          have h' := congrArg ofLex hEq
          simp only [ofLex_toLex, Prod.mk.injEq] at h'
          obtain ⟨h1sub, h2⟩ := h'
          have h1 : (ofLex ap).1 = (ofLex bp).1 := congrArg Subtype.val h1sub
          have heq_y : (ofLex ap).2 = (ofLex bp).2 := by
            have hstep : ∀ (x y : Set.Iic ξstar) (hx : ξ₀ < x.1) (hy : ξ₀ < y.1)
                (_ : x = y) (u : {y' // toLex (x.1, ⟨n, y'⟩) ∈ S})
                (v : {y' // toLex (y.1, ⟨n, y'⟩) ∈ S}),
                efib x hx u = efib y hy v → u.1 = v.1 := by
              rintro x _ hx hy rfl u v h'
              exact congrArg Subtype.val ((efib x hx).injective h')
            exact hstep ⟨(ofLex ap).1, hle_of_Iio ha⟩ ⟨(ofLex bp).1, hle_of_Iio hb⟩
              ha'' hb'' h1sub ⟨(ofLex ap).2, hap⟩ ⟨(ofLex bp).2, hbp⟩ h2
          exact Subtype.ext (Subtype.ext (Subtype.ext (ofLex.injective (Prod.ext h1 heq_y))))⟩,
        by
          rintro ⟨⟨⟨ap, hap⟩, ha''⟩, ha⟩ ⟨⟨⟨bp, hbp⟩, hb''⟩, hb⟩
          change (toLex (⟨(ofLex ap).1, hle_of_Iio ha⟩,
              efib ⟨(ofLex ap).1, hle_of_Iio ha⟩ ha'' ⟨(ofLex ap).2, hap⟩) :
              Set.Iic ξstar ×ₗ ((ω_ 1 ^ (n : Ordinal.{0})) * ηstar).ToType) ≤
            toLex (⟨(ofLex bp).1, hle_of_Iio hb⟩,
              efib ⟨(ofLex bp).1, hle_of_Iio hb⟩ hb'' ⟨(ofLex bp).2, hbp⟩) ↔
            ap ≤ bp
          rw [Prod.Lex.le_iff, Prod.Lex.le_iff]
          simp only [ofLex_toLex]
          constructor
          · rintro (h | ⟨h1sub, h2⟩)
            · exact Or.inl h
            · have h1 : (ofLex ap).1 = (ofLex bp).1 := congrArg Subtype.val h1sub
              refine Or.inr ⟨h1, ?_⟩
              have hstep : ∀ (x y : Set.Iic ξstar) (hx : ξ₀ < x.1) (hy : ξ₀ < y.1)
                  (_ : x = y) (u : {y' // toLex (x.1, ⟨n, y'⟩) ∈ S})
                  (v : {y' // toLex (y.1, ⟨n, y'⟩) ∈ S}),
                  efib x hx u ≤ efib y hy v → u.1 ≤ v.1 := by
                rintro x _ hx hy rfl u v h'
                exact (efib x hx).le_iff_le.mp h'
              exact hstep ⟨(ofLex ap).1, hle_of_Iio ha⟩ ⟨(ofLex bp).1, hle_of_Iio hb⟩
                ha'' hb'' h1sub ⟨(ofLex ap).2, hap⟩ ⟨(ofLex bp).2, hbp⟩ h2
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · refine Or.inr ⟨Subtype.ext h1, ?_⟩
              have hstep : ∀ (x y : Set.Iic ξstar) (hx : ξ₀ < x.1) (hy : ξ₀ < y.1)
                  (_ : x = y) (u : {y' // toLex (x.1, ⟨n, y'⟩) ∈ S})
                  (v : {y' // toLex (y.1, ⟨n, y'⟩) ∈ S}),
                  u.1 ≤ v.1 → efib x hx u ≤ efib y hy v := by
                rintro x _ hx hy rfl u v h'
                exact (efib x hx).le_iff_le.mpr h'
              exact hstep ⟨(ofLex ap).1, hle_of_Iio ha⟩ ⟨(ofLex bp).1, hle_of_Iio hb⟩
                ha'' hb'' (Subtype.ext h1) ⟨(ofLex ap).2, hap⟩ ⟨(ofLex bp).2, hbp⟩ h2⟩
    have hle := typeLT_le_of_orderEmbedding embIio
    have hprod : typeLT (Set.Iic ξstar ×ₗ ((ω_ 1 ^ (n : Ordinal.{0})) * ηstar).ToType) =
        ((ω_ 1 ^ (n : Ordinal.{0})) * ηstar) * typeLT (Set.Iic ξstar) := by
      have hlex : typeLT (Set.Iic ξstar ×ₗ ((ω_ 1 ^ (n : Ordinal.{0})) * ηstar).ToType) =
          Ordinal.type (Prod.Lex (· < · : Set.Iic ξstar → _ → Prop)
            (· < · : ((ω_ 1 ^ (n : Ordinal.{0})) * ηstar).ToType → _ → Prop)) :=
        Ordinal.type_eq.mpr ⟨⟨ofLex, Iff.rfl⟩⟩
      rw [hlex, Ordinal.type_prod_lex, Ordinal.type_toType]
    rw [hprod, mul_assoc] at hle
    have hIic_lt : typeLT (Set.Iic ξstar) < ω_ 1 := by
      have hcard : #(Set.Iic ξstar) = (typeLT (Set.Iic ξstar)).card := (Ordinal.card_type _).symm
      rw [Cardinal.lt_omega_iff_card_lt, ← hcard]
      exact (set_countable_iff_card_lt_aleph1 (Set.Iic ξstar)).mp (w1_Iic_countable ξstar)
    have hmul_lt : ηstar * typeLT (Set.Iic ξstar) < ω_ 1 := by
      rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_mul]
      exact Cardinal.mul_lt_of_lt Cardinal.aleph0_lt_aleph_one.le
        (Cardinal.lt_omega_iff_card_lt.mp hηstar_lt) (Cardinal.lt_omega_iff_card_lt.mp hIic_lt)
    have hpow : (ω_ 1 ^ (n : Ordinal.{0})) * ω_ 1 = ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0}) := by
      rw [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one]
    exact (hle.trans_lt (mul_lt_mul_of_pos_left hmul_lt
      (Ordinal.opow_pos _ (Ordinal.omega_pos 1)))).trans_eq hpow
  -- Combine `hlo_lt` and `hhi_le` to contradict `hSn`:
  have hsum_lt : typeLT P_lo + typeLT P_hi < ω_ 1 ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
    have hpow : (ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0})) * ω_ 1 =
        ω_ 1 ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
      rw [← Ordinal.opow_add_one, ← Nat.cast_one, ← Nat.cast_add]
    let α_lo : Ordinal.{0} := typeLT P_lo
    let d_pow : Ordinal.{0} := ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0})
    have hd_pos : 0 < d_pow := Ordinal.opow_pos _ (Ordinal.omega_pos 1)
    have hq_lt : α_lo / d_pow < ω_ 1 := by
      rw [← Ordinal.lt_mul_iff_div_lt hd_pos.ne', hpow]
      exact hlo_lt
    have hlo_le : α_lo ≤ d_pow * (α_lo / d_pow + 1) := by
      have h1 := Ordinal.div_add_mod α_lo d_pow
      have h2 := Ordinal.mod_lt α_lo hd_pos.ne'
      calc α_lo = d_pow * (α_lo / d_pow) + α_lo % d_pow := h1.symm
        _ ≤ d_pow * (α_lo / d_pow) + d_pow := add_le_add_right h2.le _
        _ = d_pow * (α_lo / d_pow + 1) := by rw [mul_add, mul_one]
    have hq2_lt : α_lo / d_pow + 2 < ω_ 1 := by
      rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_add]
      exact Cardinal.add_lt_of_lt Cardinal.aleph0_lt_aleph_one.le
        (Cardinal.lt_omega_iff_card_lt.mp hq_lt)
        (Cardinal.lt_omega_iff_card_lt.mp ((Ordinal.natCast_lt_omega0 2).trans omega0_lt_omega1))
    have hmul2 : d_pow * (α_lo / d_pow + 1) + d_pow = d_pow * (α_lo / d_pow + 2) := by
      calc d_pow * (α_lo / d_pow + 1) + d_pow
          = d_pow * (α_lo / d_pow + 1) + d_pow * 1 := by rw [mul_one]
        _ = d_pow * ((α_lo / d_pow + 1) + 1) := (mul_add _ _ _).symm
        _ = d_pow * (α_lo / d_pow + 2) := by rw [add_assoc]; norm_num
    calc α_lo + typeLT P_hi
        ≤ d_pow * (α_lo / d_pow + 1) + d_pow := add_le_add hlo_le hhi_le
      _ = d_pow * (α_lo / d_pow + 2) := hmul2
      _ < d_pow * ω_ 1 := mul_lt_mul_of_pos_left hq2_lt hd_pos
      _ = ω_ 1 ^ ((n + 2 : ℕ) : Ordinal.{0}) := hpow
  obtain ⟨eP⟩ := hSn
  have hge : ω_ 1 ^ ((n + 2 : ℕ) : Ordinal.{0}) ≤ typeLT P := by
    simpa only [Ordinal.type_toType] using typeLT_le_of_orderEmbedding eP
  exact not_lt_of_ge (hge.trans hsplit) hsum_lt

/-- **Reordering Lift Lemma for `ω_ 1 ^ (ω + 1)`**:
If `S ⊆ W1 ×ₗ NatPowSum` preserves `PowW1 (n + 2)` on every horizontal slice `n : ℕ`,
then `W1 ×ₗ NatPowSum` embeds order-preservingly into `S`. -/
private theorem omega1_pow_omega_succ_lift (S : Set (W1 ×ₗ NatPowSum))
    (hS : ∀ n : ℕ, Nonempty (PowW1 (n + 2) ↪o
      {p : W1 ×ₗ PowW1 (n + 1) // toLex ((ofLex p).1, ⟨n, (ofLex p).2⟩) ∈ S})) :
    Nonempty ((W1 ×ₗ NatPowSum) ↪o S) := by
  have hcofinal : ∀ (n : ℕ) (ξ₀ : W1), ∃ ξ : W1, ξ₀ < ξ ∧
      Nonempty (PowW1 (n + 1) ↪o {y : PowW1 (n + 1) // toLex (ξ, ⟨n, y⟩) ∈ S}) :=
    fun n ξ₀ => omega1_pow_omega_succ_cofinal S n (hS n) ξ₀
  choose nxt hnxt_gt hnxt_emb using hcofinal
  have hIio_count : ∀ u : W1 ×ₗ ℕ, (Set.Iio u).Countable := fun u => by
    have hsub : Set.Iio u ⊆ (fun p => toLex p) '' (Set.Iic (ofLex u).1 ×ˢ (Set.univ : Set ℕ)) := by
      intro v hv
      refine ⟨ofLex v, ⟨?_, trivial⟩, toLex_ofLex v⟩
      rcases Prod.Lex.lt_iff.mp hv with h1 | ⟨h1, _⟩
      · exact le_of_lt h1
      · exact le_of_eq h1
    exact (((w1_Iic_countable (ofLex u).1).prod Set.countable_univ).image _).mono hsub
  let stepRec : (u : W1 ×ₗ ℕ) → ((v : W1 ×ₗ ℕ) → v < u → W1) → W1 := fun u rec =>
    have : Countable (Set.Iio u) := Set.countable_coe_iff.mpr (hIio_count u)
    let prev : Set W1 := Set.range fun v : Set.Iio u => rec v.1 v.2
    let ξ₀ := Classical.choose (w1_exists_gt_of_countable (Set.countable_range (fun v : Set.Iio u => rec v.1 v.2)))
    nxt (ofLex u).2 ξ₀
  let g : (W1 ×ₗ ℕ) → W1 := WellFounded.fix wellFounded_lt stepRec
  have hg_lt : ∀ u v : W1 ×ₗ ℕ, v < u → g v < g u := by
    intro u v hvu
    have hfix : g u = stepRec u (fun w _ => g w) := WellFounded.fix_eq wellFounded_lt stepRec u
    rw [hfix]
    dsimp only [stepRec]
    have : Countable (Set.Iio u) := Set.countable_coe_iff.mpr (hIio_count u)
    have hξ₀ := Classical.choose_spec (w1_exists_gt_of_countable
      (Set.countable_range (fun w : Set.Iio u => g w.1)))
    have hv_lt := hξ₀ (g v) ⟨⟨v, hvu⟩, rfl⟩
    exact hv_lt.trans (hnxt_gt (ofLex u).2 _)
  have hg_emb : ∀ u : W1 ×ₗ ℕ,
      Nonempty (PowW1 ((ofLex u).2 + 1) ↪o
        {y : PowW1 ((ofLex u).2 + 1) // toLex (g u, ⟨(ofLex u).2, y⟩) ∈ S}) := by
    intro u
    have hfix : g u = stepRec u (fun w _ => g w) := WellFounded.fix_eq wellFounded_lt stepRec u
    rw [hfix]
    exact hnxt_emb (ofLex u).2 _
  let eg (u : W1 ×ₗ ℕ) := Classical.choice (hg_emb u)
  refine ⟨⟨⟨fun x =>
      let p := ofLex x
      let u : W1 ×ₗ ℕ := toLex (p.1, p.2.fst)
      ⟨toLex (g u, ⟨p.2.fst, (eg u p.2.snd).1⟩), (eg u p.2.snd).2⟩,
    by
      intro x₁ x₂ hEq
      have h1 := congrArg (fun z => ofLex z.1) hEq
      simp only [ofLex_toLex, Prod.mk.injEq] at h1
      obtain ⟨hgEq, hsigEq⟩ := h1
      have huEq : toLex ((ofLex x₁).1, (ofLex x₁).2.fst) =
          toLex ((ofLex x₂).1, (ofLex x₂).2.fst) := by
        rcases lt_trichotomy (toLex ((ofLex x₁).1, (ofLex x₁).2.fst))
            (toLex ((ofLex x₂).1, (ofLex x₂).2.fst)) with hlt | h | hgt
        · exact (ne_of_lt (hg_lt _ _ hlt) hgEq).elim
        · exact h
        · exact (ne_of_gt (hg_lt _ _ hgt) hgEq).elim
      have hp1 : (ofLex x₁).1 = (ofLex x₂).1 := congrArg (fun u => (ofLex u).1) huEq
      have hn1 : (ofLex x₁).2.fst = (ofLex x₂).2.fst := congrArg (fun u => (ofLex u).2) huEq
      apply ofLex.injective
      apply Prod.ext hp1
      cases h2x₁ : (ofLex x₁).2 with | mk n₁ y₁ =>
      cases h2x₂ : (ofLex x₂).2 with | mk n₂ y₂ =>
      rw [h2x₁, h2x₂] at hn1 hsigEq
      dsimp only at hn1 hsigEq
      subst hn1
      have hyEq : (eg (toLex ((ofLex x₁).1, n₁)) y₁).1 = (eg (toLex ((ofLex x₂).1, n₁)) y₂).1 :=
        lexSigma_snd_eq (β := fun n : ℕ => PowW1 (n + 1)) hsigEq
      rw [← hp1] at hyEq
      have hy := (eg (toLex ((ofLex x₁).1, n₁))).injective (Subtype.ext hyEq)
      rw [hy]⟩,
    by
      intro x₁ x₂
      have hlt_iff : ∀ a b : W1 ×ₗ NatPowSum, a < b →
          (toLex (g (toLex ((ofLex a).1, (ofLex a).2.fst)),
            ⟨(ofLex a).2.fst, (eg (toLex ((ofLex a).1, (ofLex a).2.fst)) (ofLex a).2.snd).1⟩) : W1 ×ₗ NatPowSum) <
          toLex (g (toLex ((ofLex b).1, (ofLex b).2.fst)),
            ⟨(ofLex b).2.fst, (eg (toLex ((ofLex b).1, (ofLex b).2.fst)) (ofLex b).2.snd).1⟩) := by
        intro a b hab
        rcases a with ⟨a1, ⟨an, ay⟩⟩
        rcases b with ⟨b1, ⟨bn, by'⟩⟩
        rcases Prod.Lex.lt_iff.mp hab with h1 | ⟨h1, h2⟩
        · apply Prod.Lex.lt_iff.mpr; left
          exact hg_lt _ _ (Prod.Lex.lt_iff.mpr (Or.inl h1))
        · have h1' : a1 = b1 := h1
          subst h1'
          rcases h2 with hn | h2'
          · apply Prod.Lex.lt_iff.mpr; left
            exact hg_lt _ _ (Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hn⟩))
          · have hsub : ∀ {m₁ m₂ : ℕ} (y₁ : PowW1 (m₁ + 1)) (y₂ : PowW1 (m₂ + 1))
                (heq : m₁ = m₂), cast (by rw [heq]) y₁ < y₂ →
                (toLex (g (toLex (a1, m₁)), ⟨m₁, (eg (toLex (a1, m₁)) y₁).1⟩) : W1 ×ₗ NatPowSum) <
                toLex (g (toLex (a1, m₂)), ⟨m₂, (eg (toLex (a1, m₂)) y₂).1⟩) := by
              rintro m₁ _ y₁ y₂ rfl hy'
              exact Prod.Lex.lt_iff.mpr
                (Or.inr ⟨rfl, Or.inr ⟨rfl, (eg (toLex (a1, m₁))).lt_iff_lt.mpr hy'⟩⟩)
            exact hsub ay by' h2'.1 h2'.2
      constructor
      · intro hle
        by_contra hgt
        push Not at hgt
        exact not_le_of_gt (hlt_iff x₂ x₁ hgt) hle
      · intro hle
        rcases lt_or_eq_of_le hle with hlt | rfl
        · exact le_of_lt (hlt_iff x₁ x₂ hlt)
        · exact le_rfl⟩⟩

/- ### Section 5: Base-`ω_ 1` decomposition and main theorem -/

private noncomputable def pieceOrd : Option ℕ → Ordinal.{0}
  | none => ω_ 1 ^ (ω + 1)
  | some n => ω_ 1 ^ ((n + 1 : ℕ) : Ordinal.{0})

/-- An ordinal `α` admits a countable well-ordered decomposition into copies of `ω_ 1 ^ (ω + 1)`
and finite powers `ω_ 1 ^ (n + 1)`. -/
private def Decomp (α : Ordinal.{0}) : Prop :=
  ∃ (A : Type) (_ : LinearOrder A) (_ : WellFoundedLT A) (_ : Countable A)
    (piece : A → Option ℕ),
    Nonempty (α.ToType ≃o LexSigma (fun a : A => (pieceOrd (piece a)).ToType))

private lemma decomp_zero : Decomp 0 := by
  refine ⟨Empty, inferInstance, inferInstance, inferInstance, Empty.elim, ?_⟩
  apply orderIso_of_typeLT_eq
  rw [Ordinal.type_toType]
  exact (Ordinal.type_eq_zero_iff_isEmpty.mpr ⟨fun x => x.fst.elim⟩).symm

private lemma decomp_piece (p : Option ℕ) : Decomp (pieceOrd p) := by
  refine ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => p, ⟨{
    toFun := fun x => ⟨(), x⟩
    invFun := fun x => x.snd
    left_inv := fun _ => rfl
    right_inv := fun ⟨(), _⟩ => rfl
    map_rel_iff' := fun {a b} => by
      constructor
      · rintro (hEq | hlt | ⟨_, hs⟩)
        · exact le_of_eq (congrArg LexSigma.snd hEq)
        · exact (lt_irrefl () hlt).elim
        · exact le_of_lt hs
      · intro hle
        rcases lt_or_eq_of_le hle with hlt | rfl
        · exact Or.inr (Or.inr ⟨rfl, hlt⟩)
        · exact Or.inl rfl }⟩⟩

private lemma decomp_omega1_pow_omega : Decomp (ω_ 1 ^ ω) := by
  refine ⟨ℕ, inferInstance, inferInstance, inferInstance, fun n => some n, ?_⟩
  apply orderIso_of_typeLT_eq
  rw [Ordinal.type_toType]
  exact typeLT_natPowSum.symm

private lemma decomp_add {α β : Ordinal.{0}} (hα : Decomp α) (hβ : Decomp β) :
    Decomp (α + β) := by
  obtain ⟨A, _, _, _, pA, ⟨eA⟩⟩ := hα
  obtain ⟨B, _, _, _, pB, ⟨eB⟩⟩ := hβ
  obtain ⟨eSum⟩ := add_toType_iso α β
  have : Countable (A ⊕ₗ B) := ofLex.injective.countable
  let pAB : (A ⊕ₗ B) → Option ℕ := fun u => match ofLex u with
    | Sum.inl a => pA a
    | Sum.inr b => pB b
  refine ⟨A ⊕ₗ B, inferInstance, inferInstance, inferInstance, pAB, ⟨eSum.trans {
    toFun := fun u => match ofLex u with
      | Sum.inl x => ⟨toLex (Sum.inl (eA x).fst), (eA x).snd⟩
      | Sum.inr y => ⟨toLex (Sum.inr (eB y).fst), (eB y).snd⟩
    invFun := fun z => match z with
      | ⟨u, v⟩ => match hu : ofLex u with
        | Sum.inl a => toLex (Sum.inl (eA.symm ⟨a, cast (by simp [pAB, hu]) v⟩))
        | Sum.inr b => toLex (Sum.inr (eB.symm ⟨b, cast (by simp [pAB, hu]) v⟩))
    left_inv := fun u => by
      cases hu : ofLex u with
      | inl x =>
        have hu' : u = toLex (Sum.inl x) := ofLex.injective (by simp [hu])
        subst hu'
        change toLex (Sum.inl (eA.symm ⟨(eA x).fst, (eA x).snd⟩)) = toLex (Sum.inl x)
        have hη : (⟨(eA x).fst, (eA x).snd⟩ : LexSigma (fun a : A => (pieceOrd (pA a)).ToType)) = eA x := rfl
        rw [hη, eA.symm_apply_apply]
      | inr y =>
        have hu' : u = toLex (Sum.inr y) := ofLex.injective (by simp [hu])
        subst hu'
        change toLex (Sum.inr (eB.symm ⟨(eB y).fst, (eB y).snd⟩)) = toLex (Sum.inr y)
        have hη : (⟨(eB y).fst, (eB y).snd⟩ : LexSigma (fun b : B => (pieceOrd (pB b)).ToType)) = eB y := rfl
        rw [hη, eB.symm_apply_apply]
    right_inv := fun ⟨u, v⟩ => by
      cases hu : ofLex u with
      | inl a =>
        have hu' : u = toLex (Sum.inl a) := ofLex.injective (by simp [hu])
        subst hu'
        change (⟨toLex (Sum.inl (eA (eA.symm ⟨a, v⟩)).fst), (eA (eA.symm ⟨a, v⟩)).snd⟩ :
            LexSigma (fun u => (pieceOrd (pAB u)).ToType)) = ⟨toLex (Sum.inl a), v⟩
        rw [eA.apply_symm_apply]
      | inr b =>
        have hu' : u = toLex (Sum.inr b) := ofLex.injective (by simp [hu])
        subst hu'
        change (⟨toLex (Sum.inr (eB (eB.symm ⟨b, v⟩)).fst), (eB (eB.symm ⟨b, v⟩)).snd⟩ :
            LexSigma (fun u => (pieceOrd (pAB u)).ToType)) = ⟨toLex (Sum.inr b), v⟩
        rw [eB.apply_symm_apply]
    map_rel_iff' := fun {u₁ u₂} => by
      cases h1 : ofLex u₁ with
      | inl x₁ =>
        cases h2 : ofLex u₂ with
        | inl x₂ =>
          have hu1 : u₁ = toLex (Sum.inl x₁) := ofLex.injective (by simp [h1])
          have hu2 : u₂ = toLex (Sum.inl x₂) := ofLex.injective (by simp [h2])
          subst hu1; subst hu2
          simp only [sumLex_le_inl_inl]
          rw [← eA.le_iff_le]
          have hcmp : ∀ z₁ z₂ : LexSigma (fun a : A => (pieceOrd (pA a)).ToType),
              (⟨toLex (Sum.inl z₁.fst), z₁.snd⟩ : LexSigma (fun u => (pieceOrd (pAB u)).ToType)) ≤
              ⟨toLex (Sum.inl z₂.fst), z₂.snd⟩ ↔ z₁ ≤ z₂ := by
            rintro ⟨a₁, v₁⟩ ⟨a₂, v₂⟩
            rw [lexSigma_le_iff, lexSigma_le_iff]
            simp only [sumLex_lt_inl_inl]
            constructor
            · rintro (h | ⟨hf, hs⟩)
              · exact Or.inl h
              · have ha : a₁ = a₂ := Sum.inl.inj (toLex.injective hf)
                subst ha
                exact Or.inr ⟨rfl, hs⟩
            · rintro (h | ⟨rfl, hs⟩)
              · exact Or.inl h
              · exact Or.inr ⟨rfl, hs⟩
          exact hcmp (eA x₁) (eA x₂)
        | inr y₂ =>
          have hu1 : u₁ = toLex (Sum.inl x₁) := ofLex.injective (by simp [h1])
          have hu2 : u₂ = toLex (Sum.inr y₂) := ofLex.injective (by simp [h2])
          subst hu1; subst hu2
          simp only [sumLex_le_inl_inr, iff_true]
          exact Or.inr (Or.inl (sumLex_lt_inl_inr _ _))
      | inr y₁ =>
        cases h2 : ofLex u₂ with
        | inl x₂ =>
          have hu1 : u₁ = toLex (Sum.inr y₁) := ofLex.injective (by simp [h1])
          have hu2 : u₂ = toLex (Sum.inl x₂) := ofLex.injective (by simp [h2])
          subst hu1; subst hu2
          simp only [sumLex_not_le_inr_inl, iff_false]
          rintro (hEq | hlt | ⟨hfst, _⟩)
          · exact Sum.inr_ne_inl (toLex.injective (congrArg LexSigma.fst hEq))
          · exact sumLex_not_lt_inr_inl _ _ hlt
          · exact Sum.inr_ne_inl (toLex.injective hfst)
        | inr y₂ =>
          have hu1 : u₁ = toLex (Sum.inr y₁) := ofLex.injective (by simp [h1])
          have hu2 : u₂ = toLex (Sum.inr y₂) := ofLex.injective (by simp [h2])
          subst hu1; subst hu2
          simp only [sumLex_le_inr_inr]
          rw [← eB.le_iff_le]
          have hcmp : ∀ z₁ z₂ : LexSigma (fun b : B => (pieceOrd (pB b)).ToType),
              (⟨toLex (Sum.inr z₁.fst), z₁.snd⟩ : LexSigma (fun u => (pieceOrd (pAB u)).ToType)) ≤
              ⟨toLex (Sum.inr z₂.fst), z₂.snd⟩ ↔ z₁ ≤ z₂ := by
            rintro ⟨b₁, v₁⟩ ⟨b₂, v₂⟩
            rw [lexSigma_le_iff, lexSigma_le_iff]
            simp only [sumLex_lt_inr_inr]
            constructor
            · rintro (h | ⟨hf, hs⟩)
              · exact Or.inl h
              · have hb : b₁ = b₂ := Sum.inr.inj (toLex.injective hf)
                subst hb
                exact Or.inr ⟨rfl, hs⟩
            · rintro (h | ⟨rfl, hs⟩)
              · exact Or.inl h
              · exact Or.inr ⟨rfl, hs⟩
          exact hcmp (eB y₁) (eB y₂) }⟩⟩

private lemma decomp_mul_lt_omega1 {α q : Ordinal.{0}} (hα : Decomp α) (hq : q < ω_ 1) :
    Decomp (α * q) := by
  obtain ⟨A, _, _, _, pA, ⟨eA⟩⟩ := hα
  obtain ⟨eMul⟩ := mul_toType_iso α q
  have : Countable q.ToType := by
    rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType, ← Cardinal.lt_aleph_one_iff]
    exact Cardinal.lt_omega_iff_card_lt.mp hq
  have : Countable (q.ToType ×ₗ A) := ofLex.injective.countable
  let pQA : (q.ToType ×ₗ A) → Option ℕ := fun u => pA (ofLex u).2
  refine ⟨q.ToType ×ₗ A, inferInstance, inferInstance, inferInstance, pQA, ⟨eMul.trans {
    toFun := fun u =>
      let p := ofLex u
      ⟨toLex (p.1, (eA p.2).fst), (eA p.2).snd⟩
    invFun := fun z =>
      let qa := ofLex z.fst
      toLex (qa.1, eA.symm ⟨qa.2, z.snd⟩)
    left_inv := fun u => by
      change toLex ((ofLex u).1, eA.symm ⟨(eA (ofLex u).2).fst, (eA (ofLex u).2).snd⟩) = u
      have hη : (⟨(eA (ofLex u).2).fst, (eA (ofLex u).2).snd⟩ :
          LexSigma (fun a : A => (pieceOrd (pA a)).ToType)) = eA (ofLex u).2 := rfl
      rw [hη, eA.symm_apply_apply, Prod.mk.eta, toLex_ofLex]
    right_inv := fun ⟨u, v⟩ => by
      change (⟨toLex ((ofLex u).1, (eA (eA.symm ⟨(ofLex u).2, v⟩)).fst),
        (eA (eA.symm ⟨(ofLex u).2, v⟩)).snd⟩ : LexSigma (fun u => (pieceOrd (pQA u)).ToType)) = ⟨u, v⟩
      rw [eA.apply_symm_apply]
      rfl
    map_rel_iff' := fun {u₁ u₂} => by
      simp only [Prod.Lex.le_iff]
      rw [← eA.le_iff_le]
      have hcmp : ∀ (q₁ q₂ : q.ToType) (z₁ z₂ : LexSigma (fun a : A => (pieceOrd (pA a)).ToType)),
          (⟨toLex (q₁, z₁.fst), z₁.snd⟩ : LexSigma (fun u => (pieceOrd (pQA u)).ToType)) ≤
          ⟨toLex (q₂, z₂.fst), z₂.snd⟩ ↔ q₁ < q₂ ∨ (q₁ = q₂ ∧ z₁ ≤ z₂) := by
        rintro q₁ q₂ ⟨a₁, v₁⟩ ⟨a₂, v₂⟩
        rw [lexSigma_le_iff, lexSigma_le_iff]
        simp only [Prod.Lex.lt_iff, ofLex_toLex]
        constructor
        · rintro ((hqlt | ⟨rfl, halt⟩) | ⟨hf, hs⟩)
          · exact Or.inl hqlt
          · exact Or.inr ⟨rfl, Or.inl halt⟩
          · have hpair := Prod.mk.inj (toLex.injective hf)
            rcases hpair with ⟨rfl, rfl⟩
            exact Or.inr ⟨rfl, Or.inr ⟨rfl, hs⟩⟩
        · rintro (hqlt | ⟨rfl, halt | ⟨rfl, hs⟩⟩)
          · exact Or.inl (Or.inl hqlt)
          · exact Or.inl (Or.inr ⟨rfl, halt⟩)
          · exact Or.inr ⟨rfl, hs⟩
      exact hcmp (ofLex u₁).1 (ofLex u₂).1 (eA (ofLex u₁).2) (eA (ofLex u₂).2) }⟩⟩

private lemma omega1_dvd_mod {α d : Ordinal.{0}} (hα : ω_ 1 ∣ α) (hd : ω_ 1 ∣ d) :
    ω_ 1 ∣ α % d := by
  obtain ⟨γ, rfl⟩ := hα
  obtain ⟨δ, rfl⟩ := hd
  have hdiv := Ordinal.div_add_mod (ω_ 1 * γ) (ω_ 1 * δ)
  have hle : ω_ 1 * (δ * (ω_ 1 * γ / (ω_ 1 * δ))) ≤ ω_ 1 * γ := by
    rw [← mul_assoc]
    conv_rhs => rw [← hdiv]
    exact le_self_add
  have hq : δ * (ω_ 1 * γ / (ω_ 1 * δ)) ≤ γ := by
    by_contra hgt
    push Not at hgt
    exact not_lt_of_ge hle (mul_lt_mul_of_pos_left hgt (Ordinal.omega_pos 1))
  refine ⟨γ - δ * (ω_ 1 * γ / (ω_ 1 * δ)), ?_⟩
  have h1 : ω_ 1 * (δ * (ω_ 1 * γ / (ω_ 1 * δ))) + ω_ 1 * (γ - δ * (ω_ 1 * γ / (ω_ 1 * δ))) =
      ω_ 1 * γ := by
    rw [← mul_add, Ordinal.add_sub_cancel_of_le hq]
  have h2 : ω_ 1 * (δ * (ω_ 1 * γ / (ω_ 1 * δ))) + (ω_ 1 * γ) % (ω_ 1 * δ) = ω_ 1 * γ := by
    rw [← mul_assoc]; exact hdiv
  exact add_left_cancel (h2.trans h1.symm)

private lemma decomp_lt_omega1_opow_nat (N : ℕ) :
    ∀ r : Ordinal.{0}, ω_ 1 ∣ r → r < ω_ 1 ^ (N : Ordinal.{0}) → Decomp r := by
  induction N with
  | zero =>
    intro r _ hr
    rw [Nat.cast_zero, Ordinal.opow_zero, Order.lt_one_iff] at hr
    subst hr
    exact decomp_zero
  | succ N ih =>
    intro r hdiv hr
    cases N with
    | zero =>
      rw [Nat.cast_one, Ordinal.opow_one] at hr
      obtain ⟨γ, rfl⟩ := hdiv
      have hγ : γ = 0 := by
        by_contra hne
        have h1 : (1 : Ordinal.{0}) ≤ γ := Order.one_le_iff_ne_zero.mpr hne
        have : ω_ 1 ≤ ω_ 1 * γ := by simpa only [mul_one] using mul_le_mul_right h1 (ω_ 1)
        exact not_le_of_gt hr this
      rw [hγ, mul_zero]
      exact decomp_zero
    | succ M =>
      have hd_pos : (0 : Ordinal.{0}) < ω_ 1 ^ ((M + 1 : ℕ) : Ordinal.{0}) :=
        Ordinal.opow_pos _ (Ordinal.omega_pos 1)
      have hd_dvd : ω_ 1 ∣ ω_ 1 ^ ((M + 1 : ℕ) : Ordinal.{0}) := by
        refine ⟨ω_ 1 ^ (M : Ordinal.{0}), ?_⟩
        have h1m : ((M + 1 : ℕ) : Ordinal.{0}) = (1 : Ordinal.{0}) + (M : Ordinal.{0}) := by
          rw [add_comm, Nat.cast_add, Nat.cast_one]
        rw [h1m, Ordinal.opow_add, Ordinal.opow_one]
      have hq_lt : r / ω_ 1 ^ ((M + 1 : ℕ) : Ordinal.{0}) < ω_ 1 := by
        rw [← Ordinal.lt_mul_iff_div_lt hd_pos.ne']
        simpa only [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one] using hr
      rw [← Ordinal.div_add_mod r (ω_ 1 ^ ((M + 1 : ℕ) : Ordinal.{0}))]
      exact decomp_add
        (decomp_mul_lt_omega1 (decomp_piece (some M)) hq_lt)
        (ih _ (omega1_dvd_mod hdiv hd_dvd) (Ordinal.mod_lt r hd_pos.ne'))

private lemma decomp_of_mul_lt (γ : Ordinal.{0}) (hγ : ω_ 1 * γ < ω_ 1 ^ (ω + 2)) :
    Decomp (ω_ 1 * γ) := by
  let α := ω_ 1 * γ
  have hα_dvd : ω_ 1 ∣ α := ⟨γ, rfl⟩
  have h1 : ω_ 1 ∣ ω_ 1 ^ (ω + 1) := by
    refine ⟨ω_ 1 ^ (ω + 1), ?_⟩
    rw [← Ordinal.opow_one_add, ← add_assoc, Ordinal.one_add_omega0]
  have h2 : ω_ 1 ∣ ω_ 1 ^ ω := by
    refine ⟨ω_ 1 ^ ω, ?_⟩
    rw [← Ordinal.opow_one_add, Ordinal.one_add_omega0]
  have hq1_lt : α / ω_ 1 ^ (ω + 1) < ω_ 1 := by
    rw [← Ordinal.lt_mul_iff_div_lt (Ordinal.opow_pos _ (Ordinal.omega_pos 1)).ne']
    have heq : ω_ 1 ^ (ω + 1) * ω_ 1 = ω_ 1 ^ (ω + 2) := by
      rw [← Ordinal.opow_add_one, add_assoc]
      norm_num
    exact heq.symm ▸ hγ
  change Decomp α
  rw [← Ordinal.div_add_mod α (ω_ 1 ^ (ω + 1))]
  refine decomp_add (decomp_mul_lt_omega1 (decomp_piece none) hq1_lt) ?_
  let r₁ := α % ω_ 1 ^ (ω + 1)
  have hr₁_lt : r₁ < ω_ 1 ^ (ω + 1) :=
    Ordinal.mod_lt α (Ordinal.opow_pos _ (Ordinal.omega_pos 1)).ne'
  have hr₁_dvd : ω_ 1 ∣ r₁ := omega1_dvd_mod hα_dvd h1
  have hq0_lt : r₁ / ω_ 1 ^ ω < ω_ 1 := by
    rw [← Ordinal.lt_mul_iff_div_lt (Ordinal.opow_pos _ (Ordinal.omega_pos 1)).ne',
      ← Ordinal.opow_add_one]
    exact hr₁_lt
  change Decomp r₁
  rw [← Ordinal.div_add_mod r₁ (ω_ 1 ^ ω)]
  refine decomp_add (decomp_mul_lt_omega1 decomp_omega1_pow_omega hq0_lt) ?_
  let r₂ := r₁ % ω_ 1 ^ ω
  have hr₂_lt : r₂ < ω_ 1 ^ ω :=
    Ordinal.mod_lt r₁ (Ordinal.opow_pos _ (Ordinal.omega_pos 1)).ne'
  have hr₂_dvd : ω_ 1 ∣ r₂ := omega1_dvd_mod hr₁_dvd h2
  have hexN : ∃ N : ℕ, r₂ < ω_ 1 ^ (N : Ordinal.{0}) := by
    rw [← Ordinal.iSup_pow_natCast (Ordinal.omega_pos 1)] at hr₂_lt
    obtain ⟨N, hN⟩ := Ordinal.lt_iSup_iff.mp hr₂_lt
    exact ⟨N, by simpa only [Ordinal.opow_natCast] using hN⟩
  obtain ⟨N, hN⟩ := hexN
  exact decomp_lt_omega1_opow_nat N r₂ hr₂_dvd hN

private noncomputable def pieceOrdCast {o₁ o₂ : Option ℕ} (h : o₁ = o₂) :
    (pieceOrd o₁).ToType ≃o (pieceOrd o₂).ToType := by
  subst h; exact OrderIso.refl _

private lemma pieceOrdCast_apply {o₁ o₂ : Option ℕ} (h : o₁ = o₂) (x : (pieceOrd o₁).ToType) :
    pieceOrdCast h x = cast (by rw [h]) x := by
  subst h; rfl

private lemma pieceOrdCast_symm_apply {o₁ o₂ : Option ℕ} (h : o₁ = o₂) (x : (pieceOrd o₂).ToType) :
    (pieceOrdCast h).symm x = cast (by rw [h]) x := by
  subst h; rfl

private def flatM {A : Type} (piece : A → Option ℕ)
    (i : {p : A × ℕ // piece p.1 = none ∨ p.2 = 0}) : ℕ :=
  match piece i.1.1 with
  | none => i.1.2 + 2
  | some k => k + 1

private lemma flatM_pos {A : Type} (piece : A → Option ℕ)
    (i : {p : A × ℕ // piece p.1 = none ∨ p.2 = 0}) : 1 ≤ flatM piece i := by
  dsimp only [flatM]
  cases piece i.1.1 with
  | none => exact Nat.succ_le_succ (Nat.zero_le _)
  | some k => exact Nat.succ_le_succ (Nat.zero_le _)

private noncomputable def flatTo {A : Type} (piece : A → Option ℕ)
    (isoω1 : (pieceOrd none).ToType ≃o (W1 ×ₗ NatPowSum))
    (isoSlice : ∀ n : ℕ, PowW1 (n + 2) ≃o (W1 ×ₗ PowW1 (n + 1))) :
    (Σ i : {p : A × ℕ // piece p.1 = none ∨ p.2 = 0}, PowW1 (flatM piece i)) →
      LexSigma (fun a : A => (pieceOrd (piece a)).ToType) :=
  fun ⟨i, x⟩ =>
    if h : piece i.1.1 = none then
      let n := i.1.2
      let x' : PowW1 (n + 2) := cast (by dsimp only [flatM]; rw [h]) x
      let p := ofLex (isoSlice n x')
      ⟨i.1.1, (pieceOrdCast h).symm (isoω1.symm (toLex (p.1, ⟨n, p.2⟩)))⟩
    else
      let k := (piece i.1.1).get (Option.isSome_iff_ne_none.mpr h)
      have hk : piece i.1.1 = some k := (Option.some_get _).symm
      ⟨i.1.1, (pieceOrdCast hk).symm (cast (by dsimp only [flatM]; rw [hk]; rfl) x)⟩

private noncomputable def flatFrom {A : Type} (piece : A → Option ℕ)
    (isoω1 : (pieceOrd none).ToType ≃o (W1 ×ₗ NatPowSum))
    (isoSlice : ∀ n : ℕ, PowW1 (n + 2) ≃o (W1 ×ₗ PowW1 (n + 1))) :
    LexSigma (fun a : A => (pieceOrd (piece a)).ToType) →
      Σ i : {p : A × ℕ // piece p.1 = none ∨ p.2 = 0}, PowW1 (flatM piece i) :=
  fun ⟨a, v⟩ =>
    if h : piece a = none then
      let p := ofLex (isoω1 (pieceOrdCast h v))
      let n : ℕ := p.2.fst
      let i : {p : A × ℕ // piece p.1 = none ∨ p.2 = 0} := ⟨(a, n), Or.inl h⟩
      let x' : PowW1 (n + 2) := (isoSlice n).symm (toLex (p.1, p.2.snd))
      ⟨i, cast (by dsimp only [flatM, i]; rw [h]) x'⟩
    else
      let k := (piece a).get (Option.isSome_iff_ne_none.mpr h)
      have hk : piece a = some k := (Option.some_get _).symm
      let i : {p : A × ℕ // piece p.1 = none ∨ p.2 = 0} := ⟨(a, 0), Or.inr rfl⟩
      ⟨i, cast (by dsimp only [flatM, i]; rw [hk]; rfl) (pieceOrdCast hk v)⟩

private noncomputable def flatEquiv {A : Type} (piece : A → Option ℕ)
    (isoω1 : (pieceOrd none).ToType ≃o (W1 ×ₗ NatPowSum))
    (isoSlice : ∀ n : ℕ, PowW1 (n + 2) ≃o (W1 ×ₗ PowW1 (n + 1))) :
    (Σ i : {p : A × ℕ // piece p.1 = none ∨ p.2 = 0}, PowW1 (flatM piece i)) ≃
      LexSigma (fun a : A => (pieceOrd (piece a)).ToType) where
  toFun := flatTo piece isoω1 isoSlice
  invFun := flatFrom piece isoω1 isoSlice
  left_inv := fun ⟨⟨⟨a, n⟩, hi⟩, x⟩ => by
    by_cases h : piece a = none
    · dsimp only [flatTo, flatFrom]
      rw [dif_pos h, dif_pos h]
      dsimp only
      let x' : PowW1 (n + 2) := cast (by dsimp only [flatM]; rw [h]) x
      let p := ofLex (isoSlice n x')
      have hp : ofLex (isoω1 ((pieceOrdCast h) ((pieceOrdCast h).symm
          (isoω1.symm (toLex (p.1, (⟨n, p.2⟩ : NatPowSum))))))) = (p.1, ⟨n, p.2⟩) := by
        rw [(pieceOrdCast h).apply_symm_apply, isoω1.apply_symm_apply, ofLex_toLex]
      refine Sigma.ext (Subtype.ext (Prod.ext rfl
        (congrArg (fun q : W1 × NatPowSum => q.2.fst) hp))) ?_
      refine (cast_heq _ _).trans ?_
      have hstep : ∀ (q : W1 × NatPowSum), q = (p.1, ⟨n, p.2⟩) →
          HEq ((isoSlice q.2.fst).symm (toLex (q.1, q.2.snd))) x := by
        rintro _ rfl
        change HEq ((isoSlice n).symm (toLex (p.1, p.2))) x
        rw [Prod.mk.eta, toLex_ofLex, (isoSlice n).symm_apply_apply]
        exact cast_heq _ _
      exact hstep _ hp
    · have hn0 : n = 0 := hi.resolve_left h
      subst hn0
      dsimp only [flatTo, flatFrom]
      rw [dif_neg h, dif_neg h]
      dsimp only
      rw [OrderIso.apply_symm_apply]
      refine Sigma.ext rfl ?_
      exact (cast_heq _ _).trans (cast_heq _ _)
  right_inv := fun ⟨a, v⟩ => by
    by_cases h : piece a = none
    · dsimp only [flatTo, flatFrom]
      rw [dif_pos h, dif_pos h]
      dsimp only
      rw [cast_cast, cast_eq, (isoSlice _).apply_symm_apply, ofLex_toLex]
      dsimp only
      have hη : (⟨(ofLex (isoω1 ((pieceOrdCast h) v))).2.fst,
          (ofLex (isoω1 ((pieceOrdCast h) v))).2.snd⟩ : NatPowSum) =
          (ofLex (isoω1 ((pieceOrdCast h) v))).2 := rfl
      rw [hη, Prod.mk.eta, toLex_ofLex, isoω1.symm_apply_apply, (pieceOrdCast h).symm_apply_apply]
    · dsimp only [flatTo, flatFrom]
      rw [dif_neg h, dif_neg h]
      dsimp only
      simp only [cast_cast, cast_eq, OrderIso.symm_apply_apply]

/-- Main theorem proving `OMA.R_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1.H1`. -/
theorem main : OMA.R_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1.H1 := by
  intro γ hγ F hF
  obtain ⟨A, _, _, _, piece, ⟨eDecomp⟩⟩ := decomp_of_mul_lt γ hγ
  let isoω1 : (pieceOrd none).ToType ≃o (W1 ×ₗ NatPowSum) :=
    Classical.choice omega1_pow_omega_succ_iso
  let isoSlice (n : ℕ) : PowW1 (n + 2) ≃o (W1 ×ₗ PowW1 (n + 1)) :=
    Classical.choice (powW1_succ_iso (n + 1))
  -- Expand each `none` piece (`ω_ 1 ^ (ω + 1)`) into `ℕ` pieces (`PowW1 (n + 2)`).
  let Idx := {p : A × ℕ // piece p.1 = none ∨ p.2 = 0}
  let m : Idx → ℕ := flatM piece
  have hm : ∀ i : Idx, 1 ≤ m i := flatM_pos piece
  -- Clean bijection `eFlat : (Σ i : Idx, PowW1 (m i)) ≃ (ω_ 1 * γ).ToType`.
  let eFlat : (Σ i : Idx, PowW1 (m i)) ≃ (ω_ 1 * γ).ToType :=
    (flatEquiv piece isoω1 isoSlice).trans eDecomp.symm.toEquiv
  let F' : (Σ i : Idx, PowW1 (m i)) → Finset (Σ i : Idx, PowW1 (m i)) :=
    fun x => (F (eFlat x)).map eFlat.symm.toEmbedding
  have hF' : ∀ x, x ∉ F' x := fun x hx => by
    rw [Finset.mem_map] at hx
    obtain ⟨y, hyF, hyEq⟩ := hx
    exact hF (eFlat x) ((eFlat.symm_apply_eq.mp hyEq) ▸ hyF)
  -- Apply the countable disjoint union engine!
  obtain ⟨emb, hemb_free⟩ := free_set_countable_pow_union m hm F' hF'
  let S_flat : Set (Σ i : Idx, PowW1 (m i)) := {z | ∃ u : PowW1 (m z.1), emb z.1 u = z.2}
  let s : Set (ω_ 1 * γ).ToType := eFlat '' S_flat
  -- `s` is `F`-free:
  have hs_free : s.Pairwise (fun x y => y ∉ F x) := by
    rintro x ⟨⟨i₁, z₁⟩, ⟨u₁, hz₁⟩, rfl⟩ y ⟨⟨i₂, z₂⟩, ⟨u₂, hz₂⟩, rfl⟩ hxy hmem
    dsimp only at hz₁ hz₂
    rw [← hz₁] at hxy hmem
    rw [← hz₂] at hxy hmem
    have hne : (⟨i₁, emb i₁ u₁⟩ : Σ i : Idx, PowW1 (m i)) ≠ ⟨i₂, emb i₂ u₂⟩ :=
      fun h => hxy (congrArg eFlat h)
    apply hemb_free i₁ u₁ i₂ u₂ hne
    rw [Finset.mem_map]
    exact ⟨eFlat ⟨i₂, emb i₂ u₂⟩, hmem, eFlat.symm_apply_apply _⟩
  -- For each `a : A`, build an order-embedding `(pieceOrd (piece a)).ToType ↪o {v // eDecomp.symm ⟨a, v⟩ ∈ s}`:
  have hblock_emb : ∀ a : A, Nonempty ((pieceOrd (piece a)).ToType ↪o
      {v : (pieceOrd (piece a)).ToType // eDecomp.symm ⟨a, v⟩ ∈ s}) := by
    intro a
    rcases Option.eq_none_or_eq_some (piece a) with h | ⟨k, h⟩
    · let S_a : Set (W1 ×ₗ NatPowSum) :=
        {w | eDecomp.symm ⟨a, (pieceOrdCast h).symm (isoω1.symm w)⟩ ∈ s}
      have hSa : ∀ n : ℕ, Nonempty (PowW1 (n + 2) ↪o
          {p : W1 ×ₗ PowW1 (n + 1) // toLex ((ofLex p).1, ⟨n, (ofLex p).2⟩) ∈ S_a}) := by
        intro n
        let i : Idx := ⟨(a, n), Or.inl h⟩
        have hm_i : m i = n + 2 := by dsimp only [m, flatM, i]; rw [h]
        let eCast : PowW1 (n + 2) ≃o PowW1 (m i) := powW1Cast hm_i.symm
        let f : PowW1 (n + 2) →
            {p : W1 ×ₗ PowW1 (n + 1) // toLex ((ofLex p).1, ⟨n, (ofLex p).2⟩) ∈ S_a} := fun x =>
          ⟨isoSlice n (eCast.symm (emb i (eCast x))), by
            refine ⟨⟨i, emb i (eCast x)⟩, ⟨eCast x, rfl⟩, ?_⟩
            change eDecomp.symm (flatTo piece isoω1 isoSlice ⟨i, emb i (eCast x)⟩) = _
            congr 1
            dsimp only [flatTo]
            rw [dif_pos h]
            dsimp only [i]
            rw [powW1Cast_symm_apply]⟩
        refine ⟨⟨⟨f, fun x₁ x₂ hEq => eCast.injective ((emb i).injective
            (eCast.symm.injective ((isoSlice n).injective (congrArg Subtype.val hEq))))⟩,
          fun {x₁ x₂} => by
            change isoSlice n (eCast.symm (emb i (eCast x₁))) ≤
                isoSlice n (eCast.symm (emb i (eCast x₂))) ↔ x₁ ≤ x₂
            simp only [(isoSlice n).le_iff_le, eCast.symm.le_iff_le,
              (emb i).le_iff_le, eCast.le_iff_le]⟩⟩
      obtain ⟨eLift⟩ := omega1_pow_omega_succ_lift S_a hSa
      let eOrd : (pieceOrd (piece a)).ToType ≃o (W1 ×ₗ NatPowSum) :=
        (pieceOrdCast h).trans isoω1
      refine ⟨⟨⟨fun v =>
          ⟨eOrd.symm (eLift (eOrd v)).1, (eLift (eOrd v)).2⟩,
        fun v₁ v₂ hEq => eOrd.injective (eLift.injective (Subtype.ext
          (eOrd.symm.injective (congrArg Subtype.val hEq))))⟩,
        fun {v₁ v₂} => by
          change eOrd.symm (eLift (eOrd v₁)).1 ≤ eOrd.symm (eLift (eOrd v₂)).1 ↔ v₁ ≤ v₂
          rw [eOrd.symm.le_iff_le]
          exact (eLift.le_iff_le).trans eOrd.le_iff_le⟩⟩
    · let i : Idx := ⟨(a, 0), Or.inr rfl⟩
      have hm_i : m i = k + 1 := by dsimp only [m, flatM, i]; rw [h]
      have hne : piece a ≠ none := by rw [h]; exact Option.some_ne_none k
      let eCast : (pieceOrd (piece a)).ToType ≃o PowW1 (m i) :=
        (pieceOrdCast h).trans (powW1Cast hm_i.symm)
      let f : (pieceOrd (piece a)).ToType →
          {v : (pieceOrd (piece a)).ToType // eDecomp.symm ⟨a, v⟩ ∈ s} := fun v =>
        ⟨eCast.symm (emb i (eCast v)), by
          refine ⟨⟨i, emb i (eCast v)⟩, ⟨eCast v, rfl⟩, ?_⟩
          change eDecomp.symm (flatTo piece isoω1 isoSlice ⟨i, emb i (eCast v)⟩) =
            eDecomp.symm ⟨a, eCast.symm (emb i (eCast v))⟩
          congr 1
          dsimp only [flatTo]
          rw [dif_neg hne]
          dsimp only [i]
          have hkEq : (piece a).get (Option.isSome_iff_ne_none.mpr hne) = k := by
            have h1 := Option.some_get (Option.isSome_iff_ne_none.mpr hne)
            exact Option.some.inj (h1.trans h)
          congr 1
          have hsymm : eCast.symm (emb i (eCast v)) =
              (pieceOrdCast h).symm ((powW1Cast hm_i.symm).symm (emb i (eCast v))) := rfl
          rw [hsymm, powW1Cast_symm_apply]
          subst hkEq
          rfl⟩
      refine ⟨⟨⟨f, fun v₁ v₂ hEq => eCast.injective ((emb i).injective
          (eCast.symm.injective (congrArg Subtype.val hEq)))⟩,
        fun {v₁ v₂} => by
          change eCast.symm (emb i (eCast v₁)) ≤ eCast.symm (emb i (eCast v₂)) ↔ v₁ ≤ v₂
          simp only [eCast.symm.le_iff_le, (emb i).le_iff_le, eCast.le_iff_le]⟩⟩
  let eb (a : A) := Classical.choice (hblock_emb a)
  -- Glue all block embeddings into `(ω_ 1 * γ).ToType ↪o s`!
  let embAll : (ω_ 1 * γ).ToType ↪o s :=
    eDecomp.toOrderEmbedding.trans
      ⟨⟨fun ⟨a, v⟩ => ⟨eDecomp.symm ⟨a, (eb a v).1⟩, (eb a v).2⟩,
        by
          rintro ⟨a₁, v₁⟩ ⟨a₂, v₂⟩ hEq
          have h1 := eDecomp.symm.injective (congrArg Subtype.val hEq)
          have ha : a₁ = a₂ := congrArg LexSigma.fst h1
          subst ha
          have hv : (eb a₁ v₁).1 = (eb a₁ v₂).1 := lexSigma_snd_eq h1
          rw [(eb a₁).injective (Subtype.ext hv)]⟩,
        by
          rintro ⟨a₁, v₁⟩ ⟨a₂, v₂⟩
          change eDecomp.symm (⟨a₁, (eb a₁ v₁).1⟩ : LexSigma (fun a => (pieceOrd (piece a)).ToType)) ≤
              eDecomp.symm ⟨a₂, (eb a₂ v₂).1⟩ ↔
            (⟨a₁, v₁⟩ : LexSigma (fun a => (pieceOrd (piece a)).ToType)) ≤ ⟨a₂, v₂⟩
          rw [eDecomp.symm.le_iff_le, lexSigma_le_iff, lexSigma_le_iff]
          constructor
          · rintro (hlt | ⟨ha, hs⟩)
            · exact Or.inl hlt
            · dsimp only at ha hs; subst ha
              exact Or.inr ⟨rfl, (eb a₁).le_iff_le.mp hs⟩
          · rintro (hlt | ⟨ha, hs⟩)
            · exact Or.inl hlt
            · dsimp only at ha hs; subst ha
              exact Or.inr ⟨rfl, (eb a₁).le_iff_le.mpr hs⟩⟩
  exact ⟨s, typeLT_eq_of_emb_toType embAll, hs_free⟩

end OMA.P_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1_H1

theorem OMA.solution : OMA.R_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1.H1 :=
  OMA.P_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1_H1.main
