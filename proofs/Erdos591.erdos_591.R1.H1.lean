import OMAReductions.R_Erdos591_erdos_591_R1

/-!
# Proof of `Erdos591.erdos_591.R1.H1`

For every `n : ℕ` and every triangle-free graph `blue` on `(ω ^ (ω ^ 2)).ToType`, any subset
`S` of order type at least `(ω ^ ω) ^ ((n + 1) * 2) = α * α` (where `α = (ω ^ ω) ^ (n + 1)`)
contains a red clique `T ⊆ S` of exact order type `α`.

The proof establishes the Erdős--Milner partition relation `α * α → (α, 3)^2` for countable
additively indecomposable ordinals `α = ω ^ (ω * (n + 1))` satisfying `ω * α = α`, via the
corrigendum inductive construction of nested families of order-type-`α` blocks.
-/

open Cardinal Ordinal Set Function Order

namespace Erdos591R1H1

abbrev Host : Type := (ω ^ (ω ^ 2) : Ordinal.{0}).ToType

/-- Order type of a subset of a well-ordered type, avoiding notation precedence ambiguity with
set operations. -/
private noncomputable def otype {W : Type} [LinearOrder W] [WellFoundedLT W]
    (s : Set W) : Ordinal.{0} :=
  typeLT s

/- ## Section 1: Ordinal arithmetic and order-type utilities -/

private lemma exists_subset_otype_eq {W : Type} [LinearOrder W] [WellFoundedLT W]
    {A : Set W} {γ : Ordinal.{0}} (h : γ ≤ otype A) :
    ∃ B : Set W, B ⊆ A ∧ otype B = γ := by
  have hle : typeLT γ.ToType ≤ typeLT A := by
    simpa [otype, Ordinal.type_toType] using h
  obtain ⟨e⟩ := Ordinal.type_le_iff.mp hle
  refine ⟨Subtype.val '' Set.range e, ?_, ?_⟩
  · rintro _ ⟨⟨x, hx⟩, _, rfl⟩
    exact hx
  · let iso : ((· < ·) : γ.ToType → γ.ToType → Prop) ≃r
        ((· < ·) : (Subtype.val '' Set.range e : Set W) →
          (Subtype.val '' Set.range e : Set W) → Prop) :=
      { toFun := fun a => ⟨(e a).1, ⟨e a, ⟨a, rfl⟩, rfl⟩⟩
        invFun := fun y =>
          Classical.choose (by
            rcases y.2 with ⟨x, ⟨a, ha⟩, hx⟩
            exact ⟨a, by rw [ha, hx]⟩ : ∃ a : γ.ToType, (e a).1 = y.1)
        left_inv := fun a => by
          have hspec : (e (Classical.choose
              (show ∃ b : γ.ToType, (e b).1 = (e a).1 from ⟨a, rfl⟩))).1 = (e a).1 :=
            Classical.choose_spec (show ∃ b : γ.ToType, (e b).1 = (e a).1 from ⟨a, rfl⟩)
          exact e.injective (Subtype.ext hspec)
        right_inv := fun y => by
          apply Subtype.ext
          exact Classical.choose_spec (by
            rcases y.2 with ⟨x, ⟨a, ha⟩, hx⟩
            exact ⟨a, by rw [ha, hx]⟩ : ∃ a : γ.ToType, (e a).1 = y.1)
        map_rel_iff' := fun {a b} => by
          change (e a).1 < (e b).1 ↔ a < b
          exact e.map_rel_iff }
    have htype : typeLT γ.ToType = otype (Subtype.val '' Set.range e : Set W) :=
      Ordinal.type_eq.mpr ⟨iso⟩
    rw [Ordinal.type_toType] at htype
    exact htype.symm

private def relEmbedding_of_strictMono {α β : Type}
    [LinearOrder α] [LinearOrder β] (f : α → β) (hf : StrictMono f) :
    ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop) :=
  { toFun := f
    inj' := hf.injective
    map_rel_iff' := hf.lt_iff_lt }

private def relEmbedding_of_prod_lex {α β W : Type}
    [LinearOrder α] [LinearOrder β] [LinearOrder W]
    (f : α × β → W)
    (hf : ∀ p q : α × β, Prod.Lex (· < ·) (· < ·) p q → f p < f q) :
    Prod.Lex ((· < ·) : α → α → Prop) ((· < ·) : β → β → Prop) ↪r
      ((· < ·) : W → W → Prop) := by
  have htrich : ∀ p q : α × β,
      Prod.Lex (· < ·) (· < ·) p q ∨ p = q ∨ Prod.Lex (· < ·) (· < ·) q p := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    rcases lt_trichotomy a₁ a₂ with h | rfl | h
    · exact Or.inl (Prod.Lex.left _ _ h)
    · rcases lt_trichotomy b₁ b₂ with hb | rfl | hb
      · exact Or.inl (Prod.Lex.right _ hb)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Prod.Lex.right _ hb))
    · exact Or.inr (Or.inr (Prod.Lex.left _ _ h))
  exact
    { toFun := f
      inj' := fun p q hpq => by
        rcases htrich p q with h | rfl | h
        · exact (ne_of_lt (hf p q h) hpq).elim
        · rfl
        · exact (ne_of_gt (hf q p h) hpq).elim
      map_rel_iff' := fun {p q} => by
        constructor
        · intro hlt
          rcases htrich p q with h | rfl | h
          · exact h
          · exact (lt_irrefl _ hlt).elim
          · exact (lt_asymm hlt (hf q p h)).elim
        · exact hf p q }

private def relEmbedding_of_sum_lex {α β W : Type}
    [LinearOrder α] [LinearOrder β] [LinearOrder W]
    (f : α ⊕ β → W)
    (hf : ∀ p q : α ⊕ β, Sum.Lex (· < ·) (· < ·) p q → f p < f q) :
    Sum.Lex ((· < ·) : α → α → Prop) ((· < ·) : β → β → Prop) ↪r
      ((· < ·) : W → W → Prop) := by
  have htrich : ∀ p q : α ⊕ β,
      Sum.Lex (· < ·) (· < ·) p q ∨ p = q ∨ Sum.Lex (· < ·) (· < ·) q p := by
    intro p q
    cases p with
    | inl a₁ =>
      cases q with
      | inl a₂ =>
        rcases lt_trichotomy a₁ a₂ with h | rfl | h
        · exact Or.inl (Sum.Lex.inl h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Sum.Lex.inl h))
      | inr b₂ => exact Or.inl (Sum.Lex.sep a₁ b₂)
    | inr b₁ =>
      cases q with
      | inl a₂ => exact Or.inr (Or.inr (Sum.Lex.sep a₂ b₁))
      | inr b₂ =>
        rcases lt_trichotomy b₁ b₂ with h | rfl | h
        · exact Or.inl (Sum.Lex.inr h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Sum.Lex.inr h))
  exact
    { toFun := f
      inj' := fun p q hpq => by
        rcases htrich p q with h | rfl | h
        · exact (ne_of_lt (hf p q h) hpq).elim
        · rfl
        · exact (ne_of_gt (hf q p h) hpq).elim
      map_rel_iff' := fun {p q} => by
        constructor
        · intro hlt
          rcases htrich p q with h | rfl | h
          · exact h
          · exact (lt_irrefl _ hlt).elim
          · exact (lt_asymm hlt (hf q p h)).elim
        · exact hf p q }

private lemma otype_empty {W : Type} [LinearOrder W] [WellFoundedLT W] :
    otype (∅ : Set W) = 0 := by
  rw [otype, Ordinal.type_eq_zero_iff_isEmpty]
  infer_instance

private lemma otype_mono {W : Type} [LinearOrder W] [WellFoundedLT W]
    {s t : Set W} (h : s ⊆ t) : otype s ≤ otype t :=
  Ordinal.type_mono h

private lemma eq_empty_of_otype_lt_one {W : Type} [LinearOrder W] [WellFoundedLT W]
    {X : Set W} (h : otype X < 1) : X = ∅ := by
  ext x
  simp only [mem_empty_iff_false, iff_false]
  intro hx
  have h1 : (1 : Ordinal.{0}) ≤ otype X := by
    have hfin : typeLT (Fin 1) = (1 : Ordinal.{0}) := by simp
    rw [← hfin]
    have e : ((· < ·) : Fin 1 → Fin 1 → Prop) ↪r ((· < ·) : X → X → Prop) :=
      relEmbedding_of_strictMono (fun _ => ⟨x, hx⟩) (fun a b hab => by omega)
    exact e.ordinal_type_le
  exact not_le_of_gt h h1

private lemma otype_le_of_finite_blocks {W : Type} [LinearOrder W] [WellFoundedLT W]
    {m : ℕ} {γ : Ordinal.{0}} {X : Set W}
    (B : Fin m → Set W)
    (hord : ∀ i j : Fin m, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y)
    (hsz : ∀ i : Fin m, γ ≤ otype (X ∩ B i)) :
    γ * (m : Ordinal.{0}) ≤ otype X := by
  have hemb : ∀ i : Fin m, Nonempty (((· < ·) : γ.ToType → γ.ToType → Prop) ↪r
      ((· < ·) : (X ∩ B i : Set W) → (X ∩ B i : Set W) → Prop)) := by
    intro i
    have hle : typeLT γ.ToType ≤ typeLT (X ∩ B i : Set W) := by
      simpa [otype, Ordinal.type_toType] using hsz i
    exact Ordinal.type_le_iff'.mp hle
  let φ := fun i => Classical.choice (hemb i)
  let f : Fin m × γ.ToType → X := fun p => ⟨(φ p.1 p.2).1, (φ p.1 p.2).2.1⟩
  have hf : ∀ p q : Fin m × γ.ToType,
      Prod.Lex (· < ·) (· < ·) p q → f p < f q := by
    intro ⟨i₁, t₁⟩ ⟨i₂, t₂⟩ hlex
    cases hlex with
    | left _ _ hi =>
      exact hord i₁ i₂ hi _ (φ i₁ t₁).2.2 _ (φ i₂ t₂).2.2
    | right _ ht =>
      exact (φ i₁).map_rel_iff.mpr ht
  have e := relEmbedding_of_prod_lex f hf
  have hle := e.ordinal_type_le
  rw [Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_fin] at hle
  exact hle

private lemma otype_le_of_omega_blocks {W : Type} [LinearOrder W] [WellFoundedLT W]
    {γ : Ordinal.{0}} {Y : Set W}
    (B : ℕ → Set W)
    (hord : ∀ i j : ℕ, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y)
    (hsz : ∀ i : ℕ, γ ≤ otype (Y ∩ B i)) :
    γ * ω ≤ otype Y := by
  have hemb : ∀ i : ℕ, Nonempty (((· < ·) : γ.ToType → γ.ToType → Prop) ↪r
      ((· < ·) : (Y ∩ B i : Set W) → (Y ∩ B i : Set W) → Prop)) := by
    intro i
    have hle : typeLT γ.ToType ≤ typeLT (Y ∩ B i : Set W) := by
      simpa [otype, Ordinal.type_toType] using hsz i
    exact Ordinal.type_le_iff'.mp hle
  let φ := fun i => Classical.choice (hemb i)
  let f : ℕ × γ.ToType → Y := fun p => ⟨(φ p.1 p.2).1, (φ p.1 p.2).2.1⟩
  have hf : ∀ p q : ℕ × γ.ToType,
      Prod.Lex (· < ·) (· < ·) p q → f p < f q := by
    intro ⟨i₁, t₁⟩ ⟨i₂, t₂⟩ hlex
    cases hlex with
    | left _ _ hi =>
      exact hord i₁ i₂ hi _ (φ i₁ t₁).2.2 _ (φ i₂ t₂).2.2
    | right _ ht =>
      exact (φ i₁).map_rel_iff.mpr ht
  have e := relEmbedding_of_prod_lex f hf
  have hle := e.ordinal_type_le
  rw [Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_nat_lt] at hle
  exact hle

private lemma exists_strictMono_of_unbounded (P : ℕ → Prop)
    (h : ∀ N : ℕ, ∃ i ≥ N, P i) (m : ℕ) :
    ∃ f : Fin m → ℕ, StrictMono f ∧ ∀ k : Fin m, P (f k) := by
  induction m with
  | zero => exact ⟨Fin.elim0, fun a => a.elim0, fun a => a.elim0⟩
  | succ m ih =>
    obtain ⟨f, hf, hP⟩ := ih
    let bound : ℕ := if hm : 0 < m then f ⟨m - 1, by omega⟩ + 1 else 0
    obtain ⟨i, hi, hPi⟩ := h bound
    refine ⟨Fin.snoc f i, ?_, ?_⟩
    · intro a b hab
      by_cases hb : b.1 < m
      · have ha : a.1 < m := lt_trans hab hb
        simp only [Fin.snoc, dif_pos ha, dif_pos hb]
        exact hf hab
      · have hb_eq : b.1 = m := by omega
        have ha : a.1 < m := by omega
        have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
        simp only [Fin.snoc, dif_pos ha, dif_neg hb]
        have hle : f ⟨a.1, ha⟩ ≤ f ⟨m - 1, by omega⟩ :=
          hf.monotone (show (⟨a.1, ha⟩ : Fin m) ≤ ⟨m - 1, by omega⟩ by
            change a.1 ≤ m - 1; omega)
        have hlt : f ⟨m - 1, by omega⟩ < i := by
          have : bound ≤ i := hi
          simp only [bound, dif_pos hm] at this
          omega
        exact lt_of_le_of_lt hle hlt
    · intro k
      by_cases hk : k.1 < m
      · simp only [Fin.snoc, dif_pos hk]
        exact hP ⟨k.1, hk⟩
      · simp only [Fin.snoc, dif_neg hk]
        exact hPi

/-- Additive indecomposability for arbitrary interleaved 2-partitions of well-ordered sets:
if `A ⊆ X ∪ Y`, `otype X < ω ^ η`, and `ω ^ η ≤ otype A`, then `ω ^ η ≤ otype Y`. -/
private theorem opow_omega_partition (η : Ordinal.{0}) :
    ∀ {W : Type} [LinearOrder W] [WellFoundedLT W] (A X Y : Set W),
      A ⊆ X ∪ Y → otype X < ω ^ η → ω ^ η ≤ otype A → ω ^ η ≤ otype Y := by
  induction η using Ordinal.limitRecOn with
  | zero =>
    intro W _ _ A X Y hsub hX hA
    rw [Ordinal.opow_zero] at hX hA ⊢
    have hXe : X = ∅ := eq_empty_of_otype_lt_one hX
    rw [hXe, empty_union] at hsub
    exact hA.trans (otype_mono hsub)
  | add_one ζ ih =>
    intro W _ _ A X Y hsub hX hA
    rw [Ordinal.opow_add_one] at hX hA ⊢
    have hpos : (0 : Ordinal.{0}) < ω ^ ζ := Ordinal.opow_pos ζ Ordinal.omega0_pos
    have hne : (ω ^ ζ : Ordinal.{0}) ≠ 0 := ne_of_gt hpos
    have hq_lt : otype X / (ω ^ ζ) < ω :=
      (Ordinal.lt_mul_iff_div_lt hne).mp hX
    obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hq_lt
    have hX_lt : otype X < ω ^ ζ * ((m + 1 : ℕ) : Ordinal.{0}) := by
      have h1 : otype X < ω ^ ζ * Order.succ (otype X / ω ^ ζ) :=
        Ordinal.lt_mul_succ_div (otype X) hne
      simpa [hm, Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using h1
    have hprod_le :
        Ordinal.type (Prod.Lex ((· < ·) : ℕ → ℕ → Prop)
          ((· < ·) : (ω ^ ζ).ToType → (ω ^ ζ).ToType → Prop)) ≤ typeLT A := by
      rw [Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_nat_lt]
      exact hA
    obtain ⟨e⟩ := Ordinal.type_le_iff'.mp hprod_le
    let B : ℕ → Set W := fun i => (fun t : (ω ^ ζ).ToType => (e (i, t)).1) '' Set.univ
    have hB_sub : ∀ i, B i ⊆ A := by
      rintro i _ ⟨t, -, rfl⟩
      exact (e (i, t)).2
    have hB_ord : ∀ i j : ℕ, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y := by
      rintro i j hij _ ⟨t₁, -, rfl⟩ _ ⟨t₂, -, rfl⟩
      exact e.map_rel_iff.mpr (Prod.Lex.left t₁ t₂ hij)
    have hB_type : ∀ i, ω ^ ζ ≤ otype (B i) := by
      intro i
      let f : (ω ^ ζ).ToType → B i := fun t => ⟨(e (i, t)).1, ⟨t, trivial, rfl⟩⟩
      have hf : StrictMono f := fun t₁ t₂ ht => e.map_rel_iff.mpr (Prod.Lex.right i ht)
      have hle := (relEmbedding_of_strictMono f hf).ordinal_type_le
      rwa [Ordinal.type_toType] at hle
    have hexN : ∃ N : ℕ, ∀ i ≥ N, otype (X ∩ B i) < ω ^ ζ := by
      by_contra hno
      push Not at hno
      obtain ⟨f, hf_mono, hf_bad⟩ := exists_strictMono_of_unbounded
        (fun i => ω ^ ζ ≤ otype (X ∩ B i)) hno (m + 1)
      have hbad : ω ^ ζ * ((m + 1 : ℕ) : Ordinal.{0}) ≤ otype X :=
        otype_le_of_finite_blocks (fun k => B (f k))
          (fun a b hab => hB_ord (f a) (f b) (hf_mono hab))
          hf_bad
      exact not_le_of_gt hX_lt hbad
    obtain ⟨N, hN⟩ := hexN
    have hY_good : ∀ k : ℕ, ω ^ ζ ≤ otype (Y ∩ B (N + k)) := by
      intro k
      have hsubk : B (N + k) ⊆ (X ∩ B (N + k)) ∪ (Y ∩ B (N + k)) := by
        intro x hx
        rcases hsub (hB_sub (N + k) hx) with hX' | hY'
        · exact Or.inl ⟨hX', hx⟩
        · exact Or.inr ⟨hY', hx⟩
      exact ih (B (N + k)) (X ∩ B (N + k)) (Y ∩ B (N + k)) hsubk
        (hN (N + k) (Nat.le_add_right N k)) (hB_type (N + k))
    exact otype_le_of_omega_blocks (fun k => B (N + k))
      (fun i j hij => hB_ord (N + i) (N + j) (Nat.add_lt_add_left hij N))
      hY_good
  | limit η hη ih =>
    intro W _ _ A X Y hsub hX hA
    rw [Ordinal.opow_limit Ordinal.omega0_ne_zero hη] at hX hA ⊢
    have hex : ∃ ζ₀ : Iio η, otype X < ω ^ ζ₀.1 := by
      by_contra hall
      push Not at hall
      have hle : (⨆ ζ : Iio η, (ω : Ordinal.{0}) ^ ζ.1) ≤ otype X :=
        Ordinal.iSup_le (fun ζ => hall ζ)
      exact not_le_of_gt hX hle
    obtain ⟨⟨ζ₀, hζ₀⟩, hX₀⟩ := hex
    apply Ordinal.iSup_le
    intro ⟨ζ, hζ⟩
    let ζ' : Ordinal.{0} := max ζ ζ₀
    have hζ'_lt : ζ' < η := max_lt hζ hζ₀
    have hX' : otype X < ω ^ ζ' :=
      lt_of_lt_of_le hX₀ (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_max_right ζ ζ₀))
    have hA' : ω ^ ζ' ≤ otype A := by
      have h1 : (ω : Ordinal.{0}) ^ ζ' ≤ ⨆ z : Iio η, (ω : Ordinal.{0}) ^ z.1 :=
        Ordinal.le_iSup (fun z : Iio η => (ω : Ordinal.{0}) ^ z.1) ⟨ζ', hζ'_lt⟩
      exact h1.trans hA
    have hY' : ω ^ ζ' ≤ otype Y := ih ζ' hζ'_lt A X Y hsub hX' hA'
    exact (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_max_left ζ ζ₀)).trans hY'

private lemma opow_omega_union_lt {W : Type} [LinearOrder W] [WellFoundedLT W]
    {η : Ordinal.{0}} {X Y : Set W}
    (hX : otype X < ω ^ η) (hY : otype Y < ω ^ η) :
    otype (X ∪ Y) < ω ^ η := by
  by_contra hge
  push Not at hge
  have hYge := opow_omega_partition η (X ∪ Y) X Y Subset.rfl hX hge
  exact not_le_of_gt hY hYge

private lemma sub_opow_log_lt {γ : Ordinal.{0}} (hγ : γ ≠ 0) :
    γ - ω ^ Ordinal.log ω γ < γ := by
  let η : Ordinal.{0} := Ordinal.log ω γ
  have hle : ω ^ η ≤ γ := Ordinal.opow_log_le_self ω hγ
  have hlt : γ < ω ^ Order.succ η := Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 γ
  rw [Order.succ_eq_add_one, Ordinal.opow_add_one] at hlt
  have hpos : (0 : Ordinal.{0}) < ω ^ η := Ordinal.opow_pos η Ordinal.omega0_pos
  have hne : (ω ^ η : Ordinal.{0}) ≠ 0 := ne_of_gt hpos
  have hq_lt : γ / (ω ^ η) < ω := (Ordinal.lt_mul_iff_div_lt hne).mp hlt
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hq_lt
  have hm_pos : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    have hq0 : γ / (ω ^ η) = 0 := by simpa [hm0] using hm
    have hlt1 : γ < ω ^ η := by
      have := Ordinal.lt_mul_succ_div γ hne
      simpa [hq0] using this
    exact not_le_of_gt hlt1 hle
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos)
  have hdecomp : γ = ω ^ η + (ω ^ η * (k : Ordinal.{0}) + γ % ω ^ η) := by
    have hdm : ω ^ η * (γ / ω ^ η) + γ % ω ^ η = γ := Ordinal.div_add_mod γ (ω ^ η)
    rw [hm] at hdm
    have hcast : ((k + 1 : ℕ) : Ordinal.{0}) = 1 + (k : Ordinal.{0}) := by
      calc
        ((k + 1 : ℕ) : Ordinal.{0}) = ((1 + k : ℕ) : Ordinal.{0}) := by rw [Nat.add_comm]
        _ = 1 + (k : Ordinal.{0}) := by rw [Nat.cast_add, Nat.cast_one]
    rw [hcast, mul_add, mul_one, add_assoc] at hdm
    exact hdm.symm
  have hsub_eq : γ - ω ^ η = ω ^ η * (k : Ordinal.{0}) + γ % ω ^ η := by
    have h1 : ω ^ η + (γ - ω ^ η) = ω ^ η + (ω ^ η * (k : Ordinal.{0}) + γ % ω ^ η) := by
      rw [Ordinal.add_sub_cancel_of_le hle, ← hdecomp]
    exact add_left_cancel h1
  rw [hsub_eq]
  have hmod : γ % ω ^ η < ω ^ η := Ordinal.mod_lt γ hne
  have h1 : ω ^ η * (k : Ordinal.{0}) + γ % ω ^ η < ω ^ η * (k : Ordinal.{0}) + ω ^ η :=
    (add_lt_add_iff_left _).mpr hmod
  have h2 : ω ^ η * (k : Ordinal.{0}) + ω ^ η = ω ^ η * ((k + 1 : ℕ) : Ordinal.{0}) := by
    rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
  have h3 : ω ^ η * ((k + 1 : ℕ) : Ordinal.{0}) ≤ γ := by
    rw [← hm]
    exact Ordinal.mul_div_le γ (ω ^ η)
  exact lt_of_lt_of_le (h2 ▸ h1) h3

/-- Cantor normal form decomposition of any well-ordered subset `D` into a finite list of
additively indecomposable pieces whose combined order-type dominance recovers `otype D`. -/
private theorem exists_indecomposable_decomp {W : Type} [LinearOrder W] [WellFoundedLT W] :
    ∀ (γ : Ordinal.{0}) (D : Set W), otype D = γ →
      ∃ L : List (Set W),
        (∀ X ∈ L, X ⊆ D ∧ ∃ η : Ordinal.{0}, otype X = ω ^ η) ∧
        ∀ M : Set W, (∀ X ∈ L, otype X ≤ otype (M ∩ X)) → otype D ≤ otype M := by
  intro γ
  refine WellFoundedLT.induction (motive := fun γ => ∀ D : Set W, otype D = γ →
      ∃ L : List (Set W),
        (∀ X ∈ L, X ⊆ D ∧ ∃ η : Ordinal.{0}, otype X = ω ^ η) ∧
        ∀ M : Set W, (∀ X ∈ L, otype X ≤ otype (M ∩ X)) → otype D ≤ otype M) γ (fun γ ih => ?_)
  intro D hD
  by_cases hγ : γ = 0
  · refine ⟨[], fun _ h => (List.not_mem_nil h).elim, ?_⟩
    intro M _
    rw [hD, hγ]
    exact zero_le
  · let η : Ordinal.{0} := Ordinal.log ω γ
    let δ : Ordinal.{0} := γ - ω ^ η
    have hle : ω ^ η ≤ γ := Ordinal.opow_log_le_self ω hγ
    have hadd : ω ^ η + δ = γ := Ordinal.add_sub_cancel_of_le hle
    have hδ_lt : δ < γ := sub_opow_log_lt hγ
    have hsum_eq :
        Ordinal.type (Sum.Lex ((· < ·) : (ω ^ η).ToType → (ω ^ η).ToType → Prop)
          ((· < ·) : δ.ToType → δ.ToType → Prop)) = typeLT D := by
      rw [Ordinal.type_sum_lex, Ordinal.type_toType, Ordinal.type_toType, hadd]
      exact hD.symm
    obtain ⟨e⟩ := Ordinal.type_eq.mp hsum_eq
    let D₁ : Set W := (fun a : (ω ^ η).ToType => (e (Sum.inl a)).1) '' Set.univ
    let D₂ : Set W := (fun b : δ.ToType => (e (Sum.inr b)).1) '' Set.univ
    have hD₁_sub : D₁ ⊆ D := by
      rintro _ ⟨a, -, rfl⟩; exact (e (Sum.inl a)).2
    have hD₂_sub : D₂ ⊆ D := by
      rintro _ ⟨b, -, rfl⟩; exact (e (Sum.inr b)).2
    have hD_ord : ∀ x ∈ D₁, ∀ y ∈ D₂, x < y := by
      rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
      exact e.map_rel_iff.mpr (Sum.Lex.sep a b)
    have hD₁_type : otype D₁ = ω ^ η := by
      let iso : ((· < ·) : (ω ^ η).ToType → (ω ^ η).ToType → Prop) ≃r
          ((· < ·) : D₁ → D₁ → Prop) :=
        { toFun := fun a => ⟨(e (Sum.inl a)).1, ⟨a, trivial, rfl⟩⟩
          invFun := fun x =>
            Classical.choose (by
              rcases x.2 with ⟨a, -, ha⟩
              exact ⟨a, ha⟩ : ∃ a : (ω ^ η).ToType, (e (Sum.inl a)).1 = x.1)
          left_inv := fun a => by
            have hspec : (e (Sum.inl (Classical.choose
                (show ∃ b : (ω ^ η).ToType, (e (Sum.inl b)).1 = (e (Sum.inl a)).1 from ⟨a, rfl⟩)))).1 =
                (e (Sum.inl a)).1 :=
              Classical.choose_spec
                (show ∃ b : (ω ^ η).ToType, (e (Sum.inl b)).1 = (e (Sum.inl a)).1 from ⟨a, rfl⟩)
            exact Sum.inl_injective (e.injective (Subtype.ext hspec))
          right_inv := fun x => by
            apply Subtype.ext
            exact Classical.choose_spec (by
              rcases x.2 with ⟨a, -, ha⟩
              exact ⟨a, ha⟩ : ∃ a : (ω ^ η).ToType, (e (Sum.inl a)).1 = x.1)
          map_rel_iff' := fun {a b} => by
            change (e (Sum.inl a)).1 < (e (Sum.inl b)).1 ↔ a < b
            rw [show (e (Sum.inl a)).1 < (e (Sum.inl b)).1 ↔ e (Sum.inl a) < e (Sum.inl b) from Iff.rfl,
              e.map_rel_iff]
            exact ⟨fun h => by cases h with | inl h' => exact h', fun h => Sum.Lex.inl h⟩ }
      rw [otype, ← Ordinal.type_toType (ω ^ η)]
      exact (Ordinal.type_eq.mpr ⟨iso⟩).symm
    have hD₂_type : otype D₂ = δ := by
      let iso : ((· < ·) : δ.ToType → δ.ToType → Prop) ≃r
          ((· < ·) : D₂ → D₂ → Prop) :=
        { toFun := fun b => ⟨(e (Sum.inr b)).1, ⟨b, trivial, rfl⟩⟩
          invFun := fun x =>
            Classical.choose (by
              rcases x.2 with ⟨b, -, hb⟩
              exact ⟨b, hb⟩ : ∃ b : δ.ToType, (e (Sum.inr b)).1 = x.1)
          left_inv := fun b => by
            have hspec : (e (Sum.inr (Classical.choose
                (show ∃ c : δ.ToType, (e (Sum.inr c)).1 = (e (Sum.inr b)).1 from ⟨b, rfl⟩)))).1 =
                (e (Sum.inr b)).1 :=
              Classical.choose_spec
                (show ∃ c : δ.ToType, (e (Sum.inr c)).1 = (e (Sum.inr b)).1 from ⟨b, rfl⟩)
            exact Sum.inr_injective (e.injective (Subtype.ext hspec))
          right_inv := fun x => by
            apply Subtype.ext
            exact Classical.choose_spec (by
              rcases x.2 with ⟨b, -, hb⟩
              exact ⟨b, hb⟩ : ∃ b : δ.ToType, (e (Sum.inr b)).1 = x.1)
          map_rel_iff' := fun {a b} => by
            change (e (Sum.inr a)).1 < (e (Sum.inr b)).1 ↔ a < b
            rw [show (e (Sum.inr a)).1 < (e (Sum.inr b)).1 ↔ e (Sum.inr a) < e (Sum.inr b) from Iff.rfl,
              e.map_rel_iff]
            exact ⟨fun h => by cases h with | inr h' => exact h', fun h => Sum.Lex.inr h⟩ }
      rw [otype, ← Ordinal.type_toType δ]
      exact (Ordinal.type_eq.mpr ⟨iso⟩).symm
    obtain ⟨L₂, hL₂_info, hL₂_rec⟩ := ih δ hδ_lt D₂ hD₂_type
    refine ⟨D₁ :: L₂, ?_, ?_⟩
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hX₂
      · exact ⟨hD₁_sub, η, hD₁_type⟩
      · obtain ⟨hsub₂, hη₂⟩ := hL₂_info X hX₂
        exact ⟨hsub₂.trans hD₂_sub, hη₂⟩
    · intro M hM
      have hM₁ : ω ^ η ≤ otype (M ∩ D₁) := by
        rw [← hD₁_type]
        exact hM D₁ List.mem_cons_self
      have hM₂ : δ ≤ otype (M ∩ D₂) := by
        rw [← hD₂_type]
        apply hL₂_rec (M ∩ D₂)
        intro X hX
        have hsubX : X ⊆ D₂ := (hL₂_info X hX).1
        have heq : (M ∩ D₂) ∩ X = M ∩ X := by
          ext x; exact ⟨fun ⟨⟨hm, _⟩, hx⟩ => ⟨hm, hx⟩, fun ⟨hm, hx⟩ => ⟨⟨hm, hsubX hx⟩, hx⟩⟩
        rw [heq]
        exact hM X (List.mem_cons_of_mem D₁ hX)
      obtain ⟨e₁⟩ := Ordinal.type_le_iff'.mp (by simpa [otype, Ordinal.type_toType] using hM₁ :
        typeLT (ω ^ η).ToType ≤ typeLT (M ∩ D₁ : Set W))
      obtain ⟨e₂⟩ := Ordinal.type_le_iff'.mp (by simpa [otype, Ordinal.type_toType] using hM₂ :
        typeLT δ.ToType ≤ typeLT (M ∩ D₂ : Set W))
      let f : (ω ^ η).ToType ⊕ δ.ToType → M :=
        Sum.elim (fun a => ⟨(e₁ a).1, (e₁ a).2.1⟩) (fun b => ⟨(e₂ b).1, (e₂ b).2.1⟩)
      have hf : ∀ p q : (ω ^ η).ToType ⊕ δ.ToType,
          Sum.Lex (· < ·) (· < ·) p q → f p < f q := by
        intro p q hpq
        cases hpq with
        | inl h => exact e₁.map_rel_iff.mpr h
        | inr h => exact e₂.map_rel_iff.mpr h
        | sep a b => exact hD_ord _ (e₁ a).2.2 _ (e₂ b).2.2
      have hleM := (relEmbedding_of_sum_lex f hf).ordinal_type_le
      rw [Ordinal.type_sum_lex, Ordinal.type_toType, Ordinal.type_toType, hadd, ← hD] at hleM
      exact hleM

private lemma otype_Iic_lt_of_isSuccLimit {W : Type} [LinearOrder W] [WellFoundedLT W]
    {A : Set W} (hlim : Order.IsSuccLimit (otype A)) (x : A) :
    otype ({y ∈ A | y ≤ x.1} : Set W) < otype A := by
  have h1 : typeLT (Set.Iio x) < otype A := by
    rw [Ordinal.type_Iio_lt]
    exact Ordinal.typein_lt_type (· < ·) x
  have h2 : otype ({y ∈ A | y ≤ x.1} : Set W) ≤ typeLT (Set.Iio x) + 1 := by
    let f : ({y ∈ A | y ≤ x.1} : Set W) → Set.Iio x ⊕ Fin 1 := fun y =>
      if hy : y.1 < x.1 then Sum.inl ⟨⟨y.1, y.2.1⟩, hy⟩ else Sum.inr 0
    have hinj : Function.Injective f := fun y₁ y₂ heq => by
      apply Subtype.ext
      by_cases h₁ : y₁.1 < x.1 <;> by_cases h₂ : y₂.1 < x.1
      · simp only [f, dif_pos h₁, dif_pos h₂, Sum.inl.injEq] at heq
        exact congrArg (fun z : Set.Iio x => z.1.1) heq
      · simp only [f, dif_pos h₁, dif_neg h₂, reduceCtorEq] at heq
      · simp only [f, dif_neg h₁, dif_pos h₂, reduceCtorEq] at heq
      · have e₁ : y₁.1 = x.1 := le_antisymm y₁.2.2 (not_lt.mp h₁)
        have e₂ : y₂.1 = x.1 := le_antisymm y₂.2.2 (not_lt.mp h₂)
        exact e₁.trans e₂.symm
    have hmap : ∀ {y₁ y₂ : ({y ∈ A | y ≤ x.1} : Set W)},
        Sum.Lex ((· < ·) : Set.Iio x → Set.Iio x → Prop)
          ((· < ·) : Fin 1 → Fin 1 → Prop) (f y₁) (f y₂) ↔ y₁ < y₂ := by
      intro y₁ y₂
      by_cases h₁ : y₁.1 < x.1 <;> by_cases h₂ : y₂.1 < x.1
      · simp only [f, dif_pos h₁, dif_pos h₂]
        exact ⟨fun h => by cases h with | inl h' => exact h', fun h => Sum.Lex.inl h⟩
      · simp only [f, dif_pos h₁, dif_neg h₂]
        have e₂ : y₂.1 = x.1 := le_antisymm y₂.2.2 (not_lt.mp h₂)
        exact ⟨fun _ => show y₁.1 < y₂.1 by rw [e₂]; exact h₁, fun _ => Sum.Lex.sep _ _⟩
      · simp only [f, dif_neg h₁, dif_pos h₂]
        have e₁ : y₁.1 = x.1 := le_antisymm y₁.2.2 (not_lt.mp h₁)
        exact ⟨fun h => (by cases h), fun h => by
          change y₁.1 < y₂.1 at h
          rw [e₁] at h
          exact (lt_asymm h h₂).elim⟩
      · simp only [f, dif_neg h₁, dif_neg h₂]
        have e₁ : y₁.1 = x.1 := le_antisymm y₁.2.2 (not_lt.mp h₁)
        have e₂ : y₂.1 = x.1 := le_antisymm y₂.2.2 (not_lt.mp h₂)
        exact ⟨fun h => by cases h with | inr h' => exact (lt_irrefl _ h').elim,
          fun h => by change y₁.1 < y₂.1 at h; rw [e₁, e₂] at h; exact (lt_irrefl _ h).elim⟩
    let iso : ((· < ·) : ({y ∈ A | y ≤ x.1} : Set W) → ({y ∈ A | y ≤ x.1} : Set W) → Prop) ↪r
        Sum.Lex ((· < ·) : Set.Iio x → Set.Iio x → Prop) ((· < ·) : Fin 1 → Fin 1 → Prop) :=
      ⟨⟨f, hinj⟩, hmap⟩
    have hle := iso.ordinal_type_le
    rwa [Ordinal.type_sum_lex, Ordinal.type_fin, Nat.cast_one] at hle
  have hsucc : typeLT (Set.Iio x) + 1 < otype A := by
    rw [← Order.succ_eq_add_one]
    exact hlim.succ_lt h1
  exact lt_of_le_of_lt h2 hsucc

private lemma tail_gt_otype_eq {W : Type} [LinearOrder W] [WellFoundedLT W]
    {η : Ordinal.{0}} (hη : η ≠ 0) {A A₁ : Set W}
    (hA : otype A = ω ^ η) (hsub : A₁ ⊆ A) (hA₁ : otype A₁ = ω ^ η)
    {x : W} (hx : x ∈ A) :
    otype ({y ∈ A₁ | x < y} : Set W) = ω ^ η := by
  have hlim : Order.IsSuccLimit (otype A) := by
    rw [hA]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hη
  have hle_part : otype ({y ∈ A₁ | y ≤ x} : Set W) < ω ^ η := by
    have h1 : otype ({y ∈ A₁ | y ≤ x} : Set W) ≤ otype ({y ∈ A | y ≤ x} : Set W) :=
      otype_mono (fun y ⟨hy₁, hyx⟩ => ⟨hsub hy₁, hyx⟩)
    have h2 : otype ({y ∈ A | y ≤ x} : Set W) < otype A :=
      otype_Iic_lt_of_isSuccLimit hlim ⟨x, hx⟩
    exact lt_of_le_of_lt h1 (hA ▸ h2)
  have hcov : A₁ ⊆ {y ∈ A₁ | y ≤ x} ∪ {y ∈ A₁ | x < y} := by
    intro y hy
    rcases le_or_gt y x with h | h
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩
  have hge : ω ^ η ≤ otype ({y ∈ A₁ | x < y} : Set W) :=
    opow_omega_partition η A₁ {y ∈ A₁ | y ≤ x} {y ∈ A₁ | x < y} hcov hle_part hA₁.ge
  have hle : otype ({y ∈ A₁ | x < y} : Set W) ≤ ω ^ η :=
    (otype_mono (fun _ h => h.1)).trans_eq hA₁
  exact le_antisymm hle hge

private lemma otype_pair_lt_omega {W : Type} [LinearOrder W] [WellFoundedLT W]
    (u v : W) : otype ({u, v} : Set W) < ω := by
  have : Fintype ({u, v} : Set W) := Set.Finite.fintype (Set.toFinite _)
  rw [otype, Ordinal.type_fintype]
  exact Ordinal.natCast_lt_omega0 _

/- ## Section 2: Cardinality and ordinal arithmetic for `α = (ω ^ ω) ^ (n + 1)` -/

private noncomputable def alpha (n : ℕ) : Ordinal.{0} := (ω ^ ω : Ordinal.{0}) ^ (n + 1)

private noncomputable def eta (n : ℕ) : Ordinal.{0} := ω * ((n + 1 : ℕ) : Ordinal.{0})

private lemma alpha_eq_opow (n : ℕ) : alpha n = ω ^ eta n := by
  unfold alpha eta
  rw [Ordinal.opow_mul, Ordinal.opow_natCast]

private lemma eta_ne_zero (n : ℕ) : eta n ≠ 0 := by
  unfold eta
  apply mul_ne_zero Ordinal.omega0_ne_zero
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)

private lemma omega_le_alpha (n : ℕ) : ω ≤ alpha n := by
  rw [alpha_eq_opow]
  have h1 : (1 : Ordinal.{0}) ≤ eta n :=
    Order.one_le_iff_ne_zero.mpr (eta_ne_zero n)
  simpa [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos h1

private lemma alpha_mul_alpha (n : ℕ) :
    alpha n * alpha n = (ω ^ ω : Ordinal.{0}) ^ ((n + 1) * 2) := by
  unfold alpha
  rw [← pow_two, ← pow_mul]

private lemma omega_mul_alpha (n : ℕ) : ω * alpha n = alpha n := by
  rw [alpha_eq_opow]
  have h1 : (1 : Ordinal.{0}) + eta n = eta n := by
    unfold eta
    have hcast : ((n + 1 : ℕ) : Ordinal.{0}) = 1 + (n : Ordinal.{0}) := by
      calc
        ((n + 1 : ℕ) : Ordinal.{0}) = ((1 + n : ℕ) : Ordinal.{0}) := by rw [Nat.add_comm]
        _ = 1 + (n : Ordinal.{0}) := by rw [Nat.cast_add, Nat.cast_one]
    rw [hcast, mul_add, mul_one, ← add_assoc, Ordinal.one_add_omega0]
  calc
    ω * ω ^ eta n = ω ^ (1 : Ordinal.{0}) * ω ^ eta n := by rw [Ordinal.opow_one]
    _ = ω ^ (1 + eta n) := (Ordinal.opow_add _ _ _).symm
    _ = ω ^ eta n := by rw [h1]

private lemma alpha_countable (n : ℕ) : Countable (alpha n).ToType := by
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType, alpha_eq_opow]
  have h1 : (ω ^ eta n : Ordinal.{0}).card ≤ max (ω : Ordinal.{0}).card (eta n).card :=
    Ordinal.card_opow_le_of_omega0_le_left le_rfl (eta n)
  have h2 : (eta n).card ≤ ℵ₀ := by
    unfold eta
    rw [Ordinal.card_mul, Ordinal.card_omega0, Ordinal.card_nat]
    calc
      ℵ₀ * ((n + 1 : ℕ) : Cardinal.{0}) ≤ ℵ₀ * ℵ₀ :=
        mul_le_mul_of_nonneg_left (le_of_lt Cardinal.natCast_lt_aleph0) zero_le
      _ = ℵ₀ := Cardinal.aleph0_mul_aleph0
  exact h1.trans (max_le (by rw [Ordinal.card_omega0]) h2)

private lemma alpha_nonempty (n : ℕ) : Nonempty (alpha n).ToType := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h0 : typeLT (alpha n).ToType = 0 := Ordinal.type_eq_zero_iff_isEmpty.mpr h
  rw [Ordinal.type_toType] at h0
  have hle : ω ≤ (0 : Ordinal.{0}) := h0 ▸ omega_le_alpha n
  exact not_lt_of_ge hle Ordinal.omega0_pos

/- ## Section 3: Erdős--Milner local claims (8), (9), and (10) -/

/-- Red neighborhood of `x` inside `S`. -/
private def K1 (blue : SimpleGraph Host) (S : Set Host) (x : Host) : Set Host :=
  {y ∈ S | y ≠ x ∧ ¬ blue.Adj x y}

/-- Claim (8): Under the contradiction hypothesis that `S` contains no red clique of order type
`alpha n`, every subset of `S` of order type at least `alpha n` contains a blue edge. -/
private lemma claim8 (n : ℕ) (blue : SimpleGraph Host) (S : Set Host)
    (hno : ∀ T : Set Host, T ⊆ S → blueᶜ.IsClique T → otype T ≠ alpha n)
    {A : Set Host} (hAsub : A ⊆ S) (hAtype : alpha n ≤ otype A) :
    ∃ u ∈ A, ∃ v ∈ A, blue.Adj u v := by
  by_contra hnob
  push Not at hnob
  obtain ⟨T, hTA, hTtype⟩ := exists_subset_otype_eq hAtype
  have hTclique : blueᶜ.IsClique T := by
    intro u hu v hv huv
    exact (blue.compl_adj u v).mpr ⟨huv, hnob u (hTA hu) v (hTA hv)⟩
  exact hno T (hTA.trans hAsub) hTclique hTtype

/-- Claim (9) for an additively indecomposable index set `D`. -/
private lemma claim9_indec (n : ℕ) (blue : SimpleGraph Host) (hfree : blue.CliqueFree 3)
    (S : Set Host)
    (hno : ∀ T : Set Host, T ⊆ S → blueᶜ.IsClique T → otype T ≠ alpha n)
    {D : Set (alpha n).ToType} {ξ : Ordinal.{0}} (hD : otype D = ω ^ ξ)
    {A : Set Host} (hAsub : A ⊆ S) (hAtype : alpha n ≤ otype A)
    {F : (alpha n).ToType → Set Host}
    (hFsub : ∀ ν ∈ D, F ν ⊆ S) (hFtype : ∀ ν ∈ D, alpha n ≤ otype (F ν)) :
    alpha n ≤ otype ({x ∈ A | otype D ≤ otype ({ν ∈ D | alpha n ≤ otype (K1 blue S x ∩ F ν)} : Set _)} : Set Host) := by
  let M : Host → Set (alpha n).ToType :=
    fun x => {ν ∈ D | alpha n ≤ otype (K1 blue S x ∩ F ν)}
  let Agood : Set Host := {x ∈ A | otype D ≤ otype (M x)}
  let Abad : Set Host := {x ∈ A | otype (M x) < otype D}
  by_contra hlt
  push Not at hlt
  have hcov : A ⊆ Agood ∪ Abad := by
    intro x hx
    rcases le_or_gt (otype D) (otype (M x)) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hAbad_ge : alpha n ≤ otype Abad := by
    have hlt' : otype Agood < ω ^ eta n := by
      have h1 : otype Agood < alpha n := hlt
      rwa [alpha_eq_opow] at h1
    have hA' : ω ^ eta n ≤ otype A := by
      rwa [alpha_eq_opow] at hAtype
    have hres := opow_omega_partition (eta n) A Agood Abad hcov hlt' hA'
    rwa [← alpha_eq_opow] at hres
  obtain ⟨u, hu, v, hv, huv⟩ := claim8 n blue S hno (fun _ h => hAsub h.1) hAbad_ge
  have hMu : otype (M u) < ω ^ ξ := hD ▸ hu.2
  have hMv : otype (M v) < ω ^ ξ := hD ▸ hv.2
  have hMuv : otype (M u ∪ M v) < ω ^ ξ := opow_omega_union_lt hMu hMv
  have hneD : ∃ ν ∈ D, ν ∉ M u ∪ M v := by
    by_contra hall
    push Not at hall
    have hDle : ω ^ ξ ≤ otype (M u ∪ M v) := hD ▸ otype_mono hall
    exact not_le_of_gt hMuv hDle
  obtain ⟨ν, hνD, hνnot⟩ := hneD
  have hKu : otype (K1 blue S u ∩ F ν) < alpha n := by
    by_contra hge; push Not at hge
    exact hνnot (Or.inl ⟨hνD, hge⟩)
  have hKv : otype (K1 blue S v ∩ F ν) < alpha n := by
    by_contra hge; push Not at hge
    exact hνnot (Or.inr ⟨hνD, hge⟩)
  have hpair : otype (({u, v} : Set Host) ∩ F ν) < alpha n := by
    have h1 : otype (({u, v} : Set Host) ∩ F ν) ≤ otype ({u, v} : Set Host) :=
      otype_mono inter_subset_left
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le (otype_pair_lt_omega u v) (omega_le_alpha n))
  have hunion : otype (((K1 blue S u ∩ F ν) ∪ (K1 blue S v ∩ F ν)) ∪ (({u, v} : Set Host) ∩ F ν)) < alpha n := by
    rw [alpha_eq_opow] at hKu hKv hpair ⊢
    exact opow_omega_union_lt (opow_omega_union_lt hKu hKv) hpair
  have hexw : ∃ w ∈ F ν, w ∉ ((K1 blue S u ∩ F ν) ∪ (K1 blue S v ∩ F ν)) ∪ (({u, v} : Set Host) ∩ F ν) := by
    by_contra hall
    push Not at hall
    have hFle : alpha n ≤ otype (((K1 blue S u ∩ F ν) ∪ (K1 blue S v ∩ F ν)) ∪ (({u, v} : Set Host) ∩ F ν)) :=
      (hFtype ν hνD).trans (otype_mono hall)
    exact not_le_of_gt hunion hFle
  obtain ⟨w, hwF, hwnot⟩ := hexw
  have hwu : w ≠ u := fun h => hwnot (Or.inr ⟨Or.inl h, hwF⟩)
  have hwv : w ≠ v := fun h => hwnot (Or.inr ⟨Or.inr h, hwF⟩)
  have hbuw : blue.Adj u w := by
    by_contra hnb
    exact hwnot (Or.inl (Or.inl ⟨⟨hFsub ν hνD hwF, hwu, hnb⟩, hwF⟩))
  have hbvw : blue.Adj v w := by
    by_contra hnb
    exact hwnot (Or.inl (Or.inr ⟨⟨hFsub ν hνD hwF, hwv, hnb⟩, hwF⟩))
  have hne_uv : u ≠ v := blue.ne_of_adj huv
  let tri : Finset Host := {u, v, w}
  have htri_card : tri.card = 3 := by
    have h1 : u ∉ ({v, w} : Finset Host) := by
      simp [hne_uv, hwu.symm]
    have h2 : v ∉ ({w} : Finset Host) := by
      simp [hwv.symm]
    simp [tri, h1, h2]
  have htri_clique : blue.IsNClique 3 tri := by
    refine ⟨?_, htri_card⟩
    intro a ha b hb hab
    simp only [tri, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact huv
    · exact hbuw
    · exact huv.symm
    · exact (hab rfl).elim
    · exact hbvw
    · exact hbuw.symm
    · exact hbvw.symm
    · exact (hab rfl).elim
  exact hfree tri htri_clique

/-- Claim (9) for an arbitrary subset `D : Set (alpha n).ToType`. -/
private lemma claim9 (n : ℕ) (blue : SimpleGraph Host) (hfree : blue.CliqueFree 3)
    (S : Set Host)
    (hno : ∀ T : Set Host, T ⊆ S → blueᶜ.IsClique T → otype T ≠ alpha n)
    (D : Set (alpha n).ToType)
    {A : Set Host} (hAsub : A ⊆ S) (hAtype : alpha n ≤ otype A)
    {F : (alpha n).ToType → Set Host}
    (hFsub : ∀ ν ∈ D, F ν ⊆ S) (hFtype : ∀ ν ∈ D, alpha n ≤ otype (F ν)) :
    alpha n ≤ otype ({x ∈ A | otype D ≤ otype ({ν ∈ D | alpha n ≤ otype (K1 blue S x ∩ F ν)} : Set _)} : Set Host) := by
  obtain ⟨L, hLinfo, hLrec⟩ := exists_indecomposable_decomp (otype D) D rfl
  have hstep : ∀ (L' : List (Set (alpha n).ToType)),
      (∀ X ∈ L', X ⊆ D ∧ ∃ ξ : Ordinal.{0}, otype X = ω ^ ξ) →
      alpha n ≤ otype ({x ∈ A | ∀ X ∈ L', otype X ≤ otype ({ν ∈ X | alpha n ≤ otype (K1 blue S x ∩ F ν)} : Set _)} : Set Host) := by
    intro L'
    induction L' with
    | nil =>
      intro _
      have heq : ({x ∈ A | ∀ X ∈ ([] : List (Set (alpha n).ToType)),
          otype X ≤ otype ({ν ∈ X | alpha n ≤ otype (K1 blue S x ∩ F ν)} : Set _)} : Set Host) = A := by
        ext x; simp
      rw [heq]
      exact hAtype
    | cons X rest ih =>
      intro hinfo
      have hrest : ∀ Y ∈ rest, Y ⊆ D ∧ ∃ ξ : Ordinal.{0}, otype Y = ω ^ ξ :=
        fun Y hY => hinfo Y (List.mem_cons_of_mem X hY)
      have hArest := ih hrest
      obtain ⟨hXD, ξ, hXtype⟩ := hinfo X List.mem_cons_self
      have hres := claim9_indec n blue hfree S hno hXtype (fun _ hx => hAsub hx.1) hArest
        (fun ν hν => hFsub ν (hXD hν)) (fun ν hν => hFtype ν (hXD hν))
      refine hres.trans (otype_mono ?_)
      intro x hx
      refine ⟨hx.1.1, fun Y hY => ?_⟩
      rcases List.mem_cons.mp hY with rfl | hYr
      · exact hx.2
      · exact hx.1.2 Y hYr
  have hLgood := hstep L hLinfo
  refine hLgood.trans (otype_mono ?_)
  intro x hx
  refine ⟨hx.1, ?_⟩
  apply hLrec {ν ∈ D | alpha n ≤ otype (K1 blue S x ∩ F ν)}
  intro X hX
  have hXD : X ⊆ D := (hLinfo X hX).1
  have heq : {ν ∈ D | alpha n ≤ otype (K1 blue S x ∩ F ν)} ∩ X =
      {ν ∈ X | alpha n ≤ otype (K1 blue S x ∩ F ν)} := by
    ext ν
    exact ⟨fun ⟨⟨_, h⟩, hνX⟩ => ⟨hνX, h⟩, fun ⟨hνX, h⟩ => ⟨⟨hXD hνX, h⟩, hνX⟩⟩
  rw [heq]
  exact hx.2 X hX

/-- Helper: two points with the same count of elements of `F` below them have the exact same
initial segment of `F` below them. -/
private lemma filter_lt_eq_of_card_eq {α : Type} [LinearOrder α] (F : Finset α) {x y : α}
    (hcard : (F.filter (· < x)).card = (F.filter (· < y)).card) :
    F.filter (· < x) = F.filter (· < y) := by
  rcases le_total x y with hxy | hyx
  · exact Finset.eq_of_subset_of_card_le
      (fun p hp => by
        simp only [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, lt_of_lt_of_le hp.2 hxy⟩)
      hcard.ge
  · exact (Finset.eq_of_subset_of_card_le
      (fun p hp => by
        simp only [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, lt_of_lt_of_le hp.2 hyx⟩)
      hcard.le).symm

/-- Claim (10): Given a finite set `Fset` of indices, a block `A ⊆ S` of order type `alpha n`,
and a family `fam` of order-type-`alpha n` blocks in `S`, there exist `x₀ ∈ A` and a strictly
monotone self-map `g` fixing `Fset` pointwise such that `K1 x₀ ∩ fam (g ν)` has order type at
least `alpha n` for every `ν`. -/
private lemma claim10 (n : ℕ) (blue : SimpleGraph Host) (hfree : blue.CliqueFree 3)
    (S : Set Host)
    (hno : ∀ T : Set Host, T ⊆ S → blueᶜ.IsClique T → otype T ≠ alpha n)
    (Fset : Finset (alpha n).ToType)
    {A : Set Host} (hAsub : A ⊆ S) (hAtype : alpha n ≤ otype A)
    (fam : (alpha n).ToType → Set Host)
    (hfsub : ∀ ν, fam ν ⊆ S) (hftype : ∀ ν, alpha n ≤ otype (fam ν)) :
    ∃ x₀ ∈ A, ∃ g : (alpha n).ToType → (alpha n).ToType,
      StrictMono g ∧ (∀ ν ∈ Fset, g ν = ν) ∧
      ∀ ν, alpha n ≤ otype (K1 blue S x₀ ∩ fam (g ν)) := by
  let D : Fin (Fset.card + 1) → Set (alpha n).ToType :=
    fun k => {ν : (alpha n).ToType | ν ∉ Fset ∧ (Fset.filter (· < ν)).card = k.1}
  let pieces : List (Set (alpha n).ToType) :=
    (Fset.toList.map (fun ν => ({ν} : Set (alpha n).ToType))) ++
    ((List.finRange (Fset.card + 1)).map D)
  have hiter : ∀ (L : List (Set (alpha n).ToType)),
      alpha n ≤ otype ({x ∈ A | ∀ P ∈ L, otype P ≤ otype ({ν ∈ P | alpha n ≤ otype (K1 blue S x ∩ fam ν)} : Set _)} : Set Host) := by
    intro L
    induction L with
    | nil =>
      have heq : ({x ∈ A | ∀ P ∈ ([] : List (Set (alpha n).ToType)),
          otype P ≤ otype ({ν ∈ P | alpha n ≤ otype (K1 blue S x ∩ fam ν)} : Set _)} : Set Host) = A := by
        ext x; simp
      rw [heq]
      exact hAtype
    | cons P rest ih =>
      have hres := claim9 n blue hfree S hno P (fun _ hx => hAsub hx.1) ih
        (fun ν _ => hfsub ν) (fun ν _ => hftype ν)
      refine hres.trans (otype_mono ?_)
      intro x hx
      refine ⟨hx.1.1, fun Q hQ => ?_⟩
      rcases List.mem_cons.mp hQ with rfl | hQr
      · exact hx.2
      · exact hx.1.2 Q hQr
  let Agood : Set Host :=
    {x ∈ A | ∀ P ∈ pieces, otype P ≤ otype ({ν ∈ P | alpha n ≤ otype (K1 blue S x ∩ fam ν)} : Set _)}
  have hAgood_ge : alpha n ≤ otype Agood := hiter pieces
  have hAgood_ne : Agood.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : otype Agood = 0 := hemp ▸ otype_empty
    rw [h0] at hAgood_ge
    exact not_lt_of_ge hAgood_ge (lt_of_lt_of_le Ordinal.omega0_pos (omega_le_alpha n))
  obtain ⟨x₀, hx₀A, hx₀good⟩ := hAgood_ne
  have hF_good : ∀ ν ∈ Fset, alpha n ≤ otype (K1 blue S x₀ ∩ fam ν) := by
    intro ν hν
    have hmem : ({ν} : Set (alpha n).ToType) ∈ pieces :=
      List.mem_append_left _ (List.mem_map.mpr ⟨ν, Finset.mem_toList.mpr hν, rfl⟩)
    have hle := hx₀good {ν} hmem
    have h1 : (1 : Ordinal.{0}) ≤ otype ({ν} : Set (alpha n).ToType) := by
      have hfin : typeLT (Fin 1) = (1 : Ordinal.{0}) := by simp
      rw [← hfin]
      exact (relEmbedding_of_strictMono
        (fun _ : Fin 1 => (⟨ν, rfl⟩ : ({ν} : Set (alpha n).ToType)))
        (fun a b hab => by omega)).ordinal_type_le
    have hpos : (0 : Ordinal.{0}) < otype ({μ ∈ ({ν} : Set (alpha n).ToType) | alpha n ≤ otype (K1 blue S x₀ ∩ fam μ)} : Set _) :=
      lt_of_lt_of_le zero_lt_one (h1.trans hle)
    have hne : ({μ ∈ ({ν} : Set (alpha n).ToType) | alpha n ≤ otype (K1 blue S x₀ ∩ fam μ)} : Set _).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, otype_empty] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨μ, hμeq, hμgood⟩ := hne
    rw [mem_singleton_iff] at hμeq
    rwa [← hμeq]
  have hD_iso : ∀ k : Fin (Fset.card + 1),
      Nonempty (((· < ·) : D k → D k → Prop) ≃r
        ((· < ·) : ({ν ∈ D k | alpha n ≤ otype (K1 blue S x₀ ∩ fam ν)} : Set _) →
          ({ν ∈ D k | alpha n ≤ otype (K1 blue S x₀ ∩ fam ν)} : Set _) → Prop)) := by
    intro k
    have hmem : D k ∈ pieces :=
      List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)
    have hge := hx₀good (D k) hmem
    have hle : otype ({ν ∈ D k | alpha n ≤ otype (K1 blue S x₀ ∩ fam ν)} : Set _) ≤ otype (D k) :=
      otype_mono (fun _ h => h.1)
    exact Ordinal.type_eq.mp (le_antisymm hge hle)
  let eD := fun k => Classical.choice (hD_iso k)
  let idx : (alpha n).ToType → Fin (Fset.card + 1) :=
    fun ν => ⟨(Fset.filter (· < ν)).card,
      Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))⟩
  let g : (alpha n).ToType → (alpha n).ToType :=
    fun ν =>
      if hν : ν ∈ Fset then ν
      else (eD (idx ν) ⟨ν, hν, rfl⟩).1
  have hg_fix : ∀ ν ∈ Fset, g ν = ν := fun ν hν => dif_pos hν
  have hg_memD : ∀ {ν}, (hν : ν ∉ Fset) → g ν ∈ D (idx ν) := by
    intro ν hν
    simpa only [g, dif_neg hν] using (eD (idx ν) ⟨ν, hν, rfl⟩).2.1
  have hg_filter : ∀ {ν}, ν ∉ Fset → Fset.filter (· < g ν) = Fset.filter (· < ν) := by
    intro ν hν
    exact filter_lt_eq_of_card_eq Fset (hg_memD hν).2
  have hg_notmem : ∀ {ν}, ν ∉ Fset → g ν ∉ Fset := fun hν => (hg_memD hν).1
  have hg_mono : StrictMono g := by
    intro ν₁ ν₂ hlt
    by_cases h₁ : ν₁ ∈ Fset <;> by_cases h₂ : ν₂ ∈ Fset
    · rwa [hg_fix ν₁ h₁, hg_fix ν₂ h₂]
    · rw [hg_fix ν₁ h₁]
      have hmem : ν₁ ∈ Fset.filter (· < g ν₂) := by
        rw [hg_filter h₂]
        exact Finset.mem_filter.mpr ⟨h₁, hlt⟩
      exact (Finset.mem_filter.mp hmem).2
    · rw [hg_fix ν₂ h₂]
      have hnot : ν₂ ∉ Fset.filter (· < g ν₁) := by
        rw [hg_filter h₁]
        intro hc
        exact lt_asymm hlt (Finset.mem_filter.mp hc).2
      have hle : g ν₁ ≤ ν₂ := by
        by_contra hgt
        push Not at hgt
        exact hnot (Finset.mem_filter.mpr ⟨h₂, hgt⟩)
      exact lt_of_le_of_ne hle (fun heq => hg_notmem h₁ (heq ▸ h₂))
    · have hsub : Fset.filter (· < ν₁) ⊆ Fset.filter (· < ν₂) := fun p hp => by
        simp only [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, lt_trans hp.2 hlt⟩
      have hcle : (idx ν₁).1 ≤ (idx ν₂).1 := Finset.card_le_card hsub
      rcases eq_or_lt_of_le hcle with hceq | hclt
      · have hid : idx ν₁ = idx ν₂ := Fin.ext hceq
        simp only [g, dif_neg h₁, dif_neg h₂]
        have hsame : ∀ {k₁ k₂ : Fin (Fset.card + 1)}, k₁ = k₂ →
            ∀ (a : D k₁) (b : D k₂), a.1 < b.1 → (eD k₁ a).1 < (eD k₂ b).1 := by
          rintro k _ rfl a b h
          exact (eD k).map_rel_iff.mpr h
        exact hsame hid ⟨ν₁, h₁, rfl⟩ ⟨ν₂, h₂, rfl⟩ hlt
      · have hssub : Fset.filter (· < ν₁) ⊂ Fset.filter (· < ν₂) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => ne_of_lt hclt (congrArg Finset.card heq)⟩
        obtain ⟨p, hp₂, hp₁⟩ := Finset.exists_of_ssubset hssub
        have hpF : p ∈ Fset := (Finset.mem_filter.mp hp₂).1
        have hp_lt_g₂ : p < g ν₂ := by
          have : p ∈ Fset.filter (· < g ν₂) := (hg_filter h₂).symm ▸ hp₂
          exact (Finset.mem_filter.mp this).2
        have hg₁_lt_p : g ν₁ < p := by
          have hnot : p ∉ Fset.filter (· < g ν₁) := (hg_filter h₁).symm ▸ hp₁
          have hle : g ν₁ ≤ p := by
            by_contra hgt
            push Not at hgt
            exact hnot (Finset.mem_filter.mpr ⟨hpF, hgt⟩)
          exact lt_of_le_of_ne hle (fun heq => hg_notmem h₁ (heq ▸ hpF))
        exact lt_trans hg₁_lt_p hp_lt_g₂
  refine ⟨x₀, hx₀A, g, hg_mono, hg_fix, ?_⟩
  intro ν
  by_cases hν : ν ∈ Fset
  · rw [hg_fix ν hν]
    exact hF_good ν hν
  · simpa only [g, dif_neg hν] using (eD (idx ν) ⟨ν, hν, rfl⟩).2.2

/- ## Section 4: Corrigendum inductive construction and main theorem -/

private structure StepState (n : ℕ) (S : Set Host) where
  fam : (alpha n).ToType → Set Host
  hsub : ∀ ν, fam ν ⊆ S
  htype : ∀ ν, otype (fam ν) = alpha n
  hord : ∀ ν μ, ν < μ → ∀ x ∈ fam ν, ∀ y ∈ fam μ, x < y

private structure StepOut (n : ℕ) (S : Set Host) where
  next : StepState n S
  pt : Host
  emb : (alpha n).ToType → (alpha n).ToType

private noncomputable def makeStep (n : ℕ) (blue : SimpleGraph Host) (hfree : blue.CliqueFree 3)
    (S : Set Host)
    (hno : ∀ T : Set Host, T ⊆ S → blueᶜ.IsClique T → otype T ≠ alpha n)
    (γ : ℕ → (alpha n).ToType) (m : ℕ) (st : StepState n S) :
    { o : StepOut n S //
      o.pt ∈ st.fam (γ m) ∧
      StrictMono o.emb ∧
      (∀ ν ∈ (Finset.range (m + 1)).image γ, o.emb ν = ν) ∧
      (∀ ν, o.next.fam ν ⊆ K1 blue S o.pt) ∧
      (∀ ν, o.next.fam ν ⊆ st.fam (o.emb ν)) ∧
      (∀ y ∈ o.next.fam (γ m), o.pt < y) } := by
  let Fset : Finset (alpha n).ToType := (Finset.range (m + 1)).image γ
  have hcl := claim10 n blue hfree S hno Fset
    (st.hsub (γ m)) (st.htype (γ m)).ge st.fam st.hsub (fun ν => (st.htype ν).ge)
  let x₀ : Host := Classical.choose hcl
  have hx₀_spec := Classical.choose_spec hcl
  have hx₀_mem : x₀ ∈ st.fam (γ m) := hx₀_spec.1
  let g : (alpha n).ToType → (alpha n).ToType := Classical.choose hx₀_spec.2
  have hg_spec := Classical.choose_spec hx₀_spec.2
  have hg_mono : StrictMono g := hg_spec.1
  have hg_fix : ∀ ν ∈ Fset, g ν = ν := hg_spec.2.1
  have hg_good : ∀ ν, alpha n ≤ otype (K1 blue S x₀ ∩ st.fam (g ν)) := hg_spec.2.2
  have hgm_mem : γ m ∈ Fset := Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), rfl⟩
  have hgm_fix : g (γ m) = γ m := hg_fix (γ m) hgm_mem
  let fam' : (alpha n).ToType → Set Host := fun ν =>
    if ν = γ m then {y ∈ K1 blue S x₀ ∩ st.fam (γ m) | x₀ < y}
    else K1 blue S x₀ ∩ st.fam (g ν)
  have hfam'_subK : ∀ ν, fam' ν ⊆ K1 blue S x₀ := by
    intro ν y hy
    by_cases hν : ν = γ m
    · simp only [fam', if_pos hν] at hy; exact hy.1.1
    · simp only [fam', if_neg hν] at hy; exact hy.1
  have hfam'_subF : ∀ ν, fam' ν ⊆ st.fam (g ν) := by
    intro ν y hy
    by_cases hν : ν = γ m
    · simp only [fam', if_pos hν] at hy
      rw [hν, hgm_fix]
      exact hy.1.2
    · simp only [fam', if_neg hν] at hy
      exact hy.2
  have hfam'_subS : ∀ ν, fam' ν ⊆ S := fun ν y hy => (hfam'_subK ν hy).1
  have hfam'_type : ∀ ν, otype (fam' ν) = alpha n := by
    intro ν
    by_cases hν : ν = γ m
    · simp only [fam', if_pos hν]
      have hge : alpha n ≤ otype (K1 blue S x₀ ∩ st.fam (γ m)) := by
        simpa [hgm_fix] using hg_good (γ m)
      have hle : otype (K1 blue S x₀ ∩ st.fam (γ m)) ≤ alpha n :=
        (otype_mono inter_subset_right).trans_eq (st.htype (γ m))
      have heq : otype (K1 blue S x₀ ∩ st.fam (γ m)) = ω ^ eta n :=
        (le_antisymm hle hge).trans (alpha_eq_opow n)
      rw [alpha_eq_opow n]
      exact tail_gt_otype_eq (eta_ne_zero n) ((st.htype (γ m)).trans (alpha_eq_opow n))
        inter_subset_right heq hx₀_mem
    · simp only [fam', if_neg hν]
      have hle : otype (K1 blue S x₀ ∩ st.fam (g ν)) ≤ alpha n :=
        (otype_mono inter_subset_right).trans_eq (st.htype (g ν))
      exact le_antisymm hle (hg_good ν)
  have hfam'_ord : ∀ ν μ, ν < μ → ∀ x ∈ fam' ν, ∀ y ∈ fam' μ, x < y := by
    intro ν μ hlt x hx y hy
    exact st.hord (g ν) (g μ) (hg_mono hlt) x (hfam'_subF ν hx) y (hfam'_subF μ hy)
  have hfam'_gt : ∀ y ∈ fam' (γ m), x₀ < y := by
    intro y hy
    simp only [fam', if_pos rfl] at hy
    exact hy.2
  exact ⟨⟨⟨fam', hfam'_subS, hfam'_type, hfam'_ord⟩, x₀, g⟩,
    hx₀_mem, hg_mono, hg_fix, hfam'_subK, hfam'_subF, hfam'_gt⟩

private lemma initial_state (n : ℕ) (S : Set Host)
    (hS : ((ω ^ ω : Ordinal.{0}) ^ ((n + 1) * 2)) ≤ otype S) :
    Nonempty (StepState n S) := by
  have hprod :
      Ordinal.type (Prod.Lex ((· < ·) : (alpha n).ToType → (alpha n).ToType → Prop)
        ((· < ·) : (alpha n).ToType → (alpha n).ToType → Prop)) ≤ typeLT S := by
    rw [Ordinal.type_prod_lex, Ordinal.type_toType, alpha_mul_alpha]
    exact hS
  obtain ⟨e⟩ := Ordinal.type_le_iff'.mp hprod
  let fam : (alpha n).ToType → Set Host :=
    fun ν => (fun t : (alpha n).ToType => (e (ν, t)).1) '' Set.univ
  refine ⟨⟨fam, ?_, ?_, ?_⟩⟩
  · rintro ν _ ⟨t, -, rfl⟩
    exact (e (ν, t)).2
  · intro ν
    let iso : ((· < ·) : (alpha n).ToType → (alpha n).ToType → Prop) ≃r
        ((· < ·) : fam ν → fam ν → Prop) :=
      { toFun := fun t => ⟨(e (ν, t)).1, ⟨t, trivial, rfl⟩⟩
        invFun := fun y =>
          Classical.choose (by
            rcases y.2 with ⟨t, -, ht⟩
            exact ⟨t, ht⟩ : ∃ t : (alpha n).ToType, (e (ν, t)).1 = y.1)
        left_inv := fun t => by
          have hspec : (e (ν, Classical.choose
              (show ∃ s : (alpha n).ToType, (e (ν, s)).1 = (e (ν, t)).1 from ⟨t, rfl⟩))).1 =
              (e (ν, t)).1 :=
            Classical.choose_spec
              (show ∃ s : (alpha n).ToType, (e (ν, s)).1 = (e (ν, t)).1 from ⟨t, rfl⟩)
          have hinj := e.injective (Subtype.ext hspec)
          exact (Prod.mk.inj hinj).2
        right_inv := fun y => by
          apply Subtype.ext
          exact Classical.choose_spec (by
            rcases y.2 with ⟨t, -, ht⟩
            exact ⟨t, ht⟩ : ∃ t : (alpha n).ToType, (e (ν, t)).1 = y.1)
        map_rel_iff' := fun {t₁ t₂} => by
          change (e (ν, t₁)).1 < (e (ν, t₂)).1 ↔ t₁ < t₂
          rw [show (e (ν, t₁)).1 < (e (ν, t₂)).1 ↔ e (ν, t₁) < e (ν, t₂) from Iff.rfl,
            e.map_rel_iff]
          exact ⟨fun h => by
            cases h with
            | left _ _ hlt => exact (lt_irrefl _ hlt).elim
            | right _ ht => exact ht,
            fun ht => Prod.Lex.right ν ht⟩ }
    rw [otype, ← Ordinal.type_toType (alpha n)]
    exact (Ordinal.type_eq.mpr ⟨iso⟩).symm
  · rintro ν μ hlt _ ⟨t₁, -, rfl⟩ _ ⟨t₂, -, rfl⟩
    exact e.map_rel_iff.mpr (Prod.Lex.left t₁ t₂ hlt)

private lemma erdos_milner_step (n : ℕ) (blue : SimpleGraph Host) (hfree : blue.CliqueFree 3)
    (S : Set Host) (hS : ((ω ^ ω : Ordinal.{0}) ^ ((n + 1) * 2)) ≤ otype S) :
    ∃ T : Set Host, T ⊆ S ∧ blueᶜ.IsClique T ∧ otype T = alpha n := by
  by_contra hno
  push Not at hno
  have hno' : ∀ T : Set Host, T ⊆ S → blueᶜ.IsClique T → otype T ≠ alpha n := hno
  have : Countable (alpha n).ToType := alpha_countable n
  have : Nonempty (alpha n).ToType := alpha_nonempty n
  obtain ⟨f, hf_surj⟩ := exists_surjective_nat (alpha n).ToType
  let γ : ℕ → (alpha n).ToType := fun m => f (Nat.unpair m).1
  have hγ_inf : ∀ (ν : (alpha n).ToType) (N : ℕ), ∃ m ≥ N, γ m = ν := by
    intro ν N
    obtain ⟨a, ha⟩ := hf_surj ν
    refine ⟨Nat.pair a N, Nat.right_le_pair a N, ?_⟩
    simp only [γ, Nat.unpair_pair, ha]
  obtain ⟨st0⟩ := initial_state n S hS
  let seq : ℕ → StepState n S :=
    Nat.rec st0 (fun m st => (makeStep n blue hfree S hno' γ m st).1.next)
  let x : ℕ → Host := fun m => (makeStep n blue hfree S hno' γ m (seq m)).1.pt
  let g : ℕ → (alpha n).ToType → (alpha n).ToType :=
    fun m => (makeStep n blue hfree S hno' γ m (seq m)).1.emb
  have hx_mem : ∀ m, x m ∈ (seq m).fam (γ m) :=
    fun m => (makeStep n blue hfree S hno' γ m (seq m)).2.1
  have hg_mono : ∀ m, StrictMono (g m) :=
    fun m => (makeStep n blue hfree S hno' γ m (seq m)).2.2.1
  have hg_fix : ∀ m ν, ν ∈ (Finset.range (m + 1)).image γ → g m ν = ν :=
    fun m => (makeStep n blue hfree S hno' γ m (seq m)).2.2.2.1
  have hnext_subK : ∀ m ν, (seq (m + 1)).fam ν ⊆ K1 blue S (x m) :=
    fun m => (makeStep n blue hfree S hno' γ m (seq m)).2.2.2.2.1
  have hnext_subF : ∀ m ν, (seq (m + 1)).fam ν ⊆ (seq m).fam (g m ν) :=
    fun m => (makeStep n blue hfree S hno' γ m (seq m)).2.2.2.2.2.1
  have hnext_gt : ∀ m y, y ∈ (seq (m + 1)).fam (γ m) → x m < y :=
    fun m => (makeStep n blue hfree S hno' γ m (seq m)).2.2.2.2.2.2
  have hg_fix_le : ∀ {j k : ℕ}, j ≤ k → g k (γ j) = γ j := by
    intro j k hjk
    exact hg_fix k (γ j) (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjk), rfl⟩)
  have hsubK : ∀ j d ν, (seq (j + 1 + d)).fam ν ⊆ K1 blue S (x j) := by
    intro j d
    induction d with
    | zero => exact hnext_subK j
    | succ d ih =>
      intro ν
      exact (hnext_subF (j + 1 + d) ν).trans (ih (g (j + 1 + d) ν))
  have hleft : ∀ j d ν, ν < γ j → ∃ η < γ j, (seq (j + d)).fam ν ⊆ (seq j).fam η := by
    intro j d
    induction d with
    | zero =>
      intro ν hν
      exact ⟨ν, hν, Subset.rfl⟩
    | succ d ih =>
      intro ν hν
      have hgn : g (j + d) ν < γ j := by
        rw [← hg_fix_le (Nat.le_add_right j d)]
        exact hg_mono (j + d) hν
      obtain ⟨η, hη, hsub⟩ := ih (g (j + d) ν) hgn
      exact ⟨η, hη, (hnext_subF (j + d) ν).trans hsub⟩
  have hright : ∀ j d ν, γ j < ν → ∃ η, γ j < η ∧ (seq (j + d)).fam ν ⊆ (seq j).fam η := by
    intro j d
    induction d with
    | zero =>
      intro ν hν
      exact ⟨ν, hν, Subset.rfl⟩
    | succ d ih =>
      intro ν hν
      have hgn : γ j < g (j + d) ν := by
        rw [← hg_fix_le (Nat.le_add_right j d)]
        exact hg_mono (j + d) hν
      obtain ⟨η, hη, hsub⟩ := ih (g (j + d) ν) hgn
      exact ⟨η, hη, (hnext_subF (j + d) ν).trans hsub⟩
  have hsame : ∀ j d, (seq (j + 1 + d)).fam (γ j) ⊆ (seq (j + 1)).fam (γ j) := by
    intro j d
    induction d with
    | zero => exact Subset.rfl
    | succ d ih =>
      have hfix : g (j + 1 + d) (γ j) = γ j := hg_fix_le (by omega)
      have h1 : (seq (j + 1 + d + 1)).fam (γ j) ⊆ (seq (j + 1 + d)).fam (γ j) := by
        simpa [hfix] using hnext_subF (j + 1 + d) (γ j)
      exact h1.trans ih
  have hx_lt_of_γ_lt : ∀ j m, γ j < γ m → x j < x m := by
    intro j m hγlt
    rcases lt_trichotomy j m with hjm | rfl | hmj
    · obtain ⟨d, rfl⟩ : ∃ d, m = j + d := ⟨m - j, (Nat.add_sub_cancel' hjm.le).symm⟩
      obtain ⟨η, hη, hsub⟩ := hright j d (γ (j + d)) hγlt
      exact (seq j).hord (γ j) η hη (x j) (hx_mem j) (x (j + d)) (hsub (hx_mem (j + d)))
    · exact (lt_irrefl _ hγlt).elim
    · obtain ⟨d, rfl⟩ : ∃ d, j = m + d := ⟨j - m, (Nat.add_sub_cancel' hmj.le).symm⟩
      obtain ⟨η, hη, hsub⟩ := hleft m d (γ (m + d)) hγlt
      exact (seq m).hord η (γ m) hη (x (m + d)) (hsub (hx_mem (m + d))) (x m) (hx_mem m)
  have hx_lt_of_γ_eq : ∀ j m, γ j = γ m → j < m → x j < x m := by
    intro j m hγeq hjm
    obtain ⟨d, rfl⟩ : ∃ d, m = j + 1 + d := ⟨m - (j + 1), by omega⟩
    have hmem : x (j + 1 + d) ∈ (seq (j + 1)).fam (γ j) :=
      hsame j d (hγeq ▸ hx_mem (j + 1 + d))
    exact hnext_gt j (x (j + 1 + d)) hmem
  let Z : Set Host := Set.range x
  have hZ_sub : Z ⊆ S := by
    rintro _ ⟨m, rfl⟩
    exact (seq m).hsub (γ m) (hx_mem m)
  have hZ_clique : blueᶜ.IsClique Z := by
    rintro _ ⟨j, rfl⟩ _ ⟨m, rfl⟩ hne
    rcases lt_trichotomy j m with hjm | rfl | hmj
    · obtain ⟨d, rfl⟩ : ∃ d, m = j + 1 + d := ⟨m - (j + 1), by omega⟩
      have hK : x (j + 1 + d) ∈ K1 blue S (x j) := hsubK j d (γ (j + 1 + d)) (hx_mem (j + 1 + d))
      exact (blue.compl_adj _ _).mpr ⟨hne, hK.2.2⟩
    · exact (hne rfl).elim
    · obtain ⟨d, rfl⟩ : ∃ d, j = m + 1 + d := ⟨j - (m + 1), by omega⟩
      have hK : x (m + 1 + d) ∈ K1 blue S (x m) := hsubK m d (γ (m + 1 + d)) (hx_mem (m + 1 + d))
      exact (blue.compl_adj _ _).mpr ⟨hne, fun h => hK.2.2 h.symm⟩
  let idx : (alpha n).ToType → ℕ → ℕ := fun ν =>
    Nat.rec (Classical.choose (hγ_inf ν 0))
      (fun _ prev => Classical.choose (hγ_inf ν (prev + 1)))
  have hidx_γ : ∀ ν r, γ (idx ν r) = ν := by
    intro ν r
    cases r with
    | zero => exact (Classical.choose_spec (hγ_inf ν 0)).2
    | succ r => exact (Classical.choose_spec (hγ_inf ν (idx ν r + 1))).2
  have hidx_step : ∀ ν r, idx ν r < idx ν (r + 1) := by
    intro ν r
    have hge : idx ν r + 1 ≤ idx ν (r + 1) :=
      (Classical.choose_spec (hγ_inf ν (idx ν r + 1))).1
    omega
  have hidx_mono : ∀ ν, StrictMono (idx ν) :=
    fun ν => strictMono_nat_of_lt_succ (hidx_step ν)
  let embFun : (alpha n).ToType × ℕ → Z := fun p => ⟨x (idx p.1 p.2), idx p.1 p.2, rfl⟩
  have hemb : ∀ p q : (alpha n).ToType × ℕ,
      Prod.Lex (· < ·) (· < ·) p q → embFun p < embFun q := by
    intro ⟨ν₁, r₁⟩ ⟨ν₂, r₂⟩ hlex
    cases hlex with
    | left _ _ hν =>
      exact hx_lt_of_γ_lt (idx ν₁ r₁) (idx ν₂ r₂) (by rw [hidx_γ, hidx_γ]; exact hν)
    | right _ hr =>
      exact hx_lt_of_γ_eq (idx ν₁ r₁) (idx ν₁ r₂) (by rw [hidx_γ, hidx_γ]) (hidx_mono ν₁ hr)
  have hleZ := (relEmbedding_of_prod_lex embFun hemb).ordinal_type_le
  rw [Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_nat_lt, omega_mul_alpha] at hleZ
  obtain ⟨T, hTZ, hTtype⟩ := exists_subset_otype_eq hleZ
  exact hno' T (hTZ.trans hZ_sub) (fun _ hu _ hv huv => hZ_clique (hTZ hu) (hTZ hv) huv) hTtype

end Erdos591R1H1

theorem OMA.solution : OMA.R_Erdos591_erdos_591_R1.H1 := by
  intro n blue hfree S hS
  exact Erdos591R1H1.erdos_milner_step n blue hfree S hS
