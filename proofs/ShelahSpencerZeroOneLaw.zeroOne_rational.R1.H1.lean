import OMAReductions.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
/-! Proof of ShelahSpencerZeroOneLaw.zeroOne_rational.R1.H1. -/
namespace ShelahSpencerH1
section
open scoped BigOperators
open Finset Real Nat MeasureTheory ProbabilityTheory unitInterval
abbrev z6 (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}
def z7 {n : ℕ} (u v : Fin n) (h : u ≠ v) : z6 n :=
  ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using h⟩
lemma z0u {n : ℕ} {u v : Fin n} (h : u ≠ v) :
    z7 u v h = z7 v u h.symm :=
  Subtype.ext Sym2.eq_swap
lemma ya {n : ℕ} {u₁ v₁ u₂ v₂ : Fin n} (h₁ : u₁ ≠ v₁) (h₂ : u₂ ≠ v₂) :
    z7 u₁ v₁ h₁ = z7 u₂ v₂ h₂ ↔ (u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂) := by
  simp [z7, Subtype.ext_iff]
lemma z2b (n : ℕ) : Fintype.card (z6 n) = n.choose 2 := by
  have heq : Fintype.card (z6 n) = Fintype.card ↑(Sym2.diagSet (α := Fin n))ᶜ :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [heq, Sym2.card_diagSet_compl, Fintype.card_fin]
noncomputable def wn {n : ℕ} (G : SimpleGraph (Fin n)) : z6 n → Bool :=
  fun e => by classical exact decide (e.1 ∈ G.edgeSet)
def z1 {n : ℕ} (f : z6 n → Bool) : SimpleGraph (Fin n) where
  Adj u v := ∃ h : u ≠ v, f (z7 u v h) = true
  symm := ⟨fun _ _ ⟨h, hf⟩ => ⟨h.symm, by rw [← z0u h]; exact hf⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩
lemma za {n : ℕ} (f : z6 n → Bool) {u v : Fin n} (h : u ≠ v) :
    (z1 f).Adj u v ↔ f (z7 u v h) = true := by
  constructor
  · rintro ⟨_, hf⟩; exact hf
  · intro hf; exact ⟨h, hf⟩
lemma z0k {n : ℕ} (f : z6 n → Bool) :
    wn (z1 f) = f := by
  classical
  funext ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
    simp only [wn, SimpleGraph.mem_edgeSet, za f huv, Bool.decide_eq_true]
    rfl
lemma wj {n : ℕ} (G : SimpleGraph (Fin n)) :
    z1 (wn G) = G := by
  classical
  ext u v
  by_cases huv : u = v
  · subst huv; simp [z1]
  · simp [za _ huv, wn, z7]
noncomputable def z10 (n : ℕ) : SimpleGraph (Fin n) ≃ (z6 n → Bool) where
  toFun := wn
  invFun := z1
  left_inv := wj
  right_inv := z0k
noncomputable def z9 (p : ℝ) (b : Bool) : ℝ :=
  if b then p else 1 - p
lemma yh {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ z9 p b := by
  cases b <;> simp [z9] <;> linarith
lemma z2d (p : ℝ) : ∑ b : Bool, z9 p b = 1 := by
  simp [z9]
lemma y4 {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) :
    (∑ f : ι → Bool, ∏ i : ι, z9 p (f i)) = 1 := by
  have h := Fintype.prod_sum (fun (_ : ι) (b : Bool) => z9 p b)
  rw [← h]
  simp only [z2d, prod_const_one]
noncomputable def z4 {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ)
    (P : (ι → Bool) → Prop) : ℝ := by
  classical
  exact ∑ f : ι → Bool, if P f then ∏ i : ι, z9 p (f i) else 0
lemma zx {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) {P Q : (ι → Bool) → Prop}
    (h : ∀ f, P f ↔ Q f) : z4 p P = z4 p Q := by
  classical
  unfold z4
  refine sum_congr rfl fun f _ => ?_
  by_cases hp : P f
  · rw [if_pos hp, if_pos ((h f).mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp ((h f).mpr hq))]
lemma ym {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (ι → Bool) → Prop) : 0 ≤ z4 p P := by
  classical
  unfold z4
  refine sum_nonneg fun f _ => ?_
  split_ifs
  · exact prod_nonneg fun _ _ => yh hp0 hp1 _
  · exact le_rfl
lemma z0b {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) :
    z4 p (fun _ : ι → Bool => True) = 1 := by
  classical
  unfold z4
  simp only [↓reduceIte]
  exact y4 p
lemma z1y {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) :
    z4 p (fun _ : ι → Bool => False) = 0 := by
  classical
  simp [z4]
lemma zi {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q : (ι → Bool) → Prop} (hPQ : ∀ f, P f → Q f) :
    z4 p P ≤ z4 p Q := by
  classical
  unfold z4
  refine sum_le_sum fun f _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (hPQ f h1) h2
  · exact prod_nonneg fun _ _ => yh hp0 hp1 _
  · exact le_rfl
lemma wg {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (P : (ι → Bool) → Prop) :
    z4 p (fun f => ¬ P f) = 1 - z4 p P := by
  classical
  have hsum : z4 p P + z4 p (fun f => ¬ P f) = 1 := by
    unfold z4
    rw [← sum_add_distrib]
    have hpt : ∀ f : ι → Bool,
        (if P f then ∏ i : ι, z9 p (f i) else 0) +
        (if ¬ P f then ∏ i : ι, z9 p (f i) else 0) =
        ∏ i : ι, z9 p (f i) := by
      intro f
      by_cases h : P f
      · rw [if_pos h, if_neg (not_not.mpr h), add_zero]
      · rw [if_neg h, if_pos h, zero_add]
    convert (sum_congr rfl fun f _ => hpt f).trans (y4 p)
  linarith
lemma yr {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q : (ι → Bool) → Prop) :
    z4 p (fun f => P f ∨ Q f) ≤ z4 p P + z4 p Q := by
  classical
  unfold z4
  rw [← sum_add_distrib]
  refine sum_le_sum fun f _ => ?_
  have hw : 0 ≤ ∏ i : ι, z9 p (f i) := prod_nonneg fun _ _ => yh hp0 hp1 _
  by_cases hP : P f <;> by_cases hQ : Q f
  · simp only [hP, hQ, or_self, ↓reduceIte]; linarith
  · simp only [hP, hQ, or_false, ↓reduceIte, add_zero, le_rfl]
  · simp only [hP, hQ, false_or, ↓reduceIte, zero_add, le_rfl]
  · simp only [hP, hQ, or_self, ↓reduceIte, add_zero, le_rfl]
lemma y3 {ι κ : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Finset κ) (P : κ → (ι → Bool) → Prop) :
    z4 p (fun f => ∃ k ∈ s, P k f) ≤ ∑ k ∈ s, z4 p (P k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [z4]
  | insert a t hat ih =>
    have heq : z4 p (fun f => ∃ k ∈ insert a t, P k f) =
        z4 p (fun f => P a f ∨ ∃ k ∈ t, P k f) :=
      zx p fun f => by simp
    rw [heq, sum_insert hat]
    linarith [yr hp0 hp1 (P a) (fun f => ∃ k ∈ t, P k f), ih]
noncomputable def gProb (n : ℕ) (p : ℝ) (E : Set (SimpleGraph (Fin n))) : ℝ :=
  z4 p (fun f : z6 n → Bool => z1 f ∈ E)
lemma gProb_mono {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {A B : Set (SimpleGraph (Fin n))} (hAB : A ⊆ B) :
    gProb n p A ≤ gProb n p B :=
  zi hp0 hp1 fun _ h => hAB h
lemma z1g {n : ℕ} (p : ℝ) (E : Set (SimpleGraph (Fin n))) :
    gProb n p Eᶜ = 1 - gProb n p E :=
  wg p _
lemma yg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Set (SimpleGraph (Fin n))) :
    gProb n p (A ∪ B) ≤ gProb n p A + gProb n p B :=
  yr hp0 hp1 _ _
lemma yd {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {κ : Type*} (s : Finset κ) (A : κ → Set (SimpleGraph (Fin n))) :
    gProb n p (⋃ k ∈ s, A k) ≤ ∑ k ∈ s, gProb n p (A k) := by
  have heq : gProb n p (⋃ k ∈ s, A k) =
      z4 p (fun f : z6 n → Bool => ∃ k ∈ s, z1 f ∈ A k) :=
    zx p fun f => by simp
  rw [heq]
  exact y3 hp0 hp1 s (fun k f => z1 f ∈ A k)
lemma wy (n : ℕ) (p : unitInterval)
    (E : Set (SimpleGraph (Fin n))) :
    SimpleGraph.binomialRandom (Fin n) p E = ENNReal.ofReal (gProb n (p : ℝ) E) := by
  classical
  let μ := SimpleGraph.binomialRandom (Fin n) p
  have v0 : ∀ G : SimpleGraph (Fin n), MeasurableSet ({G} : Set (SimpleGraph (Fin n))) :=
    fun G => OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1.measurableSet_simpleGraph {G}
  have v6 : μ E = ∑ G : SimpleGraph (Fin n), if G ∈ E then μ {G} else 0 := by
    have v9 : E = ⋃ G ∈ (univ.filter (fun G : SimpleGraph (Fin n) => G ∈ E)), ({G} : Set _) := by
      ext G; simp
    conv_lhs => rw [v9]
    rw [MeasureTheory.measure_biUnion_finset
      (fun G₁ _ G₂ _ hne => Set.disjoint_singleton.mpr hne)
      (fun G _ => v0 G), sum_filter]
  have v1 : ∀ f : z6 n → Bool,
      μ {z1 f} = ENNReal.ofReal (∏ i : z6 n, z9 (p : ℝ) (f i)) := by
    intro f
    rw [SimpleGraph.binomialRandom_singleton]
    set G := z1 f
    let T := univ.filter (fun e : z6 n => f e = true)
    have v4 : G.edgeSet.ncard = T.card := by
      have hbij : G.edgeSet = Subtype.val '' (T : Set (z6 n)) := by
        ext e
        simp only [Set.mem_image, mem_coe, T, mem_filter, mem_univ, true_and]
        constructor
        · intro he
          have hnd : ¬ e.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet G he
          refine ⟨⟨e, hnd⟩, ?_, rfl⟩
          induction e using Sym2.ind with
          | _ u v =>
            have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using hnd
            exact (za f huv).mp he
        · rintro ⟨⟨e', hnd⟩, hf, rfl⟩
          induction e' using Sym2.ind with
          | _ u v =>
            have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using hnd
            exact (za f huv).mpr hf
      rw [hbij, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
    have v8 : (Nat.card (Fin n)).choose 2 - G.edgeSet.ncard = (univ \ T).card := by
      rw [v4, Nat.card_eq_fintype_card, Fintype.card_fin, ← z2b n,
        ← Finset.card_univ, card_sdiff, inter_univ]
    have v3 : (∏ i : z6 n, z9 (p : ℝ) (f i)) =
        (p : ℝ) ^ T.card * (1 - (p : ℝ)) ^ (univ \ T).card := by
      have v5 : (univ : Finset (z6 n)) = T ∪ (univ \ T) :=
        (union_sdiff_of_subset (subset_univ T)).symm
      conv_lhs => rw [v5]
      rw [prod_union disjoint_sdiff]
      congr 1
      · rw [prod_congr rfl (g := fun _ => (p : ℝ)) (fun e he => by
          have := (mem_filter.mp he).2; simp [z9, this]), prod_const]
      · rw [prod_congr rfl (g := fun _ => 1 - (p : ℝ)) (fun e he => by
          have hnot : f e ≠ true := by
            intro h; exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
          have v7 : f e = false := Bool.eq_false_iff.mpr hnot
          simp [z9, v7]), prod_const]
    rw [v8, v4, v3, ENNReal.ofReal_mul (pow_nonneg p.2.1 _),
      ENNReal.ofReal_pow p.2.1, ENNReal.ofReal_pow (sub_nonneg.mpr p.2.2)]
    congr 1
    · congr 1; exact (ENNReal.ofReal_eq_coe_nnreal p.2.1).symm
    · congr 1
      have hσ : ((σ p : unitInterval) : ℝ) = 1 - (p : ℝ) := rfl
      rw [← hσ]
      exact (ENNReal.ofReal_eq_coe_nnreal (σ p).2.1).symm
  rw [v6]
  have v2 : (∑ G : SimpleGraph (Fin n), if G ∈ E then μ {G} else 0) =
      ∑ f : z6 n → Bool, if z1 f ∈ E then μ {z1 f} else 0 :=
    Fintype.sum_equiv (z10 n) _ _ (fun G => by
      simp [z10, wj])
  rw [v2]
  simp_rw [v1]
  rw [gProb, z4, ENNReal.ofReal_sum_of_nonneg (fun f _ => by
    split_ifs
    · exact prod_nonneg fun _ _ => yh p.2.1 p.2.2 _
    · exact le_rfl)]
  refine sum_congr rfl fun f _ => ?_
  split_ifs <;> simp
lemma sparseRandomGraph_ge_of_gProb {n : ℕ} {α : ℝ} (hα : 0 < α)
    {E : Set (SimpleGraph (Fin n))} {r : ℝ} (hr : r ≤ gProb n ((n : ℝ) ^ (-α)) E) :
    ENNReal.ofReal r ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα E := by
  rw [ShelahSpencerZeroOneLaw.sparseRandomGraph, wy]
  exact ENNReal.ofReal_le_ofReal hr
def z0 {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f₁ : {i // i ∈ S} → Bool) (f₂ : {i // i ∉ S} → Bool) : ι → Bool :=
  fun i => if h : i ∈ S then f₁ ⟨i, h⟩ else f₂ ⟨i, h⟩
def zw {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (ι → Bool) ≃ ({i // i ∈ S} → Bool) × ({i // i ∉ S} → Bool) where
  toFun f := (fun x => f x.1, fun x => f x.1)
  invFun p := z0 S p.1 p.2
  left_inv f := by funext i; simp only [z0]; split_ifs <;> rfl
  right_inv := by
    rintro ⟨f₁, f₂⟩
    ext ⟨i, hi⟩ <;> simp [z0, hi]
lemma y7 {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (p : ℝ)
    (f₁ : {i // i ∈ S} → Bool) (f₂ : {i // i ∉ S} → Bool) :
    (∏ i : ι, z9 p (z0 S f₁ f₂ i)) =
      (∏ x : {i // i ∈ S}, z9 p (f₁ x)) * (∏ x : {i // i ∉ S}, z9 p (f₂ x)) := by
  have v0 : (univ : Finset ι) = S ∪ Sᶜ := (union_compl S).symm
  conv_lhs => rw [v0]
  rw [prod_union disjoint_compl_right]
  congr 1
  · rw [← prod_coe_sort S]
    refine prod_congr rfl fun x _ => by simp [z0, x.2]
  · rw [← prod_coe_sort Sᶜ]
    refine prod_bij (fun x _ => ⟨x.1, mem_compl.mp x.2⟩)
      (fun _ _ => mem_univ _)
      (fun a _ b _ h => Subtype.ext (by simpa using congrArg Subtype.val h))
      (fun y _ => ⟨⟨y.1, mem_compl.mpr y.2⟩, mem_univ _, rfl⟩)
      (fun x _ => by
        have hx : x.1 ∉ S := mem_compl.mp x.2
        simp [z0, hx])
lemma wk {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset ι) (A B : (ι → Bool) → Prop)
    (hA_dep : ∀ f₁ f₂ f₂', A (z0 S f₁ f₂) ↔ A (z0 S f₁ f₂'))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcond : ∀ f₁ : {i // i ∈ S} → Bool,
      (∀ f₂, A (z0 S f₁ f₂)) →
      z4 p (fun f₂ : {i // i ∉ S} → Bool => B (z0 S f₁ f₂)) ≤ ε) :
    z4 p (fun f => A f ∧ B f) ≤ ε := by
  classical
  unfold z4
  rw [← Equiv.sum_comp (zw S).symm]
  simp only [zw, Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
  have v1 : ∀ f₁ : {i // i ∈ S} → Bool,
      (∑ f₂ : {i // i ∉ S} → Bool,
        if A (z0 S f₁ f₂) ∧ B (z0 S f₁ f₂) then
          ∏ i : ι, z9 p (z0 S f₁ f₂ i)
        else 0) ≤
      (∏ x : {i // i ∈ S}, z9 p (f₁ x)) * ε := by
    intro f₁
    have hw1 : 0 ≤ ∏ x : {i // i ∈ S}, z9 p (f₁ x) :=
      prod_nonneg fun x _ => yh hp0 hp1 _
    by_cases hA : ∀ f₂, A (z0 S f₁ f₂)
    · have hrew : ∀ f₂ : {i // i ∉ S} → Bool,
          (if A (z0 S f₁ f₂) ∧ B (z0 S f₁ f₂) then
            ∏ i : ι, z9 p (z0 S f₁ f₂ i) else 0) =
          (∏ x : {i // i ∈ S}, z9 p (f₁ x)) *
            (if B (z0 S f₁ f₂) then
              ∏ x : {i // i ∉ S}, z9 p (f₂ x) else 0) := by
        intro f₂
        rw [y7]
        by_cases hB : B (z0 S f₁ f₂) <;> simp [hA f₂, hB]
      simp_rw [hrew, ← mul_sum]
      have hc := hcond f₁ hA
      unfold z4 at hc
      exact mul_le_mul_of_nonneg_left (by convert hc) hw1
    · push Not at hA
      obtain ⟨f₂₀, hf₂₀⟩ := hA
      have v0 : ∀ f₂ : {i // i ∉ S} → Bool,
          (if A (z0 S f₁ f₂) ∧ B (z0 S f₁ f₂) then
            ∏ i : ι, z9 p (z0 S f₁ f₂ i) else 0) = 0 := by
        intro f₂
        have v2 : ¬ A (z0 S f₁ f₂) := fun h =>
          hf₂₀ ((hA_dep f₁ f₂ f₂₀).mp h)
        simp [v2]
      simp_rw [v0, sum_const_zero]
      exact mul_nonneg hw1 hε
  calc (∑ f₁ : {i // i ∈ S} → Bool, ∑ f₂ : {i // i ∉ S} → Bool,
          if A (z0 S f₁ f₂) ∧ B (z0 S f₁ f₂) then
            ∏ i : ι, z9 p (z0 S f₁ f₂ i) else 0)
      ≤ ∑ f₁ : {i // i ∈ S} → Bool, (∏ x : {i // i ∈ S}, z9 p (f₁ x)) * ε :=
        sum_le_sum fun f₁ _ => v1 f₁
    _ = (∑ f₁ : {i // i ∈ S} → Bool, ∏ x : {i // i ∈ S}, z9 p (f₁ x)) * ε :=
        (sum_mul _ _ _).symm
    _ = 1 * ε := by rw [y4]
    _ = ε := one_mul ε
lemma w4 {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (z6 n))
    (A B : Set (SimpleGraph (Fin n)))
    (hA_dep : ∀ f₁ f₂ f₂', z1 (z0 S f₁ f₂) ∈ A ↔ z1 (z0 S f₁ f₂') ∈ A)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcond : ∀ f₁ : {e // e ∈ S} → Bool,
      (∀ f₂, z1 (z0 S f₁ f₂) ∈ A) →
      z4 p (fun f₂ : {e // e ∉ S} → Bool => z1 (z0 S f₁ f₂) ∈ B) ≤ ε) :
    gProb n p (A ∩ B) ≤ ε :=
  wk hp0 hp1 S (fun f => z1 f ∈ A) (fun f => z1 f ∈ B)
    hA_dep ε hε hcond
lemma w2 {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι) (p : ℝ)
    (P : (ι → Bool) → Prop)
    (hdep : ∀ f g : ι → Bool, (∀ i ∈ T, f i = g i) → (P f ↔ P g)) :
    z4 p P =
      z4 p (fun f₁ : {i // i ∈ T} → Bool => P (z0 T f₁ (fun _ => false))) := by
  classical
  unfold z4
  rw [← Equiv.sum_comp (zw T).symm]
  simp only [zw, Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
  refine sum_congr rfl fun f₁ _ => ?_
  have hP : ∀ f₂ : {i // i ∉ T} → Bool,
      P (z0 T f₁ f₂) ↔ P (z0 T f₁ (fun _ => false)) := fun f₂ =>
    hdep _ _ (fun i hi => by simp [z0, hi])
  have hrew : ∀ f₂ : {i // i ∉ T} → Bool,
      (if P (z0 T f₁ f₂) then ∏ i : ι, z9 p (z0 T f₁ f₂ i) else 0) =
      (if P (z0 T f₁ (fun _ => false)) then ∏ x : {i // i ∈ T}, z9 p (f₁ x) else 0) *
        ∏ x : {i // i ∉ T}, z9 p (f₂ x) := by
    intro f₂
    rw [y7]
    by_cases h0 : P (z0 T f₁ (fun _ => false))
    · rw [if_pos ((hP f₂).mpr h0), if_pos h0]
    · rw [if_neg (fun h => h0 ((hP f₂).mp h)), if_neg h0, zero_mul]
  simp_rw [hrew, ← mul_sum]
  rw [y4, mul_one]
lemma y5 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (idx : Finset κ) (T : κ → Finset ι)
    (hdisj : Set.PairwiseDisjoint (idx : Set κ) T) (p : ℝ)
    (P : κ → (ι → Bool) → Prop)
    (hdep : ∀ k ∈ idx, ∀ f g : ι → Bool, (∀ i ∈ T k, f i = g i) → (P k f ↔ P k g)) :
    z4 p (fun f => ∀ k ∈ idx, P k f) = ∏ k ∈ idx, z4 p (P k) := by
  classical
  induction idx using Finset.induction_on with
  | empty =>
    simp only [notMem_empty, IsEmpty.forall_iff, implies_true, prod_empty]
    exact z0b p
  | insert a s has ih =>
    have v2 : Set.PairwiseDisjoint (s : Set κ) T :=
      hdisj.subset (subset_insert a s)
    have v0 : Disjoint (T a) (s.biUnion T) := by
      rw [disjoint_biUnion_right]
      intro k hk
      exact hdisj (mem_insert_self a s) (mem_insert_of_mem hk) (fun h => has (h ▸ hk))
    have v1 : ∀ k ∈ s, ∀ f g : ι → Bool, (∀ i ∈ T k, f i = g i) → (P k f ↔ P k g) :=
      fun k hk => hdep k (mem_insert_of_mem hk)
    rw [prod_insert has, ← ih v2 v1]
    unfold z4
    rw [← Equiv.sum_comp (zw (T a)).symm]
    simp only [zw, Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
    have hPa : ∀ f₁ f₂, P a (z0 (T a) f₁ f₂) ↔ P a (z0 (T a) f₁ (fun _ => false)) :=
      fun f₁ f₂ => hdep a (mem_insert_self a s) _ _ (fun i hi => by simp [z0, hi])
    have hPs : ∀ f₁ f₂, (∀ k ∈ s, P k (z0 (T a) f₁ f₂)) ↔
        (∀ k ∈ s, P k (z0 (T a) (fun _ => false) f₂)) := fun f₁ f₂ => by
      refine forall₂_congr fun k hk => v1 k hk _ _ fun i hi => ?_
      have hnot : i ∉ T a := disjoint_right.mp v0 (mem_biUnion.mpr ⟨k, hk, hi⟩)
      simp [z0, hnot]
    have hrew : ∀ f₁ f₂,
        (if ∀ k ∈ insert a s, P k (z0 (T a) f₁ f₂) then
          ∏ i : ι, z9 p (z0 (T a) f₁ f₂ i) else 0) =
        (if P a (z0 (T a) f₁ (fun _ => false)) then
          ∏ x : {i // i ∈ T a}, z9 p (f₁ x) else 0) *
        (if ∀ k ∈ s, P k (z0 (T a) (fun _ => false) f₂) then
          ∏ x : {i // i ∉ T a}, z9 p (f₂ x) else 0) := by
      intro f₁ f₂
      rw [y7]
      have hiff : (∀ k ∈ insert a s, P k (z0 (T a) f₁ f₂)) ↔
          P a (z0 (T a) f₁ (fun _ => false)) ∧
          ∀ k ∈ s, P k (z0 (T a) (fun _ => false) f₂) := by
        simp only [mem_insert, forall_eq_or_imp, hPa, hPs]
      by_cases h1 : P a (z0 (T a) f₁ (fun _ => false)) <;>
        by_cases h2 : ∀ k ∈ s, P k (z0 (T a) (fun _ => false) f₂)
      · rw [if_pos (hiff.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2]
      · rw [if_neg (fun h => h2 (hiff.mp h).2), if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg (fun h => h1 (hiff.mp h).1), if_neg h1, zero_mul]
      · rw [if_neg (fun h => h1 (hiff.mp h).1), if_neg h1, zero_mul]
    simp_rw [hrew, ← mul_sum, ← sum_mul]
    congr 1
    · have h1 := w2 (T a) p (P a) (hdep a (mem_insert_self a s))
      unfold z4 at h1
      convert h1.symm
    · have hRHS := w2 (T a)ᶜ p (fun f => ∀ k ∈ s, P k f) (fun f g hfg => by
        refine forall₂_congr fun k hk => v1 k hk _ _ fun i hi => ?_
        exact hfg i (mem_compl.mpr (disjoint_right.mp v0
          (mem_biUnion.mpr ⟨k, hk, hi⟩))))
      unfold z4 at hRHS
      have hbij : (∑ f₂ : {i // i ∉ T a} → Bool,
            if ∀ k ∈ s, P k (z0 (T a) (fun _ => false) f₂) then
              ∏ x : {i // i ∉ T a}, z9 p (f₂ x) else 0) =
          ∑ f₁ : {i // i ∈ (T a)ᶜ} → Bool,
            if ∀ k ∈ s, P k (z0 (T a)ᶜ f₁ (fun _ => false)) then
              ∏ x : {i // i ∈ (T a)ᶜ}, z9 p (f₁ x) else 0 := by
        refine sum_bij (fun f₂ _ => fun x => f₂ ⟨x.1, mem_compl.mp x.2⟩)
          (fun _ _ => mem_univ _)
          (fun f₂ g₂ _ _ heq => by
            funext ⟨i, hi⟩
            exact congrFun heq ⟨i, mem_compl.mpr hi⟩)
          (fun g _ => ⟨fun x => g ⟨x.1, mem_compl.mpr x.2⟩, mem_univ _, by
            funext ⟨i, hi⟩; rfl⟩)
          (fun f₂ _ => ?_)
        have hPeq : (∀ k ∈ s, P k (z0 (T a) (fun _ => false) f₂)) ↔
            (∀ k ∈ s, P k (z0 (T a)ᶜ (fun x => f₂ ⟨x.1, mem_compl.mp x.2⟩) (fun _ => false))) := by
          refine forall₂_congr fun k hk => v1 k hk _ _ fun i hi => ?_
          have hnot : i ∉ T a := disjoint_right.mp v0 (mem_biUnion.mpr ⟨k, hk, hi⟩)
          simp [z0, hnot]
        have hpeq : (∏ x : {i // i ∉ T a}, z9 p (f₂ x)) =
            ∏ x : {i // i ∈ (T a)ᶜ}, z9 p (f₂ ⟨x.1, mem_compl.mp x.2⟩) := by
          refine prod_bij (fun x _ => ⟨x.1, mem_compl.mpr x.2⟩)
            (fun _ _ => mem_univ _)
            (fun x _ y _ h => Subtype.ext (by simpa using congrArg Subtype.val h))
            (fun y _ => ⟨⟨y.1, mem_compl.mp y.2⟩, mem_univ _, rfl⟩)
            (fun _ _ => rfl)
        by_cases h0 : ∀ k ∈ s, P k (z0 (T a) (fun _ => false) f₂)
        · rw [if_pos h0, if_pos (hPeq.mp h0), hpeq]
        · rw [if_neg h0, if_neg (fun h => h0 (hPeq.mpr h))]
      exact hbij.trans (by convert hRHS.symm)
lemma yb {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι) (p : ℝ)
    (c : ι → Bool) :
    z4 p (fun f : ι → Bool => ∀ i ∈ T, f i = c i) = ∏ i ∈ T, z9 p (c i) := by
  classical
  have v1 : Set.PairwiseDisjoint (T : Set ι) (fun i => ({i} : Finset ι)) := by
    intro i _ j _ hne; exact disjoint_singleton.mpr hne
  rw [y5 T (fun i => {i}) v1 p (fun i f => f i = c i)
    (fun i _ f g hfg => by rw [hfg i (mem_singleton_self i)])]
  refine prod_congr rfl fun i _ => ?_
  rw [w2 {i} p (fun f => f i = c i) (fun f g hfg => by
    rw [hfg i (mem_singleton_self i)])]
  unfold z4
  let e : ({x // x ∈ ({i} : Finset ι)} → Bool) ≃ Bool :=
    { toFun := fun f₁ => f₁ ⟨i, mem_singleton_self i⟩
      invFun := fun b _ => b
      left_inv := fun f₁ => by
        funext ⟨x, hx⟩; have hxi : x = i := mem_singleton.mp hx; subst hxi; rfl
      right_inv := fun _ => rfl }
  rw [← Equiv.sum_comp e.symm]
  have v0 : ∀ b : Bool, (∏ _x : {x // x ∈ ({i} : Finset ι)}, z9 p b) = z9 p b := by
    intro b
    have v2 : Fintype.card {x // x ∈ ({i} : Finset ι)} = 1 := by simp
    rw [prod_const, Finset.card_univ, v2, pow_one]
  simp only [e, Equiv.coe_fn_symm_mk, z0, mem_singleton_self, ↓reduceDIte, v0]
  cases c i <;> simp
lemma z1p : exp (-1 / 2 : ℝ) ≤ 1 - 3 / 8 := by
  have hb := exp_bound (x := (-1 / 2 : ℝ)) (n := 4) (by norm_num) (by norm_num)
  rw [abs_le] at hb
  simp [sum_range_succ, Nat.factorial] at hb
  linarith
lemma z0s : exp (1 / 2 : ℝ) ≤ 1 + 2 / 3 := by
  have hb := exp_bound (x := (1 / 2 : ℝ)) (n := 3) (by norm_num) (by norm_num)
  rw [abs_le] at hb
  simp [sum_range_succ, Nat.factorial] at hb
  linarith
lemma yt {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    exp (-2 * x) ≤ 1 - x := by
  have h1 : 1 - x > 0 := by linarith
  have h2 : (1 - x) * exp (2 * x) ≥ 1 := by
    have hge : 1 + 2 * x + (2 * x) ^ 2 / 2 ≤ exp (2 * x) := by
      have hpos : 0 ≤ 2 * x := by linarith
      have h3 := Real.sum_le_exp_of_nonneg hpos 3
      simp [sum_range_succ, Nat.factorial] at h3
      linarith
    have v0 : 1 ≤ (1 - x) * (1 + 2 * x + (2 * x) ^ 2 / 2) := by
      have : (1 - x) * (1 + 2 * x + (2 * x) ^ 2 / 2) - 1 = x * (1 - 2 * x ^ 2) := by ring
      have hsq : 2 * x ^ 2 ≤ 1 := by nlinarith
      nlinarith
    nlinarith
  calc exp (-2 * x) = (exp (2 * x))⁻¹ := by rw [← exp_neg]; congr 1; ring
    _ ≤ 1 - x := by
      rw [inv_le_comm₀ (exp_pos _) h1]
      rw [inv_le_iff_one_le_mul₀ h1]
      linarith
lemma z0j {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - exp (-x) := by
  have v2 : exp (-x) ≤ 1 - x / 2 := by
    have h2 : 1 + x ≤ exp x := by linarith [Real.add_one_le_exp x]
    have v0 : exp (-x) = (exp x)⁻¹ := exp_neg x
    rw [v0]
    have v1 : 0 < 1 + x := by linarith
    have hinv : (exp x)⁻¹ ≤ (1 + x)⁻¹ := inv_anti₀ v1 h2
    have hrat : (1 + x)⁻¹ ≤ 1 - x / 2 := by
      rw [inv_le_comm₀ v1 (by linarith)]
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      nlinarith
    exact hinv.trans hrat
  linarith
lemma z17 {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ)
    (S : Finset ι) (t : ℝ) :
    (∑ f : ι → Bool, (∏ i : ι, z9 p (f i)) *
      exp (t * ∑ i ∈ S, if f i = true then (1 : ℝ) else 0)) =
      (p * exp t + (1 - p)) ^ S.card := by
  classical
  have hrew : ∀ f : ι → Bool,
      (∏ i : ι, z9 p (f i)) *
        exp (t * ∑ i ∈ S, if f i = true then (1 : ℝ) else 0) =
      ∏ i : ι, (z9 p (f i) * if i ∈ S then exp (if f i = true then t else 0) else 1) := by
    intro f
    rw [prod_mul_distrib, mul_sum, exp_sum]
    congr 1
    rw [← prod_filter_mul_prod_filter_not univ (· ∈ S)]
    have h1 : (∏ i ∈ univ.filter (· ∈ S),
        if i ∈ S then exp (if f i = true then t else 0) else 1) =
        ∏ i ∈ S, exp (t * if f i = true then 1 else 0) := by
      have hflt : univ.filter (· ∈ S) = S := by ext i; simp
      rw [hflt]
      refine prod_congr rfl fun i hi => by
        rw [if_pos hi]; split_ifs <;> simp
    have h2 : (∏ i ∈ univ.filter (· ∉ S),
        if i ∈ S then exp (if f i = true then t else 0) else 1) = 1 := by
      refine prod_eq_one fun i hi => by
        have hnot : i ∉ S := (mem_filter.mp hi).2
        rw [if_neg hnot]
    rw [h1, h2, mul_one]
  simp_rw [hrew]
  have v0 := Fintype.prod_sum
    (fun (i : ι) (b : Bool) => z9 p b * if i ∈ S then exp (if b = true then t else 0) else 1)
  rw [← v0, ← prod_filter_mul_prod_filter_not univ (· ∈ S)]
  have h1 : (∏ i ∈ univ.filter (· ∈ S),
      ∑ b : Bool, z9 p b * if i ∈ S then exp (if b = true then t else 0) else 1) =
      (p * exp t + (1 - p)) ^ S.card := by
    have hflt : univ.filter (· ∈ S) = S := by ext i; simp
    rw [hflt]
    have hpt : ∀ i ∈ S,
        (∑ b : Bool, z9 p b * if i ∈ S then exp (if b = true then t else 0) else 1) =
        p * exp t + (1 - p) := fun i hi => by
      simp [hi, z9]
    rw [prod_congr rfl hpt, prod_const]
  have h2 : (∏ i ∈ univ.filter (· ∉ S),
      ∑ b : Bool, z9 p b * if i ∈ S then exp (if b = true then t else 0) else 1) = 1 := by
    refine prod_eq_one fun i hi => by
      have hnot : i ∉ S := (mem_filter.mp hi).2
      simp [hnot, z9]
  rw [h1, h2, mul_one]
lemma z1a {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) :
    z4 p (fun f : ι → Bool =>
      2 * ((S.card : ℝ) * p) < ((S.filter (fun i => f i = true)).card : ℝ)) ≤
      exp (-((S.card : ℝ) * p) / 3) := by
  classical
  unfold z4
  let t : ℝ := 1 / 2
  have h1 : (∑ f : ι → Bool,
      if 2 * ((S.card : ℝ) * p) < ((S.filter (fun i => f i = true)).card : ℝ) then
        ∏ i : ι, z9 p (f i) else 0) * exp ((S.card : ℝ) * p) ≤
      (∑ f : ι → Bool, (∏ i : ι, z9 p (f i)) *
        exp (t * ∑ i ∈ S, if f i = true then (1 : ℝ) else 0)) := by
    rw [sum_mul]
    refine sum_le_sum fun f _ => ?_
    have hw : 0 ≤ ∏ i : ι, z9 p (f i) := prod_nonneg fun _ _ => yh hp0 hp1 _
    split_ifs with hgt
    · refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) hw
      have hcnt : (∑ i ∈ S, if f i = true then (1 : ℝ) else 0) =
          ((S.filter (fun i => f i = true)).card : ℝ) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      rw [hcnt]; simp only [t]; linarith
    · rw [zero_mul]
      exact mul_nonneg hw (exp_pos _).le
  rw [z17] at h1
  have v0 : p * exp t + (1 - p) ≤ exp ((2 / 3) * p) := by
    have v1 : exp t ≤ 1 + 2 / 3 := z0s
    have hlin : p * exp t + (1 - p) ≤ ((2 / 3) * p) + 1 := by nlinarith
    exact hlin.trans (Real.add_one_le_exp _)
  have hpow : (p * exp t + (1 - p)) ^ S.card ≤ exp ((2 / 3) * ((S.card : ℝ) * p)) := by
    have hnn : 0 ≤ p * exp t + (1 - p) := by
      have := exp_pos t; nlinarith
    calc (p * exp t + (1 - p)) ^ S.card
        ≤ (exp ((2 / 3) * p)) ^ S.card := pow_le_pow_left₀ hnn v0 S.card
      _ = exp ((S.card : ℝ) * ((2 / 3) * p)) := (exp_nat_mul _ _).symm
      _ = exp ((2 / 3) * ((S.card : ℝ) * p)) := by congr 1; ring
  have h2 := h1.trans hpow
  rw [← le_div_iff₀ (exp_pos _), ← exp_sub] at h2
  calc (∑ f : ι → Bool,
          if 2 * ((S.card : ℝ) * p) < ((S.filter (fun i => f i = true)).card : ℝ) then
            ∏ i : ι, z9 p (f i) else 0)
      ≤ exp ((2 / 3) * ((S.card : ℝ) * p) - (S.card : ℝ) * p) := h2
    _ = exp (-((S.card : ℝ) * p) / 3) := by congr 1; ring
lemma z27 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (S : Finset ι) (K : ℕ) :
    z4 p (fun f : ι → Bool => (S.filter (fun i => f i = true)).card = K) =
      (S.card.choose K : ℝ) * p ^ K * (1 - p) ^ (S.card - K) := by
  classical
  unfold z4
  have v4 : ∀ f : ι → Bool,
      (if (S.filter (fun i => f i = true)).card = K then ∏ i : ι, z9 p (f i) else 0) =
      ∑ T ∈ S.powersetCard K,
        if ∀ i ∈ S, f i = decide (i ∈ T) then ∏ i : ι, z9 p (f i) else 0 := by
    intro f
    by_cases hK : (S.filter (fun i => f i = true)).card = K
    · rw [if_pos hK]
      let T₀ := S.filter (fun i => f i = true)
      have hT₀_mem : T₀ ∈ S.powersetCard K :=
        mem_powersetCard.mpr ⟨filter_subset _ _, hK⟩
      symm
      rw [sum_eq_single T₀]
      · have heq : ∀ i ∈ S, f i = decide (i ∈ T₀) := fun i hi => by
          cases hfi : f i <;> simp [T₀, hi, hfi]
        rw [if_pos heq]
      · intro T hT hne
        rw [if_neg]
        intro hall
        apply hne
        ext i
        simp only [T₀, mem_filter]
        constructor
        · intro hiT
          have hiS : i ∈ S := (mem_powersetCard.mp hT).1 hiT
          exact ⟨hiS, by simpa [hiT] using hall i hiS⟩
        · rintro ⟨hiS, hfi⟩
          have := hall i hiS
          rw [hfi] at this
          simpa using this.symm
      · intro hnot; exact absurd hT₀_mem hnot
    · rw [if_neg hK]
      symm
      refine sum_eq_zero fun T hT => ?_
      rw [if_neg]
      intro hall
      apply hK
      have heq : S.filter (fun i => f i = true) = T := by
        ext i
        simp only [mem_filter]
        constructor
        · rintro ⟨hiS, hfi⟩
          have := hall i hiS; rw [hfi] at this; simpa using this.symm
        · intro hiT
          have hiS : i ∈ S := (mem_powersetCard.mp hT).1 hiT
          exact ⟨hiS, by simpa [hiT] using hall i hiS⟩
      rw [heq]
      exact (mem_powersetCard.mp hT).2
  have v1 : (∑ f : ι → Bool,
      if (S.filter (fun i => f i = true)).card = K then ∏ i : ι, z9 p (f i) else 0) =
      (S.card.choose K : ℝ) * p ^ K * (1 - p) ^ (S.card - K) := by
    simp_rw [v4]
    rw [sum_comm]
    have v5 : ∀ T ∈ S.powersetCard K,
        (∑ f : ι → Bool, if ∀ i ∈ S, f i = decide (i ∈ T) then ∏ i : ι, z9 p (f i) else 0) =
        p ^ K * (1 - p) ^ (S.card - K) := by
      intro T hT
      have h1 := yb S p (fun i => decide (i ∈ T))
      unfold z4 at h1
      rw [show (∑ f : ι → Bool, if ∀ i ∈ S, f i = decide (i ∈ T) then ∏ i : ι, z9 p (f i) else 0) =
          ∏ i ∈ S, z9 p (decide (i ∈ T)) by convert h1]
      have v2 : T ⊆ S := (mem_powersetCard.mp hT).1
      have v0 : T.card = K := (mem_powersetCard.mp hT).2
      have v3 : S = T ∪ (S \ T) := (union_sdiff_of_subset v2).symm
      conv_lhs => rw [v3]
      rw [prod_union disjoint_sdiff]
      congr 1
      · rw [prod_congr rfl (g := fun _ => p) (fun i hi => by
            simp [z9, decide_eq_true hi]),
          prod_const, v0]
      · rw [prod_congr rfl (g := fun _ => 1 - p) (fun i hi => by
          have hnot : i ∉ T := (mem_sdiff.mp hi).2
          simp [z9, decide_eq_false hnot]), prod_const, card_sdiff,
          inter_eq_left.mpr v2, v0]
    rw [sum_congr rfl v5, sum_const, card_powersetCard, nsmul_eq_mul]
    ring
  convert v1
lemma yx {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (idx : Finset κ) (T : κ → Finset ι)
    (hdisj : Set.PairwiseDisjoint (idx : Set κ) T)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : κ → (ι → Bool) → Prop) [∀ k, DecidablePred (P k)]
    (hdep : ∀ k ∈ idx, ∀ f g : ι → Bool, (∀ i ∈ T k, f i = g i) → (P k f ↔ P k g))
    {r : ℝ} (hr0 : 0 ≤ r)
    (hprob : ∀ k ∈ idx, r ≤ z4 p (P k)) :
    z4 p (fun f : ι → Bool =>
      ((idx.filter (fun k => P k f)).card : ℝ) < (1 / 2) * ((idx.card : ℝ) * r)) ≤
      exp (-((idx.card : ℝ) * r) / 8) := by
  classical
  have hmgf : ∀ t : ℝ,
      (∑ f : ι → Bool, (∏ i : ι, z9 p (f i)) *
        exp (t * ∑ k ∈ idx, if P k f then (1 : ℝ) else 0)) =
      ∏ k ∈ idx, (z4 p (P k) * exp t + (1 - z4 p (P k))) := by
    intro t
    clear hprob
    induction idx using Finset.induction_on with
    | empty =>
      simp only [sum_empty, mul_zero, exp_zero, mul_one, prod_empty]
      exact y4 p
    | insert a s has ih =>
      have v4 : Set.PairwiseDisjoint (s : Set κ) T :=
        hdisj.subset (subset_insert a s)
      have v5 : Disjoint (T a) (s.biUnion T) := by
        rw [disjoint_biUnion_right]
        intro k hk
        exact hdisj (mem_insert_self a s) (mem_insert_of_mem hk) (fun h => has (h ▸ hk))
      have v2 : ∀ k ∈ s, ∀ f g : ι → Bool, (∀ i ∈ T k, f i = g i) → (P k f ↔ P k g) :=
        fun k hk => hdep k (mem_insert_of_mem hk)
      rw [prod_insert has, ← ih v4 v2]
      rw [← Equiv.sum_comp (zw (T a)).symm]
      rw [Fintype.sum_prod_type]
      have hPa : ∀ f₁ f₂, P a (z0 (T a) f₁ f₂) ↔ P a (z0 (T a) f₁ (fun _ => false)) :=
        fun f₁ f₂ => hdep a (mem_insert_self a s) _ _ (fun i hi => by simp [z0, hi])
      have hPs : ∀ k ∈ s, ∀ f₁ f₂,
          P k (z0 (T a) f₁ f₂) ↔ P k (z0 (T a) (fun _ => false) f₂) := by
        intro k hk f₁ f₂
        refine v2 k hk _ _ fun i hi => ?_
        have hnot : i ∉ T a := disjoint_right.mp v5 (mem_biUnion.mpr ⟨k, hk, hi⟩)
        simp [z0, hnot]
      have hrew : ∀ f₁ f₂,
          (∏ i : ι, z9 p ((zw (T a)).symm (f₁, f₂) i)) *
            exp (t * ∑ k ∈ insert a s, if P k ((zw (T a)).symm (f₁, f₂)) then (1 : ℝ) else 0) =
          ((∏ x : {i // i ∈ T a}, z9 p (f₁ x)) *
            exp (t * if P a (z0 (T a) f₁ (fun _ => false)) then 1 else 0)) *
          ((∏ x : {i // i ∉ T a}, z9 p (f₂ x)) *
            exp (t * ∑ k ∈ s, if P k (z0 (T a) (fun _ => false) f₂) then (1 : ℝ) else 0)) := by
        intro f₁ f₂
        change (∏ i : ι, z9 p (z0 (T a) f₁ f₂ i)) *
            exp (t * ∑ k ∈ insert a s, if P k (z0 (T a) f₁ f₂) then (1 : ℝ) else 0) = _
        rw [y7, sum_insert has, mul_add, exp_add]
        have v3 : (if P a (z0 (T a) f₁ f₂) then (1 : ℝ) else 0) =
            if P a (z0 (T a) f₁ (fun _ => false)) then 1 else 0 := by
          by_cases h : P a (z0 (T a) f₁ (fun _ => false))
          · rw [if_pos ((hPa f₁ f₂).mpr h), if_pos h]
          · rw [if_neg (fun h' => h ((hPa f₁ f₂).mp h')), if_neg h]
        have v0 : (∑ k ∈ s, if P k (z0 (T a) f₁ f₂) then (1 : ℝ) else 0) =
            ∑ k ∈ s, if P k (z0 (T a) (fun _ => false) f₂) then 1 else 0 :=
          sum_congr rfl fun k hk => by
            by_cases h : P k (z0 (T a) (fun _ => false) f₂)
            · rw [if_pos ((hPs k hk f₁ f₂).mpr h), if_pos h]
            · rw [if_neg (fun h' => h ((hPs k hk f₁ f₂).mp h')), if_neg h]
        rw [v3, v0]; ring
      rw [sum_congr rfl fun f₁ _ => sum_congr rfl fun f₂ _ => hrew f₁ f₂]
      simp_rw [← mul_sum, ← sum_mul]
      congr 1
      · let pa := z4 p (P a)
        have hpa : pa = ∑ f₁ : {i // i ∈ T a} → Bool,
            if P a (z0 (T a) f₁ (fun _ => false)) then
              ∏ x : {i // i ∈ T a}, z9 p (f₁ x) else 0 := by
          have h := w2 (T a) p (P a) (hdep a (mem_insert_self a s))
          unfold z4 at h
          dsimp only [pa, z4]
          convert h
        have htot : (∑ f₁ : {i // i ∈ T a} → Bool, ∏ x : {i // i ∈ T a}, z9 p (f₁ x)) = 1 :=
          y4 p
        have h1 : ∀ f₁ : {i // i ∈ T a} → Bool,
            (∏ x : {i // i ∈ T a}, z9 p (f₁ x)) *
              exp (t * if P a (z0 (T a) f₁ (fun _ => false)) then 1 else 0) =
            (if P a (z0 (T a) f₁ (fun _ => false)) then
              ∏ x : {i // i ∈ T a}, z9 p (f₁ x) else 0) * exp t +
            ((∏ x : {i // i ∈ T a}, z9 p (f₁ x)) -
              if P a (z0 (T a) f₁ (fun _ => false)) then
                ∏ x : {i // i ∈ T a}, z9 p (f₁ x) else 0) := by
          intro f₁
          by_cases h : P a (z0 (T a) f₁ (fun _ => false)) <;> simp [h]
        simp_rw [h1]
        rw [sum_add_distrib, ← sum_mul, sum_sub_distrib, htot, ← hpa]
      · have h2 : (∑ f : ι → Bool, (∏ i : ι, z9 p (f i)) *
            exp (t * ∑ k ∈ s, if P k f then (1 : ℝ) else 0)) =
            ∑ f₂ : {i // i ∉ T a} → Bool, (∏ x : {i // i ∉ T a}, z9 p (f₂ x)) *
              exp (t * ∑ k ∈ s, if P k (z0 (T a) (fun _ => false) f₂) then 1 else 0) := by
          rw [← Equiv.sum_comp (zw (T a)).symm]
          rw [Fintype.sum_prod_type]
          have v6 : ∀ f₁ f₂,
              (∏ i : ι, z9 p ((zw (T a)).symm (f₁, f₂) i)) *
                exp (t * ∑ k ∈ s, if P k ((zw (T a)).symm (f₁, f₂)) then (1 : ℝ) else 0) =
              (∏ x : {i // i ∈ T a}, z9 p (f₁ x)) *
                ((∏ x : {i // i ∉ T a}, z9 p (f₂ x)) *
                  exp (t * ∑ k ∈ s, if P k (z0 (T a) (fun _ => false) f₂) then 1 else 0)) := by
            intro f₁ f₂
            change (∏ i : ι, z9 p (z0 (T a) f₁ f₂ i)) *
                exp (t * ∑ k ∈ s, if P k (z0 (T a) f₁ f₂) then (1 : ℝ) else 0) = _
            rw [y7]
            have v0 : (∑ k ∈ s, if P k (z0 (T a) f₁ f₂) then (1 : ℝ) else 0) =
                ∑ k ∈ s, if P k (z0 (T a) (fun _ => false) f₂) then 1 else 0 :=
              sum_congr rfl fun k hk => by
                by_cases h : P k (z0 (T a) (fun _ => false) f₂)
                · rw [if_pos ((hPs k hk f₁ f₂).mpr h), if_pos h]
                · rw [if_neg (fun h' => h ((hPs k hk f₁ f₂).mp h')), if_neg h]
            rw [v0]; ring
          rw [sum_congr rfl fun f₁ _ => sum_congr rfl fun f₂ _ => v6 f₁ f₂]
          simp_rw [← mul_sum, ← sum_mul]
          rw [y4, one_mul]
        exact h2.symm
  unfold z4
  let t : ℝ := -1 / 2
  have h1 : (∑ f : ι → Bool,
      if ((idx.filter (fun k => P k f)).card : ℝ) < (1 / 2) * ((idx.card : ℝ) * r) then
        ∏ i : ι, z9 p (f i) else 0) * exp (-(1 / 4) * ((idx.card : ℝ) * r)) ≤
      (∑ f : ι → Bool, (∏ i : ι, z9 p (f i)) *
        exp (t * ∑ k ∈ idx, if P k f then (1 : ℝ) else 0)) := by
    rw [sum_mul]
    refine sum_le_sum fun f _ => ?_
    have hw : 0 ≤ ∏ i : ι, z9 p (f i) := prod_nonneg fun _ _ => yh hp0 hp1 _
    split_ifs with hlt
    · refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) hw
      have hcnt : (∑ k ∈ idx, if P k f then (1 : ℝ) else 0) =
          ((idx.filter (fun k => P k f)).card : ℝ) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      rw [hcnt]; simp only [t]; linarith
    · rw [zero_mul]
      exact mul_nonneg hw (exp_pos _).le
  rw [hmgf t] at h1
  have v7 : exp t ≤ 1 - 3 / 8 := z1p
  have v1 : (∏ k ∈ idx, (z4 p (P k) * exp t + (1 - z4 p (P k)))) ≤
      exp (-(3 / 8) * ((idx.card : ℝ) * r)) := by
    calc ∏ k ∈ idx, (z4 p (P k) * exp t + (1 - z4 p (P k)))
        ≤ ∏ _k ∈ idx, exp (-(3 / 8) * r) := by
          refine prod_le_prod (fun k _ => ?_) (fun k hk => ?_)
          · have hpk0 : 0 ≤ z4 p (P k) := ym hp0 hp1 (P k)
            have hpk1 : z4 p (P k) ≤ 1 := by
              have h := zi hp0 hp1 (P := P k) (Q := fun _ => True) (fun _ _ => trivial)
              rwa [z0b] at h
            have := exp_pos t
            nlinarith
          · have hpk := hprob k hk
            have hlin : z4 p (P k) * exp t + (1 - z4 p (P k)) ≤
                (-(3 / 8) * r) + 1 := by nlinarith
            exact hlin.trans (Real.add_one_le_exp _)
      _ = (exp (-(3 / 8) * r)) ^ idx.card := prod_const _
      _ = exp ((idx.card : ℝ) * (-(3 / 8) * r)) := (exp_nat_mul _ _).symm
      _ = exp (-(3 / 8) * ((idx.card : ℝ) * r)) := by congr 1; ring
  have h2 := h1.trans v1
  rw [← le_div_iff₀ (exp_pos _), ← exp_sub] at h2
  calc (∑ f : ι → Bool,
          if ((idx.filter (fun k => P k f)).card : ℝ) < (1 / 2) * ((idx.card : ℝ) * r) then
            ∏ i : ι, z9 p (f i) else 0)
      ≤ exp (-(3 / 8) * ((idx.card : ℝ) * r) - -(1 / 4) * ((idx.card : ℝ) * r)) := h2
    _ = exp (-((idx.card : ℝ) * r) / 8) := by congr 1; ring
end
section
open Finset FirstOrder FirstOrder.Language
def zd : ℕ → ℕ
  | 0 => 1
  | i + 1 => 2 ^ zd i
lemma z03 : ∀ i : ℕ, 0 < zd i
  | 0 => by simp [zd]
  | i + 1 => Nat.two_pow_pos (zd i)
lemma wo : StrictMono zd := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  change zd i < 2 ^ zd i
  exact Nat.lt_two_pow_self
lemma y6 : Monotone zd := wo.monotone
lemma y9 : ∀ m : ℕ, 2 ≤ m → m ≤ zd (m - 1) := by
  intro m hm
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  induction r with
  | zero => simp [zd]
  | succ r ih =>
    have h1 : r + 2 ≤ zd (r + 1) := ih (by omega)
    have h2 : zd (r + 1) < zd (r + 2) := wo (Nat.lt_succ_self _)
    have hsub : r + 1 + 2 - 1 = r + 2 := by omega
    rw [hsub]
    omega
def kOf (q : ℕ) : ℕ := 3 * q - 2
def cIdx (q : ℕ) (hq : 2 ≤ q) (i : Fin (q - 1)) : Fin (kOf q) :=
  ⟨i.val, by unfold kOf; omega⟩
def z1q (q : ℕ) (hq : 2 ≤ q) (i : Fin (q - 1)) : Fin (kOf q) :=
  ⟨(q - 1) + i.val, by unfold kOf; omega⟩
def bIdx (q : ℕ) (hq : 2 ≤ q) (j : Fin (q - 2)) : Fin (kOf q) :=
  ⟨2 * (q - 1) + j.val, by unfold kOf; omega⟩
def dIdx (q : ℕ) (hq : 2 ≤ q) : Fin (kOf q) :=
  ⟨3 * q - 4, by unfold kOf; omega⟩
def z29 (q : ℕ) (hq : 2 ≤ q) : Fin (kOf q) :=
  ⟨3 * q - 3, by unfold kOf; omega⟩
def yc (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (a : Fin (kOf q) → Fin n) (i : Fin (q - 1)) : Fin n :=
  a (cIdx q hq i)
def yc' (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (a : Fin (kOf q) → Fin n) (i : Fin (q - 1)) : Fin n :=
  a (z1q q hq i)
def ys (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (a : Fin (kOf q) → Fin n) (j : Fin (q - 2)) : Fin n :=
  a (bIdx q hq j)
def w7 (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (a : Fin (kOf q) → Fin n) : Fin n :=
  a (dIdx q hq)
def w7' (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (a : Fin (kOf q) → Fin n) : Fin n :=
  a (z29 q hq)
def isBc (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (z : Fin n) : Prop :=
  ∀ i : Fin (q - 1), G.Adj z (yc q hq a i)
def isBc' (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (z : Fin n) : Prop :=
  ∀ i : Fin (q - 1), G.Adj z (yc' q hq a i)
def zs (q : ℕ) {n : ℕ} (a : Fin (kOf q) → Fin n) (v : Fin n) : Prop :=
  ∃ r : Fin (kOf q), v = a r
def z0m (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (w : Fin n) : Prop :=
  ¬ zs q a w ∧ ¬ isBc q hq G a w ∧ ¬ isBc' q hq G a w
def Rrel (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (u v : Fin n) : Prop :=
  ∃ w : Fin n, z0m q hq G a w ∧ G.Adj w u ∧ G.Adj w v ∧
    ∀ j : Fin (q - 2), G.Adj w (ys q hq a j)
def Ax (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x z : Fin n) : Prop :=
  isBc q hq G a z ∧ G.Adj z x ∧ ¬ zs q a z
def inDom (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x : Fin n) : Prop :=
  isBc' q hq G a x ∧ G.Adj x (w7 q hq a) ∧ ¬ zs q a x
def inE (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (z : Fin n) : Prop :=
  isBc' q hq G a z ∧ G.Adj z (w7' q hq a) ∧ ¬ zs q a z
def yv (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x y : Fin n) : Prop :=
  (∀ z : Fin n, inE q hq G a z → Rrel q hq G a x z → Rrel q hq G a y z) ∧
  (∃ z : Fin n, inE q hq G a z ∧ Rrel q hq G a y z ∧ ¬ Rrel q hq G a x z)
def yn (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x y : Fin n) : Prop :=
  (∀ u₁ u₂ : Fin n, Ax q hq G a y u₁ → Ax q hq G a y u₂ → u₁ ≠ u₂ →
    ∃ z : Fin n, Ax q hq G a x z ∧ ¬ (Rrel q hq G a u₁ z ↔ Rrel q hq G a u₂ z)) ∧
  (∀ v : Fin n, ∃ u : Fin n, Ax q hq G a y u ∧
    ∀ z : Fin n, Ax q hq G a x z → (Rrel q hq G a u z ↔ Rrel q hq G a v z))
def z04 (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x y : Fin n) : Prop :=
  inDom q hq G a x ∧ inDom q hq G a y ∧ yv q hq G a x y ∧
    ∀ z : Fin n, inDom q hq G a z → ¬ (yv q hq G a x z ∧ yv q hq G a z y)
def ws (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) : Prop :=
  Function.Injective a ∧
  (∃ x : Fin n, inDom q hq G a x) ∧
  (∀ x y : Fin n, inDom q hq G a x → inDom q hq G a y →
    yv q hq G a x y ∨ x = y ∨ yv q hq G a y x) ∧
  (∀ x : Fin n, inDom q hq G a x → (∀ y : Fin n, inDom q hq G a y → ¬ yv q hq G a y x) →
    ∃ z : Fin n, Ax q hq G a x z ∧ ∀ z' : Fin n, Ax q hq G a x z' → z' = z) ∧
  (∀ x y : Fin n, z04 q hq G a x y → yn q hq G a x y) ∧
  (∀ x : Fin n, inDom q hq G a x → (∀ y : Fin n, inDom q hq G a y → ¬ yv q hq G a x y) →
    ¬ ∃ y : Fin n, ¬ zs q a y ∧ yn q hq G a x y)
lemma ltRel_irrefl (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x : Fin n) : ¬ yv q hq G a x x := by
  rintro ⟨_, z, _, h1, h2⟩
  exact h2 h1
lemma ltRel_trans (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) {x y z : Fin n}
    (hxy : yv q hq G a x y) (hyz : yv q hq G a y z) :
    yv q hq G a x z := by
  refine ⟨fun w hw hx => hyz.1 w hw (hxy.1 w hw hx), ?_⟩
  rcases hxy.2 with ⟨w, hw, hy, hnx⟩
  exact ⟨w, hw, hyz.1 w hw hy, hnx⟩
abbrev GBF (α : Type*) (l : ℕ) := FirstOrder.Language.graph.BoundedFormula α l
abbrev zy (α : Type*) (l : ℕ) := FirstOrder.Language.graph.Term (α ⊕ Fin l)
def pVar {α : Type*} {l : ℕ} (i : α) : zy α l :=
  FirstOrder.Language.Term.var (Sum.inl i)
def bVar {α : Type*} {l : ℕ} (j : Fin l) : zy α l :=
  FirstOrder.Language.Term.var (Sum.inr j)
def y0 {α : Type*} {l : ℕ} : zy α l → zy α (l + 1)
  | .var (Sum.inl i) => .var (Sum.inl i)
  | .var (Sum.inr j) => .var (Sum.inr j.castSucc)
  | .func f _ => Empty.elim f
lemma yz {α : Type*} {l n : ℕ} (G : SimpleGraph (Fin n))
    (v : α → Fin n) (xs : Fin l → Fin n) (y : Fin n) (t : zy α l) :
    @Term.realize FirstOrder.Language.graph (Fin n) G.structure _ (Sum.elim v (Fin.snoc xs y)) (y0 t) =
      @Term.realize FirstOrder.Language.graph (Fin n) G.structure _ (Sum.elim v xs) t := by
  cases t with
  | var s =>
    cases s with
    | inl i => rfl
    | inr j => simp [y0, Fin.snoc_castSucc]
  | func f _ => exact Empty.elim f
def z0f {α : Type*} {l : ℕ} (t₁ t₂ : zy α l) : GBF α l :=
  BoundedFormula.rel FirstOrder.Language.adj ![t₁, t₂]
lemma w1 {α : Type*} {l n : ℕ} (G : SimpleGraph (Fin n))
    (v : α → Fin n) (xs : Fin l → Fin n) (t₁ t₂ : zy α l) :
    @BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure α l (z0f t₁ t₂) v xs ↔
      G.Adj
        (@Term.realize FirstOrder.Language.graph (Fin n) G.structure _ (Sum.elim v xs) t₁)
        (@Term.realize FirstOrder.Language.graph (Fin n) G.structure _ (Sum.elim v xs) t₂) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  rfl
def eqBF {α : Type*} {l : ℕ} (t₁ t₂ : zy α l) : GBF α l :=
  Term.bdEqual t₁ t₂
lemma wd {α : Type*} {l n : ℕ} (G : SimpleGraph (Fin n))
    (v : α → Fin n) (xs : Fin l → Fin n) (t₁ t₂ : zy α l) :
    @BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure α l (eqBF t₁ t₂) v xs ↔
      @Term.realize FirstOrder.Language.graph (Fin n) G.structure _ (Sum.elim v xs) t₁ =
      @Term.realize FirstOrder.Language.graph (Fin n) G.structure _ (Sum.elim v xs) t₂ := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp [eqBF]
def z02 {α : Type*} {l m : ℕ} (f : Fin m → GBF α l) : GBF α l :=
  ((List.finRange m).map f).foldr (· ⊓ ·) ⊤
lemma wc {α : Type*} {l m n : ℕ} (G : SimpleGraph (Fin n))
    (v : α → Fin n) (xs : Fin l → Fin n) (f : Fin m → GBF α l) :
    @BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure α l (z02 f) v xs ↔
      ∀ i : Fin m, @BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure α l (f i) v xs := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  dsimp only [z02]
  rw [BoundedFormula.realize_foldr_inf]
  constructor
  · intro h i
    exact h (f i) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · intro h φ hφ
    rcases List.mem_map.mp hφ with ⟨i, _, rfl⟩
    exact h i
def z1x {α : Type*} {l m : ℕ} (f : Fin m → GBF α l) : GBF α l :=
  ((List.finRange m).map f).foldr (· ⊔ ·) ⊥
lemma z1n {α : Type*} {l m n : ℕ} (G : SimpleGraph (Fin n))
    (v : α → Fin n) (xs : Fin l → Fin n) (f : Fin m → GBF α l) :
    @BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure α l (z1x f) v xs ↔
      ∃ i : Fin m, @BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure α l (f i) v xs := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  dsimp only [z1x]
  rw [BoundedFormula.realize_foldr_sup]
  constructor
  · rintro ⟨φ, hφ, hreal⟩
    rcases List.mem_map.mp hφ with ⟨i, _, rfl⟩
    exact ⟨i, hreal⟩
  · rintro ⟨i, hreal⟩
    exact ⟨f i, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, hreal⟩
section FormulaBuilders
variable (q : ℕ) (hq : 2 ≤ q) {α : Type*} (p : Fin (kOf q) → α)
def z1o {l : ℕ} (tz : zy α l) : GBF α l :=
  z02 fun i : Fin (q - 1) => z0f tz (pVar (p (cIdx q hq i)))
def z0z {l : ℕ} (tz : zy α l) : GBF α l :=
  z02 fun i : Fin (q - 1) => z0f tz (pVar (p (z1q q hq i)))
def we {l : ℕ} (tv : zy α l) : GBF α l :=
  z1x fun r : Fin (kOf q) => eqBF tv (pVar (p r))
def z1u {l : ℕ} (tw : zy α l) : GBF α l :=
  (we q p tw).not ⊓ (z1o q hq p tw).not ⊓ (z0z q hq p tw).not
def wh {l : ℕ} (tu tv : zy α l) : GBF α l :=
  let w : zy α (l + 1) := bVar (Fin.last l)
  (z1u q hq p w ⊓ z0f w (y0 tu) ⊓ z0f w (y0 tv) ⊓
    z02 fun j : Fin (q - 2) => z0f w (pVar (p (bIdx q hq j)))).ex
def AxBF {l : ℕ} (tx tz : zy α l) : GBF α l :=
  z1o q hq p tz ⊓ z0f tz tx ⊓ (we q p tz).not
def yy {l : ℕ} (tx : zy α l) : GBF α l :=
  z0z q hq p tx ⊓ z0f tx (pVar (p (dIdx q hq))) ⊓ (we q p tx).not
def z28 {l : ℕ} (tz : zy α l) : GBF α l :=
  z0z q hq p tz ⊓ z0f tz (pVar (p (z29 q hq))) ⊓ (we q p tz).not
def w9 {l : ℕ} (tx ty : zy α l) : GBF α l :=
  let z : zy α (l + 1) := bVar (Fin.last l)
  let x1 := y0 tx
  let y1 := y0 ty
  ((z28 q hq p z ⊓ wh q hq p x1 z).imp (wh q hq p y1 z)).all ⊓
  (z28 q hq p z ⊓ wh q hq p y1 z ⊓ (wh q hq p x1 z).not).ex
def z0n {l : ℕ} (tx ty : zy α l) : GBF α l :=
  let x2 := y0 (y0 tx)
  let y2 := y0 (y0 ty)
  let u1_2 : zy α (l + 2) := bVar (Fin.last l).castSucc
  let u2_2 : zy α (l + 2) := bVar (Fin.last (l + 1))
  let z3 : zy α (l + 3) := bVar (Fin.last (l + 2))
  let part1 : GBF α l :=
    (((AxBF q hq p y2 u1_2 ⊓ AxBF q hq p y2 u2_2 ⊓ (eqBF u1_2 u2_2).not).imp
      ((AxBF q hq p (y0 x2) z3 ⊓
        ((wh q hq p (y0 u1_2) z3).iff (wh q hq p (y0 u2_2) z3)).not).ex))).all.all
  let x2' := y0 (y0 tx)
  let y2' := y0 (y0 ty)
  let v2 : zy α (l + 2) := bVar (Fin.last l).castSucc
  let u2 : zy α (l + 2) := bVar (Fin.last (l + 1))
  let z3' : zy α (l + 3) := bVar (Fin.last (l + 2))
  let part2 : GBF α l :=
    ((AxBF q hq p y2' u2 ⊓
      ((AxBF q hq p (y0 x2') z3').imp
        ((wh q hq p (y0 u2) z3').iff (wh q hq p (y0 v2) z3'))).all).ex).all
  part1 ⊓ part2
def z0r {l : ℕ} (tx ty : zy α l) : GBF α l :=
  let z : zy α (l + 1) := bVar (Fin.last l)
  yy q hq p tx ⊓ yy q hq p ty ⊓ w9 q hq p tx ty ⊓
    ((yy q hq p z).imp
      (w9 q hq p (y0 tx) z ⊓ w9 q hq p z (y0 ty)).not).all
def z1s : GBF α 0 :=
  let injBF : GBF α 0 :=
    z02 fun r₁ : Fin (kOf q) => z02 fun r₂ : Fin (kOf q) =>
      if r₁ = r₂ then ⊤ else (eqBF (pVar (p r₁)) (pVar (p r₂))).not
  let x1 : zy α 1 := bVar (Fin.last 0)
  let nonempBF : GBF α 0 := (yy q hq p x1).ex
  let x2 : zy α 2 := bVar (Fin.last 0).castSucc
  let y2 : zy α 2 := bVar (Fin.last 1)
  let trichBF : GBF α 0 :=
    (((yy q hq p x2 ⊓ yy q hq p y2).imp
      (w9 q hq p x2 y2 ⊔ eqBF x2 y2 ⊔ w9 q hq p y2 x2))).all.all
  let isMin1 : GBF α 1 :=
    ((yy q hq p y2).imp (w9 q hq p y2 x2).not).all
  let card1 : GBF α 1 :=
    let z2 : zy α 2 := bVar (Fin.last 1)
    let z3 : zy α 3 := bVar (Fin.last 2)
    (AxBF q hq p x2 z2 ⊓
      ((AxBF q hq p (y0 x2) z3).imp (eqBF z3 (y0 z2))).all).ex
  let baseBF : GBF α 0 := ((yy q hq p x1 ⊓ isMin1).imp card1).all
  let stepBF : GBF α 0 := ((z0r q hq p x2 y2).imp (z0n q hq p x2 y2)).all.all
  let isMax1 : GBF α 1 :=
    ((yy q hq p y2).imp (w9 q hq p x2 y2).not).all
  let noStep1 : GBF α 1 :=
    ((we q p y2).not ⊓ z0n q hq p x2 y2).ex.not
  let stopBF : GBF α 0 := ((yy q hq p x1 ⊓ isMax1).imp noStep1).all
  injBF ⊓ nonempBF ⊓ trichBF ⊓ baseBF ⊓ stepBF ⊓ stopBF
lemma z0w {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tz : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (z1o q hq p tz) v xs ↔
      isBc q hq G (v ∘ p) (@Term.realize _ _ G.structure _ (Sum.elim v xs) tz) := by
  simp only [z1o, isBc, yc, Function.comp_apply, wc, w1]
  rfl
lemma wu {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tz : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (z0z q hq p tz) v xs ↔
      isBc' q hq G (v ∘ p) (@Term.realize _ _ G.structure _ (Sum.elim v xs) tz) := by
  simp only [z0z, isBc', yc', Function.comp_apply, wc, w1]
  rfl
lemma yu {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tv : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (we q p tv) v xs ↔
      zs q (v ∘ p) (@Term.realize _ _ G.structure _ (Sum.elim v xs) tv) := by
  simp only [we, zs, Function.comp_apply, z1n, wd]
  rfl
lemma z1m {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tw : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (z1u q hq p tw) v xs ↔
      z0m q hq G (v ∘ p) (@Term.realize _ _ G.structure _ (Sum.elim v xs) tw) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp only [z1u, z0m, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    yu, z0w, wu, and_assoc]
lemma z01 {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tu tv : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (wh q hq p tu tv) v xs ↔
      Rrel q hq G (v ∘ p)
        (@Term.realize _ _ G.structure _ (Sum.elim v xs) tu)
        (@Term.realize _ _ G.structure _ (Sum.elim v xs) tv) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp only [wh, Rrel, ys, Function.comp_apply, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, z1m, w1, wc,
    yz, bVar, pVar, Term.realize, Sum.elim_inr, Sum.elim_inl, Fin.snoc_last,
    and_assoc]
lemma z1c {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tx tz : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (AxBF q hq p tx tz) v xs ↔
      Ax q hq G (v ∘ p)
        (@Term.realize _ _ G.structure _ (Sum.elim v xs) tx)
        (@Term.realize _ _ G.structure _ (Sum.elim v xs) tz) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp only [AxBF, Ax, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    z0w, w1, yu, and_assoc]
lemma wv {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tx : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (yy q hq p tx) v xs ↔
      inDom q hq G (v ∘ p) (@Term.realize _ _ G.structure _ (Sum.elim v xs) tx) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp only [yy, inDom, w7, Function.comp_apply, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, wu, w1, yu,
    pVar, Term.realize, Sum.elim_inl, and_assoc]
lemma z20 {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tz : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (z28 q hq p tz) v xs ↔
      inE q hq G (v ∘ p) (@Term.realize _ _ G.structure _ (Sum.elim v xs) tz) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp only [z28, inE, w7', Function.comp_apply, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, wu, w1, yu,
    pVar, Term.realize, Sum.elim_inl, and_assoc]
lemma wt {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tx ty : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (w9 q hq p tx ty) v xs ↔
      yv q hq G (v ∘ p)
        (@Term.realize _ _ G.structure _ (Sum.elim v xs) tx)
        (@Term.realize _ _ G.structure _ (Sum.elim v xs) ty) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp only [w9, yv, BoundedFormula.realize_inf, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_not,
    z20, z01, yz, bVar, Term.realize, Sum.elim_inr,
    Fin.snoc_last, and_imp, and_assoc]
lemma z1f {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tx ty : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (z0n q hq p tx ty) v xs ↔
      yn q hq G (v ∘ p)
        (@Term.realize _ _ G.structure _ (Sum.elim v xs) tx)
        (@Term.realize _ _ G.structure _ (Sum.elim v xs) ty) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp only [z0n, yn, BoundedFormula.realize_inf, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_not,
    BoundedFormula.realize_iff, z1c, z01, wd,
    yz, bVar, Term.realize, Sum.elim_inr, Fin.snoc_last, Fin.snoc_castSucc,
    and_imp]
lemma z18 {l n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin l → Fin n)
    (tx ty : zy α l) :
    @BoundedFormula.Realize _ _ G.structure _ _ (z0r q hq p tx ty) v xs ↔
      z04 q hq G (v ∘ p)
        (@Term.realize _ _ G.structure _ (Sum.elim v xs) tx)
        (@Term.realize _ _ G.structure _ (Sum.elim v xs) ty) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp only [z0r, z04, BoundedFormula.realize_inf, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, wv, wt,
    yz, bVar, Term.realize, Sum.elim_inr, Fin.snoc_last, and_assoc]
lemma z1l {n : ℕ} (G : SimpleGraph (Fin n)) (v : α → Fin n) (xs : Fin 0 → Fin n) :
    @BoundedFormula.Realize _ _ G.structure _ _ (z1s q hq p) v xs ↔
      ws q hq G (v ∘ p) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp only [z1s, ws, BoundedFormula.realize_inf, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_not,
    BoundedFormula.realize_sup, wc, wv, wt,
    wd, z1c, z18, z1f, yu,
    yz, bVar, pVar, Term.realize, Sum.elim_inr,
    Fin.snoc_last, Fin.snoc_castSucc, and_imp, and_assoc, or_assoc]
  have hinj : (∀ r₁ r₂ : Fin (kOf q),
      (if r₁ = r₂ then (⊤ : GBF α 0)
        else (eqBF (Term.var (Sum.inl (p r₁))) (Term.var (Sum.inl (p r₂)))).not).Realize v xs) ↔
      Function.Injective (v ∘ p) := by
    constructor
    · intro h r₁ r₂ heq
      by_contra hne
      have h1 := h r₁ r₂
      rw [if_neg hne, BoundedFormula.realize_not, wd] at h1
      exact h1 heq
    · intro hinj r₁ r₂
      split_ifs with heq
      · simp
      · rw [BoundedFormula.realize_not, wd]
        intro h; exact heq (hinj h)
  rw [hinj]
end FormulaBuilders
def validFormula (q : ℕ) (hq : 2 ≤ q) : FirstOrder.Language.graph.Formula (Fin (kOf q)) :=
  z1s q hq id
def domFormula (q : ℕ) (hq : 2 ≤ q) : FirstOrder.Language.graph.Formula (Fin (kOf q + 1)) :=
  yy q hq Fin.castSucc (pVar (Fin.last (kOf q)))
def ltFormula (q : ℕ) (hq : 2 ≤ q) : FirstOrder.Language.graph.Formula (Fin (kOf q + 2)) :=
  w9 q hq (fun i => i.castSucc.castSucc)
    (pVar (Fin.last (kOf q)).castSucc) (pVar (Fin.last (kOf q + 1)))
def memFormula (q : ℕ) (hq : 2 ≤ q) : FirstOrder.Language.graph.Formula (Fin (kOf q + 2)) :=
  wh q hq (fun i => i.castSucc.castSucc)
    (pVar (Fin.last (kOf q)).castSucc) (pVar (Fin.last (kOf q + 1)))
lemma realize_validFormula (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) :
    @Formula.Realize _ _ G.structure _ (validFormula q hq) a ↔ ws q hq G a := by
  exact z1l q hq id G a default
lemma realize_domFormula (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x : Fin n) :
    @Formula.Realize _ _ G.structure _ (domFormula q hq) (Fin.snoc a x) ↔ inDom q hq G a x := by
  have h := wv q hq Fin.castSucc G (Fin.snoc a x) (default : Fin 0 → Fin n)
    (pVar (Fin.last (kOf q)))
  have v1 : Fin.snoc a x ∘ Fin.castSucc = a := by funext i; simp [Fin.snoc_castSucc]
  have v0 : @Term.realize _ _ G.structure _ (Sum.elim (Fin.snoc a x) (default : Fin 0 → Fin n))
      (pVar (Fin.last (kOf q))) = x := by simp [pVar]
  rw [v1, v0] at h
  exact h
lemma realize_ltFormula (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x y : Fin n) :
    @Formula.Realize _ _ G.structure _ (ltFormula q hq) (Fin.snoc (Fin.snoc a x) y) ↔
      yv q hq G a x y := by
  have h := wt q hq (fun i => i.castSucc.castSucc) G
    (Fin.snoc (Fin.snoc a x) y) (default : Fin 0 → Fin n)
    (pVar (Fin.last (kOf q)).castSucc) (pVar (Fin.last (kOf q + 1)))
  have v0 : Fin.snoc (Fin.snoc a x) y ∘ (fun i : Fin (kOf q) => i.castSucc.castSucc) = a := by
    funext i; simp [Fin.snoc_castSucc]
  have hx : @Term.realize _ _ G.structure _
      (Sum.elim (Fin.snoc (Fin.snoc a x) y) (default : Fin 0 → Fin n))
      (pVar (Fin.last (kOf q)).castSucc) = x := by
    simp [pVar]
  have hy : @Term.realize _ _ G.structure _
      (Sum.elim (Fin.snoc (Fin.snoc a x) y) (default : Fin 0 → Fin n))
      (pVar (Fin.last (kOf q + 1))) = y := by
    simp [pVar]
  rw [v0, hx, hy] at h
  exact h
lemma realize_memFormula (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (v x : Fin n) :
    @Formula.Realize _ _ G.structure _ (memFormula q hq) (Fin.snoc (Fin.snoc a v) x) ↔
      Rrel q hq G a v x := by
  have h := z01 q hq (fun i => i.castSucc.castSucc) G
    (Fin.snoc (Fin.snoc a v) x) (default : Fin 0 → Fin n)
    (pVar (Fin.last (kOf q)).castSucc) (pVar (Fin.last (kOf q + 1)))
  have v0 : Fin.snoc (Fin.snoc a v) x ∘ (fun i : Fin (kOf q) => i.castSucc.castSucc) = a := by
    funext i; simp [Fin.snoc_castSucc]
  have hv : @Term.realize _ _ G.structure _
      (Sum.elim (Fin.snoc (Fin.snoc a v) x) (default : Fin 0 → Fin n))
      (pVar (Fin.last (kOf q)).castSucc) = v := by
    simp [pVar]
  have hx : @Term.realize _ _ G.structure _
      (Sum.elim (Fin.snoc (Fin.snoc a v) x) (default : Fin 0 → Fin n))
      (pVar (Fin.last (kOf q + 1))) = x := by
    simp [pVar]
  rw [v0, hv, hx] at h
  exact h
lemma z1d {α : Type*} [DecidableEq α] (D : Finset α)
    (lt : α → α → Prop)
    (hirr : ∀ x ∈ D, ¬ lt x x)
    (htrans : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z)
    (htrich : ∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x) :
    ∃ e : Fin D.card → α,
      (∀ i, e i ∈ D) ∧
      (∀ x ∈ D, ∃ i, e i = x) ∧
      (∀ i j : Fin D.card, i < j → lt (e i) (e j)) := by
  classical
  suffices ∀ r (D : Finset α), D.card = r →
      (∀ x ∈ D, ¬ lt x x) →
      (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z) →
      (∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x) →
      ∃ e : Fin r → α,
        (∀ i, e i ∈ D) ∧
        (∀ x ∈ D, ∃ i, e i = x) ∧
        (∀ i j : Fin r, i < j → lt (e i) (e j)) by
    exact this D.card D rfl hirr htrans htrich
  intro r
  induction r with
  | zero =>
    intro D hcard _ _ _
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun x hx => ?_, fun i => Fin.elim0 i⟩
    have hemp : D = ∅ := card_eq_zero.mp hcard
    rw [hemp] at hx; exact False.elim (notMem_empty x hx)
  | succ r ih =>
    intro D hcard hirr htrans htrich
    have hmin : ∃ m ∈ D, ∀ y ∈ D, y ≠ m → lt m y := by
      have hne : D.Nonempty := card_pos.mp (by omega)
      clear hcard ih
      induction D using Finset.induction_on with
      | empty => exact absurd hne not_nonempty_empty
      | insert a s has ihs =>
        by_cases hs : s.Nonempty
        · have v2 : ∀ x ∈ s, ¬ lt x x := fun x hx => hirr x (mem_insert_of_mem hx)
          have v1 : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, lt x y → lt y z → lt x z :=
            fun x hx y hy z hz => htrans x (mem_insert_of_mem hx)
              y (mem_insert_of_mem hy) z (mem_insert_of_mem hz)
          have v0 : ∀ x ∈ s, ∀ y ∈ s, lt x y ∨ x = y ∨ lt y x :=
            fun x hx y hy => htrich x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)
          obtain ⟨m, hm, hmless⟩ := ihs v2 v1 v0 hs
          rcases htrich a (mem_insert_self a s) m (mem_insert_of_mem hm) with hlt | heq | hgt
          · refine ⟨a, mem_insert_self a s, fun y hy hne => ?_⟩
            rcases mem_insert.mp hy with rfl | hys
            · exact absurd rfl hne
            · by_cases hym : y = m
              · rwa [hym]
              · exact htrans a (mem_insert_self a s) m (mem_insert_of_mem hm)
                  y (mem_insert_of_mem hys) hlt (hmless y hys hym)
          · exact absurd (heq ▸ hm) has
          · refine ⟨m, mem_insert_of_mem hm, fun y hy hne => ?_⟩
            rcases mem_insert.mp hy with rfl | hys
            · exact hgt
            · exact hmless y hys hne
        · rw [not_nonempty_iff_eq_empty] at hs
          subst hs
          exact ⟨a, mem_singleton_self a, fun y hy hne =>
            absurd (mem_singleton.mp hy) hne⟩
    obtain ⟨m, hmD, hmless⟩ := hmin
    let D' := D.erase m
    have hcard' : D'.card = r := by
      dsimp only [D']
      rw [card_erase_of_mem hmD, hcard]
      rfl
    have hsub : D' ⊆ D := erase_subset m D
    obtain ⟨e', he'_mem, he'_surj, he'_lt⟩ := ih D' hcard'
      (fun x hx => hirr x (hsub hx))
      (fun x hx y hy z hz => htrans x (hsub hx) y (hsub hy) z (hsub hz))
      (fun x hx y hy => htrich x (hsub hx) y (hsub hy))
    let e : Fin (r + 1) → α := Fin.cons m e'
    refine ⟨e, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases hmD (fun j => hsub (he'_mem j)) i
    · intro x hx
      by_cases hxm : x = m
      · exact ⟨0, hxm.symm⟩
      · obtain ⟨j, hj⟩ := he'_surj x (mem_erase.mpr ⟨hxm, hx⟩)
        exact ⟨j.succ, hj⟩
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (fun hij => absurd hij (lt_irrefl _)) (fun j' _ => ?_) j
        have hmem : e' j' ∈ D' := he'_mem j'
        exact hmless (e' j') (hsub hmem) (mem_erase.mp hmem).1
      · refine Fin.cases (fun hij => absurd hij (Fin.not_lt_zero _)) (fun j' hij => ?_) j
        exact he'_lt i' j' (Fin.succ_lt_succ_iff.mp hij)
noncomputable def zh (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x : Fin n) : Finset (Fin n) := by
  classical exact univ.filter (fun z : Fin n => Ax q hq G a x z)
lemma zt (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x z : Fin n) :
    z ∈ zh q hq G a x ↔ Ax q hq G a x z := by
  classical simp [zh]
noncomputable def domFinset (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) : Finset (Fin n) := by
  classical exact univ.filter (fun x : Fin n => inDom q hq G a x)
lemma mem_domFinset (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x : Fin n) :
    x ∈ domFinset q hq G a ↔ inDom q hq G a x := by
  classical simp [domFinset]
noncomputable def zc {q n : ℕ} (G : SimpleGraph (Fin n))
    (u : Fin q → Fin n) : Finset (Fin n) := by
  classical exact univ.filter (fun z : Fin n => ∀ j : Fin q, G.Adj z (u j))
lemma zl {q n : ℕ} (G : SimpleGraph (Fin n))
    (u : Fin q → Fin n) (z : Fin n) :
    z ∈ zc G u ↔ ∀ j : Fin q, G.Adj z (u j) := by
  classical simp [zc]
lemma wx (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (x y : Fin n)
    (hstep : yn q hq G a x y)
    (huniv : ∀ S ⊆ zh q hq G a x,
      ∃ v : Fin n, ∀ z ∈ zh q hq G a x, Rrel q hq G a v z ↔ z ∈ S) :
    (zh q hq G a y).card = 2 ^ (zh q hq G a x).card := by
  classical
  let AxSet := zh q hq G a x
  let AySet := zh q hq G a y
  let sig : Fin n → Finset (Fin n) := fun u => AxSet.filter (fun z => Rrel q hq G a u z)
  have hbij : AySet.card = AxSet.powerset.card := by
    refine card_bij (fun u _ => sig u) ?_ ?_ ?_
    · intro u _
      exact mem_powerset.mpr (filter_subset _ _)
    · intro u₁ hu₁ u₂ hu₂ hsig
      by_contra hne
      have h1 : Ax q hq G a y u₁ := (zt q hq G a y u₁).mp hu₁
      have h2 : Ax q hq G a y u₂ := (zt q hq G a y u₂).mp hu₂
      obtain ⟨z, hzx, hdiff⟩ := hstep.1 u₁ u₂ h1 h2 hne
      have v1 : z ∈ AxSet := (zt q hq G a x z).mpr hzx
      have v0 : z ∈ sig u₁ ↔ z ∈ sig u₂ := by rw [hsig]
      simp only [sig, mem_filter, v1, true_and] at v0
      exact hdiff v0
    · intro S hS
      obtain ⟨v, hv⟩ := huniv S (mem_powerset.mp hS)
      obtain ⟨u, huy, huv⟩ := hstep.2 v
      refine ⟨u, (zt q hq G a y u).mpr huy, ?_⟩
      ext z
      simp only [sig, mem_filter]
      constructor
      · rintro ⟨hz, hR⟩
        exact (hv z hz).mp ((huv z ((zt q hq G a x z).mp hz)).mp hR)
      · intro hzS
        have hz : z ∈ AxSet := (mem_powerset.mp hS) hzS
        exact ⟨hz, (huv z ((zt q hq G a x z).mp hz)).mpr ((hv z hz).mpr hzS)⟩
  rw [hbij, card_powerset]
def EventE1 (q : ℕ) (n K : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∀ u : Fin q → Fin n, Function.Injective u → (zc G u).card < K}
def EventE2 (q : ℕ) (hq : 2 ≤ q) (n m : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∀ a : Fin (kOf q) → Fin n, Function.Injective a →
    (∀ x : Fin n, ¬ zs q a x →
      (zh q hq G a x).card ≤ zd (m - 1) →
      ∀ S ⊆ zh q hq G a x,
        ∃ v : Fin n, ∀ z ∈ zh q hq G a x, Rrel q hq G a v z ↔ z ∈ S) ∧
    ((domFinset q hq G a).card ≤ zd (m - 1) →
      ∀ S ⊆ domFinset q hq G a,
        ∃ v : Fin n, ∀ x ∈ domFinset q hq G a, Rrel q hq G a v x ↔ x ∈ S)}
def EventE3 (q : ℕ) (hq : 2 ≤ q) (n m : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∀ a : Fin (kOf q) → Fin n, Function.Injective a →
    ∀ x : Fin n, ¬ zs q a x →
      (zh q hq G a x).card ≤ zd (m - 2) →
      ∃ y : Fin n, ¬ zs q a y ∧ yn q hq G a x y}
theorem card_eq_m_of_events (q : ℕ) (hq : 2 ≤ q) {n m K : ℕ}
    (hm : 2 ≤ m) (hK : K ≤ zd m)
    {G : SimpleGraph (Fin n)}
    (hE1 : G ∈ EventE1 q n K)
    (hE2 : G ∈ EventE2 q hq n m)
    (hE3 : G ∈ EventE3 q hq n m)
    (a : Fin (kOf q) → Fin n) (D : Finset (Fin n))
    (hvalid : ws q hq G a)
    (hD : ∀ x : Fin n, x ∈ D ↔ inDom q hq G a x) :
    D.card = m ∧
    (∀ S ⊆ D, ∃ v : Fin n, ∀ x ∈ D, Rrel q hq G a v x ↔ x ∈ S) := by
  classical
  rcases hvalid with ⟨hinj, ⟨x₀, hx₀⟩, htrich, hbase, hstep, hstop⟩
  have vn : D = domFinset q hq G a := by
    ext x; rw [hD, mem_domFinset]
  have vo : 0 < D.card := card_pos.mpr ⟨x₀, (hD x₀).mpr hx₀⟩
  obtain ⟨e, he_mem, he_surj, he_lt⟩ := z1d D (yv q hq G a)
    (fun x _ => ltRel_irrefl q hq G a x)
    (fun _ _ _ _ _ _ h1 h2 => ltRel_trans q hq G a h1 h2)
    (fun x hx y hy => htrich x y ((hD x).mp hx) ((hD y).mp hy))
  have v2 : ∀ i j : Fin D.card, yv q hq G a (e i) (e j) ↔ i < j := by
    intro i j
    constructor
    · intro hlt
      by_contra hle
      rcases lt_or_eq_of_le (not_lt.mp hle) with hji | heq
      · exact ltRel_irrefl q hq G a (e i) (ltRel_trans q hq G a hlt (he_lt j i hji))
      · rw [heq] at hlt
        exact ltRel_irrefl q hq G a (e i) hlt
    · exact he_lt i j
  have v5 : ∀ i : Fin D.card, (zh q hq G a (e i)).card < zd m := by
    intro i
    have vj : inDom q hq G a (e i) := (hD (e i)).mp (he_mem i)
    have v3 : ¬ zs q a (e i) := vj.2.2
    let u : Fin q → Fin n := fun j =>
      if hj : j.val < q - 1 then yc q hq a ⟨j.val, hj⟩ else e i
    have vi : Function.Injective u := by
      intro j₁ j₂ heq
      by_cases h1 : j₁.val < q - 1 <;> by_cases h2 : j₂.val < q - 1
      · simp only [u, h1, h2, ↓reduceDIte] at heq
        have hidx := hinj heq
        have hv : j₁.val = j₂.val := congrArg (Fin.val : Fin (kOf q) → ℕ) hidx
        exact Fin.ext hv
      · simp only [u, h1, h2, ↓reduceDIte] at heq
        exact False.elim (v3 ⟨cIdx q hq ⟨j₁.val, h1⟩, heq.symm⟩)
      · simp only [u, h1, h2, ↓reduceDIte] at heq
        exact False.elim (v3 ⟨cIdx q hq ⟨j₂.val, h2⟩, heq⟩)
      · exact Fin.ext (by omega)
    have hsub : zh q hq G a (e i) ⊆ zc G u := by
      intro z hz
      rcases (zt q hq G a (e i) z).mp hz with ⟨hbc, hadj, _⟩
      rw [zl]
      intro j
      dsimp only [u]
      split_ifs with hj
      · exact hbc ⟨j.val, hj⟩
      · exact hadj
    exact lt_of_le_of_lt (card_le_card hsub) (lt_of_lt_of_le (hE1 u vi) hK)
  have vc : ∀ (i : ℕ) (hiD : i < D.card) (him : i < m),
      (zh q hq G a (e ⟨i, hiD⟩)).card = zd i := by
    intro i
    induction i with
    | zero =>
      intro hiD _
      have hmin : ∀ y : Fin n, inDom q hq G a y → ¬ yv q hq G a y (e ⟨0, hiD⟩) := by
        intro y hy
        obtain ⟨j, rfl⟩ := he_surj y ((hD y).mpr hy)
        rw [v2]
        simp only [Fin.lt_def]
        omega
      obtain ⟨z₀, hz₀, huniq⟩ := hbase (e ⟨0, hiD⟩) ((hD _).mp (he_mem ⟨0, hiD⟩)) hmin
      have hset : zh q hq G a (e ⟨0, hiD⟩) = {z₀} := by
        ext z
        rw [zt, mem_singleton]
        exact ⟨huniq z, fun h => h ▸ hz₀⟩
      rw [hset, card_singleton]; rfl
    | succ i ih =>
      intro hiD him
      have hiD' : i < D.card := by omega
      have him' : i < m := by omega
      have vg := ih hiD' him'
      have ve : (zh q hq G a (e ⟨i, hiD'⟩)).card ≤ zd (m - 1) := by
        rw [vg]; exact y6 (by omega)
      have v3 : ¬ zs q a (e ⟨i, hiD'⟩) := ((hD _).mp (he_mem ⟨i, hiD'⟩)).2.2
      have va := (hE2 a hinj).1 (e ⟨i, hiD'⟩) v3 ve
      have vb : z04 q hq G a (e ⟨i, hiD'⟩) (e ⟨i + 1, hiD⟩) := by
        refine ⟨(hD _).mp (he_mem ⟨i, hiD'⟩), (hD _).mp (he_mem ⟨i + 1, hiD⟩),
          he_lt ⟨i, hiD'⟩ ⟨i + 1, hiD⟩ (by simp [Fin.lt_def]), ?_⟩
        intro z hz ⟨h1, h2⟩
        obtain ⟨j, rfl⟩ := he_surj z ((hD z).mpr hz)
        rw [v2] at h1 h2
        simp [Fin.lt_def] at h1 h2
        omega
      have vm := wx q hq G a (e ⟨i, hiD'⟩) (e ⟨i + 1, hiD⟩) (hstep _ _ vb) va
      rw [vm, vg]; rfl
  have v8 : D.card = m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    ·
      have v1 : D.card - 1 < D.card := by omega
      have vf : D.card - 1 < m := by omega
      have v9 := vc (D.card - 1) v1 vf
      have vd : (zh q hq G a (e ⟨D.card - 1, v1⟩)).card ≤ zd (m - 2) := by
        rw [v9]; exact y6 (by omega)
      have v6 : inDom q hq G a (e ⟨D.card - 1, v1⟩) :=
        (hD _).mp (he_mem ⟨D.card - 1, v1⟩)
      have hmax : ∀ y : Fin n, inDom q hq G a y →
          ¬ yv q hq G a (e ⟨D.card - 1, v1⟩) y := by
        intro y hy
        obtain ⟨j, rfl⟩ := he_surj y ((hD y).mpr hy)
        rw [v2]
        simp only [Fin.lt_def]
        omega
      exact hstop _ v6 hmax (hE3 a hinj _ v6.2.2 vd)
    ·
      have v0 : m - 1 < D.card := by omega
      have vl : m - 1 < m := by omega
      have v7 := vc (m - 1) v0 vl
      have v3 : ¬ zs q a (e ⟨m - 1, v0⟩) := ((hD _).mp (he_mem ⟨m - 1, v0⟩)).2.2
      have va := (hE2 a hinj).1 (e ⟨m - 1, v0⟩) v3 (le_of_eq v7)
      have vb : z04 q hq G a (e ⟨m - 1, v0⟩) (e ⟨m, hgt⟩) := by
        refine ⟨(hD _).mp (he_mem ⟨m - 1, v0⟩), (hD _).mp (he_mem ⟨m, hgt⟩),
          he_lt ⟨m - 1, v0⟩ ⟨m, hgt⟩ (by simp [Fin.lt_def]; omega), ?_⟩
        intro z hz ⟨h1, h2⟩
        obtain ⟨j, rfl⟩ := he_surj z ((hD z).mpr hz)
        rw [v2] at h1 h2
        simp [Fin.lt_def] at h1 h2
        omega
      have v4 := wx q hq G a (e ⟨m - 1, v0⟩) (e ⟨m, hgt⟩) (hstep _ _ vb) va
      rw [v7] at v4
      have htm : 2 ^ zd (m - 1) = zd m := by
        have vk : m = (m - 1) + 1 := by omega
        conv_rhs => rw [vk]
        rfl
      rw [htm] at v4
      exact lt_irrefl (zd m) (v4 ▸ v5 ⟨m, hgt⟩)
  refine ⟨v8, ?_⟩
  have vh : D.card ≤ zd (m - 1) := v8 ▸ y9 m hm
  rw [vn] at vh ⊢
  exact (hE2 a hinj).2 vh
end
section
open scoped BigOperators
open Finset Real Nat
lemma z2g {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (idx : Finset κ) (T : κ → Finset ι)
    (hdisj : Set.PairwiseDisjoint (idx : Set κ) T)
    (p : ℝ) (P : κ → (ι → Bool) → Prop) [∀ k, DecidablePred (P k)]
    (hdep : ∀ k ∈ idx, ∀ f g : ι → Bool, (∀ i ∈ T k, f i = g i) → (P k f ↔ P k g))
    (t : ℝ) :
    (∑ f : ι → Bool, (∏ i : ι, z9 p (f i)) *
      exp (t * ∑ k ∈ idx, if P k f then (1 : ℝ) else 0)) =
    ∏ k ∈ idx, (z4 p (P k) * exp t + (1 - z4 p (P k))) := by
  classical
  induction idx using Finset.induction_on with
  | empty =>
    simp only [sum_empty, mul_zero, exp_zero, mul_one, prod_empty]
    exact y4 p
  | insert a s has ih =>
    have v3 : Set.PairwiseDisjoint (s : Set κ) T :=
      hdisj.subset (subset_insert a s)
    have v4 : Disjoint (T a) (s.biUnion T) := by
      rw [disjoint_biUnion_right]
      intro k hk
      exact hdisj (mem_insert_self a s) (mem_insert_of_mem hk) (fun h => has (h ▸ hk))
    have v1 : ∀ k ∈ s, ∀ f g : ι → Bool, (∀ i ∈ T k, f i = g i) → (P k f ↔ P k g) :=
      fun k hk => hdep k (mem_insert_of_mem hk)
    rw [prod_insert has, ← ih v3 v1]
    rw [← Equiv.sum_comp (zw (T a)).symm, Fintype.sum_prod_type]
    have hPa : ∀ f₁ f₂, P a (z0 (T a) f₁ f₂) ↔ P a (z0 (T a) f₁ (fun _ => false)) :=
      fun f₁ f₂ => hdep a (mem_insert_self a s) _ _ (fun i hi => by simp [z0, hi])
    have hPs : ∀ k ∈ s, ∀ f₁ f₂,
        P k (z0 (T a) f₁ f₂) ↔ P k (z0 (T a) (fun _ => false) f₂) := by
      intro k hk f₁ f₂
      refine v1 k hk _ _ fun i hi => ?_
      have hnot : i ∉ T a := disjoint_right.mp v4 (mem_biUnion.mpr ⟨k, hk, hi⟩)
      simp [z0, hnot]
    have hrew : ∀ f₁ f₂,
        (∏ i : ι, z9 p ((zw (T a)).symm (f₁, f₂) i)) *
          exp (t * ∑ k ∈ insert a s, if P k ((zw (T a)).symm (f₁, f₂)) then (1 : ℝ) else 0) =
        ((∏ x : {i // i ∈ T a}, z9 p (f₁ x)) *
          exp (t * if P a (z0 (T a) f₁ (fun _ => false)) then 1 else 0)) *
        ((∏ x : {i // i ∉ T a}, z9 p (f₂ x)) *
          exp (t * ∑ k ∈ s, if P k (z0 (T a) (fun _ => false) f₂) then 1 else 0)) := by
      intro f₁ f₂
      change (∏ i : ι, z9 p (z0 (T a) f₁ f₂ i)) *
          exp (t * ∑ k ∈ insert a s, if P k (z0 (T a) f₁ f₂) then (1 : ℝ) else 0) = _
      rw [y7, sum_insert has, mul_add, exp_add]
      have v2 : (if P a (z0 (T a) f₁ f₂) then (1 : ℝ) else 0) =
          if P a (z0 (T a) f₁ (fun _ => false)) then 1 else 0 := by
        by_cases h : P a (z0 (T a) f₁ (fun _ => false))
        · rw [if_pos ((hPa f₁ f₂).mpr h), if_pos h]
        · rw [if_neg (fun h' => h ((hPa f₁ f₂).mp h')), if_neg h]
      have v0 : (∑ k ∈ s, if P k (z0 (T a) f₁ f₂) then (1 : ℝ) else 0) =
          ∑ k ∈ s, if P k (z0 (T a) (fun _ => false) f₂) then 1 else 0 :=
        sum_congr rfl fun k hk => by
          by_cases h : P k (z0 (T a) (fun _ => false) f₂)
          · rw [if_pos ((hPs k hk f₁ f₂).mpr h), if_pos h]
          · rw [if_neg (fun h' => h ((hPs k hk f₁ f₂).mp h')), if_neg h]
      rw [v2, v0]; ring
    rw [sum_congr rfl fun f₁ _ => sum_congr rfl fun f₂ _ => hrew f₁ f₂]
    simp_rw [← mul_sum, ← sum_mul]
    congr 1
    · let pa := z4 p (P a)
      have hpa : pa = ∑ f₁ : {i // i ∈ T a} → Bool,
          if P a (z0 (T a) f₁ (fun _ => false)) then
            ∏ x : {i // i ∈ T a}, z9 p (f₁ x) else 0 := by
        have h := w2 (T a) p (P a) (hdep a (mem_insert_self a s))
        unfold z4 at h
        dsimp only [pa, z4]
        convert h
      have htot : (∑ f₁ : {i // i ∈ T a} → Bool, ∏ x : {i // i ∈ T a}, z9 p (f₁ x)) = 1 :=
        y4 p
      have h1 : ∀ f₁ : {i // i ∈ T a} → Bool,
          (∏ x : {i // i ∈ T a}, z9 p (f₁ x)) *
            exp (t * if P a (z0 (T a) f₁ (fun _ => false)) then 1 else 0) =
          (if P a (z0 (T a) f₁ (fun _ => false)) then
            ∏ x : {i // i ∈ T a}, z9 p (f₁ x) else 0) * exp t +
          ((∏ x : {i // i ∈ T a}, z9 p (f₁ x)) -
            if P a (z0 (T a) f₁ (fun _ => false)) then
              ∏ x : {i // i ∈ T a}, z9 p (f₁ x) else 0) := by
        intro f₁
        by_cases h : P a (z0 (T a) f₁ (fun _ => false)) <;> simp [h]
      simp_rw [h1]
      rw [sum_add_distrib, ← sum_mul, sum_sub_distrib, htot, ← hpa]
    · have h2 : (∑ f : ι → Bool, (∏ i : ι, z9 p (f i)) *
          exp (t * ∑ k ∈ s, if P k f then (1 : ℝ) else 0)) =
          ∑ f₂ : {i // i ∉ T a} → Bool, (∏ x : {i // i ∉ T a}, z9 p (f₂ x)) *
            exp (t * ∑ k ∈ s, if P k (z0 (T a) (fun _ => false) f₂) then 1 else 0) := by
        rw [← Equiv.sum_comp (zw (T a)).symm, Fintype.sum_prod_type]
        have v5 : ∀ f₁ f₂,
            (∏ i : ι, z9 p ((zw (T a)).symm (f₁, f₂) i)) *
              exp (t * ∑ k ∈ s, if P k ((zw (T a)).symm (f₁, f₂)) then (1 : ℝ) else 0) =
            (∏ x : {i // i ∈ T a}, z9 p (f₁ x)) *
              ((∏ x : {i // i ∉ T a}, z9 p (f₂ x)) *
                exp (t * ∑ k ∈ s, if P k (z0 (T a) (fun _ => false) f₂) then 1 else 0)) := by
          intro f₁ f₂
          change (∏ i : ι, z9 p (z0 (T a) f₁ f₂ i)) *
              exp (t * ∑ k ∈ s, if P k (z0 (T a) f₁ f₂) then (1 : ℝ) else 0) = _
          rw [y7]
          have v0 : (∑ k ∈ s, if P k (z0 (T a) f₁ f₂) then (1 : ℝ) else 0) =
              ∑ k ∈ s, if P k (z0 (T a) (fun _ => false) f₂) then 1 else 0 :=
            sum_congr rfl fun k hk => by
              by_cases h : P k (z0 (T a) (fun _ => false) f₂)
              · rw [if_pos ((hPs k hk f₁ f₂).mpr h), if_pos h]
              · rw [if_neg (fun h' => h ((hPs k hk f₁ f₂).mp h')), if_neg h]
          rw [v0]; ring
        rw [sum_congr rfl fun f₁ _ => sum_congr rfl fun f₂ _ => v5 f₁ f₂]
        simp_rw [← mul_sum, ← sum_mul]
        rw [y4, one_mul]
      exact h2.symm
lemma ww {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (idx : Finset κ) (T : κ → Finset ι)
    (hdisj : Set.PairwiseDisjoint (idx : Set κ) T)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : κ → (ι → Bool) → Prop) [∀ k, DecidablePred (P k)]
    (hdep : ∀ k ∈ idx, ∀ f g : ι → Bool, (∀ i ∈ T k, f i = g i) → (P k f ↔ P k g))
    {r : ℝ}
    (hprob : ∀ k ∈ idx, z4 p (P k) ≤ r) :
    z4 p (fun f : ι → Bool =>
      2 * ((idx.card : ℝ) * r) < ((idx.filter (fun k => P k f)).card : ℝ)) ≤
      exp (-((idx.card : ℝ) * r) / 3) := by
  classical
  unfold z4
  let t : ℝ := 1 / 2
  have h1 : (∑ f : ι → Bool,
      if 2 * ((idx.card : ℝ) * r) < ((idx.filter (fun k => P k f)).card : ℝ) then
        ∏ i : ι, z9 p (f i) else 0) * exp ((idx.card : ℝ) * r) ≤
      (∑ f : ι → Bool, (∏ i : ι, z9 p (f i)) *
        exp (t * ∑ k ∈ idx, if P k f then (1 : ℝ) else 0)) := by
    rw [sum_mul]
    refine sum_le_sum fun f _ => ?_
    have hw : 0 ≤ ∏ i : ι, z9 p (f i) := prod_nonneg fun _ _ => yh hp0 hp1 _
    split_ifs with hgt
    · refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) hw
      have hcnt : (∑ k ∈ idx, if P k f then (1 : ℝ) else 0) =
          ((idx.filter (fun k => P k f)).card : ℝ) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      rw [hcnt]; simp only [t]; linarith
    · rw [zero_mul]
      exact mul_nonneg hw (exp_pos _).le
  rw [z2g idx T hdisj p P hdep t] at h1
  have v2 : exp t ≤ 1 + 2 / 3 := z0s
  have v1 : 1 ≤ exp t := by
    have : 0 ≤ t := by norm_num [t]
    linarith [Real.add_one_le_exp t]
  have v0 : (∏ k ∈ idx, (z4 p (P k) * exp t + (1 - z4 p (P k)))) ≤
      exp ((2 / 3) * ((idx.card : ℝ) * r)) := by
    calc ∏ k ∈ idx, (z4 p (P k) * exp t + (1 - z4 p (P k)))
        ≤ ∏ _k ∈ idx, exp ((2 / 3) * r) := by
          refine prod_le_prod (fun k _ => ?_) (fun k hk => ?_)
          · have hpk0 : 0 ≤ z4 p (P k) := ym hp0 hp1 (P k)
            have hpk1 : z4 p (P k) ≤ 1 := by
              have h := zi hp0 hp1 (P := P k) (Q := fun _ => True) (fun _ _ => trivial)
              rwa [z0b] at h
            nlinarith
          · have hpk := hprob k hk
            have hpk0 : 0 ≤ z4 p (P k) := ym hp0 hp1 (P k)
            have hlin : z4 p (P k) * exp t + (1 - z4 p (P k)) ≤
                ((2 / 3) * r) + 1 := by nlinarith
            exact hlin.trans (Real.add_one_le_exp _)
      _ = (exp ((2 / 3) * r)) ^ idx.card := prod_const _
      _ = exp ((idx.card : ℝ) * ((2 / 3) * r)) := (exp_nat_mul _ _).symm
      _ = exp ((2 / 3) * ((idx.card : ℝ) * r)) := by congr 1; ring
  have h2 := h1.trans v0
  rw [← le_div_iff₀ (exp_pos _), ← exp_sub] at h2
  calc (∑ f : ι → Bool,
          if 2 * ((idx.card : ℝ) * r) < ((idx.filter (fun k => P k f)).card : ℝ) then
            ∏ i : ι, z9 p (f i) else 0)
      ≤ exp ((2 / 3) * ((idx.card : ℝ) * r) - (idx.card : ℝ) * r) := h2
    _ = exp (-((idx.card : ℝ) * r) / 3) := by congr 1; ring
def EOf (m : ℕ) : ℕ := zd (m - 1) ^ 10
def R8Of (m : ℕ) : ℕ := 2 ^ EOf m
def R4Of (m : ℕ) : ℕ := 2 ^ (2 * EOf m)
def R2Of (m : ℕ) : ℕ := 2 ^ (4 * EOf m)
def ROf (m : ℕ) : ℕ := 2 ^ (8 * EOf m)
def nOf (q m : ℕ) : ℕ := 2 ^ (8 * q * EOf m)
def KOf (q m : ℕ) : ℕ := 8 * q ^ 2 * EOf m
lemma z1r (m : ℕ) : R4Of m = R8Of m ^ 2 := by
  simp only [R4Of, R8Of, ← pow_mul, mul_comm]
lemma z2f (m : ℕ) : R2Of m = R4Of m ^ 2 := by
  simp only [R2Of, R4Of, ← pow_mul]; congr 1; ring
lemma z15 (m : ℕ) : ROf m = R2Of m ^ 2 := by
  simp only [ROf, R2Of, ← pow_mul]; congr 1; ring
lemma wz (m : ℕ) : ROf m = R4Of m ^ 4 := by
  simp only [ROf, R4Of, ← pow_mul]; congr 1; ring
lemma zq (m : ℕ) : ROf m = R8Of m ^ 8 := by
  simp only [ROf, R8Of, ← pow_mul]; congr 1; ring
lemma w5 (q m : ℕ) : nOf q m = ROf m ^ q := by
  simp only [nOf, ROf, ← pow_mul]; congr 1; ring
lemma z2a (q m : ℕ) : nOf q m ^ q = 2 ^ KOf q m := by
  simp only [nOf, KOf, ← pow_mul]; congr 1; ring
lemma R_pos (m : ℕ) : 0 < ROf m := Nat.two_pow_pos _
lemma z1e (m : ℕ) : 0 < R8Of m := Nat.two_pow_pos _
lemma wq (q m : ℕ) : 0 < nOf q m := Nat.two_pow_pos _
lemma nOf_rpow_neg_inv (q m : ℕ) (hq : 2 ≤ q) :
    ((nOf q m : ℝ) ^ (-((1 : ℝ) / (q : ℝ)))) = ((ROf m : ℝ))⁻¹ := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hR0 : (0 : ℝ) ≤ (ROf m : ℝ) := Nat.cast_nonneg _
  rw [w5 q m, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hR0]
  have hexp : (q : ℝ) * -((1 : ℝ) / (q : ℝ)) = -1 := by field_simp
  rw [hexp, Real.rpow_neg_one]
lemma z07 (k : ℕ) (hk : 4 ≤ k) :
    4 ^ (k - 3) ≤ k.factorial := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 4 := ⟨k - 4, by omega⟩
  induction r with
  | zero => norm_num [Nat.factorial]
  | succ r ih =>
    have h1 : 4 ^ (r + 1) ≤ (r + 4).factorial := ih (by omega)
    have h2 : r + 1 + 4 - 3 = (r + 1) + 1 := by omega
    rw [h2, pow_succ, show r + 1 + 4 = (r + 4) + 1 by omega, Nat.factorial_succ]
    calc 4 ^ (r + 1) * 4 ≤ (r + 4).factorial * 4 := Nat.mul_le_mul_right 4 h1
      _ ≤ (r + 4).factorial * (r + 4 + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (r + 4 + 1) * (r + 4).factorial := Nat.mul_comm _ _
lemma z0g (k : ℕ) (hk : 4 ≤ k) :
    ((2 : ℝ) ^ k) / (k.factorial : ℝ) ≤ 64 / ((2 : ℝ) ^ k) := by
  have hfac : ((4 : ℝ) ^ (k - 3)) ≤ (k.factorial : ℝ) := by
    exact_mod_cast z07 k hk
  have v0 : (0 : ℝ) < (4 : ℝ) ^ (k - 3) := by positivity
  have v1 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  calc ((2 : ℝ) ^ k) / (k.factorial : ℝ)
      ≤ ((2 : ℝ) ^ k) / ((4 : ℝ) ^ (k - 3)) := div_le_div_of_nonneg_left v1.le v0 hfac
    _ = 64 / ((2 : ℝ) ^ k) := by
        rw [div_eq_div_iff v0.ne' v1.ne']
        have h4 : (4 : ℝ) ^ (k - 3) * 64 = (4 : ℝ) ^ k := by
          have hk3 : k - 3 + 3 = k := by omega
          calc (4 : ℝ) ^ (k - 3) * 64 = (4 : ℝ) ^ (k - 3) * (4 : ℝ) ^ 3 := by norm_num
            _ = (4 : ℝ) ^ (k - 3 + 3) := (pow_add _ _ _).symm
            _ = (4 : ℝ) ^ k := by rw [hk3]
        have h24 : (2 : ℝ) ^ k * (2 : ℝ) ^ k = (4 : ℝ) ^ k := by
          rw [← mul_pow]; norm_num
        linarith
lemma z13 (c : ℕ) : ∃ T₀ : ℕ, ∀ T ≥ T₀, c * T ^ 10 ≤ 2 ^ T := by
  have v4 : ∀ r : ℕ, (2 * r + 140) ^ 10 ≤ 2 ^ (r + 72) := by
    intro r
    induction r with
    | zero => norm_num
    | succ r ih =>
      have v1 : (2 * r + 142) ^ 10 ≤ 2 * (2 * r + 140) ^ 10 := by
        have h142 : 142 ^ 10 ≤ 2 * 140 ^ 10 := by norm_num
        have hmul : (2 * r + 142) * 140 ≤ 142 * (2 * r + 140) := by omega
        have v0 : ((2 * r + 142) * 140) ^ 10 ≤ (142 * (2 * r + 140)) ^ 10 :=
          Nat.pow_le_pow_left hmul 10
        rw [mul_pow, mul_pow] at v0
        have v3 : (2 * r + 142) ^ 10 * 140 ^ 10 ≤ (2 * (2 * r + 140) ^ 10) * 140 ^ 10 := by
          calc (2 * r + 142) ^ 10 * 140 ^ 10
              ≤ 142 ^ 10 * (2 * r + 140) ^ 10 := v0
            _ ≤ (2 * 140 ^ 10) * (2 * r + 140) ^ 10 := Nat.mul_le_mul_right _ h142
            _ = (2 * (2 * r + 140) ^ 10) * 140 ^ 10 := by ring
        exact Nat.le_of_mul_le_mul_right v3 (by norm_num)
      calc (2 * (r + 1) + 140) ^ 10 = (2 * r + 142) ^ 10 := by ring_nf
        _ ≤ 2 * (2 * r + 140) ^ 10 := v1
        _ ≤ 2 * 2 ^ (r + 72) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (r + 1 + 72) := by rw [← _root_.pow_succ']
  refine ⟨2 * c + 146, fun T hT => ?_⟩
  set r := (T - 140) / 2 + 1
  have hTr : T ≤ 2 * r + 140 := by omega
  have v5 : r + 72 + c ≤ T := by omega
  have v2 : c ≤ 2 ^ c := Nat.le_of_lt Nat.lt_two_pow_self
  calc c * T ^ 10
      ≤ 2 ^ c * (2 * r + 140) ^ 10 := Nat.mul_le_mul v2 (Nat.pow_le_pow_left hTr 10)
    _ ≤ 2 ^ c * 2 ^ (r + 72) := Nat.mul_le_mul_left _ (v4 r)
    _ = 2 ^ (c + (r + 72)) := (pow_add 2 c (r + 72)).symm
    _ ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) (by omega)
lemma z11 (x : ℝ) (n : ℕ) (hxn : 2 * x ≤ (n : ℝ)) :
    exp x ≤ (2 : ℝ) ^ n := by
  have he2 : exp (1 / 2 : ℝ) ≤ 2 := by linarith [z0s]
  calc exp x ≤ exp ((n : ℝ) * (1 / 2 : ℝ)) := exp_le_exp.mpr (by linarith)
    _ = (exp (1 / 2 : ℝ)) ^ n := by rw [← exp_nat_mul]
    _ ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (exp_pos _).le he2 n
lemma z1t (n : ℕ) : (2 : ℝ) ^ n ≤ exp (n : ℝ) := by
  have h2e : (2 : ℝ) ≤ exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (2 : ℝ) ^ n ≤ (exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h2e n
    _ = exp (n : ℝ) := by rw [← exp_nat_mul, mul_one]
lemma z0a (a : ℝ) (N : ℕ) (ha : (N : ℝ) ≤ a) :
    exp (-a) ≤ ((2 : ℝ) ^ N)⁻¹ := by
  rw [exp_neg]
  exact inv_anti₀ (by positivity) ((z1t N).trans (exp_le_exp.mpr ha))
structure LargeParams (q m : ℕ) : Prop where
  hm : 10 ≤ m
  hT_ge : 1000 * q ^ 2 ≤ zd (m - 1)
  hK_le_tower : KOf q m ≤ zd m
  hK_ge : 100 ≤ KOf q m
  hR8_ge : 10000 ≤ R8Of m
  hn_ge_params : 100 * (kOf q + 10) ≤ nOf q m
  hK_le_R8 : KOf q m + kOf q + 10 ≤ R8Of m
  hT_pow_le_E : 1000 * (q + m + zd (m - 1) ^ 3 + 100) ≤ EOf m
  hR_le_n : 100 * (zd (m - 1) + 10) * ROf m ≤ nOf q m
  hexp_T_le_R8 : exp (20 * (m : ℝ) * (zd (m - 1) : ℝ) ^ 2 + 100) ≤ (R8Of m : ℝ)
  hpoly_exp_R8 : ((nOf q m : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (zd (m - 1) + 10) *
      exp (-((R8Of m : ℝ)) / 64) ≤ 1 / 256
  hpoly_exp_R2 : ((nOf q m : ℝ) ^ (kOf q + 4)) *
      exp (-((R2Of m : ℝ)) / 64) ≤ 1 / 256
  hsubset_exp_R8 : ((2 * (ROf m : ℝ) + 1) ^ (zd (m - 1) + 1)) * (2 : ℝ) ^ (zd (m - 1) + 10) *
      exp (-((R8Of m : ℝ)) / 64) ≤ 1 / 256
lemma z2c : ∀ i : ℕ, i ≤ zd i := by
  intro i
  induction i with
  | zero => simp [zd]
  | succ i ih =>
    have hlt : zd i < zd (i + 1) := wo (Nat.lt_succ_self i)
    omega
lemma z0v : ∀ x : ℕ, 10 ≤ x → x * x ≤ 2 ^ x := by
  intro x hx
  obtain ⟨r, rfl⟩ : ∃ r, x = r + 10 := ⟨x - 10, by omega⟩
  induction r with
  | zero => norm_num
  | succ r ih =>
    have v0 : (r + 11) * (r + 11) ≤ 2 * ((r + 10) * (r + 10)) := by nlinarith
    calc (r + 1 + 10) * (r + 1 + 10) = (r + 11) * (r + 11) := by ring
      _ ≤ 2 * ((r + 10) * (r + 10)) := v0
      _ ≤ 2 * 2 ^ (r + 10) := Nat.mul_le_mul_left 2 (ih (by omega))
      _ = 2 ^ (r + 1 + 10) := by rw [← _root_.pow_succ']
lemma z0q (q m : ℕ)
    (hR8_huge : (8 * q * EOf m * (kOf q + 4) + (8 * EOf m + 2) * (zd (m - 1) + 1) +
        zd (m - 1) + 20) * 64 ≤ R8Of m) :
    ((nOf q m : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (zd (m - 1) + 10) *
      exp (-((R8Of m : ℝ)) / 64) ≤ 1 / 256 ∧
    ((nOf q m : ℝ) ^ (kOf q + 4)) * exp (-((R2Of m : ℝ)) / 64) ≤ 1 / 256 ∧
    ((2 * (ROf m : ℝ) + 1) ^ (zd (m - 1) + 1)) * (2 : ℝ) ^ (zd (m - 1) + 10) *
      exp (-((R8Of m : ℝ)) / 64) ≤ 1 / 256 := by
  set T := zd (m - 1)
  set E := EOf m
  have hdom : ∀ A : ℕ, (A + 8) * 64 ≤ R8Of m →
      ((2 : ℝ) ^ A) * exp (-((R8Of m : ℝ)) / 64) ≤ 1 / 256 := by
    intro A hA
    have h1 : exp (-((R8Of m : ℝ)) / 64) ≤ ((2 : ℝ) ^ (A + 8))⁻¹ := by
      have v6 : ((A + 8 : ℕ) : ℝ) ≤ (R8Of m : ℝ) / 64 := by
        rw [le_div_iff₀ (by norm_num)]
        exact_mod_cast hA
      rw [show -((R8Of m : ℝ)) / 64 = -((R8Of m : ℝ) / 64) by ring]
      exact z0a ((R8Of m : ℝ) / 64) (A + 8) v6
    calc ((2 : ℝ) ^ A) * exp (-((R8Of m : ℝ)) / 64)
        ≤ ((2 : ℝ) ^ A) * ((2 : ℝ) ^ (A + 8))⁻¹ := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / 256 := by
          rw [pow_add]
          have hpos : (2 : ℝ) ^ A ≠ 0 := by positivity
          field_simp
          norm_num
  have v0 : ((nOf q m : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (T + 10) *
      exp (-((R8Of m : ℝ)) / 64) ≤ 1 / 256 := by
    have hrew : ((nOf q m : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (T + 10) =
        (2 : ℝ) ^ (8 * q * E * (kOf q + 4) + (T + 10)) := by
      change (((2 ^ (8 * q * E) : ℕ) : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (T + 10) = _
      rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add]
    rw [hrew]
    refine hdom _ ?_
    have hle : 8 * q * E * (kOf q + 4) + (T + 10) + 8 ≤
        8 * q * E * (kOf q + 4) + (8 * E + 2) * (T + 1) + T + 20 := by omega
    exact le_trans (Nat.mul_le_mul_right 64 hle) hR8_huge
  have v2 : ((nOf q m : ℝ) ^ (kOf q + 4)) * exp (-((R2Of m : ℝ)) / 64) ≤ 1 / 256 := by
    have v5 : (R8Of m : ℝ) ≤ (R2Of m : ℝ) := by
      have : R8Of m ≤ R2Of m := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this
    have hexp : exp (-((R2Of m : ℝ)) / 64) ≤ exp (-((R8Of m : ℝ)) / 64) :=
      exp_le_exp.mpr (by linarith)
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (T + 10) := by
      exact_mod_cast Nat.one_le_pow (T + 10) 2 (by norm_num)
    have hnn : 0 ≤ ((nOf q m : ℝ) ^ (kOf q + 4)) := by positivity
    have v4 : 0 ≤ exp (-((R2Of m : ℝ)) / 64) := (exp_pos _).le
    calc ((nOf q m : ℝ) ^ (kOf q + 4)) * exp (-((R2Of m : ℝ)) / 64)
        ≤ ((nOf q m : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (T + 10) *
            exp (-((R2Of m : ℝ)) / 64) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hnn h1) v4
      _ ≤ ((nOf q m : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (T + 10) *
            exp (-((R8Of m : ℝ)) / 64) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ 1 / 256 := v0
  have v1 : ((2 * (ROf m : ℝ) + 1) ^ (T + 1)) * (2 : ℝ) ^ (T + 10) *
      exp (-((R8Of m : ℝ)) / 64) ≤ 1 / 256 := by
    have v7 : 2 * (ROf m : ℝ) + 1 ≤ (2 : ℝ) ^ (8 * E + 2) := by
      change 2 * ((2 ^ (8 * E) : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (8 * E + 2)
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_add]
      have hpos : (1 : ℝ) ≤ (2 : ℝ) ^ (8 * E) := by
        exact_mod_cast Nat.one_le_pow _ 2 (by norm_num)
      norm_num; linarith
    have v3 : (2 * (ROf m : ℝ) + 1) ^ (T + 1) * (2 : ℝ) ^ (T + 10) ≤
        (2 : ℝ) ^ ((8 * E + 2) * (T + 1) + (T + 10)) := by
      calc (2 * (ROf m : ℝ) + 1) ^ (T + 1) * (2 : ℝ) ^ (T + 10)
          ≤ ((2 : ℝ) ^ (8 * E + 2)) ^ (T + 1) * (2 : ℝ) ^ (T + 10) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) v7 _) (by positivity)
        _ = (2 : ℝ) ^ ((8 * E + 2) * (T + 1) + (T + 10)) := by rw [← pow_mul, ← pow_add]
    have hle : (8 * E + 2) * (T + 1) + (T + 10) + 8 ≤
        8 * q * E * (kOf q + 4) + (8 * E + 2) * (T + 1) + T + 20 := by omega
    calc ((2 * (ROf m : ℝ) + 1) ^ (T + 1)) * (2 : ℝ) ^ (T + 10) * exp (-((R8Of m : ℝ)) / 64)
        ≤ (2 : ℝ) ^ ((8 * E + 2) * (T + 1) + (T + 10)) * exp (-((R8Of m : ℝ)) / 64) :=
          mul_le_mul_of_nonneg_right v3 (exp_pos _).le
      _ ≤ 1 / 256 := hdom _ (le_trans (Nat.mul_le_mul_right 64 hle) hR8_huge)
  exact ⟨v0, v2, v1⟩
lemma exists_largeParams (q : ℕ) (hq : 2 ≤ q) :
    ∃ M₀ : ℕ, ∀ m ≥ M₀, LargeParams q m := by
  obtain ⟨T₁, hT₁⟩ := z13 (8 * q ^ 2)
  let M₀ := max 20 (max (1000 * q ^ 2 + 20) (T₁ + 2))
  refine ⟨M₀, fun m hm => ?_⟩
  have hm10 : 10 ≤ m := by omega
  have vp : m - 1 ≤ zd (m - 1) := z2c (m - 1)
  have va : m ≤ zd (m - 1) := y9 m (by omega)
  have vk : 1000 * q ^ 2 ≤ zd (m - 1) := by omega
  have v6 : T₁ ≤ zd (m - 1) := by omega
  set T := zd (m - 1)
  set E := EOf m
  have v5 : E = T ^ 10 := rfl
  have vh : q ≤ q ^ 2 := by nlinarith
  have vo : 4 ≤ q ^ 2 := by nlinarith
  have v7 : 1000 ≤ T := by nlinarith
  have vn : q ≤ T := by omega
  have vs : kOf q ≤ 3 * q := by unfold kOf; omega
  have v4 : KOf q m ≤ zd m := by
    have htm : zd m = 2 ^ T := by
      have hm1 : m = (m - 1) + 1 := by omega
      conv_lhs => rw [hm1]
      rfl
    rw [htm]
    exact hT₁ T v6
  have vm : 10000 ≤ E := by
    rw [v5]
    calc 10000 ≤ 1000 ^ 2 := by norm_num
      _ ≤ T ^ 2 := Nat.pow_le_pow_left v7 2
      _ ≤ T ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have vb : T ≤ E := by rw [v5]; exact Nat.le_self_pow (by norm_num) T
  have v0 : E * E ≤ R8Of m := z0v E (by omega)
  have vl : 100 ≤ KOf q m := by
    change 100 ≤ 8 * q ^ 2 * E
    nlinarith
  have vg : 10000 ≤ R8Of m := by
    have : 10000 ≤ E * E := by nlinarith
    exact le_trans this v0
  have v1 : 100 * (kOf q + 10) ≤ nOf q m := by
    have h1 : 100 * (kOf q + 10) ≤ T := by nlinarith
    have h2 : T ≤ 8 * q * E := by nlinarith
    exact le_trans h1 (le_trans h2 (Nat.le_of_lt Nat.lt_two_pow_self))
  have v9 : KOf q m + kOf q + 10 ≤ R8Of m := by
    change 8 * q ^ 2 * E + kOf q + 10 ≤ R8Of m
    have hq2 : 8 * q ^ 2 + 3 * q + 10 ≤ T := by nlinarith
    have ve : 8 * q ^ 2 * E + kOf q + 10 ≤ E * E := by
      have h1 : (8 * q ^ 2 + 3 * q + 10) * E ≤ E * E :=
        Nat.mul_le_mul_right E (le_trans hq2 vb)
      have vr : 1 ≤ E := by omega
      nlinarith
    exact le_trans ve v0
  have v3 : 1000 * (q + m + T ^ 3 + 100) ≤ E := by
    have vq : T ≤ T ^ 3 := Nat.le_self_pow (by norm_num) T
    have h1 : q + m + T ^ 3 + 100 ≤ 4 * T ^ 3 := by omega
    have hT7 : 4000 ≤ T ^ 7 := by
      calc 4000 ≤ 1000 ^ 2 := by norm_num
        _ ≤ T ^ 2 := Nat.pow_le_pow_left v7 2
        _ ≤ T ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : 4000 * T ^ 3 ≤ E := by
      rw [v5]
      calc 4000 * T ^ 3 ≤ T ^ 7 * T ^ 3 := Nat.mul_le_mul_right _ hT7
        _ = T ^ 10 := by ring
    omega
  have vc : 100 * (T + 10) * ROf m ≤ nOf q m := by
    rw [w5 q m]
    have vd : ROf m ^ 2 ≤ ROf m ^ q := Nat.pow_le_pow_right (R_pos m) hq
    have hT10 : 100 * (T + 10) ≤ ROf m := by
      have h1 : 100 * (T + 10) ≤ E := by
        have : T ≤ T ^ 3 := Nat.le_self_pow (by norm_num) T
        omega
      calc 100 * (T + 10) ≤ E := h1
        _ ≤ 2 ^ E := Nat.le_of_lt Nat.lt_two_pow_self
        _ ≤ 2 ^ (8 * E) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 100 * (T + 10) * ROf m ≤ ROf m * ROf m := Nat.mul_le_mul_right _ hT10
      _ = ROf m ^ 2 := (sq _).symm
      _ ≤ ROf m ^ q := vd
  have v2 : exp (20 * (m : ℝ) * (T : ℝ) ^ 2 + 100) ≤ (R8Of m : ℝ) := by
    change exp (20 * (m : ℝ) * (T : ℝ) ^ 2 + 100) ≤ ((2 ^ E : ℕ) : ℝ)
    rw [Nat.cast_pow, Nat.cast_ofNat]
    refine z11 _ E ?_
    have hmT : m * T ^ 2 ≤ T ^ 3 := by
      calc m * T ^ 2 ≤ T * T ^ 2 := Nat.mul_le_mul_right _ va
        _ = T ^ 3 := by ring
    have hnat : 2 * (20 * (m * T ^ 2) + 100) ≤ E := by omega
    have vj : ((2 * (20 * (m * T ^ 2) + 100) : ℕ) : ℝ) ≤ (E : ℝ) := by exact_mod_cast hnat
    push_cast at vj
    linarith
  have v8 : (8 * q * E * (kOf q + 4) + (8 * E + 2) * (T + 1) + T + 20) * 64 ≤ R8Of m := by
    have vf : 1000 * T ≤ T * T := Nat.mul_le_mul_right T v7
    have vi : 64 * (8 * q * (3 * q + 4) + 12 * (T + 2)) ≤ T ^ 3 := by
      have h1 : 8 * q * (3 * q + 4) ≤ 56 * q ^ 2 := by nlinarith only [hq]
      have h2 : 56 * q ^ 2 ≤ T := by omega
      have h3 : 64 * (T + 12 * (T + 2)) ≤ 1000 * T := by omega
      have h4 : 1000 * T ≤ T ^ 3 := by
        calc 1000 * T ≤ T * T := vf
          _ ≤ T * T * T := Nat.le_mul_of_pos_right _ (by omega)
          _ = T ^ 3 := by ring
      omega
    have hbig : (8 * q * E * (kOf q + 4) + (8 * E + 2) * (T + 1) + T + 20) * 64 ≤ E * E := by
      have hT3E : T ^ 3 ≤ E := by omega
      have hA : 8 * q * E * (kOf q + 4) ≤ (8 * q * (3 * q + 4)) * E := by
        calc 8 * q * E * (kOf q + 4) = (8 * q * (kOf q + 4)) * E := by ring
          _ ≤ (8 * q * (3 * q + 4)) * E := Nat.mul_le_mul_right E (Nat.mul_le_mul_left _ (by omega))
      have hB : (8 * E + 2) * (T + 1) + T + 20 ≤ (12 * (T + 2)) * E := by
        nlinarith only [vm]
      have hsum : (8 * q * E * (kOf q + 4) + (8 * E + 2) * (T + 1) + T + 20) * 64 ≤
          (64 * (8 * q * (3 * q + 4) + 12 * (T + 2))) * E := by
        nlinarith only [hA, hB]
      exact le_trans hsum (Nat.mul_le_mul_right E (le_trans vi hT3E))
    exact le_trans hbig v0
  obtain ⟨hpoly_exp_R8, hpoly_exp_R2, hsubset_exp_R8⟩ := z0q q m v8
  exact ⟨hm10, vk, v4, vl, vg, v1, v9, v3,
    vc, v2, hpoly_exp_R8, hpoly_exp_R2, hsubset_exp_R8⟩
lemma z26 {n r : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (u : Fin r → Fin n) (hu : Function.Injective u) (K : ℕ) :
    gProb n p {G | K ≤ (zc G u).card} ≤
      (n.choose K : ℝ) * (p ^ r) ^ K := by
  classical
  let Z : Finset (Fin n) := univ.filter (fun z => ∀ j : Fin r, z ≠ u j)
  have v2 : ∀ G : SimpleGraph (Fin n),
      zc G u = Z.filter (fun z => ∀ j : Fin r, G.Adj z (u j)) := by
    intro G
    ext z
    simp only [zl, Z, mem_filter, mem_univ, true_and]
    constructor
    · intro h
      exact ⟨fun j heq => G.loopless.irrefl (u j) (heq ▸ h j), h⟩
    · exact fun h => h.2
  let T : Fin n → Finset (z6 n) := fun z =>
    if hz : ∀ j : Fin r, z ≠ u j then
      univ.image (fun j : Fin r => z7 z (u j) (hz j))
    else ∅
  have v4 : Set.PairwiseDisjoint (Z : Set (Fin n)) T := by
    intro z₁ hz₁ z₂ hz₂ hne
    have h1 : ∀ j : Fin r, z₁ ≠ u j := (mem_filter.mp hz₁).2
    have h2 : ∀ j : Fin r, z₂ ≠ u j := (mem_filter.mp hz₂).2
    change Disjoint (T z₁) (T z₂)
    rw [disjoint_left]
    intro e he₁ he₂
    dsimp only [T] at he₁ he₂
    rw [dif_pos h1] at he₁
    rw [dif_pos h2] at he₂
    rcases mem_image.mp he₁ with ⟨j₁, _, rfl⟩
    rcases mem_image.mp he₂ with ⟨j₂, _, heq⟩
    rcases (ya (h2 j₂) (h1 j₁)).mp heq with ⟨hzz, _⟩ | ⟨hzu, _⟩
    · exact hne hzz.symm
    · exact h2 j₁ hzu
  have v5 : ∀ z ∈ Z, (T z).card = r := by
    intro z hz
    have h1 : ∀ j : Fin r, z ≠ u j := (mem_filter.mp hz).2
    dsimp only [T]
    rw [dif_pos h1]
    rw [Finset.card_image_of_injective _ (fun j₁ j₂ heq => by
      rcases (ya (h1 j₁) (h1 j₂)).mp heq with ⟨_, heq'⟩ | ⟨hzu, _⟩
      · exact hu heq'
      · exact absurd hzu (h1 j₂)), Finset.card_univ, Fintype.card_fin]
  have v8 : gProb n p {G | K ≤ (zc G u).card} ≤
      z4 p (fun f : z6 n → Bool =>
        ∃ W ∈ Z.powersetCard K, ∀ z ∈ W, ∀ e ∈ T z, f e = true) := by
    refine zi hp0 hp1 fun f hf => ?_
    change K ≤ (zc (z1 f) u).card at hf
    rw [v2] at hf
    obtain ⟨W, v0, v1⟩ := exists_subset_card_eq hf
    refine ⟨W, mem_powersetCard.mpr ⟨v0.trans (filter_subset _ _), v1⟩, ?_⟩
    intro z hzW e heT
    have hzZ : z ∈ Z := (filter_subset _ _) (v0 hzW)
    have h1 : ∀ j : Fin r, z ≠ u j := (mem_filter.mp hzZ).2
    have hadj : ∀ j : Fin r, (z1 f).Adj z (u j) := (mem_filter.mp (v0 hzW)).2
    dsimp only [T] at heT
    rw [dif_pos h1] at heT
    rcases mem_image.mp heT with ⟨j, _, rfl⟩
    exact (za f (h1 j)).mp (hadj j)
  have v7 : ∀ W ∈ Z.powersetCard K,
      z4 p (fun f : z6 n → Bool => ∀ z ∈ W, ∀ e ∈ T z, f e = true) = (p ^ r) ^ K := by
    intro W hW
    have v0 : W ⊆ Z := (mem_powersetCard.mp hW).1
    have v1 : W.card = K := (mem_powersetCard.mp hW).2
    have v6 : Set.PairwiseDisjoint (W : Set (Fin n)) T := v4.subset v0
    rw [y5 W T v6 p (fun z f => ∀ e ∈ T z, f e = true)
      (fun z _ f g hfg => forall₂_congr fun e he => by rw [hfg e he])]
    have v3 : ∀ z ∈ W, z4 p (fun f : z6 n → Bool => ∀ e ∈ T z, f e = true) = p ^ r := by
      intro z hz
      rw [yb (T z) p (fun _ => true)]
      simp [z9, v5 z (v0 hz)]
    rw [prod_congr rfl v3, prod_const, v1]
  calc gProb n p {G | K ≤ (zc G u).card}
      ≤ z4 p (fun f : z6 n → Bool =>
          ∃ W ∈ Z.powersetCard K, ∀ z ∈ W, ∀ e ∈ T z, f e = true) := v8
    _ ≤ ∑ W ∈ Z.powersetCard K,
          z4 p (fun f : z6 n → Bool => ∀ z ∈ W, ∀ e ∈ T z, f e = true) :=
        y3 hp0 hp1 _ _
    _ = ∑ _W ∈ Z.powersetCard K, (p ^ r) ^ K := sum_congr rfl v7
    _ = (Z.card.choose K : ℝ) * (p ^ r) ^ K := by
        rw [sum_const, card_powersetCard, nsmul_eq_mul]
    _ ≤ (n.choose K : ℝ) * (p ^ r) ^ K := by
        have hZle : Z.card ≤ n := by
          calc Z.card ≤ (univ : Finset (Fin n)).card := card_le_card (subset_univ _)
            _ = n := by simp
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.choose_le_choose K hZle)) (by positivity)
lemma z0y (q m : ℕ) (hlp : LargeParams q m) :
    gProb (nOf q m) ((ROf m : ℝ)⁻¹) (EventE1 q (nOf q m) (KOf q m))ᶜ ≤ 1 / 64 := by
  classical
  set n := nOf q m
  set R := ROf m
  set K := KOf q m
  set p : ℝ := (R : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have hsub : (EventE1 q n K)ᶜ ⊆
      ⋃ u ∈ (univ.filter (fun u : Fin q → Fin n => Function.Injective u)),
        {G : SimpleGraph (Fin n) | K ≤ (zc G u).card} := by
    intro G hG
    simp only [Set.mem_compl_iff, EventE1, Set.mem_ofPred_eq, not_forall, not_lt] at hG
    rcases hG with ⟨u, hu, hcard⟩
    exact Set.mem_biUnion (mem_filter.mpr ⟨mem_univ _, hu⟩) hcard
  have v0 : (n.choose K : ℝ) * (p ^ q) ^ K ≤ 1 / (K.factorial : ℝ) := by
    have h1 : (n.choose K : ℝ) * (K.factorial : ℝ) ≤ (n : ℝ) ^ K := by
      have hnat : K.factorial * n.choose K = n.descFactorial K :=
        (Nat.descFactorial_eq_factorial_mul_choose n K).symm
      have hle : n.descFactorial K ≤ n ^ K := Nat.descFactorial_le_pow n K
      have hnat' : n.choose K * K.factorial ≤ n ^ K := by linarith
      exact_mod_cast hnat'
    have hpq : p ^ q = ((n : ℝ))⁻¹ := by
      have hnR : (n : ℝ) = (R : ℝ) ^ q := by exact_mod_cast w5 q m
      rw [hnR, show p = (R : ℝ)⁻¹ from rfl, inv_pow]
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (wq q m)
    have v2 : (0 : ℝ) < (K.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos K)
    rw [hpq, inv_pow, le_div_iff₀ v2]
    have hmul : (n.choose K : ℝ) * ((n : ℝ) ^ K)⁻¹ * (K.factorial : ℝ) =
        ((n.choose K : ℝ) * (K.factorial : ℝ)) * ((n : ℝ) ^ K)⁻¹ := by ring
    rw [hmul]
    calc ((n.choose K : ℝ) * (K.factorial : ℝ)) * ((n : ℝ) ^ K)⁻¹
        ≤ ((n : ℝ) ^ K) * ((n : ℝ) ^ K)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 := mul_inv_cancel₀ (pow_pos hn0 K).ne'
  calc gProb n p (EventE1 q n K)ᶜ
      ≤ gProb n p (⋃ u ∈ univ.filter (fun u : Fin q → Fin n => Function.Injective u),
          {G | K ≤ (zc G u).card}) := gProb_mono hp0 hp1 hsub
    _ ≤ ∑ u ∈ univ.filter (fun u : Fin q → Fin n => Function.Injective u),
          gProb n p {G | K ≤ (zc G u).card} := yd hp0 hp1 _ _
    _ ≤ ∑ _u ∈ univ.filter (fun u : Fin q → Fin n => Function.Injective u),
          (1 / (K.factorial : ℝ)) := by
        refine sum_le_sum fun u hu => ?_
        exact (z26 hp0 hp1 u (mem_filter.mp hu).2 K).trans v0
    _ ≤ ((n : ℝ) ^ q) * (1 / (K.factorial : ℝ)) := by
        rw [sum_const, nsmul_eq_mul]
        have v1 : ((univ.filter (fun u : Fin q → Fin n => Function.Injective u)).card : ℝ) ≤
            (n : ℝ) ^ q := by
          have : (univ.filter (fun u : Fin q → Fin n => Function.Injective u)).card ≤
              (univ : Finset (Fin q → Fin n)).card := card_le_card (subset_univ _)
          simpa [Fintype.card_fun, Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr this
        exact mul_le_mul_of_nonneg_right v1 (by positivity)
    _ = ((2 : ℝ) ^ K) / (K.factorial : ℝ) := by
        have hnq : (n : ℝ) ^ q = (2 : ℝ) ^ K := by exact_mod_cast z2a q m
        rw [hnq, mul_one_div]
    _ ≤ 64 / ((2 : ℝ) ^ K) := z0g K (by have := hlp.hK_ge; omega)
    _ ≤ 1 / 64 := by
        have h2K : (4096 : ℝ) ≤ (2 : ℝ) ^ K := by
          have : 4096 ≤ 2 ^ K := calc 4096 = 2 ^ 12 := by norm_num
            _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by have := hlp.hK_ge; omega)
          exact_mod_cast this
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
lemma z25 {n r : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 4 * r ≤ n) (u : Fin r → Fin n) (hu : Function.Injective u) :
    gProb n p {G | ((zc G u).card : ℝ) < (1 / 3) * ((n : ℝ) * p ^ r)} ≤
      exp (-((n : ℝ) * p ^ r) / 16) ∧
    gProb n p {G | 2 * ((n : ℝ) * p ^ r) < ((zc G u).card : ℝ)} ≤
      exp (-((n : ℝ) * p ^ r) / 6) := by
  classical
  let Z : Finset (Fin n) := univ.filter (fun z => ∀ j : Fin r, z ≠ u j)
  have v5 : ∀ G : SimpleGraph (Fin n),
      zc G u = Z.filter (fun z => ∀ j : Fin r, G.Adj z (u j)) := by
    intro G
    ext z
    simp only [zl, Z, mem_filter, mem_univ, true_and]
    constructor
    · intro h; exact ⟨fun j heq => G.loopless.irrefl (u j) (heq ▸ h j), h⟩
    · exact fun h => h.2
  have vd : (3 / 4 : ℝ) * (n : ℝ) ≤ (Z.card : ℝ) := by
    have v9 : univ \ Z ⊆ univ.image u := by
      intro z hz
      simp only [Z, mem_sdiff, mem_univ, mem_filter, true_and, not_forall,
        not_ne_iff] at hz
      rcases hz with ⟨j, rfl⟩
      exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
    have v8 : (univ \ Z).card ≤ r := by
      calc (univ \ Z).card ≤ (univ.image u).card := card_le_card v9
        _ ≤ (univ : Finset (Fin r)).card := card_image_le
        _ = r := by simp
    have ve : n - Z.card ≤ r := by
      have : (univ \ Z).card = n - Z.card := by
        rw [card_sdiff, inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    have va : Z.card ≤ n := by
      calc Z.card ≤ (univ : Finset (Fin n)).card := card_le_card (subset_univ _)
        _ = n := by simp
    have hnat : 3 * n ≤ 4 * Z.card := by omega
    have vb : (3 : ℝ) * (n : ℝ) ≤ 4 * (Z.card : ℝ) := by exact_mod_cast hnat
    linarith
  have vc : (Z.card : ℝ) ≤ (n : ℝ) := by
    have : Z.card ≤ n := by
      calc Z.card ≤ (univ : Finset (Fin n)).card := card_le_card (subset_univ _)
        _ = n := by simp
    exact_mod_cast this
  let T : Fin n → Finset (z6 n) := fun z =>
    if hz : ∀ j : Fin r, z ≠ u j then
      univ.image (fun j : Fin r => z7 z (u j) (hz j))
    else ∅
  have v1 : Set.PairwiseDisjoint (Z : Set (Fin n)) T := by
    intro z₁ hz₁ z₂ hz₂ hne
    have h1 : ∀ j : Fin r, z₁ ≠ u j := (mem_filter.mp hz₁).2
    have h2 : ∀ j : Fin r, z₂ ≠ u j := (mem_filter.mp hz₂).2
    change Disjoint (T z₁) (T z₂)
    rw [disjoint_left]
    intro e he₁ he₂
    dsimp only [T] at he₁ he₂
    rw [dif_pos h1] at he₁
    rw [dif_pos h2] at he₂
    rcases mem_image.mp he₁ with ⟨j₁, _, rfl⟩
    rcases mem_image.mp he₂ with ⟨j₂, _, heq⟩
    rcases (ya (h2 j₂) (h1 j₁)).mp heq with ⟨hzz, _⟩ | ⟨hzu, _⟩
    · exact hne hzz.symm
    · exact h2 j₁ hzu
  have v6 : ∀ z ∈ Z, (T z).card = r := by
    intro z hz
    have h1 : ∀ j : Fin r, z ≠ u j := (mem_filter.mp hz).2
    dsimp only [T]
    rw [dif_pos h1]
    rw [Finset.card_image_of_injective _ (fun j₁ j₂ heq => by
      rcases (ya (h1 j₁) (h1 j₂)).mp heq with ⟨_, heq'⟩ | ⟨hzu, _⟩
      · exact hu heq'
      · exact absurd hzu (h1 j₂)), Finset.card_univ, Fintype.card_fin]
  let P : Fin n → (z6 n → Bool) → Prop := fun z f => ∀ e ∈ T z, f e = true
  have v4 : ∀ z ∈ Z, ∀ f g : z6 n → Bool, (∀ e ∈ T z, f e = g e) → (P z f ↔ P z g) :=
    fun z _ f g hfg => forall₂_congr fun e he => by rw [hfg e he]
  have v2 : ∀ z ∈ Z, z4 p (P z) = p ^ r := by
    intro z hz
    rw [yb (T z) p (fun _ => true)]
    simp [z9, v6 z hz]
  have v0 : ∀ f : z6 n → Bool,
      (zc (z1 f) u).card = (Z.filter (fun z => P z f)).card := by
    intro f
    congr 1
    rw [v5]
    ext z
    simp only [mem_filter]
    refine and_congr_right fun hzZ => ?_
    have h1 : ∀ j : Fin r, z ≠ u j := (mem_filter.mp hzZ).2
    dsimp only [P, T]
    rw [dif_pos h1]
    constructor
    · intro hadj e he
      rcases mem_image.mp he with ⟨j, _, rfl⟩
      exact (za f (h1 j)).mp (hadj j)
    · intro hall j
      exact (za f (h1 j)).mpr (hall _ (mem_image.mpr ⟨j, mem_univ _, rfl⟩))
  have v7 : 0 ≤ p ^ r := pow_nonneg hp0 r
  constructor
  · have v3 : gProb n p {G | ((zc G u).card : ℝ) < (1 / 3) * ((n : ℝ) * p ^ r)} ≤
        z4 p (fun f : z6 n → Bool =>
          ((Z.filter (fun z => P z f)).card : ℝ) < (1 / 2) * ((Z.card : ℝ) * p ^ r)) := by
      refine zi hp0 hp1 fun f hf => ?_
      change ((zc (z1 f) u).card : ℝ) < (1 / 3) * ((n : ℝ) * p ^ r) at hf
      rw [v0] at hf
      have h1 : (1 / 3 : ℝ) * ((n : ℝ) * p ^ r) ≤ (1 / 2) * ((Z.card : ℝ) * p ^ r) := by nlinarith
      linarith
    exact v3.trans ((yx Z T v1 hp0 hp1 P v4 v7
      (fun z hz => le_of_eq (v2 z hz).symm)).trans
      (exp_le_exp.mpr (by nlinarith)))
  · have v3 : gProb n p {G | 2 * ((n : ℝ) * p ^ r) < ((zc G u).card : ℝ)} ≤
        z4 p (fun f : z6 n → Bool =>
          2 * ((Z.card : ℝ) * p ^ r) < ((Z.filter (fun z => P z f)).card : ℝ)) := by
      refine zi hp0 hp1 fun f hf => ?_
      change 2 * ((n : ℝ) * p ^ r) < ((zc (z1 f) u).card : ℝ) at hf
      rw [v0] at hf
      have h1 : 2 * ((Z.card : ℝ) * p ^ r) ≤ 2 * ((n : ℝ) * p ^ r) := by nlinarith
      linarith
    exact v3.trans ((ww Z T v1 hp0 hp1 P v4
      (fun z hz => le_of_eq (v2 z hz))).trans
      (exp_le_exp.mpr (by nlinarith)))
def EventEdeg (q n R : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∀ (r : ℕ), 1 ≤ r → r < q →
    ∀ u : Fin r → Fin n, Function.Injective u →
      (1 / 3 : ℝ) * ((R : ℝ) ^ (q - r)) ≤ ((zc G u).card : ℝ) ∧
      ((zc G u).card : ℝ) ≤ 2 * ((R : ℝ) ^ (q - r))}
lemma z0h (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) :
    gProb (nOf q m) ((ROf m : ℝ)⁻¹) (EventEdeg q (nOf q m) (ROf m))ᶜ ≤ 1 / 64 := by
  classical
  set n := nOf q m
  set R := ROf m
  set p : ℝ := (R : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have v9 : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (R_pos m)
  have va : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast R_pos m
  have vb : (R2Of m : ℝ) ≤ (R : ℝ) := by
    have : R2Of m ≤ R := by
      change R2Of m ≤ ROf m
      rw [z15]; exact Nat.le_self_pow (by norm_num) _
    exact_mod_cast this
  have v8 : (EventEdeg q n R)ᶜ ⊆
      ⋃ r ∈ Ico 1 q,
        {G : SimpleGraph (Fin n) |
          ∃ u : Fin r → Fin n, Function.Injective u ∧
            (((zc G u).card : ℝ) < (1 / 3) * ((R : ℝ) ^ (q - r)) ∨
             2 * ((R : ℝ) ^ (q - r)) < ((zc G u).card : ℝ))} := by
    intro G hG
    simp only [Set.mem_compl_iff, EventEdeg, Set.mem_ofPred_eq, not_forall, not_and_or, not_le] at hG
    rcases hG with ⟨r, hr1, hrq, u, hu, hbad⟩
    exact Set.mem_biUnion (mem_Ico.mpr ⟨hr1, hrq⟩) ⟨u, hu, hbad⟩
  have v2 : ∀ r ∈ Ico 1 q,
      gProb n p {G : SimpleGraph (Fin n) |
        ∃ u : Fin r → Fin n, Function.Injective u ∧
          (((zc G u).card : ℝ) < (1 / 3) * ((R : ℝ) ^ (q - r)) ∨
           2 * ((R : ℝ) ^ (q - r)) < ((zc G u).card : ℝ))} ≤
      2 * ((n : ℝ) ^ r) * exp (-((R2Of m : ℝ)) / 64) := by
    intro r hr
    rcases mem_Ico.mp hr with ⟨hr1, hrq⟩
    have v6 : (n : ℝ) * p ^ r = (R : ℝ) ^ (q - r) := by
      have hnR : (n : ℝ) = (R : ℝ) ^ q := by exact_mod_cast w5 q m
      have hqr : q = (q - r) + r := by omega
      have hne : (R : ℝ) ^ r ≠ 0 := (pow_pos v9 r).ne'
      calc (n : ℝ) * p ^ r = (R : ℝ) ^ q * ((R : ℝ) ^ r)⁻¹ := by rw [hnR]; simp [p, inv_pow]
        _ = ((R : ℝ) ^ (q - r) * (R : ℝ) ^ r) * ((R : ℝ) ^ r)⁻¹ := by rw [← pow_add, ← hqr]
        _ = (R : ℝ) ^ (q - r) := mul_inv_cancel_right₀ hne _
    have v5 : (R2Of m : ℝ) ≤ (n : ℝ) * p ^ r := by
      rw [v6]
      have hpow : (R : ℝ) ^ 1 ≤ (R : ℝ) ^ (q - r) := pow_le_pow_right₀ va (by omega)
      linarith [pow_one (R : ℝ)]
    have h4r : 4 * r ≤ n := by
      have := hlp.hn_ge_params
      unfold kOf at this
      omega
    have v7 : {G : SimpleGraph (Fin n) |
        ∃ u : Fin r → Fin n, Function.Injective u ∧
          (((zc G u).card : ℝ) < (1 / 3) * ((R : ℝ) ^ (q - r)) ∨
           2 * ((R : ℝ) ^ (q - r)) < ((zc G u).card : ℝ))} ⊆
        ⋃ u ∈ univ.filter (fun u : Fin r → Fin n => Function.Injective u),
          ({G | ((zc G u).card : ℝ) < (1 / 3) * ((n : ℝ) * p ^ r)} ∪
           {G | 2 * ((n : ℝ) * p ^ r) < ((zc G u).card : ℝ)}) := by
      intro G ⟨u, hu, hbad⟩
      rw [← v6] at hbad
      exact Set.mem_biUnion (mem_filter.mpr ⟨mem_univ _, hu⟩) hbad
    calc gProb n p _
        ≤ gProb n p _ := gProb_mono hp0 hp1 v7
      _ ≤ ∑ u ∈ univ.filter (fun u : Fin r → Fin n => Function.Injective u),
            gProb n p ({G | ((zc G u).card : ℝ) < (1 / 3) * ((n : ℝ) * p ^ r)} ∪
              {G | 2 * ((n : ℝ) * p ^ r) < ((zc G u).card : ℝ)}) :=
          yd hp0 hp1 _ _
      _ ≤ ∑ _u ∈ univ.filter (fun u : Fin r → Fin n => Function.Injective u),
            (2 * exp (-((R2Of m : ℝ)) / 64)) := by
          refine sum_le_sum fun u hu => ?_
          have v0 := z25 hp0 hp1 h4r u (mem_filter.mp hu).2
          have hlow : exp (-((n : ℝ) * p ^ r) / 16) ≤ exp (-((R2Of m : ℝ)) / 64) :=
            exp_le_exp.mpr (by linarith)
          have hup : exp (-((n : ℝ) * p ^ r) / 6) ≤ exp (-((R2Of m : ℝ)) / 64) :=
            exp_le_exp.mpr (by linarith)
          linarith [yg hp0 hp1
            {G | ((zc G u).card : ℝ) < (1 / 3) * ((n : ℝ) * p ^ r)}
            {G | 2 * ((n : ℝ) * p ^ r) < ((zc G u).card : ℝ)}, v0.1, v0.2]
      _ ≤ ((n : ℝ) ^ r) * (2 * exp (-((R2Of m : ℝ)) / 64)) := by
          rw [sum_const, nsmul_eq_mul]
          have v1 : ((univ.filter (fun u : Fin r → Fin n => Function.Injective u)).card : ℝ) ≤
              (n : ℝ) ^ r := by
            have : (univ.filter (fun u : Fin r → Fin n => Function.Injective u)).card ≤
                (univ : Finset (Fin r → Fin n)).card := card_le_card (subset_univ _)
            simpa [Fintype.card_fun, Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr this
          exact mul_le_mul_of_nonneg_right v1 (by positivity)
      _ = 2 * ((n : ℝ) ^ r) * exp (-((R2Of m : ℝ)) / 64) := by ring
  calc gProb n p (EventEdeg q n R)ᶜ
      ≤ gProb n p _ := gProb_mono hp0 hp1 v8
    _ ≤ ∑ r ∈ Ico 1 q, gProb n p _ := yd hp0 hp1 _ _
    _ ≤ ∑ r ∈ Ico 1 q, (2 * ((n : ℝ) ^ r) * exp (-((R2Of m : ℝ)) / 64)) :=
        sum_le_sum v2
    _ ≤ ∑ _r ∈ Ico 1 q, (2 * ((n : ℝ) ^ q) * exp (-((R2Of m : ℝ)) / 64)) := by
        refine sum_le_sum fun r hr => ?_
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast wq q m
        have hpow : (n : ℝ) ^ r ≤ (n : ℝ) ^ q := pow_le_pow_right₀ hn1 (by
          have := (mem_Ico.mp hr).2; omega)
        have v4 : 0 ≤ exp (-((R2Of m : ℝ)) / 64) := (exp_pos _).le
        nlinarith
    _ = ((q - 1 : ℕ) : ℝ) * (2 * ((n : ℝ) ^ q) * exp (-((R2Of m : ℝ)) / 64)) := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ 2 * ((n : ℝ) ^ (kOf q + 4)) * exp (-((R2Of m : ℝ)) / 64) := by
        have v3 : ((q - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
          have := hlp.hn_ge_params; unfold kOf at this
          have : q - 1 ≤ n := by omega
          exact_mod_cast this
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast wq q m
        have hpow : (n : ℝ) ^ (q + 1) ≤ (n : ℝ) ^ (kOf q + 4) := pow_le_pow_right₀ hn1 (by
          unfold kOf; omega)
        have hmul : ((q - 1 : ℕ) : ℝ) * (n : ℝ) ^ q ≤ (n : ℝ) ^ (kOf q + 4) := by
          calc ((q - 1 : ℕ) : ℝ) * (n : ℝ) ^ q
              ≤ (n : ℝ) * (n : ℝ) ^ q := mul_le_mul_of_nonneg_right v3 (by positivity)
            _ = (n : ℝ) ^ (q + 1) := (_root_.pow_succ' _ _).symm
            _ ≤ (n : ℝ) ^ (kOf q + 4) := hpow
        have v4 : 0 ≤ exp (-((R2Of m : ℝ)) / 64) := (exp_pos _).le
        nlinarith
    _ ≤ 2 * (1 / 256) := by linarith [hlp.hpoly_exp_R2]
    _ ≤ 1 / 64 := by norm_num
end
section
open scoped BigOperators
open Finset Real Nat
lemma zv {n : ℕ} {S : Finset (z6 n)} {u₁ v₁ u₂ v₂ : Fin n}
    {h₁ : u₁ ≠ v₁} {h₂ : u₂ ≠ v₂} {hs₁ : z7 u₁ v₁ h₁ ∉ S} {hs₂ : z7 u₂ v₂ h₂ ∉ S}
    (heq : (⟨z7 u₁ v₁ h₁, hs₁⟩ : {e // e ∉ S}) = ⟨z7 u₂ v₂ h₂, hs₂⟩) :
    (u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂) :=
  (ya h₁ h₂).mp (congrArg Subtype.val heq)
def ze {n : ℕ} (P : Finset (Fin n)) : Finset (z6 n) := by
  classical
  exact univ.filter (fun e : z6 n => ∃ u ∈ P, u ∈ e.1)
def z8 {n : ℕ} (U V : Finset (Fin n)) : Finset (z6 n) := by
  classical
  exact univ.filter (fun e : z6 n => ∃ u ∈ U, ∃ v ∈ V, e.1 = s(u, v))
lemma z0p {n : ℕ} (P : Finset (Fin n)) {u v : Fin n} (h : u ≠ v) :
    z7 u v h ∈ ze P ↔ u ∈ P ∨ v ∈ P := by
  classical
  simp only [ze, z7, mem_filter, mem_univ, true_and, Sym2.mem_iff]
  constructor
  · rintro ⟨w, hw, rfl | rfl⟩
    · exact Or.inl hw
    · exact Or.inr hw
  · rintro (hu | hv)
    · exact ⟨u, hu, Or.inl rfl⟩
    · exact ⟨v, hv, Or.inr rfl⟩
lemma z5 {n : ℕ} (U V : Finset (Fin n)) {u v : Fin n} (h : u ≠ v) :
    z7 u v h ∈ z8 U V ↔ (u ∈ U ∧ v ∈ V) ∨ (v ∈ U ∧ u ∈ V) := by
  classical
  simp only [z8, z7, mem_filter, mem_univ, true_and, Sym2.eq_iff]
  constructor
  · rintro ⟨a, ha, b, hb, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact ⟨u, hu, v, hv, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, hv, u, hu, Or.inr ⟨rfl, rfl⟩⟩
lemma zo {n : ℕ} {P U V : Finset (Fin n)}
    (hPU : Disjoint P U) (hPV : Disjoint P V) :
    Disjoint (ze P) (z8 U V) := by
  rw [disjoint_left]
  intro ⟨e, he⟩ he1 he2
  induction e using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
    have h1 := (z0p P huv).mp he1
    have h2 := (z5 U V huv).mp he2
    rcases h1 with hu | hv <;> rcases h2 with ⟨hU, hV⟩ | ⟨hU, hV⟩
    · exact disjoint_left.mp hPU hu hU
    · exact disjoint_left.mp hPV hu hV
    · exact disjoint_left.mp hPV hv hV
    · exact disjoint_left.mp hPU hv hU
noncomputable def zg (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) : Finset (Fin n) := by
  classical
  exact univ.filter (fun w : Fin n =>
    z0m q hq G a w ∧ ∀ j : Fin (q - 2), G.Adj w (ys q hq a j))
lemma y8 (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (w : Fin n) :
    w ∈ zg q hq G a ↔
      z0m q hq G a w ∧ ∀ j : Fin (q - 2), G.Adj w (ys q hq a j) := by
  classical simp [zg]
lemma w3 (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) (u v : Fin n) :
    Rrel q hq G a u v ↔ ∃ w ∈ zg q hq G a, G.Adj w u ∧ G.Adj w v := by
  simp only [Rrel, y8]
  constructor
  · rintro ⟨w, hw, hu, hv, hb⟩; exact ⟨w, ⟨hw, hb⟩, hu, hv⟩
  · rintro ⟨w, ⟨hw, hb⟩, hu, hv⟩; exact ⟨w, hw, hu, hv, hb⟩
noncomputable def zk (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) : Finset (Fin n) := by
  classical exact univ.filter (fun z : Fin n => isBc q hq G a z)
noncomputable def zm (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) : Finset (Fin n) := by
  classical exact univ.filter (fun z : Fin n => isBc' q hq G a z)
lemma wa (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) :
    zk q hq G a = zc G (yc q hq a) := by
  classical
  ext z
  unfold zk
  rw [mem_filter, zl]
  simp [isBc]
lemma w6 (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin (kOf q) → Fin n) :
    zm q hq G a = zc G (yc' q hq a) := by
  classical
  ext z
  unfold zm
  rw [mem_filter, zl]
  simp [isBc']
lemma yw (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    {G : SimpleGraph (Fin (nOf q m))}
    (hE1 : G ∈ EventE1 q (nOf q m) (KOf q m))
    (hEdeg : G ∈ EventEdeg q (nOf q m) (ROf m))
    (a : Fin (kOf q) → Fin (nOf q m)) (hinj : Function.Injective a) :
    ((ROf m : ℝ) / 3 ≤ ((zk q hq G a).card : ℝ) ∧
      ((zk q hq G a).card : ℝ) ≤ 2 * (ROf m : ℝ)) ∧
    ((ROf m : ℝ) / 3 ≤ ((zm q hq G a).card : ℝ) ∧
      ((zm q hq G a).card : ℝ) ≤ 2 * (ROf m : ℝ)) ∧
    ((zk q hq G a ∩ zm q hq G a).card < KOf q m) ∧
    ((1 / 4 : ℝ) * ((ROf m : ℝ) ^ 2) ≤ ((zg q hq G a).card : ℝ) ∧
      ((zg q hq G a).card : ℝ) ≤ 2 * ((ROf m : ℝ) ^ 2)) ∧
    (∀ x : Fin (nOf q m), ¬ zs q a x →
      ((zg q hq G a ∩ zc G (fun _ : Fin 1 => x)).card : ℝ) ≤ 2 * (ROf m : ℝ)) := by
  classical
  set R := ROf m
  set K := KOf q m
  have v8 : 10000 ≤ R := by
    have h1 : R8Of m ≤ R := by
      change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
    have := hlp.hR8_ge; omega
  have vk : K + kOf q + 10 ≤ R := by
    have h1 : R8Of m ≤ R := by
      change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
    have := hlp.hK_le_R8; omega
  have vb : Function.Injective (yc q hq a) := fun i j h => by
    have h1 := hinj h
    exact Fin.ext (congrArg (Fin.val : Fin (kOf q) → ℕ) h1)
  have v5 : Function.Injective (yc' q hq a) := fun i j h => by
    have h1 := hinj h
    have h2 : (q - 1) + i.val = (q - 1) + j.val := congrArg (Fin.val : Fin (kOf q) → ℕ) h1
    exact Fin.ext (by omega)
  have vc : Function.Injective (ys q hq a) := fun i j h => by
    have h1 := hinj h
    have h2 : 2 * (q - 1) + i.val = 2 * (q - 1) + j.val := congrArg (Fin.val : Fin (kOf q) → ℕ) h1
    exact Fin.ext (by omega)
  have hBc : (R : ℝ) / 3 ≤ ((zk q hq G a).card : ℝ) ∧
      ((zk q hq G a).card : ℝ) ≤ 2 * (R : ℝ) := by
    rw [wa]
    have h := hEdeg (q - 1) (by omega) (by omega) (yc q hq a) vb
    have hsub : q - (q - 1) = 1 := by omega
    rw [hsub, pow_one] at h
    constructor <;> linarith
  have hBc' : (R : ℝ) / 3 ≤ ((zm q hq G a).card : ℝ) ∧
      ((zm q hq G a).card : ℝ) ≤ 2 * (R : ℝ) := by
    rw [w6]
    have h := hEdeg (q - 1) (by omega) (by omega) (yc' q hq a) v5
    have hsub : q - (q - 1) = 1 := by omega
    rw [hsub, pow_one] at h
    constructor <;> linarith
  have vd : (zk q hq G a ∩ zm q hq G a).card < K := by
    let u : Fin q → Fin (nOf q m) := fun j =>
      if hj : j.val < q - 1 then yc q hq a ⟨j.val, hj⟩ else yc' q hq a ⟨0, by omega⟩
    have v0 : Function.Injective u := by
      intro j₁ j₂ heq
      by_cases h1 : j₁.val < q - 1 <;> by_cases h2 : j₂.val < q - 1
      · simp only [u, h1, h2, ↓reduceDIte] at heq
        exact Fin.ext (congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq))
      · simp only [u, h1, h2, ↓reduceDIte] at heq
        have hv : j₁.val = q - 1 + 0 := congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq)
        omega
      · simp only [u, h1, h2, ↓reduceDIte] at heq
        have hv : q - 1 + 0 = j₂.val := congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq)
        omega
      · exact Fin.ext (by omega)
    have hsub : zk q hq G a ∩ zm q hq G a ⊆ zc G u := by
      intro z hz
      rcases mem_inter.mp hz with ⟨hz1, hz2⟩
      rw [wa, zl] at hz1
      rw [w6, zl] at hz2
      rw [zl]
      intro j
      dsimp only [u]
      split_ifs with hj
      · exact hz1 ⟨j.val, hj⟩
      · exact hz2 ⟨0, by omega⟩
    exact lt_of_le_of_lt (card_le_card hsub) (hE1 u v0)
  have hBb : (1 / 4 : ℝ) * ((R : ℝ) ^ 2) ≤ ((zg q hq G a).card : ℝ) ∧
      ((zg q hq G a).card : ℝ) ≤ 2 * ((R : ℝ) ^ 2) := by
    let Pset := univ.image a
    have v3 : Pset.card ≤ kOf q := by
      calc Pset.card ≤ (univ : Finset (Fin (kOf q))).card := card_image_le
        _ = kOf q := by simp
    by_cases hq2 : q = 2
    · have v7 : nOf q m = R ^ 2 := by rw [w5 q m, hq2]
      have ve : zg q hq G a = univ \ (Pset ∪ zk q hq G a ∪ zm q hq G a) := by
        ext w
        simp only [y8, z0m, zs, mem_sdiff, mem_univ, true_and,
          mem_union, Pset, mem_image, zk, zm, mem_filter]
        constructor
        · rintro ⟨⟨hnp, hnbc, hnbc'⟩, _⟩
          rintro ((⟨r, hr⟩ | hbc) | hbc')
          · exact hnp ⟨r, hr.symm⟩
          · exact hnbc hbc
          · exact hnbc' hbc'
        · intro hnot
          refine ⟨⟨fun ⟨r, hr⟩ => hnot (Or.inl (Or.inl ⟨r, hr.symm⟩)),
            fun hbc => hnot (Or.inl (Or.inr hbc)),
            fun hbc' => hnot (Or.inr hbc')⟩, fun j => by have := j.isLt; omega⟩
      have hle : ((zg q hq G a).card : ℝ) ≤ (R : ℝ) ^ 2 := by
        have h1 : (zg q hq G a).card ≤ nOf q m := by
          calc (zg q hq G a).card ≤ (univ : Finset (Fin (nOf q m))).card :=
                card_le_card (subset_univ _)
            _ = nOf q m := by simp
        have h2 : (zg q hq G a).card ≤ R ^ 2 := v7 ▸ h1
        exact_mod_cast h2
      have hge : (1 / 4 : ℝ) * ((R : ℝ) ^ 2) ≤ ((zg q hq G a).card : ℝ) := by
        have hbad : (Pset ∪ zk q hq G a ∪ zm q hq G a).card ≤
            Pset.card + (zk q hq G a).card + (zm q hq G a).card :=
          (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
        have vh : nOf q m ≤ (zg q hq G a).card +
            (Pset ∪ zk q hq G a ∪ zm q hq G a).card := by
          rw [ve]
          have v1 := card_sdiff (s := Pset ∪ zk q hq G a ∪ zm q hq G a)
            (t := univ)
          rw [inter_univ, Finset.card_univ, Fintype.card_fin] at v1
          omega
        have vo : ((Pset ∪ zk q hq G a ∪ zm q hq G a).card : ℝ) ≤
            (kOf q : ℝ) + 4 * (R : ℝ) := by
          have h1 : ((Pset ∪ zk q hq G a ∪ zm q hq G a).card : ℝ) ≤
              (Pset.card : ℝ) + ((zk q hq G a).card : ℝ) + ((zm q hq G a).card : ℝ) := by
            exact_mod_cast hbad
          have h2 : (Pset.card : ℝ) ≤ (kOf q : ℝ) := by exact_mod_cast v3
          linarith [hBc.2, hBc'.2]
        have v9 : R ^ 2 ≤ (zg q hq G a).card +
            (Pset ∪ zk q hq G a ∪ zm q hq G a).card := v7 ▸ vh
        have hnR : ((R : ℝ) ^ 2) ≤ ((zg q hq G a).card : ℝ) +
            ((Pset ∪ zk q hq G a ∪ zm q hq G a).card : ℝ) := by
          exact_mod_cast v9
        have vn : (kOf q : ℝ) + 4 * (R : ℝ) ≤ (3 / 4 : ℝ) * ((R : ℝ) ^ 2) := by
          have hkR : (kOf q : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show kOf q ≤ R by omega)
          have vi : (10000 : ℝ) ≤ (R : ℝ) := by exact_mod_cast v8
          nlinarith
        linarith
      exact ⟨hge, by linarith⟩
    · have hq3 : 3 ≤ q := by omega
      let B0 := zc G (ys q hq a)
      have hB0 := hEdeg (q - 2) (by omega) (by omega) (ys q hq a) vc
      have vf : q - (q - 2) = 2 := by omega
      rw [vf] at hB0
      have v6 : zg q hq G a ⊆ B0 := by
        intro w hw
        rw [zl]
        exact ((y8 q hq G a w).mp hw).2
      have hle : ((zg q hq G a).card : ℝ) ≤ 2 * ((R : ℝ) ^ 2) := by
        have : ((zg q hq G a).card : ℝ) ≤ (B0.card : ℝ) :=
          Nat.cast_le.mpr (card_le_card v6)
        linarith [hB0.2]
      have v2 : (B0 ∩ zk q hq G a).card < K := by
        let u : Fin q → Fin (nOf q m) := fun j =>
          if hj : j.val < q - 1 then yc q hq a ⟨j.val, hj⟩ else ys q hq a ⟨0, by omega⟩
        have v0 : Function.Injective u := by
          intro j₁ j₂ heq
          by_cases h1 : j₁.val < q - 1 <;> by_cases h2 : j₂.val < q - 1
          · simp only [u, h1, h2, ↓reduceDIte] at heq
            exact Fin.ext (congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq))
          · simp only [u, h1, h2, ↓reduceDIte] at heq
            have hv : j₁.val = 2 * (q - 1) + 0 := congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq)
            omega
          · simp only [u, h1, h2, ↓reduceDIte] at heq
            have hv : 2 * (q - 1) + 0 = j₂.val := congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq)
            omega
          · exact Fin.ext (by omega)
        have hsub : B0 ∩ zk q hq G a ⊆ zc G u := by
          intro z hz
          rcases mem_inter.mp hz with ⟨hz1, hz2⟩
          rw [zl] at hz1
          rw [wa, zl] at hz2
          rw [zl]
          intro j; dsimp only [u]; split_ifs with hj
          · exact hz2 ⟨j.val, hj⟩
          · exact hz1 ⟨0, by omega⟩
        exact lt_of_le_of_lt (card_le_card hsub) (hE1 u v0)
      have v2' : (B0 ∩ zm q hq G a).card < K := by
        let u : Fin q → Fin (nOf q m) := fun j =>
          if hj : j.val < q - 1 then yc' q hq a ⟨j.val, hj⟩ else ys q hq a ⟨0, by omega⟩
        have v0 : Function.Injective u := by
          intro j₁ j₂ heq
          by_cases h1 : j₁.val < q - 1 <;> by_cases h2 : j₂.val < q - 1
          · simp only [u, h1, h2, ↓reduceDIte] at heq
            have hv : (q - 1) + j₁.val = (q - 1) + j₂.val :=
              congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq)
            exact Fin.ext (by omega)
          · simp only [u, h1, h2, ↓reduceDIte] at heq
            have hv : (q - 1) + j₁.val = 2 * (q - 1) + 0 :=
              congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq)
            omega
          · simp only [u, h1, h2, ↓reduceDIte] at heq
            have hv : 2 * (q - 1) + 0 = (q - 1) + j₂.val :=
              congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq)
            omega
          · exact Fin.ext (by omega)
        have hsub : B0 ∩ zm q hq G a ⊆ zc G u := by
          intro z hz
          rcases mem_inter.mp hz with ⟨hz1, hz2⟩
          rw [zl] at hz1
          rw [w6, zl] at hz2
          rw [zl]
          intro j; dsimp only [u]; split_ifs with hj
          · exact hz2 ⟨j.val, hj⟩
          · exact hz1 ⟨0, by omega⟩
        exact lt_of_le_of_lt (card_le_card hsub) (hE1 u v0)
      have va : B0 ⊆ zg q hq G a ∪ Pset ∪ (B0 ∩ zk q hq G a) ∪ (B0 ∩ zm q hq G a) := by
        intro w hw
        by_cases hp : zs q a w
        · rcases hp with ⟨r, rfl⟩
          exact mem_union_left _ (mem_union_left _ (mem_union_right _
            (mem_image.mpr ⟨r, mem_univ _, rfl⟩)))
        · by_cases hbc : isBc q hq G a w
          · exact mem_union_left _ (mem_union_right _
              (mem_inter.mpr ⟨hw, by simp [zk, hbc]⟩))
          · by_cases hbc' : isBc' q hq G a w
            · exact mem_union_right _
                (mem_inter.mpr ⟨hw, by simp [zm, hbc']⟩)
            · exact mem_union_left _ (mem_union_left _ (mem_union_left _
                ((y8 q hq G a w).mpr ⟨⟨hp, hbc, hbc'⟩, (zl G _ w).mp hw⟩)))
      have v4 : B0.card ≤ (zg q hq G a).card + Pset.card +
          (B0 ∩ zk q hq G a).card + (B0 ∩ zm q hq G a).card := by
        calc B0.card ≤ (zg q hq G a ∪ Pset ∪ (B0 ∩ zk q hq G a) ∪
                (B0 ∩ zm q hq G a)).card := card_le_card va
          _ ≤ (zg q hq G a ∪ Pset ∪ (B0 ∩ zk q hq G a)).card +
                (B0 ∩ zm q hq G a).card := card_union_le _ _
          _ ≤ (zg q hq G a ∪ Pset).card + (B0 ∩ zk q hq G a).card +
                (B0 ∩ zm q hq G a).card := Nat.add_le_add_right (card_union_le _ _) _
          _ ≤ (zg q hq G a).card + Pset.card + (B0 ∩ zk q hq G a).card +
                (B0 ∩ zm q hq G a).card :=
              Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _
      have vm : (B0.card : ℝ) ≤ ((zg q hq G a).card : ℝ) + (kOf q : ℝ) + 2 * (K : ℝ) := by
        have h1 : (B0.card : ℝ) ≤ ((zg q hq G a).card : ℝ) + (Pset.card : ℝ) +
            ((B0 ∩ zk q hq G a).card : ℝ) + ((B0 ∩ zm q hq G a).card : ℝ) := by
          exact_mod_cast v4
        have h2 : (Pset.card : ℝ) ≤ (kOf q : ℝ) := by exact_mod_cast v3
        have h3 : ((B0 ∩ zk q hq G a).card : ℝ) ≤ (K : ℝ) := by exact_mod_cast v2.le
        have h4 : ((B0 ∩ zm q hq G a).card : ℝ) ≤ (K : ℝ) := by exact_mod_cast v2'.le
        linarith
      have vl : (kOf q : ℝ) + 2 * (K : ℝ) ≤ (1 / 12 : ℝ) * ((R : ℝ) ^ 2) := by
        have h1 : (kOf q : ℝ) + 2 * (K : ℝ) ≤ 2 * (R : ℝ) := by
          have : kOf q + 2 * K ≤ 2 * R := by omega
          exact_mod_cast this
        have vi : (10000 : ℝ) ≤ (R : ℝ) := by exact_mod_cast v8
        nlinarith
      exact ⟨by linarith [hB0.1], hle⟩
  have vj : ∀ x : Fin (nOf q m), ¬ zs q a x →
      ((zg q hq G a ∩ zc G (fun _ : Fin 1 => x)).card : ℝ) ≤ 2 * (R : ℝ) := by
    intro x hnx
    let u : Fin (q - 1) → Fin (nOf q m) := fun j =>
      if hj : j.val < q - 2 then ys q hq a ⟨j.val, hj⟩ else x
    have v0 : Function.Injective u := by
      intro j₁ j₂ heq
      by_cases h1 : j₁.val < q - 2 <;> by_cases h2 : j₂.val < q - 2
      · simp only [u, h1, h2, ↓reduceDIte] at heq
        have hv : 2 * (q - 1) + j₁.val = 2 * (q - 1) + j₂.val :=
          congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq)
        exact Fin.ext (by omega)
      · simp only [u, h1, h2, ↓reduceDIte] at heq
        exact False.elim (hnx ⟨bIdx q hq ⟨j₁.val, h1⟩, heq.symm⟩)
      · simp only [u, h1, h2, ↓reduceDIte] at heq
        exact False.elim (hnx ⟨bIdx q hq ⟨j₂.val, h2⟩, heq⟩)
      · exact Fin.ext (by omega)
    have hsub : zg q hq G a ∩ zc G (fun _ : Fin 1 => x) ⊆ zc G u := by
      intro z hz
      rcases mem_inter.mp hz with ⟨hz1, hz2⟩
      have hb := ((y8 q hq G a z).mp hz1).2
      have hx := (zl G _ z).mp hz2 ⟨0, by omega⟩
      rw [zl]
      intro j; dsimp only [u]; split_ifs with hj
      · exact hb ⟨j.val, hj⟩
      · exact hx
    have hdeg := (hEdeg (q - 1) (by omega) (by omega) u v0).2
    have vg : q - (q - 1) = 1 := by omega
    rw [vg, pow_one] at hdeg
    exact (Nat.cast_le.mpr (card_le_card hsub)).trans hdeg
  exact ⟨hBc, hBc', vd, hBb, vj⟩
lemma yk {n R : ℕ} (hR : 10000 ≤ R)
    (S_rev : Finset (z6 n))
    (B_all B_sub A : Finset (Fin n))
    (hsub : B_sub ⊆ B_all)
    (hdisj_BA : Disjoint B_all A)
    (hdisj_S : Disjoint S_rev (z8 B_all A))
    (hB_lo : (1 / 12 : ℝ) * ((R : ℝ) ^ 2) ≤ (B_sub.card : ℝ))
    (hB_hi : (B_all.card : ℝ) ≤ 2 * ((R : ℝ) ^ 2))
    (hA_le : 4 * (A.card : ℝ) ≤ (R : ℝ)) :
    let p : ℝ := (R : ℝ)⁻¹
    let adj : ({e : z6 n // e ∉ S_rev} → Bool) → Fin n → Fin n → Prop :=
      fun f₂ u v => ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S_rev), f₂ ⟨z7 u v h, hmem⟩ = true
    z4 p (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
      ¬ ((∀ z ∈ A, ((B_all.filter (fun w => adj f₂ w z)).card : ℝ) ≤ 4 * (R : ℝ)) ∧
         (∀ z ∈ A, (R : ℝ) / 48 ≤
           ((B_sub.filter (fun w => adj f₂ w z ∧ ∀ z' ∈ A, z' ≠ z → ¬ adj f₂ w z')).card : ℝ)))) ≤
      2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200) := by
  classical
  set p : ℝ := (R : ℝ)⁻¹
  have ve : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ R))
  have vf : p ≤ 1 / 2 := by
    rw [show p = (R : ℝ)⁻¹ from rfl, inv_le_comm₀ ve (by norm_num)]
    have : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 2 ≤ R)
    linarith
  let adj : ({e : z6 n // e ∉ S_rev} → Bool) → Fin n → Fin n → Prop :=
    fun f₂ u v => ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S_rev), f₂ ⟨z7 u v h, hmem⟩ = true
  have v0 : ∀ w ∈ B_all, ∀ z ∈ A, w ≠ z := fun w hw z hz h =>
    disjoint_left.mp hdisj_BA hw (h ▸ hz)
  have v1 : ∀ w (hw : w ∈ B_all) z (hz : z ∈ A), z7 w z (v0 w hw z hz) ∉ S_rev :=
    fun w hw z hz => disjoint_right.mp hdisj_S
      ((z5 B_all A (v0 w hw z hz)).mpr (Or.inl ⟨hw, hz⟩))
  have vj : ∀ z ∈ A,
      z4 p (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
        4 * (R : ℝ) < ((B_all.filter (fun w => adj f₂ w z)).card : ℝ)) ≤
      exp (-((R : ℝ)) / 200) := by
    intro z hz
    let T : Fin n → Finset {e : z6 n // e ∉ S_rev} := fun w =>
      if hw : w ∈ B_all then {⟨z7 w z (v0 w hw z hz), v1 w hw z hz⟩} else ∅
    have v2 : Set.PairwiseDisjoint (B_all : Set (Fin n)) T := by
      intro w₁ hw₁ w₂ hw₂ hne
      have hw₁' : w₁ ∈ B_all := mem_coe.mp hw₁
      have hw₂' : w₂ ∈ B_all := mem_coe.mp hw₂
      change Disjoint (T w₁) (T w₂)
      dsimp only [T]
      rw [dif_pos hw₁', dif_pos hw₂', disjoint_singleton]
      intro heq
      have hval := congrArg Subtype.val heq
      rcases (ya (v0 w₁ hw₁' z hz) (v0 w₂ hw₂' z hz)).mp hval with
        ⟨hww, _⟩ | ⟨hwz, _⟩
      · exact hne hww
      · exact v0 w₁ hw₁' z hz hwz
    let P : Fin n → ({e : z6 n // e ∉ S_rev} → Bool) → Prop := fun w f₂ => adj f₂ w z
    have v6 : ∀ w ∈ B_all, ∀ f g : {e : z6 n // e ∉ S_rev} → Bool,
        (∀ x ∈ T w, f x = g x) → (P w f ↔ P w g) := by
      intro w hw f g hfg
      have hmem : ⟨z7 w z (v0 w hw z hz), v1 w hw z hz⟩ ∈ T w := by
        dsimp only [T]; rw [dif_pos hw]; exact mem_singleton_self _
      have heq := hfg _ hmem
      simp only [P, adj]
      constructor
      · rintro ⟨h', hnot', hf'⟩; exact ⟨h', hnot', by rwa [← heq]⟩
      · rintro ⟨h', hnot', hg'⟩; exact ⟨h', hnot', by rwa [heq]⟩
    have v3 : ∀ w ∈ B_all, z4 p (P w) = p := by
      intro w hw
      let e0 : {e : z6 n // e ∉ S_rev} := ⟨z7 w z (v0 w hw z hz), v1 w hw z hz⟩
      have v5 : z4 p (P w) = z4 p (fun f₂ => ∀ x ∈ ({e0} : Finset _), f₂ x = true) :=
        zx p fun f₂ => by
          simp only [P, adj, mem_singleton, forall_eq, e0]
          exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨v0 w hw z hz, v1 w hw z hz, h⟩⟩
      rw [v5, yb]
      simp [z9]
    have v9 : (1 / 12 : ℝ) * ((R : ℝ) ^ 2) ≤ (B_all.card : ℝ) :=
      hB_lo.trans (Nat.cast_le.mpr (card_le_card hsub))
    have vk : 2 * ((B_all.card : ℝ) * p) ≤ 4 * (R : ℝ) := by
      have : (B_all.card : ℝ) * p ≤ 2 * (R : ℝ) := by
        calc (B_all.card : ℝ) * p ≤ (2 * (R : ℝ) ^ 2) * (R : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_right hB_hi hp0
          _ = 2 * (R : ℝ) := by field_simp
      linarith
    have vd : (R : ℝ) / 12 ≤ (B_all.card : ℝ) * p := by
      calc (R : ℝ) / 12 = ((1 / 12 : ℝ) * (R : ℝ) ^ 2) * (R : ℝ)⁻¹ := by field_simp
        _ ≤ (B_all.card : ℝ) * p := mul_le_mul_of_nonneg_right v9 hp0
    have vc : z4 p (fun f₂ => 4 * (R : ℝ) < ((B_all.filter (fun w => adj f₂ w z)).card : ℝ)) ≤
        z4 p (fun f₂ => 2 * ((B_all.card : ℝ) * p) < ((B_all.filter (fun w => P w f₂)).card : ℝ)) :=
      zi hp0 hp1 fun f₂ hf₂ => by linarith
    exact vc.trans ((ww B_all T v2 hp0 hp1 P v6
      (fun w hw => le_of_eq (v3 w hw))).trans (exp_le_exp.mpr (by linarith)))
  have vl : ∀ z ∈ A,
      z4 p (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
        ((B_sub.filter (fun w => adj f₂ w z ∧ ∀ z' ∈ A, z' ≠ z → ¬ adj f₂ w z')).card : ℝ) <
          (R : ℝ) / 48) ≤
      exp (-((R : ℝ)) / 200) := by
    intro z hz
    let T : Fin n → Finset {e : z6 n // e ∉ S_rev} := fun w =>
      if hw : w ∈ B_sub then
        A.attach.image (fun z' =>
          ⟨z7 w z'.1 (v0 w (hsub hw) z'.1 z'.2), v1 w (hsub hw) z'.1 z'.2⟩)
      else ∅
    have v2 : Set.PairwiseDisjoint (B_sub : Set (Fin n)) T := by
      intro w₁ hw₁ w₂ hw₂ hne
      have hw₁' : w₁ ∈ B_sub := mem_coe.mp hw₁
      have hw₂' : w₂ ∈ B_sub := mem_coe.mp hw₂
      change Disjoint (T w₁) (T w₂)
      rw [disjoint_left]
      intro e he₁ he₂
      dsimp only [T] at he₁ he₂
      rw [dif_pos hw₁'] at he₁
      rw [dif_pos hw₂'] at he₂
      rcases mem_image.mp he₁ with ⟨z₁, _, rfl⟩
      rcases mem_image.mp he₂ with ⟨z₂, _, heq⟩
      have hval := congrArg Subtype.val heq
      rcases (ya (v0 w₂ (hsub hw₂') z₂.1 z₂.2)
          (v0 w₁ (hsub hw₁') z₁.1 z₁.2)).mp hval with ⟨hww, _⟩ | ⟨hwz, _⟩
      · exact hne hww.symm
      · exact v0 w₂ (hsub hw₂') z₁.1 z₁.2 hwz
    let P : Fin n → ({e : z6 n // e ∉ S_rev} → Bool) → Prop :=
      fun w f₂ => adj f₂ w z ∧ ∀ z' ∈ A, z' ≠ z → ¬ adj f₂ w z'
    have v6 : ∀ w ∈ B_sub, ∀ f g : {e : z6 n // e ∉ S_rev} → Bool,
        (∀ x ∈ T w, f x = g x) → (P w f ↔ P w g) := by
      intro w hw f g hfg
      have vh : ∀ z' (hz' : z' ∈ A),
          f ⟨z7 w z' (v0 w (hsub hw) z' hz'), v1 w (hsub hw) z' hz'⟩ =
          g ⟨z7 w z' (v0 w (hsub hw) z' hz'), v1 w (hsub hw) z' hz'⟩ := fun z' hz' =>
        hfg _ (by
          dsimp only [T]; rw [dif_pos hw]
          exact mem_image.mpr ⟨⟨z', hz'⟩, mem_attach _ _, rfl⟩)
      have v4 : ∀ z' (hz' : z' ∈ A), adj f w z' ↔ adj g w z' := fun z' hz' => by
        simp only [adj]
        constructor
        · rintro ⟨h', hnot', hf'⟩; exact ⟨h', hnot', by rwa [← vh z' hz']⟩
        · rintro ⟨h', hnot', hg'⟩; exact ⟨h', hnot', by rwa [vh z' hz']⟩
      exact and_congr (v4 z hz) (forall₂_congr fun z' hz' => imp_congr_right fun _ => not_congr (v4 z' hz'))
    have v3 : ∀ w ∈ B_sub, p / 2 ≤ z4 p (P w) := by
      intro w hw
      let e_z : {e : z6 n // e ∉ S_rev} :=
        ⟨z7 w z (v0 w (hsub hw) z hz), v1 w (hsub hw) z hz⟩
      let c : {e : z6 n // e ∉ S_rev} → Bool := fun x => decide (x = e_z)
      have v5 : z4 p (P w) = z4 p (fun f₂ => ∀ x ∈ T w, f₂ x = c x) := by
        refine zx p fun f₂ => ?_
        constructor
        · rintro ⟨h1, h2⟩ x hx
          dsimp only [T] at hx; rw [dif_pos hw] at hx
          rcases mem_image.mp hx with ⟨⟨z', hz'⟩, _, rfl⟩
          by_cases hzz : z' = z
          · subst hzz
            rcases h1 with ⟨_, _, hf⟩
            simpa [c, e_z] using hf
          · have vb : (⟨z7 w z' (v0 w (hsub hw) z' hz'),
                v1 w (hsub hw) z' hz'⟩ : {e // e ∉ S_rev}) ≠ e_z := by
              intro heq
              have hval := congrArg Subtype.val heq
              rcases (ya (v0 w (hsub hw) z' hz')
                  (v0 w (hsub hw) z hz)).mp hval with ⟨_, heq'⟩ | ⟨hwz, _⟩
              · exact hzz heq'
              · exact v0 w (hsub hw) z hz hwz
            have vi : f₂ ⟨z7 w z' (v0 w (hsub hw) z' hz'),
                v1 w (hsub hw) z' hz'⟩ ≠ true := fun ht =>
              h2 z' hz' hzz ⟨v0 w (hsub hw) z' hz', v1 w (hsub hw) z' hz', ht⟩
            simp [c, decide_eq_false vb, Bool.eq_false_iff.mpr vi]
        · intro hall
          refine ⟨?_, ?_⟩
          · have hmem : e_z ∈ T w := by
              dsimp only [T]; rw [dif_pos hw]
              exact mem_image.mpr ⟨⟨z, hz⟩, mem_attach _ _, rfl⟩
            have := hall e_z hmem
            simp only [c, decide_true] at this
            exact ⟨v0 w (hsub hw) z hz, v1 w (hsub hw) z hz, this⟩
          · intro z' hz' hne' ⟨_, _, hf⟩
            have hmem : (⟨z7 w z' (v0 w (hsub hw) z' hz'),
                v1 w (hsub hw) z' hz'⟩ : {e // e ∉ S_rev}) ∈ T w := by
              dsimp only [T]; rw [dif_pos hw]
              exact mem_image.mpr ⟨⟨z', hz'⟩, mem_attach _ _, rfl⟩
            have hval := hall _ hmem
            have vb : (⟨z7 w z' (v0 w (hsub hw) z' hz'),
                v1 w (hsub hw) z' hz'⟩ : {e // e ∉ S_rev}) ≠ e_z := by
              intro heq
              rcases (ya (v0 w (hsub hw) z' hz')
                  (v0 w (hsub hw) z hz)).mp (congrArg Subtype.val heq) with ⟨_, heq'⟩ | ⟨hwz, _⟩
              · exact hne' heq'
              · exact v0 w (hsub hw) z hz hwz
            simp only [c, decide_eq_false vb] at hval
            rw [hf] at hval; exact Bool.noConfusion hval
      rw [v5, yb]
      have vg : (T w).card = A.card := by
        dsimp only [T]; rw [dif_pos hw]
        rw [Finset.card_image_of_injective _ (fun a₁ a₂ heq => by
          rcases (ya (v0 w (hsub hw) a₁.1 a₁.2)
              (v0 w (hsub hw) a₂.1 a₂.2)).mp (congrArg Subtype.val heq) with ⟨_, h⟩ | ⟨hwz, _⟩
          · exact Subtype.ext h
          · exact absurd hwz (v0 w (hsub hw) a₂.1 a₂.2)), card_attach]
      have v7 : e_z ∈ T w := by
        dsimp only [T]; rw [dif_pos hw]
        exact mem_image.mpr ⟨⟨z, hz⟩, mem_attach _ _, rfl⟩
      rw [← mul_prod_erase (T w) (fun x => z9 p (c x)) v7]
      have h1 : z9 p (c e_z) = p := by simp [c, z9]
      have h2 : (∏ x ∈ (T w).erase e_z, z9 p (c x)) = (1 - p) ^ (A.card - 1) := by
        rw [prod_congr rfl (g := fun _ => 1 - p) (fun x hx => by
          have hne : x ≠ e_z := (mem_erase.mp hx).1
          simp [c, z9, decide_eq_false hne]), prod_const,
          card_erase_of_mem v7, vg]
      rw [h1, h2]
      have vm : (1 / 2 : ℝ) ≤ (1 - p) ^ (A.card - 1) := by
        have h1mp : exp (-2 * p) ≤ 1 - p := yt hp0 vf
        have hnn : 0 ≤ exp (-2 * p) := (exp_pos _).le
        have va : exp (-2 * p * ((A.card - 1 : ℕ) : ℝ)) ≤ (1 - p) ^ (A.card - 1) := by
          calc exp (-2 * p * ((A.card - 1 : ℕ) : ℝ))
              = exp (((A.card - 1 : ℕ) : ℝ) * (-2 * p)) := by congr 1; ring
            _ = (exp (-2 * p)) ^ (A.card - 1) := exp_nat_mul _ _
            _ ≤ (1 - p) ^ (A.card - 1) := pow_le_pow_left₀ hnn h1mp _
        have hlin : (1 / 2 : ℝ) ≤ exp (-2 * p * ((A.card - 1 : ℕ) : ℝ)) := by
          have vn : 2 * p * ((A.card - 1 : ℕ) : ℝ) ≤ 1 / 2 := by
            have hA1 : ((A.card - 1 : ℕ) : ℝ) ≤ (A.card : ℝ) := by
              exact_mod_cast Nat.sub_le A.card 1
            have : 2 * ((A.card - 1 : ℕ) : ℝ) * (R : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
              rw [mul_inv_le_iff₀ ve]; linarith
            simpa [p, mul_comm, mul_left_comm, mul_assoc] using this
          linarith [Real.add_one_le_exp (-2 * p * ((A.card - 1 : ℕ) : ℝ))]
        exact hlin.trans va
      nlinarith
    have vd : (R : ℝ) / 24 ≤ (B_sub.card : ℝ) * (p / 2) := by
      calc (R : ℝ) / 24 = ((1 / 12 : ℝ) * (R : ℝ) ^ 2) * ((R : ℝ)⁻¹ / 2) := by field_simp; ring
        _ ≤ (B_sub.card : ℝ) * (p / 2) := mul_le_mul_of_nonneg_right hB_lo (by positivity)
    have vc : z4 p (fun f₂ =>
          ((B_sub.filter (fun w => P w f₂)).card : ℝ) < (R : ℝ) / 48) ≤
        z4 p (fun f₂ =>
          ((B_sub.filter (fun w => P w f₂)).card : ℝ) < (1 / 2) * ((B_sub.card : ℝ) * (p / 2))) :=
      zi hp0 hp1 fun f₂ hf₂ => by linarith
    calc z4 p (fun f₂ => ((B_sub.filter (fun w => P w f₂)).card : ℝ) < (R : ℝ) / 48)
        ≤ z4 p (fun f₂ => ((B_sub.filter (fun w => P w f₂)).card : ℝ) <
            (1 / 2) * ((B_sub.card : ℝ) * (p / 2))) := vc
      _ ≤ exp (-((B_sub.card : ℝ) * (p / 2)) / 8) := by
          convert yx B_sub T v2 hp0 hp1 P v6 (by positivity) v3
      _ ≤ exp (-((R : ℝ)) / 200) := exp_le_exp.mpr (by linarith)
  have v8 : z4 p (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
      ¬ ((∀ z ∈ A, ((B_all.filter (fun w => adj f₂ w z)).card : ℝ) ≤ 4 * (R : ℝ)) ∧
         (∀ z ∈ A, (R : ℝ) / 48 ≤
           ((B_sub.filter (fun w => adj f₂ w z ∧ ∀ z' ∈ A, z' ≠ z → ¬ adj f₂ w z')).card : ℝ)))) ≤
      z4 p (fun f₂ => ∃ z ∈ A,
        4 * (R : ℝ) < ((B_all.filter (fun w => adj f₂ w z)).card : ℝ) ∨
        ((B_sub.filter (fun w => adj f₂ w z ∧ ∀ z' ∈ A, z' ≠ z → ¬ adj f₂ w z')).card : ℝ) <
          (R : ℝ) / 48) := by
    refine zi hp0 hp1 fun f₂ hf₂ => ?_
    rw [not_and_or] at hf₂
    push Not at hf₂
    rcases hf₂ with ⟨z, hz, h⟩ | ⟨z, hz, h⟩
    · exact ⟨z, hz, Or.inl h⟩
    · exact ⟨z, hz, Or.inr h⟩
  calc z4 p _
      ≤ z4 p _ := v8
    _ ≤ ∑ z ∈ A, z4 p (fun f₂ =>
          4 * (R : ℝ) < ((B_all.filter (fun w => adj f₂ w z)).card : ℝ) ∨
          ((B_sub.filter (fun w => adj f₂ w z ∧ ∀ z' ∈ A, z' ≠ z → ¬ adj f₂ w z')).card : ℝ) <
            (R : ℝ) / 48) := y3 hp0 hp1 A _
    _ ≤ ∑ _z ∈ A, (2 * exp (-((R : ℝ)) / 200)) := by
        refine sum_le_sum fun z hz => ?_
        linarith [yr hp0 hp1
          (fun f₂ => 4 * (R : ℝ) < ((B_all.filter (fun w => adj f₂ w z)).card : ℝ))
          (fun f₂ => ((B_sub.filter (fun w => adj f₂ w z ∧ ∀ z' ∈ A, z' ≠ z → ¬ adj f₂ w z')).card : ℝ) <
            (R : ℝ) / 48),
          vj z hz, vl z hz]
    _ = 2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200) := by
        rw [sum_const, nsmul_eq_mul]; ring
lemma yj {n R : ℕ} (hR : 10000 ≤ R)
    (S_rev : Finset (z6 n))
    (A W_any U : Finset (Fin n))
    (W_only W_z : Fin n → Finset (Fin n))
    (hW_any_hi : (W_any.card : ℝ) ≤ 4 * (A.card : ℝ) * (R : ℝ))
    (hW_only_sub : ∀ z ∈ A, W_only z ⊆ W_z z)
    (hW_z_sub : ∀ z ∈ A, W_z z ⊆ W_any)
    (hW_only_lo : ∀ z ∈ A, (R : ℝ) / 48 ≤ ((W_only z).card : ℝ))
    (hW_only_disj : ∀ z₁ ∈ A, ∀ z₂ ∈ A, z₁ ≠ z₂ → Disjoint (W_only z₁) (W_z z₂))
    (hdisj_UW : Disjoint U W_any)
    (hdisj_S : Disjoint S_rev (z8 U W_any)) :
    let p : ℝ := (R : ℝ)⁻¹
    let adj : ({e : z6 n // e ∉ S_rev} → Bool) → Fin n → Fin n → Prop :=
      fun f₂ u v => ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S_rev), f₂ ⟨z7 u v h, hmem⟩ = true
    z4 p (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
      ∃ S ∈ A.powerset,
        ((U.filter (fun u => ∀ z ∈ A, (∃ w ∈ W_z z, adj f₂ u w) ↔ z ∈ S)).card : ℝ) <
          (1 / 2) * ((U.card : ℝ) * exp (-13 * (A.card : ℝ)))) ≤
      ((2 : ℝ) ^ A.card) * exp (-((U.card : ℝ) * exp (-13 * (A.card : ℝ))) / 8) := by
  classical
  set p : ℝ := (R : ℝ)⁻¹
  have vm : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ R))
  have vf : p ≤ 1 / 2 := by
    rw [show p = (R : ℝ)⁻¹ from rfl, inv_le_comm₀ vm (by norm_num)]
    have : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 2 ≤ R)
    linarith
  let adj : ({e : z6 n // e ∉ S_rev} → Bool) → Fin n → Fin n → Prop :=
    fun f₂ u v => ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S_rev), f₂ ⟨z7 u v h, hmem⟩ = true
  have v1 : ∀ u ∈ U, ∀ w ∈ W_any, u ≠ w := fun u hu w hw h =>
    disjoint_left.mp hdisj_UW hu (h ▸ hw)
  have v2 : ∀ u (hu : u ∈ U) w (hw : w ∈ W_any), z7 u w (v1 u hu w hw) ∉ S_rev :=
    fun u hu w hw => disjoint_right.mp hdisj_S
      ((z5 U W_any (v1 u hu w hw)).mpr (Or.inl ⟨hu, hw⟩))
  have ve : ∀ S ∈ A.powerset,
      z4 p (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
        ((U.filter (fun u => ∀ z ∈ A, (∃ w ∈ W_z z, adj f₂ u w) ↔ z ∈ S)).card : ℝ) <
          (1 / 2) * ((U.card : ℝ) * exp (-13 * (A.card : ℝ)))) ≤
      exp (-((U.card : ℝ) * exp (-13 * (A.card : ℝ))) / 8) := by
    intro S hS_mem
    have hSA : S ⊆ A := mem_powerset.mp hS_mem
    let v3 : Finset (Fin n) := (A \ S).biUnion W_z
    have v0 : v3 ⊆ W_any := by
      intro w hw
      rcases mem_biUnion.mp hw with ⟨z, hz, hwz⟩
      exact hW_z_sub z (mem_sdiff.mp hz).1 hwz
    let T : Fin n → Finset {e : z6 n // e ∉ S_rev} := fun u =>
      if hu : u ∈ U then
        W_any.attach.image (fun w =>
          ⟨z7 u w.1 (v1 u hu w.1 w.2), v2 u hu w.1 w.2⟩)
      else ∅
    have vh : Set.PairwiseDisjoint (U : Set (Fin n)) T := by
      intro u₁ hu₁ u₂ hu₂ hne
      have hu₁' : u₁ ∈ U := mem_coe.mp hu₁
      have hu₂' : u₂ ∈ U := mem_coe.mp hu₂
      change Disjoint (T u₁) (T u₂)
      rw [disjoint_left]
      intro e he₁ he₂
      dsimp only [T] at he₁ he₂
      rw [dif_pos hu₁'] at he₁
      rw [dif_pos hu₂'] at he₂
      rcases mem_image.mp he₁ with ⟨w₁, _, rfl⟩
      rcases mem_image.mp he₂ with ⟨w₂, _, heq⟩
      rcases (ya (v1 u₂ hu₂' w₂.1 w₂.2)
          (v1 u₁ hu₁' w₁.1 w₁.2)).mp (congrArg Subtype.val heq) with ⟨huu, _⟩ | ⟨huw, _⟩
      · exact hne huu.symm
      · exact v1 u₂ hu₂' w₁.1 w₁.2 huw
    let P : Fin n → ({e : z6 n // e ∉ S_rev} → Bool) → Prop :=
      fun u f₂ => (∀ z ∈ S, ∃ w ∈ W_only z, adj f₂ u w) ∧ (∀ w ∈ v3, ¬ adj f₂ u w)
    have vo : ∀ u ∈ U, ∀ f₂, P u f₂ →
        (∀ z ∈ A, (∃ w ∈ W_z z, adj f₂ u w) ↔ z ∈ S) := by
      intro u _ f₂ ⟨hpos, hneg⟩ z hzA
      constructor
      · rintro ⟨w, hwz, hadj⟩
        by_contra hnotS
        exact hneg w (mem_biUnion.mpr ⟨z, mem_sdiff.mpr ⟨hzA, hnotS⟩, hwz⟩) hadj
      · intro hzS
        rcases hpos z hzS with ⟨w, hwonly, hadj⟩
        exact ⟨w, hW_only_sub z hzA hwonly, hadj⟩
    have vp : ∀ u ∈ U, ∀ f g : {e : z6 n // e ∉ S_rev} → Bool,
        (∀ x ∈ T u, f x = g x) → (P u f ↔ P u g) := by
      intro u hu f g hfg
      have vj : ∀ w (hw : w ∈ W_any),
          f ⟨z7 u w (v1 u hu w hw), v2 u hu w hw⟩ =
          g ⟨z7 u w (v1 u hu w hw), v2 u hu w hw⟩ := fun w hw =>
        hfg _ (by
          dsimp only [T]; rw [dif_pos hu]
          exact mem_image.mpr ⟨⟨w, hw⟩, mem_attach _ _, rfl⟩)
      have v5 : ∀ w (hw : w ∈ W_any), adj f u w ↔ adj g u w := fun w hw => by
        simp only [adj]
        constructor
        · rintro ⟨h', hnot', hf'⟩; exact ⟨h', hnot', by rwa [← vj w hw]⟩
        · rintro ⟨h', hnot', hg'⟩; exact ⟨h', hnot', by rwa [vj w hw]⟩
      refine and_congr ?_ ?_
      · exact forall₂_congr fun z hz => exists_congr fun w =>
          and_congr_right fun hwo => v5 w (hW_z_sub z (hSA hz) (hW_only_sub z (hSA hz) hwo))
      · exact forall₂_congr fun w hw => not_congr (v5 w (v0 hw))
    have vi : ∀ u ∈ U, exp (-13 * (A.card : ℝ)) ≤ z4 p (P u) := by
      intro u hu
      let idx : Finset (Option (Fin n)) := insert none (S.image some)
      let blk : Option (Fin n) → Finset {e : z6 n // e ∉ S_rev} := fun o =>
        match o with
        | none => v3.attach.image (fun w =>
            ⟨z7 u w.1 (v1 u hu w.1 (v0 w.2)),
             v2 u hu w.1 (v0 w.2)⟩)
        | some z =>
            if hz : z ∈ S then
              (W_only z).attach.image (fun w =>
                ⟨z7 u w.1 (v1 u hu w.1 (hW_z_sub z (hSA hz) (hW_only_sub z (hSA hz) w.2))),
                 v2 u hu w.1 (hW_z_sub z (hSA hz) (hW_only_sub z (hSA hz) w.2))⟩)
            else ∅
      have vb : Set.PairwiseDisjoint (idx : Set (Option (Fin n))) blk := by
        intro o₁ ho₁ o₂ ho₂ hne
        change Disjoint (blk o₁) (blk o₂)
        rw [disjoint_left]
        intro e he₁ he₂
        cases o₁ with
        | none =>
          cases o₂ with
          | none => exact hne rfl
          | some z₂ =>
            have hz₂ : z₂ ∈ S := by
              simp only [idx, mem_coe, mem_insert, mem_image,
                reduceCtorEq, false_or, Option.some.injEq] at ho₂
              rcases ho₂ with ⟨z', hz', rfl⟩; exact hz'
            dsimp only [blk] at he₁ he₂; rw [dif_pos hz₂] at he₂
            rcases mem_image.mp he₁ with ⟨w₁, _, rfl⟩
            rcases mem_image.mp he₂ with ⟨w₂, _, heq⟩
            rcases zv heq with ⟨_, hww⟩ | ⟨huw, _⟩
            · rcases mem_biUnion.mp w₁.2 with ⟨z₁, hz₁, hw₁z⟩
              have v4 : z₂ ≠ z₁ := fun h => (mem_sdiff.mp hz₁).2 (h ▸ hz₂)
              exact disjoint_left.mp (hW_only_disj z₂ (hSA hz₂) z₁
                (mem_sdiff.mp hz₁).1 v4) w₂.2 (hww ▸ hw₁z)
            · exact v1 u hu w₁.1 (v0 w₁.2) huw
        | some z₁ =>
          have hz₁ : z₁ ∈ S := by
            simp only [idx, mem_coe, mem_insert, mem_image,
              reduceCtorEq, false_or, Option.some.injEq] at ho₁
            rcases ho₁ with ⟨z', hz', rfl⟩; exact hz'
          cases o₂ with
          | none =>
            dsimp only [blk] at he₁ he₂; rw [dif_pos hz₁] at he₁
            rcases mem_image.mp he₁ with ⟨w₁, _, rfl⟩
            rcases mem_image.mp he₂ with ⟨w₂, _, heq⟩
            rcases zv heq with ⟨_, hww⟩ | ⟨huw, _⟩
            · rcases mem_biUnion.mp w₂.2 with ⟨z₂, hz₂, hw₂z⟩
              have v4 : z₁ ≠ z₂ := fun h => (mem_sdiff.mp hz₂).2 (h ▸ hz₁)
              exact disjoint_left.mp (hW_only_disj z₁ (hSA hz₁) z₂
                (mem_sdiff.mp hz₂).1 v4) w₁.2 (hww.symm ▸ hw₂z)
            · exact v1 u hu w₁.1 (hW_z_sub z₁ (hSA hz₁) (hW_only_sub z₁ (hSA hz₁) w₁.2)) huw
          | some z₂ =>
            have hz₂ : z₂ ∈ S := by
              simp only [idx, mem_coe, mem_insert, mem_image,
                reduceCtorEq, false_or, Option.some.injEq] at ho₂
              rcases ho₂ with ⟨z', hz', rfl⟩; exact hz'
            have v4 : z₁ ≠ z₂ := fun h => hne (congrArg some h)
            dsimp only [blk] at he₁ he₂; rw [dif_pos hz₁] at he₁; rw [dif_pos hz₂] at he₂
            rcases mem_image.mp he₁ with ⟨w₁, _, rfl⟩
            rcases mem_image.mp he₂ with ⟨w₂, _, heq⟩
            rcases zv heq with ⟨_, hww⟩ | ⟨huw, _⟩
            · exact disjoint_left.mp (hW_only_disj z₁ (hSA hz₁) z₂ (hSA hz₂) v4)
                w₁.2 (hW_only_sub z₂ (hSA hz₂) (hww ▸ w₂.2))
            · exact v1 u hu w₁.1 (hW_z_sub z₁ (hSA hz₁) (hW_only_sub z₁ (hSA hz₁) w₁.2)) huw
      let Q : Option (Fin n) → ({e : z6 n // e ∉ S_rev} → Bool) → Prop := fun o f₂ =>
        match o with
        | none => ∀ x ∈ blk none, f₂ x = false
        | some z => ∃ x ∈ blk (some z), f₂ x = true
      have hPQ : z4 p (P u) = z4 p (fun f₂ => ∀ o ∈ idx, Q o f₂) := by
        refine zx p fun f₂ => ?_
        constructor
        · rintro ⟨hpos, hneg⟩ o ho
          rcases mem_insert.mp ho with rfl | ho'
          · intro x hx
            rcases mem_image.mp hx with ⟨w, _, rfl⟩
            have hnt : f₂ ⟨z7 u w.1 (v1 u hu w.1 (v0 w.2)),
                v2 u hu w.1 (v0 w.2)⟩ ≠ true := fun ht =>
              hneg w.1 w.2 ⟨_, _, ht⟩
            exact Bool.eq_false_iff.mpr hnt
          · rcases mem_image.mp ho' with ⟨z, hz, rfl⟩
            rcases hpos z hz with ⟨w, hwo, ⟨_, _, hf⟩⟩
            refine ⟨⟨z7 u w (v1 u hu w (hW_z_sub z (hSA hz) (hW_only_sub z (hSA hz) hwo))),
              v2 u hu w (hW_z_sub z (hSA hz) (hW_only_sub z (hSA hz) hwo))⟩, ?_, hf⟩
            dsimp only [blk]; rw [dif_pos hz]
            exact mem_image.mpr ⟨⟨w, hwo⟩, mem_attach _ _, rfl⟩
        · intro hall
          refine ⟨?_, ?_⟩
          · intro z hz
            have hq := hall (some z) (mem_insert_of_mem (mem_image.mpr ⟨z, hz, rfl⟩))
            rcases hq with ⟨x, hx, hfx⟩
            dsimp only [blk] at hx; rw [dif_pos hz] at hx
            rcases mem_image.mp hx with ⟨w, _, rfl⟩
            exact ⟨w.1, w.2, ⟨_, _, hfx⟩⟩
          · intro w hw ⟨_, _, hft⟩
            have hq := hall none (mem_insert_self _ _)
            have hmem : (⟨z7 u w (v1 u hu w (v0 hw)),
                v2 u hu w (v0 hw)⟩ : {e // e ∉ S_rev}) ∈ blk none :=
              mem_image.mpr ⟨⟨w, hw⟩, mem_attach _ _, rfl⟩
            have hff := hq _ hmem
            rw [hft] at hff; exact Bool.noConfusion hff
      have vn : ∀ o ∈ idx, ∀ f g : {e : z6 n // e ∉ S_rev} → Bool,
          (∀ x ∈ blk o, f x = g x) → (Q o f ↔ Q o g) := by
        intro o _ f g hfg
        cases o with
        | none => exact forall₂_congr fun x hx => by rw [hfg x hx]
        | some z => exact exists_congr fun x => and_congr_right fun hx => by rw [hfg x hx]
      rw [hPQ, y5 idx blk vb p Q vn]
      have v7 : none ∉ S.image some := by simp
      rw [prod_insert v7]
      have v9 : exp (-8 * (A.card : ℝ)) ≤ z4 p (Q none) := by
        rw [show z4 p (Q none) = (1 - p) ^ (blk none).card by
          rw [yb]; simp [z9]]
        have va : (blk none).card = v3.card := by
          dsimp only [blk]
          rw [Finset.card_image_of_injective _ (fun w₁ w₂ heq => by
            rcases zv heq with ⟨_, h⟩ | ⟨huw, _⟩
            · exact Subtype.ext h
            · exact absurd huw (v1 u hu w₂.1 (v0 w₂.2))), card_attach]
        rw [va]
        have h1mp := yt hp0 vf
        calc exp (-8 * (A.card : ℝ))
            ≤ exp ((v3.card : ℝ) * (-2 * p)) := by
              refine exp_le_exp.mpr ?_
              have vg : (v3.card : ℝ) ≤ 4 * (A.card : ℝ) * (R : ℝ) :=
                (Nat.cast_le.mpr (card_le_card v0)).trans hW_any_hi
              have : (v3.card : ℝ) * (2 * p) ≤ 8 * (A.card : ℝ) := by
                calc (v3.card : ℝ) * (2 * p)
                    ≤ (4 * (A.card : ℝ) * (R : ℝ)) * (2 * (R : ℝ)⁻¹) :=
                      mul_le_mul_of_nonneg_right vg (by positivity)
                  _ = 8 * (A.card : ℝ) := by field_simp; ring
              linarith
          _ = (exp (-2 * p)) ^ v3.card := exp_nat_mul _ _
          _ ≤ (1 - p) ^ v3.card := pow_le_pow_left₀ (exp_pos _).le h1mp _
      have v8 : ∀ o ∈ S.image some, exp (-5 : ℝ) ≤ z4 p (Q o) := by
        intro o ho
        rcases mem_image.mp ho with ⟨z, hz, rfl⟩
        have vl : z4 p (Q (some z)) = 1 - (1 - p) ^ (blk (some z)).card := by
          have vs : z4 p (fun f₂ => ¬ Q (some z) f₂) = (1 - p) ^ (blk (some z)).card := by
            have vk : z4 p (fun f₂ => ¬ Q (some z) f₂) =
                z4 p (fun f₂ => ∀ x ∈ blk (some z), f₂ x = false) :=
              zx p fun f₂ => by
                simp only [Q, not_exists, not_and, Bool.eq_false_iff]
            rw [vk, yb]; simp [z9]
          have h1 := wg p (Q (some z))
          linarith
        rw [vl]
        have vd : (blk (some z)).card = (W_only z).card := by
          dsimp only [blk]; rw [dif_pos hz]
          rw [Finset.card_image_of_injective _ (fun w₁ w₂ heq => by
            rcases zv heq with ⟨_, h⟩ | ⟨huw, _⟩
            · exact Subtype.ext h
            · exact absurd huw (v1 u hu w₂.1
                (hW_z_sub z (hSA hz) (hW_only_sub z (hSA hz) w₂.2)))), card_attach]
        rw [vd]
        have vr : (1 - p) ^ (W_only z).card ≤ exp (-1 / 48 : ℝ) := by
          have h1mp : 1 - p ≤ exp (-p) := by linarith [Real.add_one_le_exp (-p)]
          calc (1 - p) ^ (W_only z).card
              ≤ (exp (-p)) ^ (W_only z).card := pow_le_pow_left₀ (by linarith) h1mp _
            _ = exp (((W_only z).card : ℝ) * (-p)) := (exp_nat_mul _ _).symm
            _ ≤ exp (-1 / 48 : ℝ) := by
                refine exp_le_exp.mpr ?_
                have hlo := hW_only_lo z (hSA hz)
                have h1 : (1 / 48 : ℝ) ≤ ((W_only z).card : ℝ) * p := by
                  calc (1 / 48 : ℝ) = ((R : ℝ) / 48) * (R : ℝ)⁻¹ := by field_simp
                    _ ≤ ((W_only z).card : ℝ) * p := mul_le_mul_of_nonneg_right hlo hp0
                linarith
        have h1me : (1 / 96 : ℝ) ≤ 1 - exp (-1 / 48 : ℝ) := by
          have := z0j (x := (1 / 48 : ℝ)) (by norm_num) (by norm_num)
          linarith
        have vt : exp (-5 : ℝ) ≤ (1 / 96 : ℝ) := by
          have hsum := Real.sum_le_exp_of_nonneg (x := (5 : ℝ)) (by norm_num) 7
          simp [sum_range_succ, Nat.factorial] at hsum
          rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
          linarith
        linarith
      have v6 : exp (-5 * (A.card : ℝ)) ≤ ∏ o ∈ S.image some, z4 p (Q o) := by
        calc exp (-5 * (A.card : ℝ))
            ≤ exp (-5 * (S.card : ℝ)) := by
              refine exp_le_exp.mpr ?_
              have : (S.card : ℝ) ≤ (A.card : ℝ) := Nat.cast_le.mpr (card_le_card hSA)
              linarith
          _ = exp ((S.card : ℝ) * (-5 : ℝ)) := by congr 1; ring
          _ = (exp (-5 : ℝ)) ^ S.card := exp_nat_mul _ _
          _ = (exp (-5 : ℝ)) ^ (S.image some).card := by
              rw [Finset.card_image_of_injective _ (Option.some_injective (Fin n))]
          _ = ∏ _o ∈ S.image some, exp (-5 : ℝ) := (prod_const _).symm
          _ ≤ ∏ o ∈ S.image some, z4 p (Q o) :=
              prod_le_prod (fun _ _ => (exp_pos _).le) v8
      calc exp (-13 * (A.card : ℝ))
          = exp (-8 * (A.card : ℝ)) * exp (-5 * (A.card : ℝ)) := by
              rw [← exp_add]; congr 1; ring
        _ ≤ z4 p (Q none) * ∏ o ∈ S.image some, z4 p (Q o) :=
            mul_le_mul v9 v6 (exp_pos _).le (ym hp0 hp1 _)
    have vq : z4 p (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
          ((U.filter (fun u => ∀ z ∈ A, (∃ w ∈ W_z z, adj f₂ u w) ↔ z ∈ S)).card : ℝ) <
            (1 / 2) * ((U.card : ℝ) * exp (-13 * (A.card : ℝ)))) ≤
        z4 p (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
          ((U.filter (fun u => P u f₂)).card : ℝ) <
            (1 / 2) * ((U.card : ℝ) * exp (-13 * (A.card : ℝ)))) := by
      refine zi hp0 hp1 fun f₂ hf₂ => ?_
      have vc : U.filter (fun u => P u f₂) ⊆
          U.filter (fun u => ∀ z ∈ A, (∃ w ∈ W_z z, adj f₂ u w) ↔ z ∈ S) := fun u hu => by
        rcases mem_filter.mp hu with ⟨huU, hPu⟩
        exact mem_filter.mpr ⟨huU, vo u huU f₂ hPu⟩
      have hle : ((U.filter (fun u => P u f₂)).card : ℝ) ≤
          ((U.filter (fun u => ∀ z ∈ A, (∃ w ∈ W_z z, adj f₂ u w) ↔ z ∈ S)).card : ℝ) :=
        Nat.cast_le.mpr (card_le_card vc)
      linarith
    exact vq.trans (yx U T vh hp0 hp1 P vp (exp_pos _).le vi)
  calc z4 p _
      ≤ ∑ S ∈ A.powerset, z4 p (fun f₂ =>
          ((U.filter (fun u => ∀ z ∈ A, (∃ w ∈ W_z z, adj f₂ u w) ↔ z ∈ S)).card : ℝ) <
            (1 / 2) * ((U.card : ℝ) * exp (-13 * (A.card : ℝ)))) :=
        y3 hp0 hp1 A.powerset _
    _ ≤ ∑ _S ∈ A.powerset, exp (-((U.card : ℝ) * exp (-13 * (A.card : ℝ))) / 8) :=
        sum_le_sum ve
    _ = ((2 : ℝ) ^ A.card) * exp (-((U.card : ℝ) * exp (-13 * (A.card : ℝ))) / 8) := by
        rw [sum_const, card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
lemma yo {κ : Type*} [DecidableEq κ] {n R : ℕ} (hR : 10000 ≤ R)
    (S_rev : Finset (z6 n))
    (y : Fin n) (B : Finset (Fin n)) (hyB : y ∉ B)
    (hB_hi : (B.card : ℝ) ≤ 2 * (R : ℝ))
    (hdisj_S : Disjoint S_rev (z8 {y} B))
    (idx : Finset κ) (P : κ → Finset (Fin n))
    (hP_sub : ∀ k ∈ idx, P k ⊆ B)
    (hP_disj : Set.PairwiseDisjoint (idx : Set κ) P)
    {r_min : ℝ} (hr0 : 0 ≤ r_min)
    (hP_lo : ∀ k ∈ idx, r_min * (R : ℝ) ≤ ((P k).card : ℝ)) :
    let p : ℝ := (R : ℝ)⁻¹
    let adj : ({e : z6 n // e ∉ S_rev} → Bool) → Fin n → Fin n → Prop :=
      fun f₂ u v => ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S_rev), f₂ ⟨z7 u v h, hmem⟩ = true
    r_min ^ idx.card * exp (-4 : ℝ) ≤
      z4 p (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
        (∀ k ∈ idx, ((P k).filter (fun u => adj f₂ y u)).card = 1) ∧
        (∀ u ∈ B \ idx.biUnion P, ¬ adj f₂ y u)) := by
  classical
  set p : ℝ := (R : ℝ)⁻¹
  have vg : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ R))
  have vc : p ≤ 1 / 2 := by
    rw [show p = (R : ℝ)⁻¹ from rfl, inv_le_comm₀ vg (by norm_num)]
    have : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 2 ≤ R)
    linarith
  let adj : ({e : z6 n // e ∉ S_rev} → Bool) → Fin n → Fin n → Prop :=
    fun f₂ u v => ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S_rev), f₂ ⟨z7 u v h, hmem⟩ = true
  have v0 : ∀ u ∈ B, y ≠ u := fun u hu h => hyB (h ▸ hu)
  have v4 : ∀ u (hu : u ∈ B), z7 y u (v0 u hu) ∉ S_rev := fun u hu =>
    disjoint_right.mp hdisj_S
      ((z5 {y} B (v0 u hu)).mpr (Or.inl ⟨mem_singleton_self y, hu⟩))
  let edgesOf : (C : Finset (Fin n)) → C ⊆ B → Finset {e : z6 n // e ∉ S_rev} :=
    fun C hC => C.attach.image (fun u =>
      ⟨z7 y u.1 (v0 u.1 (hC u.2)), v4 u.1 (hC u.2)⟩)
  have v2 : ∀ (C : Finset (Fin n)) (hC : C ⊆ B), (edgesOf C hC).card = C.card := by
    intro C hC
    dsimp only [edgesOf]
    rw [Finset.card_image_of_injective _ (fun u₁ u₂ heq => by
      rcases (ya (v0 u₁.1 (hC u₁.2)) (v0 u₂.1 (hC u₂.2))).mp
          (congrArg Subtype.val heq) with ⟨_, h⟩ | ⟨hyu, _⟩
      · exact Subtype.ext h
      · exact absurd hyu (v0 u₂.1 (hC u₂.2))), card_attach]
  have v1 : ∀ {C₁ C₂ : Finset (Fin n)} (h₁ : C₁ ⊆ B) (h₂ : C₂ ⊆ B),
      Disjoint C₁ C₂ → Disjoint (edgesOf C₁ h₁) (edgesOf C₂ h₂) := by
    intro C₁ C₂ h₁ h₂ hdisj
    rw [disjoint_left]
    intro e he₁ he₂
    rcases mem_image.mp he₁ with ⟨u₁, _, rfl⟩
    rcases mem_image.mp he₂ with ⟨u₂, _, heq⟩
    rcases zv heq with ⟨_, h⟩ | ⟨hyu, _⟩
    · exact disjoint_left.mp hdisj u₁.2 (h ▸ u₂.2)
    · exact v0 u₁.1 (h₁ u₁.2) hyu
  let allIdx : Finset (Option κ) := insert none (idx.image some)
  let blk : Option κ → Finset {e : z6 n // e ∉ S_rev} := fun o =>
    match o with
    | none => edgesOf (B \ idx.biUnion P) sdiff_subset
    | some k => if hk : k ∈ idx then edgesOf (P k) (hP_sub k hk) else ∅
  have vb : Set.PairwiseDisjoint (allIdx : Set (Option κ)) blk := by
    intro o₁ ho₁ o₂ ho₂ hne
    change Disjoint (blk o₁) (blk o₂)
    cases o₁ with
    | none =>
      cases o₂ with
      | none => exact absurd rfl hne
      | some k₂ =>
        have hk₂ : k₂ ∈ idx := by
          simp only [allIdx, mem_coe, mem_insert, mem_image,
            reduceCtorEq, false_or, Option.some.injEq] at ho₂
          rcases ho₂ with ⟨k', hk', rfl⟩; exact hk'
        dsimp only [blk]; rw [dif_pos hk₂]
        refine v1 sdiff_subset (hP_sub k₂ hk₂) ?_
        rw [disjoint_left]
        intro u hu₁ hu₂
        exact (mem_sdiff.mp hu₁).2 (mem_biUnion.mpr ⟨k₂, hk₂, hu₂⟩)
    | some k₁ =>
      have hk₁ : k₁ ∈ idx := by
        simp only [allIdx, mem_coe, mem_insert, mem_image,
          reduceCtorEq, false_or, Option.some.injEq] at ho₁
        rcases ho₁ with ⟨k', hk', rfl⟩; exact hk'
      cases o₂ with
      | none =>
        dsimp only [blk]; rw [dif_pos hk₁]
        refine v1 (hP_sub k₁ hk₁) sdiff_subset ?_
        rw [disjoint_left]
        intro u hu₁ hu₂
        exact (mem_sdiff.mp hu₂).2 (mem_biUnion.mpr ⟨k₁, hk₁, hu₁⟩)
      | some k₂ =>
        have hk₂ : k₂ ∈ idx := by
          simp only [allIdx, mem_coe, mem_insert, mem_image,
            reduceCtorEq, false_or, Option.some.injEq] at ho₂
          rcases ho₂ with ⟨k', hk', rfl⟩; exact hk'
        have vj : k₁ ≠ k₂ := fun h => hne (congrArg some h)
        dsimp only [blk]; rw [dif_pos hk₁, dif_pos hk₂]
        exact v1 (hP_sub k₁ hk₁) (hP_sub k₂ hk₂) (hP_disj hk₁ hk₂ vj)
  let Q : Option κ → ({e : z6 n // e ∉ S_rev} → Bool) → Prop := fun o f₂ =>
    match o with
    | none => ∀ x ∈ blk none, f₂ x = false
    | some k => ((blk (some k)).filter (fun x => f₂ x = true)).card = 1
  have vh : ∀ o ∈ allIdx, ∀ f g : {e : z6 n // e ∉ S_rev} → Bool,
      (∀ x ∈ blk o, f x = g x) → (Q o f ↔ Q o g) := by
    intro o _ f g hfg
    cases o with
    | none => exact forall₂_congr fun x hx => by rw [hfg x hx]
    | some k =>
      have hflt : (blk (some k)).filter (fun x => f x = true) =
          (blk (some k)).filter (fun x => g x = true) :=
        filter_congr fun x hx => by rw [hfg x hx]
      simp only [Q, hflt]
  have vf : z4 p (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
        (∀ k ∈ idx, ((P k).filter (fun u => adj f₂ y u)).card = 1) ∧
        (∀ u ∈ B \ idx.biUnion P, ¬ adj f₂ y u)) =
      z4 p (fun f₂ => ∀ o ∈ allIdx, Q o f₂) := by
    refine zx p fun f₂ => ?_
    have v6 : ∀ k (hk : k ∈ idx),
        ((P k).filter (fun u => adj f₂ y u)).card =
        ((blk (some k)).filter (fun x => f₂ x = true)).card := fun k hk => by
      dsimp only [blk]; rw [dif_pos hk]
      refine card_bij
        (fun u hu => ⟨z7 y u (v0 u (hP_sub k hk (mem_filter.mp hu).1)),
          v4 u (hP_sub k hk (mem_filter.mp hu).1)⟩)
        (fun u hu => by
          rcases mem_filter.mp hu with ⟨huP, ⟨_, _, hf⟩⟩
          exact mem_filter.mpr ⟨mem_image.mpr ⟨⟨u, huP⟩, mem_attach _ _, rfl⟩, hf⟩)
        (fun u₁ hu₁ u₂ hu₂ heq => by
          rcases zv heq with ⟨_, h⟩ | ⟨hyu, _⟩
          · exact h
          · exact absurd hyu (v0 u₂ (hP_sub k hk (mem_filter.mp hu₂).1)))
        (fun x hx => by
          rcases mem_filter.mp hx with ⟨hximg, hfx⟩
          dsimp only [edgesOf] at hximg
          rcases mem_image.mp hximg with ⟨⟨u, huP⟩, _, rfl⟩
          exact ⟨u, mem_filter.mpr ⟨huP, ⟨_, _, hfx⟩⟩, rfl⟩)
    constructor
    · rintro ⟨h1, h2⟩ o ho
      rcases mem_insert.mp ho with rfl | ho'
      · intro x hx
        rcases mem_image.mp hx with ⟨u, _, rfl⟩
        exact Bool.eq_false_iff.mpr fun ht => h2 u.1 u.2 ⟨_, _, ht⟩
      · rcases mem_image.mp ho' with ⟨k, hk, rfl⟩
        dsimp only [Q]; rw [← v6 k hk]; exact h1 k hk
    · intro hall
      refine ⟨fun k hk => ?_, fun u hu ⟨_, _, ht⟩ => ?_⟩
      · rw [v6 k hk]
        exact hall (some k) (mem_insert_of_mem (mem_image.mpr ⟨k, hk, rfl⟩))
      · have hmem : (⟨z7 y u (v0 u (sdiff_subset hu)),
            v4 u (sdiff_subset hu)⟩ : {e // e ∉ S_rev}) ∈ blk none :=
          mem_image.mpr ⟨⟨u, hu⟩, mem_attach _ _, rfl⟩
        have hff := hall none (mem_insert_self _ _) _ hmem
        rw [ht] at hff; exact Bool.noConfusion hff
  dsimp only
  rw [show z4 (R : ℝ)⁻¹ (fun f₂ : {e : z6 n // e ∉ S_rev} → Bool =>
        (∀ k ∈ idx, ((P k).filter (fun u =>
          ∃ (h : y ≠ u) (hmem : z7 y u h ∉ S_rev), f₂ ⟨z7 y u h, hmem⟩ = true)).card = 1) ∧
        (∀ u ∈ B \ idx.biUnion P,
          ¬ ∃ (h : y ≠ u) (hmem : z7 y u h ∉ S_rev), f₂ ⟨z7 y u h, hmem⟩ = true)) =
      z4 p (fun f₂ => ∀ o ∈ allIdx, Q o f₂) from vf,
    y5 allIdx blk vb p Q vh]
  have v8 : none ∉ idx.image some := by simp
  rw [prod_insert v8]
  have va : z4 p (Q none) = (1 - p) ^ (B \ idx.biUnion P).card := by
    rw [yb]; simp [z9, blk, v2]
  have v9 : ∀ k ∈ idx,
      r_min * (1 - p) ^ (P k).card ≤ z4 p (Q (some k)) := by
    intro k hk
    have heq : z4 p (Q (some k)) = ((P k).card : ℝ) * p * (1 - p) ^ ((P k).card - 1) := by
      dsimp only [Q]
      rw [z27]
      have vk : (blk (some k)).card = (P k).card := by
        dsimp only [blk]; rw [dif_pos hk]; exact v2 (P k) (hP_sub k hk)
      rw [vk, Nat.choose_one_right, pow_one]
    rw [heq]
    have vd : (1 - p) ^ (P k).card ≤ (1 - p) ^ ((P k).card - 1) := by
      by_cases h0 : (P k).card = 0
      · simp [h0]
      · have hpos : 1 ≤ (P k).card := by omega
        have : (1 - p) ^ (P k).card = (1 - p) ^ ((P k).card - 1) * (1 - p) := by
          rw [← pow_succ, Nat.sub_add_cancel hpos]
        rw [this]
        have hnn : 0 ≤ (1 - p) ^ ((P k).card - 1) := pow_nonneg (by linarith) _
        nlinarith
    have vi : r_min ≤ ((P k).card : ℝ) * p := by
      calc r_min = (r_min * (R : ℝ)) * (R : ℝ)⁻¹ := by field_simp
        _ ≤ ((P k).card : ℝ) * p := mul_le_mul_of_nonneg_right (hP_lo k hk) hp0
    exact mul_le_mul vi vd (pow_nonneg (by linarith) _) (by positivity)
  have v3 : (∏ k ∈ idx, (r_min * (1 - p) ^ (P k).card)) ≤
      ∏ o ∈ idx.image some, z4 p (Q o) := by
    rw [prod_image (fun _ _ _ _ h => Option.some_injective _ h)]
    exact prod_le_prod (fun _ _ => mul_nonneg hr0 (pow_nonneg (by linarith) _)) v9
  rw [prod_mul_distrib, prod_const, prod_pow_eq_pow_sum] at v3
  have v7 : (B \ idx.biUnion P).card + ∑ k ∈ idx, (P k).card = B.card := by
    have v5 : idx.biUnion P ⊆ B := biUnion_subset.mpr hP_sub
    rw [← card_biUnion (fun a ha b hb hne => hP_disj ha hb hne),
      card_sdiff, inter_eq_left.mpr v5]
    have hle : (idx.biUnion P).card ≤ B.card := card_le_card v5
    omega
  have ve : exp (-4 : ℝ) ≤ (1 - p) ^ B.card := by
    have h1mp := yt hp0 vc
    calc exp (-4 : ℝ)
        ≤ exp ((B.card : ℝ) * (-2 * p)) := by
          refine exp_le_exp.mpr ?_
          have : (B.card : ℝ) * (2 * p) ≤ 4 := by
            calc (B.card : ℝ) * (2 * p)
                ≤ (2 * (R : ℝ)) * (2 * (R : ℝ)⁻¹) := mul_le_mul_of_nonneg_right hB_hi (by positivity)
              _ = 4 := by field_simp; ring
          linarith
      _ = (exp (-2 * p)) ^ B.card := exp_nat_mul _ _
      _ ≤ (1 - p) ^ B.card := pow_le_pow_left₀ (exp_pos _).le h1mp _
  calc r_min ^ idx.card * exp (-4 : ℝ)
      ≤ r_min ^ idx.card * (1 - p) ^ B.card := mul_le_mul_of_nonneg_left ve (pow_nonneg hr0 _)
    _ = (1 - p) ^ (B \ idx.biUnion P).card * (r_min ^ idx.card * (1 - p) ^ ∑ k ∈ idx, (P k).card) := by
        rw [← v7, pow_add]; ring
    _ ≤ z4 p (Q none) * ∏ o ∈ idx.image some, z4 p (Q o) := by
        rw [va]
        exact mul_le_mul_of_nonneg_left v3 (pow_nonneg (by linarith) _)
lemma z05 {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S₀ S₁ : Finset (z6 n)) (hsub : S₀ ⊆ S₁)
    (f₀ : {e : z6 n // e ∈ S₀} → Bool)
    (A B : (z6 n → Bool) → Prop)
    (hA_dep : ∀ f g : z6 n → Bool, (∀ e ∈ S₁, f e = g e) → (A f ↔ A g))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcond : ∀ f₁ : {e : z6 n // e ∈ S₁} → Bool,
      (∀ x : {e // e ∈ S₀}, f₁ ⟨x.1, hsub x.2⟩ = f₀ x) →
      (∀ f₂ : {e // e ∉ S₁} → Bool, A (z0 S₁ f₁ f₂)) →
      z4 p (fun f₂ : {e // e ∉ S₁} → Bool => B (z0 S₁ f₁ f₂)) ≤ ε) :
    z4 p (fun f_rem : {e : z6 n // e ∉ S₀} → Bool =>
      A (z0 S₀ f₀ f_rem) ∧ B (z0 S₀ f₀ f_rem)) ≤ ε := by
  classical
  let T : Finset {e : z6 n // e ∉ S₀} := univ.filter (fun x => x.1 ∈ S₁)
  let mkF1 : ({x : {e : z6 n // e ∉ S₀} // x ∈ T} → Bool) → ({e : z6 n // e ∈ S₁} → Bool) :=
    fun g₁ y => if h0 : y.1 ∈ S₀ then f₀ ⟨y.1, h0⟩
      else g₁ ⟨⟨y.1, h0⟩, mem_filter.mpr ⟨mem_univ _, y.2⟩⟩
  let eRem : {x : {e : z6 n // e ∉ S₀} // x ∉ T} ≃ {e : z6 n // e ∉ S₁} :=
    { toFun := fun z => ⟨z.1.1, fun h1 => z.2 (mem_filter.mpr ⟨mem_univ _, h1⟩)⟩
      invFun := fun y => ⟨⟨y.1, fun h0 => y.2 (hsub h0)⟩, fun hT => y.2 (mem_filter.mp hT).2⟩
      left_inv := fun z => by ext; rfl
      right_inv := fun y => by ext; rfl }
  have v0 : ∀ (g₁ : {x : {e : z6 n // e ∉ S₀} // x ∈ T} → Bool)
      (g₂ : {x : {e : z6 n // e ∉ S₀} // x ∉ T} → Bool),
      z0 S₀ f₀ (z0 T g₁ g₂) =
        z0 S₁ (mkF1 g₁) (fun y => g₂ (eRem.symm y)) := by
    intro g₁ g₂
    funext e
    by_cases h0 : e ∈ S₀
    · have h1 : e ∈ S₁ := hsub h0
      simp [z0, mkF1, h0, h1]
    · by_cases h1 : e ∈ S₁
      · have hT : (⟨e, h0⟩ : {e // e ∉ S₀}) ∈ T := mem_filter.mpr ⟨mem_univ _, h1⟩
        simp [z0, mkF1, h0, h1, hT]
      · have v5 : (⟨e, h0⟩ : {e // e ∉ S₀}) ∉ T := fun h => h1 (mem_filter.mp h).2
        simp [z0, eRem, h0, h1, v5]
  refine wk hp0 hp1 T
    (fun f_rem => A (z0 S₀ f₀ f_rem))
    (fun f_rem => B (z0 S₀ f₀ f_rem)) ?_ ε hε ?_
  · intro g₁ g₂ g₂'
    refine hA_dep _ _ fun e he1 => ?_
    rw [v0, v0]
    simp [z0, he1]
  · intro g₁ hAg₁
    have v4 : ∀ x : {e // e ∈ S₀}, mkF1 g₁ ⟨x.1, hsub x.2⟩ = f₀ x := by
      intro x; simp [mkF1, x.2]
    have hA1 : ∀ f₂ : {e // e ∉ S₁} → Bool, A (z0 S₁ (mkF1 g₁) f₂) := by
      intro f₂
      have := hAg₁ (fun z => f₂ (eRem z))
      rw [v0] at this
      have hfun : (fun y : {e // e ∉ S₁} => f₂ (eRem (eRem.symm y))) = f₂ := by
        funext y; simp
      rwa [hfun] at this
    have v3 := hcond (mkF1 g₁) v4 hA1
    have hbij : z4 p (fun g₂ : {x : {e : z6 n // e ∉ S₀} // x ∉ T} → Bool =>
          B (z0 S₀ f₀ (z0 T g₁ g₂))) =
        z4 p (fun f₂ : {e // e ∉ S₁} → Bool => B (z0 S₁ (mkF1 g₁) f₂)) := by
      unfold z4
      let eFun : ({x : {e : z6 n // e ∉ S₀} // x ∉ T} → Bool) ≃ ({e : z6 n // e ∉ S₁} → Bool) :=
        Equiv.arrowCongr eRem (Equiv.refl Bool)
      refine Fintype.sum_equiv eFun _ _ fun g₂ => ?_
      have v2 : B (z0 S₀ f₀ (z0 T g₁ g₂)) ↔ B (z0 S₁ (mkF1 g₁) (eFun g₂)) := by
        rw [v0]
        have heq : (fun y : {e // e ∉ S₁} => g₂ (eRem.symm y)) = eFun g₂ := rfl
        rw [heq]
      have v1 : (∏ z : {x : {e : z6 n // e ∉ S₀} // x ∉ T}, z9 p (g₂ z)) =
          ∏ y : {e : z6 n // e ∉ S₁}, z9 p (eFun g₂ y) :=
        Fintype.prod_equiv eRem _ _ fun z => by simp [eFun]
      by_cases hB : B (z0 S₀ f₀ (z0 T g₁ g₂))
      · rw [if_pos hB, if_pos (v2.mp hB), v1]
      · rw [if_neg hB, if_neg (fun h => hB (v2.mpr h))]
    rw [hbij]
    exact v3
lemma zu {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S₀ S₁ : Finset (z6 n)) (hsub : S₀ ⊆ S₁)
    (f₀ : {e : z6 n // e ∈ S₀} → Bool)
    (A B : (z6 n → Bool) → Prop)
    (hA_dep : ∀ f g : z6 n → Bool, (∀ e ∈ S₁, f e = g e) → (A f ↔ A g))
    {ε₁ ε₂ : ℝ} (hε₂ : 0 ≤ ε₂)
    (hfailA : z4 p (fun f_rem : {e : z6 n // e ∉ S₀} → Bool =>
      ¬ A (z0 S₀ f₀ f_rem)) ≤ ε₁)
    (hcond : ∀ f₁ : {e : z6 n // e ∈ S₁} → Bool,
      (∀ x : {e // e ∈ S₀}, f₁ ⟨x.1, hsub x.2⟩ = f₀ x) →
      (∀ f₂ : {e // e ∉ S₁} → Bool, A (z0 S₁ f₁ f₂)) →
      z4 p (fun f₂ : {e // e ∉ S₁} → Bool => B (z0 S₁ f₁ f₂)) ≤ ε₂) :
    z4 p (fun f_rem : {e : z6 n // e ∉ S₀} → Bool =>
      B (z0 S₀ f₀ f_rem)) ≤ ε₁ + ε₂ := by
  have h1 : z4 p (fun f_rem : {e : z6 n // e ∉ S₀} → Bool => B (z0 S₀ f₀ f_rem)) ≤
      z4 p (fun f_rem => ¬ A (z0 S₀ f₀ f_rem) ∨
        (A (z0 S₀ f₀ f_rem) ∧ B (z0 S₀ f₀ f_rem))) :=
    zi hp0 hp1 fun f_rem hB => by
      by_cases hA : A (z0 S₀ f₀ f_rem)
      · exact Or.inr ⟨hA, hB⟩
      · exact Or.inl hA
  have h2 := yr hp0 hp1
    (fun f_rem : {e : z6 n // e ∉ S₀} → Bool => ¬ A (z0 S₀ f₀ f_rem))
    (fun f_rem => A (z0 S₀ f₀ f_rem) ∧ B (z0 S₀ f₀ f_rem))
  have h3 := z05 hp0 hp1 S₀ S₁ hsub f₀ A B hA_dep ε₂ hε₂ hcond
  linarith
end
section
open scoped BigOperators Classical
open Finset Real Nat
lemma zb {n : ℕ} (S : Finset (z6 n))
    (f₁ : {e : z6 n // e ∈ S} → Bool) (f₂ : {e : z6 n // e ∉ S} → Bool)
    {u v : Fin n} (huv : u ≠ v) (hnot : z7 u v huv ∉ S) :
    (z1 (z0 S f₁ f₂)).Adj u v ↔
      ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S), f₂ ⟨z7 u v h, hmem⟩ = true := by
  rw [za (z0 S f₁ f₂) huv]
  simp only [z0, dif_neg hnot]
  exact ⟨fun h => ⟨huv, hnot, h⟩, fun ⟨_, _, h⟩ => h⟩
lemma zf {n : ℕ} (S : Finset (z6 n))
    (f₁ : {e : z6 n // e ∈ S} → Bool) (f₂ : {e : z6 n // e ∉ S} → Bool)
    {u v : Fin n} (huv : u ≠ v) (hmem : z7 u v huv ∈ S) :
    (z1 (z0 S f₁ f₂)).Adj u v ↔ f₁ ⟨z7 u v huv, hmem⟩ = true := by
  rw [za (z0 S f₁ f₂) huv]
  simp only [z0, dif_pos hmem]
lemma yq {q n : ℕ} (hq : 2 ≤ q) (a : Fin (kOf q) → Fin n)
    (P : Finset (Fin n)) (haP : ∀ r : Fin (kOf q), a r ∈ P)
    (f g : z6 n → Bool) (hfg : ∀ e ∈ ze P, f e = g e) :
    (∀ u ∈ P, ∀ v : Fin n, (z1 f).Adj u v ↔ (z1 g).Adj u v) ∧
    zk q hq (z1 f) a = zk q hq (z1 g) a ∧
    zm q hq (z1 f) a = zm q hq (z1 g) a ∧
    zg q hq (z1 f) a = zg q hq (z1 g) a ∧
    domFinset q hq (z1 f) a = domFinset q hq (z1 g) a ∧
    (∀ x ∈ P, zh q hq (z1 f) a x = zh q hq (z1 g) a x) := by
  classical
  have hadj : ∀ u ∈ P, ∀ v : Fin n, (z1 f).Adj u v ↔ (z1 g).Adj u v := by
    intro u hu v
    by_cases huv : u = v
    · subst huv; simp
    · rw [za f huv, za g huv,
        hfg (z7 u v huv) ((z0p P huv).mpr (Or.inl hu))]
  have v0 : ∀ v : Fin n, ∀ u ∈ P, (z1 f).Adj v u ↔ (z1 g).Adj v u :=
    fun v u hu => by rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (G := z1 g)]; exact hadj u hu v
  have v2 : ∀ z, isBc q hq (z1 f) a z ↔ isBc q hq (z1 g) a z := fun z =>
    forall_congr' fun i => v0 z _ (haP _)
  have v1 : ∀ z, isBc' q hq (z1 f) a z ↔ isBc' q hq (z1 g) a z := fun z =>
    forall_congr' fun i => v0 z _ (haP _)
  have hBc : zk q hq (z1 f) a = zk q hq (z1 g) a := by
    ext z; unfold zk; simp [v2]
  have hBc' : zm q hq (z1 f) a = zm q hq (z1 g) a := by
    ext z; unfold zm; simp [v1]
  have hBb : zg q hq (z1 f) a = zg q hq (z1 g) a := by
    ext w
    simp only [y8, z0m, v2, v1]
    exact and_congr_right fun _ => forall_congr' fun j => v0 w _ (haP _)
  have hDom : domFinset q hq (z1 f) a = domFinset q hq (z1 g) a := by
    ext x
    simp only [mem_domFinset, inDom, v1, v0 x (w7 q hq a) (haP (dIdx q hq))]
  have hAx : ∀ x ∈ P, zh q hq (z1 f) a x = zh q hq (z1 g) a x := by
    intro x hx; ext z
    simp only [zt, Ax, v2, v0 z x hx]
  exact ⟨hadj, hBc, hBc', hBb, hDom, hAx⟩
lemma yf (q m : ℕ) (hlp : LargeParams q m) :
    exp (-((ROf m : ℝ)) / 200) ≤ exp (-((R8Of m : ℝ)) / 64) ∧
    (R8Of m : ℝ) ≤ ((ROf m : ℝ) / 8) * exp (-13 * (zd (m - 1) : ℝ)) ∧
    exp (-((ROf m : ℝ) / 8 * exp (-13 * (zd (m - 1) : ℝ))) / 8) ≤
      exp (-((R8Of m : ℝ)) / 64) ∧
    ((R8Of m : ℝ))⁻¹ ≤ exp (-20 * (m : ℝ) * (zd (m - 1) : ℝ) ^ 2 - 100) := by
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
  have v0 : (0 : ℝ) < (R8 : ℝ) := by linarith
  have v2 : (R : ℝ) = (R8 : ℝ) ^ 8 := by exact_mod_cast zq m
  have v3 : 10000 * (R8 : ℝ) ^ 2 ≤ (R : ℝ) := by
    rw [v2]
    have h2 : (R8 : ℝ) ^ 3 ≤ (R8 : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith [pow_pos v0 2]
  have h1 : exp (-((R : ℝ)) / 200) ≤ exp (-((R8 : ℝ)) / 64) := by
    refine exp_le_exp.mpr ?_
    have : 10000 * (R8 : ℝ) ≤ (R : ℝ) := by nlinarith
    linarith
  have v1 : exp (13 * (T : ℝ)) ≤ (R8 : ℝ) := by
    have hle : 13 * (T : ℝ) ≤ 20 * (m : ℝ) * (T : ℝ) ^ 2 + 100 := by
      have hm10 : (10 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlp.hm
      have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast z03 (m - 1)
      nlinarith
    exact (exp_le_exp.mpr hle).trans hlp.hexp_T_le_R8
  have h2 : (R8 : ℝ) ≤ ((R : ℝ) / 8) * exp (-13 * (T : ℝ)) := by
    rw [show -13 * (T : ℝ) = -(13 * (T : ℝ)) by ring, exp_neg,
      ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)]
    calc (R8 : ℝ) * exp (13 * (T : ℝ)) ≤ (R8 : ℝ) * (R8 : ℝ) :=
          mul_le_mul_of_nonneg_left v1 v0.le
      _ = (R8 : ℝ) ^ 2 := (sq _).symm
      _ ≤ (R : ℝ) / 8 := by linarith
  have h3 : exp (-((R : ℝ) / 8 * exp (-13 * (T : ℝ))) / 8) ≤
      exp (-((R8 : ℝ)) / 64) :=
    exp_le_exp.mpr (by linarith)
  have h4 : ((R8 : ℝ))⁻¹ ≤ exp (-20 * (m : ℝ) * (T : ℝ) ^ 2 - 100) := by
    rw [show -20 * (m : ℝ) * (T : ℝ) ^ 2 - 100 = -(20 * (m : ℝ) * (T : ℝ) ^ 2 + 100) by ring,
      exp_neg]
    exact inv_anti₀ (exp_pos _) hlp.hexp_T_le_R8
  exact ⟨h1, h2, h3, h4⟩
private lemma z1h (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (a : Fin (kOf q) → Fin (nOf q m)) (x₀ : Fin (nOf q m))
    (mkA : SimpleGraph (Fin (nOf q m)) → Finset (Fin (nOf q m)))
    (hA_dep : ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ ze (univ.image a ∪ {x₀}), f e = g e) →
      mkA (z1 f) = mkA (z1 g))
    (f₀ : {e : z6 (nOf q m) // e ∈ ze (univ.image a ∪ {x₀})} → Bool)
    (B_all B_sub B_rest : Finset (Fin (nOf q m)))
    (hB_sub_le : B_sub ⊆ B_all) (hB_rest_eq : B_rest = B_all \ B_sub)
    (hB_rest_lo : (1 / 12 : ℝ) * ((ROf m : ℝ) ^ 2) ≤ (B_rest.card : ℝ))
    (hB_all_eq : B_all = (zg q hq (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false))) a).erase x₀)
    (hBb_x₀ : x₀ ∈ zg q hq (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false))) a →
      ((zg q hq (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false))) a ∩
        zc (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false))) (fun _ : Fin 1 => x₀)).card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hA_card : (mkA (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false)))).card ≤ zd (m - 1))
    (hdisj_PB : Disjoint (univ.image a ∪ {x₀}) B_all)
    (hdisj_BA : Disjoint B_all (mkA (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false)))))
    (f₁ : {e : z6 (nOf q m) // e ∈ ze (univ.image a ∪ {x₀}) ∪
      z8 B_all (mkA (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false))))} → Bool)
    (hagree : ∀ x : {e // e ∈ ze (univ.image a ∪ {x₀})},
      f₁ ⟨x.1, subset_union_left x.2⟩ = f₀ x)
    (hW_hi : ∀ z ∈ mkA (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false))),
      ((B_all.filter (fun w => (z1 (z0 _ f₁ (fun _ => false))).Adj w z)).card : ℝ) ≤ 4 * (ROf m : ℝ))
    (hW_only_lo : ∀ z ∈ mkA (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false))),
      (ROf m : ℝ) / 48 ≤
        ((B_sub.filter (fun w => (z1 (z0 _ f₁ (fun _ => false))).Adj w z ∧
          ∀ z' ∈ mkA (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false))),
            z' ≠ z → ¬ (z1 (z0 _ f₁ (fun _ => false))).Adj w z')).card : ℝ)) :
    z4 ((ROf m : ℝ)⁻¹)
      (fun f₂ : {e : z6 (nOf q m) // e ∉ ze (univ.image a ∪ {x₀}) ∪
          z8 B_all (mkA (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false))))} → Bool =>
        ¬ ∀ S ⊆ mkA (z1 (z0 _ f₁ f₂)),
          ∃ v : Fin (nOf q m), ∀ z ∈ mkA (z1 (z0 _ f₁ f₂)),
            Rrel q hq (z1 (z0 _ f₁ f₂)) a v z ↔ z ∈ S) ≤
      ((2 : ℝ) ^ (mkA (z1 (z0 (ze (univ.image a ∪ {x₀})) f₀ (fun _ => false)))).card) *
        exp (-((R8Of m : ℝ)) / 64) := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set p : ℝ := (R : ℝ)⁻¹
  have vg : R8 ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have vj : 10000 ≤ R := le_trans hlp.hR8_ge vg
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have ve : T ≤ R8 := le_trans (Nat.le_self_pow (by norm_num) T) (Nat.le_of_lt Nat.lt_two_pow_self)
  have vf : (R : ℝ) = (R8 : ℝ) ^ 8 := by exact_mod_cast zq m
  have vm := yf q m hlp
  let P : Finset (Fin (nOf q m)) := univ.image a ∪ {x₀}
  let S₀ : Finset (z6 (nOf q m)) := ze P
  have haP : ∀ r : Fin (kOf q), a r ∈ P := fun r =>
    mem_union_left _ (mem_image.mpr ⟨r, mem_univ _, rfl⟩)
  have hx₀P : x₀ ∈ P := mem_union_right _ (mem_singleton_self x₀)
  let G₀ := z1 (z0 S₀ f₀ (fun _ => false))
  let Bb := zg q hq G₀ a
  let A := mkA G₀
  let S₁ : Finset (z6 (nOf q m)) := S₀ ∪ z8 B_all A
  let G₁ := z1 (z0 S₁ f₁ (fun _ => false))
  have vr : ∀ f₂ : {e // e ∉ S₁} → Bool,
      (∀ u ∈ P, ∀ v : Fin (nOf q m), (z1 (z0 S₁ f₁ f₂)).Adj u v ↔ G₀.Adj u v) ∧
      zg q hq (z1 (z0 S₁ f₁ f₂)) a = Bb ∧
      mkA (z1 (z0 S₁ f₁ f₂)) = A ∧
      (∀ w ∈ B_all, ∀ z ∈ A, (z1 (z0 S₁ f₁ f₂)).Adj w z ↔ G₁.Adj w z) := by
    intro f₂
    have hS0 : ∀ e ∈ S₀, z0 S₁ f₁ f₂ e = z0 S₀ f₀ (fun _ => false) e := by
      intro e he0
      have he1 : e ∈ S₁ := subset_union_left he0
      simp only [z0, dif_pos he1, dif_pos he0]
      exact hagree ⟨e, he0⟩
    have h1 := yq hq a P haP _ _ hS0
    have h2 := hA_dep _ _ hS0
    have h3 : ∀ w ∈ B_all, ∀ z ∈ A,
        (z1 (z0 S₁ f₁ f₂)).Adj w z ↔ G₁.Adj w z := by
      intro w hw z hz
      have hne : w ≠ z := fun h => disjoint_left.mp hdisj_BA hw (h ▸ hz)
      have hmem : z7 w z hne ∈ S₁ :=
        mem_union_right _ ((z5 B_all A hne).mpr (Or.inl ⟨hw, hz⟩))
      rw [zf S₁ f₁ f₂ hne hmem, zf S₁ f₁ (fun _ => false) hne hmem]
    exact ⟨h1.1, h1.2.2.2.1, h2, h3⟩
  let W_z : Fin (nOf q m) → Finset (Fin (nOf q m)) := fun z => B_all.filter (fun w => G₁.Adj w z)
  let vp : Fin (nOf q m) → Finset (Fin (nOf q m)) := fun z =>
    B_sub.filter (fun w => G₁.Adj w z ∧ ∀ z' ∈ A, z' ≠ z → ¬ G₁.Adj w z')
  let v0 : Finset (Fin (nOf q m)) := A.biUnion W_z
  have v2 : v0 ⊆ B_all := biUnion_subset.mpr fun z _ => filter_subset _ _
  have v8 : (v0.card : ℝ) ≤ 4 * (A.card : ℝ) * (R : ℝ) := by
    have h1 : (v0.card : ℝ) ≤ ∑ z ∈ A, ((W_z z).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    calc (v0.card : ℝ) ≤ ∑ z ∈ A, ((W_z z).card : ℝ) := h1
      _ ≤ ∑ _z ∈ A, (4 * (R : ℝ)) := sum_le_sum fun z hz => hW_hi z hz
      _ = 4 * (A.card : ℝ) * (R : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
  let U : Finset (Fin (nOf q m)) :=
    if x₀ ∈ Bb then (B_rest \ v0).filter (fun u => ¬ G₀.Adj u x₀) else B_rest \ v0
  have v3 : U ⊆ B_rest := by
    dsimp only [U]; split_ifs
    · exact (filter_subset _ _).trans sdiff_subset
    · exact sdiff_subset
  have v4 : Disjoint U v0 := by
    rw [disjoint_left]; intro u huU huW
    dsimp only [U] at huU; split_ifs at huU
    · exact (mem_sdiff.mp (mem_filter.mp huU).1).2 huW
    · exact (mem_sdiff.mp huU).2 huW
  have hU_not_x₀ : ∀ u ∈ U, x₀ ∈ Bb → ¬ G₀.Adj u x₀ := by
    intro u huU hx₀
    dsimp only [U] at huU; rw [if_pos hx₀] at huU
    exact (mem_filter.mp huU).2
  have vt : (R : ℝ) / 8 ≤ (U.card : ℝ) := by
    have vs : B_rest.card ≤ (B_rest \ v0).card + v0.card := by
      have h1 := card_sdiff (s := v0) (t := B_rest)
      have h2 : (v0 ∩ B_rest).card ≤ v0.card := card_le_card inter_subset_left
      omega
    have vl : (B_rest.card : ℝ) - (v0.card : ℝ) ≤ ((B_rest \ v0).card : ℝ) := by
      have hc : (B_rest.card : ℝ) ≤ ((B_rest \ v0).card : ℝ) + (v0.card : ℝ) := by exact_mod_cast vs
      linarith
    have v9 : ((B_rest \ v0).card : ℝ) - 2 * (R : ℝ) ≤ (U.card : ℝ) := by
      dsimp only [U]
      split_ifs with hx₀
      · have vo : ((B_rest \ v0).filter (fun u => G₀.Adj u x₀)).card ≤
            (Bb ∩ zc G₀ (fun _ : Fin 1 => x₀)).card := by
          refine card_le_card fun u hu => ?_
          rcases mem_filter.mp hu with ⟨hu1, hadj⟩
          have vk : u ∈ B_all := by
            have := sdiff_subset hu1; rw [hB_rest_eq] at this; exact sdiff_subset this
          refine mem_inter.mpr ⟨mem_of_mem_erase (hB_all_eq ▸ vk), ?_⟩
          rw [zl]; intro _; exact hadj
        have vq : ((B_rest \ v0).filter (fun u => ¬ G₀.Adj u x₀)).card +
            ((B_rest \ v0).filter (fun u => G₀.Adj u x₀)).card = (B_rest \ v0).card := by
          rw [← card_union_of_disjoint (disjoint_filter.mpr fun _ _ h1 h2 => h1 h2),
            union_comm, filter_union_filter_not_eq]
        have h1 : (((B_rest \ v0).filter (fun u => G₀.Adj u x₀)).card : ℝ) ≤ 2 * (R : ℝ) :=
          (Nat.cast_le.mpr vo).trans (hBb_x₀ hx₀)
        have h2 : (((B_rest \ v0).filter (fun u => ¬ G₀.Adj u x₀)).card : ℝ) +
            (((B_rest \ v0).filter (fun u => G₀.Adj u x₀)).card : ℝ) = ((B_rest \ v0).card : ℝ) := by
          exact_mod_cast vq
        linarith
      · linarith
    have va : (A.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hA_card
    have hTR : 4 * (T : ℝ) + 4 ≤ (1 / 24 : ℝ) * (R : ℝ) := by
      have h1 : (T : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast ve
      have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
      have vv : 10000 * (R8 : ℝ) ≤ (R : ℝ) := by
        rw [vf]
        have : (R8 : ℝ) ^ 2 ≤ (R8 : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
        nlinarith only [hR8_ge, this]
      linarith
    have vu : (10000 : ℝ) ≤ (R : ℝ) := by exact_mod_cast vj
    nlinarith only [hB_rest_lo, v8, vl, v9, va, hTR, vu]
  have v7 : B_rest ⊆ B_all := by rw [hB_rest_eq]; exact sdiff_subset
  have v1 : Disjoint S₁ (z8 U v0) := by
    rw [disjoint_union_left]
    refine ⟨zo
        (hdisj_PB.mono_right (v3.trans v7))
        (hdisj_PB.mono_right v2), ?_⟩
    rw [disjoint_left]
    intro ⟨e, he⟩ he1 he2
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
      have h1 := (z5 B_all A huv).mp he1
      have h2 := (z5 U v0 huv).mp he2
      have vd : U ⊆ B_all := v3.trans v7
      rcases h1 with ⟨_, hvA⟩ | ⟨_, huA⟩ <;> rcases h2 with ⟨huU, hvW⟩ | ⟨hvU, huW⟩
      · exact disjoint_left.mp hdisj_BA (v2 hvW) hvA
      · exact disjoint_left.mp hdisj_BA (vd hvU) hvA
      · exact disjoint_left.mp hdisj_BA (vd huU) huA
      · exact disjoint_left.mp hdisj_BA (v2 huW) huA
  have vb : z4 p (fun f₂ : {e // e ∉ S₁} → Bool =>
        ¬ ∀ S ⊆ mkA (z1 (z0 S₁ f₁ f₂)),
          ∃ v : Fin (nOf q m), ∀ z ∈ mkA (z1 (z0 S₁ f₁ f₂)),
            Rrel q hq (z1 (z0 S₁ f₁ f₂)) a v z ↔ z ∈ S) ≤
      z4 p (fun f₂ : {e // e ∉ S₁} → Bool =>
        ∃ S ∈ A.powerset,
          ((U.filter (fun u => ∀ z ∈ A,
            (∃ w ∈ W_z z, ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S₁),
              f₂ ⟨z7 u w h, hmem⟩ = true) ↔ z ∈ S)).card : ℝ) <
            (1 / 2) * ((U.card : ℝ) * exp (-13 * (A.card : ℝ)))) := by
    refine zi hp0 hp1 fun f₂ hbad => ?_
    have hfx := vr f₂
    rw [hfx.2.2.1] at hbad
    simp only [not_forall, not_exists] at hbad
    rcases hbad with ⟨S, hSA, hno_v⟩
    refine ⟨S, mem_powerset.mpr hSA, ?_⟩
    have hemp : U.filter (fun u => ∀ z ∈ A,
        (∃ w ∈ W_z z, ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S₁),
          f₂ ⟨z7 u w h, hmem⟩ = true) ↔ z ∈ S) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro u hu
      rcases mem_filter.mp hu with ⟨huU, hpat⟩
      rcases hno_v u with ⟨z, hzA, hne_iff⟩
      apply hne_iff
      rw [w3, hfx.2.1, ← hpat z hzA]
      constructor
      · rintro ⟨w, hwBb, hwu, hwz⟩
        have hw_ne_x₀ : w ≠ x₀ := by
          intro hw_eq; subst hw_eq
          exact hU_not_x₀ u huU hwBb ((hfx.1 w hx₀P u).mp hwu).symm
        have v6 : w ∈ B_all := hB_all_eq.symm ▸ mem_erase.mpr ⟨hw_ne_x₀, hwBb⟩
        have hwWz : w ∈ W_z z := mem_filter.mpr ⟨v6, (hfx.2.2.2 w v6 z hzA).mp hwz⟩
        have v5 : w ∈ v0 := mem_biUnion.mpr ⟨z, hzA, hwWz⟩
        have huw : u ≠ w := fun h => disjoint_left.mp v4 huU (h ▸ v5)
        have vc : z7 u w huw ∉ S₁ :=
          disjoint_right.mp v1 ((z5 U v0 huw).mpr (Or.inl ⟨huU, v5⟩))
        exact ⟨w, hwWz, (zb S₁ f₁ f₂ huw vc).mp hwu.symm⟩
      · rintro ⟨w, hwWz, hrem⟩
        have v6 : w ∈ B_all := (mem_filter.mp hwWz).1
        have v5 : w ∈ v0 := mem_biUnion.mpr ⟨z, hzA, hwWz⟩
        have huw : u ≠ w := fun h => disjoint_left.mp v4 huU (h ▸ v5)
        have vc : z7 u w huw ∉ S₁ :=
          disjoint_right.mp v1 ((z5 U v0 huw).mpr (Or.inl ⟨huU, v5⟩))
        have hwu : (z1 (z0 S₁ f₁ f₂)).Adj w u :=
          ((zb S₁ f₁ f₂ huw vc).mpr hrem).symm
        have hwz : (z1 (z0 S₁ f₁ f₂)).Adj w z :=
          (hfx.2.2.2 w v6 z hzA).mpr (mem_filter.mp hwWz).2
        exact ⟨w, mem_of_mem_erase (hB_all_eq ▸ v6), hwu, hwz⟩
    rw [hemp, card_empty, Nat.cast_zero]
    have vn : (0 : ℝ) < (U.card : ℝ) := by
      have : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (R_pos m)
      linarith
    exact mul_pos (by norm_num) (mul_pos vn (exp_pos _))
  have vh := yj vj S₁ A v0 U vp W_z
    v8
    (fun z _ => fun w hw => mem_filter.mpr ⟨hB_sub_le (mem_filter.mp hw).1,
      (mem_filter.mp hw).2.1⟩)
    (fun z hz => fun w hw => mem_biUnion.mpr ⟨z, hz, hw⟩)
    hW_only_lo
    (fun z₁ _ z₂ hz₂ hne => by
      rw [disjoint_left]; intro w hw1 hw2
      exact (mem_filter.mp hw1).2.2 z₂ hz₂ hne.symm (mem_filter.mp hw2).2)
    v4 v1
  have vi : exp (-((U.card : ℝ) * exp (-13 * (A.card : ℝ))) / 8) ≤
      exp (-((R8 : ℝ)) / 64) := by
    have va : (A.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hA_card
    have h1 : exp (-13 * (T : ℝ)) ≤ exp (-13 * (A.card : ℝ)) :=
      exp_le_exp.mpr (by linarith)
    have h2 : ((R : ℝ) / 8) * exp (-13 * (T : ℝ)) ≤
        (U.card : ℝ) * exp (-13 * (A.card : ℝ)) :=
      mul_le_mul vt h1 (exp_pos _).le (Nat.cast_nonneg _)
    exact (exp_le_exp.mpr (by linarith)).trans vm.2.2.1
  calc z4 p (fun f₂ : {e // e ∉ S₁} → Bool =>
        ¬ ∀ S ⊆ mkA (z1 (z0 S₁ f₁ f₂)),
          ∃ v : Fin (nOf q m), ∀ z ∈ mkA (z1 (z0 S₁ f₁ f₂)),
            Rrel q hq (z1 (z0 S₁ f₁ f₂)) a v z ↔ z ∈ S)
      ≤ ((2 : ℝ) ^ A.card) * exp (-((U.card : ℝ) * exp (-13 * (A.card : ℝ))) / 8) :=
        vb.trans vh
    _ ≤ ((2 : ℝ) ^ A.card) * exp (-((R8 : ℝ)) / 64) :=
        mul_le_mul_of_nonneg_left vi (pow_nonneg (by norm_num) _)
lemma wp (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (a : Fin (kOf q) → Fin (nOf q m)) (hinj : Function.Injective a)
    (x₀ : Fin (nOf q m))
    (mkA : SimpleGraph (Fin (nOf q m)) → Finset (Fin (nOf q m)))
    (hA_dep : ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ ze (univ.image a ∪ {x₀}), f e = g e) →
      mkA (z1 f) = mkA (z1 g))
    (hA_sub_Bc : ∀ G : SimpleGraph (Fin (nOf q m)),
      mkA G ⊆ zk q hq G a ∪ zm q hq G a)
    (hA_disj_P : ∀ G : SimpleGraph (Fin (nOf q m)),
      Disjoint (univ.image a ∪ {x₀}) (mkA G)) :
    gProb (nOf q m) ((ROf m : ℝ)⁻¹)
      (EventE1 q (nOf q m) (KOf q m) ∩ EventEdeg q (nOf q m) (ROf m) ∩
        {G | (mkA G).card ≤ zd (m - 1) ∧
          ¬ ∀ S ⊆ mkA G, ∃ v : Fin (nOf q m), ∀ z ∈ mkA G, Rrel q hq G a v z ↔ z ∈ S}) ≤
      ((2 : ℝ) ^ (zd (m - 1) + 2)) * exp (-((R8Of m : ℝ)) / 64) := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set p : ℝ := (R : ℝ)⁻¹
  have ve : R8 ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have va : 10000 ≤ R := le_trans hlp.hR8_ge ve
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have vl : T ≤ R8 := le_trans (Nat.le_self_pow (by norm_num) T) (Nat.le_of_lt Nat.lt_two_pow_self)
  have vj := yf q m hlp
  let P : Finset (Fin (nOf q m)) := univ.image a ∪ {x₀}
  let S₀ : Finset (z6 (nOf q m)) := ze P
  have haP : ∀ r : Fin (kOf q), a r ∈ P := fun r =>
    mem_union_left _ (mem_image.mpr ⟨r, mem_univ _, rfl⟩)
  have hx₀P : x₀ ∈ P := mem_union_right _ (mem_singleton_self x₀)
  let Good0 : Set (SimpleGraph (Fin (nOf q m))) :=
    {G | (1 / 4 : ℝ) * ((R : ℝ) ^ 2) ≤ ((zg q hq G a).card : ℝ) ∧
         ((zg q hq G a).card : ℝ) ≤ 2 * ((R : ℝ) ^ 2) ∧
         (x₀ ∈ zg q hq G a →
           ((zg q hq G a ∩ zc G (fun _ : Fin 1 => x₀)).card : ℝ) ≤ 2 * (R : ℝ)) ∧
         (mkA G).card ≤ T}
  let Bad : Set (SimpleGraph (Fin (nOf q m))) :=
    {G | ¬ ∀ S ⊆ mkA G, ∃ v : Fin (nOf q m), ∀ z ∈ mkA G, Rrel q hq G a v z ↔ z ∈ S}
  have v7 :
      EventE1 q (nOf q m) (KOf q m) ∩ EventEdeg q (nOf q m) (ROf m) ∩
        {G | (mkA G).card ≤ T ∧ G ∈ Bad} ⊆ Good0 ∩ Bad := by
    rintro G ⟨⟨hE1, hEdeg⟩, hcardA, hbad⟩
    have hdet := yw q m hq hlp hE1 hEdeg a hinj
    refine ⟨⟨hdet.2.2.2.1.1, hdet.2.2.2.1.2, ?_, hcardA⟩, hbad⟩
    intro hx₀Bb
    exact hdet.2.2.2.2 x₀ ((y8 q hq G a x₀).mp hx₀Bb).1.1
  refine (gProb_mono hp0 hp1 v7).trans ?_
  refine w4 hp0 hp1 S₀ Good0 Bad ?_
    (((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) (by positivity) ?_
  · intro f₀ f₂ f₂'
    have vh : ∀ e ∈ S₀, z0 S₀ f₀ f₂ e = z0 S₀ f₀ f₂' e := fun e he => by
      simp only [z0, dif_pos he]
    have hfix := yq hq a P haP (z0 S₀ f₀ f₂) (z0 S₀ f₀ f₂') vh
    have hAeq := hA_dep (z0 S₀ f₀ f₂) (z0 S₀ f₀ f₂') vh
    have hNx : zc (z1 (z0 S₀ f₀ f₂)) (fun _ : Fin 1 => x₀) =
        zc (z1 (z0 S₀ f₀ f₂')) (fun _ : Fin 1 => x₀) := by
      ext z; simp only [zl]
      exact forall_congr' fun _ => by
        rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (G := z1 (z0 S₀ f₀ f₂'))]
        exact hfix.1 x₀ hx₀P z
    simp only [Good0, Set.mem_ofPred_eq, hfix.2.2.2.1, hNx, hAeq]
  · intro f₀ hGood0
    let G₀ := z1 (z0 S₀ f₀ (fun _ => false))
    rcases hGood0 (fun _ => false) with ⟨hBb_lo, hBb_hi, hBb_x₀, hA_card⟩
    let Bb := zg q hq G₀ a
    let A := mkA G₀
    let v0 := Bb.erase x₀
    have hA_card' : A.card ≤ T := hA_card
    have v4 : (1 / 5 : ℝ) * ((R : ℝ) ^ 2) ≤ (v0.card : ℝ) := by
      have hnat : Bb.card ≤ v0.card + 1 := by
        by_cases hx : x₀ ∈ Bb
        · rw [show v0 = Bb.erase x₀ from rfl, card_erase_of_mem hx]; omega
        · rw [show v0 = Bb.erase x₀ from rfl, erase_eq_of_notMem hx]; omega
      have hc : (Bb.card : ℝ) ≤ (v0.card : ℝ) + 1 := by exact_mod_cast hnat
      have v6 : (10000 : ℝ) ≤ (R : ℝ) := by exact_mod_cast va
      nlinarith only [hBb_lo, hc, v6]
    have vc : (v0.card : ℝ) ≤ 2 * ((R : ℝ) ^ 2) :=
      (Nat.cast_le.mpr (card_le_card (erase_subset _ _))).trans hBb_hi
    obtain ⟨B_sub, hB_sub_le, hB_sub_card⟩ :=
      exists_subset_card_eq (s := v0) (n := v0.card / 2) (Nat.div_le_self _ 2)
    let v3 := v0 \ B_sub
    have vb : (1 / 12 : ℝ) * ((R : ℝ) ^ 2) ≤ (B_sub.card : ℝ) := by
      have h1 : v0.card ≤ 2 * B_sub.card + 1 := by omega
      have hc : (v0.card : ℝ) ≤ 2 * (B_sub.card : ℝ) + 1 := by exact_mod_cast h1
      have v6 : (10000 : ℝ) ≤ (R : ℝ) := by exact_mod_cast va
      nlinarith only [v4, hc, v6]
    have v9 : (1 / 12 : ℝ) * ((R : ℝ) ^ 2) ≤ (v3.card : ℝ) := by
      have h1 : v3.card = v0.card - B_sub.card := by
        rw [card_sdiff, inter_eq_left.mpr hB_sub_le]
      have h2 : v0.card ≤ 2 * v3.card + 1 := by omega
      have hc : (v0.card : ℝ) ≤ 2 * (v3.card : ℝ) + 1 := by exact_mod_cast h2
      have v6 : (10000 : ℝ) ≤ (R : ℝ) := by exact_mod_cast va
      nlinarith only [v4, hc, v6]
    have v5 : Disjoint P v0 := by
      rw [disjoint_left]; intro v hvP hvB
      rcases mem_erase.mp hvB with ⟨hvne, hvBb⟩
      rcases mem_union.mp hvP with hvimg | hvx
      · rcases mem_image.mp hvimg with ⟨r, _, rfl⟩
        exact ((y8 q hq G₀ a (a r)).mp hvBb).1.1 ⟨r, rfl⟩
      · exact hvne (mem_singleton.mp hvx)
    have vd : Disjoint P A := hA_disj_P G₀
    have v1 : Disjoint v0 A := by
      rw [disjoint_left]; intro w hwB hwA
      have hnot := ((y8 q hq G₀ a w).mp (mem_of_mem_erase hwB)).1
      rcases mem_union.mp (hA_sub_Bc G₀ hwA) with hbc | hbc'
      · exact hnot.2.1 (by unfold zk at hbc; exact (mem_filter.mp hbc).2)
      · exact hnot.2.2 (by unfold zm at hbc'; exact (mem_filter.mp hbc').2)
    have v2 : Disjoint S₀ (z8 v0 A) :=
      zo v5 vd
    let S₁ : Finset (z6 (nOf q m)) := S₀ ∪ z8 v0 A
    let Good1 : (z6 (nOf q m) → Bool) → Prop := fun f =>
      (∀ z ∈ A, ((v0.filter (fun w => (z1 f).Adj w z)).card : ℝ) ≤ 4 * (R : ℝ)) ∧
      (∀ z ∈ A, (R : ℝ) / 48 ≤
        ((B_sub.filter (fun w => (z1 f).Adj w z ∧
          ∀ z' ∈ A, z' ≠ z → ¬ (z1 f).Adj w z')).card : ℝ))
    have v8 : ∀ f g : z6 (nOf q m) → Bool,
        (∀ e ∈ S₁, f e = g e) → (Good1 f ↔ Good1 g) := by
      intro f g hfg
      have hadj : ∀ w ∈ v0, ∀ z ∈ A, (z1 f).Adj w z ↔ (z1 g).Adj w z := by
        intro w hw z hz
        have hne : w ≠ z := fun h => disjoint_left.mp v1 hw (h ▸ hz)
        rw [za f hne, za g hne,
          hfg _ (mem_union_right _ ((z5 v0 A hne).mpr (Or.inl ⟨hw, hz⟩)))]
      exact and_congr
        (forall₂_congr fun z hz => by rw [filter_congr fun w hw => hadj w hw z hz])
        (forall₂_congr fun z hz => by
          rw [filter_congr fun w hw =>
            and_congr (hadj w (hB_sub_le hw) z hz)
              (forall₂_congr fun z' hz' => imp_congr_right fun _ => not_congr (hadj w (hB_sub_le hw) z' hz'))])
    refine (zu hp0 hp1 S₀ S₁ subset_union_left f₀
      Good1 (fun f => z1 f ∈ Bad) v8
      (ε₁ := 2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200))
      (ε₂ := ((2 : ℝ) ^ A.card) * exp (-((R8 : ℝ)) / 64))
      (by positivity) ?_ ?_).trans ?_
    · have vg : 4 * (A.card : ℝ) ≤ (R : ℝ) := by
        have h4R8 : 4 * R8 ≤ R := by
          have hpow : R8 ^ 2 ≤ R8 ^ 8 := Nat.pow_le_pow_right (z1e m) (by norm_num)
          have hreq : R = R8 ^ 8 := zq m
          have hge := hlp.hR8_ge
          nlinarith only [hpow, hreq, hge]
        have hnat : 4 * A.card ≤ R := by omega
        exact_mod_cast hnat
      have vi : z4 p (fun f_rem : {e // e ∉ S₀} → Bool => ¬ Good1 (z0 S₀ f₀ f_rem)) =
          z4 p (fun f_rem : {e // e ∉ S₀} → Bool =>
            ¬ ((∀ z ∈ A, ((v0.filter (fun w =>
                  ∃ (h : w ≠ z) (hmem : z7 w z h ∉ S₀), f_rem ⟨z7 w z h, hmem⟩ = true)).card : ℝ) ≤
                4 * (R : ℝ)) ∧
               (∀ z ∈ A, (R : ℝ) / 48 ≤
                 ((B_sub.filter (fun w =>
                   (∃ (h : w ≠ z) (hmem : z7 w z h ∉ S₀), f_rem ⟨z7 w z h, hmem⟩ = true) ∧
                   ∀ z' ∈ A, z' ≠ z →
                     ¬ ∃ (h : w ≠ z') (hmem : z7 w z' h ∉ S₀),
                       f_rem ⟨z7 w z' h, hmem⟩ = true)).card : ℝ)))) := by
        refine zx p fun f_rem => not_congr ?_
        have hadj : ∀ w ∈ v0, ∀ z ∈ A,
            (z1 (z0 S₀ f₀ f_rem)).Adj w z ↔
            ∃ (h : w ≠ z) (hmem : z7 w z h ∉ S₀), f_rem ⟨z7 w z h, hmem⟩ = true := by
          intro w hw z hz
          have hne : w ≠ z := fun h => disjoint_left.mp v1 hw (h ▸ hz)
          have hnot : z7 w z hne ∉ S₀ :=
            disjoint_right.mp v2 ((z5 v0 A hne).mpr (Or.inl ⟨hw, hz⟩))
          exact zb S₀ f₀ f_rem hne hnot
        exact and_congr
          (forall₂_congr fun z hz => by rw [filter_congr fun w hw => hadj w hw z hz])
          (forall₂_congr fun z hz => by
            rw [filter_congr fun w hw =>
              and_congr (hadj w (hB_sub_le hw) z hz)
                (forall₂_congr fun z' hz' => imp_congr_right fun _ => not_congr (hadj w (hB_sub_le hw) z' hz'))])
      rw [vi]
      exact yk va S₀ v0 B_sub A hB_sub_le v1 v2
        vb vc vg
    · intro f₁ hagree hGood1
      rcases hGood1 (fun _ => false) with ⟨hW_hi, hW_only_lo⟩
      exact z1h q m hq hlp a x₀ mkA hA_dep f₀ v0 B_sub v3
        hB_sub_le rfl v9 rfl hBb_x₀ hA_card v5 v1
        f₁ hagree hW_hi hW_only_lo
    · have h1 : 2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200) ≤
          2 * (T : ℝ) * exp (-((R8 : ℝ)) / 64) := by
        have hAT : (A.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hA_card'
        calc 2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200)
            ≤ 2 * (T : ℝ) * exp (-((R : ℝ)) / 200) := by
              have := exp_pos (-((R : ℝ)) / 200); nlinarith
          _ ≤ 2 * (T : ℝ) * exp (-((R8 : ℝ)) / 64) :=
              mul_le_mul_of_nonneg_left vj.1 (by positivity)
      have h2 : ((2 : ℝ) ^ A.card) * exp (-((R8 : ℝ)) / 64) ≤
          ((2 : ℝ) ^ T) * exp (-((R8 : ℝ)) / 64) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hA_card') (exp_pos _).le
      have vk : 2 * (T : ℝ) + (2 : ℝ) ^ T ≤ (2 : ℝ) ^ (T + 2) := by
        have hlt : (T : ℝ) ≤ (2 : ℝ) ^ T := by exact_mod_cast Nat.le_of_lt Nat.lt_two_pow_self
        rw [pow_add]; norm_num; linarith
      have vf : 0 ≤ exp (-((R8 : ℝ)) / 64) := (exp_pos _).le
      nlinarith only [h1, h2, vk, vf]
lemma wm (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) :
    gProb (nOf q m) ((ROf m : ℝ)⁻¹)
      (EventE1 q (nOf q m) (KOf q m) ∩ EventEdeg q (nOf q m) (ROf m) ∩
        (EventE2 q hq (nOf q m) m)ᶜ) ≤ 1 / 64 := by
  classical
  set n := nOf q m
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set p : ℝ := (R : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  let InjA := univ.filter (fun a : Fin (kOf q) → Fin n => Function.Injective a)
  let BadA : (Fin (kOf q) → Fin n) → Fin n → Set (SimpleGraph (Fin n)) := fun a x =>
    EventE1 q n (KOf q m) ∩ EventEdeg q n R ∩
      {G | (zh q hq G a x).card ≤ T ∧
        ¬ ∀ S ⊆ zh q hq G a x, ∃ v : Fin n, ∀ z ∈ zh q hq G a x, Rrel q hq G a v z ↔ z ∈ S}
  let BadD : (Fin (kOf q) → Fin n) → Set (SimpleGraph (Fin n)) := fun a =>
    EventE1 q n (KOf q m) ∩ EventEdeg q n R ∩
      {G | (domFinset q hq G a).card ≤ T ∧
        ¬ ∀ S ⊆ domFinset q hq G a, ∃ v : Fin n, ∀ z ∈ domFinset q hq G a, Rrel q hq G a v z ↔ z ∈ S}
  have hsub : EventE1 q n (KOf q m) ∩ EventEdeg q n R ∩ (EventE2 q hq n m)ᶜ ⊆
      (⋃ a ∈ InjA, ⋃ x ∈ univ, BadA a x) ∪ (⋃ a ∈ InjA, BadD a) := by
    rintro G ⟨⟨hE1, hEdeg⟩, hnotE2⟩
    simp only [Set.mem_compl_iff, EventE2, Set.mem_ofPred_eq, not_forall, not_and_or] at hnotE2
    rcases hnotE2 with ⟨a, hinj, hpart1 | hpart2⟩
    · push Not at hpart1
      rcases hpart1 with ⟨x, _, hcard, S, hS, hno⟩
      exact Or.inl (Set.mem_biUnion (mem_filter.mpr ⟨mem_univ _, hinj⟩)
        (Set.mem_biUnion (mem_univ x) ⟨⟨hE1, hEdeg⟩, hcard, fun h => by
          rcases h S hS with ⟨v, hv⟩; rcases hno v with ⟨z, hz, hiff⟩
          have := hv z hz; tauto⟩))
    · push Not at hpart2
      rcases hpart2 with ⟨hcard, S, hS, hno⟩
      exact Or.inr (Set.mem_biUnion (mem_filter.mpr ⟨mem_univ _, hinj⟩)
        ⟨⟨hE1, hEdeg⟩, hcard, fun h => by
          rcases h S hS with ⟨v, hv⟩; rcases hno v with ⟨z, hz, hiff⟩
          have := hv z hz; tauto⟩)
  have v4 : ∀ a ∈ InjA, ∀ x : Fin n,
      gProb n p (BadA a x) ≤ ((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64) := by
    intro a ha x
    have hinj : Function.Injective a := (mem_filter.mp ha).2
    refine wp q m hq hlp a hinj x (fun G => zh q hq G a x) ?_ ?_ ?_
    · intro f g hfg
      have hfix := yq hq a (univ.image a ∪ {x})
        (fun r => mem_union_left _ (mem_image.mpr ⟨r, mem_univ _, rfl⟩)) f g hfg
      exact hfix.2.2.2.2.2 x (mem_union_right _ (mem_singleton_self x))
    · intro G z hz
      have hbc := ((zt q hq G a x z).mp hz).1
      exact mem_union_left _ (by unfold zk; exact mem_filter.mpr ⟨mem_univ _, hbc⟩)
    · intro G
      rw [disjoint_left]
      intro z hzP hzA
      rcases (zt q hq G a x z).mp hzA with ⟨_, hadj, v1⟩
      rcases mem_union.mp hzP with hzimg | hzx
      · rcases mem_image.mp hzimg with ⟨r, _, rfl⟩; exact v1 ⟨r, rfl⟩
      · exact G.loopless.irrefl z (mem_singleton.mp hzx ▸ hadj)
  have v3 : ∀ a ∈ InjA,
      gProb n p (BadD a) ≤ ((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64) := by
    intro a ha
    have hinj : Function.Injective a := (mem_filter.mp ha).2
    refine wp q m hq hlp a hinj (w7 q hq a) (fun G => domFinset q hq G a) ?_ ?_ ?_
    · intro f g hfg
      have hfix := yq hq a (univ.image a ∪ {w7 q hq a})
        (fun r => mem_union_left _ (mem_image.mpr ⟨r, mem_univ _, rfl⟩)) f g hfg
      exact hfix.2.2.2.2.1
    · intro G z hz
      have hbc' := ((mem_domFinset q hq G a z).mp hz).1
      exact mem_union_right _ (by unfold zm; exact mem_filter.mpr ⟨mem_univ _, hbc'⟩)
    · intro G
      rw [disjoint_left]
      intro z hzP hzD
      have v1 := ((mem_domFinset q hq G a z).mp hzD).2.2
      rcases mem_union.mp hzP with hzimg | hzd
      · rcases mem_image.mp hzimg with ⟨r, _, rfl⟩; exact v1 ⟨r, rfl⟩
      · exact v1 ⟨dIdx q hq, mem_singleton.mp hzd⟩
  have v0 : (InjA.card : ℝ) ≤ (n : ℝ) ^ (kOf q) := by
    have : InjA.card ≤ (univ : Finset (Fin (kOf q) → Fin n)).card :=
      card_le_card (subset_univ _)
    simpa [Fintype.card_fun, Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr this
  have v8 : gProb n p (⋃ a ∈ InjA, ⋃ x ∈ univ, BadA a x) ≤
      ((n : ℝ) ^ (kOf q + 1)) * ((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64) := by
    calc gProb n p (⋃ a ∈ InjA, ⋃ x ∈ univ, BadA a x)
        ≤ ∑ a ∈ InjA, gProb n p (⋃ x ∈ univ, BadA a x) := yd hp0 hp1 _ _
      _ ≤ ∑ a ∈ InjA, ∑ x ∈ (univ : Finset (Fin n)), gProb n p (BadA a x) :=
          sum_le_sum fun a _ => yd hp0 hp1 _ _
      _ ≤ ∑ _a ∈ InjA, ∑ _x ∈ (univ : Finset (Fin n)),
            (((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) :=
          sum_le_sum fun a ha => sum_le_sum fun x _ => v4 a ha x
      _ = (InjA.card : ℝ) * (n : ℝ) * (((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) := by
          simp [sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ((n : ℝ) ^ (kOf q)) * (n : ℝ) * (((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) := by
          have : 0 ≤ (n : ℝ) * (((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) := by positivity
          nlinarith
      _ = ((n : ℝ) ^ (kOf q + 1)) * ((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64) := by
          rw [pow_succ]; ring
  have v7 : gProb n p (⋃ a ∈ InjA, BadD a) ≤
      ((n : ℝ) ^ (kOf q + 1)) * ((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast wq q m
    calc gProb n p (⋃ a ∈ InjA, BadD a)
        ≤ ∑ a ∈ InjA, gProb n p (BadD a) := yd hp0 hp1 _ _
      _ ≤ ∑ _a ∈ InjA, (((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) :=
          sum_le_sum fun a ha => v3 a ha
      _ = (InjA.card : ℝ) * (((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) ^ (kOf q + 1)) * ((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64) := by
          have h1 : (InjA.card : ℝ) ≤ (n : ℝ) ^ (kOf q + 1) := by
            calc (InjA.card : ℝ) ≤ (n : ℝ) ^ (kOf q) := v0
              _ ≤ (n : ℝ) ^ (kOf q + 1) := pow_le_pow_right₀ hn1 (by omega)
          have hnn : 0 ≤ ((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64) := by positivity
          nlinarith
  have htot : 2 * (((n : ℝ) ^ (kOf q + 1)) * ((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) ≤
      ((n : ℝ) ^ (kOf q + 4)) * ((2 : ℝ) ^ (T + 10)) * exp (-((R8 : ℝ)) / 64) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast wq q m
    have v5 : (n : ℝ) ^ (kOf q + 1) ≤ (n : ℝ) ^ (kOf q + 4) := pow_le_pow_right₀ hn1 (by omega)
    have v6 : 2 * ((2 : ℝ) ^ (T + 2)) ≤ (2 : ℝ) ^ (T + 10) := by
      have : 2 * (2 ^ (T + 2)) ≤ 2 ^ (T + 10) := by
        rw [← _root_.pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this
    have v2 : 0 ≤ exp (-((R8 : ℝ)) / 64) := (exp_pos _).le
    have hmul : 2 * ((n : ℝ) ^ (kOf q + 1)) * ((2 : ℝ) ^ (T + 2)) ≤
        ((n : ℝ) ^ (kOf q + 4)) * ((2 : ℝ) ^ (T + 10)) := by
      calc 2 * ((n : ℝ) ^ (kOf q + 1)) * ((2 : ℝ) ^ (T + 2))
          = ((n : ℝ) ^ (kOf q + 1)) * (2 * ((2 : ℝ) ^ (T + 2))) := by ring
        _ ≤ ((n : ℝ) ^ (kOf q + 4)) * ((2 : ℝ) ^ (T + 10)) :=
            mul_le_mul v5 v6 (by positivity) (by positivity)
    calc 2 * (((n : ℝ) ^ (kOf q + 1)) * ((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64))
        = (2 * ((n : ℝ) ^ (kOf q + 1)) * ((2 : ℝ) ^ (T + 2))) * exp (-((R8 : ℝ)) / 64) := by ring
      _ ≤ (((n : ℝ) ^ (kOf q + 4)) * ((2 : ℝ) ^ (T + 10))) * exp (-((R8 : ℝ)) / 64) :=
          mul_le_mul_of_nonneg_right hmul v2
  calc gProb n p (EventE1 q n (KOf q m) ∩ EventEdeg q n R ∩ (EventE2 q hq n m)ᶜ)
      ≤ gProb n p ((⋃ a ∈ InjA, ⋃ x ∈ univ, BadA a x) ∪ (⋃ a ∈ InjA, BadD a)) :=
        gProb_mono hp0 hp1 hsub
    _ ≤ gProb n p (⋃ a ∈ InjA, ⋃ x ∈ univ, BadA a x) + gProb n p (⋃ a ∈ InjA, BadD a) :=
        yg hp0 hp1 _ _
    _ ≤ 2 * (((n : ℝ) ^ (kOf q + 1)) * ((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) := by linarith
    _ ≤ ((n : ℝ) ^ (kOf q + 4)) * ((2 : ℝ) ^ (T + 10)) * exp (-((R8 : ℝ)) / 64) := htot
    _ ≤ 1 / 256 := hlp.hpoly_exp_R8
    _ ≤ 1 / 64 := by norm_num
lemma wb (q : ℕ) (hq : 2 ≤ q) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (a : Fin (kOf q) → Fin n) (x y : Fin n)
    (B : Finset (Fin n))
    (hAx_y_sub : zh q hq G a y ⊆ B)
    (hB_sub : ∀ u ∈ B, isBc q hq G a u ∧ ¬ zs q a u)
    (Pool : Finset (Fin n) → Finset (Fin n))
    (hPool_sub : ∀ S ∈ (zh q hq G a x).powerset, Pool S ⊆ B)
    (hPool_pat : ∀ S ∈ (zh q hq G a x).powerset, ∀ u ∈ Pool S,
      ∀ z ∈ zh q hq G a x, Rrel q hq G a u z ↔ z ∈ S)
    (hexact : ∀ S ∈ (zh q hq G a x).powerset,
      ((Pool S).filter (fun u => G.Adj y u)).card = 1)
    (hzero : ∀ u ∈ B \ (zh q hq G a x).powerset.biUnion Pool, ¬ G.Adj y u) :
    yn q hq G a x y := by
  classical
  let AxSet := zh q hq G a x
  have v0 : ∀ u, Ax q hq G a y u → ∃ S ∈ AxSet.powerset, u ∈ Pool S := by
    intro u huy
    have huB : u ∈ B := hAx_y_sub ((zt q hq G a y u).mpr huy)
    by_contra hnot
    have v1 : u ∉ AxSet.powerset.biUnion Pool := by
      intro hmem; rcases mem_biUnion.mp hmem with ⟨S, hS, huS⟩; exact hnot ⟨S, hS, huS⟩
    exact hzero u (mem_sdiff.mpr ⟨huB, v1⟩) huy.2.1.symm
  constructor
  ·
    intro u₁ u₂ hu₁ hu₂ hne
    obtain ⟨S₁, hS₁, hu₁S⟩ := v0 u₁ hu₁
    obtain ⟨S₂, hS₂, hu₂S⟩ := v0 u₂ hu₂
    have v5 : S₁ ≠ S₂ := by
      rintro rfl
      have v3 := hexact S₁ hS₁
      rcases card_eq_one.mp v3 with ⟨u₀, hu₀⟩
      have h1 : u₁ ∈ (Pool S₁).filter (fun u => G.Adj y u) :=
        mem_filter.mpr ⟨hu₁S, hu₁.2.1.symm⟩
      have h2 : u₂ ∈ (Pool S₁).filter (fun u => G.Adj y u) :=
        mem_filter.mpr ⟨hu₂S, hu₂.2.1.symm⟩
      rw [hu₀, mem_singleton] at h1 h2
      exact hne (h1.trans h2.symm)
    have v4 : ∃ z, (z ∈ S₁ ∧ z ∉ S₂) ∨ (z ∈ S₂ ∧ z ∉ S₁) := by
      by_contra hall
      push Not at hall
      apply v5
      ext z
      exact ⟨fun h1 => (hall z).1 h1, fun h2 => (hall z).2 h2⟩
    rcases v4 with ⟨z, ⟨hz1, hz2⟩ | ⟨hz2, hz1⟩⟩
    · have hzA : z ∈ AxSet := mem_powerset.mp hS₁ hz1
      refine ⟨z, (zt q hq G a x z).mp hzA, ?_⟩
      rw [hPool_pat S₁ hS₁ u₁ hu₁S z hzA, hPool_pat S₂ hS₂ u₂ hu₂S z hzA]
      tauto
    · have hzA : z ∈ AxSet := mem_powerset.mp hS₂ hz2
      refine ⟨z, (zt q hq G a x z).mp hzA, ?_⟩
      rw [hPool_pat S₁ hS₁ u₁ hu₁S z hzA, hPool_pat S₂ hS₂ u₂ hu₂S z hzA]
      tauto
  ·
    intro v
    let S := AxSet.filter (fun z => Rrel q hq G a v z)
    have hS : S ∈ AxSet.powerset := mem_powerset.mpr (filter_subset _ _)
    rcases card_eq_one.mp (hexact S hS) with ⟨u, hu⟩
    have v2 : u ∈ (Pool S).filter (fun u => G.Adj y u) := by
      rw [hu]; exact mem_singleton_self u
    rcases mem_filter.mp v2 with ⟨huP, hadj⟩
    have huB := hB_sub u (hPool_sub S hS huP)
    refine ⟨u, ⟨huB.1, hadj.symm, huB.2⟩, fun z hz => ?_⟩
    have hzA : z ∈ AxSet := (zt q hq G a x z).mpr hz
    rw [hPool_pat S hS u huP z hzA]
    simp [S, hzA]
private lemma z1i (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (a : Fin (kOf q) → Fin (nOf q m)) (x : Fin (nOf q m))
    (f₀ : {e : z6 (nOf q m) // e ∈ ze (univ.image a ∪ {x})} → Bool)
    (Bc B_all A U B W_any : Finset (Fin (nOf q m)))
    (W_z : Fin (nOf q m) → Finset (Fin (nOf q m)))
    (hBc_eq : Bc = zk q hq (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))) a)
    (hB_all_eq : B_all = (zg q hq (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))) a).erase x)
    (hA_eq : A = zh q hq (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))) a x)
    (hB_eq : B = (Bc \ (A ∪ univ.image a)).erase x)
    (hU_sub_B : U ⊆ B)
    (hB_hi : (B.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hB_all_lo : (1 / 12 : ℝ) * ((ROf m : ℝ) ^ 2) ≤ (B_all.card : ℝ))
    (hBb_x : ((zg q hq (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))) a ∩
      zc (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))) (fun _ : Fin 1 => x)).card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hA_card : A.card ≤ zd (m - 2))
    (hW_any_hi : (W_any.card : ℝ) ≤ 4 * (A.card : ℝ) * (ROf m : ℝ))
    (hW_any_eq : W_any = A.biUnion W_z)
    (hdisj_PB : Disjoint (univ.image a ∪ {x}) B_all)
    (hdisj_PBc : Disjoint (univ.image a ∪ {x}) B)
    (hdisj_BA : Disjoint B_all A)
    (hdisj_Ball_B : Disjoint B_all B)
    (hdisj_B_A : Disjoint B A)
    (hdisj_UW : Disjoint U W_any)
    (hU_not_x : ∀ u ∈ U, ¬ (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))).Adj u x)
    (f₁ : {e : z6 (nOf q m) // e ∈ ze (univ.image a ∪ {x}) ∪ z8 B_all A} → Bool)
    (hagree : ∀ e : {e // e ∈ ze (univ.image a ∪ {x})}, f₁ ⟨e.1, subset_union_left e.2⟩ = f₀ e)
    (hWz_eq : ∀ z, W_z z = B_all.filter (fun w => (z1 (z0 _ f₁ (fun _ => false))).Adj w z))
    (f₂ : {e : z6 (nOf q m) // e ∈ (ze (univ.image a ∪ {x}) ∪ z8 B_all A) ∪ z8 U W_any} → Bool)
    (hagree2 : ∀ e : {e // e ∈ ze (univ.image a ∪ {x}) ∪ z8 B_all A},
      f₂ ⟨e.1, subset_union_left e.2⟩ = f₁ e)
    (hGood2 : ∀ S ∈ A.powerset,
      ((1 / 8 : ℝ) * exp (-13 * (A.card : ℝ))) * (ROf m : ℝ) ≤
        ((U.filter (fun u => ∀ z ∈ A, (∃ w ∈ W_z z, (z1 (z0 _ f₂ (fun _ => false))).Adj u w) ↔ z ∈ S)).card : ℝ)) :
    z4 ((ROf m : ℝ)⁻¹)
      (fun f₃ : {e : z6 (nOf q m) // e ∉ (ze (univ.image a ∪ {x}) ∪ z8 B_all A) ∪ z8 U W_any} → Bool =>
        ¬ ∃ y : Fin (nOf q m), ¬ zs q a y ∧ yn q hq (z1 (z0 _ f₂ f₃)) a x y) ≤
      exp (-((R8Of m : ℝ)) / 64) := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set Tprev := zd (m - 2)
  set p : ℝ := (R : ℝ)⁻¹
  have vv : R8 ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have vy : 10000 ≤ R := le_trans hlp.hR8_ge vv
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have v8 : Tprev ≤ T := y6 (by have := hlp.hm; omega)
  have vf : 2 ^ Tprev = T := by
    have hm2 : m - 1 = (m - 2) + 1 := by have := hlp.hm; omega
    change 2 ^ zd (m - 2) = zd (m - 1); rw [hm2]; rfl
  have vu : T ≤ R8 := le_trans (Nat.le_self_pow (by norm_num) T) (Nat.le_of_lt Nat.lt_two_pow_self)
  have vd : (R : ℝ) = (R8 : ℝ) ^ 8 := by exact_mod_cast zq m
  have u2 := yf q m hlp
  let P : Finset (Fin (nOf q m)) := univ.image a ∪ {x}
  let S₀ : Finset (z6 (nOf q m)) := ze P
  let S₁ : Finset (z6 (nOf q m)) := S₀ ∪ z8 B_all A
  let S₂ : Finset (z6 (nOf q m)) := S₁ ∪ z8 U W_any
  have haP : ∀ r : Fin (kOf q), a r ∈ P := fun r =>
    mem_union_left _ (mem_image.mpr ⟨r, mem_univ _, rfl⟩)
  have hxP : x ∈ P := mem_union_right _ (mem_singleton_self x)
  let G₀ := z1 (z0 S₀ f₀ (fun _ => false))
  let G₁ := z1 (z0 S₁ f₁ (fun _ => false))
  let G₂ := z1 (z0 S₂ f₂ (fun _ => false))
  let Bb := zg q hq G₀ a
  let vb : ℝ := (1 / 8 : ℝ) * exp (-13 * (A.card : ℝ))
  let Pool : Finset (Fin (nOf q m)) → Finset (Fin (nOf q m)) := fun S =>
    U.filter (fun u => ∀ z ∈ A, (∃ w ∈ W_z z, G₂.Adj u w) ↔ z ∈ S)
  have v5 : ∀ S ∈ A.powerset, Pool S ⊆ B := fun _ _ =>
    (filter_subset _ _).trans hU_sub_B
  have vh : Set.PairwiseDisjoint (A.powerset : Set (Finset (Fin (nOf q m)))) Pool := by
    intro S₁' hS₁' S₂' hS₂' hne
    change Disjoint (Pool S₁') (Pool S₂')
    rw [disjoint_left]; intro u hu1 hu2
    apply hne; ext z
    by_cases hzA : z ∈ A
    · rw [← (mem_filter.mp hu1).2 z hzA, (mem_filter.mp hu2).2 z hzA]
    · exact ⟨fun h => absurd (mem_powerset.mp (mem_coe.mp hS₁') h) hzA,
        fun h => absurd (mem_powerset.mp (mem_coe.mp hS₂') h) hzA⟩
  let Y : Finset (Fin (nOf q m)) := (B_all \ W_any).filter (fun y => ¬ G₀.Adj y x)
  have u6 : (R : ℝ) ≤ (Y.card : ℝ) := by
    have u5 : B_all.card ≤ (B_all \ W_any).card + W_any.card := by
      have h1 := card_sdiff (s := W_any) (t := B_all)
      have h2 : (W_any ∩ B_all).card ≤ W_any.card := card_le_card inter_subset_left
      omega
    have hNx : ((B_all \ W_any).filter (fun y => G₀.Adj y x)).card ≤
        (Bb ∩ zc G₀ (fun _ : Fin 1 => x)).card := by
      refine card_le_card fun y hy => ?_
      rcases mem_filter.mp hy with ⟨hy1, hadj⟩
      refine mem_inter.mpr ⟨mem_of_mem_erase (hB_all_eq ▸ sdiff_subset hy1), ?_⟩
      rw [zl]; intro _; exact hadj
    have u4 : Y.card + ((B_all \ W_any).filter (fun y => G₀.Adj y x)).card =
        (B_all \ W_any).card := by
      rw [← card_union_of_disjoint (disjoint_filter.mpr fun _ _ h1 h2 => h1 h2),
        union_comm, filter_union_filter_not_eq]
    have hc1 : (B_all.card : ℝ) ≤ ((B_all \ W_any).card : ℝ) + (W_any.card : ℝ) := by exact_mod_cast u5
    have hc2 : (Y.card : ℝ) + (((B_all \ W_any).filter (fun y => G₀.Adj y x)).card : ℝ) =
        ((B_all \ W_any).card : ℝ) := by exact_mod_cast u4
    have hc3 : (((B_all \ W_any).filter (fun y => G₀.Adj y x)).card : ℝ) ≤ 2 * (R : ℝ) :=
      (Nat.cast_le.mpr hNx).trans hBb_x
    have hAT : (A.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast le_trans hA_card v8
    have hTR : 4 * (T : ℝ) + 4 ≤ (1 / 24 : ℝ) * (R : ℝ) := by
      have h1 : (T : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast vu
      have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
      have u8 : 10000 * (R8 : ℝ) ≤ (R : ℝ) := by
        rw [vd]
        have : (R8 : ℝ) ^ 2 ≤ (R8 : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
        nlinarith only [hR8_ge, this]
      linarith
    have u7 : (10000 : ℝ) ≤ (R : ℝ) := by exact_mod_cast vy
    nlinarith only [hB_all_lo, hW_any_hi, hc1, hc2, hc3, hAT, hTR, u7]
  have v0 : Y ⊆ B_all := (filter_subset _ _).trans sdiff_subset
  have v1 : ∀ y ∈ Y, y ∉ B := fun y hy hyB =>
    disjoint_left.mp hdisj_Ball_B (v0 hy) hyB
  have v2 : ∀ y ∈ Y, Disjoint S₂ (z8 {y} B) := by
    intro y hy
    have vo : y ∈ B_all := v0 hy
    have va : y ∉ W_any := (mem_sdiff.mp (mem_filter.mp hy).1).2
    have vz : y ∉ P := disjoint_right.mp hdisj_PB vo
    have vn : y ∉ A := disjoint_left.mp hdisj_BA vo
    have vm : y ∉ U := fun h => v1 y hy (hU_sub_B h)
    rw [disjoint_union_left, disjoint_union_left]
    refine ⟨⟨zo (disjoint_singleton_right.mpr vz) hdisj_PBc, ?_⟩, ?_⟩
    · rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        have h1 := (z5 B_all A huv).mp he1
        have h2 := (z5 {y} B huv).mp he2
        rcases h1 with ⟨_, hvA⟩ | ⟨_, huA⟩ <;> rcases h2 with ⟨huy, hvB⟩ | ⟨hvy, huB⟩
        · exact disjoint_left.mp hdisj_B_A hvB hvA
        · exact vn (mem_singleton.mp hvy ▸ hvA)
        · exact vn (mem_singleton.mp huy ▸ huA)
        · exact disjoint_left.mp hdisj_B_A huB huA
    · rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        have h1 := (z5 U W_any huv).mp he1
        have h2 := (z5 {y} B huv).mp he2
        rcases h1 with ⟨huU, hvW⟩ | ⟨hvU, huW⟩ <;> rcases h2 with ⟨huy, hvB⟩ | ⟨hvy, huB⟩
        · exact vm (mem_singleton.mp huy ▸ huU)
        · exact va (mem_singleton.mp hvy ▸ hvW)
        · exact va (mem_singleton.mp huy ▸ huW)
        · exact vm (mem_singleton.mp hvy ▸ hvU)
  let Ty : Fin (nOf q m) → Finset {e : z6 (nOf q m) // e ∉ S₂} := fun y =>
    if hy : y ∈ Y then
      B.attach.image (fun (u : {v // v ∈ B}) =>
        have hne : y ≠ u.1 := fun h => v1 y hy (h ▸ u.2)
        ⟨z7 y u.1 hne, disjoint_right.mp (v2 y hy)
          ((z5 {y} B hne).mpr (Or.inl ⟨mem_singleton_self y, u.2⟩))⟩)
    else ∅
  have vt : Set.PairwiseDisjoint (Y : Set (Fin (nOf q m))) Ty := by
    intro y₁ hy₁ y₂ hy₂ hne
    have hy₁' : y₁ ∈ Y := mem_coe.mp hy₁
    have hy₂' : y₂ ∈ Y := mem_coe.mp hy₂
    change Disjoint (Ty y₁) (Ty y₂)
    rw [disjoint_left]; intro e he₁ he₂
    dsimp only [Ty] at he₁ he₂; rw [dif_pos hy₁'] at he₁; rw [dif_pos hy₂'] at he₂
    rcases mem_image.mp he₁ with ⟨u₁, _, rfl⟩
    rcases mem_image.mp he₂ with ⟨u₂, _, heq⟩
    rcases zv heq with ⟨hyy, _⟩ | ⟨hyu, _⟩
    · exact hne hyy.symm
    · exact v1 y₂ hy₂' (hyu ▸ u₁.2)
  let GoodY : Fin (nOf q m) → ({e : z6 (nOf q m) // e ∉ S₂} → Bool) → Prop :=
    fun y f₃ =>
      (∀ S ∈ A.powerset, ((Pool S).filter (fun u =>
        ∃ (h : y ≠ u) (hmem : z7 y u h ∉ S₂), f₃ ⟨z7 y u h, hmem⟩ = true)).card = 1) ∧
      (∀ u ∈ B \ A.powerset.biUnion Pool,
        ¬ ∃ (h : y ≠ u) (hmem : z7 y u h ∉ S₂), f₃ ⟨z7 y u h, hmem⟩ = true)
  have vj : ∀ y ∈ Y, ∀ f g : {e // e ∉ S₂} → Bool,
      (∀ x ∈ Ty y, f x = g x) → (GoodY y f ↔ GoodY y g) := by
    intro y hy f g hfg
    have hadj : ∀ u (hu : u ∈ B),
        (∃ (h : y ≠ u) (hmem : z7 y u h ∉ S₂), f ⟨z7 y u h, hmem⟩ = true) ↔
        (∃ (h : y ≠ u) (hmem : z7 y u h ∉ S₂), g ⟨z7 y u h, hmem⟩ = true) := by
      intro u hu
      have hne : y ≠ u := fun h => v1 y hy (h ▸ hu)
      have hnot : z7 y u hne ∉ S₂ := disjoint_right.mp (v2 y hy)
        ((z5 {y} B hne).mpr (Or.inl ⟨mem_singleton_self y, hu⟩))
      have hmem : (⟨z7 y u hne, hnot⟩ : {e // e ∉ S₂}) ∈ Ty y := by
        dsimp only [Ty]; rw [dif_pos hy]
        exact mem_image.mpr ⟨⟨u, hu⟩, mem_attach _ _, rfl⟩
      have heq := hfg _ hmem
      exact ⟨fun ⟨_, _, hf⟩ => ⟨hne, hnot, by rwa [← heq]⟩,
        fun ⟨_, _, hg⟩ => ⟨hne, hnot, by rwa [heq]⟩⟩
    exact and_congr
      (forall₂_congr fun S hS => by
        rw [filter_congr fun u hu => hadj u (v5 S hS hu)])
      (forall₂_congr fun u hu => not_congr (hadj u (sdiff_subset hu)))
  have vi : ∀ y ∈ Y, ∀ f₃ : {e // e ∉ S₂} → Bool,
      GoodY y f₃ → ∃ y' : Fin (nOf q m), ¬ zs q a y' ∧ yn q hq (z1 (z0 S₂ f₂ f₃)) a x y' := by
    intro y hy f₃ hGy
    let G₃ := z1 (z0 S₂ f₂ f₃)
    have hS0 : ∀ e ∈ S₀, z0 S₂ f₂ f₃ e = z0 S₀ f₀ (fun _ => false) e := by
      intro e he0
      have he1 : e ∈ S₁ := subset_union_left he0
      have he2 : e ∈ S₂ := subset_union_left he1
      simp only [z0, dif_pos he2, dif_pos he0]
      rw [hagree2 ⟨e, he1⟩, hagree ⟨e, he0⟩]
    have vc := yq hq a P haP _ _ hS0
    have hS1 : ∀ e ∈ S₁, z0 S₂ f₂ f₃ e = z0 S₁ f₁ (fun _ => false) e := by
      intro e he1
      have he2 : e ∈ S₂ := subset_union_left he1
      simp only [z0, dif_pos he2, dif_pos he1]
      exact hagree2 ⟨e, he1⟩
    have hS2 : ∀ e ∈ S₂, z0 S₂ f₂ f₃ e = z0 S₂ f₂ (fun _ => false) e := fun e he2 => by
      simp only [z0, dif_pos he2]
    have v7 : zh q hq G₃ a x = A := (vc.2.2.2.2.2 x hxP).trans hA_eq.symm
    have vk : zk q hq G₃ a = Bc := vc.2.1.trans hBc_eq.symm
    have vx : zg q hq G₃ a = Bb := vc.2.2.2.1
    have u3 : ¬ zs q a y := ((y8 q hq G₀ a y).mp
      (mem_of_mem_erase (hB_all_eq ▸ v0 hy))).1.1
    refine ⟨y, u3, ?_⟩
    refine wb q hq G₃ a x y B ?_ ?_ Pool
      (by rw [v7]; exact v5) ?_ ?_ ?_
    · intro u hu
      rcases (zt q hq G₃ a y u).mp hu with ⟨hbc, hadj, hnp⟩
      have huBc : u ∈ Bc := by
        rw [← vk]; unfold zk; exact mem_filter.mpr ⟨mem_univ _, hbc⟩
      have hux : u ≠ x := by
        rintro rfl
        exact (mem_filter.mp hy).2 ((vc.1 u hxP y).mp hadj).symm
      have huA : u ∉ A := by
        intro huA
        have va : y ∉ W_any := (mem_sdiff.mp (mem_filter.mp hy).1).2
        apply va
        rw [hW_any_eq]
        refine mem_biUnion.mpr ⟨u, huA, ?_⟩
        rw [hWz_eq u]
        refine mem_filter.mpr ⟨v0 hy, ?_⟩
        have hne : y ≠ u := fun h => disjoint_left.mp hdisj_BA (v0 hy) (h ▸ huA)
        have hmem : z7 y u hne ∈ S₁ :=
          mem_union_right _ ((z5 B_all A hne).mpr (Or.inl ⟨v0 hy, huA⟩))
        rw [za _ hne, ← hS1 _ hmem]
        exact (za _ hne).mp hadj.symm
      have huI : u ∉ univ.image a := fun h => by
        rcases mem_image.mp h with ⟨r, _, rfl⟩; exact hnp ⟨r, rfl⟩
      rw [hB_eq]
      exact mem_erase.mpr ⟨hux, mem_sdiff.mpr ⟨huBc, by simp [huA, huI]⟩⟩
    · intro u huB
      rw [hB_eq] at huB
      have huBc : u ∈ Bc := (mem_sdiff.mp (mem_of_mem_erase huB)).1
      have u0 : u ∉ univ.image a := fun h =>
        (mem_sdiff.mp (mem_of_mem_erase huB)).2 (mem_union_right _ h)
      refine ⟨?_, fun ⟨r, hr⟩ => u0 (mem_image.mpr ⟨r, mem_univ _, hr.symm⟩)⟩
      rw [← vk] at huBc; unfold zk at huBc; exact (mem_filter.mp huBc).2
    · rw [v7]
      intro S hS u huP z hzA
      rcases mem_filter.mp huP with ⟨huU, hpat⟩
      rw [w3, vx, ← hpat z hzA]
      constructor
      · rintro ⟨w, hwBb, hwu, hwz⟩
        have hwx : w ≠ x := by
          rintro rfl
          exact hU_not_x u huU ((vc.1 w hxP u).mp hwu).symm
        have v6 : w ∈ B_all := hB_all_eq.symm ▸ mem_erase.mpr ⟨hwx, hwBb⟩
        have v3 : w ≠ z := fun h => disjoint_left.mp hdisj_BA v6 (h ▸ hzA)
        have vs : z7 w z v3 ∈ S₁ :=
          mem_union_right _ ((z5 B_all A v3).mpr (Or.inl ⟨v6, hzA⟩))
        have hwz1 : G₁.Adj w z := by
          rw [za _ v3, ← hS1 _ vs]
          exact (za _ v3).mp hwz
        have hwWz : w ∈ W_z z := by rw [hWz_eq z]; exact mem_filter.mpr ⟨v6, hwz1⟩
        have v9 : w ∈ W_any := by rw [hW_any_eq]; exact mem_biUnion.mpr ⟨z, hzA, hwWz⟩
        have v4 : u ≠ w := fun h => disjoint_left.mp hdisj_UW huU (h ▸ v9)
        have vr : z7 u w v4 ∈ S₂ :=
          mem_union_right _ ((z5 U W_any v4).mpr (Or.inl ⟨huU, v9⟩))
        have huw2 : G₂.Adj u w := by
          rw [za _ v4, ← hS2 _ vr]
          exact (za _ v4).mp hwu.symm
        exact ⟨w, hwWz, huw2⟩
      · rintro ⟨w, hwWz, huw2⟩
        have hwWz' := hwWz; rw [hWz_eq z] at hwWz'
        have v6 : w ∈ B_all := (mem_filter.mp hwWz').1
        have v9 : w ∈ W_any := by rw [hW_any_eq]; exact mem_biUnion.mpr ⟨z, hzA, hwWz⟩
        have v4 : u ≠ w := fun h => disjoint_left.mp hdisj_UW huU (h ▸ v9)
        have vr : z7 u w v4 ∈ S₂ :=
          mem_union_right _ ((z5 U W_any v4).mpr (Or.inl ⟨huU, v9⟩))
        have hwu3 : G₃.Adj w u := by
          have : G₃.Adj u w := by
            rw [za _ v4, hS2 _ vr]
            exact (za _ v4).mp huw2
          exact this.symm
        have v3 : w ≠ z := fun h => disjoint_left.mp hdisj_BA v6 (h ▸ hzA)
        have vs : z7 w z v3 ∈ S₁ :=
          mem_union_right _ ((z5 B_all A v3).mpr (Or.inl ⟨v6, hzA⟩))
        have hwz3 : G₃.Adj w z := by
          rw [za _ v3, hS1 _ vs]
          exact (za _ v3).mp (mem_filter.mp hwWz').2
        exact ⟨w, mem_of_mem_erase (hB_all_eq ▸ v6), hwu3, hwz3⟩
    · rw [v7]
      intro S hS
      rw [← hGy.1 S hS]
      congr 1
      refine filter_congr fun u hu => ?_
      have huB := v5 S hS hu
      have hne : y ≠ u := fun h => v1 y hy (h ▸ huB)
      have hnot : z7 y u hne ∉ S₂ := disjoint_right.mp (v2 y hy)
        ((z5 {y} B hne).mpr (Or.inl ⟨mem_singleton_self y, huB⟩))
      exact zb S₂ f₂ f₃ hne hnot
    · rw [v7]
      intro u hu
      have huB : u ∈ B := sdiff_subset hu
      have hne : y ≠ u := fun h => v1 y hy (h ▸ huB)
      have hnot : z7 y u hne ∉ S₂ := disjoint_right.mp (v2 y hy)
        ((z5 {y} B hne).mpr (Or.inl ⟨mem_singleton_self y, huB⟩))
      rw [zb S₂ f₂ f₃ hne hnot]
      exact hGy.2 u hu
  have ve : ∀ y ∈ Y, ((R8 : ℝ))⁻¹ ≤ z4 p (GoodY y) := by
    intro y hy
    have hEO := yo vy S₂ y B (v1 y hy) hB_hi (v2 y hy)
      A.powerset Pool v5 vh (by positivity : 0 ≤ vb) hGood2
    have u1 : exp (-13 * (A.card : ℝ) - 3) ≤ vb := by
      dsimp only [vb]
      have h8 : exp (-3 : ℝ) ≤ (1 / 8 : ℝ) := by
        have hsum := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 4
        simp [sum_range_succ, Nat.factorial] at hsum
        rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
        linarith
      calc exp (-13 * (A.card : ℝ) - 3)
          = exp (-3 : ℝ) * exp (-13 * (A.card : ℝ)) := by
            rw [← exp_add]; congr 1; ring
        _ ≤ (1 / 8 : ℝ) * exp (-13 * (A.card : ℝ)) :=
            mul_le_mul_of_nonneg_right h8 (exp_pos _).le
    have vl : A.powerset.card ≤ T := by
      rw [card_powerset, ← vf]
      exact Nat.pow_le_pow_right (by norm_num) hA_card
    have vg : ((R8 : ℝ))⁻¹ ≤ vb ^ A.powerset.card * exp (-4 : ℝ) := by
      have h1 : exp (-20 * (m : ℝ) * (T : ℝ) ^ 2 - 100) ≤
          exp ((A.powerset.card : ℝ) * (-13 * (A.card : ℝ) - 3) - 4) := by
        refine exp_le_exp.mpr ?_
        have hAT : (A.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast le_trans hA_card v8
        have hPT : (A.powerset.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast vl
        have hm10 : (10 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlp.hm
        have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast z03 (m - 1)
        nlinarith only [hAT, hPT, hm10, hT1]
      calc ((R8 : ℝ))⁻¹
          ≤ exp (-20 * (m : ℝ) * (T : ℝ) ^ 2 - 100) := u2.2.2.2
        _ ≤ exp ((A.powerset.card : ℝ) * (-13 * (A.card : ℝ) - 3) - 4) := h1
        _ = exp ((A.powerset.card : ℝ) * (-13 * (A.card : ℝ) - 3)) * exp (-4 : ℝ) := by
            rw [← exp_add]; rfl
        _ = (exp (-13 * (A.card : ℝ) - 3)) ^ A.powerset.card * exp (-4 : ℝ) := by
            rw [exp_nat_mul]
        _ ≤ vb ^ A.powerset.card * exp (-4 : ℝ) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (exp_pos _).le u1 _)
              (exp_pos _).le
    exact vg.trans hEO
  have vq : z4 p (fun f₃ : {e // e ∉ S₂} → Bool =>
        ¬ ∃ y : Fin (nOf q m), ¬ zs q a y ∧ yn q hq (z1 (z0 S₂ f₂ f₃)) a x y) ≤
      z4 p (fun f₃ : {e // e ∉ S₂} → Bool => ∀ y ∈ Y, ¬ GoodY y f₃) :=
    zi hp0 hp1 fun f₃ hbad y hy hGy => hbad (vi y hy f₃ hGy)
  rw [y5 Y Ty vt p (fun y f₃ => ¬ GoodY y f₃)
    (fun y hy f g hfg => not_congr (vj y hy f g hfg))] at vq
  have vp : (∏ y ∈ Y, z4 p (fun f₃ => ¬ GoodY y f₃)) ≤
      exp (-((R8 : ℝ)) / 64) := by
    have hfac : ∀ y ∈ Y, z4 p (fun f₃ => ¬ GoodY y f₃) ≤ exp (-((R8 : ℝ))⁻¹) := by
      intro y hy
      rw [wg]
      have h1 := ve y hy
      have h2 := Real.add_one_le_exp (-((R8 : ℝ))⁻¹)
      linarith
    calc (∏ y ∈ Y, z4 p (fun f₃ => ¬ GoodY y f₃))
        ≤ ∏ _y ∈ Y, exp (-((R8 : ℝ))⁻¹) :=
          prod_le_prod (fun _ _ => ym hp0 hp1 _) hfac
      _ = (exp (-((R8 : ℝ))⁻¹)) ^ Y.card := prod_const _
      _ = exp ((Y.card : ℝ) * (-((R8 : ℝ))⁻¹)) := (exp_nat_mul _ _).symm
      _ ≤ exp (-((R8 : ℝ)) / 64) := by
          refine exp_le_exp.mpr ?_
          have vw : (0 : ℝ) < (R8 : ℝ) := Nat.cast_pos.mpr (z1e m)
          have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
          have hRR8 : (R8 : ℝ) ^ 2 ≤ (R : ℝ) := by
            rw [vd]; exact pow_le_pow_right₀ (by linarith) (by norm_num)
          have hdiv : (R8 : ℝ) ≤ (Y.card : ℝ) * ((R8 : ℝ))⁻¹ := by
            rw [le_mul_inv_iff₀ vw]; nlinarith only [u6, hRR8]
          linarith
  exact vq.trans vp
private lemma z1j (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (a : Fin (kOf q) → Fin (nOf q m)) (x : Fin (nOf q m))
    (f₀ : {e : z6 (nOf q m) // e ∈ ze (univ.image a ∪ {x})} → Bool)
    (Bc B_all A U B : Finset (Fin (nOf q m)))
    (hBc_eq : Bc = zk q hq (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))) a)
    (hB_all_eq : B_all = (zg q hq (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))) a).erase x)
    (hA_eq : A = zh q hq (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))) a x)
    (hB_eq : B = (Bc \ (A ∪ univ.image a)).erase x)
    (hU_sub_B : U ⊆ B)
    (hB_hi : (B.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hU_lo : (ROf m : ℝ) / 4 ≤ (U.card : ℝ))
    (hB_all_lo : (1 / 12 : ℝ) * ((ROf m : ℝ) ^ 2) ≤ (B_all.card : ℝ))
    (hBb_x : ((zg q hq (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))) a ∩
      zc (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))) (fun _ : Fin 1 => x)).card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hA_card : A.card ≤ zd (m - 2))
    (hdisj_PB : Disjoint (univ.image a ∪ {x}) B_all)
    (hdisj_PBc : Disjoint (univ.image a ∪ {x}) B)
    (hdisj_BA : Disjoint B_all A)
    (hdisj_Ball_B : Disjoint B_all B)
    (hdisj_B_A : Disjoint B A)
    (hU_not_x : ∀ u ∈ U, ¬ (z1 (z0 (ze (univ.image a ∪ {x})) f₀ (fun _ => false))).Adj u x)
    (f₁ : {e : z6 (nOf q m) // e ∈ ze (univ.image a ∪ {x}) ∪ z8 B_all A} → Bool)
    (hagree : ∀ e : {e // e ∈ ze (univ.image a ∪ {x})}, f₁ ⟨e.1, subset_union_left e.2⟩ = f₀ e)
    (hW_hi : ∀ z ∈ A, ((B_all.filter (fun w => (z1 (z0 _ f₁ (fun _ => false))).Adj w z)).card : ℝ) ≤ 4 * (ROf m : ℝ))
    (hW_only_lo : ∀ z ∈ A, (ROf m : ℝ) / 48 ≤
      ((B_all.filter (fun w => (z1 (z0 _ f₁ (fun _ => false))).Adj w z ∧
        ∀ z' ∈ A, z' ≠ z → ¬ (z1 (z0 _ f₁ (fun _ => false))).Adj w z')).card : ℝ)) :
    z4 ((ROf m : ℝ)⁻¹)
      (fun f₂ : {e : z6 (nOf q m) // e ∉ ze (univ.image a ∪ {x}) ∪ z8 B_all A} → Bool =>
        ¬ ∃ y : Fin (nOf q m), ¬ zs q a y ∧ yn q hq (z1 (z0 _ f₁ f₂)) a x y) ≤
      ((2 : ℝ) ^ A.card + 1) * exp (-((R8Of m : ℝ)) / 64) := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set Tprev := zd (m - 2)
  set p : ℝ := (R : ℝ)⁻¹
  have v8 : R8 ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have vh : 10000 ≤ R := le_trans hlp.hR8_ge v8
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have v5 : Tprev ≤ T := y6 (by have := hlp.hm; omega)
  have ve := yf q m hlp
  let P : Finset (Fin (nOf q m)) := univ.image a ∪ {x}
  let S₀ : Finset (z6 (nOf q m)) := ze P
  let S₁ : Finset (z6 (nOf q m)) := S₀ ∪ z8 B_all A
  let G₁ := z1 (z0 S₁ f₁ (fun _ => false))
  let W_z : Fin (nOf q m) → Finset (Fin (nOf q m)) := fun z => B_all.filter (fun w => G₁.Adj w z)
  let vf : Fin (nOf q m) → Finset (Fin (nOf q m)) := fun z =>
    B_all.filter (fun w => G₁.Adj w z ∧ ∀ z' ∈ A, z' ≠ z → ¬ G₁.Adj w z')
  let v0 : Finset (Fin (nOf q m)) := A.biUnion W_z
  have v1 : v0 ⊆ B_all := biUnion_subset.mpr fun z _ => filter_subset _ _
  have v4 : (v0.card : ℝ) ≤ 4 * (A.card : ℝ) * (R : ℝ) := by
    have h1 : (v0.card : ℝ) ≤ ∑ z ∈ A, ((W_z z).card : ℝ) := by exact_mod_cast card_biUnion_le
    calc (v0.card : ℝ) ≤ ∑ z ∈ A, ((W_z z).card : ℝ) := h1
      _ ≤ ∑ _z ∈ A, (4 * (R : ℝ)) := sum_le_sum fun z hz => hW_hi z hz
      _ = 4 * (A.card : ℝ) * (R : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
  have v2 : Disjoint U v0 :=
    (hdisj_Ball_B.symm.mono_left hU_sub_B).mono_right v1
  have v3 : Disjoint S₁ (z8 U v0) := by
    rw [disjoint_union_left]
    refine ⟨zo
        (hdisj_PBc.mono_right hU_sub_B) (hdisj_PB.mono_right v1), ?_⟩
    rw [disjoint_left]
    intro ⟨e, he⟩ he1 he2
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
      have h1 := (z5 B_all A huv).mp he1
      have h2 := (z5 U v0 huv).mp he2
      rcases h1 with ⟨_, hvA⟩ | ⟨_, huA⟩ <;> rcases h2 with ⟨huU, hvW⟩ | ⟨hvU, huW⟩
      · exact disjoint_left.mp hdisj_BA (v1 hvW) hvA
      · exact disjoint_left.mp hdisj_B_A (hU_sub_B hvU) hvA
      · exact disjoint_left.mp hdisj_B_A (hU_sub_B huU) huA
      · exact disjoint_left.mp hdisj_BA (v1 huW) huA
  let S₂ : Finset (z6 (nOf q m)) := S₁ ∪ z8 U v0
  let v7 : ℝ := (1 / 8 : ℝ) * exp (-13 * (A.card : ℝ))
  let Good2 : (z6 (nOf q m) → Bool) → Prop := fun f =>
    ∀ S ∈ A.powerset,
      v7 * (R : ℝ) ≤
        ((U.filter (fun u => ∀ z ∈ A, (∃ w ∈ W_z z, (z1 f).Adj u w) ↔ z ∈ S)).card : ℝ)
  have v6 : ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ S₂, f e = g e) → (Good2 f ↔ Good2 g) := by
    intro f g hfg
    have hadj : ∀ u ∈ U, ∀ w ∈ v0, (z1 f).Adj u w ↔ (z1 g).Adj u w := by
      intro u hu w hw
      have hne : u ≠ w := fun h => disjoint_left.mp v2 hu (h ▸ hw)
      rw [za f hne, za g hne,
        hfg _ (mem_union_right _ ((z5 U v0 hne).mpr (Or.inl ⟨hu, hw⟩)))]
    refine forall₂_congr fun S _ => ?_
    rw [filter_congr fun u hu => forall₂_congr fun z hz =>
      iff_congr (exists_congr fun w => and_congr_right fun hw =>
        hadj u hu w (mem_biUnion.mpr ⟨z, hz, hw⟩)) Iff.rfl]
  refine (zu hp0 hp1 S₁ S₂ subset_union_left f₁
    Good2 (fun f => ¬ ∃ y : Fin (nOf q m), ¬ zs q a y ∧ yn q hq (z1 f) a x y) v6
    (ε₁ := ((2 : ℝ) ^ A.card) * exp (-((R8 : ℝ)) / 64))
    (ε₂ := exp (-((R8 : ℝ)) / 64))
    (exp_pos _).le ?_ ?_).trans (by ring_nf; exact le_rfl)
  · have vd : z4 p (fun f_rem : {e // e ∉ S₁} → Bool => ¬ Good2 (z0 S₁ f₁ f_rem)) ≤
        z4 p (fun f_rem : {e // e ∉ S₁} → Bool =>
          ∃ S ∈ A.powerset,
            ((U.filter (fun u => ∀ z ∈ A,
              (∃ w ∈ W_z z, ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S₁),
                f_rem ⟨z7 u w h, hmem⟩ = true) ↔ z ∈ S)).card : ℝ) <
              (1 / 2) * ((U.card : ℝ) * exp (-13 * (A.card : ℝ)))) := by
      refine zi hp0 hp1 fun f_rem hnot => ?_
      simp only [Good2, not_forall, not_le] at hnot
      rcases hnot with ⟨S, hS, hlt⟩
      refine ⟨S, hS, ?_⟩
      have va : U.filter (fun u => ∀ z ∈ A,
            (∃ w ∈ W_z z, (z1 (z0 S₁ f₁ f_rem)).Adj u w) ↔ z ∈ S) =
          U.filter (fun u => ∀ z ∈ A,
            (∃ w ∈ W_z z, ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S₁),
              f_rem ⟨z7 u w h, hmem⟩ = true) ↔ z ∈ S) := by
        refine filter_congr fun u hu => forall₂_congr fun z hz =>
          iff_congr (exists_congr fun w => and_congr_right fun hw => ?_) Iff.rfl
        have hwW : w ∈ v0 := mem_biUnion.mpr ⟨z, hz, hw⟩
        have hne : u ≠ w := fun h => disjoint_left.mp v2 hu (h ▸ hwW)
        have vg : z7 u w hne ∉ S₁ :=
          disjoint_right.mp v3 ((z5 U v0 hne).mpr (Or.inl ⟨hu, hwW⟩))
        exact zb S₁ f₁ f_rem hne vg
      rw [← va]
      have vi : v7 * (R : ℝ) ≤ (1 / 2) * ((U.card : ℝ) * exp (-13 * (A.card : ℝ))) := by
        dsimp only [v7]
        have vb : 0 ≤ exp (-13 * (A.card : ℝ)) := (exp_pos _).le
        nlinarith only [hU_lo, vb]
      linarith
    have v9 := yj vh S₁ A v0 U vf W_z
      v4
      (fun z _ => fun w hw => mem_filter.mpr ⟨(mem_filter.mp hw).1,
        (mem_filter.mp hw).2.1⟩)
      (fun z hz => fun w hw => mem_biUnion.mpr ⟨z, hz, hw⟩)
      hW_only_lo
      (fun z₁ _ z₂ hz₂ hne => by
        rw [disjoint_left]; intro w hw1 hw2
        exact (mem_filter.mp hw1).2.2 z₂ hz₂ hne.symm (mem_filter.mp hw2).2)
      v2 v3
    have vc : exp (-((U.card : ℝ) * exp (-13 * (A.card : ℝ))) / 8) ≤
        exp (-((R8 : ℝ)) / 64) := by
      have hAT : (A.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast le_trans hA_card v5
      have h1 : exp (-13 * (T : ℝ)) ≤ exp (-13 * (A.card : ℝ)) :=
        exp_le_exp.mpr (by linarith)
      have h2 : ((R : ℝ) / 8) * exp (-13 * (T : ℝ)) ≤
          (U.card : ℝ) * exp (-13 * (A.card : ℝ)) :=
        mul_le_mul (by linarith) h1 (exp_pos _).le (Nat.cast_nonneg _)
      exact (exp_le_exp.mpr (by linarith)).trans ve.2.2.1
    exact (vd.trans v9).trans (mul_le_mul_of_nonneg_left vc (pow_nonneg (by norm_num) _))
  · intro f₂ hagree2 hGood2
    exact z1i q m hq hlp a x f₀ Bc B_all A U B v0 W_z
      hBc_eq hB_all_eq hA_eq hB_eq hU_sub_B hB_hi hB_all_lo hBb_x hA_card
      v4 rfl hdisj_PB hdisj_PBc hdisj_BA hdisj_Ball_B hdisj_B_A v2
      hU_not_x f₁ hagree (fun _ => rfl) f₂ hagree2 (hGood2 (fun _ => false))
lemma z0x (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (a : Fin (kOf q) → Fin (nOf q m)) (hinj : Function.Injective a)
    (x : Fin (nOf q m)) (hnx : ¬ zs q a x) :
    gProb (nOf q m) ((ROf m : ℝ)⁻¹)
      (EventE1 q (nOf q m) (KOf q m) ∩ EventEdeg q (nOf q m) (ROf m) ∩
        {G | (zh q hq G a x).card ≤ zd (m - 2) ∧
          ¬ ∃ y : Fin (nOf q m), ¬ zs q a y ∧ yn q hq G a x y}) ≤
      ((2 : ℝ) ^ (zd (m - 1) + 3)) * exp (-((R8Of m : ℝ)) / 64) := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set K := KOf q m
  set T := zd (m - 1)
  set Tprev := zd (m - 2)
  set p : ℝ := (R : ℝ)⁻¹
  have vg : R8 ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have vj : 10000 ≤ R := le_trans hlp.hR8_ge vg
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have v3 : Tprev ≤ T := y6 (by have := hlp.hm; omega)
  have vu : T ≤ R8 := le_trans (Nat.le_self_pow (by norm_num) T) (Nat.le_of_lt Nat.lt_two_pow_self)
  have vf : (R : ℝ) = (R8 : ℝ) ^ 8 := by exact_mod_cast zq m
  have vn := yf q m hlp
  let P : Finset (Fin (nOf q m)) := univ.image a ∪ {x}
  let S₀ : Finset (z6 (nOf q m)) := ze P
  have haP : ∀ r : Fin (kOf q), a r ∈ P := fun r =>
    mem_union_left _ (mem_image.mpr ⟨r, mem_univ _, rfl⟩)
  have hxP : x ∈ P := mem_union_right _ (mem_singleton_self x)
  let Good0 : Set (SimpleGraph (Fin (nOf q m))) :=
    {G | ((R : ℝ) / 3 ≤ ((zk q hq G a).card : ℝ) ∧ ((zk q hq G a).card : ℝ) ≤ 2 * (R : ℝ)) ∧
         ((zk q hq G a ∩ zm q hq G a).card < K) ∧
         ((1 / 4 : ℝ) * ((R : ℝ) ^ 2) ≤ ((zg q hq G a).card : ℝ) ∧
           ((zg q hq G a).card : ℝ) ≤ 2 * ((R : ℝ) ^ 2)) ∧
         ((zg q hq G a ∩ zc G (fun _ : Fin 1 => x)).card : ℝ) ≤ 2 * (R : ℝ) ∧
         (zh q hq G a x).card ≤ Tprev}
  let Bad : Set (SimpleGraph (Fin (nOf q m))) :=
    {G | ¬ ∃ y : Fin (nOf q m), ¬ zs q a y ∧ yn q hq G a x y}
  have v7 :
      EventE1 q (nOf q m) K ∩ EventEdeg q (nOf q m) R ∩
        {G | (zh q hq G a x).card ≤ Tprev ∧ G ∈ Bad} ⊆ Good0 ∩ Bad := by
    rintro G ⟨⟨hE1, hEdeg⟩, hcardA, hbad⟩
    have hdet := yw q m hq hlp hE1 hEdeg a hinj
    exact ⟨⟨hdet.1, hdet.2.2.1, hdet.2.2.2.1, hdet.2.2.2.2 x hnx, hcardA⟩, hbad⟩
  refine (gProb_mono hp0 hp1 v7).trans ?_
  refine w4 hp0 hp1 S₀ Good0 Bad ?_
    (((2 : ℝ) ^ (T + 3)) * exp (-((R8 : ℝ)) / 64)) (by positivity) ?_
  · intro f₀ f₂ f₂'
    have vr : ∀ e ∈ S₀, z0 S₀ f₀ f₂ e = z0 S₀ f₀ f₂' e := fun e he => by
      simp only [z0, dif_pos he]
    have hfix := yq hq a P haP (z0 S₀ f₀ f₂) (z0 S₀ f₀ f₂') vr
    have hNx : zc (z1 (z0 S₀ f₀ f₂)) (fun _ : Fin 1 => x) =
        zc (z1 (z0 S₀ f₀ f₂')) (fun _ : Fin 1 => x) := by
      ext z; simp only [zl]
      exact forall_congr' fun _ => by
        rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (G := z1 (z0 S₀ f₀ f₂'))]
        exact hfix.1 x hxP z
    simp only [Good0, Set.mem_ofPred_eq, hfix.2.1, hfix.2.2.1, hfix.2.2.2.1, hfix.2.2.2.2.2 x hxP, hNx]
  · intro f₀ hGood0
    let G₀ := z1 (z0 S₀ f₀ (fun _ => false))
    rcases hGood0 (fun _ => false) with ⟨⟨hBc_lo, hBc_hi⟩, hInter, ⟨hBb_lo, hBb_hi⟩, hBb_x, hA_card⟩
    let Bc := zk q hq G₀ a
    let Bc' := zm q hq G₀ a
    let Bb := zg q hq G₀ a
    let A := zh q hq G₀ a x
    have hInter' : (Bc ∩ Bc').card < K := hInter
    have hA_card' : A.card ≤ Tprev := hA_card
    let v0 := Bb.erase x
    let U := (Bc \ (Bc' ∪ A ∪ univ.image a)).erase x
    let B := (Bc \ (A ∪ univ.image a)).erase x
    have vd : U ⊆ B := by
      intro u hu
      rcases mem_erase.mp hu with ⟨hux, hu1⟩
      rcases mem_sdiff.mp hu1 with ⟨huBc, hnot⟩
      refine mem_erase.mpr ⟨hux, mem_sdiff.mpr ⟨huBc, fun h => ?_⟩⟩
      rcases mem_union.mp h with huA | huI
      · exact hnot (mem_union_left _ (mem_union_right _ huA))
      · exact hnot (mem_union_right _ huI)
    have vw : (B.card : ℝ) ≤ 2 * (R : ℝ) :=
      (Nat.cast_le.mpr (card_le_card ((erase_subset _ _).trans sdiff_subset))).trans hBc_hi
    have vt : (R : ℝ) / 4 ≤ (U.card : ℝ) := by
      have vl : Bc ⊆ U ∪ (Bc ∩ Bc') ∪ A ∪ univ.image a ∪ {x} := by
        intro u hu
        by_cases hux : u = x
        · exact mem_union_right _ (mem_singleton.mpr hux)
        · by_cases huI : u ∈ univ.image a
          · exact mem_union_left _ (mem_union_right _ huI)
          · by_cases huA : u ∈ A
            · exact mem_union_left _ (mem_union_left _ (mem_union_right _ huA))
            · by_cases huBc' : u ∈ Bc'
              · exact mem_union_left _ (mem_union_left _ (mem_union_left _
                  (mem_union_right _ (mem_inter.mpr ⟨hu, huBc'⟩))))
              · refine mem_union_left _ (mem_union_left _ (mem_union_left _
                  (mem_union_left _ (mem_erase.mpr ⟨hux, mem_sdiff.mpr ⟨hu, ?_⟩⟩))))
                simp [huBc', huA, huI]
      have vs : Bc.card ≤ U.card + (Bc ∩ Bc').card + A.card + kOf q + 1 := by
        have hI : (univ.image a).card ≤ kOf q := by
          calc (univ.image a).card ≤ (univ : Finset (Fin (kOf q))).card := card_image_le
            _ = kOf q := by simp
        calc Bc.card ≤ (U ∪ (Bc ∩ Bc') ∪ A ∪ univ.image a ∪ {x}).card := card_le_card vl
          _ ≤ (U ∪ (Bc ∩ Bc') ∪ A ∪ univ.image a).card + ({x} : Finset _).card := card_union_le _ _
          _ ≤ (U ∪ (Bc ∩ Bc') ∪ A).card + (univ.image a).card + 1 := by
              rw [card_singleton]; exact Nat.add_le_add_right (card_union_le _ _) 1
          _ ≤ (U ∪ (Bc ∩ Bc')).card + A.card + kOf q + 1 := by
              have := card_union_le (U ∪ (Bc ∩ Bc')) A; omega
          _ ≤ U.card + (Bc ∩ Bc').card + A.card + kOf q + 1 := by
              have := card_union_le U (Bc ∩ Bc'); omega
      have vk : (Bc ∩ Bc').card + A.card + kOf q + 1 ≤ 2 * R8 := by
        have := hlp.hK_le_R8; omega
      have vo : 2 * (R8 : ℝ) ≤ (R : ℝ) / 12 := by
        have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
        rw [vf]
        have : (R8 : ℝ) ^ 2 ≤ (R8 : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
        nlinarith only [hR8_ge, this]
      have hc1 : (Bc.card : ℝ) ≤ (U.card : ℝ) + ((Bc ∩ Bc').card + A.card + kOf q + 1 : ℕ) := by
        exact_mod_cast (show Bc.card ≤ U.card + ((Bc ∩ Bc').card + A.card + kOf q + 1) by omega)
      have hc2 : (((Bc ∩ Bc').card + A.card + kOf q + 1 : ℕ) : ℝ) ≤ 2 * (R8 : ℝ) := by exact_mod_cast vk
      linarith
    have v4 : (1 / 12 : ℝ) * ((R : ℝ) ^ 2) ≤ (v0.card : ℝ) := by
      have h1 : Bb.card ≤ v0.card + 1 := by
        by_cases hx : x ∈ Bb
        · rw [show v0 = Bb.erase x from rfl, card_erase_of_mem hx]; omega
        · rw [show v0 = Bb.erase x from rfl, erase_eq_of_notMem hx]; omega
      have hc : (Bb.card : ℝ) ≤ (v0.card : ℝ) + 1 := by exact_mod_cast h1
      have vv : (10000 : ℝ) ≤ (R : ℝ) := by exact_mod_cast vj
      nlinarith only [hBb_lo, hc, vv]
    have vb : (v0.card : ℝ) ≤ 2 * ((R : ℝ) ^ 2) :=
      (Nat.cast_le.mpr (card_le_card (erase_subset _ _))).trans hBb_hi
    have v6 : Disjoint P v0 := by
      rw [disjoint_left]; intro v hvP hvB
      rcases mem_erase.mp hvB with ⟨hvx, hvBb⟩
      rcases mem_union.mp hvP with hvimg | hvx'
      · rcases mem_image.mp hvimg with ⟨r, _, rfl⟩
        exact ((y8 q hq G₀ a (a r)).mp hvBb).1.1 ⟨r, rfl⟩
      · exact hvx (mem_singleton.mp hvx')
    have vc : Disjoint P A := by
      rw [disjoint_left]; intro z hzP hzA
      rcases (zt q hq G₀ a x z).mp hzA with ⟨_, hadj, hnotp⟩
      rcases mem_union.mp hzP with hzimg | hzx
      · rcases mem_image.mp hzimg with ⟨r, _, rfl⟩; exact hnotp ⟨r, rfl⟩
      · exact G₀.loopless.irrefl z (mem_singleton.mp hzx ▸ hadj)
    have v9 : Disjoint P B := by
      rw [disjoint_left]; intro u huP huB
      rcases mem_erase.mp huB with ⟨hux, hu1⟩
      rcases mem_sdiff.mp hu1 with ⟨_, hnot⟩
      rcases mem_union.mp huP with huimg | hux'
      · exact hnot (mem_union_right _ huimg)
      · exact hux (mem_singleton.mp hux')
    have v1 : Disjoint v0 A := by
      rw [disjoint_left]; intro w hwB hwA
      have hnot := ((y8 q hq G₀ a w).mp (mem_of_mem_erase hwB)).1
      exact hnot.2.1 ((zt q hq G₀ a x w).mp hwA).1
    have v5 : Disjoint v0 B := by
      rw [disjoint_left]; intro w hwB hwBc
      have hnot := ((y8 q hq G₀ a w).mp (mem_of_mem_erase hwB)).1
      have hbc : w ∈ zk q hq G₀ a := (mem_sdiff.mp (mem_of_mem_erase hwBc)).1
      exact hnot.2.1 (by unfold zk at hbc; exact (mem_filter.mp hbc).2)
    have va : Disjoint B A := by
      rw [disjoint_left]; intro u huB huA
      exact (mem_sdiff.mp (mem_of_mem_erase huB)).2 (mem_union_left _ huA)
    have ve : ∀ u ∈ U, ¬ G₀.Adj u x := by
      intro u hu hadj
      rcases mem_sdiff.mp (mem_of_mem_erase hu) with ⟨huBc, hnot⟩
      have vp : ¬ zs q a u := fun ⟨r, hr⟩ =>
        hnot (mem_union_right _ (mem_image.mpr ⟨r, mem_univ _, hr.symm⟩))
      have vq : isBc q hq G₀ a u := by
        change u ∈ zk q hq G₀ a at huBc
        unfold zk at huBc; exact (mem_filter.mp huBc).2
      have huA : u ∈ A := (zt q hq G₀ a x u).mpr ⟨vq, hadj, vp⟩
      exact hnot (mem_union_left _ (mem_union_right _ huA))
    let S₁ : Finset (z6 (nOf q m)) := S₀ ∪ z8 v0 A
    have v2 : Disjoint S₀ (z8 v0 A) :=
      zo v6 vc
    let Good1 : (z6 (nOf q m) → Bool) → Prop := fun f =>
      (∀ z ∈ A, ((v0.filter (fun w => (z1 f).Adj w z)).card : ℝ) ≤ 4 * (R : ℝ)) ∧
      (∀ z ∈ A, (R : ℝ) / 48 ≤
        ((v0.filter (fun w => (z1 f).Adj w z ∧
          ∀ z' ∈ A, z' ≠ z → ¬ (z1 f).Adj w z')).card : ℝ))
    have v8 : ∀ f g : z6 (nOf q m) → Bool,
        (∀ e ∈ S₁, f e = g e) → (Good1 f ↔ Good1 g) := by
      intro f g hfg
      have hadj : ∀ w ∈ v0, ∀ z ∈ A, (z1 f).Adj w z ↔ (z1 g).Adj w z := by
        intro w hw z hz
        have hne : w ≠ z := fun h => disjoint_left.mp v1 hw (h ▸ hz)
        rw [za f hne, za g hne,
          hfg _ (mem_union_right _ ((z5 v0 A hne).mpr (Or.inl ⟨hw, hz⟩)))]
      exact and_congr
        (forall₂_congr fun z hz => by rw [filter_congr fun w hw => hadj w hw z hz])
        (forall₂_congr fun z hz => by
          rw [filter_congr fun w hw =>
            and_congr (hadj w hw z hz)
              (forall₂_congr fun z' hz' => imp_congr_right fun _ => not_congr (hadj w hw z' hz'))])
    refine (zu hp0 hp1 S₀ S₁ subset_union_left f₀
      Good1 (fun f => z1 f ∈ Bad) v8
      (ε₁ := 2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200))
      (ε₂ := ((2 : ℝ) ^ A.card + 1) * exp (-((R8 : ℝ)) / 64))
      (by positivity) ?_ ?_).trans ?_
    · have vi : 4 * (A.card : ℝ) ≤ (R : ℝ) := by
        have h4R8 : 4 * R8 ≤ R := by
          have hpow : R8 ^ 2 ≤ R8 ^ 8 := Nat.pow_le_pow_right (z1e m) (by norm_num)
          have hreq : R = R8 ^ 8 := zq m
          have hge := hlp.hR8_ge
          nlinarith only [hpow, hreq, hge]
        have hnat : 4 * A.card ≤ R := by omega
        exact_mod_cast hnat
      have vm : z4 p (fun f_rem : {e // e ∉ S₀} → Bool => ¬ Good1 (z0 S₀ f₀ f_rem)) =
          z4 p (fun f_rem : {e // e ∉ S₀} → Bool =>
            ¬ ((∀ z ∈ A, ((v0.filter (fun w =>
                  ∃ (h : w ≠ z) (hmem : z7 w z h ∉ S₀), f_rem ⟨z7 w z h, hmem⟩ = true)).card : ℝ) ≤
                4 * (R : ℝ)) ∧
               (∀ z ∈ A, (R : ℝ) / 48 ≤
                 ((v0.filter (fun w =>
                   (∃ (h : w ≠ z) (hmem : z7 w z h ∉ S₀), f_rem ⟨z7 w z h, hmem⟩ = true) ∧
                   ∀ z' ∈ A, z' ≠ z →
                     ¬ ∃ (h : w ≠ z') (hmem : z7 w z' h ∉ S₀),
                       f_rem ⟨z7 w z' h, hmem⟩ = true)).card : ℝ)))) := by
        refine zx p fun f_rem => not_congr ?_
        have hadj : ∀ w ∈ v0, ∀ z ∈ A,
            (z1 (z0 S₀ f₀ f_rem)).Adj w z ↔
            ∃ (h : w ≠ z) (hmem : z7 w z h ∉ S₀), f_rem ⟨z7 w z h, hmem⟩ = true := by
          intro w hw z hz
          have hne : w ≠ z := fun h => disjoint_left.mp v1 hw (h ▸ hz)
          have hnot : z7 w z hne ∉ S₀ :=
            disjoint_right.mp v2 ((z5 v0 A hne).mpr (Or.inl ⟨hw, hz⟩))
          exact zb S₀ f₀ f_rem hne hnot
        exact and_congr
          (forall₂_congr fun z hz => by rw [filter_congr fun w hw => hadj w hw z hz])
          (forall₂_congr fun z hz => by
            rw [filter_congr fun w hw =>
              and_congr (hadj w hw z hz)
                (forall₂_congr fun z' hz' => imp_congr_right fun _ => not_congr (hadj w hw z' hz'))])
      rw [vm]
      exact yk vj S₀ v0 v0 A (Subset.refl _)
        v1 v2 v4 vb vi
    · intro f₁ hagree hGood1
      rcases hGood1 (fun _ => false) with ⟨hW_hi, hW_only_lo⟩
      exact z1j q m hq hlp a x f₀ Bc v0 A U B
        rfl rfl rfl rfl vd vw vt v4 hBb_x hA_card'
        v6 v9 v1 v5 va ve
        f₁ hagree hW_hi hW_only_lo
    · have hAT : (A.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast le_trans hA_card' v3
      have h1 : 2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200) ≤
          2 * (T : ℝ) * exp (-((R8 : ℝ)) / 64) := by
        calc 2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200)
            ≤ 2 * (T : ℝ) * exp (-((R : ℝ)) / 200) := by
              have := exp_pos (-((R : ℝ)) / 200); nlinarith
          _ ≤ 2 * (T : ℝ) * exp (-((R8 : ℝ)) / 64) :=
              mul_le_mul_of_nonneg_left vn.1 (by positivity)
      have h2 : ((2 : ℝ) ^ A.card + 1) * exp (-((R8 : ℝ)) / 64) ≤
          ((2 : ℝ) ^ T + 1) * exp (-((R8 : ℝ)) / 64) := by
        refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
        have : (2 : ℝ) ^ A.card ≤ (2 : ℝ) ^ T := pow_le_pow_right₀ (by norm_num) (le_trans hA_card' v3)
        linarith
      have hsum : 2 * (T : ℝ) + ((2 : ℝ) ^ T + 1) ≤ (2 : ℝ) ^ (T + 3) := by
        have hlt : (T : ℝ) ≤ (2 : ℝ) ^ T := by exact_mod_cast Nat.le_of_lt Nat.lt_two_pow_self
        have vx : (1 : ℝ) ≤ (2 : ℝ) ^ T := by exact_mod_cast Nat.one_le_pow T 2 (by norm_num)
        rw [pow_add]; norm_num; linarith
      have vh : 0 ≤ exp (-((R8 : ℝ)) / 64) := (exp_pos _).le
      nlinarith only [h1, h2, hsum, vh]
lemma wl (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) :
    gProb (nOf q m) ((ROf m : ℝ)⁻¹)
      (EventE1 q (nOf q m) (KOf q m) ∩ EventEdeg q (nOf q m) (ROf m) ∩
        (EventE3 q hq (nOf q m) m)ᶜ) ≤ 1 / 64 := by
  classical
  set n := nOf q m
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set p : ℝ := (R : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  let InjA := univ.filter (fun a : Fin (kOf q) → Fin n => Function.Injective a)
  let BadPair : (Fin (kOf q) → Fin n) → Fin n → Set (SimpleGraph (Fin n)) := fun a x =>
    EventE1 q n (KOf q m) ∩ EventEdeg q n R ∩
      {G | (zh q hq G a x).card ≤ zd (m - 2) ∧
        ¬ ∃ y : Fin n, ¬ zs q a y ∧ yn q hq G a x y}
  have hsub : EventE1 q n (KOf q m) ∩ EventEdeg q n R ∩ (EventE3 q hq n m)ᶜ ⊆
      ⋃ a ∈ InjA, ⋃ x ∈ univ.filter (fun x => ¬ zs q a x), BadPair a x := by
    rintro G ⟨⟨hE1, hEdeg⟩, hnotE3⟩
    simp only [Set.mem_compl_iff, EventE3, Set.mem_ofPred_eq, not_forall] at hnotE3
    rcases hnotE3 with ⟨a, hinj, x, hnx, hcard, hno⟩
    exact Set.mem_biUnion (mem_filter.mpr ⟨mem_univ _, hinj⟩)
      (Set.mem_biUnion (mem_filter.mpr ⟨mem_univ _, hnx⟩) ⟨⟨hE1, hEdeg⟩, hcard, hno⟩)
  have v0 : (InjA.card : ℝ) ≤ (n : ℝ) ^ (kOf q) := by
    have : InjA.card ≤ (univ : Finset (Fin (kOf q) → Fin n)).card :=
      card_le_card (subset_univ _)
    simpa [Fintype.card_fun, Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr this
  calc gProb n p (EventE1 q n (KOf q m) ∩ EventEdeg q n R ∩ (EventE3 q hq n m)ᶜ)
      ≤ gProb n p (⋃ a ∈ InjA, ⋃ x ∈ univ.filter (fun x => ¬ zs q a x), BadPair a x) :=
        gProb_mono hp0 hp1 hsub
    _ ≤ ∑ a ∈ InjA, gProb n p (⋃ x ∈ univ.filter (fun x => ¬ zs q a x), BadPair a x) :=
        yd hp0 hp1 _ _
    _ ≤ ∑ a ∈ InjA, ∑ x ∈ univ.filter (fun x => ¬ zs q a x), gProb n p (BadPair a x) :=
        sum_le_sum fun a _ => yd hp0 hp1 _ _
    _ ≤ ∑ _a ∈ InjA, ((n : ℝ) * (((2 : ℝ) ^ (T + 3)) * exp (-((R8 : ℝ)) / 64))) := by
        refine sum_le_sum fun a ha => ?_
        have hinj : Function.Injective a := (mem_filter.mp ha).2
        calc ∑ x ∈ univ.filter (fun x => ¬ zs q a x), gProb n p (BadPair a x)
            ≤ ∑ _x ∈ univ.filter (fun x => ¬ zs q a x),
                (((2 : ℝ) ^ (T + 3)) * exp (-((R8 : ℝ)) / 64)) :=
              sum_le_sum fun x hx =>
                z0x q m hq hlp a hinj x (mem_filter.mp hx).2
          _ = ((univ.filter (fun x => ¬ zs q a x)).card : ℝ) *
                (((2 : ℝ) ^ (T + 3)) * exp (-((R8 : ℝ)) / 64)) := by
              rw [sum_const, nsmul_eq_mul]
          _ ≤ (n : ℝ) * (((2 : ℝ) ^ (T + 3)) * exp (-((R8 : ℝ)) / 64)) := by
              have hle : ((univ.filter (fun x => ¬ zs q a x)).card : ℝ) ≤ (n : ℝ) := by
                have : (univ.filter (fun x => ¬ zs q a x)).card ≤
                    (univ : Finset (Fin n)).card := card_le_card (subset_univ _)
                simpa using (Nat.cast_le (α := ℝ)).mpr this
              exact mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (InjA.card : ℝ) * (n : ℝ) * (((2 : ℝ) ^ (T + 3)) * exp (-((R8 : ℝ)) / 64)) := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ((n : ℝ) ^ (kOf q + 4)) * ((2 : ℝ) ^ (T + 10)) * exp (-((R8 : ℝ)) / 64) := by
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast wq q m
        have h1 : (InjA.card : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ (kOf q + 4) := by
          calc (InjA.card : ℝ) * (n : ℝ) ≤ ((n : ℝ) ^ (kOf q)) * (n : ℝ) :=
                mul_le_mul_of_nonneg_right v0 (by positivity)
            _ = (n : ℝ) ^ (kOf q + 1) := (pow_succ _ _).symm
            _ ≤ (n : ℝ) ^ (kOf q + 4) := pow_le_pow_right₀ hn1 (by omega)
        have h2 : (2 : ℝ) ^ (T + 3) ≤ (2 : ℝ) ^ (T + 10) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hmul := mul_le_mul h1 h2 (by positivity) (by positivity)
        have v1 : 0 ≤ exp (-((R8 : ℝ)) / 64) := (exp_pos _).le
        calc (InjA.card : ℝ) * (n : ℝ) * (((2 : ℝ) ^ (T + 3)) * exp (-((R8 : ℝ)) / 64))
            = ((InjA.card : ℝ) * (n : ℝ) * ((2 : ℝ) ^ (T + 3))) * exp (-((R8 : ℝ)) / 64) := by ring
          _ ≤ (((n : ℝ) ^ (kOf q + 4)) * ((2 : ℝ) ^ (T + 10))) * exp (-((R8 : ℝ)) / 64) :=
              mul_le_mul_of_nonneg_right hmul v1
    _ ≤ 1 / 256 := hlp.hpoly_exp_R8
    _ ≤ 1 / 64 := by norm_num
end
section
open scoped BigOperators Classical
open Finset Real Nat
lemma z0l {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι)
    (A B : (ι → Bool) → Prop)
    (hA_dep : ∀ f₁ (f₂ f₂' : {i // i ∉ S} → Bool), A (z0 S f₁ f₂) ↔ A (z0 S f₁ f₂'))
    (c : ℝ) (_hc : 0 ≤ c)
    (hcond : ∀ f₁ : {i // i ∈ S} → Bool,
      (∀ f₂ : {i // i ∉ S} → Bool, A (z0 S f₁ f₂)) →
      c ≤ z4 p (fun f₂ : {i // i ∉ S} → Bool => B (z0 S f₁ f₂))) :
    z4 p A * c ≤ z4 p (fun f => A f ∧ B f) := by
  classical
  have hLHS : z4 p A =
      ∑ f₁ : {i // i ∈ S} → Bool,
        if A (z0 S f₁ (fun _ => false)) then ∏ x : {i // i ∈ S}, z9 p (f₁ x) else 0 := by
    unfold z4
    rw [← Equiv.sum_comp (zw S).symm, Fintype.sum_prod_type]
    refine sum_congr rfl fun f₁ _ => ?_
    by_cases hA : A (z0 S f₁ (fun _ => false))
    · rw [if_pos hA]
      have v0 : ∀ f₂ : {i // i ∉ S} → Bool,
          (if A ((zw S).symm (f₁, f₂)) then ∏ i : ι, z9 p ((zw S).symm (f₁, f₂) i) else 0) =
          (∏ x : {i // i ∈ S}, z9 p (f₁ x)) * (∏ x : {i // i ∉ S}, z9 p (f₂ x)) := by
        intro f₂
        change (if A (z0 S f₁ f₂) then ∏ i : ι, z9 p (z0 S f₁ f₂ i) else 0) = _
        rw [if_pos ((hA_dep f₁ (fun _ => false) f₂).mp hA), y7]
      simp_rw [v0, ← mul_sum, y4, mul_one]
    · rw [if_neg hA]
      refine sum_eq_zero fun f₂ _ => ?_
      change (if A (z0 S f₁ f₂) then _ else 0) = 0
      rw [if_neg (fun h => hA ((hA_dep f₁ f₂ (fun _ => false)).mp h))]
  have hRHS : z4 p (fun f => A f ∧ B f) =
      ∑ f₁ : {i // i ∈ S} → Bool,
        if A (z0 S f₁ (fun _ => false)) then
          (∏ x : {i // i ∈ S}, z9 p (f₁ x)) *
            z4 p (fun f₂ : {i // i ∉ S} → Bool => B (z0 S f₁ f₂))
        else 0 := by
    unfold z4
    rw [← Equiv.sum_comp (zw S).symm, Fintype.sum_prod_type]
    refine sum_congr rfl fun f₁ _ => ?_
    by_cases hA : A (z0 S f₁ (fun _ => false))
    · rw [if_pos hA, mul_sum]
      refine sum_congr rfl fun f₂ _ => ?_
      have hA2 : A (z0 S f₁ f₂) := (hA_dep f₁ (fun _ => false) f₂).mp hA
      have hsp : (zw S).symm (f₁, f₂) = z0 S f₁ f₂ := rfl
      simp only [hsp, y7]
      by_cases hB : B (z0 S f₁ f₂)
      · rw [if_pos ⟨hA2, hB⟩, if_pos hB]
      · rw [if_neg (fun h => hB h.2), if_neg hB, mul_zero]
    · rw [if_neg hA]
      refine sum_eq_zero fun f₂ _ => ?_
      have hsp : (zw S).symm (f₁, f₂) = z0 S f₁ f₂ := rfl
      simp only [hsp]
      rw [if_neg (fun h => hA ((hA_dep f₁ f₂ (fun _ => false)).mp h.1))]
  rw [hLHS, hRHS, sum_mul]
  refine sum_le_sum fun f₁ _ => ?_
  by_cases hA : A (z0 S f₁ (fun _ => false))
  · rw [if_pos hA, if_pos hA]
    have hw : 0 ≤ ∏ x : {i // i ∈ S}, z9 p (f₁ x) :=
      prod_nonneg fun _ _ => yh hp0 hp1 _
    exact mul_le_mul_of_nonneg_left
      (hcond f₁ fun f₂ => (hA_dep f₁ (fun _ => false) f₂).mp hA) hw
  · rw [if_neg hA, if_neg hA, zero_mul]
lemma z06 {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S₀ S₁ : Finset (z6 n)) (hsub : S₀ ⊆ S₁)
    (f₀ : {e : z6 n // e ∈ S₀} → Bool)
    (A B : (z6 n → Bool) → Prop)
    (hA_dep : ∀ f g : z6 n → Bool, (∀ e ∈ S₁, f e = g e) → (A f ↔ A g))
    (c : ℝ) (hc : 0 ≤ c)
    (hcond : ∀ f₁ : {e : z6 n // e ∈ S₁} → Bool,
      (∀ x : {e // e ∈ S₀}, f₁ ⟨x.1, hsub x.2⟩ = f₀ x) →
      (∀ f₂ : {e // e ∉ S₁} → Bool, A (z0 S₁ f₁ f₂)) →
      c ≤ z4 p (fun f₂ : {e // e ∉ S₁} → Bool => B (z0 S₁ f₁ f₂))) :
    z4 p (fun f_rem : {e : z6 n // e ∉ S₀} → Bool => A (z0 S₀ f₀ f_rem)) * c ≤
      z4 p (fun f_rem : {e : z6 n // e ∉ S₀} → Bool =>
        A (z0 S₀ f₀ f_rem) ∧ B (z0 S₀ f₀ f_rem)) := by
  classical
  let T : Finset {e : z6 n // e ∉ S₀} := univ.filter (fun x => x.1 ∈ S₁)
  let mkF1 : ({x : {e : z6 n // e ∉ S₀} // x ∈ T} → Bool) → ({e : z6 n // e ∈ S₁} → Bool) :=
    fun g₁ y => if h0 : y.1 ∈ S₀ then f₀ ⟨y.1, h0⟩
      else g₁ ⟨⟨y.1, h0⟩, mem_filter.mpr ⟨mem_univ _, y.2⟩⟩
  let eRem : {x : {e : z6 n // e ∉ S₀} // x ∉ T} ≃ {e : z6 n // e ∉ S₁} :=
    { toFun := fun z => ⟨z.1.1, fun h1 => z.2 (mem_filter.mpr ⟨mem_univ _, h1⟩)⟩
      invFun := fun y => ⟨⟨y.1, fun h0 => y.2 (hsub h0)⟩, fun hT => y.2 (mem_filter.mp hT).2⟩
      left_inv := fun z => by ext; rfl
      right_inv := fun y => by ext; rfl }
  have v0 : ∀ (g₁ : {x : {e : z6 n // e ∉ S₀} // x ∈ T} → Bool)
      (g₂ : {x : {e : z6 n // e ∉ S₀} // x ∉ T} → Bool),
      z0 S₀ f₀ (z0 T g₁ g₂) =
        z0 S₁ (mkF1 g₁) (fun y => g₂ (eRem.symm y)) := by
    intro g₁ g₂
    funext e
    by_cases h0 : e ∈ S₀
    · have h1 : e ∈ S₁ := hsub h0
      simp [z0, mkF1, h0, h1]
    · by_cases h1 : e ∈ S₁
      · have hT : (⟨e, h0⟩ : {e // e ∉ S₀}) ∈ T := mem_filter.mpr ⟨mem_univ _, h1⟩
        simp [z0, mkF1, h0, h1, hT]
      · have v5 : (⟨e, h0⟩ : {e // e ∉ S₀}) ∉ T := fun h => h1 (mem_filter.mp h).2
        simp [z0, eRem, h0, h1, v5]
  refine z0l hp0 hp1 T
    (fun f_rem => A (z0 S₀ f₀ f_rem))
    (fun f_rem => B (z0 S₀ f₀ f_rem)) ?_ c hc ?_
  · intro g₁ g₂ g₂'
    refine hA_dep _ _ fun e he1 => ?_
    rw [v0, v0]; simp [z0, he1]
  · intro g₁ hAg₁
    have v4 : ∀ x : {e // e ∈ S₀}, mkF1 g₁ ⟨x.1, hsub x.2⟩ = f₀ x := by
      intro x; simp [mkF1, x.2]
    have hA1 : ∀ f₂ : {e // e ∉ S₁} → Bool, A (z0 S₁ (mkF1 g₁) f₂) := by
      intro f₂
      have := hAg₁ (fun z => f₂ (eRem z))
      rw [v0] at this
      have hfun : (fun y : {e // e ∉ S₁} => f₂ (eRem (eRem.symm y))) = f₂ := by
        funext y; simp
      rwa [hfun] at this
    have v3 := hcond (mkF1 g₁) v4 hA1
    have hbij : z4 p (fun g₂ : {x : {e : z6 n // e ∉ S₀} // x ∉ T} → Bool =>
          B (z0 S₀ f₀ (z0 T g₁ g₂))) =
        z4 p (fun f₂ : {e // e ∉ S₁} → Bool => B (z0 S₁ (mkF1 g₁) f₂)) := by
      unfold z4
      let eFun : ({x : {e : z6 n // e ∉ S₀} // x ∉ T} → Bool) ≃ ({e : z6 n // e ∉ S₁} → Bool) :=
        Equiv.arrowCongr eRem (Equiv.refl Bool)
      refine Fintype.sum_equiv eFun _ _ fun g₂ => ?_
      have v2 : B (z0 S₀ f₀ (z0 T g₁ g₂)) ↔ B (z0 S₁ (mkF1 g₁) (eFun g₂)) := by
        rw [v0]; rfl
      have v1 : (∏ z : {x : {e : z6 n // e ∉ S₀} // x ∉ T}, z9 p (g₂ z)) =
          ∏ y : {e : z6 n // e ∉ S₁}, z9 p (eFun g₂ y) :=
        Fintype.prod_equiv eRem _ _ fun z => by simp [eFun]
      by_cases hB : B (z0 S₀ f₀ (z0 T g₁ g₂))
      · rw [if_pos hB, if_pos (v2.mp hB), v1]
      · rw [if_neg hB, if_neg (fun h => hB (v2.mpr h))]
    rw [hbij]
    exact v3
noncomputable def QOf (m : ℕ) : ℝ := exp (-(20 * (m : ℝ) * (zd (m - 1) : ℝ) ^ 2 + 100))
lemma z1z (m : ℕ) : 0 < QOf m := exp_pos _
lemma z19 (q m : ℕ) (hlp : LargeParams q m) :
    exp (2 * (20 * (m : ℝ) * (zd (m - 1) : ℝ) ^ 2 + 100) + 10) ≤ (R8Of m : ℝ) := by
  set T := zd (m - 1)
  have h1 : 2 * (2 * (20 * (m : ℝ) * (T : ℝ) ^ 2 + 100) + 10) ≤ (EOf m : ℝ) := by
    have hE : (1000 : ℝ) * ((q : ℝ) + (m : ℝ) + (T : ℝ) ^ 3 + 100) ≤ (EOf m : ℝ) := by
      exact_mod_cast hlp.hT_pow_le_E
    have hmT : (m : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast y9 m (by have := hlp.hm; omega)
    have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast z03 (m - 1)
    have hm10 : (10 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlp.hm
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith only [hE, hmT, hT1, hm10, hq0]
  have h2 := z11 (2 * (20 * (m : ℝ) * (T : ℝ) ^ 2 + 100) + 10) (EOf m) h1
  simpa [R8Of] using h2
lemma yi (q m : ℕ) (hlp : LargeParams q m) :
    (R8Of m : ℝ) ≤ ((R4Of m : ℝ) * (QOf m) ^ 2) / 2 ∧
    (R8Of m : ℝ) ≤ ((R4Of m : ℝ) * QOf m) / 8 ∧
    exp (-((R8Of m : ℝ))) ≤ 1 / 256 ∧
    2 / (R2Of m : ℝ) ≤ 1 / 256 ∧
    ((R4Of m : ℝ) * (m : ℝ)) * ((ROf m : ℝ))⁻¹ ≤ 1 / 256 := by
  set T := zd (m - 1)
  set R8 := R8Of m
  set R4 := R4Of m
  set R2 := R2Of m
  set R := ROf m
  have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
  have v1 : (0 : ℝ) < (R8 : ℝ) := by linarith
  have v0 : (R4 : ℝ) = (R8 : ℝ) ^ 2 := by exact_mod_cast z1r m
  have vg : (R2 : ℝ) = (R4 : ℝ) ^ 2 := by exact_mod_cast z2f m
  have vj : (R : ℝ) = (R4 : ℝ) ^ 4 := by exact_mod_cast wz m
  have vi := z19 q m hlp
  have v8 : (exp 10) / (R8 : ℝ) ≤ (QOf m) ^ 2 := by
    have h1 : (QOf m) ^ 2 = (exp (2 * (20 * (m : ℝ) * (T : ℝ) ^ 2 + 100)))⁻¹ := by
      unfold QOf
      rw [← exp_nat_mul, ← exp_neg]; congr 1; ring
    rw [h1, div_le_iff₀ v1]
    calc exp 10 = (exp (2 * (20 * (m : ℝ) * (T : ℝ) ^ 2 + 100)))⁻¹ *
            exp (2 * (20 * (m : ℝ) * (T : ℝ) ^ 2 + 100) + 10) := by
          rw [exp_add, ← mul_assoc, inv_mul_cancel₀ (exp_pos _).ne', one_mul]
      _ ≤ (exp (2 * (20 * (m : ℝ) * (T : ℝ) ^ 2 + 100)))⁻¹ * (R8 : ℝ) :=
          mul_le_mul_of_nonneg_left vi (inv_nonneg.mpr (exp_pos _).le)
  have he10 : (10 : ℝ) ≤ exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
  have vd : (R8 : ℝ) ≤ ((R4 : ℝ) * (QOf m) ^ 2) / 2 := by
    have hmul : (R4 : ℝ) * ((exp 10) / (R8 : ℝ)) ≤ (R4 : ℝ) * (QOf m) ^ 2 :=
      mul_le_mul_of_nonneg_left v8 (by positivity)
    have v3 : (R4 : ℝ) * ((exp 10) / (R8 : ℝ)) = (R8 : ℝ) * exp 10 := by
      rw [v0]; field_simp
    nlinarith only [hmul, v3, he10, v1]
  have vh : QOf m ≤ 1 := by
    unfold QOf; rw [exp_le_one_iff]
    have : 0 ≤ 20 * (m : ℝ) * (T : ℝ) ^ 2 := by positivity
    linarith
  have vc : (R8 : ℝ) ≤ ((R4 : ℝ) * QOf m) / 8 := by
    have h1 : (QOf m) ^ 2 ≤ QOf m := by
      have := z1z m; nlinarith only [this, vh]
    have v5 : (0 : ℝ) ≤ (R4 : ℝ) := Nat.cast_nonneg _
    have h2 : (R4 : ℝ) * (QOf m) ^ 2 ≤ (R4 : ℝ) * QOf m := mul_le_mul_of_nonneg_left h1 v5
    have h3 : (R8 : ℝ) * 10 ≤ (R4 : ℝ) * (QOf m) ^ 2 := by
      have hmul : (R4 : ℝ) * ((exp 10) / (R8 : ℝ)) ≤ (R4 : ℝ) * (QOf m) ^ 2 :=
        mul_le_mul_of_nonneg_left v8 v5
      have v3 : (R4 : ℝ) * ((exp 10) / (R8 : ℝ)) = (R8 : ℝ) * exp 10 := by
        rw [v0]; field_simp
      nlinarith only [hmul, v3, he10, v1]
    linarith
  have vb : exp (-((R8 : ℝ))) ≤ 1 / 256 := by
    have h1 : (10000 : ℝ) ≤ exp (R8 : ℝ) := by linarith [Real.add_one_le_exp (R8 : ℝ)]
    rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
    linarith
  have va : 2 / (R2 : ℝ) ≤ 1 / 256 := by
    have v2 : (10000 : ℝ) ≤ (R4 : ℝ) := by rw [v0]; nlinarith only [hR8_ge]
    have vm : (10000 : ℝ) ≤ (R2 : ℝ) := by rw [vg]; nlinarith only [v2]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have v9 : ((R4 : ℝ) * (m : ℝ)) * ((R : ℝ))⁻¹ ≤ 1 / 256 := by
    have v4 : (m : ℝ) ≤ (R8 : ℝ) := by
      have hmT : m ≤ T := y9 m (by have := hlp.hm; omega)
      have v7 : T ≤ EOf m := Nat.le_self_pow (by norm_num) T
      have v6 : EOf m ≤ R8 := Nat.le_of_lt Nat.lt_two_pow_self
      exact_mod_cast le_trans (le_trans hmT v7) v6
    have vf : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (R_pos m)
    rw [← div_eq_mul_inv, div_le_div_iff₀ vf (by norm_num)]
    have v2 : (10000 : ℝ) ≤ (R4 : ℝ) := by rw [v0]; nlinarith only [hR8_ge]
    have vn : (R4 : ℝ) ^ 2 ≤ (R4 : ℝ) ^ 4 := by
      have : (1 : ℝ) ≤ (R4 : ℝ) := by linarith
      exact pow_le_pow_right₀ this (by norm_num)
    have vl : (R4 : ℝ) * (R8 : ℝ) ≤ (R4 : ℝ) ^ 2 := by
      rw [v0]; nlinarith only [hR8_ge]
    have vk : 256 * ((R4 : ℝ) * (R8 : ℝ)) ≤ (R4 : ℝ) ^ 4 := by
      have : 256 * (R4 : ℝ) ^ 2 ≤ (R4 : ℝ) ^ 4 := by
        have hsq : (R4 : ℝ) ^ 4 = (R4 : ℝ) ^ 2 * (R4 : ℝ) ^ 2 := by ring
        rw [hsq]
        have h2 : (256 : ℝ) ≤ (R4 : ℝ) ^ 2 := by nlinarith only [v2]
        nlinarith only [h2, sq_nonneg (R4 : ℝ)]
      nlinarith only [vl, this]
    have ve : (R4 : ℝ) * (m : ℝ) ≤ (R4 : ℝ) * (R8 : ℝ) :=
      mul_le_mul_of_nonneg_left v4 (Nat.cast_nonneg _)
    rw [vj]
    nlinarith only [ve, vk]
  exact ⟨vd, vc, vb, va, v9⟩
lemma z0e {α : Type*} [DecidableEq α] (U : Finset α) (m s : ℕ)
    (hms : m * s ≤ U.card) :
    ∃ C : Fin m → Finset α,
      (∀ i : Fin m, C i ⊆ U) ∧
      (∀ i : Fin m, (C i).card = s) ∧
      Set.PairwiseDisjoint ((univ : Finset (Fin m)) : Set (Fin m)) C := by
  induction m generalizing U with
  | zero =>
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  | succ k ih =>
    have v0 : s ≤ U.card := by
      have : s ≤ (k + 1) * s := by nlinarith
      omega
    obtain ⟨A, hAU, hAcard⟩ := exists_subset_card_eq v0
    have hrem : k * s ≤ (U \ A).card := by
      rw [card_sdiff, inter_eq_left.mpr hAU]
      have : (k + 1) * s = k * s + s := by ring
      omega
    obtain ⟨C', hC'sub, hC'card, hC'disj⟩ := ih (U \ A) hrem
    let C : Fin (k + 1) → Finset α := Fin.cases A C'
    refine ⟨C, ?_, ?_, ?_⟩
    · intro i; refine Fin.cases ?_ ?_ i
      · exact hAU
      · intro j; exact (hC'sub j).trans sdiff_subset
    · intro i; refine Fin.cases ?_ ?_ i
      · exact hAcard
      · intro j; exact hC'card j
    · intro i _ j _ hij
      change Disjoint (C i) (C j)
      revert hij
      refine Fin.cases ?_ ?_ i
      · refine Fin.cases ?_ ?_ j
        · intro hij; exact absurd rfl hij
        · intro j' _
          exact disjoint_left.mpr fun x hxA hxC =>
            (mem_sdiff.mp (hC'sub j' hxC)).2 hxA
      · intro i'
        refine Fin.cases ?_ ?_ j
        · intro _
          exact disjoint_left.mpr fun x hxC hxA =>
            (mem_sdiff.mp (hC'sub i' hxC)).2 hxA
        · intro j' hij
          have hne : i' ≠ j' := fun h => hij (by rw [h])
          exact hC'disj (mem_coe.mpr (mem_univ i'))
            (mem_coe.mpr (mem_univ j')) hne
lemma wi {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S_rev : Finset (z6 n)) (V W : Finset (Fin n))
    (hdisj_VW : Disjoint V W) (hdisj_S : Disjoint S_rev (z8 V W)) :
    let adj : ({e : z6 n // e ∉ S_rev} → Bool) → Fin n → Fin n → Prop :=
      fun f u v => ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S_rev), f ⟨z7 u v h, hmem⟩ = true
    z4 p (fun f : {e : z6 n // e ∉ S_rev} → Bool =>
      ∃ v₁ ∈ V, ∃ v₂ ∈ V, v₁ ≠ v₂ ∧ ∃ z ∈ W, adj f v₁ z ∧ adj f v₂ z) ≤
      ((V.card : ℝ) ^ 2) * (W.card : ℝ) * p ^ 2 := by
  classical
  let adj : ({e : z6 n // e ∉ S_rev} → Bool) → Fin n → Fin n → Prop :=
    fun f u v => ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S_rev), f ⟨z7 u v h, hmem⟩ = true
  calc z4 p (fun f => ∃ v₁ ∈ V, ∃ v₂ ∈ V, v₁ ≠ v₂ ∧ ∃ z ∈ W, adj f v₁ z ∧ adj f v₂ z)
      ≤ ∑ v₁ ∈ V, z4 p (fun f => ∃ v₂ ∈ V, v₁ ≠ v₂ ∧ ∃ z ∈ W, adj f v₁ z ∧ adj f v₂ z) :=
        y3 hp0 hp1 V _
    _ ≤ ∑ v₁ ∈ V, ∑ v₂ ∈ V, z4 p (fun f => v₁ ≠ v₂ ∧ ∃ z ∈ W, adj f v₁ z ∧ adj f v₂ z) :=
        sum_le_sum fun v₁ _ => y3 hp0 hp1 V _
    _ ≤ ∑ _v₁ ∈ V, ∑ _v₂ ∈ V, ((W.card : ℝ) * p ^ 2) := by
        refine sum_le_sum fun v₁ hv₁ => sum_le_sum fun v₂ hv₂ => ?_
        by_cases hne : v₁ = v₂
        · subst hne
          have v2 : z4 p (fun f : {e // e ∉ S_rev} → Bool =>
              v₁ ≠ v₁ ∧ ∃ z ∈ W, adj f v₁ z ∧ adj f v₁ z) = 0 := by
            rw [zx p (Q := fun _ => False) (fun _ => by simp), z1y]
          rw [v2]; positivity
        · have h1 : z4 p (fun f => v₁ ≠ v₂ ∧ ∃ z ∈ W, adj f v₁ z ∧ adj f v₂ z) ≤
              z4 p (fun f => ∃ z ∈ W, adj f v₁ z ∧ adj f v₂ z) :=
            zi hp0 hp1 fun _ h => h.2
          refine h1.trans ((y3 hp0 hp1 W _).trans ?_)
          calc ∑ z ∈ W, z4 p (fun f => adj f v₁ z ∧ adj f v₂ z)
              ≤ ∑ _z ∈ W, p ^ 2 := by
                refine sum_le_sum fun z hz => ?_
                have hne1 : v₁ ≠ z := fun h => disjoint_left.mp hdisj_VW hv₁ (h ▸ hz)
                have hne2 : v₂ ≠ z := fun h => disjoint_left.mp hdisj_VW hv₂ (h ▸ hz)
                have v1 : z7 v₁ z hne1 ∉ S_rev := disjoint_right.mp hdisj_S
                  ((z5 V W hne1).mpr (Or.inl ⟨hv₁, hz⟩))
                have v0 : z7 v₂ z hne2 ∉ S_rev := disjoint_right.mp hdisj_S
                  ((z5 V W hne2).mpr (Or.inl ⟨hv₂, hz⟩))
                let e₁ : {e : z6 n // e ∉ S_rev} := ⟨z7 v₁ z hne1, v1⟩
                let e₂ : {e : z6 n // e ∉ S_rev} := ⟨z7 v₂ z hne2, v0⟩
                have v4 : e₁ ≠ e₂ := by
                  intro heq
                  rcases zv heq with ⟨hv, _⟩ | ⟨hv, _⟩
                  · exact hne hv
                  · exact disjoint_left.mp hdisj_VW hv₁ (hv ▸ hz)
                have v3 : z4 p (fun f => adj f v₁ z ∧ adj f v₂ z) =
                    z4 p (fun f : {e // e ∉ S_rev} → Bool => ∀ e ∈ ({e₁, e₂} : Finset _), f e = true) := by
                  refine zx p fun f => ?_
                  simp only [adj, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
                  exact ⟨fun ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ => ⟨h1, h2⟩,
                    fun ⟨h1, h2⟩ => ⟨⟨hne1, v1, h1⟩, ⟨hne2, v0, h2⟩⟩⟩
                rw [v3, yb ({e₁, e₂} : Finset _) p (fun _ => true),
                  prod_pair v4]
                simp [z9, sq]
            _ = (W.card : ℝ) * p ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ = ((V.card : ℝ) ^ 2) * (W.card : ℝ) * p ^ 2 := by
        simp [sum_const, nsmul_eq_mul]; ring
lemma z12 {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S_rev : Finset (z6 n)) (V E : Finset (Fin n))
    (hdisj_VE : Disjoint V E) (hdisj_S : Disjoint S_rev (z8 V E)) :
    let adj : ({e : z6 n // e ∉ S_rev} → Bool) → Fin n → Fin n → Prop :=
      fun f u v => ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S_rev), f ⟨z7 u v h, hmem⟩ = true
    z4 p (fun f : {e : z6 n // e ∉ S_rev} → Bool =>
      ∃ v ∈ V, ∃ z ∈ E, adj f v z) ≤
      (V.card : ℝ) * (E.card : ℝ) * p := by
  classical
  let adj : ({e : z6 n // e ∉ S_rev} → Bool) → Fin n → Fin n → Prop :=
    fun f u v => ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S_rev), f ⟨z7 u v h, hmem⟩ = true
  calc z4 p (fun f => ∃ v ∈ V, ∃ z ∈ E, adj f v z)
      ≤ ∑ v ∈ V, z4 p (fun f => ∃ z ∈ E, adj f v z) := y3 hp0 hp1 V _
    _ ≤ ∑ v ∈ V, ∑ z ∈ E, z4 p (fun f => adj f v z) :=
        sum_le_sum fun v _ => y3 hp0 hp1 E _
    _ ≤ ∑ _v ∈ V, ∑ _z ∈ E, p := by
        refine sum_le_sum fun v hv => sum_le_sum fun z hz => ?_
        have hne : v ≠ z := fun h => disjoint_left.mp hdisj_VE hv (h ▸ hz)
        have hnot : z7 v z hne ∉ S_rev := disjoint_right.mp hdisj_S
          ((z5 V E hne).mpr (Or.inl ⟨hv, hz⟩))
        let e₀ : {e : z6 n // e ∉ S_rev} := ⟨z7 v z hne, hnot⟩
        have v0 : z4 p (fun f => adj f v z) =
            z4 p (fun f : {e // e ∉ S_rev} → Bool => ∀ e ∈ ({e₀} : Finset _), f e = true) := by
          refine zx p fun f => ?_
          simp only [adj, mem_singleton, forall_eq]
          exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hne, hnot, h⟩⟩
        rw [v0, yb ({e₀} : Finset _) p (fun _ => true), prod_singleton]
        simp [z9]
    _ = (V.card : ℝ) * (E.card : ℝ) * p := by
        simp [sum_const, nsmul_eq_mul]; ring
lemma z0t (q m : ℕ) (hlp : LargeParams q m)
    (S_rev : Finset (z6 (nOf q m)))
    (v : Fin (nOf q m)) (Bc' Bc'0 : Finset (Fin (nOf q m)))
    (hBc'0_sub : Bc'0 ⊆ Bc') (hv_not : v ∉ Bc')
    (hBc'_hi : (Bc'.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc'0_lo : (ROf m : ℝ) / 4 ≤ (Bc'0.card : ℝ))
    (hdisj_S : Disjoint S_rev (z8 {v} Bc')) :
    let p : ℝ := ((ROf m : ℝ))⁻¹
    let adj : ({e : z6 (nOf q m) // e ∉ S_rev} → Bool) → Fin (nOf q m) → Fin (nOf q m) → Prop :=
      fun f u w => ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S_rev), f ⟨z7 u w h, hmem⟩ = true
    QOf m ≤ z4 p (fun f : {e : z6 (nOf q m) // e ∉ S_rev} → Bool =>
      (Bc'.filter (fun z => adj f v z)).card = m ∧ Bc'.filter (fun z => adj f v z) ⊆ Bc'0) := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set p : ℝ := (R : ℝ)⁻¹
  have v4 : R8 ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have vb : 10000 ≤ R := le_trans hlp.hR8_ge v4
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have v2 : 0 < m := by have := hlp.hm; omega
  let s : ℕ := Bc'0.card / m
  have hms : m * s ≤ Bc'0.card := Nat.mul_div_le Bc'0.card m
  obtain ⟨C, hC_sub, hC_card, hC_disj⟩ := z0e Bc'0 m s hms
  let v0 : ℝ := (5 * (m : ℝ))⁻¹
  have va : ∀ i ∈ (univ : Finset (Fin m)), v0 * (R : ℝ) ≤ ((C i).card : ℝ) := by
    intro i _
    rw [hC_card i]
    have hdiv : Bc'0.card ≤ m * s + m := by
      have hlt := Nat.lt_div_mul_add v2 (a := Bc'0.card)
      rw [mul_comm] at hlt
      change Bc'0.card ≤ m * (Bc'0.card / m) + m
      omega
    have hc : (Bc'0.card : ℝ) ≤ (m : ℝ) * (s : ℝ) + (m : ℝ) := by exact_mod_cast hdiv
    have v3 : (m : ℝ) ≤ (R8 : ℝ) := by
      have hmT : m ≤ T := y9 m (by have := hlp.hm; omega)
      have v8 : T ≤ EOf m := Nat.le_self_pow (by norm_num) T
      exact_mod_cast le_trans (le_trans hmT v8) (Nat.le_of_lt Nat.lt_two_pow_self)
    have v1 : 20 * (R8 : ℝ) ≤ (R : ℝ) := by
      have vc : (R : ℝ) = (R8 : ℝ) ^ 8 := by exact_mod_cast zq m
      have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
      have hpow : (R8 : ℝ) ^ 2 ≤ (R8 : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
      rw [vc]; nlinarith only [hR8_ge, hpow]
    have ve : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr v2
    rw [show v0 = (5 * (m : ℝ))⁻¹ from rfl, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    nlinarith only [hBc'0_lo, hc, v3, v1]
  have hEO := yo vb S_rev v Bc' hv_not hBc'_hi hdisj_S
    (univ : Finset (Fin m)) C (fun i _ => (hC_sub i).trans hBc'0_sub) hC_disj
    (by positivity : 0 ≤ v0) va
  have vd : QOf m ≤ v0 ^ (univ : Finset (Fin m)).card * exp (-4 : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    have v9 : exp (-5 * (m : ℝ)) ≤ v0 := by
      dsimp only [v0]
      have h1 : 5 * (m : ℝ) ≤ exp (5 * (m : ℝ)) := by linarith [Real.add_one_le_exp (5 * (m : ℝ))]
      rw [show -5 * (m : ℝ) = -(5 * (m : ℝ)) by ring, exp_neg]
      exact inv_anti₀ (by positivity) h1
    have h1 : QOf m ≤ exp ((m : ℝ) * (-5 * (m : ℝ)) - 4) := by
      unfold QOf
      refine exp_le_exp.mpr ?_
      have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast z03 (m - 1)
      have hmT : (m : ℝ) ≤ (T : ℝ) := by exact_mod_cast y9 m (by have := hlp.hm; omega)
      have hm10 : (10 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlp.hm
      nlinarith only [hT1, hmT, hm10]
    calc QOf m ≤ exp ((m : ℝ) * (-5 * (m : ℝ)) - 4) := h1
      _ = exp ((m : ℝ) * (-5 * (m : ℝ))) * exp (-4 : ℝ) := by rw [← exp_add]; rfl
      _ = (exp (-5 * (m : ℝ))) ^ m * exp (-4 : ℝ) := by rw [exp_nat_mul]
      _ ≤ v0 ^ m * exp (-4 : ℝ) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (exp_pos _).le v9 m) (exp_pos _).le
  refine vd.trans (hEO.trans (zi hp0 hp1 fun f ⟨hexact, hzero⟩ => ?_))
  let adj : Fin (nOf q m) → Prop := fun z =>
    ∃ (h : v ≠ z) (hmem : z7 v z h ∉ S_rev), f ⟨z7 v z h, hmem⟩ = true
  have v5 : Bc'.filter adj ⊆ (univ : Finset (Fin m)).biUnion (fun i => (C i).filter adj) := by
    intro z hz
    rcases mem_filter.mp hz with ⟨hzBc', hadj⟩
    by_contra hnot
    have v6 : z ∉ (univ : Finset (Fin m)).biUnion C := by
      intro hmem; rcases mem_biUnion.mp hmem with ⟨i, hi, hzC⟩
      exact hnot (mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨hzC, hadj⟩⟩)
    exact hzero z (mem_sdiff.mpr ⟨hzBc', v6⟩) hadj
  have v7 : (univ : Finset (Fin m)).biUnion (fun i => (C i).filter adj) ⊆ Bc'.filter adj :=
    biUnion_subset.mpr fun i _ => fun z hz =>
      mem_filter.mpr ⟨hBc'0_sub (hC_sub i (mem_filter.mp hz).1), (mem_filter.mp hz).2⟩
  have heq : Bc'.filter adj = (univ : Finset (Fin m)).biUnion (fun i => (C i).filter adj) :=
    Subset.antisymm v5 v7
  refine ⟨?_, ?_⟩
  · rw [heq, card_biUnion]
    · rw [sum_congr rfl fun i hi => hexact i hi, sum_const, smul_eq_mul, mul_one,
        Finset.card_univ, Fintype.card_fin]
    · intro i _ j _ hne
      exact (hC_disj (mem_coe.mpr (mem_univ i))
        (mem_coe.mpr (mem_univ j)) hne).mono
        (filter_subset _ _) (filter_subset _ _)
  · rw [heq]
    exact biUnion_subset.mpr fun i _ => (filter_subset _ _).trans (hC_sub i)
lemma z0o (q m : ℕ) (hlp : LargeParams q m)
    (S_rev : Finset (z6 (nOf q m)))
    (V02 Bc0 : Finset (Fin (nOf q m)))
    (hdisj_VB : Disjoint V02 Bc0) (hdisj_S : Disjoint S_rev (z8 V02 Bc0))
    (hV_card : V02.card = 2 * R4Of m)
    (hB_lo : (ROf m : ℝ) / 4 ≤ (Bc0.card : ℝ))
    (hB_hi : (Bc0.card : ℝ) ≤ 2 * (ROf m : ℝ)) :
    let p : ℝ := ((ROf m : ℝ))⁻¹
    let adj : ({e : z6 (nOf q m) // e ∉ S_rev} → Bool) → Fin (nOf q m) → Fin (nOf q m) → Prop :=
      fun f u w => ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S_rev), f ⟨z7 u w h, hmem⟩ = true
    z4 p (fun f : {e : z6 (nOf q m) // e ∉ S_rev} → Bool =>
      ((Bc0.filter (fun u => ∀ v ∈ V02, ¬ adj f u v)).card : ℝ) < (ROf m : ℝ) / 5) ≤ 1 / 256 := by
  classical
  set R := ROf m
  set R4 := R4Of m
  set R8 := R8Of m
  set p : ℝ := (R : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  let adj : ({e : z6 (nOf q m) // e ∉ S_rev} → Bool) → Fin (nOf q m) → Fin (nOf q m) → Prop :=
    fun f u w => ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S_rev), f ⟨z7 u w h, hmem⟩ = true
  let v0 : Finset {e : z6 (nOf q m) // e ∉ S_rev} :=
    (V02 ×ˢ Bc0).attach.image (fun (x : {p // p ∈ V02 ×ˢ Bc0}) =>
      have hne : x.1.1 ≠ x.1.2 := fun h =>
        disjoint_left.mp hdisj_VB (mem_product.mp x.2).1 (h ▸ (mem_product.mp x.2).2)
      ⟨z7 x.1.1 x.1.2 hne, disjoint_right.mp hdisj_S
        ((z5 V02 Bc0 hne).mpr (Or.inl (mem_product.mp x.2)))⟩)
  have v3 : v0.card = V02.card * Bc0.card := by
    rw [Finset.card_image_of_injective]
    · rw [card_attach, card_product]
    · intro x y heq
      rcases zv heq with ⟨h1, h2⟩ | ⟨h1, _⟩
      · exact Subtype.ext (Prod.ext h1 h2)
      · exact False.elim (disjoint_left.mp hdisj_VB (mem_product.mp x.2).1
          (h1 ▸ (mem_product.mp y.2).2))
  have v4 : ∀ f : {e // e ∉ S_rev} → Bool,
      (Bc0.filter (fun u => ∃ v ∈ V02, adj f u v)).card ≤ (v0.filter (fun e => f e = true)).card := by
    intro f
    have hmap : ∀ u ∈ Bc0.filter (fun u => ∃ v ∈ V02, adj f u v),
        ∃ e ∈ v0.filter (fun e => f e = true),
          ∃ v ∈ V02, ∃ (h : v ≠ u) (hnot : z7 v u h ∉ S_rev), e = ⟨z7 v u h, hnot⟩ := by
      intro u hu
      rcases (mem_filter.mp hu) with ⟨huB, v, hvV, hne, hnot, hf⟩
      have hne' : v ≠ u := hne.symm
      have hnot' : z7 v u hne' ∉ S_rev := by rwa [z0u] at hnot
      have hf' : f ⟨z7 v u hne', hnot'⟩ = true := by
        convert hf using 2; exact Subtype.ext (z0u hne).symm
      refine ⟨⟨z7 v u hne', hnot'⟩, mem_filter.mpr ⟨?_, hf'⟩, v, hvV, hne', hnot', rfl⟩
      exact mem_image.mpr ⟨⟨(v, u), mem_product.mpr ⟨hvV, huB⟩⟩, mem_attach _ _, rfl⟩
    choose g hg_mem hg_spec using hmap
    rw [← card_attach (s := Bc0.filter (fun u => ∃ v ∈ V02, adj f u v))]
    refine card_le_card_of_injOn (fun u => g u.1 u.2)
      (fun u _ => hg_mem u.1 u.2) ?_
    intro u₁ _ u₂ _ heq
    dsimp only at heq
    rcases hg_spec u₁.1 u₁.2 with ⟨v₁, hv₁, hne1, hnot1, hg1⟩
    rcases hg_spec u₂.1 u₂.2 with ⟨v₂, hv₂, hne2, hnot2, hg2⟩
    rw [hg1, hg2] at heq
    rcases zv heq with ⟨_, hu⟩ | ⟨hv, _⟩
    · exact Subtype.ext hu
    · exact False.elim (disjoint_left.mp hdisj_VB hv₁ (hv ▸ (mem_filter.mp u₂.2).1))
  have v9 : z4 p (fun f : {e // e ∉ S_rev} → Bool =>
        ((Bc0.filter (fun u => ∀ v ∈ V02, ¬ adj f u v)).card : ℝ) < (R : ℝ) / 5) ≤
      z4 p (fun f : {e // e ∉ S_rev} → Bool =>
        2 * ((v0.card : ℝ) * p) < ((v0.filter (fun e => f e = true)).card : ℝ)) := by
    refine zi hp0 hp1 fun f hlt => ?_
    have v8 : (Bc0.filter (fun u => ∀ v ∈ V02, ¬ adj f u v)).card +
        (Bc0.filter (fun u => ∃ v ∈ V02, adj f u v)).card = Bc0.card := by
      have hnot : Bc0.filter (fun u => ∃ v ∈ V02, adj f u v) =
          Bc0.filter (fun u => ¬ ∀ v ∈ V02, ¬ adj f u v) :=
        filter_congr fun _ _ => by simp
      rw [hnot, ← card_union_of_disjoint (disjoint_filter.mpr fun _ _ h1 h2 => h2 h1),
        filter_union_filter_not_eq]
    have h1 : (Bc0.card : ℝ) - ((Bc0.filter (fun u => ∀ v ∈ V02, ¬ adj f u v)).card : ℝ) ≤
        ((v0.filter (fun e => f e = true)).card : ℝ) := by
      have hc1 : ((Bc0.filter (fun u => ∀ v ∈ V02, ¬ adj f u v)).card : ℝ) +
          ((Bc0.filter (fun u => ∃ v ∈ V02, adj f u v)).card : ℝ) = (Bc0.card : ℝ) := by exact_mod_cast v8
      have hc2 : ((Bc0.filter (fun u => ∃ v ∈ V02, adj f u v)).card : ℝ) ≤
          ((v0.filter (fun e => f e = true)).card : ℝ) := by exact_mod_cast v4 f
      linarith
    have vb : 2 * ((v0.card : ℝ) * p) ≤ 8 * (R4 : ℝ) := by
      have v1 : (v0.card : ℝ) = (2 * (R4 : ℝ)) * (Bc0.card : ℝ) := by
        rw [v3, hV_card]; push_cast; ring
      rw [v1]
      have v2 : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (R_pos m)
      have hmul : (Bc0.card : ℝ) * p ≤ 2 := by
        rw [show p = (R : ℝ)⁻¹ from rfl, ← div_eq_mul_inv, div_le_iff₀ v2]; linarith
      nlinarith only [hmul, Nat.cast_nonneg (α := ℝ) R4]
    have v7 : 8 * (R4 : ℝ) < (R : ℝ) / 20 := by
      have vc : (R : ℝ) = (R4 : ℝ) ^ 4 := by exact_mod_cast wz m
      have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
      have v5 : (10000 : ℝ) ≤ (R4 : ℝ) := by
        have : (R4 : ℝ) = (R8 : ℝ) ^ 2 := by exact_mod_cast z1r m
        rw [this]; nlinarith only [hR8_ge]
      have hpow : (R4 : ℝ) ^ 2 ≤ (R4 : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      rw [vc]; nlinarith only [v5, hpow]
    linarith
  refine v9.trans ((z1a hp0 hp1 v0).trans ?_)
  have va : (R4 : ℝ) / 2 ≤ (v0.card : ℝ) * p := by
    have v1 : (v0.card : ℝ) = (2 * (R4 : ℝ)) * (Bc0.card : ℝ) := by
      rw [v3, hV_card]; push_cast; ring
    rw [v1]
    have v2 : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (R_pos m)
    have hmul : (1 / 4 : ℝ) ≤ (Bc0.card : ℝ) * p := by
      rw [show p = (R : ℝ)⁻¹ from rfl, ← div_eq_mul_inv, le_div_iff₀ v2]; linarith
    nlinarith only [hmul, Nat.cast_nonneg (α := ℝ) R4]
  have vd : (R8 : ℝ) ≤ (R4 : ℝ) / 6 := by
    have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
    have v6 : (R4 : ℝ) = (R8 : ℝ) ^ 2 := by exact_mod_cast z1r m
    rw [v6]; nlinarith only [hR8_ge]
  have hexp : exp (-((v0.card : ℝ) * p) / 3) ≤ exp (-((R8 : ℝ))) :=
    exp_le_exp.mpr (by linarith)
  exact hexp.trans (yi q m hlp).2.2.1
private lemma z09 (q m : ℕ) (hlp : LargeParams q m)
    (S_rev : Finset (z6 (nOf q m)))
    (f₀ : {e : z6 (nOf q m) // e ∈ S_rev} → Bool)
    (V1 Bc0_clean A : Finset (Fin (nOf q m)))
    (hA_sub : A ⊆ Bc0_clean) (hA_card : A.card ≤ zd (m - 2))
    (hdisj_VB : Disjoint V1 Bc0_clean)
    (hdisj_S : Disjoint S_rev (z8 V1 Bc0_clean))
    (hV1_lo : (1 / 12 : ℝ) * ((ROf m : ℝ) ^ 2) ≤ (V1.card : ℝ))
    (hV1_hi : (V1.card : ℝ) ≤ 2 * ((ROf m : ℝ) ^ 2))
    (hB_lo : (ROf m : ℝ) / 5 ≤ (Bc0_clean.card : ℝ)) :
    z4 ((ROf m : ℝ)⁻¹) (fun f_rem : {e : z6 (nOf q m) // e ∉ S_rev} → Bool =>
      ¬ ∀ S ∈ A.powerset,
        ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (ROf m : ℝ) ≤
          (((Bc0_clean \ A).filter (fun u => ∀ z ∈ A,
            (∃ w ∈ V1, (z1 (z0 S_rev f₀ f_rem)).Adj w u ∧
              (z1 (z0 S_rev f₀ f_rem)).Adj w z) ↔ z ∈ S)).card : ℝ)) ≤
      ((2 : ℝ) ^ (zd (m - 1) + 2)) * exp (-((R8Of m : ℝ)) / 64) := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set Tprev := zd (m - 2)
  set p : ℝ := (R : ℝ)⁻¹
  have vi : R8 ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have vm : 10000 ≤ R := le_trans hlp.hR8_ge vi
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have vc : Tprev ≤ T := y6 (by have := hlp.hm; omega)
  have v6 : A.card ≤ T := le_trans hA_card vc
  have vh : T ≤ R8 := le_trans (Nat.le_self_pow (by norm_num) T) (Nat.le_of_lt Nat.lt_two_pow_self)
  have vg := yf q m hlp
  let U := Bc0_clean \ A
  have vr : (R : ℝ) / 6 ≤ (U.card : ℝ) := by
    have h1 : Bc0_clean.card ≤ U.card + A.card := by
      have hsd : U.card = Bc0_clean.card - A.card := by
        change (Bc0_clean \ A).card = Bc0_clean.card - A.card
        rw [card_sdiff, inter_eq_left.mpr hA_sub]
      have : A.card ≤ Bc0_clean.card := card_le_card hA_sub
      omega
    have hc : (Bc0_clean.card : ℝ) ≤ (U.card : ℝ) + (A.card : ℝ) := by exact_mod_cast h1
    have vt : (A.card : ℝ) ≤ (R : ℝ) / 30 := by
      have h1 : (A.card : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast le_trans v6 vh
      have vs : (R : ℝ) = (R8 : ℝ) ^ 8 := by exact_mod_cast zq m
      have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
      have hpow : (R8 : ℝ) ^ 2 ≤ (R8 : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
      rw [vs]; nlinarith only [h1, hR8_ge, hpow]
    linarith
  have v0 : Disjoint V1 A := hdisj_VB.mono_right hA_sub
  have v9 : Disjoint S_rev (z8 V1 A) := by
    refine hdisj_S.mono_right fun ⟨e, he⟩ heVA => ?_
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
      change z7 u v huv ∈ z8 V1 Bc0_clean
      rw [z5 V1 Bc0_clean huv]
      rcases (z5 V1 A huv).mp heVA with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, hA_sub h2⟩
      · exact Or.inr ⟨h1, hA_sub h2⟩
  let S₁ : Finset (z6 (nOf q m)) := S_rev ∪ z8 V1 A
  let Good1 : (z6 (nOf q m) → Bool) → Prop := fun f =>
    (∀ z ∈ A, ((V1.filter (fun w => (z1 f).Adj w z)).card : ℝ) ≤ 4 * (R : ℝ)) ∧
    (∀ z ∈ A, (R : ℝ) / 48 ≤
      ((V1.filter (fun w => (z1 f).Adj w z ∧
        ∀ z' ∈ A, z' ≠ z → ¬ (z1 f).Adj w z')).card : ℝ))
  have vd : ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ S₁, f e = g e) → (Good1 f ↔ Good1 g) := by
    intro f g hfg
    have hadj : ∀ w ∈ V1, ∀ z ∈ A, (z1 f).Adj w z ↔ (z1 g).Adj w z := by
      intro w hw z hz
      have hne : w ≠ z := fun h => disjoint_left.mp v0 hw (h ▸ hz)
      rw [za f hne, za g hne,
        hfg _ (mem_union_right _ ((z5 V1 A hne).mpr (Or.inl ⟨hw, hz⟩)))]
    exact and_congr
      (forall₂_congr fun z hz => by rw [filter_congr fun w hw => hadj w hw z hz])
      (forall₂_congr fun z hz => by
        rw [filter_congr fun w hw =>
          and_congr (hadj w hw z hz)
            (forall₂_congr fun z' hz' => imp_congr_right fun _ => not_congr (hadj w hw z' hz'))])
  refine (zu hp0 hp1 S_rev S₁ subset_union_left f₀ Good1
    (fun f => ¬ ∀ S ∈ A.powerset,
      ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (R : ℝ) ≤
        ((U.filter (fun u => ∀ z ∈ A,
          (∃ w ∈ V1, (z1 f).Adj w u ∧ (z1 f).Adj w z) ↔ z ∈ S)).card : ℝ))
    vd
    (ε₁ := 2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200))
    (ε₂ := ((2 : ℝ) ^ A.card) * exp (-((R8 : ℝ)) / 64))
    (by positivity) ?_ ?_).trans ?_
  · have vl : 4 * (A.card : ℝ) ≤ (R : ℝ) := by
      have h4R8 : 4 * R8 ≤ R := by
        have hpow : R8 ^ 2 ≤ R8 ^ 8 := Nat.pow_le_pow_right (z1e m) (by norm_num)
        have hreq : R = R8 ^ 8 := zq m
        have hge := hlp.hR8_ge
        nlinarith only [hpow, hreq, hge]
      exact_mod_cast (show 4 * A.card ≤ R by omega)
    have vo : z4 p (fun f_rem : {e // e ∉ S_rev} → Bool => ¬ Good1 (z0 S_rev f₀ f_rem)) =
        z4 p (fun f_rem : {e // e ∉ S_rev} → Bool =>
          ¬ ((∀ z ∈ A, ((V1.filter (fun w =>
                ∃ (h : w ≠ z) (hmem : z7 w z h ∉ S_rev), f_rem ⟨z7 w z h, hmem⟩ = true)).card : ℝ) ≤
              4 * (R : ℝ)) ∧
             (∀ z ∈ A, (R : ℝ) / 48 ≤
               ((V1.filter (fun w =>
                 (∃ (h : w ≠ z) (hmem : z7 w z h ∉ S_rev), f_rem ⟨z7 w z h, hmem⟩ = true) ∧
                 ∀ z' ∈ A, z' ≠ z →
                   ¬ ∃ (h : w ≠ z') (hmem : z7 w z' h ∉ S_rev),
                     f_rem ⟨z7 w z' h, hmem⟩ = true)).card : ℝ)))) := by
      refine zx p fun f_rem => not_congr ?_
      have hadj : ∀ w ∈ V1, ∀ z ∈ A,
          (z1 (z0 S_rev f₀ f_rem)).Adj w z ↔
          ∃ (h : w ≠ z) (hmem : z7 w z h ∉ S_rev), f_rem ⟨z7 w z h, hmem⟩ = true := by
        intro w hw z hz
        have hne : w ≠ z := fun h => disjoint_left.mp v0 hw (h ▸ hz)
        have hnot : z7 w z hne ∉ S_rev :=
          disjoint_right.mp v9 ((z5 V1 A hne).mpr (Or.inl ⟨hw, hz⟩))
        exact zb S_rev f₀ f_rem hne hnot
      exact and_congr
        (forall₂_congr fun z hz => by rw [filter_congr fun w hw => hadj w hw z hz])
        (forall₂_congr fun z hz => by
          rw [filter_congr fun w hw =>
            and_congr (hadj w hw z hz)
              (forall₂_congr fun z' hz' => imp_congr_right fun _ => not_congr (hadj w hw z' hz'))])
    rw [vo]
    exact yk vm S_rev V1 V1 A (Subset.refl _)
      v0 v9 hV1_lo hV1_hi vl
  · intro f₁ _ hGood1
    let G₁ := z1 (z0 S₁ f₁ (fun _ => false))
    rcases hGood1 (fun _ => false) with ⟨hW_hi, hW_only_lo⟩
    let W_z : Fin (nOf q m) → Finset (Fin (nOf q m)) := fun z => V1.filter (fun w => G₁.Adj w z)
    let vq : Fin (nOf q m) → Finset (Fin (nOf q m)) := fun z =>
      V1.filter (fun w => G₁.Adj w z ∧ ∀ z' ∈ A, z' ≠ z → ¬ G₁.Adj w z')
    let v2 : Finset (Fin (nOf q m)) := A.biUnion W_z
    have v1 : v2 ⊆ V1 := biUnion_subset.mpr fun _ _ => filter_subset _ _
    have ve : (v2.card : ℝ) ≤ 4 * (A.card : ℝ) * (R : ℝ) := by
      have h1 : (v2.card : ℝ) ≤ ∑ z ∈ A, ((W_z z).card : ℝ) := by exact_mod_cast card_biUnion_le
      calc (v2.card : ℝ) ≤ ∑ z ∈ A, ((W_z z).card : ℝ) := h1
        _ ≤ ∑ _z ∈ A, (4 * (R : ℝ)) := sum_le_sum fun z hz => hW_hi z hz
        _ = 4 * (A.card : ℝ) * (R : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
    have v8 : Disjoint U v2 :=
      (hdisj_VB.symm.mono_left sdiff_subset).mono_right v1
    have v4 : Disjoint S₁ (z8 U v2) := by
      rw [disjoint_union_left]
      refine ⟨?_, ?_⟩
      · refine hdisj_S.mono_right fun ⟨e, he⟩ heUW => ?_
        induction e using Sym2.ind with
        | _ u v =>
          have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
          change z7 u v huv ∈ z8 V1 Bc0_clean
          rw [z5 V1 Bc0_clean huv]
          rcases (z5 U v2 huv).mp heUW with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr ⟨v1 h2, sdiff_subset h1⟩
          · exact Or.inl ⟨v1 h2, sdiff_subset h1⟩
      · rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
        induction e using Sym2.ind with
        | _ u v =>
          have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
          rcases (z5 V1 A huv).mp he1 with ⟨_, hvA⟩ | ⟨_, huA⟩ <;>
            rcases (z5 U v2 huv).mp he2 with ⟨huU, hvW⟩ | ⟨hvU, huW⟩
          · exact disjoint_left.mp v0 (v1 hvW) hvA
          · exact (mem_sdiff.mp hvU).2 hvA
          · exact (mem_sdiff.mp huU).2 huA
          · exact disjoint_left.mp v0 (v1 huW) huA
    have vn : z4 p (fun f₂ : {e // e ∉ S₁} → Bool =>
          ¬ ∀ S ∈ A.powerset,
            ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (R : ℝ) ≤
              ((U.filter (fun u => ∀ z ∈ A,
                (∃ w ∈ V1, (z1 (z0 S₁ f₁ f₂)).Adj w u ∧
                  (z1 (z0 S₁ f₁ f₂)).Adj w z) ↔ z ∈ S)).card : ℝ)) ≤
        z4 p (fun f₂ : {e // e ∉ S₁} → Bool =>
          ∃ S ∈ A.powerset,
            ((U.filter (fun u => ∀ z ∈ A,
              (∃ w ∈ W_z z, ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S₁),
                f₂ ⟨z7 u w h, hmem⟩ = true) ↔ z ∈ S)).card : ℝ) <
              (1 / 2) * ((U.card : ℝ) * exp (-13 * (A.card : ℝ)))) := by
      refine zi hp0 hp1 fun f₂ hnot => ?_
      simp only [not_forall, not_le] at hnot
      rcases hnot with ⟨S, hS, hlt⟩
      refine ⟨S, hS, ?_⟩
      have hflt : U.filter (fun u => ∀ z ∈ A,
            (∃ w ∈ V1, (z1 (z0 S₁ f₁ f₂)).Adj w u ∧
              (z1 (z0 S₁ f₁ f₂)).Adj w z) ↔ z ∈ S) =
          U.filter (fun u => ∀ z ∈ A,
            (∃ w ∈ W_z z, ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S₁),
              f₂ ⟨z7 u w h, hmem⟩ = true) ↔ z ∈ S) := by
        refine filter_congr fun u hu => forall₂_congr fun z hz => iff_congr ?_ Iff.rfl
        constructor
        · rintro ⟨w, hwV, hwu, hwz⟩
          have v3 : w ≠ z := fun h => disjoint_left.mp v0 hwV (h ▸ hz)
          have vb : z7 w z v3 ∈ S₁ :=
            mem_union_right _ ((z5 V1 A v3).mpr (Or.inl ⟨hwV, hz⟩))
          have hwz1 : G₁.Adj w z := by
            rw [zf S₁ f₁ (fun _ => false) v3 vb]
            exact (zf S₁ f₁ f₂ v3 vb).mp hwz
          have hwWz : w ∈ W_z z := mem_filter.mpr ⟨hwV, hwz1⟩
          have v7 : w ∈ v2 := mem_biUnion.mpr ⟨z, hz, hwWz⟩
          have v5 : u ≠ w := fun h => disjoint_left.mp v8 hu (h ▸ v7)
          have vf : z7 u w v5 ∉ S₁ :=
            disjoint_right.mp v4 ((z5 U v2 v5).mpr (Or.inl ⟨hu, v7⟩))
          exact ⟨w, hwWz, (zb S₁ f₁ f₂ v5 vf).mp hwu.symm⟩
        · rintro ⟨w, hwWz, hrem⟩
          have hwV : w ∈ V1 := (mem_filter.mp hwWz).1
          have v7 : w ∈ v2 := mem_biUnion.mpr ⟨z, hz, hwWz⟩
          have v5 : u ≠ w := fun h => disjoint_left.mp v8 hu (h ▸ v7)
          have vf : z7 u w v5 ∉ S₁ :=
            disjoint_right.mp v4 ((z5 U v2 v5).mpr (Or.inl ⟨hu, v7⟩))
          have hwu : (z1 (z0 S₁ f₁ f₂)).Adj w u :=
            ((zb S₁ f₁ f₂ v5 vf).mpr hrem).symm
          have v3 : w ≠ z := fun h => disjoint_left.mp v0 hwV (h ▸ hz)
          have vb : z7 w z v3 ∈ S₁ :=
            mem_union_right _ ((z5 V1 A v3).mpr (Or.inl ⟨hwV, hz⟩))
          have hwz : (z1 (z0 S₁ f₁ f₂)).Adj w z := by
            rw [zf S₁ f₁ f₂ v3 vb]
            exact (zf S₁ f₁ (fun _ => false) v3 vb).mp (mem_filter.mp hwWz).2
          exact ⟨w, hwV, hwu, hwz⟩
      rw [← hflt]
      have va : 0 ≤ exp (-13 * (A.card : ℝ)) := (exp_pos _).le
      nlinarith only [hlt, vr, va]
    have vj := yj vm S₁ A v2 U vq W_z
      ve
      (fun z _ => fun w hw => mem_filter.mpr ⟨(mem_filter.mp hw).1,
        (mem_filter.mp hw).2.1⟩)
      (fun z hz => fun w hw => mem_biUnion.mpr ⟨z, hz, hw⟩)
      hW_only_lo
      (fun z₁ _ z₂ hz₂ hne => by
        rw [disjoint_left]; intro w hw1 hw2
        exact (mem_filter.mp hw1).2.2 z₂ hz₂ hne.symm (mem_filter.mp hw2).2)
      v8 v4
    have vk : exp (-((U.card : ℝ) * exp (-13 * (A.card : ℝ))) / 8) ≤
        exp (-((R8 : ℝ)) / 64) := by
      have hAT : (A.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast v6
      have h1 : exp (-13 * (T : ℝ)) ≤ exp (-13 * (A.card : ℝ)) :=
        exp_le_exp.mpr (by linarith)
      have h2 : ((R : ℝ) / 8) * exp (-13 * (T : ℝ)) ≤
          (U.card : ℝ) * exp (-13 * (A.card : ℝ)) :=
        mul_le_mul (by linarith) h1 (exp_pos _).le (Nat.cast_nonneg _)
      exact (exp_le_exp.mpr (by linarith)).trans vg.2.2.1
    exact (vn.trans vj).trans (mul_le_mul_of_nonneg_left vk (pow_nonneg (by norm_num) _))
  · have hAT : (A.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast v6
    have h1 : 2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200) ≤
        2 * (T : ℝ) * exp (-((R8 : ℝ)) / 64) := by
      calc 2 * (A.card : ℝ) * exp (-((R : ℝ)) / 200)
          ≤ 2 * (T : ℝ) * exp (-((R : ℝ)) / 200) := by
            have := exp_pos (-((R : ℝ)) / 200); nlinarith
        _ ≤ 2 * (T : ℝ) * exp (-((R8 : ℝ)) / 64) :=
            mul_le_mul_of_nonneg_left vg.1 (by positivity)
    have h2 : ((2 : ℝ) ^ A.card) * exp (-((R8 : ℝ)) / 64) ≤
        ((2 : ℝ) ^ T) * exp (-((R8 : ℝ)) / 64) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) v6) (exp_pos _).le
    have vp : 2 * (T : ℝ) + (2 : ℝ) ^ T ≤ (2 : ℝ) ^ (T + 2) := by
      have hlt : (T : ℝ) ≤ (2 : ℝ) ^ T := by exact_mod_cast Nat.le_of_lt Nat.lt_two_pow_self
      rw [pow_add]; norm_num; linarith
    have va : 0 ≤ exp (-((R8 : ℝ)) / 64) := (exp_pos _).le
    nlinarith only [h1, h2, vp, va]
lemma z0c (q m : ℕ) (hlp : LargeParams q m)
    (S_rev : Finset (z6 (nOf q m)))
    (f₀ : {e : z6 (nOf q m) // e ∈ S_rev} → Bool)
    (V1 Bc0_clean : Finset (Fin (nOf q m)))
    (hdisj_VB : Disjoint V1 Bc0_clean)
    (hdisj_S : Disjoint S_rev (z8 V1 Bc0_clean))
    (hV1_lo : (1 / 12 : ℝ) * ((ROf m : ℝ) ^ 2) ≤ (V1.card : ℝ))
    (hV1_hi : (V1.card : ℝ) ≤ 2 * ((ROf m : ℝ) ^ 2))
    (hB_lo : (ROf m : ℝ) / 5 ≤ (Bc0_clean.card : ℝ))
    (hB_hi : (Bc0_clean.card : ℝ) ≤ 2 * (ROf m : ℝ)) :
    z4 ((ROf m : ℝ)⁻¹) (fun f_rem : {e : z6 (nOf q m) // e ∉ S_rev} → Bool =>
      ¬ ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
        ∀ S ∈ A.powerset,
          ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (ROf m : ℝ) ≤
            (((Bc0_clean \ A).filter (fun u => ∀ z ∈ A,
              (∃ w ∈ V1, (z1 (z0 S_rev f₀ f_rem)).Adj w u ∧
                (z1 (z0 S_rev f₀ f_rem)).Adj w z) ↔ z ∈ S)).card : ℝ)) ≤ 1 / 256 := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set Tprev := zd (m - 2)
  set p : ℝ := (R : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  let Fam := Bc0_clean.powerset.filter (fun A => A.card ≤ Tprev)
  have v0 : (Fam.card : ℝ) ≤ (2 * (R : ℝ) + 1) ^ (T + 1) := by
    have v1 : Fam ⊆ (range (Tprev + 1)).biUnion (fun k => Bc0_clean.powersetCard k) := by
      intro A hA
      rcases mem_filter.mp hA with ⟨hAp, hAc⟩
      exact mem_biUnion.mpr ⟨A.card, mem_range.mpr (by omega),
        mem_powersetCard.mpr ⟨mem_powerset.mp hAp, rfl⟩⟩
    have h1 : Fam.card ≤ ∑ k ∈ range (Tprev + 1), Bc0_clean.card.choose k := by
      calc Fam.card ≤ ((range (Tprev + 1)).biUnion (fun k => Bc0_clean.powersetCard k)).card :=
            card_le_card v1
        _ ≤ ∑ k ∈ range (Tprev + 1), (Bc0_clean.powersetCard k).card := card_biUnion_le
        _ = ∑ k ∈ range (Tprev + 1), Bc0_clean.card.choose k := by
            refine sum_congr rfl fun k _ => card_powersetCard k Bc0_clean
    have h2 : ∑ k ∈ range (Tprev + 1), Bc0_clean.card.choose k ≤
        (Tprev + 1) * (Bc0_clean.card + 1) ^ Tprev := by
      calc ∑ k ∈ range (Tprev + 1), Bc0_clean.card.choose k
          ≤ ∑ _k ∈ range (Tprev + 1), (Bc0_clean.card + 1) ^ Tprev := by
            refine sum_le_sum fun k hk => ?_
            have v8 : k ≤ Tprev := Nat.lt_succ_iff.mp (mem_range.mp hk)
            have v5 : Bc0_clean.card.choose k ≤ Bc0_clean.card ^ k := by
              have h1 : Bc0_clean.card.choose k ≤ k.factorial * Bc0_clean.card.choose k :=
                Nat.le_mul_of_pos_left _ (Nat.factorial_pos k)
              rw [← Nat.descFactorial_eq_factorial_mul_choose] at h1
              exact h1.trans (Nat.descFactorial_le_pow Bc0_clean.card k)
            calc Bc0_clean.card.choose k ≤ Bc0_clean.card ^ k := v5
              _ ≤ (Bc0_clean.card + 1) ^ k := Nat.pow_le_pow_left (by omega) k
              _ ≤ (Bc0_clean.card + 1) ^ Tprev := Nat.pow_le_pow_right (by omega) v8
        _ = (Tprev + 1) * (Bc0_clean.card + 1) ^ Tprev := by simp
    have v4 : Tprev ≤ Bc0_clean.card := by
      have h1 : Tprev ≤ T := y6 (by have := hlp.hm; omega)
      have h2 : T ≤ R8 := le_trans (Nat.le_self_pow (by norm_num) T) (Nat.le_of_lt Nat.lt_two_pow_self)
      have h3 : (R8 : ℝ) ≤ (R : ℝ) / 5 := by
        have v9 : (R : ℝ) = (R8 : ℝ) ^ 8 := by exact_mod_cast zq m
        have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
        have hpow : (R8 : ℝ) ^ 2 ≤ (R8 : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
        rw [v9]; nlinarith only [hR8_ge, hpow]
      have h4 : (Tprev : ℝ) ≤ (Bc0_clean.card : ℝ) := by
        have hTR : (Tprev : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast le_trans h1 h2
        linarith
      exact_mod_cast h4
    have h3 : Fam.card ≤ (Bc0_clean.card + 1) ^ (T + 1) := by
      have v3 : Tprev ≤ T := y6 (by have := hlp.hm; omega)
      calc Fam.card ≤ (Tprev + 1) * (Bc0_clean.card + 1) ^ Tprev := le_trans h1 h2
        _ ≤ (Bc0_clean.card + 1) * (Bc0_clean.card + 1) ^ Tprev := Nat.mul_le_mul_right _ (by omega)
        _ = (Bc0_clean.card + 1) ^ (Tprev + 1) := by rw [← _root_.pow_succ']
        _ ≤ (Bc0_clean.card + 1) ^ (T + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc (Fam.card : ℝ) ≤ ((Bc0_clean.card : ℝ) + 1) ^ (T + 1) := by exact_mod_cast h3
      _ ≤ (2 * (R : ℝ) + 1) ^ (T + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
  have v7 : z4 p (fun f_rem : {e // e ∉ S_rev} → Bool =>
        ¬ ∀ A ∈ Bc0_clean.powerset, A.card ≤ Tprev →
          ∀ S ∈ A.powerset,
            ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (R : ℝ) ≤
              (((Bc0_clean \ A).filter (fun u => ∀ z ∈ A,
                (∃ w ∈ V1, (z1 (z0 S_rev f₀ f_rem)).Adj w u ∧
                  (z1 (z0 S_rev f₀ f_rem)).Adj w z) ↔ z ∈ S)).card : ℝ)) ≤
      z4 p (fun f_rem : {e // e ∉ S_rev} → Bool =>
        ∃ A ∈ Fam, ¬ ∀ S ∈ A.powerset,
          ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (R : ℝ) ≤
            (((Bc0_clean \ A).filter (fun u => ∀ z ∈ A,
              (∃ w ∈ V1, (z1 (z0 S_rev f₀ f_rem)).Adj w u ∧
                (z1 (z0 S_rev f₀ f_rem)).Adj w z) ↔ z ∈ S)).card : ℝ)) := by
    refine zi hp0 hp1 fun f_rem hnot => ?_
    simp only [not_forall] at hnot
    rcases hnot with ⟨A, hAp, hAc, S, hS, hlt⟩
    exact ⟨A, mem_filter.mpr ⟨hAp, hAc⟩, fun hall => hlt (hall S hS)⟩
  calc z4 p (fun f_rem => _)
      ≤ ∑ A ∈ Fam, z4 p (fun f_rem : {e // e ∉ S_rev} → Bool =>
          ¬ ∀ S ∈ A.powerset,
            ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (R : ℝ) ≤
              (((Bc0_clean \ A).filter (fun u => ∀ z ∈ A,
                (∃ w ∈ V1, (z1 (z0 S_rev f₀ f_rem)).Adj w u ∧
                  (z1 (z0 S_rev f₀ f_rem)).Adj w z) ↔ z ∈ S)).card : ℝ)) :=
        v7.trans (y3 hp0 hp1 Fam _)
    _ ≤ ∑ _A ∈ Fam, (((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) :=
        sum_le_sum fun A hA =>
          z09 q m hlp S_rev f₀ V1 Bc0_clean A
            (mem_powerset.mp (mem_filter.mp hA).1)
            (mem_filter.mp hA).2 hdisj_VB hdisj_S hV1_lo hV1_hi hB_lo
    _ = (Fam.card : ℝ) * (((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((2 * (R : ℝ) + 1) ^ (T + 1)) * ((2 : ℝ) ^ (T + 10)) * exp (-((R8 : ℝ)) / 64) := by
        have v6 : (2 : ℝ) ^ (T + 2) ≤ (2 : ℝ) ^ (T + 10) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hmul := mul_le_mul v0 v6 (by positivity) (by positivity)
        have v2 : 0 ≤ exp (-((R8 : ℝ)) / 64) := (exp_pos _).le
        calc (Fam.card : ℝ) * (((2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64))
            = ((Fam.card : ℝ) * (2 : ℝ) ^ (T + 2)) * exp (-((R8 : ℝ)) / 64) := by ring
          _ ≤ (((2 * (R : ℝ) + 1) ^ (T + 1)) * (2 : ℝ) ^ (T + 10)) * exp (-((R8 : ℝ)) / 64) :=
              mul_le_mul_of_nonneg_right hmul v2
    _ ≤ 1 / 256 := hlp.hsubset_exp_R8
lemma z08 (q m : ℕ) (hlp : LargeParams q m)
    (S_rev : Finset (z6 (nOf q m)))
    (f_rev : {e : z6 (nOf q m) // e ∈ S_rev} → Bool)
    (x : Fin m → Fin (nOf q m)) (hx_inj : Function.Injective x)
    (B Bc0_clean : Finset (Fin (nOf q m)))
    (hBc0_sub : Bc0_clean ⊆ B)
    (hB_hi : (B.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc0_lo : (ROf m : ℝ) / 5 ≤ (Bc0_clean.card : ℝ))
    (hdisj_xB : ∀ i : Fin m, x i ∉ B)
    (hdisj_S : Disjoint S_rev (z8 (univ.image x) B))
    (Pool : Finset (Fin (nOf q m)) → Finset (Fin (nOf q m)) → Finset (Fin (nOf q m)))
    (hPool_sub : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      ∀ S ∈ A.powerset, Pool A S ⊆ Bc0_clean \ A)
    (hPool_disj : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      Set.PairwiseDisjoint (A.powerset : Set (Finset (Fin (nOf q m)))) (Pool A))
    (hPool_lo : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      ∀ S ∈ A.powerset, ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (ROf m : ℝ) ≤
        ((Pool A S).card : ℝ)) :
    let p : ℝ := ((ROf m : ℝ))⁻¹
    let N : (z6 (nOf q m) → Bool) → Fin m → Finset (Fin (nOf q m)) :=
      fun f i => B.filter (fun z => (z1 f).Adj (x i) z)
    QOf m ≤ z4 p (fun f_rem : {e : z6 (nOf q m) // e ∉ S_rev} → Bool =>
      let f := z0 S_rev f_rev f_rem
      ((Bc0_clean.filter (fun z => (z1 f).Adj (x ⟨0, by have := hlp.hm; omega⟩) z)).card = 1 ∧
       ∀ u ∈ B \ Bc0_clean, ¬ (z1 f).Adj (x ⟨0, by have := hlp.hm; omega⟩) u) ∧
      ∀ i : Fin (m - 1),
        let A := N f ⟨i.val, by omega⟩
        (∀ S ∈ A.powerset, ((Pool A S).filter (fun u => (z1 f).Adj (x ⟨i.val + 1, by omega⟩) u)).card = 1) ∧
        (∀ u ∈ B \ A.powerset.biUnion (Pool A), ¬ (z1 f).Adj (x ⟨i.val + 1, by omega⟩) u)) := by
  classical
  set R := ROf m
  set T := zd (m - 1)
  set p : ℝ := (R : ℝ)⁻¹
  have vj : R8Of m ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have vq : 10000 ≤ R := le_trans hlp.hR8_ge vj
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have v1 : 0 < m := by have := hlp.hm; omega
  let N : (z6 (nOf q m) → Bool) → Fin m → Finset (Fin (nOf q m)) :=
    fun f i => B.filter (fun z => (z1 f).Adj (x i) z)
  let BaseOk : (z6 (nOf q m) → Bool) → Prop := fun f =>
    (Bc0_clean.filter (fun z => (z1 f).Adj (x ⟨0, v1⟩) z)).card = 1 ∧
    ∀ u ∈ B \ Bc0_clean, ¬ (z1 f).Adj (x ⟨0, v1⟩) u
  let StepOk : ℕ → (z6 (nOf q m) → Bool) → Prop := fun j f =>
    ∀ (i : ℕ) (hi : i + 1 < j) (him : i + 1 < m),
      let A := N f ⟨i, by omega⟩
      (∀ S ∈ A.powerset, ((Pool A S).filter (fun u => (z1 f).Adj (x ⟨i + 1, him⟩) u)).card = 1) ∧
      (∀ u ∈ B \ A.powerset.biUnion (Pool A), ¬ (z1 f).Adj (x ⟨i + 1, him⟩) u)
  let ChainOk : ℕ → (z6 (nOf q m) → Bool) → Prop := fun j f => BaseOk f ∧ StepOk j f
  let PrefX : ℕ → Finset (Fin (nOf q m)) := fun j =>
    (univ.filter (fun i : Fin m => i.val < j)).image x
  let v0 : ℕ → Finset (z6 (nOf q m)) := fun j => S_rev ∪ z8 (PrefX j) B
  have v4 : ∀ (j : ℕ), 1 ≤ j → (hjm : j ≤ m) → ∀ f : z6 (nOf q m) → Bool,
      ChainOk j f → ∀ (i : ℕ) (hij : i < j),
        N f ⟨i, by omega⟩ ⊆ Bc0_clean ∧ (N f ⟨i, by omega⟩).card = zd i := by
    intro j hj1 hjm f ⟨hbase, hstep⟩ i
    induction i with
    | zero =>
      intro _
      have heq : N f ⟨0, v1⟩ = Bc0_clean.filter (fun z => (z1 f).Adj (x ⟨0, v1⟩) z) := by
        ext z; simp only [N, mem_filter]
        constructor
        · rintro ⟨hzB, hadj⟩
          by_contra hnot
          have vw : z ∉ Bc0_clean := fun h => hnot ⟨h, hadj⟩
          exact hbase.2 z (mem_sdiff.mpr ⟨hzB, vw⟩) hadj
        · rintro ⟨hzC, hadj⟩; exact ⟨hBc0_sub hzC, hadj⟩
      rw [heq]; exact ⟨filter_subset _ _, hbase.1⟩
    | succ k ih =>
      intro hkj
      have ⟨hsub_k, hcard_k⟩ := ih (by omega)
      have v7 : (N f ⟨k, by omega⟩).card ≤ zd (m - 2) := by
        rw [hcard_k]; exact y6 (by omega)
      have v8 : N f ⟨k, by omega⟩ ∈ Bc0_clean.powerset := mem_powerset.mpr hsub_k
      have hst := hstep k hkj (by omega)
      set A := N f ⟨k, by omega⟩
      let adj1 : Fin (nOf q m) → Prop := fun u => (z1 f).Adj (x ⟨k + 1, by omega⟩) u
      have heq : N f ⟨k + 1, by omega⟩ = A.powerset.biUnion (fun S => (Pool A S).filter adj1) := by
        ext u; simp only [N, mem_filter, mem_biUnion]
        constructor
        · rintro ⟨huB, hadj⟩
          by_contra hnot
          have ve : u ∉ A.powerset.biUnion (Pool A) := by
            intro hm; rcases mem_biUnion.mp hm with ⟨S, hS, huP⟩
            exact hnot ⟨S, hS, huP, hadj⟩
          exact hst.2 u (mem_sdiff.mpr ⟨huB, ve⟩) hadj
        · rintro ⟨S, hS, huP, hadj⟩
          exact ⟨hBc0_sub (sdiff_subset (hPool_sub A v8 v7 S hS huP)), hadj⟩
      rw [heq]
      refine ⟨biUnion_subset.mpr fun S hS =>
        (filter_subset _ _).trans ((hPool_sub A v8 v7 S hS).trans sdiff_subset), ?_⟩
      rw [card_biUnion]
      · rw [sum_congr rfl fun S hS => hst.1 S hS, sum_const, smul_eq_mul, mul_one,
          card_powerset, hcard_k]; rfl
      · intro S₁ hS₁ S₂ hS₂ hne
        exact (hPool_disj A v8 v7 hS₁ hS₂ hne).mono
          (filter_subset _ _) (filter_subset _ _)
  have v6 : ∀ (j : ℕ), 1 ≤ j → j ≤ m → ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ v0 j, f e = g e) → ChainOk j f → ChainOk j g := by
    intro j hj1 hjm f g hfg hCf
    have hadj : ∀ (i : Fin m), i.val < j → ∀ u ∈ B,
        (z1 f).Adj (x i) u ↔ (z1 g).Adj (x i) u := by
      intro i hi u hu
      have hne : x i ≠ u := fun h => hdisj_xB i (h ▸ hu)
      have vr : x i ∈ PrefX j := mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩
      rw [za f hne, za g hne,
        hfg _ (mem_union_right _ ((z5 (PrefX j) B hne).mpr (Or.inl ⟨vr, hu⟩)))]
    have hNeq : ∀ (i : Fin m), i.val < j → N f i = N g i := fun i hi => by
      ext z; simp only [N, mem_filter]; exact and_congr_right fun hz => hadj i hi z hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [filter_congr fun z hz => (hadj ⟨0, v1⟩ (by simp; omega) z (hBc0_sub hz)).symm]
      exact hCf.1.1
    · intro u hu
      rw [← hadj ⟨0, v1⟩ (by simp; omega) u (sdiff_subset hu)]
      exact hCf.1.2 u hu
    · intro i hi him
      have hAeq : N g ⟨i, by omega⟩ = N f ⟨i, by omega⟩ :=
        (hNeq ⟨i, by omega⟩ (by simp; omega)).symm
      have ⟨hsub_i, hcard_i⟩ := v4 j hj1 hjm f hCf i (by omega)
      have vn : N f ⟨i, by omega⟩ ∈ Bc0_clean.powerset := mem_powerset.mpr hsub_i
      have vk : (N f ⟨i, by omega⟩).card ≤ zd (m - 2) := by
        rw [hcard_i]; exact y6 (by omega)
      have hst := hCf.2 i hi him
      dsimp only; rw [hAeq]
      refine ⟨fun S hS => ?_, fun u hu => ?_⟩
      · rw [filter_congr fun u hu =>
          (hadj ⟨i + 1, him⟩ hi u (hBc0_sub (sdiff_subset (hPool_sub _ vn vk S hS hu)))).symm]
        exact hst.1 S hS
      · rw [← hadj ⟨i + 1, him⟩ hi u (sdiff_subset hu)]; exact hst.2 u hu
  have vb : ∀ (j : ℕ), 1 ≤ j → j ≤ m → ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ v0 j, f e = g e) → (ChainOk j f ↔ ChainOk j g) :=
    fun j hj1 hjm f g hfg => ⟨v6 j hj1 hjm f g hfg,
      v6 j hj1 hjm g f (fun e he => (hfg e he).symm)⟩
  have v5 : ∀ (i : Fin m), Disjoint (v0 i.val) (z8 {x i} B) := by
    intro i
    rw [disjoint_union_left]
    refine ⟨?_, ?_⟩
    · refine hdisj_S.mono_right fun ⟨e, he⟩ he1 => ?_
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        change z7 u v huv ∈ z8 (univ.image x) B
        rw [z5 (univ.image x) B huv]
        rcases (z5 {x i} B huv).mp he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨mem_singleton.mp h1 ▸ mem_image.mpr ⟨i, mem_univ _, rfl⟩, h2⟩
        · exact Or.inr ⟨mem_singleton.mp h1 ▸ mem_image.mpr ⟨i, mem_univ _, rfl⟩, h2⟩
    · rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        rcases (z5 (PrefX i.val) B huv).mp he1 with ⟨huP, hvB⟩ | ⟨hvP, huB⟩ <;>
          rcases (z5 {x i} B huv).mp he2 with ⟨hux, hvB'⟩ | ⟨hvx, huB'⟩
        · rcases mem_image.mp huP with ⟨k, hk, hxk⟩
          have hki : k = i := hx_inj (hxk.trans (mem_singleton.mp hux))
          have hklt : k.val < i.val := (mem_filter.mp hk).2
          rw [hki] at hklt; omega
        · exact hdisj_xB i (mem_singleton.mp hvx ▸ hvB)
        · exact hdisj_xB i (mem_singleton.mp hux ▸ huB)
        · rcases mem_image.mp hvP with ⟨k, hk, hxk⟩
          have hki : k = i := hx_inj (hxk.trans (mem_singleton.mp hvx))
          have hklt : k.val < i.val := (mem_filter.mp hk).2
          rw [hki] at hklt; omega
  let v2 : ℝ := exp (-17 * (T : ℝ) ^ 2 - 4)
  have vc : exp (-6 : ℝ) ≤
      z4 p (fun f_rem : {e // e ∉ S_rev} → Bool => ChainOk 1 (z0 S_rev f_rev f_rem)) := by
    have vh : Disjoint S_rev (z8 {x ⟨0, v1⟩} B) :=
      (v5 ⟨0, v1⟩).mono_left subset_union_left
    have hEO := yo vq S_rev (x ⟨0, v1⟩) B (hdisj_xB ⟨0, v1⟩) hB_hi vh
      (univ : Finset (Fin 1)) (fun _ => Bc0_clean) (fun _ _ => hBc0_sub)
      (fun a _ b _ hne => absurd (Subsingleton.elim a b) hne)
      (by norm_num : (0 : ℝ) ≤ 1 / 5) (fun _ _ => by linarith)
    have u4 : exp (-6 : ℝ) ≤ (1 / 5 : ℝ) ^ (univ : Finset (Fin 1)).card * exp (-4 : ℝ) := by
      simp only [Finset.card_univ, Fintype.card_fin, pow_one]
      have h5 : exp (-2 : ℝ) ≤ (1 / 5 : ℝ) := by
        have hsum := Real.sum_le_exp_of_nonneg (x := (2 : ℝ)) (by norm_num) 4
        simp [sum_range_succ, Nat.factorial] at hsum
        rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
        linarith
      calc exp (-6 : ℝ) = exp (-2 : ℝ) * exp (-4 : ℝ) := by rw [← exp_add]; congr 1; norm_num
        _ ≤ (1 / 5 : ℝ) * exp (-4 : ℝ) := mul_le_mul_of_nonneg_right h5 (exp_pos _).le
    refine u4.trans (hEO.trans (zi hp0 hp1 fun f_rem ⟨hex, hzr⟩ => ?_))
    have hadj : ∀ u ∈ B, (z1 (z0 S_rev f_rev f_rem)).Adj (x ⟨0, v1⟩) u ↔
        ∃ (h : x ⟨0, v1⟩ ≠ u) (hmem : z7 (x ⟨0, v1⟩) u h ∉ S_rev),
          f_rem ⟨z7 (x ⟨0, v1⟩) u h, hmem⟩ = true := by
      intro u hu
      have hne : x ⟨0, v1⟩ ≠ u := fun h => hdisj_xB _ (h ▸ hu)
      have hnot : z7 (x ⟨0, v1⟩) u hne ∉ S_rev := disjoint_right.mp vh
        ((z5 {x ⟨0, v1⟩} B hne).mpr (Or.inl ⟨mem_singleton_self _, hu⟩))
      exact zb S_rev f_rev f_rem hne hnot
    refine ⟨⟨?_, ?_⟩, fun i hi _ => by omega⟩
    · rw [← hex ⟨0, by norm_num⟩ (mem_univ _)]; congr 1
      exact filter_congr fun z hz => hadj z (hBc0_sub hz)
    · intro u hu
      have hbi : (univ : Finset (Fin 1)).biUnion (fun _ => Bc0_clean) = Bc0_clean := by simp
      rw [hadj u (sdiff_subset hu)]
      exact hzr u (by rwa [hbi])
  have hind : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      exp (-6 : ℝ) * v2 ^ (j - 1) ≤
        z4 p (fun f_rem : {e // e ∉ S_rev} → Bool => ChainOk j (z0 S_rev f_rev f_rem)) := by
    intro j hj1 hjm
    induction j with
    | zero => omega
    | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0; simpa using vc
      · have hk1 : 1 ≤ k := by omega
        have hkm : k ≤ m := by omega
        have vx := ih hk1 hkm
        let StepK : (z6 (nOf q m) → Bool) → Prop := fun f =>
          let A := N f ⟨k - 1, by omega⟩
          (∀ S ∈ A.powerset, ((Pool A S).filter (fun u => (z1 f).Adj (x ⟨k, by omega⟩) u)).card = 1) ∧
          (∀ u ∈ B \ A.powerset.biUnion (Pool A), ¬ (z1 f).Adj (x ⟨k, by omega⟩) u)
        have u1 : ∀ f₁ : {e // e ∈ v0 k} → Bool,
            (∀ e : {e // e ∈ S_rev}, f₁ ⟨e.1, subset_union_left e.2⟩ = f_rev e) →
            (∀ f₂ : {e // e ∉ v0 k} → Bool, ChainOk k (z0 (v0 k) f₁ f₂)) →
            v2 ≤ z4 p (fun f₂ : {e // e ∉ v0 k} → Bool =>
              StepK (z0 (v0 k) f₁ f₂)) := by
          intro f₁ _ hCk
          let G₁ := z1 (z0 (v0 k) f₁ (fun _ => false))
          have hCk0 := hCk (fun _ => false)
          let A := N (z0 (v0 k) f₁ (fun _ => false)) ⟨k - 1, by omega⟩
          have ⟨hA_sub, hA_card_eq⟩ := v4 k hk1 hkm _ hCk0 (k - 1) (by omega)
          have v9 : A ∈ Bc0_clean.powerset := mem_powerset.mpr hA_sub
          have v3 : A.card ≤ zd (m - 2) := by rw [hA_card_eq]; exact y6 (by omega)
          have vd : Disjoint (v0 k) (z8 {x ⟨k, by omega⟩} B) := v5 ⟨k, by omega⟩
          let va : ℝ := (1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))
          have hEO := yo vq (v0 k) (x ⟨k, by omega⟩) B
            (hdisj_xB ⟨k, by omega⟩) hB_hi vd A.powerset (Pool A)
            (fun S hS => (hPool_sub A v9 v3 S hS).trans (sdiff_subset.trans hBc0_sub))
            (hPool_disj A v9 v3) (by positivity : 0 ≤ va)
            (hPool_lo A v9 v3)
          have u2 : v2 ≤ va ^ A.powerset.card * exp (-4 : ℝ) := by
            have vs : exp (-13 * (A.card : ℝ) - 3) ≤ va := by
              dsimp only [va]
              have h12 : exp (-3 : ℝ) ≤ (1 / 12 : ℝ) := by
                have hsum := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 5
                simp [sum_range_succ, Nat.factorial] at hsum
                rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
                linarith
              calc exp (-13 * (A.card : ℝ) - 3)
                  = exp (-3 : ℝ) * exp (-13 * (A.card : ℝ)) := by rw [← exp_add]; congr 1; ring
                _ ≤ (1 / 12 : ℝ) * exp (-13 * (A.card : ℝ)) :=
                    mul_le_mul_of_nonneg_right h12 (exp_pos _).le
            have vf : A.powerset.card ≤ T := by
              rw [card_powerset, hA_card_eq]
              have : 2 ^ zd (k - 1) = zd k := by
                have vy : k = (k - 1) + 1 := by omega
                rw [vy]; rfl
              rw [this]; exact y6 (by omega)
            have vp : A.card ≤ T := le_trans v3 (y6 (by have := hlp.hm; omega))
            have h1 : v2 ≤ exp ((A.powerset.card : ℝ) * (-13 * (A.card : ℝ) - 3) - 4) := by
              dsimp only [v2]
              refine exp_le_exp.mpr ?_
              have hAT : (A.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast vp
              have hPT : (A.powerset.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast vf
              have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast z03 (m - 1)
              nlinarith only [hAT, hPT, hT1]
            calc v2 ≤ exp ((A.powerset.card : ℝ) * (-13 * (A.card : ℝ) - 3) - 4) := h1
              _ = exp ((A.powerset.card : ℝ) * (-13 * (A.card : ℝ) - 3)) * exp (-4 : ℝ) := by
                  rw [← exp_add]; rfl
              _ = (exp (-13 * (A.card : ℝ) - 3)) ^ A.powerset.card * exp (-4 : ℝ) := by
                  rw [exp_nat_mul]
              _ ≤ va ^ A.powerset.card * exp (-4 : ℝ) :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (exp_pos _).le vs _)
                    (exp_pos _).le
          refine u2.trans (hEO.trans (zi hp0 hp1 fun f₂ ⟨hex, hzr⟩ => ?_))
          have vo : N (z0 (v0 k) f₁ f₂) ⟨k - 1, by omega⟩ = A := by
            ext z; simp only [A, N, mem_filter]
            refine and_congr_right fun hzB => ?_
            have hne : x ⟨k - 1, by omega⟩ ≠ z := fun h => hdisj_xB _ (h ▸ hzB)
            have hxP : x ⟨k - 1, by omega⟩ ∈ PrefX k :=
              mem_image.mpr ⟨⟨k - 1, by omega⟩, mem_filter.mpr ⟨mem_univ _, by simp; omega⟩, rfl⟩
            have hmem : z7 (x ⟨k - 1, by omega⟩) z hne ∈ v0 k :=
              mem_union_right _ ((z5 (PrefX k) B hne).mpr (Or.inl ⟨hxP, hzB⟩))
            rw [zf (v0 k) f₁ f₂ hne hmem,
              zf (v0 k) f₁ (fun _ => false) hne hmem]
          have vi : ∀ u ∈ B, (z1 (z0 (v0 k) f₁ f₂)).Adj (x ⟨k, by omega⟩) u ↔
              ∃ (h : x ⟨k, by omega⟩ ≠ u) (hmem : z7 (x ⟨k, by omega⟩) u h ∉ v0 k),
                f₂ ⟨z7 (x ⟨k, by omega⟩) u h, hmem⟩ = true := by
            intro u hu
            have hne : x ⟨k, by omega⟩ ≠ u := fun h => hdisj_xB _ (h ▸ hu)
            have hnot : z7 (x ⟨k, by omega⟩) u hne ∉ v0 k := disjoint_right.mp vd
              ((z5 {x ⟨k, by omega⟩} B hne).mpr (Or.inl ⟨mem_singleton_self _, hu⟩))
            exact zb (v0 k) f₁ f₂ hne hnot
          dsimp only [StepK]; rw [vo]
          refine ⟨fun S hS => ?_, fun u hu => ?_⟩
          · rw [← hex S hS]; congr 1
            exact filter_congr fun u hu =>
              vi u (hBc0_sub (sdiff_subset (hPool_sub A v9 v3 S hS hu)))
          · rw [vi u (sdiff_subset hu)]; exact hzr u hu
        have vg := z06 hp0 hp1 S_rev (v0 k)
          subset_union_left f_rev (ChainOk k) StepK (vb k hk1 hkm)
          v2 (exp_pos _).le u1
        have vm : z4 p (fun f_rem : {e // e ∉ S_rev} → Bool =>
              ChainOk k (z0 S_rev f_rev f_rem) ∧ StepK (z0 S_rev f_rev f_rem)) ≤
            z4 p (fun f_rem : {e // e ∉ S_rev} → Bool =>
              ChainOk (k + 1) (z0 S_rev f_rev f_rem)) := by
          refine zi hp0 hp1 fun f_rem ⟨hCk, hSk⟩ => ?_
          refine ⟨hCk.1, fun i hi him => ?_⟩
          by_cases hik : i + 1 < k
          · exact hCk.2 i hik him
          · have u0 : i = k - 1 := by omega
            subst u0
            have vz : (⟨k - 1 + 1, him⟩ : Fin m) = ⟨k, by omega⟩ := Fin.ext (by simp; omega)
            rw [vz]; exact hSk
        have vl : exp (-6 : ℝ) * v2 ^ (k + 1 - 1) =
            (exp (-6 : ℝ) * v2 ^ (k - 1)) * v2 := by
          have vu : k + 1 - 1 = (k - 1) + 1 := by omega
          rw [vu, pow_succ]; ring
        rw [vl]
        exact (mul_le_mul_of_nonneg_right vx (exp_pos _).le).trans (vg.trans vm)
  have vv := hind m (by omega) le_rfl
  have u3 : QOf m ≤ exp (-6 : ℝ) * v2 ^ (m - 1) := by
    change exp (-(20 * (m : ℝ) * (T : ℝ) ^ 2 + 100)) ≤ exp (-6 : ℝ) * v2 ^ (m - 1)
    dsimp only [v2]
    rw [← exp_nat_mul, ← exp_add]
    refine exp_le_exp.mpr ?_
    have hm1 : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
    have vt : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hT2 : (4 : ℝ) ≤ (T : ℝ) := by
      have hmT : m ≤ T := y9 m (by have := hlp.hm; omega)
      have hm10 := hlp.hm
      exact_mod_cast (show 4 ≤ T by omega)
    have hTsq : (16 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith only [hT2]
    have hm10 : (10 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlp.hm
    nlinarith only [hm1, vt, hTsq, hm10]
  refine u3.trans (vv.trans (zi hp0 hp1 fun f_rem ⟨hbase, hstep⟩ => ?_))
  exact ⟨hbase, fun i => hstep i.val (by omega) (by omega)⟩
lemma z1b (q : ℕ) (hq : 2 ≤ q) {n m K : ℕ}
    (hm : 2 ≤ m) (hK : K ≤ zd m)
    {G : SimpleGraph (Fin n)}
    (hE1 : G ∈ EventE1 q n K)
    (hE2 : G ∈ EventE2 q hq n m)
    (a : Fin (kOf q) → Fin n) (hinj : Function.Injective a)
    (e : Fin m → Fin n) (x : Fin m → Fin n) (_hx_inj : Function.Injective x)
    (hE_iff : ∀ z : Fin n, inE q hq G a z ↔ ∃ j : Fin m, z = e j)
    (hD_iff : ∀ v : Fin n, inDom q hq G a v ↔ ∃ i : Fin m, v = x i)
    (hR_iff : ∀ i j : Fin m, Rrel q hq G a (x i) (e j) ↔ j.val ≤ i.val)
    (hbase_card : (zh q hq G a (x ⟨0, by omega⟩)).card = 1)
    (hstep_chain : ∀ i : Fin (m - 1),
      yn q hq G a (x ⟨i.val, by omega⟩) (x ⟨i.val + 1, by omega⟩)) :
    ws q hq G a := by
  classical
  have v1 : 0 < m := by omega
  have v0 : ∀ i k : Fin m, yv q hq G a (x i) (x k) ↔ i.val < k.val := by
    intro i k
    constructor
    · rintro ⟨_, z, hzE, hRkz, hnRiz⟩
      rcases (hE_iff z).mp hzE with ⟨j, rfl⟩
      have h1 : j.val ≤ k.val := (hR_iff k j).mp hRkz
      have h2 : ¬ j.val ≤ i.val := fun h => hnRiz ((hR_iff i j).mpr h)
      omega
    · intro hik
      refine ⟨fun z hzE hRiz => ?_, ?_⟩
      · rcases (hE_iff z).mp hzE with ⟨j, rfl⟩
        exact (hR_iff k j).mpr (le_trans ((hR_iff i j).mp hRiz) (le_of_lt hik))
      · refine ⟨e k, (hE_iff (e k)).mpr ⟨k, rfl⟩, (hR_iff k k).mpr le_rfl, ?_⟩
        rw [hR_iff i k]; omega
  refine ⟨hinj, ⟨x ⟨0, v1⟩, (hD_iff _).mpr ⟨⟨0, v1⟩, rfl⟩⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro u v hu hv
    rcases (hD_iff u).mp hu with ⟨i, rfl⟩
    rcases (hD_iff v).mp hv with ⟨k, rfl⟩
    rcases lt_trichotomy i.val k.val with hlt | heq | hgt
    · exact Or.inl ((v0 i k).mpr hlt)
    · exact Or.inr (Or.inl (by rw [Fin.ext heq]))
    · exact Or.inr (Or.inr ((v0 k i).mpr hgt))
  ·
    intro u hu hmin
    rcases (hD_iff u).mp hu with ⟨i, rfl⟩
    have hi0 : i = ⟨0, v1⟩ := by
      by_contra hne
      have hpos : 0 < i.val := by
        have : i.val ≠ 0 := fun h => hne (Fin.ext h)
        omega
      exact hmin (x ⟨0, v1⟩) ((hD_iff _).mpr ⟨⟨0, v1⟩, rfl⟩)
        ((v0 ⟨0, v1⟩ i).mpr hpos)
    subst hi0
    rcases card_eq_one.mp hbase_card with ⟨z₀, hz₀⟩
    refine ⟨z₀, (zt q hq G a (x ⟨0, v1⟩) z₀).mp (by rw [hz₀]; exact mem_singleton_self z₀),
      fun z' hz' => ?_⟩
    have hmem : z' ∈ zh q hq G a (x ⟨0, v1⟩) := (zt q hq G a _ _).mpr hz'
    rw [hz₀, mem_singleton] at hmem
    exact hmem
  ·
    intro u v ⟨hu, hv, hlt, hno⟩
    rcases (hD_iff u).mp hu with ⟨i, rfl⟩
    rcases (hD_iff v).mp hv with ⟨k, rfl⟩
    have hik : i.val < k.val := (v0 i k).mp hlt
    have vb : k.val = i.val + 1 := by
      by_contra hne
      have hmid : i.val + 1 < k.val := by omega
      exact hno (x ⟨i.val + 1, by omega⟩) ((hD_iff _).mpr ⟨⟨i.val + 1, by omega⟩, rfl⟩)
        ⟨(v0 i ⟨i.val + 1, by omega⟩).mpr (by simp),
         (v0 ⟨i.val + 1, by omega⟩ k).mpr hmid⟩
    have vc : i.val < m - 1 := by omega
    have hst := hstep_chain ⟨i.val, vc⟩
    have h1 : (⟨i.val, by omega⟩ : Fin m) = i := Fin.ext rfl
    have h2 : (⟨i.val + 1, by omega⟩ : Fin m) = k := Fin.ext vb.symm
    rwa [h1, h2] at hst
  ·
    have v6 : ∀ (i : ℕ) (hi : i < m), (zh q hq G a (x ⟨i, hi⟩)).card = zd i := by
      intro i
      induction i with
      | zero => intro _; exact hbase_card
      | succ k ih =>
        intro hk
        have v7 := ih (by omega)
        have hle : (zh q hq G a (x ⟨k, by omega⟩)).card ≤ zd (m - 1) := by
          rw [v7]; exact y6 (by omega)
        have v5 : ¬ zs q a (x ⟨k, by omega⟩) := ((hD_iff _).mpr ⟨⟨k, by omega⟩, rfl⟩).2.2
        have v4 := (hE2 a hinj).1 (x ⟨k, by omega⟩) v5 hle
        have hst := hstep_chain ⟨k, by omega⟩
        have vd := wx q hq G a (x ⟨k, by omega⟩) (x ⟨k + 1, hk⟩) hst v4
        rw [vd, v7]; rfl
    intro u hu hmax ⟨y, hny, hstep⟩
    rcases (hD_iff u).mp hu with ⟨i, rfl⟩
    have v9 : i = ⟨m - 1, by omega⟩ := by
      by_contra hne
      have hlt : i.val < m - 1 := by
        have : i.val ≠ m - 1 := fun h => hne (Fin.ext h)
        omega
      exact hmax (x ⟨m - 1, by omega⟩) ((hD_iff _).mpr ⟨⟨m - 1, by omega⟩, rfl⟩)
        ((v0 i ⟨m - 1, by omega⟩).mpr hlt)
    subst v9
    have v2 : (zh q hq G a (x ⟨m - 1, by omega⟩)).card = zd (m - 1) :=
      v6 (m - 1) (by omega)
    have v5 : ¬ zs q a (x ⟨m - 1, by omega⟩) := ((hD_iff _).mpr ⟨⟨m - 1, by omega⟩, rfl⟩).2.2
    have v4 := (hE2 a hinj).1 (x ⟨m - 1, by omega⟩) v5 (le_of_eq v2)
    have v3 := wx q hq G a (x ⟨m - 1, by omega⟩) y hstep v4
    rw [v2] at v3
    have htm : 2 ^ zd (m - 1) = zd m := by
      have va : m = (m - 1) + 1 := by omega
      rw [va]; rfl
    rw [htm] at v3
    let w : Fin q → Fin n := fun j =>
      if hj : j.val < q - 1 then yc q hq a ⟨j.val, hj⟩ else y
    have v8 : Function.Injective w := by
      intro j₁ j₂ heq
      by_cases h1 : j₁.val < q - 1 <;> by_cases h2 : j₂.val < q - 1
      · simp only [w, h1, h2, ↓reduceDIte] at heq
        exact Fin.ext (congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq))
      · simp only [w, h1, h2, ↓reduceDIte] at heq
        exact False.elim (hny ⟨cIdx q hq ⟨j₁.val, h1⟩, heq.symm⟩)
      · simp only [w, h1, h2, ↓reduceDIte] at heq
        exact False.elim (hny ⟨cIdx q hq ⟨j₂.val, h2⟩, heq⟩)
      · exact Fin.ext (by omega)
    have hsub : zh q hq G a y ⊆ zc G w := by
      intro z hz
      rcases (zt q hq G a y z).mp hz with ⟨hbc, hadj, _⟩
      rw [zl]; intro j; dsimp only [w]
      split_ifs with hj
      · exact hbc ⟨j.val, hj⟩
      · exact hadj
    have ve : (zh q hq G a y).card < K :=
      lt_of_le_of_lt (card_le_card hsub) (hE1 w v8)
    omega
end
section
open scoped BigOperators Classical
open Finset Real Nat
def EventE4 (q : ℕ) (hq : 2 ≤ q) (n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∃ a : Fin (kOf q) → Fin n, ws q hq G a}
def mkA (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (d d' : Fin (nOf q m)) : Fin (kOf q) → Fin (nOf q m) := fun r =>
  if h1 : r.val < 3 * q - 4 then
    ⟨r.val, by have := hlp.hn_ge_params; unfold kOf at this; omega⟩
  else if r.val = 3 * q - 4 then d
  else d'
def zn (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) : Finset (Fin (nOf q m)) :=
  (univ : Finset (Fin (3 * q - 4))).image (fun r =>
    ⟨r.val, by have := hlp.hn_ge_params; unfold kOf at this; omega⟩)
def ye (q m : ℕ) (hlp : LargeParams q m) : Fin (nOf q m) :=
  ⟨3 * q - 4, by have := hlp.hn_ge_params; unfold kOf at this; omega⟩
def ye' (q m : ℕ) (hlp : LargeParams q m) : Fin (nOf q m) :=
  ⟨3 * q - 3, by have := hlp.hn_ge_params; unfold kOf at this; omega⟩
lemma z2e (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) (d d' : Fin (nOf q m)) (i : Fin (q - 1)) :
    yc q hq (mkA q m hq hlp d d') i =
      ⟨i.val, by have := hlp.hn_ge_params; unfold kOf at this; omega⟩ := by
  unfold yc mkA cIdx
  have hlt : i.val < 3 * q - 4 := by omega
  simp [hlt]
lemma z2e' (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) (d d' : Fin (nOf q m)) (i : Fin (q - 1)) :
    yc' q hq (mkA q m hq hlp d d') i =
      ⟨(q - 1) + i.val, by have := hlp.hn_ge_params; unfold kOf at this; omega⟩ := by
  unfold yc' mkA z1q
  have hlt : (q - 1) + i.val < 3 * q - 4 := by omega
  simp [hlt]
lemma z2h (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) (d d' : Fin (nOf q m)) (j : Fin (q - 2)) :
    ys q hq (mkA q m hq hlp d d') j =
      ⟨2 * (q - 1) + j.val, by have := hlp.hn_ge_params; unfold kOf at this; omega⟩ := by
  unfold ys mkA bIdx
  have hlt : 2 * (q - 1) + j.val < 3 * q - 4 := by omega
  simp [hlt]
lemma z14 (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) (d d' : Fin (nOf q m)) :
    w7 q hq (mkA q m hq hlp d d') = d := by
  unfold w7 mkA dIdx; simp
lemma z14' (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) (d d' : Fin (nOf q m)) :
    w7' q hq (mkA q m hq hlp d d') = d' := by
  unfold w7' mkA z29
  have h1 : ¬ (3 * q - 3 < 3 * q - 4) := by omega
  have h2 : ¬ (3 * q - 3 = 3 * q - 4) := by omega
  simp [h1, h2]
lemma yp (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (d d' : Fin (nOf q m)) (r : Fin (kOf q)) (hr : r.val < 3 * q - 4) :
    mkA q m hq hlp d d' r ∈ zn q m hq hlp := by
  unfold mkA zn
  simp only [dif_pos hr, mem_image, mem_univ, true_and]
  exact ⟨⟨r.val, hr⟩, rfl⟩
lemma yl (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (d d' v : Fin (nOf q m)) :
    zs q (mkA q m hq hlp d d') v ↔ v ∈ zn q m hq hlp ∨ v = d ∨ v = d' := by
  constructor
  · rintro ⟨r, rfl⟩
    by_cases h1 : r.val < 3 * q - 4
    · exact Or.inl (yp q m hq hlp d d' r h1)
    · by_cases h2 : r.val = 3 * q - 4
      · exact Or.inr (Or.inl (by unfold mkA; simp [h2]))
      · exact Or.inr (Or.inr (by unfold mkA; simp [h1, h2]))
  · rintro (hP | heq | heq)
    · rcases mem_image.mp hP with ⟨r, _, rfl⟩
      refine ⟨⟨r.val, by unfold kOf; omega⟩, ?_⟩
      unfold mkA; simp [r.isLt]
    · rw [heq]; exact ⟨dIdx q hq, (z14 q m hq hlp d d').symm⟩
    · rw [heq]; exact ⟨z29 q hq, (z14' q m hq hlp d d').symm⟩
lemma z16 (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    {d d' : Fin (nOf q m)} (hd : d ∉ zn q m hq hlp)
    (hd' : d' ∉ zn q m hq hlp) (hne : d ≠ d') :
    Function.Injective (mkA q m hq hlp d d') := by
  intro r₁ r₂ heq
  by_cases h1 : r₁.val < 3 * q - 4 <;> by_cases h2 : r₂.val < 3 * q - 4
  · simp only [mkA, dif_pos h1, dif_pos h2, Fin.mk.injEq] at heq; exact Fin.ext heq
  · have hm : mkA q m hq hlp d d' r₁ ∈ zn q m hq hlp := yp q m hq hlp d d' r₁ h1
    rw [heq] at hm
    by_cases h2' : r₂.val = 3 * q - 4
    · simp only [mkA, dif_neg h2, if_pos h2'] at hm; exact absurd hm hd
    · simp only [mkA, dif_neg h2, if_neg h2'] at hm; exact absurd hm hd'
  · have hm : mkA q m hq hlp d d' r₂ ∈ zn q m hq hlp := yp q m hq hlp d d' r₂ h2
    rw [← heq] at hm
    by_cases h1' : r₁.val = 3 * q - 4
    · simp only [mkA, dif_neg h1, if_pos h1'] at hm; exact absurd hm hd
    · simp only [mkA, dif_neg h1, if_neg h1'] at hm; exact absurd hm hd'
  · have hr1 := r₁.isLt; have hr2 := r₂.isLt; unfold kOf at hr1 hr2
    by_cases h1' : r₁.val = 3 * q - 4 <;> by_cases h2' : r₂.val = 3 * q - 4
    · exact Fin.ext (by omega)
    · simp only [mkA, dif_neg h1, dif_neg h2, if_pos h1', if_neg h2'] at heq; exact absurd heq hne
    · simp only [mkA, dif_neg h1, dif_neg h2, if_neg h1', if_pos h2'] at heq; exact absurd heq.symm hne
    · exact Fin.ext (by omega)
def wf (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (G : SimpleGraph (Fin (nOf q m))) (z : Fin (nOf q m)) : Prop :=
  isBc q hq G (mkA q m hq hlp (ye q m hlp) (ye' q m hlp)) z
def wr (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (G : SimpleGraph (Fin (nOf q m))) (z : Fin (nOf q m)) : Prop :=
  isBc' q hq G (mkA q m hq hlp (ye q m hlp) (ye' q m hlp)) z
lemma z0i (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (G : SimpleGraph (Fin (nOf q m))) (d d' z : Fin (nOf q m)) :
    isBc q hq G (mkA q m hq hlp d d') z ↔ wf q m hq hlp G z := by
  unfold wf isBc; simp only [z2e]
lemma w8 (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (G : SimpleGraph (Fin (nOf q m))) (d d' z : Fin (nOf q m)) :
    isBc' q hq G (mkA q m hq hlp d d') z ↔ wr q m hq hlp G z := by
  unfold wr isBc'; simp only [z2e']
noncomputable def zr (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (G : SimpleGraph (Fin (nOf q m))) : Finset (Fin (nOf q m)) :=
  univ.filter (wf q m hq hlp G)
noncomputable def zp (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (G : SimpleGraph (Fin (nOf q m))) : Finset (Fin (nOf q m)) :=
  univ.filter (wr q m hq hlp G)
noncomputable def zj (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (G : SimpleGraph (Fin (nOf q m))) : Finset (Fin (nOf q m)) :=
  univ.filter fun w =>
    w ∉ zn q m hq hlp ∧ ¬ wf q m hq hlp G w ∧ ¬ wr q m hq hlp G w ∧
    ∀ j : Fin (q - 2), G.Adj w (ys q hq (mkA q m hq hlp (ye q m hlp) (ye' q m hlp)) j)
lemma z00 (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (G : SimpleGraph (Fin (nOf q m))) (d d' : Fin (nOf q m)) :
    zg q hq G (mkA q m hq hlp d d') = ((zj q m hq hlp G).erase d).erase d' := by
  ext w
  simp only [y8, z0m, yl, z0i, w8, z2h,
    mem_erase, zj, mem_filter, mem_univ, true_and]
  tauto
lemma zz (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (f g : z6 (nOf q m) → Bool)
    (hfg : ∀ e ∈ ze (zn q m hq hlp), f e = g e) :
    zr q m hq hlp (z1 f) = zr q m hq hlp (z1 g) ∧
    zp q m hq hlp (z1 f) = zp q m hq hlp (z1 g) ∧
    zj q m hq hlp (z1 f) = zj q m hq hlp (z1 g) := by
  have hadj : ∀ u ∈ zn q m hq hlp, ∀ v : Fin (nOf q m),
      (z1 f).Adj v u ↔ (z1 g).Adj v u := by
    intro u hu v
    by_cases hvu : v = u
    · subst hvu; simp
    · rw [za f hvu, za g hvu,
        hfg _ ((z0p _ hvu).mpr (Or.inr hu))]
  have v3 : ∀ i : Fin (q - 1), yc q hq (mkA q m hq hlp (ye q m hlp) (ye' q m hlp)) i ∈
      zn q m hq hlp := fun i => yp q m hq hlp _ _ (cIdx q hq i) (by unfold cIdx; simp; omega)
  have v2 : ∀ i : Fin (q - 1), yc' q hq (mkA q m hq hlp (ye q m hlp) (ye' q m hlp)) i ∈
      zn q m hq hlp := fun i => yp q m hq hlp _ _ (z1q q hq i) (by unfold z1q; simp; omega)
  have v4 : ∀ j : Fin (q - 2), ys q hq (mkA q m hq hlp (ye q m hlp) (ye' q m hlp)) j ∈
      zn q m hq hlp := fun j => yp q m hq hlp _ _ (bIdx q hq j) (by unfold bIdx; simp; omega)
  have v1 : ∀ z, wf q m hq hlp (z1 f) z ↔ wf q m hq hlp (z1 g) z :=
    fun z => forall_congr' fun i => hadj _ (v3 i) z
  have v0 : ∀ z, wr q m hq hlp (z1 f) z ↔ wr q m hq hlp (z1 g) z :=
    fun z => forall_congr' fun i => hadj _ (v2 i) z
  refine ⟨?_, ?_, ?_⟩
  · ext z; simp only [zr, mem_filter, mem_univ, true_and, v1]
  · ext z; simp only [zp, mem_filter, mem_univ, true_and, v0]
  · ext w; simp only [zj, mem_filter, mem_univ, true_and, v1, v0]
    exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      forall_congr' fun j => hadj _ (v4 j) w
lemma z1k (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    {G : SimpleGraph (Fin (nOf q m))}
    (hE1 : G ∈ EventE1 q (nOf q m) (KOf q m))
    (hEdeg : G ∈ EventEdeg q (nOf q m) (ROf m)) :
    let R := ROf m
    ((R : ℝ) / 3 ≤ ((zr q m hq hlp G).card : ℝ) ∧ ((zr q m hq hlp G).card : ℝ) ≤ 2 * (R : ℝ)) ∧
    ((R : ℝ) / 3 ≤ ((zp q m hq hlp G).card : ℝ) ∧ ((zp q m hq hlp G).card : ℝ) ≤ 2 * (R : ℝ)) ∧
    ((zr q m hq hlp G ∩ zp q m hq hlp G).card < KOf q m) ∧
    ((1 / 4 : ℝ) * ((R : ℝ) ^ 2) ≤ ((zj q m hq hlp G).card : ℝ) ∧
      ((zj q m hq hlp G).card : ℝ) ≤ 2 * ((R : ℝ) ^ 2)) := by
  let a₀ := mkA q m hq hlp (ye q m hlp) (ye' q m hlp)
  have v2 : ye q m hlp ∉ zn q m hq hlp := by
    intro h; rcases mem_image.mp h with ⟨r, _, hr⟩
    have hv := congrArg Fin.val hr; simp only [ye] at hv; omega
  have v0 : ye' q m hlp ∉ zn q m hq hlp := by
    intro h; rcases mem_image.mp h with ⟨r, _, hr⟩
    have hv := congrArg Fin.val hr; simp only [ye'] at hv; omega
  have hne : ye q m hlp ≠ ye' q m hlp := by
    intro h; have hv := congrArg Fin.val h; simp only [ye, ye'] at hv; omega
  have hinj : Function.Injective a₀ := z16 q m hq hlp v2 v0 hne
  have hdet := yw q m hq hlp hE1 hEdeg a₀ hinj
  have v3 : zr q m hq hlp G = zk q hq G a₀ := rfl
  have v1 : zp q m hq hlp G = zm q hq G a₀ := rfl
  rw [v3, v1]
  refine ⟨hdet.1, hdet.2.1, hdet.2.2.1, ?_, ?_⟩
  · have hsub : zg q hq G a₀ ⊆ zj q m hq hlp G := by
      rw [z00]
      exact (erase_subset _ _).trans (erase_subset _ _)
    exact hdet.2.2.2.1.1.trans (Nat.cast_le.mpr (card_le_card hsub))
  ·
    by_cases hq2 : q = 2
    · have hle : (zj q m hq hlp G).card ≤ nOf q m := by
        calc (zj q m hq hlp G).card ≤ (univ : Finset (Fin (nOf q m))).card :=
              card_le_card (subset_univ _)
          _ = nOf q m := by simp
      have hn : nOf q m = ROf m ^ 2 := by rw [w5, hq2]
      have hle' : (zj q m hq hlp G).card ≤ ROf m ^ 2 := by omega
      have hc : ((zj q m hq hlp G).card : ℝ) ≤ (ROf m : ℝ) ^ 2 := by exact_mod_cast hle'
      nlinarith only [hc, sq_nonneg (ROf m : ℝ)]
    · have hq3 : 3 ≤ q := by omega
      have v4 : Function.Injective (ys q hq a₀) := fun j₁ j₂ heq => by
        have hv := congrArg (Fin.val : Fin (kOf q) → ℕ) (hinj heq)
        simp only [bIdx] at hv; exact Fin.ext (by omega)
      have hsub : zj q m hq hlp G ⊆ zc G (ys q hq a₀) := fun w hw => by
        rw [zl]
        exact (mem_filter.mp hw).2.2.2.2
      have hdeg := (hEdeg (q - 2) (by omega) (by omega) (ys q hq a₀) v4).2
      have hexp : q - (q - 2) = 2 := by omega
      rw [hexp] at hdeg
      exact (Nat.cast_le.mpr (card_le_card hsub)).trans hdeg
private lemma z21 (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (S₄ : Finset (z6 (nOf q m)))
    (f₄ : {e : z6 (nOf q m) // e ∈ S₄} → Bool)
    (d' : Fin (nOf q m))
    (V0 V1 V2 V2_star _E Bc_np Bc'_np Bc0_clean : Finset (Fin (nOf q m)))
    (e_enum : Fin m → Fin (nOf q m))
    (x_map : Fin (nOf q m) → Fin m → Fin (nOf q m))
    (Pool : Finset (Fin (nOf q m)) → Finset (Fin (nOf q m)) → Finset (Fin (nOf q m)))
    (hS0_sub : ze (zn q m hq hlp) ⊆ S₄)
    (hd'_V0 : d' ∈ V0)
    (hV0_sub : V0 ⊆ zj q m hq hlp (z1 (z0 S₄ f₄ (fun _ => false))))
    (_hV1_sub : V1 ⊆ zj q m hq hlp (z1 (z0 S₄ f₄ (fun _ => false))))
    (hV2_sub : V2 ⊆ zj q m hq hlp (z1 (z0 S₄ f₄ (fun _ => false))))
    (hV2s_sub : V2_star ⊆ V2)
    (_hV01 : Disjoint V0 V1) (hV02 : Disjoint V0 V2) (_hV12 : Disjoint V1 V2)
    (_hV_cover : zj q m hq hlp (z1 (z0 S₄ f₄ (fun _ => false))) ⊆ V0 ∪ V1 ∪ V2)
    (hBc_np_eq : Bc_np = zr q m hq hlp (z1 (z0 S₄ f₄ (fun _ => false))) \ zn q m hq hlp)
    (_hBc'_np_eq : Bc'_np = zp q m hq hlp (z1 (z0 S₄ f₄ (fun _ => false))) \ zn q m hq hlp)
    (hBc0_sub : Bc0_clean ⊆ Bc_np)
    (hBc_hi : (Bc_np.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc0_lo : (ROf m : ℝ) / 5 ≤ (Bc0_clean.card : ℝ))
    (hV2s_lo : (1 / 2 : ℝ) * ((R4Of m : ℝ) * QOf m) ≤ (V2_star.card : ℝ))
    (hx_inj : ∀ d ∈ V2_star, Function.Injective (x_map d))
    (hx_not_B : ∀ d ∈ V2_star, ∀ i : Fin m, x_map d i ∉ Bc_np)
    (hx_disj_d : ∀ d₁ ∈ V2_star, ∀ d₂ ∈ V2_star, d₁ ≠ d₂ →
      Disjoint (univ.image (x_map d₁)) (univ.image (x_map d₂)))
    (hdisj_S4 : ∀ d ∈ V2_star, Disjoint S₄ (z8 (univ.image (x_map d)) Bc_np))
    (hE_iff : ∀ d ∈ V2_star, ∀ f₅ : {e // e ∉ S₄} → Bool, ∀ z : Fin (nOf q m),
      inE q hq (z1 (z0 S₄ f₄ f₅)) (mkA q m hq hlp d d') z ↔ ∃ j : Fin m, z = e_enum j)
    (hD_iff : ∀ d ∈ V2_star, ∀ f₅ : {e // e ∉ S₄} → Bool, ∀ v : Fin (nOf q m),
      inDom q hq (z1 (z0 S₄ f₄ f₅)) (mkA q m hq hlp d d') v ↔ ∃ i : Fin m, v = x_map d i)
    (hR_xe : ∀ d ∈ V2_star, ∀ f₅ : {e // e ∉ S₄} → Bool, ∀ i j : Fin m,
      Rrel q hq (z1 (z0 S₄ f₄ f₅)) (mkA q m hq hlp d d') (x_map d i) (e_enum j) ↔ j.val ≤ i.val)
    (hR_bc0 : ∀ d ∈ V2_star, ∀ f₅ : {e // e ∉ S₄} → Bool, ∀ u ∈ Bc0_clean, ∀ z ∈ Bc0_clean,
      Rrel q hq (z1 (z0 S₄ f₄ f₅)) (mkA q m hq hlp d d') u z ↔
        ∃ w ∈ V1, (z1 (z0 S₄ f₄ (fun _ => false))).Adj w u ∧
          (z1 (z0 S₄ f₄ (fun _ => false))).Adj w z)
    (hPool_sub : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      ∀ S ∈ A.powerset, Pool A S ⊆ Bc0_clean \ A)
    (hPool_disj : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      Set.PairwiseDisjoint (A.powerset : Set (Finset (Fin (nOf q m)))) (Pool A))
    (hPool_lo : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      ∀ S ∈ A.powerset, ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (ROf m : ℝ) ≤
        ((Pool A S).card : ℝ))
    (hPool_pat : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      ∀ S ∈ A.powerset, ∀ u ∈ Pool A S, ∀ z ∈ A,
        (∃ w ∈ V1, (z1 (z0 S₄ f₄ (fun _ => false))).Adj w u ∧
          (z1 (z0 S₄ f₄ (fun _ => false))).Adj w z) ↔ z ∈ S) :
    z4 ((ROf m : ℝ)⁻¹) (fun f₅ : {e : z6 (nOf q m) // e ∉ S₄} → Bool =>
      z1 (z0 S₄ f₄ f₅) ∈
        EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ) ≤
      1 / 256 := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set p : ℝ := (R : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have v1 : 0 < m := by have := hlp.hm; omega
  let G₄ := z1 (z0 S₄ f₄ (fun _ => false))
  let Td : Fin (nOf q m) → Finset {e : z6 (nOf q m) // e ∉ S₄} := fun d =>
    if hd : d ∈ V2_star then
      ((univ.image (x_map d)) ×ˢ Bc_np).attach.image (fun (y : {t // t ∈ (univ.image (x_map d)) ×ˢ Bc_np}) =>
        have hy1 : y.1.1 ∈ univ.image (x_map d) := (mem_product.mp y.2).1
        have hy2 : y.1.2 ∈ Bc_np := (mem_product.mp y.2).2
        have hne : y.1.1 ≠ y.1.2 := by
          rcases mem_image.mp hy1 with ⟨i, _, hi⟩
          exact fun h => hx_not_B d hd i (hi.symm ▸ h ▸ hy2)
        ⟨z7 y.1.1 y.1.2 hne, disjoint_right.mp (hdisj_S4 d hd)
          ((z5 _ _ hne).mpr (Or.inl ⟨hy1, hy2⟩))⟩)
    else ∅
  have vf : Set.PairwiseDisjoint (V2_star : Set (Fin (nOf q m))) Td := by
    intro d₁ hd₁ d₂ hd₂ hne_d
    have hd₁' : d₁ ∈ V2_star := mem_coe.mp hd₁
    have hd₂' : d₂ ∈ V2_star := mem_coe.mp hd₂
    change Disjoint (Td d₁) (Td d₂)
    rw [disjoint_left]; intro e he₁ he₂
    dsimp only [Td] at he₁ he₂; rw [dif_pos hd₁'] at he₁; rw [dif_pos hd₂'] at he₂
    rcases mem_image.mp he₁ with ⟨y₁, _, rfl⟩
    rcases mem_image.mp he₂ with ⟨y₂, _, heq⟩
    rcases zv heq with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact disjoint_left.mp (hx_disj_d d₁ hd₁' d₂ hd₂' hne_d)
        (mem_product.mp y₁.2).1 (h1 ▸ (mem_product.mp y₂.2).1)
    · rcases mem_image.mp (mem_product.mp y₂.2).1 with ⟨i, _, hi⟩
      exact hx_not_B d₂ hd₂' i (hi.symm ▸ h1 ▸ (mem_product.mp y₁.2).2)
  let GoodD : Fin (nOf q m) → ({e : z6 (nOf q m) // e ∉ S₄} → Bool) → Prop := fun d f₅ =>
    let f := z0 S₄ f₄ f₅
    let N : Fin m → Finset (Fin (nOf q m)) := fun i => Bc_np.filter (fun z => (z1 f).Adj (x_map d i) z)
    ((Bc0_clean.filter (fun z => (z1 f).Adj (x_map d ⟨0, v1⟩) z)).card = 1 ∧
      ∀ u ∈ Bc_np \ Bc0_clean, ¬ (z1 f).Adj (x_map d ⟨0, v1⟩) u) ∧
    ∀ i : Fin (m - 1),
      let A := N ⟨i.val, by omega⟩
      (∀ S ∈ A.powerset, ((Pool A S).filter (fun u => (z1 f).Adj (x_map d ⟨i.val + 1, by omega⟩) u)).card = 1) ∧
      (∀ u ∈ Bc_np \ A.powerset.biUnion (Pool A), ¬ (z1 f).Adj (x_map d ⟨i.val + 1, by omega⟩) u)
  have v2 : ∀ d ∈ V2_star, ∀ f₅ g₅ : {e // e ∉ S₄} → Bool,
      (∀ e ∈ Td d, f₅ e = g₅ e) → GoodD d f₅ → GoodD d g₅ := by
    intro d hd f₅ g₅ hfg hGf
    have hadj : ∀ (i : Fin m) (u : Fin (nOf q m)), u ∈ Bc_np →
        ((z1 (z0 S₄ f₄ f₅)).Adj (x_map d i) u ↔
         (z1 (z0 S₄ f₄ g₅)).Adj (x_map d i) u) := by
      intro i u hu
      have hne : x_map d i ≠ u := fun h => hx_not_B d hd i (h ▸ hu)
      have hxI : x_map d i ∈ univ.image (x_map d) := mem_image.mpr ⟨i, mem_univ _, rfl⟩
      have hnot : z7 (x_map d i) u hne ∉ S₄ := disjoint_right.mp (hdisj_S4 d hd)
        ((z5 _ _ hne).mpr (Or.inl ⟨hxI, hu⟩))
      have hmem : (⟨z7 (x_map d i) u hne, hnot⟩ : {e // e ∉ S₄}) ∈ Td d := by
        dsimp only [Td]; rw [dif_pos hd]
        exact mem_image.mpr ⟨⟨(x_map d i, u), mem_product.mpr ⟨hxI, hu⟩⟩, mem_attach _ _, rfl⟩
      rw [zb S₄ f₄ f₅ hne hnot, zb S₄ f₄ g₅ hne hnot]
      have heq := hfg _ hmem
      exact ⟨fun ⟨_, _, hf⟩ => ⟨hne, hnot, by rwa [← heq]⟩, fun ⟨_, _, hg⟩ => ⟨hne, hnot, by rwa [heq]⟩⟩
    let Nf : Fin m → Finset (Fin (nOf q m)) := fun i => Bc_np.filter (fun z => (z1 (z0 S₄ f₄ f₅)).Adj (x_map d i) z)
    let Ng : Fin m → Finset (Fin (nOf q m)) := fun i => Bc_np.filter (fun z => (z1 (z0 S₄ f₄ g₅)).Adj (x_map d i) z)
    have hNeq : ∀ i : Fin m, Nf i = Ng i := fun i => by
      ext z; simp only [Nf, Ng, mem_filter]; exact and_congr_right fun hz => hadj i z hz
    have vd : ∀ (i : ℕ) (hi : i < m), Nf ⟨i, hi⟩ ⊆ Bc0_clean ∧ (Nf ⟨i, hi⟩).card = zd i := by
      intro i; induction i with
      | zero =>
        intro _
        have heq : Nf ⟨0, v1⟩ = Bc0_clean.filter (fun z => (z1 (z0 S₄ f₄ f₅)).Adj (x_map d ⟨0, v1⟩) z) := by
          ext z; simp only [Nf, mem_filter]
          constructor
          · rintro ⟨hzB, ha⟩; by_contra hn
            exact hGf.1.2 z (mem_sdiff.mpr ⟨hzB, fun h => hn ⟨h, ha⟩⟩) ha
          · rintro ⟨hzC, ha⟩; exact ⟨hBc0_sub hzC, ha⟩
        rw [heq]; exact ⟨filter_subset _ _, hGf.1.1⟩
      | succ k ih =>
        intro hk
        have ⟨hsub_k, hcard_k⟩ := ih (by omega)
        have v3 : Nf ⟨k, by omega⟩ ∈ Bc0_clean.powerset := mem_powerset.mpr hsub_k
        have v0 : (Nf ⟨k, by omega⟩).card ≤ zd (m - 2) := by rw [hcard_k]; exact y6 (by omega)
        have hst := hGf.2 ⟨k, by omega⟩
        set A := Nf ⟨k, by omega⟩
        have heq : Nf ⟨k + 1, hk⟩ = A.powerset.biUnion (fun S =>
            (Pool A S).filter (fun u => (z1 (z0 S₄ f₄ f₅)).Adj (x_map d ⟨k + 1, hk⟩) u)) := by
          ext u; simp only [Nf, mem_filter, mem_biUnion]
          constructor
          · rintro ⟨huB, ha⟩; by_contra hn
            exact hst.2 u (mem_sdiff.mpr ⟨huB, fun h => by
              rcases mem_biUnion.mp h with ⟨S, hS, huP⟩; exact hn ⟨S, hS, huP, ha⟩⟩) ha
          · rintro ⟨S, hS, huP, ha⟩
            exact ⟨hBc0_sub (sdiff_subset (hPool_sub A v3 v0 S hS huP)), ha⟩
        rw [heq]
        refine ⟨biUnion_subset.mpr fun S hS =>
          (filter_subset _ _).trans ((hPool_sub A v3 v0 S hS).trans sdiff_subset), ?_⟩
        rw [card_biUnion]
        · rw [sum_congr rfl fun S hS => hst.1 S hS, sum_const, smul_eq_mul, mul_one,
            card_powerset, hcard_k]; rfl
        · intro S₁ hS₁ S₂ hS₂ hne
          exact (hPool_disj A v3 v0 hS₁ hS₂ hne).mono
            (filter_subset _ _) (filter_subset _ _)
    refine ⟨⟨?_, ?_⟩, fun i => ?_⟩
    · rw [filter_congr fun z hz => (hadj ⟨0, v1⟩ z (hBc0_sub hz)).symm]; exact hGf.1.1
    · intro u hu; rw [← hadj ⟨0, v1⟩ u (sdiff_subset hu)]; exact hGf.1.2 u hu
    · have vo : Ng ⟨i.val, by omega⟩ = Nf ⟨i.val, by omega⟩ := (hNeq ⟨i.val, by omega⟩).symm
      have ⟨hsub_i, hcard_i⟩ := vd i.val (by omega)
      have vj : Nf ⟨i.val, by omega⟩ ∈ Bc0_clean.powerset := mem_powerset.mpr hsub_i
      have vg : (Nf ⟨i.val, by omega⟩).card ≤ zd (m - 2) := by rw [hcard_i]; exact y6 (by omega)
      have hst := hGf.2 i
      change (∀ S ∈ (Ng ⟨i.val, by omega⟩).powerset,
          ((Pool (Ng ⟨i.val, by omega⟩) S).filter
            (fun u => (z1 (z0 S₄ f₄ g₅)).Adj (x_map d ⟨i.val + 1, by omega⟩) u)).card = 1) ∧
        (∀ u ∈ Bc_np \ (Ng ⟨i.val, by omega⟩).powerset.biUnion (Pool (Ng ⟨i.val, by omega⟩)),
          ¬ (z1 (z0 S₄ f₄ g₅)).Adj (x_map d ⟨i.val + 1, by omega⟩) u)
      rw [vo]
      refine ⟨fun S hS => ?_, fun u hu => ?_⟩
      · rw [filter_congr fun u hu =>
          (hadj ⟨i.val + 1, by omega⟩ u (hBc0_sub (sdiff_subset (hPool_sub _ vj vg S hS hu)))).symm]
        exact hst.1 S hS
      · rw [← hadj ⟨i.val + 1, by omega⟩ u (sdiff_subset hu)]; exact hst.2 u hu
  have va : ∀ d ∈ V2_star, ∀ f₅ g₅ : {e // e ∉ S₄} → Bool,
      (∀ e ∈ Td d, f₅ e = g₅ e) → (GoodD d f₅ ↔ GoodD d g₅) :=
    fun d hd f₅ g₅ hfg => ⟨v2 d hd f₅ g₅ hfg,
      v2 d hd g₅ f₅ (fun e he => (hfg e he).symm)⟩
  have v9 : ∀ d ∈ V2_star, ∀ f₅ : {e // e ∉ S₄} → Bool,
      GoodD d f₅ →
      z1 (z0 S₄ f₄ f₅) ∉
        EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ := by
    intro d hd f₅ hGd ⟨⟨hE1, hE2⟩, hnotE4⟩
    let G₅ := z1 (z0 S₄ f₄ f₅)
    have vl := zz q m hq hlp (z0 S₄ f₄ f₅) (z0 S₄ f₄ (fun _ => false))
      (fun e he => by simp only [z0, dif_pos (hS0_sub he)])
    have v8 : d ∈ zj q m hq hlp G₄ := hV2_sub (hV2s_sub hd)
    have v6 : d' ∈ zj q m hq hlp G₄ := hV0_sub hd'_V0
    have vh : d ∉ zn q m hq hlp := (mem_filter.mp v8).2.1
    have ve : d' ∉ zn q m hq hlp := (mem_filter.mp v6).2.1
    have hd_ne_d' : d ≠ d' := fun h => disjoint_left.mp hV02 hd'_V0 (h ▸ hV2s_sub hd)
    have vm : Function.Injective (mkA q m hq hlp d d') :=
      z16 q m hq hlp vh ve hd_ne_d'
    have v4 : ∀ i : Fin m,
        zh q hq G₅ (mkA q m hq hlp d d') (x_map d i) =
          Bc_np.filter (fun z => G₅.Adj (x_map d i) z) := by
      intro i; ext z
      have vi : wf q m hq hlp G₅ z ↔ wf q m hq hlp G₄ z := by
        have h := Finset.ext_iff.mp vl.1 z
        simpa [zr] using h
      simp only [zt, Ax, z0i, yl, mem_filter, hBc_np_eq,
        mem_sdiff, zr, mem_univ, true_and, vi]
      constructor
      · rintro ⟨hbc, hadj, hnp⟩
        exact ⟨⟨hbc, fun hP => hnp (Or.inl hP)⟩, hadj.symm⟩
      · rintro ⟨⟨hbc, hnotP⟩, hadj⟩
        refine ⟨hbc, hadj.symm, ?_⟩
        rintro (hP | heq | heq)
        · exact hnotP hP
        · exact (mem_filter.mp v8).2.2.1 (heq ▸ hbc)
        · exact (mem_filter.mp v6).2.2.1 (heq ▸ hbc)
    have v5 : ∀ (i : ℕ) (hi : i < m),
        zh q hq G₅ (mkA q m hq hlp d d') (x_map d ⟨i, hi⟩) ⊆ Bc0_clean ∧
        (zh q hq G₅ (mkA q m hq hlp d d') (x_map d ⟨i, hi⟩)).card = zd i := by
      intro i; induction i with
      | zero =>
        intro _
        rw [v4 ⟨0, v1⟩]
        have heq : Bc_np.filter (fun z => G₅.Adj (x_map d ⟨0, v1⟩) z) =
            Bc0_clean.filter (fun z => G₅.Adj (x_map d ⟨0, v1⟩) z) := by
          ext z; simp only [mem_filter]
          constructor
          · rintro ⟨hzB, ha⟩; by_contra hn
            exact hGd.1.2 z (mem_sdiff.mpr ⟨hzB, fun h => hn ⟨h, ha⟩⟩) ha
          · rintro ⟨hzC, ha⟩; exact ⟨hBc0_sub hzC, ha⟩
        rw [heq]; exact ⟨filter_subset _ _, hGd.1.1⟩
      | succ k ih =>
        intro hk
        have ⟨hsub_k, hcard_k⟩ := ih (by omega)
        have v3 : zh q hq G₅ (mkA q m hq hlp d d') (x_map d ⟨k, by omega⟩) ∈ Bc0_clean.powerset :=
          mem_powerset.mpr hsub_k
        have v0 : (zh q hq G₅ (mkA q m hq hlp d d') (x_map d ⟨k, by omega⟩)).card ≤ zd (m - 2) := by
          rw [hcard_k]; exact y6 (by omega)
        have hst := hGd.2 ⟨k, by omega⟩
        change (∀ S ∈ (Bc_np.filter (fun z => G₅.Adj (x_map d ⟨k, by omega⟩) z)).powerset,
          ((Pool (Bc_np.filter (fun z => G₅.Adj (x_map d ⟨k, by omega⟩) z)) S).filter
            (fun u => G₅.Adj (x_map d ⟨k + 1, hk⟩) u)).card = 1) ∧
          (∀ u ∈ Bc_np \ (Bc_np.filter (fun z => G₅.Adj (x_map d ⟨k, by omega⟩) z)).powerset.biUnion
            (Pool (Bc_np.filter (fun z => G₅.Adj (x_map d ⟨k, by omega⟩) z))),
            ¬ G₅.Adj (x_map d ⟨k + 1, hk⟩) u) at hst
        rw [← v4 ⟨k, by omega⟩] at hst
        set A := zh q hq G₅ (mkA q m hq hlp d d') (x_map d ⟨k, by omega⟩)
        rw [v4 ⟨k + 1, hk⟩]
        have heq : Bc_np.filter (fun z => G₅.Adj (x_map d ⟨k + 1, hk⟩) z) =
            A.powerset.biUnion (fun S => (Pool A S).filter (fun u => G₅.Adj (x_map d ⟨k + 1, hk⟩) u)) := by
          ext u; simp only [mem_filter, mem_biUnion]
          constructor
          · rintro ⟨huB, ha⟩; by_contra hn
            exact hst.2 u (mem_sdiff.mpr ⟨huB, fun h => by
              rcases mem_biUnion.mp h with ⟨S, hS, huP⟩; exact hn ⟨S, hS, huP, ha⟩⟩) ha
          · rintro ⟨S, hS, huP, ha⟩
            exact ⟨hBc0_sub (sdiff_subset (hPool_sub A v3 v0 S hS huP)), ha⟩
        rw [heq]
        refine ⟨biUnion_subset.mpr fun S hS =>
          (filter_subset _ _).trans ((hPool_sub A v3 v0 S hS).trans sdiff_subset), ?_⟩
        rw [card_biUnion]
        · rw [sum_congr rfl fun S hS => hst.1 S hS, sum_const, smul_eq_mul, mul_one,
            card_powerset, hcard_k]; rfl
        · intro S₁ hS₁ S₂ hS₂ hne
          exact (hPool_disj A v3 v0 hS₁ hS₂ hne).mono
            (filter_subset _ _) (filter_subset _ _)
    apply hnotE4
    refine ⟨mkA q m hq hlp d d', z1b q hq (by have := hlp.hm; omega) hlp.hK_le_tower
      hE1 hE2 (mkA q m hq hlp d d') vm e_enum (x_map d) (hx_inj d hd)
      (hE_iff d hd f₅) (hD_iff d hd f₅) (hR_xe d hd f₅) (v5 0 v1).2 ?_⟩
    intro i
    have ⟨hsub_i, hcard_i⟩ := v5 i.val (by omega)
    set A := zh q hq G₅ (mkA q m hq hlp d d') (x_map d ⟨i.val, by omega⟩)
    have vb : A ∈ Bc0_clean.powerset := mem_powerset.mpr hsub_i
    have v7 : A.card ≤ zd (m - 2) := by rw [hcard_i]; exact y6 (by omega)
    have hst := hGd.2 i
    change (∀ S ∈ (Bc_np.filter (fun z => G₅.Adj (x_map d ⟨i.val, by omega⟩) z)).powerset,
      ((Pool (Bc_np.filter (fun z => G₅.Adj (x_map d ⟨i.val, by omega⟩) z)) S).filter
        (fun u => G₅.Adj (x_map d ⟨i.val + 1, by omega⟩) u)).card = 1) ∧
      (∀ u ∈ Bc_np \ (Bc_np.filter (fun z => G₅.Adj (x_map d ⟨i.val, by omega⟩) z)).powerset.biUnion
        (Pool (Bc_np.filter (fun z => G₅.Adj (x_map d ⟨i.val, by omega⟩) z))),
        ¬ G₅.Adj (x_map d ⟨i.val + 1, by omega⟩) u) at hst
    rw [← v4 ⟨i.val, by omega⟩] at hst
    refine wb q hq G₅ (mkA q m hq hlp d d')
      (x_map d ⟨i.val, by omega⟩) (x_map d ⟨i.val + 1, by omega⟩) Bc_np
      (by rw [v4 ⟨i.val + 1, by omega⟩]; exact filter_subset _ _)
      (fun u hu => by
        rw [hBc_np_eq] at hu
        rcases mem_sdiff.mp hu with ⟨huBc, huNotP⟩
        have vq : u ∈ zr q m hq hlp G₅ := by rwa [vl.1]
        have vp : isBc q hq G₅ (mkA q m hq hlp d d') u := by
          rw [z0i]; exact (mem_filter.mp vq).2
        refine ⟨vp, ?_⟩
        rw [yl]; rintro (hP | rfl | rfl)
        · exact huNotP hP
        · exact (mem_filter.mp v8).2.2.1 (mem_filter.mp huBc).2
        · exact (mem_filter.mp v6).2.2.1 (mem_filter.mp huBc).2)
      (Pool A)
      (fun S hS => (hPool_sub A vb v7 S hS).trans (sdiff_subset.trans hBc0_sub))
      (fun S hS u huP z hzA => by
        have huC : u ∈ Bc0_clean := sdiff_subset (hPool_sub A vb v7 S hS huP)
        have hzC : z ∈ Bc0_clean := hsub_i hzA
        rw [hR_bc0 d hd f₅ u huC z hzC]
        exact hPool_pat A vb v7 S hS u huP z hzA)
      hst.1 hst.2
  have vk : z4 p (fun f₅ : {e // e ∉ S₄} → Bool =>
        z1 (z0 S₄ f₄ f₅) ∈
          EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ) ≤
      z4 p (fun f₅ : {e // e ∉ S₄} → Bool => ∀ d ∈ V2_star, ¬ GoodD d f₅) :=
    zi hp0 hp1 fun f₅ hbad d hd hGd => v9 d hd f₅ hGd hbad
  rw [y5 V2_star Td vf p (fun d f₅ => ¬ GoodD d f₅)
    (fun d hd f g hfg => not_congr (va d hd f g hfg))] at vk
  have hfac : ∀ d ∈ V2_star, z4 p (fun f₅ => ¬ GoodD d f₅) ≤ exp (-(QOf m)) := by
    intro d hd
    rw [wg]
    have hQ := z08 q m hlp S₄ f₄ (x_map d) (hx_inj d hd)
      Bc_np Bc0_clean hBc0_sub hBc_hi hBc0_lo (hx_not_B d hd) (hdisj_S4 d hd)
      Pool hPool_sub hPool_disj hPool_lo
    have h2 := Real.add_one_le_exp (-(QOf m))
    linarith
  have vr : (∏ d ∈ V2_star, z4 p (fun f₅ => ¬ GoodD d f₅)) ≤ 1 / 256 := by
    have vn := z1z m
    have vc := yi q m hlp
    calc (∏ d ∈ V2_star, z4 p (fun f₅ => ¬ GoodD d f₅))
        ≤ ∏ _d ∈ V2_star, exp (-(QOf m)) :=
          prod_le_prod (fun _ _ => ym hp0 hp1 _) hfac
      _ = (exp (-(QOf m))) ^ V2_star.card := prod_const _
      _ = exp ((V2_star.card : ℝ) * (-(QOf m))) := (exp_nat_mul _ _).symm
      _ ≤ exp (-((R8 : ℝ))) := by
          refine exp_le_exp.mpr ?_
          have hmul : (1 / 2 : ℝ) * ((R4Of m : ℝ) * QOf m) * QOf m ≤ (V2_star.card : ℝ) * QOf m :=
            mul_le_mul_of_nonneg_right hV2s_lo vn.le
          have hsq : (1 / 2 : ℝ) * ((R4Of m : ℝ) * QOf m) * QOf m = ((R4Of m : ℝ) * (QOf m) ^ 2) / 2 := by ring
          linarith [vc.1]
      _ ≤ 1 / 256 := vc.2.2.1
  exact vk.trans vr
private lemma z22 (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (S₃b : Finset (z6 (nOf q m)))
    (f₃b : {e : z6 (nOf q m) // e ∈ S₃b} → Bool)
    (d' : Fin (nOf q m))
    (V0 V1 V2 E Bc_np Bc'_np Bc'0 Bc0_clean : Finset (Fin (nOf q m)))
    (e_enum : Fin m → Fin (nOf q m))
    (P_dom : Fin m → Finset (Fin (nOf q m)))
    (Pool : Finset (Fin (nOf q m)) → Finset (Fin (nOf q m)) → Finset (Fin (nOf q m)))
    (hS0_sub : ze (zn q m hq hlp) ⊆ S₃b)
    (hd'_V0 : d' ∈ V0)
    (hV0_sub : V0 ⊆ zj q m hq hlp (z1 (z0 S₃b f₃b (fun _ => false))))
    (hV1_sub : V1 ⊆ zj q m hq hlp (z1 (z0 S₃b f₃b (fun _ => false))))
    (hV2_sub : V2 ⊆ zj q m hq hlp (z1 (z0 S₃b f₃b (fun _ => false))))
    (hV2_card : V2.card = R4Of m)
    (hV01 : Disjoint V0 V1) (hV02 : Disjoint V0 V2) (hV12 : Disjoint V1 V2)
    (hV_cover : zj q m hq hlp (z1 (z0 S₃b f₃b (fun _ => false))) ⊆ V0 ∪ V1 ∪ V2)
    (hBc_np_eq : Bc_np = zr q m hq hlp (z1 (z0 S₃b f₃b (fun _ => false))) \ zn q m hq hlp)
    (hBc'_np_eq : Bc'_np = zp q m hq hlp (z1 (z0 S₃b f₃b (fun _ => false))) \ zn q m hq hlp)
    (hBc'0_eq : Bc'0 = Bc'_np \ Bc_np)
    (_hE_sub : E ⊆ Bc'0)
    (hBc0_sub : Bc0_clean ⊆ Bc_np)
    (hBc_hi : (Bc_np.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc'_hi : (Bc'_np.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc0_lo : (ROf m : ℝ) / 5 ≤ (Bc0_clean.card : ℝ))
    (hdisj_S3b_V2 : Disjoint S₃b (z8 V2 (Bc'_np \ E)))
    (hdisj_S3b_6 : Disjoint S₃b (z8 (Bc'0 \ E) Bc_np))
    (hV2_no_E : ∀ d ∈ V2, ∀ z ∈ E, ∀ f : {e // e ∉ S₃b} → Bool, ¬ (z1 (z0 S₃b f₃b f)).Adj d z)
    (hE_iff : ∀ d ∈ V2, ∀ f : {e // e ∉ S₃b} → Bool, ∀ z : Fin (nOf q m),
      inE q hq (z1 (z0 S₃b f₃b f)) (mkA q m hq hlp d d') z ↔ ∃ j : Fin m, z = e_enum j)
    (hP_sub : ∀ i : Fin m, P_dom i ⊆ Bc'0 \ E)
    (hP_disj : Set.PairwiseDisjoint ((univ : Finset (Fin m)) : Set (Fin m)) P_dom)
    (hP_lo : ∀ i : Fin m, ((1 / 12 : ℝ) * exp (-13 * (m : ℝ))) * (ROf m : ℝ) ≤ ((P_dom i).card : ℝ))
    (hP_R : ∀ d ∈ V2, ∀ f : {e // e ∉ S₃b} → Bool, ∀ i : Fin m, ∀ u ∈ P_dom i, ∀ j : Fin m,
      Rrel q hq (z1 (z0 S₃b f₃b f)) (mkA q m hq hlp d d') u (e_enum j) ↔ j.val ≤ i.val)
    (hR_bc0 : ∀ d ∈ V2, ∀ f : {e // e ∉ S₃b} → Bool, ∀ u ∈ Bc0_clean, ∀ z ∈ Bc0_clean,
      Rrel q hq (z1 (z0 S₃b f₃b f)) (mkA q m hq hlp d d') u z ↔
        ∃ w ∈ V1, (z1 (z0 S₃b f₃b (fun _ => false))).Adj w u ∧
          (z1 (z0 S₃b f₃b (fun _ => false))).Adj w z)
    (hPool_sub : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      ∀ S ∈ A.powerset, Pool A S ⊆ Bc0_clean \ A)
    (hPool_disj : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      Set.PairwiseDisjoint (A.powerset : Set (Finset (Fin (nOf q m)))) (Pool A))
    (hPool_lo : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      ∀ S ∈ A.powerset, ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (ROf m : ℝ) ≤
        ((Pool A S).card : ℝ))
    (hPool_pat : ∀ A ∈ Bc0_clean.powerset, A.card ≤ zd (m - 2) →
      ∀ S ∈ A.powerset, ∀ u ∈ Pool A S, ∀ z ∈ A,
        (∃ w ∈ V1, (z1 (z0 S₃b f₃b (fun _ => false))).Adj w u ∧
          (z1 (z0 S₃b f₃b (fun _ => false))).Adj w z) ↔ z ∈ S) :
    z4 ((ROf m : ℝ)⁻¹) (fun f_rem : {e : z6 (nOf q m) // e ∉ S₃b} → Bool =>
      z1 (z0 S₃b f₃b f_rem) ∈
        EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ) ≤
      3 / 256 := by
  classical
  set R := ROf m
  set R4 := R4Of m
  set R8 := R8Of m
  set T := zd (m - 1)
  set p : ℝ := (R : ℝ)⁻¹
  have vq : R8 ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have ua : 10000 ≤ R := le_trans hlp.hR8_ge vq
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  let G₃ := z1 (z0 S₃b f₃b (fun _ => false))
  let W := Bc'_np \ E
  have v0 : Disjoint V2 W := by
    rw [disjoint_left]; intro v hvV hvW
    have hvBb := hV2_sub hvV
    have hvBc' : v ∈ zp q m hq hlp G₃ := by
      have := sdiff_subset hvW; rw [hBc'_np_eq] at this; exact sdiff_subset this
    exact (mem_filter.mp hvBb).2.2.2.1 (mem_filter.mp hvBc').2
  have vw : (W.card : ℝ) ≤ 2 * (R : ℝ) :=
    (Nat.cast_le.mpr (card_le_card sdiff_subset)).trans hBc'_hi
  have v6 : ∀ i : Fin m, P_dom i ⊆ W := fun i u hu => by
    rcases mem_sdiff.mp (hP_sub i hu) with ⟨hu0, huE⟩
    rw [hBc'0_eq] at hu0
    exact mem_sdiff.mpr ⟨sdiff_subset hu0, huE⟩
  let S₄ : Finset (z6 (nOf q m)) := S₃b ∪ z8 V2 W
  let DomGood : Fin (nOf q m) → (z6 (nOf q m) → Bool) → Prop := fun d f =>
    (∀ i : Fin m, ((P_dom i).filter (fun u => (z1 f).Adj d u)).card = 1) ∧
    (∀ u ∈ W \ (univ : Finset (Fin m)).biUnion P_dom, ¬ (z1 f).Adj d u)
  let Good5 : (z6 (nOf q m) → Bool) → Prop := fun f =>
    (∀ d₁ ∈ V2, ∀ d₂ ∈ V2, d₁ ≠ d₂ → ∀ z ∈ W, ¬ ((z1 f).Adj d₁ z ∧ (z1 f).Adj d₂ z)) ∧
    ((1 / 2 : ℝ) * ((R4 : ℝ) * QOf m) ≤ ((V2.filter (fun d => DomGood d f)).card : ℝ))
  have ve : ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ S₄, f e = g e) → (Good5 f ↔ Good5 g) := by
    intro f g hfg
    have hadj : ∀ d ∈ V2, ∀ u ∈ W, (z1 f).Adj d u ↔ (z1 g).Adj d u := by
      intro d hd u hu
      have hne : d ≠ u := fun h => disjoint_left.mp v0 hd (h ▸ hu)
      rw [za f hne, za g hne,
        hfg _ (mem_union_right _ ((z5 V2 W hne).mpr (Or.inl ⟨hd, hu⟩)))]
    refine and_congr ?_ ?_
    · exact forall₂_congr fun d₁ hd₁ => forall₂_congr fun d₂ hd₂ => imp_congr_right fun _ =>
        forall₂_congr fun z hz => not_congr (and_congr (hadj d₁ hd₁ z hz) (hadj d₂ hd₂ z hz))
    · have hDG : ∀ d ∈ V2, DomGood d f ↔ DomGood d g := fun d hd =>
        and_congr
          (forall_congr' fun i => by rw [filter_congr fun u hu => hadj d hd u (v6 i hu)])
          (forall₂_congr fun u hu => not_congr (hadj d hd u (sdiff_subset hu)))
      rw [filter_congr hDG]
  refine (zu hp0 hp1 S₃b S₄ subset_union_left f₃b Good5
    (fun f => z1 f ∈ EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ)
    ve (ε₁ := 2 / 256) (ε₂ := 1 / 256) (by norm_num) ?_ ?_).trans (by norm_num)
  ·
    have ug : z4 p (fun f_rem : {e // e ∉ S₃b} → Bool =>
          ¬ ∀ d₁ ∈ V2, ∀ d₂ ∈ V2, d₁ ≠ d₂ → ∀ z ∈ W,
            ¬ ((z1 (z0 S₃b f₃b f_rem)).Adj d₁ z ∧
               (z1 (z0 S₃b f₃b f_rem)).Adj d₂ z)) ≤ 1 / 256 := by
      have u8 : z4 p (fun f_rem : {e // e ∉ S₃b} → Bool =>
            ¬ ∀ d₁ ∈ V2, ∀ d₂ ∈ V2, d₁ ≠ d₂ → ∀ z ∈ W,
              ¬ ((z1 (z0 S₃b f₃b f_rem)).Adj d₁ z ∧
                 (z1 (z0 S₃b f₃b f_rem)).Adj d₂ z)) ≤
          z4 p (fun f_rem : {e // e ∉ S₃b} → Bool =>
            ∃ d₁ ∈ V2, ∃ d₂ ∈ V2, d₁ ≠ d₂ ∧ ∃ z ∈ W,
              (∃ (h : d₁ ≠ z) (hmem : z7 d₁ z h ∉ S₃b), f_rem ⟨z7 d₁ z h, hmem⟩ = true) ∧
              (∃ (h : d₂ ≠ z) (hmem : z7 d₂ z h ∉ S₃b), f_rem ⟨z7 d₂ z h, hmem⟩ = true)) := by
        refine zi hp0 hp1 fun f_rem hnot => ?_
        push Not at hnot
        rcases hnot with ⟨d₁, hd₁, d₂, hd₂, hne, z, hz, ha1, ha2⟩
        have hne1 : d₁ ≠ z := fun h => disjoint_left.mp v0 hd₁ (h ▸ hz)
        have hne2 : d₂ ≠ z := fun h => disjoint_left.mp v0 hd₂ (h ▸ hz)
        have u7 : z7 d₁ z hne1 ∉ S₃b := disjoint_right.mp hdisj_S3b_V2
          ((z5 V2 W hne1).mpr (Or.inl ⟨hd₁, hz⟩))
        have u6 : z7 d₂ z hne2 ∉ S₃b := disjoint_right.mp hdisj_S3b_V2
          ((z5 V2 W hne2).mpr (Or.inl ⟨hd₂, hz⟩))
        exact ⟨d₁, hd₁, d₂, hd₂, hne, z, hz,
          (zb S₃b f₃b f_rem hne1 u7).mp ha1,
          (zb S₃b f₃b f_rem hne2 u6).mp ha2⟩
      refine u8.trans ((wi hp0 hp1 S₃b V2 W v0 hdisj_S3b_V2).trans ?_)
      have uh : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (R_pos m)
      have ud : (0 : ℝ) < (R2Of m : ℝ) := Nat.cast_pos.mpr (Nat.two_pow_pos _)
      have ub : (R : ℝ) = (R2Of m : ℝ) ^ 2 := by exact_mod_cast z15 m
      have u3 : (R2Of m : ℝ) = (R4 : ℝ) ^ 2 := by exact_mod_cast z2f m
      have u9 : ((V2.card : ℝ) ^ 2) * (W.card : ℝ) * p ^ 2 ≤ 2 / (R2Of m : ℝ) := by
        rw [hV2_card]
        calc ((R4 : ℝ) ^ 2) * (W.card : ℝ) * p ^ 2
            ≤ ((R4 : ℝ) ^ 2) * (2 * (R : ℝ)) * p ^ 2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left vw (by positivity)) (by positivity)
          _ = 2 / (R2Of m : ℝ) := by
              rw [show p = (R : ℝ)⁻¹ from rfl, ← u3, ub]; field_simp
      exact u9.trans (yi q m hlp).2.2.2.1
    have uf : z4 p (fun f_rem : {e // e ∉ S₃b} → Bool =>
          ((V2.filter (fun d => DomGood d (z0 S₃b f₃b f_rem))).card : ℝ) <
            (1 / 2 : ℝ) * ((R4 : ℝ) * QOf m)) ≤ 1 / 256 := by
      let Td : Fin (nOf q m) → Finset {e : z6 (nOf q m) // e ∉ S₃b} := fun d =>
        if hd : d ∈ V2 then
          W.attach.image (fun (u : {v // v ∈ W}) =>
            have hne : d ≠ u.1 := fun h => disjoint_left.mp v0 hd (h ▸ u.2)
            ⟨z7 d u.1 hne, disjoint_right.mp hdisj_S3b_V2
              ((z5 V2 W hne).mpr (Or.inl ⟨hd, u.2⟩))⟩)
        else ∅
      have vp : Set.PairwiseDisjoint (V2 : Set (Fin (nOf q m))) Td := by
        intro d₁ hd₁ d₂ hd₂ hne
        have hd₁' : d₁ ∈ V2 := mem_coe.mp hd₁
        have hd₂' : d₂ ∈ V2 := mem_coe.mp hd₂
        change Disjoint (Td d₁) (Td d₂)
        rw [disjoint_left]; intro e he₁ he₂
        dsimp only [Td] at he₁ he₂; rw [dif_pos hd₁'] at he₁; rw [dif_pos hd₂'] at he₂
        rcases mem_image.mp he₁ with ⟨u₁, _, rfl⟩
        rcases mem_image.mp he₂ with ⟨u₂, _, heq⟩
        rcases zv heq with ⟨hdd, _⟩ | ⟨hdu, _⟩
        · exact hne hdd.symm
        · exact disjoint_left.mp v0 hd₂' (hdu ▸ u₁.2)
      have hdep : ∀ d ∈ V2, ∀ f g : {e // e ∉ S₃b} → Bool, (∀ x ∈ Td d, f x = g x) →
          (DomGood d (z0 S₃b f₃b f) ↔ DomGood d (z0 S₃b f₃b g)) := by
        intro d hd f g hfg
        have hadj : ∀ u (hu : u ∈ W),
            (z1 (z0 S₃b f₃b f)).Adj d u ↔ (z1 (z0 S₃b f₃b g)).Adj d u := by
          intro u hu
          have hne : d ≠ u := fun h => disjoint_left.mp v0 hd (h ▸ hu)
          have hnot : z7 d u hne ∉ S₃b := disjoint_right.mp hdisj_S3b_V2
            ((z5 V2 W hne).mpr (Or.inl ⟨hd, hu⟩))
          have hmem : (⟨z7 d u hne, hnot⟩ : {e // e ∉ S₃b}) ∈ Td d := by
            dsimp only [Td]; rw [dif_pos hd]
            exact mem_image.mpr ⟨⟨u, hu⟩, mem_attach _ _, rfl⟩
          rw [zb S₃b f₃b f hne hnot, zb S₃b f₃b g hne hnot]
          have heq := hfg _ hmem
          exact ⟨fun ⟨_, _, hf⟩ => ⟨hne, hnot, by rwa [← heq]⟩, fun ⟨_, _, hg⟩ => ⟨hne, hnot, by rwa [heq]⟩⟩
        exact and_congr
          (forall_congr' fun i => by rw [filter_congr fun u hu => hadj u (v6 i hu)])
          (forall₂_congr fun u hu => not_congr (hadj u (sdiff_subset hu)))
      have vr : ∀ d ∈ V2, QOf m ≤ z4 p (fun f_rem => DomGood d (z0 S₃b f₃b f_rem)) := by
        intro d hd
        have vg : d ∉ W := fun h => disjoint_left.mp v0 hd h
        have vf : Disjoint S₃b (z8 {d} W) := by
          refine hdisj_S3b_V2.mono_right fun ⟨e, he⟩ he1 => ?_
          induction e using Sym2.ind with
          | _ u v =>
            have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
            change z7 u v huv ∈ z8 V2 W
            rw [z5 V2 W huv]
            rcases (z5 {d} W huv).mp he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨mem_singleton.mp h1 ▸ hd, h2⟩
            · exact Or.inr ⟨mem_singleton.mp h1 ▸ hd, h2⟩
        let vc : ℝ := (1 / 12 : ℝ) * exp (-13 * (m : ℝ))
        have hEO := yo ua S₃b d W vg vw vf
          (univ : Finset (Fin m)) P_dom (fun i _ => v6 i) hP_disj
          (by positivity : 0 ≤ vc) (fun i _ => hP_lo i)
        have uc : QOf m ≤ vc ^ (univ : Finset (Fin m)).card * exp (-4 : ℝ) := by
          rw [Finset.card_univ, Fintype.card_fin]
          have u0 : exp (-13 * (m : ℝ) - 3) ≤ vc := by
            dsimp only [vc]
            have h12 : exp (-3 : ℝ) ≤ (1 / 12 : ℝ) := by
              have hsum := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 5
              simp [sum_range_succ, Nat.factorial] at hsum
              rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
              linarith
            calc exp (-13 * (m : ℝ) - 3)
                = exp (-3 : ℝ) * exp (-13 * (m : ℝ)) := by rw [← exp_add]; congr 1; ring
              _ ≤ (1 / 12 : ℝ) * exp (-13 * (m : ℝ)) := mul_le_mul_of_nonneg_right h12 (exp_pos _).le
          have h1 : QOf m ≤ exp ((m : ℝ) * (-13 * (m : ℝ) - 3) - 4) := by
            change exp (-(20 * (m : ℝ) * (T : ℝ) ^ 2 + 100)) ≤ _
            refine exp_le_exp.mpr ?_
            have hmT : (m : ℝ) ≤ (T : ℝ) := by exact_mod_cast y9 m (by have := hlp.hm; omega)
            have hm10 : (10 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlp.hm
            nlinarith only [hmT, hm10]
          calc QOf m ≤ exp ((m : ℝ) * (-13 * (m : ℝ) - 3) - 4) := h1
            _ = exp ((m : ℝ) * (-13 * (m : ℝ) - 3)) * exp (-4 : ℝ) := by rw [← exp_add]; rfl
            _ = (exp (-13 * (m : ℝ) - 3)) ^ m * exp (-4 : ℝ) := by rw [exp_nat_mul]
            _ ≤ vc ^ m * exp (-4 : ℝ) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (exp_pos _).le u0 m) (exp_pos _).le
        refine uc.trans (hEO.trans (zi hp0 hp1 fun f_rem ⟨hex, hzr⟩ => ?_))
        have hadj : ∀ u ∈ W, (z1 (z0 S₃b f₃b f_rem)).Adj d u ↔
            ∃ (h : d ≠ u) (hmem : z7 d u h ∉ S₃b), f_rem ⟨z7 d u h, hmem⟩ = true := by
          intro u hu
          have hne : d ≠ u := fun h => vg (h ▸ hu)
          have hnot : z7 d u hne ∉ S₃b := disjoint_right.mp vf
            ((z5 {d} W hne).mpr (Or.inl ⟨mem_singleton_self _, hu⟩))
          exact zb S₃b f₃b f_rem hne hnot
        refine ⟨fun i => ?_, fun u hu => ?_⟩
        · rw [filter_congr fun u hu => hadj u (v6 i hu)]; exact hex i (mem_univ _)
        · rw [hadj u (sdiff_subset hu)]; exact hzr u hu
      have hch := yx V2 Td vp hp0 hp1
        (fun d f_rem => DomGood d (z0 S₃b f₃b f_rem)) hdep (z1z m).le vr
      rw [hV2_card] at hch
      have hexp : exp (-((R4 : ℝ) * QOf m) / 8) ≤ 1 / 256 :=
        (exp_le_exp.mpr (by linarith [(yi q m hlp).2.1])).trans (yi q m hlp).2.2.1
      exact hch.trans hexp
    have ue : z4 p (fun f_rem : {e // e ∉ S₃b} → Bool => ¬ Good5 (z0 S₃b f₃b f_rem)) ≤
        z4 p (fun f_rem => ¬ ∀ d₁ ∈ V2, ∀ d₂ ∈ V2, d₁ ≠ d₂ → ∀ z ∈ W,
          ¬ ((z1 (z0 S₃b f₃b f_rem)).Adj d₁ z ∧ (z1 (z0 S₃b f₃b f_rem)).Adj d₂ z)) +
        z4 p (fun f_rem => ((V2.filter (fun d => DomGood d (z0 S₃b f₃b f_rem))).card : ℝ) <
          (1 / 2 : ℝ) * ((R4 : ℝ) * QOf m)) := by
      refine (zi hp0 hp1 fun f_rem hnot => ?_).trans (yr hp0 hp1 _ _)
      dsimp only [Good5] at hnot; rw [not_and_or, not_le] at hnot; exact hnot
    linarith
  ·
    intro f₄ hagree hGood5
    rcases hGood5 (fun _ => false) with ⟨hNoShare, hV2s_lo⟩
    let G₄ := z1 (z0 S₄ f₄ (fun _ => false))
    let v2 := V2.filter (fun d => DomGood d (z0 S₄ f₄ (fun _ => false)))
    have v1 : v2 ⊆ V2 := filter_subset _ _
    have v9 : ∀ f₅ : {e // e ∉ S₄} → Bool, ∀ e ∈ S₃b,
        z0 S₄ f₄ f₅ e = z0 S₃b f₃b (fun _ => false) e := fun f₅ e he => by
      have he4 : e ∈ S₄ := subset_union_left he
      simp only [z0, dif_pos he4, dif_pos he]; exact hagree ⟨e, he⟩
    have va : ∀ f₅ : {e // e ∉ S₄} → Bool, ∃ f' : {e // e ∉ S₃b} → Bool,
        z0 S₄ f₄ f₅ = z0 S₃b f₃b f' := by
      intro f₅
      refine ⟨fun x => z0 S₄ f₄ f₅ x.1, ?_⟩
      funext e; by_cases h : e ∈ S₃b
      · have heq := v9 f₅ e h; simp only [z0, dif_pos h] at heq ⊢; exact heq
      · simp only [z0, dif_neg h]
    have vb := zz q m hq hlp (z0 S₄ f₄ (fun _ => false))
      (z0 S₃b f₃b (fun _ => false)) (fun e he => v9 (fun _ => false) e (hS0_sub he))
    have vt : ∀ d ∈ v2, ∀ i : Fin m,
        ∃ u ∈ P_dom i, G₄.Adj d u ∧ ∀ v ∈ P_dom i, G₄.Adj d v → v = u := by
      intro d hd i
      have u2 := (mem_filter.mp hd).2.1 i
      rcases card_eq_one.mp u2 with ⟨u, hu⟩
      have vz : u ∈ (P_dom i).filter (fun u => G₄.Adj d u) := by rw [hu]; exact mem_singleton_self u
      rcases mem_filter.mp vz with ⟨huP, hadj⟩
      refine ⟨u, huP, hadj, fun v hvP hvadj => ?_⟩
      have vj : v ∈ (P_dom i).filter (fun u => G₄.Adj d u) := mem_filter.mpr ⟨hvP, hvadj⟩
      rw [hu, mem_singleton] at vj; exact vj
    let v3 : Fin (nOf q m) → Fin m → Fin (nOf q m) := fun d i =>
      if hd : d ∈ v2 then Classical.choose (vt d hd i) else d
    have v5 : ∀ d ∈ v2, ∀ i : Fin m,
        v3 d i ∈ P_dom i ∧ G₄.Adj d (v3 d i) ∧ ∀ v ∈ P_dom i, G₄.Adj d v → v = v3 d i := by
      intro d hd i
      dsimp only [v3]; rw [dif_pos hd]
      exact Classical.choose_spec (vt d hd i)
    have vx : ∀ d ∈ v2, Function.Injective (v3 d) := by
      intro d hd i₁ i₂ heq
      by_contra hne
      have h1 := (v5 d hd i₁).1
      have h2 := (v5 d hd i₂).1
      exact disjoint_left.mp (hP_disj (mem_coe.mpr (mem_univ i₁))
        (mem_coe.mpr (mem_univ i₂)) hne) h1 (heq ▸ h2)
    have vi : ∀ d ∈ v2, ∀ i : Fin m, v3 d i ∉ Bc_np := by
      intro d hd i hB
      have h0 : v3 d i ∈ Bc'0 := sdiff_subset (hP_sub i (v5 d hd i).1)
      rw [hBc'0_eq] at h0; exact (mem_sdiff.mp h0).2 hB
    have vh : ∀ d₁ ∈ v2, ∀ d₂ ∈ v2, d₁ ≠ d₂ →
        Disjoint (univ.image (v3 d₁)) (univ.image (v3 d₂)) := by
      intro d₁ hd₁ d₂ hd₂ hne
      rw [disjoint_left]; intro u hu1 hu2
      rcases mem_image.mp hu1 with ⟨i₁, _, rfl⟩
      rcases mem_image.mp hu2 with ⟨i₂, _, heq⟩
      have h1 := v5 d₁ hd₁ i₁
      have h2 := v5 d₂ hd₂ i₂
      exact hNoShare d₁ (v1 hd₁) d₂ (v1 hd₂) hne (v3 d₁ i₁) (v6 i₁ h1.1)
        ⟨h1.2.1, heq ▸ h2.2.1⟩
    have vn : ∀ d ∈ v2, Disjoint S₄ (z8 (univ.image (v3 d)) Bc_np) := by
      intro d hd
      have v8 : univ.image (v3 d) ⊆ Bc'0 \ E := fun u hu => by
        rcases mem_image.mp hu with ⟨i, _, rfl⟩; exact hP_sub i (v5 d hd i).1
      rw [disjoint_union_left]
      refine ⟨?_, ?_⟩
      · refine hdisj_S3b_6.mono_right fun ⟨e, he⟩ he1 => ?_
        induction e using Sym2.ind with
        | _ u v =>
          have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
          change z7 u v huv ∈ z8 (Bc'0 \ E) Bc_np
          rw [z5 (Bc'0 \ E) Bc_np huv]
          rcases (z5 _ _ huv).mp he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨v8 h1, h2⟩
          · exact Or.inr ⟨v8 h1, h2⟩
      · rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
        induction e using Sym2.ind with
        | _ u v =>
          have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
          have v4 : Disjoint V2 Bc_np := by
            rw [disjoint_left]; intro w hwV hwB
            rw [hBc_np_eq] at hwB
            exact (mem_filter.mp (hV2_sub hwV)).2.2.1 (mem_filter.mp (sdiff_subset hwB)).2
          have v7 : Disjoint V2 (Bc'0 \ E) := v0.mono_right fun z hz => by
            rcases mem_sdiff.mp hz with ⟨h0, hE⟩; rw [hBc'0_eq] at h0
            exact mem_sdiff.mpr ⟨sdiff_subset h0, hE⟩
          rcases (z5 V2 W huv).mp he1 with ⟨huV, _⟩ | ⟨hvV, _⟩ <;>
            rcases (z5 _ _ huv).mp he2 with ⟨huI, hvB⟩ | ⟨hvI, huB⟩
          · exact disjoint_left.mp v7 huV (v8 huI)
          · exact disjoint_left.mp v4 huV huB
          · exact disjoint_left.mp v4 hvV hvB
          · exact disjoint_left.mp v7 hvV (v8 hvI)
    have u4 : ∀ d ∈ v2, ∀ f₅ : {e // e ∉ S₄} → Bool, ∀ v : Fin (nOf q m),
        inDom q hq (z1 (z0 S₄ f₄ f₅)) (mkA q m hq hlp d d') v ↔ ∃ i : Fin m, v = v3 d i := by
      intro d hd f₅ v
      let G₅ := z1 (z0 S₄ f₄ f₅)
      have vu := zz q m hq hlp (z0 S₄ f₄ f₅) (z0 S₃b f₃b (fun _ => false))
        (fun e he => v9 f₅ e (hS0_sub he))
      have u1 := hV2_sub (v1 hd)
      have vs := hV0_sub hd'_V0
      have vo : ∀ u ∈ W, G₅.Adj d u ↔ G₄.Adj d u := fun u hu => by
        have hne : d ≠ u := fun h => disjoint_left.mp v0 (v1 hd) (h ▸ hu)
        have hmem : z7 d u hne ∈ S₄ :=
          mem_union_right _ ((z5 V2 W hne).mpr (Or.inl ⟨v1 hd, hu⟩))
        rw [zf S₄ f₄ f₅ hne hmem, zf S₄ f₄ (fun _ => false) hne hmem]
      constructor
      · rintro ⟨hbc', hadj, hnp⟩
        rw [z14] at hadj
        have vl : v ∈ Bc'_np := by
          rw [hBc'_np_eq]
          refine mem_sdiff.mpr ⟨?_, fun hP => hnp ((yl q m hq hlp d d' v).mpr (Or.inl hP))⟩
          rw [← vu.2.1]; exact mem_filter.mpr ⟨mem_univ _, (w8 q m hq hlp G₅ d d' v).mp hbc'⟩
        have vy : v ∉ E := by
          intro hvE
          rcases va f₅ with ⟨f', hf'⟩
          exact hV2_no_E d (v1 hd) v hvE f' (by change (z1 (z0 S₄ f₄ f₅)).Adj v d at hadj; rw [hf'] at hadj; exact hadj.symm)
        have hvW : v ∈ W := mem_sdiff.mpr ⟨vl, vy⟩
        have vv : G₄.Adj d v := (vo v hvW).mp hadj.symm
        have vk : v ∈ (univ : Finset (Fin m)).biUnion P_dom := by
          by_contra hnot
          exact (mem_filter.mp hd).2.2 v (mem_sdiff.mpr ⟨hvW, hnot⟩) vv
        rcases mem_biUnion.mp vk with ⟨i, _, hvP⟩
        exact ⟨i, (v5 d hd i).2.2 v hvP vv⟩
      · rintro ⟨i, rfl⟩
        have hsp := v5 d hd i
        have hxW : v3 d i ∈ W := v6 i hsp.1
        have vd : v3 d i ∈ Bc'_np := sdiff_subset hxW
        rw [hBc'_np_eq] at vd
        rcases mem_sdiff.mp vd with ⟨hxBc', hxNotP⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [w8]
          have : v3 d i ∈ zp q m hq hlp G₅ := by rwa [vu.2.1]
          exact (mem_filter.mp this).2
        · rw [z14]; exact ((vo _ hxW).mpr hsp.2.1).symm
        · rw [yl]; rintro (hP | heq | heq)
          · exact hxNotP hP
          · exact (mem_filter.mp u1).2.2.2.1 (heq ▸ (mem_filter.mp hxBc').2)
          · exact (mem_filter.mp vs).2.2.2.1 (heq ▸ (mem_filter.mp hxBc').2)
    exact z21 q m hq hlp S₄ f₄ d' V0 V1 V2 v2 E Bc_np Bc'_np Bc0_clean e_enum v3 Pool
      (hS0_sub.trans subset_union_left) hd'_V0
      (vb.2.2.symm ▸ hV0_sub) (vb.2.2.symm ▸ hV1_sub) (vb.2.2.symm ▸ hV2_sub) v1
      hV01 hV02 hV12 (vb.2.2.symm ▸ hV_cover)
      (vb.1.symm ▸ hBc_np_eq) (vb.2.1.symm ▸ hBc'_np_eq)
      hBc0_sub hBc_hi hBc0_lo hV2s_lo vx vi vh vn
      (fun d hd f₅ z => by rcases va f₅ with ⟨f', hf'⟩; rw [hf']; exact hE_iff d (v1 hd) f' z)
      u4
      (fun d hd f₅ i j => by
        rcases va f₅ with ⟨f', hf'⟩; rw [hf']
        exact hP_R d (v1 hd) f' i (v3 d i) (v5 d hd i).1 j)
      (fun d hd f₅ u hu z hz => by
        rcases va f₅ with ⟨f', hf'⟩; rw [hf']
        rw [hR_bc0 d (v1 hd) f' u hu z hz]
        have h4eq : ∀ w ∈ V1, ∀ v ∈ Bc0_clean, G₄.Adj w v ↔ G₃.Adj w v := fun w hw v hv => by
          have hne : w ≠ v := fun h => by
            have hvB : v ∈ zr q m hq hlp G₃ := sdiff_subset (hBc_np_eq ▸ hBc0_sub hv)
            exact (mem_filter.mp (hV1_sub hw)).2.2.1 (h ▸ (mem_filter.mp hvB).2)
          by_cases hmem : z7 w v hne ∈ S₃b
          · rw [za _ hne, za _ hne, v9 (fun _ => false) _ hmem]
          · have vm : z7 w v hne ∉ S₄ := by
              intro h4
              rcases mem_union.mp h4 with h3 | h2W
              · exact hmem h3
              · rcases (z5 V2 W hne).mp h2W with ⟨hw2, _⟩ | ⟨hv2, _⟩
                · exact disjoint_left.mp hV12 hw hw2
                · have hvB : v ∈ zr q m hq hlp G₃ := sdiff_subset (hBc_np_eq ▸ hBc0_sub hv)
                  exact (mem_filter.mp (hV2_sub hv2)).2.2.1 (mem_filter.mp hvB).2
            rw [zb S₄ f₄ (fun _ => false) hne vm,
              zb S₃b f₃b (fun _ => false) hne hmem]
            simp
        exact exists_congr fun w => and_congr_right fun hw => and_congr (h4eq w hw u hu).symm (h4eq w hw z hz).symm)
      hPool_sub hPool_disj hPool_lo
      (fun A hA hAc S hS u hu z hz => by
        have huC : u ∈ Bc0_clean := sdiff_subset (hPool_sub A hA hAc S hS hu)
        have hzC : z ∈ Bc0_clean := mem_powerset.mp hA hz
        have h4eq : ∀ w ∈ V1, ∀ v ∈ Bc0_clean, G₄.Adj w v ↔ G₃.Adj w v := fun w hw v hv => by
          have hne : w ≠ v := fun h => by
            have hvB : v ∈ zr q m hq hlp G₃ := sdiff_subset (hBc_np_eq ▸ hBc0_sub hv)
            exact (mem_filter.mp (hV1_sub hw)).2.2.1 (h ▸ (mem_filter.mp hvB).2)
          by_cases hmem : z7 w v hne ∈ S₃b
          · rw [za _ hne, za _ hne, v9 (fun _ => false) _ hmem]
          · have vm : z7 w v hne ∉ S₄ := by
              intro h4
              rcases mem_union.mp h4 with h3 | h2W
              · exact hmem h3
              · rcases (z5 V2 W hne).mp h2W with ⟨hw2, _⟩ | ⟨hv2, _⟩
                · exact disjoint_left.mp hV12 hw hw2
                · have hvB : v ∈ zr q m hq hlp G₃ := sdiff_subset (hBc_np_eq ▸ hBc0_sub hv)
                  exact (mem_filter.mp (hV2_sub hv2)).2.2.1 (mem_filter.mp hvB).2
            rw [zb S₄ f₄ (fun _ => false) hne vm,
              zb S₃b f₃b (fun _ => false) hne hmem]
            simp
        rw [← hPool_pat A hA hAc S hS u hu z hz]
        exact exists_congr fun w => and_congr_right fun hw => and_congr (h4eq w hw u huC) (h4eq w hw z hzC))
private lemma z1v (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (S₃a : Finset (z6 (nOf q m)))
    (f₃a : {e : z6 (nOf q m) // e ∈ S₃a} → Bool)
    (d' : Fin (nOf q m))
    (V0 V1 V2 E Bc_np Bc'_np Bc0 Bc'0 : Finset (Fin (nOf q m)))
    (e_enum : Fin m → Fin (nOf q m))
    (P_dom : Fin m → Finset (Fin (nOf q m)))
    (hS0_sub : ze (zn q m hq hlp) ⊆ S₃a)
    (hd'_V0 : d' ∈ V0)
    (hV0_sub : V0 ⊆ zj q m hq hlp (z1 (z0 S₃a f₃a (fun _ => false))))
    (hV1_sub : V1 ⊆ zj q m hq hlp (z1 (z0 S₃a f₃a (fun _ => false))))
    (hV2_sub : V2 ⊆ zj q m hq hlp (z1 (z0 S₃a f₃a (fun _ => false))))
    (hV0_card : V0.card = R4Of m) (hV2_card : V2.card = R4Of m)
    (hV1_lo : (1 / 12 : ℝ) * ((ROf m : ℝ) ^ 2) ≤ (V1.card : ℝ))
    (hV1_hi : (V1.card : ℝ) ≤ 2 * ((ROf m : ℝ) ^ 2))
    (hV01 : Disjoint V0 V1) (hV02 : Disjoint V0 V2) (hV12 : Disjoint V1 V2)
    (hV_cover : zj q m hq hlp (z1 (z0 S₃a f₃a (fun _ => false))) ⊆ V0 ∪ V1 ∪ V2)
    (hBc_np_eq : Bc_np = zr q m hq hlp (z1 (z0 S₃a f₃a (fun _ => false))) \ zn q m hq hlp)
    (hBc'_np_eq : Bc'_np = zp q m hq hlp (z1 (z0 S₃a f₃a (fun _ => false))) \ zn q m hq hlp)
    (hBc0_eq : Bc0 = Bc_np \ Bc'_np) (hBc'0_eq : Bc'0 = Bc'_np \ Bc_np)
    (hE_sub : E ⊆ Bc'0)
    (hBc_hi : (Bc_np.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc'_hi : (Bc'_np.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc0_lo : (ROf m : ℝ) / 4 ≤ (Bc0.card : ℝ))
    (hdisj_S3a_Bb0_Bc0 : Disjoint S₃a (z8 (V0 ∪ V1 ∪ V2) Bc0))
    (hdisj_S3a_V2 : Disjoint S₃a (z8 V2 (Bc'_np \ E)))
    (hdisj_S3a_6 : Disjoint S₃a (z8 (Bc'0 \ E) Bc_np))
    (hV2_no_E : ∀ d ∈ V2, ∀ z ∈ E, ∀ f : {e // e ∉ S₃a} → Bool, ¬ (z1 (z0 S₃a f₃a f)).Adj d z)
    (hE_iff : ∀ d ∈ V2, ∀ f : {e // e ∉ S₃a} → Bool, ∀ z : Fin (nOf q m),
      inE q hq (z1 (z0 S₃a f₃a f)) (mkA q m hq hlp d d') z ↔ ∃ j : Fin m, z = e_enum j)
    (hP_sub : ∀ i : Fin m, P_dom i ⊆ Bc'0 \ E)
    (hP_disj : Set.PairwiseDisjoint ((univ : Finset (Fin m)) : Set (Fin m)) P_dom)
    (hP_lo : ∀ i : Fin m, ((1 / 12 : ℝ) * exp (-13 * (m : ℝ))) * (ROf m : ℝ) ≤ ((P_dom i).card : ℝ))
    (hP_R : ∀ d ∈ V2, ∀ f : {e // e ∉ S₃a} → Bool, ∀ i : Fin m, ∀ u ∈ P_dom i, ∀ j : Fin m,
      Rrel q hq (z1 (z0 S₃a f₃a f)) (mkA q m hq hlp d d') u (e_enum j) ↔ j.val ≤ i.val) :
    z4 ((ROf m : ℝ)⁻¹) (fun f_rem : {e : z6 (nOf q m) // e ∉ S₃a} → Bool =>
      z1 (z0 S₃a f₃a f_rem) ∈
        EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ) ≤
      5 / 256 := by
  classical
  set R := ROf m
  set p : ℝ := (R : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  let G₃a := z1 (z0 S₃a f₃a (fun _ => false))
  let V02 := V0 ∪ V2
  have vn : V02.card = 2 * R4Of m := by
    rw [card_union_of_disjoint hV02, hV0_card, hV2_card]; ring
  have v5 : Bc0 ⊆ Bc_np := by rw [hBc0_eq]; exact sdiff_subset
  have vm : (Bc0.card : ℝ) ≤ 2 * (R : ℝ) :=
    (Nat.cast_le.mpr (card_le_card v5)).trans hBc_hi
  have v0 : Disjoint (V0 ∪ V1 ∪ V2) Bc_np := by
    rw [disjoint_left]; intro w hwV hwB
    rw [hBc_np_eq] at hwB
    have hwBb : w ∈ zj q m hq hlp G₃a := by
      rcases mem_union.mp hwV with h01 | h2
      · rcases mem_union.mp h01 with h0 | h1
        · exact hV0_sub h0
        · exact hV1_sub h1
      · exact hV2_sub h2
    exact (mem_filter.mp hwBb).2.2.1 (mem_filter.mp (sdiff_subset hwB)).2
  have v3 : Disjoint V02 Bc0 :=
    (v0.mono_left (fun w hw => by
      rcases mem_union.mp hw with h0 | h2
      · exact mem_union_left _ (mem_union_left _ h0)
      · exact mem_union_right _ h2)).mono_right v5
  have v4 : Disjoint S₃a (z8 V02 Bc0) := by
    refine hdisj_S3a_Bb0_Bc0.mono_right fun ⟨e, he⟩ he1 => ?_
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
      change z7 u v huv ∈ z8 (V0 ∪ V1 ∪ V2) Bc0
      rw [z5 _ _ huv]
      have hsub : V02 ⊆ V0 ∪ V1 ∪ V2 := fun w hw => by
        rcases mem_union.mp hw with h0 | h2
        · exact mem_union_left _ (mem_union_left _ h0)
        · exact mem_union_right _ h2
      rcases (z5 V02 Bc0 huv).mp he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hsub h1, h2⟩
      · exact Or.inr ⟨hsub h1, h2⟩
  let S₃b1 : Finset (z6 (nOf q m)) := S₃a ∪ z8 V02 Bc0
  let Good4b1 : (z6 (nOf q m) → Bool) → Prop := fun f =>
    (R : ℝ) / 5 ≤ ((Bc0.filter (fun u => ∀ v ∈ V02, ¬ (z1 f).Adj u v)).card : ℝ)
  have vi : ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ S₃b1, f e = g e) → (Good4b1 f ↔ Good4b1 g) := by
    intro f g hfg
    have hadj : ∀ u ∈ Bc0, ∀ v ∈ V02, (z1 f).Adj u v ↔ (z1 g).Adj u v := by
      intro u hu v hv
      have hne : u ≠ v := fun h => disjoint_left.mp v3 hv (h ▸ hu)
      rw [za f hne, za g hne,
        hfg _ (mem_union_right _ ((z5 V02 Bc0 hne).mpr (Or.inr ⟨hv, hu⟩)))]
    dsimp only [Good4b1]
    rw [filter_congr fun u hu => forall₂_congr fun v hv => not_congr (hadj u hu v hv)]
  refine (zu hp0 hp1 S₃a S₃b1 subset_union_left f₃a Good4b1
    (fun f => z1 f ∈ EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ)
    vi (ε₁ := 1 / 256) (ε₂ := 4 / 256) (by norm_num) ?_ ?_).trans (by norm_num)
  ·
    have vr : z4 p (fun f_rem : {e // e ∉ S₃a} → Bool => ¬ Good4b1 (z0 S₃a f₃a f_rem)) =
        z4 p (fun f_rem : {e // e ∉ S₃a} → Bool =>
          ((Bc0.filter (fun u => ∀ v ∈ V02,
            ¬ ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S₃a), f_rem ⟨z7 u v h, hmem⟩ = true)).card : ℝ) <
            (R : ℝ) / 5) := by
      refine zx p fun f_rem => ?_
      dsimp only [Good4b1]; rw [not_le]
      have hflt : Bc0.filter (fun u => ∀ v ∈ V02, ¬ (z1 (z0 S₃a f₃a f_rem)).Adj u v) =
          Bc0.filter (fun u => ∀ v ∈ V02,
            ¬ ∃ (h : u ≠ v) (hmem : z7 u v h ∉ S₃a), f_rem ⟨z7 u v h, hmem⟩ = true) := by
        refine filter_congr fun u hu => forall₂_congr fun v hv => not_congr ?_
        have hne : u ≠ v := fun h => disjoint_left.mp v3 hv (h ▸ hu)
        have hnot : z7 u v hne ∉ S₃a := disjoint_right.mp v4
          ((z5 V02 Bc0 hne).mpr (Or.inr ⟨hv, hu⟩))
        exact zb S₃a f₃a f_rem hne hnot
      rw [hflt]
    rw [vr]
    exact z0o q m hlp S₃a V02 Bc0 v3 v4
      vn hBc0_lo vm
  ·
    intro f₃b1 hagree1 hGood4b1
    let G₃b1 := z1 (z0 S₃b1 f₃b1 (fun _ => false))
    let v1 := Bc0.filter (fun u => ∀ v ∈ V02, ¬ G₃b1.Adj u v)
    have v6 : (R : ℝ) / 5 ≤ (v1.card : ℝ) := hGood4b1 (fun _ => false)
    have v2 : v1 ⊆ Bc0 := filter_subset _ _
    have vc : (v1.card : ℝ) ≤ 2 * (R : ℝ) :=
      (Nat.cast_le.mpr (card_le_card v2)).trans vm
    have v7 : Disjoint V1 v1 :=
      (v0.mono_left (fun w hw => mem_union_left _ (mem_union_right _ hw))).mono_right
        (v2.trans v5)
    have v9 : Disjoint S₃b1 (z8 V1 v1) := by
      rw [disjoint_union_left]
      refine ⟨?_, ?_⟩
      · refine hdisj_S3a_Bb0_Bc0.mono_right fun ⟨e, he⟩ he1 => ?_
        induction e using Sym2.ind with
        | _ u v =>
          have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
          change z7 u v huv ∈ z8 (V0 ∪ V1 ∪ V2) Bc0
          rw [z5 _ _ huv]
          rcases (z5 V1 v1 huv).mp he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨mem_union_left _ (mem_union_right _ h1), v2 h2⟩
          · exact Or.inr ⟨mem_union_left _ (mem_union_right _ h1), v2 h2⟩
      · rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
        induction e using Sym2.ind with
        | _ u v =>
          have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
          have v8 : Disjoint V02 V1 := disjoint_union_left.mpr ⟨hV01, hV12.symm⟩
          rcases (z5 V02 Bc0 huv).mp he1 with ⟨hu02, hvB⟩ | ⟨hv02, huB⟩ <;>
            rcases (z5 V1 v1 huv).mp he2 with ⟨hu1, hvC⟩ | ⟨hv1, huC⟩
          · exact disjoint_left.mp v8 hu02 hu1
          · exact disjoint_left.mp v3 hu02 (v2 huC)
          · exact disjoint_left.mp v3 hv02 (v2 hvC)
          · exact disjoint_left.mp v8 hv02 hv1
    let S₃b : Finset (z6 (nOf q m)) := S₃b1 ∪ z8 V1 v1
    let Good4b2 : (z6 (nOf q m) → Bool) → Prop := fun f =>
      ∀ A ∈ v1.powerset, A.card ≤ zd (m - 2) →
        ∀ S ∈ A.powerset,
          ((1 / 12 : ℝ) * exp (-13 * (A.card : ℝ))) * (R : ℝ) ≤
            (((v1 \ A).filter (fun u => ∀ z ∈ A,
              (∃ w ∈ V1, (z1 f).Adj w u ∧ (z1 f).Adj w z) ↔ z ∈ S)).card : ℝ)
    have vh : ∀ f g : z6 (nOf q m) → Bool,
        (∀ e ∈ S₃b, f e = g e) → (Good4b2 f ↔ Good4b2 g) := by
      intro f g hfg
      have hadj : ∀ w ∈ V1, ∀ u ∈ v1, (z1 f).Adj w u ↔ (z1 g).Adj w u := by
        intro w hw u hu
        have hne : w ≠ u := fun h => disjoint_left.mp v7 hw (h ▸ hu)
        rw [za f hne, za g hne,
          hfg _ (mem_union_right _ ((z5 V1 v1 hne).mpr (Or.inl ⟨hw, hu⟩)))]
      refine forall₂_congr fun A hA => imp_congr_right fun _ => forall₂_congr fun S _ => ?_
      rw [filter_congr fun u hu => forall₂_congr fun z hz =>
        iff_congr (exists_congr fun w => and_congr_right fun hw =>
          and_congr (hadj w hw u (sdiff_subset hu)) (hadj w hw z (mem_powerset.mp hA hz))) Iff.rfl]
    refine (zu hp0 hp1 S₃b1 S₃b subset_union_left f₃b1 Good4b2
      (fun f => z1 f ∈ EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ)
      vh (ε₁ := 1 / 256) (ε₂ := 3 / 256) (by norm_num) ?_ ?_).trans (by norm_num)
    · exact z0c q m hlp S₃b1 f₃b1 V1 v1 v7 v9
        hV1_lo hV1_hi v6 vc
    ·
      intro f₃b hagree2 hGood4b2
      let G₃b := z1 (z0 S₃b f₃b (fun _ => false))
      have vk : S₃a ⊆ S₃b := subset_union_left.trans subset_union_left
      have vg : ∀ f : {e // e ∉ S₃b} → Bool, ∀ e ∈ S₃a,
          z0 S₃b f₃b f e = z0 S₃a f₃a (fun _ => false) e := fun f e he => by
        have he1 : e ∈ S₃b1 := subset_union_left he
        have he2 : e ∈ S₃b := subset_union_left he1
        simp only [z0, dif_pos he2, dif_pos he]
        rw [hagree2 ⟨e, he1⟩, hagree1 ⟨e, he⟩]
      have vl : ∀ f : {e // e ∉ S₃b} → Bool, ∃ f' : {e // e ∉ S₃a} → Bool,
          z0 S₃b f₃b f = z0 S₃a f₃a f' := fun f =>
        ⟨fun x => z0 S₃b f₃b f x.1, by
          funext e; by_cases h : e ∈ S₃a
          · have heq := vg f e h; simp only [z0, dif_pos h] at heq ⊢; exact heq
          · simp only [z0, dif_neg h]⟩
      have ve := zz q m hq hlp (z0 S₃b f₃b (fun _ => false))
        (z0 S₃a f₃a (fun _ => false)) (fun e he => vg (fun _ => false) e (hS0_sub he))
      have hdisj_Bc0_Bc' : Disjoint Bc0 Bc'_np := by
        rw [hBc0_eq]; exact sdiff_disjoint
      have vp : Disjoint Bc0 (Bc'0 \ E) := by
        refine hdisj_Bc0_Bc'.mono_right fun z hz => ?_
        have h0 := sdiff_subset hz; rw [hBc'0_eq] at h0; exact sdiff_subset h0
      have v0' : Disjoint (V0 ∪ V1 ∪ V2) Bc'_np := by
        rw [disjoint_left]; intro w hwV hwB
        rw [hBc'_np_eq] at hwB
        have hwBb : w ∈ zj q m hq hlp G₃a := by
          rcases mem_union.mp hwV with h01 | h2
          · rcases mem_union.mp h01 with h0 | h1
            · exact hV0_sub h0
            · exact hV1_sub h1
          · exact hV2_sub h2
        exact (mem_filter.mp hwBb).2.2.2.1 (mem_filter.mp (sdiff_subset hwB)).2
      have vf : Disjoint S₃b (z8 V2 (Bc'_np \ E)) := by
        rw [disjoint_union_left, disjoint_union_left]
        refine ⟨⟨hdisj_S3a_V2, ?_⟩, ?_⟩
        · rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
          induction e using Sym2.ind with
          | _ u v =>
            have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
            rcases (z5 V02 Bc0 huv).mp he1 with ⟨_, hvB⟩ | ⟨_, huB⟩ <;>
              rcases (z5 V2 (Bc'_np \ E) huv).mp he2 with ⟨hu2, hv'⟩ | ⟨hv2, hu'⟩
            · exact disjoint_left.mp hdisj_Bc0_Bc' hvB (sdiff_subset hv')
            · exact disjoint_left.mp v3 (mem_union_right _ hv2) hvB
            · exact disjoint_left.mp v3 (mem_union_right _ hu2) huB
            · exact disjoint_left.mp hdisj_Bc0_Bc' huB (sdiff_subset hu')
        · rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
          induction e using Sym2.ind with
          | _ u v =>
            have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
            rcases (z5 V1 v1 huv).mp he1 with ⟨hu1, hvC⟩ | ⟨hv1, huC⟩ <;>
              rcases (z5 V2 (Bc'_np \ E) huv).mp he2 with ⟨hu2, hv'⟩ | ⟨hv2, hu'⟩
            · exact disjoint_left.mp hV12 hu1 hu2
            · exact disjoint_left.mp v0' (mem_union_left _ (mem_union_right _ hu1)) (sdiff_subset hu')
            · exact disjoint_left.mp v0' (mem_union_left _ (mem_union_right _ hv1))
                (sdiff_subset hv')
            · exact disjoint_left.mp hV12 hv1 hv2
      have vj : Disjoint S₃b (z8 (Bc'0 \ E) Bc_np) := by
        rw [disjoint_union_left, disjoint_union_left]
        refine ⟨⟨hdisj_S3a_6, ?_⟩, ?_⟩
        · rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
          induction e using Sym2.ind with
          | _ u v =>
            have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
            have vb : V02 ⊆ V0 ∪ V1 ∪ V2 := fun w hw => by
              rcases mem_union.mp hw with h0 | h2
              · exact mem_union_left _ (mem_union_left _ h0)
              · exact mem_union_right _ h2
            rcases (z5 V02 Bc0 huv).mp he1 with ⟨hu02, _⟩ | ⟨hv02, _⟩ <;>
              rcases (z5 (Bc'0 \ E) Bc_np huv).mp he2 with ⟨hu', hvB⟩ | ⟨hv', huB⟩
            · exact disjoint_left.mp v0' (vb hu02)
                (sdiff_subset (hBc'0_eq ▸ sdiff_subset hu'))
            · exact disjoint_left.mp v0 (vb hu02) huB
            · exact disjoint_left.mp v0 (vb hv02) hvB
            · exact disjoint_left.mp v0' (vb hv02)
                (sdiff_subset (hBc'0_eq ▸ sdiff_subset hv'))
        · rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
          induction e using Sym2.ind with
          | _ u v =>
            have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
            rcases (z5 V1 v1 huv).mp he1 with ⟨hu1, _⟩ | ⟨hv1, _⟩ <;>
              rcases (z5 (Bc'0 \ E) Bc_np huv).mp he2 with ⟨hu', hvB⟩ | ⟨hv', huB⟩
            · exact disjoint_left.mp v0' (mem_union_left _ (mem_union_right _ hu1))
                (sdiff_subset (hBc'0_eq ▸ sdiff_subset hu'))
            · exact disjoint_left.mp v0 (mem_union_left _ (mem_union_right _ hu1)) huB
            · exact disjoint_left.mp v0 (mem_union_left _ (mem_union_right _ hv1)) hvB
            · exact disjoint_left.mp v0' (mem_union_left _ (mem_union_right _ hv1))
                (sdiff_subset (hBc'0_eq ▸ sdiff_subset hv'))
      let Pool : Finset (Fin (nOf q m)) → Finset (Fin (nOf q m)) → Finset (Fin (nOf q m)) := fun A S =>
        (v1 \ A).filter (fun u => ∀ z ∈ A, (∃ w ∈ V1, G₃b.Adj w u ∧ G₃b.Adj w z) ↔ z ∈ S)
      have vs : ∀ d ∈ V2, ∀ f : {e // e ∉ S₃b} → Bool, ∀ u ∈ v1, ∀ z ∈ v1,
          Rrel q hq (z1 (z0 S₃b f₃b f)) (mkA q m hq hlp d d') u z ↔
            ∃ w ∈ V1, G₃b.Adj w u ∧ G₃b.Adj w z := by
        intro d hd f u hu z hz
        let Gf := z1 (z0 S₃b f₃b f)
        have vv := zz q m hq hlp (z0 S₃b f₃b f)
          (z0 S₃a f₃a (fun _ => false)) (fun e he => vg f e (hS0_sub he))
        rw [w3, z00, vv.2.2]
        have va : ∀ w ∈ V1, ∀ v ∈ v1, Gf.Adj w v ↔ G₃b.Adj w v := fun w hw v hv => by
          have hne : w ≠ v := fun h => disjoint_left.mp v7 hw (h ▸ hv)
          have hmem : z7 w v hne ∈ S₃b :=
            mem_union_right _ ((z5 V1 v1 hne).mpr (Or.inl ⟨hw, hv⟩))
          rw [zf S₃b f₃b f hne hmem, zf S₃b f₃b (fun _ => false) hne hmem]
        constructor
        · rintro ⟨w, hwBb, hwu, hwz⟩
          have vt : w ∈ zj q m hq hlp G₃a := mem_of_mem_erase (mem_of_mem_erase hwBb)
          have vd : w ∉ V02 := by
            intro hw02
            have hne : u ≠ w := fun h => disjoint_left.mp v3 hw02 (h ▸ v2 hu)
            have vo : z7 u w hne ∈ S₃b1 :=
              mem_union_right _ ((z5 V02 Bc0 hne).mpr (Or.inr ⟨hw02, v2 hu⟩))
            have vu : z7 u w hne ∈ S₃b := subset_union_left vo
            have huw1 : G₃b1.Adj u w := by
              rw [zf S₃b1 f₃b1 (fun _ => false) hne vo, ← hagree2 ⟨_, vo⟩]
              exact (zf S₃b f₃b f hne vu).mp hwu.symm
            exact (mem_filter.mp hu).2 w hw02 huw1
          have hwV1 : w ∈ V1 := by
            rcases mem_union.mp (hV_cover vt) with h01 | h2
            · rcases mem_union.mp h01 with h0 | h1
              · exact absurd (mem_union_left _ h0) vd
              · exact h1
            · exact absurd (mem_union_right _ h2) vd
          exact ⟨w, hwV1, (va w hwV1 u hu).mp hwu, (va w hwV1 z hz).mp hwz⟩
        · rintro ⟨w, hwV1, hwu, hwz⟩
          have hwd : w ≠ d := fun h => disjoint_left.mp hV12 hwV1 (h ▸ hd)
          have hwd' : w ≠ d' := fun h => disjoint_left.mp hV01 hd'_V0 (h ▸ hwV1)
          refine ⟨w, mem_erase.mpr ⟨hwd', mem_erase.mpr ⟨hwd, hV1_sub hwV1⟩⟩,
            (va w hwV1 u hu).mpr hwu, (va w hwV1 z hz).mpr hwz⟩
      exact z22 q m hq hlp S₃b f₃b d' V0 V1 V2 E Bc_np Bc'_np Bc'0 v1 e_enum P_dom Pool
        (hS0_sub.trans vk) hd'_V0
        (ve.2.2.symm ▸ hV0_sub) (ve.2.2.symm ▸ hV1_sub) (ve.2.2.symm ▸ hV2_sub) hV2_card
        hV01 hV02 hV12 (ve.2.2.symm ▸ hV_cover)
        (ve.1.symm ▸ hBc_np_eq) (ve.2.1.symm ▸ hBc'_np_eq) hBc'0_eq hE_sub
        (v2.trans v5) hBc_hi hBc'_hi v6
        vf vj
        (fun d hd z hz f => by rcases vl f with ⟨f', hf'⟩; rw [hf']; exact hV2_no_E d hd z hz f')
        (fun d hd f z => by rcases vl f with ⟨f', hf'⟩; rw [hf']; exact hE_iff d hd f' z)
        hP_sub hP_disj hP_lo
        (fun d hd f i u hu j => by rcases vl f with ⟨f', hf'⟩; rw [hf']; exact hP_R d hd f' i u hu j)
        vs
        (fun _ _ _ _ _ => filter_subset _ _)
        (fun A _ _ S₁' hS₁' S₂' hS₂' hne => by
          change Disjoint (Pool A S₁') (Pool A S₂')
          rw [disjoint_left]; intro u hu1 hu2
          apply hne; ext z
          by_cases hzA : z ∈ A
          · rw [← (mem_filter.mp hu1).2 z hzA, (mem_filter.mp hu2).2 z hzA]
          · exact ⟨fun h => absurd (mem_powerset.mp (mem_coe.mp hS₁') h) hzA,
              fun h => absurd (mem_powerset.mp (mem_coe.mp hS₂') h) hzA⟩)
        (hGood4b2 (fun _ => false))
        (fun _ _ _ _ _ u hu z hz => (mem_filter.mp hu).2 z hz)
private lemma z1w (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (S₂ : Finset (z6 (nOf q m)))
    (f₂ : {e : z6 (nOf q m) // e ∈ S₂} → Bool)
    (d' : Fin (nOf q m))
    (V0 V1 V2 E Bc_np Bc'_np Bc0 Bc'0 : Finset (Fin (nOf q m)))
    (e_enum : Fin m → Fin (nOf q m))
    (he_inj : Function.Injective e_enum)
    (he_eq : E = univ.image e_enum)
    (hS0_sub : ze (zn q m hq hlp) ⊆ S₂)
    (hd'_V0 : d' ∈ V0)
    (hV0_sub : V0 ⊆ zj q m hq hlp (z1 (z0 S₂ f₂ (fun _ => false))))
    (hV1_sub : V1 ⊆ zj q m hq hlp (z1 (z0 S₂ f₂ (fun _ => false))))
    (hV2_sub : V2 ⊆ zj q m hq hlp (z1 (z0 S₂ f₂ (fun _ => false))))
    (hV0_card : V0.card = R4Of m) (hV2_card : V2.card = R4Of m)
    (hV1_lo : (1 / 12 : ℝ) * ((ROf m : ℝ) ^ 2) ≤ (V1.card : ℝ))
    (hV1_hi : (V1.card : ℝ) ≤ 2 * ((ROf m : ℝ) ^ 2))
    (hV01 : Disjoint V0 V1) (hV02 : Disjoint V0 V2) (hV12 : Disjoint V1 V2)
    (hV_cover : zj q m hq hlp (z1 (z0 S₂ f₂ (fun _ => false))) ⊆ V0 ∪ V1 ∪ V2)
    (hBc_np_eq : Bc_np = zr q m hq hlp (z1 (z0 S₂ f₂ (fun _ => false))) \ zn q m hq hlp)
    (hBc'_np_eq : Bc'_np = zp q m hq hlp (z1 (z0 S₂ f₂ (fun _ => false))) \ zn q m hq hlp)
    (hBc0_eq : Bc0 = Bc_np \ Bc'_np) (hBc'0_eq : Bc'0 = Bc'_np \ Bc_np)
    (hE_sub : E ⊆ Bc'0) (hE_card : E.card = m)
    (hBc_hi : (Bc_np.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc'_hi : (Bc'_np.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc0_lo : (ROf m : ℝ) / 4 ≤ (Bc0.card : ℝ))
    (hBc'0_lo : (ROf m : ℝ) / 4 ≤ (Bc'0.card : ℝ))
    (hV1_E_sub : z8 V1 E ⊆ S₂)
    (hdisj_S2_4a : Disjoint S₂ (z8 (Bc'0 \ E) V1))
    (hdisj_S2_Bb0_Bc0 : Disjoint S₂ (z8 (V0 ∪ V1 ∪ V2) Bc0))
    (hdisj_S2_V2 : Disjoint S₂ (z8 V2 (Bc'_np \ E)))
    (hdisj_S2_6 : Disjoint S₂ (z8 (Bc'0 \ E) Bc_np))
    (hV0_no_E : ∀ w ∈ V0, w ≠ d' → ∀ z ∈ E, ∀ f : {e // e ∉ S₂} → Bool, ¬ (z1 (z0 S₂ f₂ f)).Adj w z)
    (hV2_no_E : ∀ d ∈ V2, ∀ z ∈ E, ∀ f : {e // e ∉ S₂} → Bool, ¬ (z1 (z0 S₂ f₂ f)).Adj d z)
    (hE_iff : ∀ d ∈ V2, ∀ f : {e // e ∉ S₂} → Bool, ∀ z : Fin (nOf q m),
      inE q hq (z1 (z0 S₂ f₂ f)) (mkA q m hq hlp d d') z ↔ ∃ j : Fin m, z = e_enum j)
    (hW_hi : ∀ z ∈ E, ((V1.filter (fun w => (z1 (z0 S₂ f₂ (fun _ => false))).Adj w z)).card : ℝ) ≤ 4 * (ROf m : ℝ))
    (hW_only_lo : ∀ z ∈ E, (ROf m : ℝ) / 48 ≤
      ((V1.filter (fun w => (z1 (z0 S₂ f₂ (fun _ => false))).Adj w z ∧
        ∀ z' ∈ E, z' ≠ z → ¬ (z1 (z0 S₂ f₂ (fun _ => false))).Adj w z')).card : ℝ)) :
    z4 ((ROf m : ℝ)⁻¹) (fun f_rem : {e : z6 (nOf q m) // e ∉ S₂} → Bool =>
      z1 (z0 S₂ f₂ f_rem) ∈
        EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ) ≤
      6 / 256 := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set p : ℝ := (R : ℝ)⁻¹
  have vm : R8 ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have u2 : 10000 ≤ R := le_trans hlp.hR8_ge vm
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  have vt := yf q m hlp
  let G₂ := z1 (z0 S₂ f₂ (fun _ => false))
  let W_z : Fin (nOf q m) → Finset (Fin (nOf q m)) := fun z => V1.filter (fun w => G₂.Adj w z)
  let vu : Fin (nOf q m) → Finset (Fin (nOf q m)) := fun z =>
    V1.filter (fun w => G₂.Adj w z ∧ ∀ z' ∈ E, z' ≠ z → ¬ G₂.Adj w z')
  let v2 : Finset (Fin (nOf q m)) := E.biUnion W_z
  have v1 : v2 ⊆ V1 := biUnion_subset.mpr fun _ _ => filter_subset _ _
  have vh : (v2.card : ℝ) ≤ 4 * (E.card : ℝ) * (R : ℝ) := by
    have h1 : (v2.card : ℝ) ≤ ∑ z ∈ E, ((W_z z).card : ℝ) := by exact_mod_cast card_biUnion_le
    calc (v2.card : ℝ) ≤ ∑ z ∈ E, ((W_z z).card : ℝ) := h1
      _ ≤ ∑ _z ∈ E, (4 * (R : ℝ)) := sum_le_sum fun z hz => hW_hi z hz
      _ = 4 * (E.card : ℝ) * (R : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
  let U := Bc'0 \ E
  have u1 : (R : ℝ) / 5 ≤ (U.card : ℝ) := by
    have hsd : U.card = Bc'0.card - E.card := by
      change (Bc'0 \ E).card = _; rw [card_sdiff, inter_eq_left.mpr hE_sub]
    have hle : E.card ≤ Bc'0.card := card_le_card hE_sub
    have hc : (Bc'0.card : ℝ) ≤ (U.card : ℝ) + (m : ℝ) := by
      have : Bc'0.card ≤ U.card + m := by omega
      exact_mod_cast this
    have vz : (m : ℝ) ≤ (R : ℝ) / 20 := by
      have hmT : m ≤ T := y9 m (by have := hlp.hm; omega)
      have vk : T ≤ R8 := le_trans (Nat.le_self_pow (by norm_num) T) (Nat.le_of_lt Nat.lt_two_pow_self)
      have u3 : (R : ℝ) = (R8 : ℝ) ^ 8 := by exact_mod_cast zq m
      have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
      have hpow : (R8 : ℝ) ^ 2 ≤ (R8 : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have hmR8 : (m : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast le_trans hmT vk
      rw [u3]; nlinarith only [hmR8, hR8_ge, hpow]
    linarith
  have vg : Disjoint U V1 := by
    rw [disjoint_left]; intro u huU hu1
    have huBc' : u ∈ zp q m hq hlp G₂ := by
      have h0 : u ∈ Bc'0 := sdiff_subset huU
      rw [hBc'0_eq] at h0; exact sdiff_subset (hBc'_np_eq ▸ sdiff_subset h0)
    exact (mem_filter.mp (hV1_sub hu1)).2.2.2.1 (mem_filter.mp huBc').2
  have v4 : Disjoint U v2 := vg.mono_right v1
  have v6 : Disjoint S₂ (z8 U v2) := by
    refine hdisj_S2_4a.mono_right fun ⟨e, he⟩ he1 => ?_
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
      change z7 u v huv ∈ z8 U V1
      rw [z5 U V1 huv]
      rcases (z5 U v2 huv).mp he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, v1 h2⟩
      · exact Or.inr ⟨h1, v1 h2⟩
  let S₃a : Finset (z6 (nOf q m)) := S₂ ∪ z8 U v2
  let Good4a : (z6 (nOf q m) → Bool) → Prop := fun f =>
    ∀ S ∈ E.powerset,
      ((1 / 12 : ℝ) * exp (-13 * (m : ℝ))) * (R : ℝ) ≤
        ((U.filter (fun u => ∀ z ∈ E, (∃ w ∈ W_z z, (z1 f).Adj u w) ↔ z ∈ S)).card : ℝ)
  have ve : ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ S₃a, f e = g e) → (Good4a f ↔ Good4a g) := by
    intro f g hfg
    have hadj : ∀ u ∈ U, ∀ w ∈ v2, (z1 f).Adj u w ↔ (z1 g).Adj u w := by
      intro u hu w hw
      have hne : u ≠ w := fun h => disjoint_left.mp v4 hu (h ▸ hw)
      rw [za f hne, za g hne,
        hfg _ (mem_union_right _ ((z5 U v2 hne).mpr (Or.inl ⟨hu, hw⟩)))]
    refine forall₂_congr fun S _ => ?_
    rw [filter_congr fun u hu => forall₂_congr fun z hz =>
      iff_congr (exists_congr fun w => and_congr_right fun hw =>
        hadj u hu w (mem_biUnion.mpr ⟨z, hz, hw⟩)) Iff.rfl]
  refine (zu hp0 hp1 S₂ S₃a subset_union_left f₂ Good4a
    (fun f => z1 f ∈ EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ)
    ve (ε₁ := 1 / 256) (ε₂ := 5 / 256) (by norm_num) ?_ ?_).trans (by norm_num)
  ·
    have vx : z4 p (fun f_rem : {e // e ∉ S₂} → Bool => ¬ Good4a (z0 S₂ f₂ f_rem)) ≤
        z4 p (fun f_rem : {e // e ∉ S₂} → Bool =>
          ∃ S ∈ E.powerset,
            ((U.filter (fun u => ∀ z ∈ E,
              (∃ w ∈ W_z z, ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S₂),
                f_rem ⟨z7 u w h, hmem⟩ = true) ↔ z ∈ S)).card : ℝ) <
              (1 / 2) * ((U.card : ℝ) * exp (-13 * (E.card : ℝ)))) := by
      refine zi hp0 hp1 fun f_rem hnot => ?_
      simp only [Good4a, not_forall, not_le] at hnot
      rcases hnot with ⟨S, hS, hlt⟩
      refine ⟨S, hS, ?_⟩
      have hflt : U.filter (fun u => ∀ z ∈ E, (∃ w ∈ W_z z, (z1 (z0 S₂ f₂ f_rem)).Adj u w) ↔ z ∈ S) =
          U.filter (fun u => ∀ z ∈ E,
            (∃ w ∈ W_z z, ∃ (h : u ≠ w) (hmem : z7 u w h ∉ S₂), f_rem ⟨z7 u w h, hmem⟩ = true) ↔ z ∈ S) := by
        refine filter_congr fun u hu => forall₂_congr fun z hz =>
          iff_congr (exists_congr fun w => and_congr_right fun hw => ?_) Iff.rfl
        have hwW : w ∈ v2 := mem_biUnion.mpr ⟨z, hz, hw⟩
        have hne : u ≠ w := fun h => disjoint_left.mp v4 hu (h ▸ hwW)
        have vw : z7 u w hne ∉ S₂ := disjoint_right.mp v6
          ((z5 U v2 hne).mpr (Or.inl ⟨hu, hwW⟩))
        exact zb S₂ f₂ f_rem hne vw
      rw [← hflt, hE_card]
      have vp : 0 ≤ exp (-13 * (m : ℝ)) := (exp_pos _).le
      nlinarith only [hlt, u1, vp]
    have vn := yj u2 S₂ E v2 U vu W_z vh
      (fun z _ => fun w hw => mem_filter.mpr ⟨(mem_filter.mp hw).1, (mem_filter.mp hw).2.1⟩)
      (fun z hz => fun w hw => mem_biUnion.mpr ⟨z, hz, hw⟩)
      hW_only_lo
      (fun z₁ _ z₂ hz₂ hne => by
        rw [disjoint_left]; intro w hw1 hw2
        exact (mem_filter.mp hw1).2.2 z₂ hz₂ hne.symm (mem_filter.mp hw2).2)
      v4 v6
    have vo : m ≤ T := y9 m (by have := hlp.hm; omega)
    have vq : exp (-((U.card : ℝ) * exp (-13 * (E.card : ℝ))) / 8) ≤
        exp (-((R8 : ℝ)) / 64) := by
      rw [hE_card]
      have hmT : (m : ℝ) ≤ (T : ℝ) := by exact_mod_cast vo
      have h1 : exp (-13 * (T : ℝ)) ≤ exp (-13 * (m : ℝ)) := exp_le_exp.mpr (by linarith)
      have h2 : ((R : ℝ) / 8) * exp (-13 * (T : ℝ)) ≤ (U.card : ℝ) * exp (-13 * (m : ℝ)) :=
        mul_le_mul (by linarith) h1 (exp_pos _).le (Nat.cast_nonneg _)
      exact (exp_le_exp.mpr (by linarith)).trans vt.2.2.1
    have hfin : ((2 : ℝ) ^ E.card) * exp (-((R8 : ℝ)) / 64) ≤ 1 / 256 := by
      rw [hE_card]
      have h1 : (2 : ℝ) ^ m ≤ ((nOf q m : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (T + 10) := by
        have hn1 : (1 : ℝ) ≤ (nOf q m : ℝ) ^ (kOf q + 4) := one_le_pow₀ (by exact_mod_cast wq q m)
        have h2 : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (T + 10) := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith only [hn1, h2, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m]
      exact (mul_le_mul_of_nonneg_right h1 (exp_pos _).le).trans hlp.hpoly_exp_R8
    exact (vx.trans vn).trans ((mul_le_mul_of_nonneg_left vq (pow_nonneg (by norm_num) _)).trans hfin)
  ·
    intro f₃a hagree hGood4a
    let G₃a := z1 (z0 S₃a f₃a (fun _ => false))
    have vb : ∀ f : {e // e ∉ S₃a} → Bool, ∀ e ∈ S₂,
        z0 S₃a f₃a f e = z0 S₂ f₂ (fun _ => false) e := fun f e he => by
      have he3 : e ∈ S₃a := subset_union_left he
      simp only [z0, dif_pos he3, dif_pos he]; exact hagree ⟨e, he⟩
    have vl : ∀ f : {e // e ∉ S₃a} → Bool, ∃ f' : {e // e ∉ S₂} → Bool,
        z0 S₃a f₃a f = z0 S₂ f₂ f' := fun f =>
      ⟨fun x => z0 S₃a f₃a f x.1, by
        funext e; by_cases h : e ∈ S₂
        · have heq := vb f e h; simp only [z0, dif_pos h] at heq ⊢; exact heq
        · simp only [z0, dif_neg h]⟩
    have v8 := zz q m hq hlp (z0 S₃a f₃a (fun _ => false))
      (z0 S₂ f₂ (fun _ => false)) (fun e he => vb (fun _ => false) e (hS0_sub he))
    let Pref : Fin m → Finset (Fin (nOf q m)) := fun i =>
      (univ.filter (fun j : Fin m => j.val ≤ i.val)).image e_enum
    have vi : ∀ i : Fin m, Pref i ∈ E.powerset := fun i =>
      mem_powerset.mpr fun z hz => by
        rcases mem_image.mp hz with ⟨j, _, rfl⟩
        rw [he_eq]; exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
    let vf : Fin m → Finset (Fin (nOf q m)) := fun i =>
      U.filter (fun u => ∀ z ∈ E, (∃ w ∈ W_z z, G₃a.Adj u w) ↔ z ∈ Pref i)
    have vr : Set.PairwiseDisjoint ((univ : Finset (Fin m)) : Set (Fin m)) vf := by
      intro i₁ _ i₂ _ hne
      change Disjoint (vf i₁) (vf i₂)
      rw [disjoint_left]; intro u hu1 hu2
      have vy := (mem_filter.mp hu1).2
      have vj := (mem_filter.mp hu2).2
      apply hne; apply Fin.ext
      have hiff : ∀ j : Fin m, j.val ≤ i₁.val ↔ j.val ≤ i₂.val := fun j => by
        have hzE : e_enum j ∈ E := by rw [he_eq]; exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
        have hp1 : e_enum j ∈ Pref i₁ ↔ j.val ≤ i₁.val := by
          simp only [Pref, mem_image, mem_filter, mem_univ, true_and]
          exact ⟨fun ⟨k, hk, hke⟩ => (he_inj hke) ▸ hk, fun h => ⟨j, h, rfl⟩⟩
        have hp2 : e_enum j ∈ Pref i₂ ↔ j.val ≤ i₂.val := by
          simp only [Pref, mem_image, mem_filter, mem_univ, true_and]
          exact ⟨fun ⟨k, hk, hke⟩ => (he_inj hke) ▸ hk, fun h => ⟨j, h, rfl⟩⟩
        rw [← hp1, ← hp2, ← vy _ hzE, vj _ hzE]
      have h12 : i₁.val ≤ i₂.val := (hiff i₁).mp le_rfl
      have h21 : i₂.val ≤ i₁.val := (hiff i₂).mpr le_rfl
      omega
    have hdisj_Bc0_Bc' : Disjoint Bc0 Bc'_np := by rw [hBc0_eq]; exact sdiff_disjoint
    have v0' : Disjoint (V0 ∪ V1 ∪ V2) Bc'_np := by
      rw [disjoint_left]; intro w hwV hwB
      rw [hBc'_np_eq] at hwB
      have hwBb : w ∈ zj q m hq hlp G₂ := by
        rcases mem_union.mp hwV with h01 | h2
        · rcases mem_union.mp h01 with h0 | h1
          · exact hV0_sub h0
          · exact hV1_sub h1
        · exact hV2_sub h2
      exact (mem_filter.mp hwBb).2.2.2.1 (mem_filter.mp (sdiff_subset hwB)).2
    have v0 : Disjoint (V0 ∪ V1 ∪ V2) Bc_np := by
      rw [disjoint_left]; intro w hwV hwB
      rw [hBc_np_eq] at hwB
      have hwBb : w ∈ zj q m hq hlp G₂ := by
        rcases mem_union.mp hwV with h01 | h2
        · rcases mem_union.mp h01 with h0 | h1
          · exact hV0_sub h0
          · exact hV1_sub h1
        · exact hV2_sub h2
      exact (mem_filter.mp hwBb).2.2.1 (mem_filter.mp (sdiff_subset hwB)).2
    have v5 : Disjoint S₃a (z8 (V0 ∪ V1 ∪ V2) Bc0) := by
      rw [disjoint_union_left]
      refine ⟨hdisj_S2_Bb0_Bc0, ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        have hU_sub_Bc' : U ⊆ Bc'_np := fun z hz => sdiff_subset (hBc'0_eq ▸ sdiff_subset hz)
        rcases (z5 U v2 huv).mp he1 with ⟨huU, _⟩ | ⟨hvU, _⟩ <;>
          rcases (z5 (V0 ∪ V1 ∪ V2) Bc0 huv).mp he2 with ⟨huV, hvB⟩ | ⟨hvV, huB⟩
        · exact disjoint_left.mp v0' huV (hU_sub_Bc' huU)
        · exact disjoint_left.mp hdisj_Bc0_Bc' huB (hU_sub_Bc' huU)
        · exact disjoint_left.mp hdisj_Bc0_Bc' hvB (hU_sub_Bc' hvU)
        · exact disjoint_left.mp v0' hvV (hU_sub_Bc' hvU)
    have va : Disjoint S₃a (z8 V2 (Bc'_np \ E)) := by
      rw [disjoint_union_left]
      refine ⟨hdisj_S2_V2, ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        have hU_sub_Bc' : U ⊆ Bc'_np := fun z hz => sdiff_subset (hBc'0_eq ▸ sdiff_subset hz)
        rcases (z5 U v2 huv).mp he1 with ⟨huU, hvW⟩ | ⟨hvU, huW⟩ <;>
          rcases (z5 V2 (Bc'_np \ E) huv).mp he2 with ⟨hu2, hv'⟩ | ⟨hv2, hu'⟩
        · exact disjoint_left.mp v0' (mem_union_right _ hu2) (hU_sub_Bc' huU)
        · exact disjoint_left.mp hV12 (v1 hvW) hv2
        · exact disjoint_left.mp hV12 (v1 huW) hu2
        · exact disjoint_left.mp v0' (mem_union_right _ hv2) (hU_sub_Bc' hvU)
    have vd : Disjoint S₃a (z8 (Bc'0 \ E) Bc_np) := by
      rw [disjoint_union_left]
      refine ⟨hdisj_S2_6, ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        have hU_sub_Bc' : U ⊆ Bc'_np := fun z hz => sdiff_subset (hBc'0_eq ▸ sdiff_subset hz)
        rcases (z5 U v2 huv).mp he1 with ⟨_, hvW⟩ | ⟨_, huW⟩ <;>
          rcases (z5 U Bc_np huv).mp he2 with ⟨huU, hvB⟩ | ⟨hvU, huB⟩
        · exact disjoint_left.mp v0 (mem_union_left _ (mem_union_right _ (v1 hvW))) hvB
        · exact disjoint_left.mp v0' (mem_union_left _ (mem_union_right _ (v1 hvW))) (hU_sub_Bc' hvU)
        · exact disjoint_left.mp v0' (mem_union_left _ (mem_union_right _ (v1 huW))) (hU_sub_Bc' huU)
        · exact disjoint_left.mp v0 (mem_union_left _ (mem_union_right _ (v1 huW))) huB
    have hP_R : ∀ d ∈ V2, ∀ f : {e // e ∉ S₃a} → Bool, ∀ i : Fin m, ∀ u ∈ vf i, ∀ j : Fin m,
        Rrel q hq (z1 (z0 S₃a f₃a f)) (mkA q m hq hlp d d') u (e_enum j) ↔ j.val ≤ i.val := by
      intro d hd f i u hu j
      let Gf := z1 (z0 S₃a f₃a f)
      rcases vl f with ⟨f', hf'⟩
      have u0 := zz q m hq hlp (z0 S₃a f₃a f)
        (z0 S₂ f₂ (fun _ => false)) (fun e he => vb f e (hS0_sub he))
      have hzE : e_enum j ∈ E := by rw [he_eq]; exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
      have huU : u ∈ U := (mem_filter.mp hu).1
      have hpat := (mem_filter.mp hu).2 (e_enum j) hzE
      have vs : e_enum j ∈ Pref i ↔ j.val ≤ i.val := by
        simp only [Pref, mem_image, mem_filter, mem_univ, true_and]
        exact ⟨fun ⟨k, hk, hke⟩ => (he_inj hke) ▸ hk, fun h => ⟨j, h, rfl⟩⟩
      rw [← vs, ← hpat, w3, z00, u0.2.2]
      have v9 : ∀ w ∈ V1, Gf.Adj w (e_enum j) ↔ G₂.Adj w (e_enum j) := fun w hw => by
        have hne : w ≠ e_enum j := fun h =>
          disjoint_left.mp v0' (mem_union_left _ (mem_union_right _ hw))
            (h ▸ sdiff_subset (hBc'0_eq ▸ hE_sub hzE))
        have vj : z7 w (e_enum j) hne ∈ S₂ :=
          hV1_E_sub ((z5 V1 E hne).mpr (Or.inl ⟨hw, hzE⟩))
        rw [za _ hne, za _ hne, vb f _ vj]
      constructor
      · rintro ⟨w, hwBb, hwu, hwz⟩
        have hw_ne_d' : w ≠ d' := (mem_erase.mp hwBb).1
        have vv : w ∈ zj q m hq hlp G₂ := mem_of_mem_erase (mem_of_mem_erase hwBb)
        have hwV1 : w ∈ V1 := by
          rcases mem_union.mp (hV_cover vv) with h01 | h2
          · rcases mem_union.mp h01 with h0 | h1
            · exact absurd (by change (z1 (z0 S₃a f₃a f)).Adj w (e_enum j) at hwz; rw [hf'] at hwz; exact hwz)
                (hV0_no_E w h0 hw_ne_d' (e_enum j) hzE f')
            · exact h1
          · exact absurd (by change (z1 (z0 S₃a f₃a f)).Adj w (e_enum j) at hwz; rw [hf'] at hwz; exact hwz)
              (hV2_no_E w h2 (e_enum j) hzE f')
        have hwWz : w ∈ W_z (e_enum j) := mem_filter.mpr ⟨hwV1, (v9 w hwV1).mp hwz⟩
        have v7 : w ∈ v2 := mem_biUnion.mpr ⟨e_enum j, hzE, hwWz⟩
        have v3 : u ≠ w := fun h => disjoint_left.mp v4 huU (h ▸ v7)
        have vc : z7 u w v3 ∈ S₃a :=
          mem_union_right _ ((z5 U v2 v3).mpr (Or.inl ⟨huU, v7⟩))
        refine ⟨w, hwWz, ?_⟩
        rw [zf S₃a f₃a (fun _ => false) v3 vc]
        exact (zf S₃a f₃a f v3 vc).mp hwu.symm
      · rintro ⟨w, hwWz, huw3⟩
        have hwV1 : w ∈ V1 := (mem_filter.mp hwWz).1
        have v7 : w ∈ v2 := mem_biUnion.mpr ⟨e_enum j, hzE, hwWz⟩
        have v3 : u ≠ w := fun h => disjoint_left.mp v4 huU (h ▸ v7)
        have vc : z7 u w v3 ∈ S₃a :=
          mem_union_right _ ((z5 U v2 v3).mpr (Or.inl ⟨huU, v7⟩))
        have hwu : Gf.Adj w u :=
          ((zf S₃a f₃a f v3 vc).mpr
            ((zf S₃a f₃a (fun _ => false) v3 vc).mp huw3)).symm
        have hwz : Gf.Adj w (e_enum j) := (v9 w hwV1).mpr (mem_filter.mp hwWz).2
        have hwd : w ≠ d := fun h => disjoint_left.mp hV12 hwV1 (h ▸ hd)
        have hwd' : w ≠ d' := fun h => disjoint_left.mp hV01 hd'_V0 (h ▸ hwV1)
        exact ⟨w, mem_erase.mpr ⟨hwd', mem_erase.mpr ⟨hwd, hV1_sub hwV1⟩⟩, hwu, hwz⟩
    exact z1v q m hq hlp S₃a f₃a d' V0 V1 V2 E Bc_np Bc'_np Bc0 Bc'0 e_enum vf
      (hS0_sub.trans subset_union_left) hd'_V0
      (v8.2.2.symm ▸ hV0_sub) (v8.2.2.symm ▸ hV1_sub) (v8.2.2.symm ▸ hV2_sub)
      hV0_card hV2_card hV1_lo hV1_hi hV01 hV02 hV12 (v8.2.2.symm ▸ hV_cover)
      (v8.1.symm ▸ hBc_np_eq) (v8.2.1.symm ▸ hBc'_np_eq) hBc0_eq hBc'0_eq hE_sub
      hBc_hi hBc'_hi hBc0_lo v5 va vd
      (fun d hd z hz f => by rcases vl f with ⟨f', hf'⟩; rw [hf']; exact hV2_no_E d hd z hz f')
      (fun d hd f z => by rcases vl f with ⟨f', hf'⟩; rw [hf']; exact hE_iff d hd f' z)
      (fun _ => filter_subset _ _) vr
      (fun i => hGood4a (fun _ => false) (Pref i) (vi i)) hP_R
private lemma z23 (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (S₁ : Finset (z6 (nOf q m)))
    (f₁ : {e : z6 (nOf q m) // e ∈ S₁} → Bool)
    (d' : Fin (nOf q m))
    (V0 V1 V2 E Bc_np Bc'_np Bc0 Bc'0 : Finset (Fin (nOf q m)))
    (e_enum : Fin m → Fin (nOf q m))
    (he_inj : Function.Injective e_enum)
    (he_eq : E = univ.image e_enum)
    (hS0_sub : ze (zn q m hq hlp) ⊆ S₁)
    (hd'_V0 : d' ∈ V0)
    (hV0_sub : V0 ⊆ zj q m hq hlp (z1 (z0 S₁ f₁ (fun _ => false))))
    (hV1_sub : V1 ⊆ zj q m hq hlp (z1 (z0 S₁ f₁ (fun _ => false))))
    (hV2_sub : V2 ⊆ zj q m hq hlp (z1 (z0 S₁ f₁ (fun _ => false))))
    (hV0_card : V0.card = R4Of m) (hV2_card : V2.card = R4Of m)
    (hV1_lo : (1 / 12 : ℝ) * ((ROf m : ℝ) ^ 2) ≤ (V1.card : ℝ))
    (hV1_hi : (V1.card : ℝ) ≤ 2 * ((ROf m : ℝ) ^ 2))
    (hV01 : Disjoint V0 V1) (hV02 : Disjoint V0 V2) (hV12 : Disjoint V1 V2)
    (hV_cover : zj q m hq hlp (z1 (z0 S₁ f₁ (fun _ => false))) ⊆ V0 ∪ V1 ∪ V2)
    (hBc_np_eq : Bc_np = zr q m hq hlp (z1 (z0 S₁ f₁ (fun _ => false))) \ zn q m hq hlp)
    (hBc'_np_eq : Bc'_np = zp q m hq hlp (z1 (z0 S₁ f₁ (fun _ => false))) \ zn q m hq hlp)
    (hBc0_eq : Bc0 = Bc_np \ Bc'_np) (hBc'0_eq : Bc'0 = Bc'_np \ Bc_np)
    (hE_sub : E ⊆ Bc'0) (hE_card : E.card = m)
    (hBc_hi : (Bc_np.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc'_hi : (Bc'_np.card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc0_lo : (ROf m : ℝ) / 4 ≤ (Bc0.card : ℝ))
    (hBc'0_lo : (ROf m : ℝ) / 4 ≤ (Bc'0.card : ℝ))
    (hdisj_S1_V12_E : Disjoint S₁ (z8 (V1 ∪ V2) E))
    (hdisj_S1_4a : Disjoint S₁ (z8 (Bc'0 \ E) V1))
    (hdisj_S1_Bb0_Bc0 : Disjoint S₁ (z8 (V0 ∪ V1 ∪ V2) Bc0))
    (hdisj_S1_V2 : Disjoint S₁ (z8 V2 (Bc'_np \ E)))
    (hdisj_S1_6 : Disjoint S₁ (z8 (Bc'0 \ E) Bc_np))
    (hV0_no_E : ∀ w ∈ V0, w ≠ d' → ∀ z ∈ E, ∀ f : {e // e ∉ S₁} → Bool, ¬ (z1 (z0 S₁ f₁ f)).Adj w z)
    (hE_iff : ∀ d ∈ V2, ∀ f : {e // e ∉ S₁} → Bool, ∀ z : Fin (nOf q m),
      inE q hq (z1 (z0 S₁ f₁ f)) (mkA q m hq hlp d d') z ↔ ∃ j : Fin m, z = e_enum j) :
    z4 ((ROf m : ℝ)⁻¹) (fun f_rem : {e : z6 (nOf q m) // e ∉ S₁} → Bool =>
      z1 (z0 S₁ f₁ f_rem) ∈
        EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ) ≤
      8 / 256 := by
  classical
  set R := ROf m
  set R8 := R8Of m
  set T := zd (m - 1)
  set p : ℝ := (R : ℝ)⁻¹
  have vg : R8 ≤ R := by
    change R8Of m ≤ ROf m; rw [zq]; exact Nat.le_self_pow (by norm_num) _
  have vp : 10000 ≤ R := le_trans hlp.hR8_ge vg
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  let G₁ := z1 (z0 S₁ f₁ (fun _ => false))
  have v0' : Disjoint (V0 ∪ V1 ∪ V2) Bc'_np := by
    rw [disjoint_left]; intro w hwV hwB
    rw [hBc'_np_eq] at hwB
    have hwBb : w ∈ zj q m hq hlp G₁ := by
      rcases mem_union.mp hwV with h01 | h2
      · rcases mem_union.mp h01 with h0 | h1
        · exact hV0_sub h0
        · exact hV1_sub h1
      · exact hV2_sub h2
    exact (mem_filter.mp hwBb).2.2.2.1 (mem_filter.mp (sdiff_subset hwB)).2
  have v0 : Disjoint (V0 ∪ V1 ∪ V2) Bc_np := by
    rw [disjoint_left]; intro w hwV hwB
    rw [hBc_np_eq] at hwB
    have hwBb : w ∈ zj q m hq hlp G₁ := by
      rcases mem_union.mp hwV with h01 | h2
      · rcases mem_union.mp h01 with h0 | h1
        · exact hV0_sub h0
        · exact hV1_sub h1
      · exact hV2_sub h2
    exact (mem_filter.mp hwBb).2.2.1 (mem_filter.mp (sdiff_subset hwB)).2
  have hE_sub_Bc' : E ⊆ Bc'_np := fun z hz => sdiff_subset (hBc'0_eq ▸ hE_sub hz)
  have v2 : Disjoint (V1 ∪ V2) E :=
    (v0'.mono_left fun w hw => by
      rcases mem_union.mp hw with h1 | h2
      · exact mem_union_left _ (mem_union_right _ h1)
      · exact mem_union_right _ h2).mono_right hE_sub_Bc'
  have v7 : Disjoint V1 E := v2.mono_left subset_union_left
  have v1 : Disjoint V2 E := v2.mono_left subset_union_right
  have v4 : Disjoint S₁ (z8 V1 E) := by
    refine hdisj_S1_V12_E.mono_right fun ⟨e, he⟩ he1 => ?_
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
      change z7 u v huv ∈ z8 (V1 ∪ V2) E
      rw [z5 _ _ huv]
      rcases (z5 V1 E huv).mp he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨mem_union_left _ h1, h2⟩
      · exact Or.inr ⟨mem_union_left _ h1, h2⟩
  have v3 : Disjoint S₁ (z8 V2 E) := by
    refine hdisj_S1_V12_E.mono_right fun ⟨e, he⟩ he1 => ?_
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
      change z7 u v huv ∈ z8 (V1 ∪ V2) E
      rw [z5 _ _ huv]
      rcases (z5 V2 E huv).mp he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨mem_union_right _ h1, h2⟩
      · exact Or.inr ⟨mem_union_right _ h1, h2⟩
  let S₂ : Finset (z6 (nOf q m)) := S₁ ∪ z8 (V1 ∪ V2) E
  let Good3 : (z6 (nOf q m) → Bool) → Prop := fun f =>
    (∀ d ∈ V2, ∀ z ∈ E, ¬ (z1 f).Adj d z) ∧
    ((∀ z ∈ E, ((V1.filter (fun w => (z1 f).Adj w z)).card : ℝ) ≤ 4 * (R : ℝ)) ∧
     (∀ z ∈ E, (R : ℝ) / 48 ≤
       ((V1.filter (fun w => (z1 f).Adj w z ∧
         ∀ z' ∈ E, z' ≠ z → ¬ (z1 f).Adj w z')).card : ℝ)))
  have vc : ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ S₂, f e = g e) → (Good3 f ↔ Good3 g) := by
    intro f g hfg
    have hadj : ∀ w ∈ V1 ∪ V2, ∀ z ∈ E, (z1 f).Adj w z ↔ (z1 g).Adj w z := by
      intro w hw z hz
      have hne : w ≠ z := fun h => disjoint_left.mp v2 hw (h ▸ hz)
      rw [za f hne, za g hne,
        hfg _ (mem_union_right _ ((z5 (V1 ∪ V2) E hne).mpr (Or.inl ⟨hw, hz⟩)))]
    refine and_congr (forall₂_congr fun d hd => forall₂_congr fun z hz => not_congr (hadj d (mem_union_right _ hd) z hz))
      (and_congr (forall₂_congr fun z hz => by rw [filter_congr fun w hw => hadj w (mem_union_left _ hw) z hz])
        (forall₂_congr fun z hz => by
          rw [filter_congr fun w hw => and_congr (hadj w (mem_union_left _ hw) z hz)
            (forall₂_congr fun z' hz' => imp_congr_right fun _ => not_congr (hadj w (mem_union_left _ hw) z' hz'))]))
  refine (zu hp0 hp1 S₁ S₂ subset_union_left f₁ Good3
    (fun f => z1 f ∈ EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ)
    vc (ε₁ := 2 / 256) (ε₂ := 6 / 256) (by norm_num) ?_ ?_).trans (by norm_num)
  ·
    have vs : z4 p (fun f_rem : {e // e ∉ S₁} → Bool =>
          ¬ ∀ d ∈ V2, ∀ z ∈ E, ¬ (z1 (z0 S₁ f₁ f_rem)).Adj d z) ≤ 1 / 256 := by
      have vn : z4 p (fun f_rem : {e // e ∉ S₁} → Bool =>
            ¬ ∀ d ∈ V2, ∀ z ∈ E, ¬ (z1 (z0 S₁ f₁ f_rem)).Adj d z) ≤
          z4 p (fun f_rem : {e // e ∉ S₁} → Bool =>
            ∃ d ∈ V2, ∃ z ∈ E, ∃ (h : d ≠ z) (hmem : z7 d z h ∉ S₁), f_rem ⟨z7 d z h, hmem⟩ = true) := by
        refine zi hp0 hp1 fun f_rem hnot => ?_
        push Not at hnot
        rcases hnot with ⟨d, hd, z, hz, hadj⟩
        have hne : d ≠ z := fun h => disjoint_left.mp v1 hd (h ▸ hz)
        have vm : z7 d z hne ∉ S₁ := disjoint_right.mp v3
          ((z5 V2 E hne).mpr (Or.inl ⟨hd, hz⟩))
        exact ⟨d, hd, z, hz, (zb S₁ f₁ f_rem hne vm).mp hadj⟩
      refine vn.trans ((z12 hp0 hp1 S₁ V2 E v1 v3).trans ?_)
      rw [hV2_card, hE_card]
      exact (yi q m hlp).2.2.2.2
    have vr : z4 p (fun f_rem : {e // e ∉ S₁} → Bool =>
          ¬ ((∀ z ∈ E, ((V1.filter (fun w => (z1 (z0 S₁ f₁ f_rem)).Adj w z)).card : ℝ) ≤ 4 * (R : ℝ)) ∧
             (∀ z ∈ E, (R : ℝ) / 48 ≤
               ((V1.filter (fun w => (z1 (z0 S₁ f₁ f_rem)).Adj w z ∧
                 ∀ z' ∈ E, z' ≠ z → ¬ (z1 (z0 S₁ f₁ f_rem)).Adj w z')).card : ℝ)))) ≤ 1 / 256 := by
      have vh : m ≤ T := y9 m (by have := hlp.hm; omega)
      have vi : 4 * (E.card : ℝ) ≤ (R : ℝ) := by
        have vo : T ≤ R8 := le_trans (Nat.le_self_pow (by norm_num) T) (Nat.le_of_lt Nat.lt_two_pow_self)
        have h4R8 : 4 * R8 ≤ R := by
          have hpow : R8 ^ 2 ≤ R8 ^ 8 := Nat.pow_le_pow_right (z1e m) (by norm_num)
          have hreq : R = R8 ^ 8 := zq m
          have hge := hlp.hR8_ge
          nlinarith only [hpow, hreq, hge]
        exact_mod_cast (show 4 * E.card ≤ R by omega)
      have vk : z4 p (fun f_rem : {e // e ∉ S₁} → Bool =>
            ¬ ((∀ z ∈ E, ((V1.filter (fun w => (z1 (z0 S₁ f₁ f_rem)).Adj w z)).card : ℝ) ≤ 4 * (R : ℝ)) ∧
               (∀ z ∈ E, (R : ℝ) / 48 ≤
                 ((V1.filter (fun w => (z1 (z0 S₁ f₁ f_rem)).Adj w z ∧
                   ∀ z' ∈ E, z' ≠ z → ¬ (z1 (z0 S₁ f₁ f_rem)).Adj w z')).card : ℝ)))) =
          z4 p (fun f_rem : {e // e ∉ S₁} → Bool =>
            ¬ ((∀ z ∈ E, ((V1.filter (fun w =>
                  ∃ (h : w ≠ z) (hmem : z7 w z h ∉ S₁), f_rem ⟨z7 w z h, hmem⟩ = true)).card : ℝ) ≤ 4 * (R : ℝ)) ∧
               (∀ z ∈ E, (R : ℝ) / 48 ≤
                 ((V1.filter (fun w =>
                   (∃ (h : w ≠ z) (hmem : z7 w z h ∉ S₁), f_rem ⟨z7 w z h, hmem⟩ = true) ∧
                   ∀ z' ∈ E, z' ≠ z →
                     ¬ ∃ (h : w ≠ z') (hmem : z7 w z' h ∉ S₁), f_rem ⟨z7 w z' h, hmem⟩ = true)).card : ℝ)))) := by
        refine zx p fun f_rem => not_congr ?_
        have hadj : ∀ w ∈ V1, ∀ z ∈ E, (z1 (z0 S₁ f₁ f_rem)).Adj w z ↔
            ∃ (h : w ≠ z) (hmem : z7 w z h ∉ S₁), f_rem ⟨z7 w z h, hmem⟩ = true := by
          intro w hw z hz
          have hne : w ≠ z := fun h => disjoint_left.mp v7 hw (h ▸ hz)
          have hnot : z7 w z hne ∉ S₁ := disjoint_right.mp v4
            ((z5 V1 E hne).mpr (Or.inl ⟨hw, hz⟩))
          exact zb S₁ f₁ f_rem hne hnot
        exact and_congr
          (forall₂_congr fun z hz => by rw [filter_congr fun w hw => hadj w hw z hz])
          (forall₂_congr fun z hz => by
            rw [filter_congr fun w hw => and_congr (hadj w hw z hz)
              (forall₂_congr fun z' hz' => imp_congr_right fun _ => not_congr (hadj w hw z' hz'))])
      rw [vk]
      refine (yk vp S₁ V1 V1 E (Subset.refl _)
        v7 v4 hV1_lo hV1_hi vi).trans ?_
      rw [hE_card]
      have h1 : 2 * (m : ℝ) * exp (-((R : ℝ)) / 200) ≤
          ((nOf q m : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (T + 10) * exp (-((R8 : ℝ)) / 64) := by
        have vl := yf q m hlp
        have hm2 : 2 * (m : ℝ) ≤ ((nOf q m : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (T + 10) := by
          have hn1 : (1 : ℝ) ≤ (nOf q m : ℝ) ^ (kOf q + 4) := one_le_pow₀ (by exact_mod_cast wq q m)
          have h2 : 2 * m ≤ 2 ^ (T + 10) := by
            have : m ≤ 2 ^ T := le_trans vh (Nat.le_of_lt Nat.lt_two_pow_self)
            have : 2 * (2 ^ T) ≤ 2 ^ (T + 10) := by rw [← _root_.pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          have h2R : 2 * (m : ℝ) ≤ (2 : ℝ) ^ (T + 10) := by exact_mod_cast h2
          nlinarith only [hn1, h2R, Nat.cast_nonneg (α := ℝ) m]
        calc 2 * (m : ℝ) * exp (-((R : ℝ)) / 200)
            ≤ 2 * (m : ℝ) * exp (-((R8 : ℝ)) / 64) := mul_le_mul_of_nonneg_left vl.1 (by positivity)
          _ ≤ ((nOf q m : ℝ) ^ (kOf q + 4)) * (2 : ℝ) ^ (T + 10) * exp (-((R8 : ℝ)) / 64) :=
              mul_le_mul_of_nonneg_right hm2 (exp_pos _).le
      exact h1.trans hlp.hpoly_exp_R8
    have vq : z4 p (fun f_rem : {e // e ∉ S₁} → Bool => ¬ Good3 (z0 S₁ f₁ f_rem)) ≤
        z4 p (fun f_rem => ¬ ∀ d ∈ V2, ∀ z ∈ E, ¬ (z1 (z0 S₁ f₁ f_rem)).Adj d z) +
        z4 p (fun f_rem =>
          ¬ ((∀ z ∈ E, ((V1.filter (fun w => (z1 (z0 S₁ f₁ f_rem)).Adj w z)).card : ℝ) ≤ 4 * (R : ℝ)) ∧
             (∀ z ∈ E, (R : ℝ) / 48 ≤
               ((V1.filter (fun w => (z1 (z0 S₁ f₁ f_rem)).Adj w z ∧
                 ∀ z' ∈ E, z' ≠ z → ¬ (z1 (z0 S₁ f₁ f_rem)).Adj w z')).card : ℝ)))) := by
      refine (zi hp0 hp1 fun f_rem hnot => ?_).trans (yr hp0 hp1 _ _)
      dsimp only [Good3] at hnot; rw [not_and_or] at hnot; exact hnot
    linarith
  ·
    intro f₂ hagree hGood3
    rcases hGood3 (fun _ => false) with ⟨hV2_no_E0, hW_hi, hW_only_lo⟩
    have vf : ∀ f : {e // e ∉ S₂} → Bool, ∀ e ∈ S₁,
        z0 S₂ f₂ f e = z0 S₁ f₁ (fun _ => false) e := fun f e he => by
      have he2 : e ∈ S₂ := subset_union_left he
      simp only [z0, dif_pos he2, dif_pos he]; exact hagree ⟨e, he⟩
    have vj : ∀ f : {e // e ∉ S₂} → Bool, ∃ f' : {e // e ∉ S₁} → Bool,
        z0 S₂ f₂ f = z0 S₁ f₁ f' := fun f =>
      ⟨fun x => z0 S₂ f₂ f x.1, by
        funext e; by_cases h : e ∈ S₁
        · have heq := vf f e h; simp only [z0, dif_pos h] at heq ⊢; exact heq
        · simp only [z0, dif_neg h]⟩
    have v8 := zz q m hq hlp (z0 S₂ f₂ (fun _ => false))
      (z0 S₁ f₁ (fun _ => false)) (fun e he => vf (fun _ => false) e (hS0_sub he))
    have vd : z8 V1 E ⊆ S₂ := fun ⟨e, he⟩ he1 => by
      refine mem_union_right _ ?_
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        change z7 u v huv ∈ z8 (V1 ∪ V2) E
        rw [z5 _ _ huv]
        rcases (z5 V1 E huv).mp he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨mem_union_left _ h1, h2⟩
        · exact Or.inr ⟨mem_union_left _ h1, h2⟩
    have hdisj_Bc0_Bc' : Disjoint Bc0 Bc'_np := by rw [hBc0_eq]; exact sdiff_disjoint
    have va : Disjoint S₂ (z8 (Bc'0 \ E) V1) := by
      rw [disjoint_union_left]; refine ⟨hdisj_S1_4a, ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        rcases (z5 (V1 ∪ V2) E huv).mp he1 with ⟨hu12, hvE⟩ | ⟨hv12, huE⟩ <;>
          rcases (z5 (Bc'0 \ E) V1 huv).mp he2 with ⟨hu', hv1⟩ | ⟨hv', hu1⟩
        · exact disjoint_left.mp v0' (by rcases mem_union.mp hu12 with h1 | h2; exact mem_union_left _ (mem_union_right _ h1); exact mem_union_right _ h2)
            (sdiff_subset (hBc'0_eq ▸ sdiff_subset hu'))
        · exact (mem_sdiff.mp hv').2 hvE
        · exact (mem_sdiff.mp hu').2 huE
        · exact disjoint_left.mp v0' (by rcases mem_union.mp hv12 with h1 | h2; exact mem_union_left _ (mem_union_right _ h1); exact mem_union_right _ h2)
            (sdiff_subset (hBc'0_eq ▸ sdiff_subset hv'))
    have v5 : Disjoint S₂ (z8 (V0 ∪ V1 ∪ V2) Bc0) := by
      rw [disjoint_union_left]; refine ⟨hdisj_S1_Bb0_Bc0, ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        rcases (z5 (V1 ∪ V2) E huv).mp he1 with ⟨_, hvE⟩ | ⟨_, huE⟩ <;>
          rcases (z5 (V0 ∪ V1 ∪ V2) Bc0 huv).mp he2 with ⟨huV, hvB⟩ | ⟨hvV, huB⟩
        · exact disjoint_left.mp hdisj_Bc0_Bc' hvB (hE_sub_Bc' hvE)
        · exact disjoint_left.mp v0' hvV (hE_sub_Bc' hvE)
        · exact disjoint_left.mp v0' huV (hE_sub_Bc' huE)
        · exact disjoint_left.mp hdisj_Bc0_Bc' huB (hE_sub_Bc' huE)
    have v9 : Disjoint S₂ (z8 V2 (Bc'_np \ E)) := by
      rw [disjoint_union_left]; refine ⟨hdisj_S1_V2, ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        rcases (z5 (V1 ∪ V2) E huv).mp he1 with ⟨_, hvE⟩ | ⟨_, huE⟩ <;>
          rcases (z5 V2 (Bc'_np \ E) huv).mp he2 with ⟨hu2, hv'⟩ | ⟨hv2, hu'⟩
        · exact (mem_sdiff.mp hv').2 hvE
        · exact disjoint_left.mp v1 hv2 hvE
        · exact disjoint_left.mp v1 hu2 huE
        · exact (mem_sdiff.mp hu').2 huE
    have vb : Disjoint S₂ (z8 (Bc'0 \ E) Bc_np) := by
      rw [disjoint_union_left]; refine ⟨hdisj_S1_6, ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        have v6 : V1 ∪ V2 ⊆ V0 ∪ V1 ∪ V2 := fun w hw => by
          rcases mem_union.mp hw with h1 | h2
          · exact mem_union_left _ (mem_union_right _ h1)
          · exact mem_union_right _ h2
        rcases (z5 (V1 ∪ V2) E huv).mp he1 with ⟨hu12, _⟩ | ⟨hv12, _⟩ <;>
          rcases (z5 (Bc'0 \ E) Bc_np huv).mp he2 with ⟨hu', hvB⟩ | ⟨hv', huB⟩
        · exact disjoint_left.mp v0' (v6 hu12) (sdiff_subset (hBc'0_eq ▸ sdiff_subset hu'))
        · exact disjoint_left.mp v0 (v6 hu12) huB
        · exact disjoint_left.mp v0 (v6 hv12) hvB
        · exact disjoint_left.mp v0' (v6 hv12) (sdiff_subset (hBc'0_eq ▸ sdiff_subset hv'))
    have ve : ∀ d ∈ V2, ∀ z ∈ E, ∀ f : {e // e ∉ S₂} → Bool, ¬ (z1 (z0 S₂ f₂ f)).Adj d z := by
      intro d hd z hz f
      have hne : d ≠ z := fun h => disjoint_left.mp v1 hd (h ▸ hz)
      have hmem : z7 d z hne ∈ S₂ :=
        mem_union_right _ ((z5 (V1 ∪ V2) E hne).mpr (Or.inl ⟨mem_union_right _ hd, hz⟩))
      rw [zf S₂ f₂ f hne hmem, ← zf S₂ f₂ (fun _ => false) hne hmem]
      exact hV2_no_E0 d hd z hz
    exact z1w q m hq hlp S₂ f₂ d' V0 V1 V2 E Bc_np Bc'_np Bc0 Bc'0 e_enum he_inj he_eq
      (hS0_sub.trans subset_union_left) hd'_V0
      (v8.2.2.symm ▸ hV0_sub) (v8.2.2.symm ▸ hV1_sub) (v8.2.2.symm ▸ hV2_sub)
      hV0_card hV2_card hV1_lo hV1_hi hV01 hV02 hV12 (v8.2.2.symm ▸ hV_cover)
      (v8.1.symm ▸ hBc_np_eq) (v8.2.1.symm ▸ hBc'_np_eq) hBc0_eq hBc'0_eq hE_sub hE_card
      hBc_hi hBc'_hi hBc0_lo hBc'0_lo vd va v5 v9 vb
      (fun w hw hne z hz f => by rcases vj f with ⟨f', hf'⟩; rw [hf']; exact hV0_no_E w hw hne z hz f')
      ve
      (fun d hd f z => by rcases vj f with ⟨f', hf'⟩; rw [hf']; exact hE_iff d hd f' z)
      hW_hi hW_only_lo
private lemma z24 (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m)
    (f₀ : {e : z6 (nOf q m) // e ∈ ze (zn q m hq hlp)} → Bool)
    (hBc_lo : (ROf m : ℝ) / 3 ≤ ((zr q m hq hlp (z1 (z0 (ze (zn q m hq hlp)) f₀ (fun _ => false)))).card : ℝ))
    (hBc_hi : ((zr q m hq hlp (z1 (z0 (ze (zn q m hq hlp)) f₀ (fun _ => false)))).card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hBc'_lo : (ROf m : ℝ) / 3 ≤ ((zp q m hq hlp (z1 (z0 (ze (zn q m hq hlp)) f₀ (fun _ => false)))).card : ℝ))
    (hBc'_hi : ((zp q m hq hlp (z1 (z0 (ze (zn q m hq hlp)) f₀ (fun _ => false)))).card : ℝ) ≤ 2 * (ROf m : ℝ))
    (hInter : (zr q m hq hlp (z1 (z0 (ze (zn q m hq hlp)) f₀ (fun _ => false))) ∩
      zp q m hq hlp (z1 (z0 (ze (zn q m hq hlp)) f₀ (fun _ => false)))).card < KOf q m)
    (hBb0_lo : (1 / 4 : ℝ) * ((ROf m : ℝ) ^ 2) ≤ ((zj q m hq hlp (z1 (z0 (ze (zn q m hq hlp)) f₀ (fun _ => false)))).card : ℝ))
    (hBb0_hi : ((zj q m hq hlp (z1 (z0 (ze (zn q m hq hlp)) f₀ (fun _ => false)))).card : ℝ) ≤ 2 * ((ROf m : ℝ) ^ 2)) :
    z4 ((ROf m : ℝ)⁻¹) (fun f_rem : {e : z6 (nOf q m) // e ∉ ze (zn q m hq hlp)} → Bool =>
      z1 (z0 (ze (zn q m hq hlp)) f₀ f_rem) ∈
        EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ) ≤
      10 / 256 := by
  classical
  set R := ROf m
  set R4 := R4Of m
  set R8 := R8Of m
  set K := KOf q m
  set p : ℝ := (R : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  let P₀ := zn q m hq hlp
  let S₀ := ze P₀
  let G₀ := z1 (z0 S₀ f₀ (fun _ => false))
  let Bc := zr q m hq hlp G₀
  let Bc' := zp q m hq hlp G₀
  let Bb0 := zj q m hq hlp G₀
  let vb := Bc \ P₀
  let v0 := Bc' \ P₀
  let Bc0 := vb \ v0
  let Bc'0 := v0 \ vb
  have vn : P₀.card ≤ kOf q := by
    calc P₀.card ≤ (univ : Finset (Fin (3 * q - 4))).card := card_image_le
      _ = 3 * q - 4 := by simp
      _ ≤ kOf q := by unfold kOf; omega
  have ua : (K : ℝ) + (kOf q : ℝ) ≤ (R : ℝ) / 12 := by
    have h1 : K + kOf q ≤ R8 := by have := hlp.hK_le_R8; omega
    have ve : (R : ℝ) = (R8 : ℝ) ^ 8 := by exact_mod_cast zq m
    have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
    have hpow : (R8 : ℝ) ^ 2 ≤ (R8 : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h1R : (K : ℝ) + (kOf q : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast h1
    rw [ve]; nlinarith only [h1R, hR8_ge, hpow]
  have vt : (vb.card : ℝ) ≤ 2 * (R : ℝ) :=
    (Nat.cast_le.mpr (card_le_card sdiff_subset)).trans hBc_hi
  have v7 : (v0.card : ℝ) ≤ 2 * (R : ℝ) :=
    (Nat.cast_le.mpr (card_le_card sdiff_subset)).trans hBc'_hi
  have u0 : (R : ℝ) / 4 ≤ (Bc0.card : ℝ) := by
    have hcov : Bc ⊆ Bc0 ∪ (Bc ∩ Bc') ∪ P₀ := by
      intro z hz
      by_cases hP : z ∈ P₀
      · exact mem_union_right _ hP
      · by_cases h' : z ∈ Bc'
        · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hz, h'⟩))
        · exact mem_union_left _ (mem_union_left _
            (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hz, hP⟩, fun h => h' (sdiff_subset h)⟩))
    have hle : Bc.card ≤ Bc0.card + (Bc ∩ Bc').card + P₀.card := by
      calc Bc.card ≤ (Bc0 ∪ (Bc ∩ Bc') ∪ P₀).card := card_le_card hcov
        _ ≤ (Bc0 ∪ (Bc ∩ Bc')).card + P₀.card := card_union_le _ _
        _ ≤ Bc0.card + (Bc ∩ Bc').card + P₀.card := Nat.add_le_add_right (card_union_le _ _) _
    have hc : (Bc.card : ℝ) ≤ (Bc0.card : ℝ) + ((Bc ∩ Bc').card : ℝ) + (P₀.card : ℝ) := by exact_mod_cast hle
    have hI : ((Bc ∩ Bc').card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hInter.le
    have hP : (P₀.card : ℝ) ≤ (kOf q : ℝ) := by exact_mod_cast vn
    linarith
  have vo : (R : ℝ) / 4 ≤ (Bc'0.card : ℝ) := by
    have hcov : Bc' ⊆ Bc'0 ∪ (Bc ∩ Bc') ∪ P₀ := by
      intro z hz
      by_cases hP : z ∈ P₀
      · exact mem_union_right _ hP
      · by_cases h' : z ∈ Bc
        · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨h', hz⟩))
        · exact mem_union_left _ (mem_union_left _
            (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hz, hP⟩, fun h => h' (sdiff_subset h)⟩))
    have hle : Bc'.card ≤ Bc'0.card + (Bc ∩ Bc').card + P₀.card := by
      calc Bc'.card ≤ (Bc'0 ∪ (Bc ∩ Bc') ∪ P₀).card := card_le_card hcov
        _ ≤ (Bc'0 ∪ (Bc ∩ Bc')).card + P₀.card := card_union_le _ _
        _ ≤ Bc'0.card + (Bc ∩ Bc').card + P₀.card := Nat.add_le_add_right (card_union_le _ _) _
    have hc : (Bc'.card : ℝ) ≤ (Bc'0.card : ℝ) + ((Bc ∩ Bc').card : ℝ) + (P₀.card : ℝ) := by exact_mod_cast hle
    have hI : ((Bc ∩ Bc').card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hInter.le
    have hP : (P₀.card : ℝ) ≤ (kOf q : ℝ) := by exact_mod_cast vn
    linarith
  have u3 : 2 * R4 ≤ Bb0.card := by
    have vq : (R4 : ℝ) = (R8 : ℝ) ^ 2 := by exact_mod_cast z1r m
    have ve : (R : ℝ) = (R4 : ℝ) ^ 4 := by exact_mod_cast wz m
    have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
    have vg : (10000 : ℝ) ≤ (R4 : ℝ) := by rw [vq]; nlinarith only [hR8_ge]
    have hpow : (R4 : ℝ) ^ 2 ≤ (R4 : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have vf : 8 * (R4 : ℝ) ≤ (R : ℝ) := by rw [ve]; nlinarith only [vg, hpow]
    have h1 : (2 * R4 : ℝ) ≤ (Bb0.card : ℝ) := by nlinarith only [hBb0_lo, vf, vg]
    exact_mod_cast h1
  obtain ⟨V0, hV0_sub, hV0_card⟩ := exists_subset_card_eq (s := Bb0) (n := R4) (by omega)
  have vj : R4 ≤ (Bb0 \ V0).card := by
    rw [card_sdiff, inter_eq_left.mpr hV0_sub]; omega
  obtain ⟨V2, hV2_sub_sd, hV2_card⟩ := exists_subset_card_eq (s := Bb0 \ V0) (n := R4) vj
  have v4 : V2 ⊆ Bb0 := hV2_sub_sd.trans sdiff_subset
  let V1 := Bb0 \ (V0 ∪ V2)
  have v5 : V1 ⊆ Bb0 := sdiff_subset
  have hV02 : Disjoint V0 V2 := disjoint_left.mpr fun w hw0 hw2 => (mem_sdiff.mp (hV2_sub_sd hw2)).2 hw0
  have hV01 : Disjoint V0 V1 := disjoint_left.mpr fun w hw0 hw1 => (mem_sdiff.mp hw1).2 (mem_union_left _ hw0)
  have hV12 : Disjoint V1 V2 := disjoint_left.mpr fun w hw1 hw2 => (mem_sdiff.mp hw1).2 (mem_union_right _ hw2)
  have vv : Bb0 ⊆ V0 ∪ V1 ∪ V2 := fun w hw => by
    by_cases h0 : w ∈ V0
    · exact mem_union_left _ (mem_union_left _ h0)
    · by_cases h2 : w ∈ V2
      · exact mem_union_right _ h2
      · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨hw, by simp [h0, h2]⟩))
  have u6 : (1 / 12 : ℝ) * ((R : ℝ) ^ 2) ≤ (V1.card : ℝ) := by
    have hsd : V1.card = Bb0.card - (V0 ∪ V2).card := by
      change (Bb0 \ (V0 ∪ V2)).card = _; rw [card_sdiff, inter_eq_left.mpr (union_subset hV0_sub v4)]
    have hun : (V0 ∪ V2).card = 2 * R4 := by rw [card_union_of_disjoint hV02, hV0_card, hV2_card]; ring
    have hc : (Bb0.card : ℝ) ≤ (V1.card : ℝ) + 2 * (R4 : ℝ) := by
      have : Bb0.card ≤ V1.card + 2 * R4 := by omega
      exact_mod_cast this
    have vq : (R4 : ℝ) = (R8 : ℝ) ^ 2 := by exact_mod_cast z1r m
    have ve : (R : ℝ) = (R4 : ℝ) ^ 4 := by exact_mod_cast wz m
    have hR8_ge : (10000 : ℝ) ≤ (R8 : ℝ) := by exact_mod_cast hlp.hR8_ge
    have vg : (10000 : ℝ) ≤ (R4 : ℝ) := by rw [vq]; nlinarith only [hR8_ge]
    have hpow : (R4 : ℝ) ^ 2 ≤ (R4 : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have vf : 8 * (R4 : ℝ) ≤ (R : ℝ) := by rw [ve]; nlinarith only [vg, hpow]
    nlinarith only [hBb0_lo, hc, vf, vg]
  have u7 : (V1.card : ℝ) ≤ 2 * ((R : ℝ) ^ 2) :=
    (Nat.cast_le.mpr (card_le_card v5)).trans hBb0_hi
  have v2 : Disjoint P₀ Bb0 := disjoint_left.mpr fun v hvP hvB => (mem_filter.mp hvB).2.1 hvP
  have v1 : Disjoint P₀ vb := sdiff_disjoint.symm
  have v1' : Disjoint P₀ v0 := sdiff_disjoint.symm
  have hdisj_V0_Bc' : Disjoint V0 v0 := disjoint_left.mpr fun w hw0 hwB =>
    (mem_filter.mp (hV0_sub hw0)).2.2.2.1 (mem_filter.mp (sdiff_subset hwB)).2
  have hdisj_S0_V0_Bc' : Disjoint S₀ (z8 V0 v0) :=
    zo (v2.mono_right hV0_sub) v1'
  let S₁ : Finset (z6 (nOf q m)) := S₀ ∪ z8 V0 v0
  let Good2 : (z6 (nOf q m) → Bool) → Prop := fun f =>
    (∃ d' ∈ V0, (v0.filter (fun z => (z1 f).Adj d' z)).card = m ∧
      v0.filter (fun z => (z1 f).Adj d' z) ⊆ Bc'0) ∧
    (∀ v₁ ∈ V0, ∀ v₂ ∈ V0, v₁ ≠ v₂ → ∀ z ∈ v0,
      ¬ ((z1 f).Adj v₁ z ∧ (z1 f).Adj v₂ z))
  have vr : ∀ f g : z6 (nOf q m) → Bool,
      (∀ e ∈ S₁, f e = g e) → (Good2 f ↔ Good2 g) := by
    intro f g hfg
    have hadj : ∀ v ∈ V0, ∀ z ∈ v0, (z1 f).Adj v z ↔ (z1 g).Adj v z := by
      intro v hv z hz
      have hne : v ≠ z := fun h => disjoint_left.mp hdisj_V0_Bc' hv (h ▸ hz)
      rw [za f hne, za g hne,
        hfg _ (mem_union_right _ ((z5 V0 v0 hne).mpr (Or.inl ⟨hv, hz⟩)))]
    refine and_congr ?_ ?_
    · refine exists_congr fun d' => and_congr_right fun hd' => ?_
      rw [filter_congr fun z hz => hadj d' hd' z hz]
    · exact forall₂_congr fun v₁ hv₁ => forall₂_congr fun v₂ hv₂ => imp_congr_right fun _ =>
        forall₂_congr fun z hz => not_congr (and_congr (hadj v₁ hv₁ z hz) (hadj v₂ hv₂ z hz))
  refine (zu hp0 hp1 S₀ S₁ subset_union_left f₀ Good2
    (fun f => z1 f ∈ EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ)
    vr (ε₁ := 2 / 256) (ε₂ := 8 / 256) (by norm_num) ?_ ?_).trans (by norm_num)
  ·
    have ui : z4 p (fun f_rem : {e // e ∉ S₀} → Bool =>
          ¬ ∃ d' ∈ V0, (v0.filter (fun z => (z1 (z0 S₀ f₀ f_rem)).Adj d' z)).card = m ∧
            v0.filter (fun z => (z1 (z0 S₀ f₀ f_rem)).Adj d' z) ⊆ Bc'0) ≤ 1 / 256 := by
      let Tv : Fin (nOf q m) → Finset {e : z6 (nOf q m) // e ∉ S₀} := fun v =>
        if hv : v ∈ V0 then
          v0.attach.image (fun (z : {w // w ∈ v0}) =>
            have hne : v ≠ z.1 := fun h => disjoint_left.mp hdisj_V0_Bc' hv (h ▸ z.2)
            ⟨z7 v z.1 hne, disjoint_right.mp hdisj_S0_V0_Bc'
              ((z5 V0 v0 hne).mpr (Or.inl ⟨hv, z.2⟩))⟩)
        else ∅
      have vx : Set.PairwiseDisjoint (V0 : Set (Fin (nOf q m))) Tv := by
        intro v₁ hv₁ v₂ hv₂ hne
        have hv₁' : v₁ ∈ V0 := mem_coe.mp hv₁
        have hv₂' : v₂ ∈ V0 := mem_coe.mp hv₂
        change Disjoint (Tv v₁) (Tv v₂)
        rw [disjoint_left]; intro e he₁ he₂
        dsimp only [Tv] at he₁ he₂; rw [dif_pos hv₁'] at he₁; rw [dif_pos hv₂'] at he₂
        rcases mem_image.mp he₁ with ⟨z₁, _, rfl⟩
        rcases mem_image.mp he₂ with ⟨z₂, _, heq⟩
        rcases zv heq with ⟨hvv, _⟩ | ⟨hvz, _⟩
        · exact hne hvv.symm
        · exact disjoint_left.mp hdisj_V0_Bc' hv₂' (hvz ▸ z₁.2)
      let OkV : Fin (nOf q m) → ({e : z6 (nOf q m) // e ∉ S₀} → Bool) → Prop := fun v f_rem =>
        (v0.filter (fun z => (z1 (z0 S₀ f₀ f_rem)).Adj v z)).card = m ∧
        v0.filter (fun z => (z1 (z0 S₀ f₀ f_rem)).Adj v z) ⊆ Bc'0
      have hdep : ∀ v ∈ V0, ∀ f g : {e // e ∉ S₀} → Bool, (∀ x ∈ Tv v, f x = g x) → (OkV v f ↔ OkV v g) := by
        intro v hv f g hfg
        have hadj : ∀ z (hz : z ∈ v0),
            (z1 (z0 S₀ f₀ f)).Adj v z ↔ (z1 (z0 S₀ f₀ g)).Adj v z := by
          intro z hz
          have hne : v ≠ z := fun h => disjoint_left.mp hdisj_V0_Bc' hv (h ▸ hz)
          have hnot : z7 v z hne ∉ S₀ := disjoint_right.mp hdisj_S0_V0_Bc'
            ((z5 V0 v0 hne).mpr (Or.inl ⟨hv, hz⟩))
          have hmem : (⟨z7 v z hne, hnot⟩ : {e // e ∉ S₀}) ∈ Tv v := by
            dsimp only [Tv]; rw [dif_pos hv]
            exact mem_image.mpr ⟨⟨z, hz⟩, mem_attach _ _, rfl⟩
          rw [zb S₀ f₀ f hne hnot, zb S₀ f₀ g hne hnot]
          have heq := hfg _ hmem
          exact ⟨fun ⟨_, _, hf⟩ => ⟨hne, hnot, by rwa [← heq]⟩, fun ⟨_, _, hg⟩ => ⟨hne, hnot, by rwa [heq]⟩⟩
        dsimp only [OkV]
        rw [filter_congr fun z hz => hadj z hz]
      have vz : ∀ v ∈ V0, QOf m ≤ z4 p (OkV v) := by
        intro v hv
        have vu : v ∉ v0 := fun h => disjoint_left.mp hdisj_V0_Bc' hv h
        have vs : Disjoint S₀ (z8 {v} v0) :=
          zo (disjoint_singleton_right.mpr (disjoint_right.mp v2 (hV0_sub hv)))
            v1'
        have hEX := z0t q m hlp S₀ v v0 Bc'0 sdiff_subset vu
          v7 vo vs
        refine hEX.trans (zi hp0 hp1 fun f_rem h => ?_)
        have hflt : v0.filter (fun z => (z1 (z0 S₀ f₀ f_rem)).Adj v z) =
            v0.filter (fun z => ∃ (h : v ≠ z) (hmem : z7 v z h ∉ S₀), f_rem ⟨z7 v z h, hmem⟩ = true) := by
          refine filter_congr fun z hz => ?_
          have hne : v ≠ z := fun h => vu (h ▸ hz)
          have hnot : z7 v z hne ∉ S₀ := disjoint_right.mp vs
            ((z5 {v} v0 hne).mpr (Or.inl ⟨mem_singleton_self _, hz⟩))
          exact zb S₀ f₀ f_rem hne hnot
        dsimp only [OkV]; rwa [hflt]
      have u5 : z4 p (fun f_rem : {e // e ∉ S₀} → Bool => ¬ ∃ d' ∈ V0, OkV d' f_rem) =
          z4 p (fun f_rem : {e // e ∉ S₀} → Bool => ∀ v ∈ V0, ¬ OkV v f_rem) :=
        zx p fun _ => by simp
      rw [u5, y5 V0 Tv vx p (fun v f => ¬ OkV v f)
        (fun v hv f g hfg => not_congr (hdep v hv f g hfg))]
      have hfac : ∀ v ∈ V0, z4 p (fun f => ¬ OkV v f) ≤ exp (-(QOf m)) := by
        intro v hv; rw [wg]; linarith [vz v hv, Real.add_one_le_exp (-(QOf m))]
      calc (∏ v ∈ V0, z4 p (fun f => ¬ OkV v f))
          ≤ ∏ _v ∈ V0, exp (-(QOf m)) := prod_le_prod (fun _ _ => ym hp0 hp1 _) hfac
        _ = (exp (-(QOf m))) ^ V0.card := prod_const _
        _ = exp ((V0.card : ℝ) * (-(QOf m))) := (exp_nat_mul _ _).symm
        _ ≤ exp (-((R8 : ℝ))) := by
            rw [hV0_card]; refine exp_le_exp.mpr ?_
            linarith [(yi q m hlp).2.1]
        _ ≤ 1 / 256 := (yi q m hlp).2.2.1
    have uh : z4 p (fun f_rem : {e // e ∉ S₀} → Bool =>
          ¬ ∀ v₁ ∈ V0, ∀ v₂ ∈ V0, v₁ ≠ v₂ → ∀ z ∈ v0,
            ¬ ((z1 (z0 S₀ f₀ f_rem)).Adj v₁ z ∧
               (z1 (z0 S₀ f₀ f_rem)).Adj v₂ z)) ≤ 1 / 256 := by
      have ud : z4 p (fun f_rem : {e // e ∉ S₀} → Bool =>
            ¬ ∀ v₁ ∈ V0, ∀ v₂ ∈ V0, v₁ ≠ v₂ → ∀ z ∈ v0,
              ¬ ((z1 (z0 S₀ f₀ f_rem)).Adj v₁ z ∧
                 (z1 (z0 S₀ f₀ f_rem)).Adj v₂ z)) ≤
          z4 p (fun f_rem : {e // e ∉ S₀} → Bool =>
            ∃ v₁ ∈ V0, ∃ v₂ ∈ V0, v₁ ≠ v₂ ∧ ∃ z ∈ v0,
              (∃ (h : v₁ ≠ z) (hmem : z7 v₁ z h ∉ S₀), f_rem ⟨z7 v₁ z h, hmem⟩ = true) ∧
              (∃ (h : v₂ ≠ z) (hmem : z7 v₂ z h ∉ S₀), f_rem ⟨z7 v₂ z h, hmem⟩ = true)) := by
        refine zi hp0 hp1 fun f_rem hnot => ?_
        push Not at hnot
        rcases hnot with ⟨v₁, hv₁, v₂, hv₂, hne, z, hz, ha1, ha2⟩
        have hne1 : v₁ ≠ z := fun h => disjoint_left.mp hdisj_V0_Bc' hv₁ (h ▸ hz)
        have hne2 : v₂ ≠ z := fun h => disjoint_left.mp hdisj_V0_Bc' hv₂ (h ▸ hz)
        have uc : z7 v₁ z hne1 ∉ S₀ := disjoint_right.mp hdisj_S0_V0_Bc'
          ((z5 V0 v0 hne1).mpr (Or.inl ⟨hv₁, hz⟩))
        have ub : z7 v₂ z hne2 ∉ S₀ := disjoint_right.mp hdisj_S0_V0_Bc'
          ((z5 V0 v0 hne2).mpr (Or.inl ⟨hv₂, hz⟩))
        exact ⟨v₁, hv₁, v₂, hv₂, hne, z, hz,
          (zb S₀ f₀ f_rem hne1 uc).mp ha1,
          (zb S₀ f₀ f_rem hne2 ub).mp ha2⟩
      refine ud.trans ((wi hp0 hp1 S₀ V0 v0 hdisj_V0_Bc' hdisj_S0_V0_Bc').trans ?_)
      have uj : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (R_pos m)
      have ve : (R : ℝ) = (R2Of m : ℝ) ^ 2 := by exact_mod_cast z15 m
      have u8 : (R2Of m : ℝ) = (R4 : ℝ) ^ 2 := by exact_mod_cast z2f m
      have uf : ((V0.card : ℝ) ^ 2) * (v0.card : ℝ) * p ^ 2 ≤ 2 / (R2Of m : ℝ) := by
        rw [hV0_card]
        calc ((R4 : ℝ) ^ 2) * (v0.card : ℝ) * p ^ 2
            ≤ ((R4 : ℝ) ^ 2) * (2 * (R : ℝ)) * p ^ 2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left v7 (by positivity)) (by positivity)
          _ = 2 / (R2Of m : ℝ) := by
              rw [show p = (R : ℝ)⁻¹ from rfl, ← u8, ve]; field_simp
      exact uf.trans (yi q m hlp).2.2.2.1
    have ug : z4 p (fun f_rem : {e // e ∉ S₀} → Bool => ¬ Good2 (z0 S₀ f₀ f_rem)) ≤
        z4 p (fun f_rem => ¬ ∃ d' ∈ V0, (v0.filter (fun z => (z1 (z0 S₀ f₀ f_rem)).Adj d' z)).card = m ∧
          v0.filter (fun z => (z1 (z0 S₀ f₀ f_rem)).Adj d' z) ⊆ Bc'0) +
        z4 p (fun f_rem => ¬ ∀ v₁ ∈ V0, ∀ v₂ ∈ V0, v₁ ≠ v₂ → ∀ z ∈ v0,
          ¬ ((z1 (z0 S₀ f₀ f_rem)).Adj v₁ z ∧ (z1 (z0 S₀ f₀ f_rem)).Adj v₂ z)) := by
      refine (zi hp0 hp1 fun f_rem hnot => ?_).trans (yr hp0 hp1 _ _)
      dsimp only [Good2] at hnot; rw [not_and_or] at hnot; exact hnot
    linarith
  ·
    intro f₁ hagree hGood2
    rcases hGood2 (fun _ => false) with ⟨⟨d', hd'_V0, hE_card, hE_sub⟩, hNoShare⟩
    let G₁ := z1 (z0 S₁ f₁ (fun _ => false))
    let E := v0.filter (fun z => G₁.Adj d' z)
    have vy : ∀ f : {e // e ∉ S₁} → Bool, ∀ e ∈ S₀,
        z0 S₁ f₁ f e = z0 S₀ f₀ (fun _ => false) e := fun f e he => by
      have he1 : e ∈ S₁ := subset_union_left he
      simp only [z0, dif_pos he1, dif_pos he]; exact hagree ⟨e, he⟩
    have vh := zz q m hq hlp (z0 S₁ f₁ (fun _ => false))
      (z0 S₀ f₀ (fun _ => false)) (vy (fun _ => false))
    let vc : E ≃ Fin m := E.equivFinOfCardEq hE_card
    let v9 : Fin m → Fin (nOf q m) := fun j => (vc.symm j).1
    have u4 : Function.Injective v9 := fun j₁ j₂ heq =>
      vc.symm.injective (Subtype.ext heq)
    have u2 : E = univ.image v9 := by
      ext z; simp only [mem_image, mem_univ, true_and, v9]
      exact ⟨fun hz => ⟨vc ⟨z, hz⟩, by simp⟩, fun ⟨j, hj⟩ => hj ▸ (vc.symm j).2⟩
    have hdisj_Bc0_Bc' : Disjoint Bc0 v0 := sdiff_disjoint
    have v3 : Disjoint (V0 ∪ V1 ∪ V2) vb := disjoint_left.mpr fun w hwV hwB => by
      have hwBb : w ∈ Bb0 := by
        rcases mem_union.mp hwV with h01 | h2
        · rcases mem_union.mp h01 with h0 | h1
          · exact hV0_sub h0
          · exact v5 h1
        · exact v4 h2
      exact (mem_filter.mp hwBb).2.2.1 (mem_filter.mp (sdiff_subset hwB)).2
    have v3' : Disjoint (V0 ∪ V1 ∪ V2) v0 := disjoint_left.mpr fun w hwV hwB => by
      have hwBb : w ∈ Bb0 := by
        rcases mem_union.mp hwV with h01 | h2
        · rcases mem_union.mp h01 with h0 | h1
          · exact hV0_sub h0
          · exact v5 h1
        · exact v4 h2
      exact (mem_filter.mp hwBb).2.2.2.1 (mem_filter.mp (sdiff_subset hwB)).2
    have vd : Disjoint S₁ (z8 (V1 ∪ V2) E) := by
      rw [disjoint_union_left]
      refine ⟨zo
          (v2.mono_right (union_subset v5 v4))
          (v1'.mono_right (filter_subset _ _)), ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        have va : Disjoint V0 (V1 ∪ V2) := disjoint_union_right.mpr ⟨hV01, hV02⟩
        rcases (z5 V0 v0 huv).mp he1 with ⟨hu0, _⟩ | ⟨hv0, _⟩ <;>
          rcases (z5 (V1 ∪ V2) E huv).mp he2 with ⟨hu12, hvE⟩ | ⟨hv12, huE⟩
        · exact disjoint_left.mp va hu0 hu12
        · exact disjoint_left.mp hdisj_V0_Bc' hu0 (filter_subset _ _ huE)
        · exact disjoint_left.mp hdisj_V0_Bc' hv0 (filter_subset _ _ hvE)
        · exact disjoint_left.mp va hv0 hv12
    have vm : Disjoint S₁ (z8 (Bc'0 \ E) V1) := by
      rw [disjoint_union_left]
      refine ⟨zo
          (v1'.mono_right (sdiff_subset.trans sdiff_subset))
          (v2.mono_right v5), ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        rcases (z5 V0 v0 huv).mp he1 with ⟨hu0, _⟩ | ⟨hv0, _⟩ <;>
          rcases (z5 (Bc'0 \ E) V1 huv).mp he2 with ⟨hu', hv1⟩ | ⟨hv', hu1⟩
        · exact disjoint_left.mp hdisj_V0_Bc' hu0 (sdiff_subset (sdiff_subset hu'))
        · exact disjoint_left.mp hV01 hu0 hu1
        · exact disjoint_left.mp hV01 hv0 hv1
        · exact disjoint_left.mp hdisj_V0_Bc' hv0 (sdiff_subset (sdiff_subset hv'))
    have v8 : Disjoint S₁ (z8 (V0 ∪ V1 ∪ V2) Bc0) := by
      rw [disjoint_union_left]
      refine ⟨zo
          (v2.mono_right (union_subset (union_subset hV0_sub v5) v4))
          (v1.mono_right sdiff_subset), ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        rcases (z5 V0 v0 huv).mp he1 with ⟨_, hv'⟩ | ⟨_, hu'⟩ <;>
          rcases (z5 (V0 ∪ V1 ∪ V2) Bc0 huv).mp he2 with ⟨huV, hvB⟩ | ⟨hvV, huB⟩
        · exact disjoint_left.mp hdisj_Bc0_Bc' hvB hv'
        · exact disjoint_left.mp v3' hvV hv'
        · exact disjoint_left.mp v3' huV hu'
        · exact disjoint_left.mp hdisj_Bc0_Bc' huB hu'
    have vl : Disjoint S₁ (z8 V2 (v0 \ E)) := by
      rw [disjoint_union_left]
      refine ⟨zo (v2.mono_right v4) (v1'.mono_right sdiff_subset), ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        rcases (z5 V0 v0 huv).mp he1 with ⟨hu0, _⟩ | ⟨hv0, _⟩ <;>
          rcases (z5 V2 (v0 \ E) huv).mp he2 with ⟨hu2, hv'⟩ | ⟨hv2, hu'⟩
        · exact disjoint_left.mp hV02 hu0 hu2
        · exact disjoint_left.mp hdisj_V0_Bc' hu0 (sdiff_subset hu')
        · exact disjoint_left.mp hdisj_V0_Bc' hv0 (sdiff_subset hv')
        · exact disjoint_left.mp hV02 hv0 hv2
    have vp : Disjoint S₁ (z8 (Bc'0 \ E) vb) := by
      rw [disjoint_union_left]
      refine ⟨zo
          (v1'.mono_right (sdiff_subset.trans sdiff_subset)) v1, ?_⟩
      rw [disjoint_left]; intro ⟨e, he⟩ he1 he2
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he
        rcases (z5 V0 v0 huv).mp he1 with ⟨hu0, _⟩ | ⟨hv0, _⟩ <;>
          rcases (z5 (Bc'0 \ E) vb huv).mp he2 with ⟨hu', hvB⟩ | ⟨hv', huB⟩
        · exact disjoint_left.mp hdisj_V0_Bc' hu0 (sdiff_subset (sdiff_subset hu'))
        · exact disjoint_left.mp v3 (mem_union_left _ (mem_union_left _ hu0)) huB
        · exact disjoint_left.mp v3 (mem_union_left _ (mem_union_left _ hv0)) hvB
        · exact disjoint_left.mp hdisj_V0_Bc' hv0 (sdiff_subset (sdiff_subset hv'))
    have vw : ∀ w ∈ V0, w ≠ d' → ∀ z ∈ E, ∀ f : {e // e ∉ S₁} → Bool, ¬ (z1 (z0 S₁ f₁ f)).Adj w z := by
      intro w hw hne_wd z hz f hadj
      have hzBc' : z ∈ v0 := (mem_filter.mp hz).1
      have vi : w ≠ z := fun h => disjoint_left.mp hdisj_V0_Bc' hw (h ▸ hzBc')
      have hmem : z7 w z vi ∈ S₁ := mem_union_right _ ((z5 V0 v0 vi).mpr (Or.inl ⟨hw, hzBc'⟩))
      have hwz1 : G₁.Adj w z := by
        rw [zf S₁ f₁ (fun _ => false) vi hmem]
        exact (zf S₁ f₁ f vi hmem).mp hadj
      exact hNoShare w hw d' hd'_V0 hne_wd z hzBc' ⟨hwz1, (mem_filter.mp hz).2⟩
    have u9 : ∀ d ∈ V2, ∀ f : {e // e ∉ S₁} → Bool, ∀ z : Fin (nOf q m),
        inE q hq (z1 (z0 S₁ f₁ f)) (mkA q m hq hlp d d') z ↔ ∃ j : Fin m, z = v9 j := by
      intro d hd f z
      let Gf := z1 (z0 S₁ f₁ f)
      have u1 := zz q m hq hlp (z0 S₁ f₁ f)
        (z0 S₀ f₀ (fun _ => false)) (vy f)
      have hadj_d' : ∀ u ∈ v0, Gf.Adj d' u ↔ G₁.Adj d' u := fun u hu => by
        have hne : d' ≠ u := fun h => disjoint_left.mp hdisj_V0_Bc' hd'_V0 (h ▸ hu)
        have hmem : z7 d' u hne ∈ S₁ := mem_union_right _ ((z5 V0 v0 hne).mpr (Or.inl ⟨hd'_V0, hu⟩))
        rw [zf S₁ f₁ f hne hmem, zf S₁ f₁ (fun _ => false) hne hmem]
      have ue : (∃ j : Fin m, z = v9 j) ↔ z ∈ E := by
        rw [u2]; simp only [mem_image, mem_univ, true_and, eq_comm]
      rw [ue]
      constructor
      · rintro ⟨hbc', hadj, hnp⟩
        rw [z14'] at hadj
        have v6 : z ∈ v0 := by
          refine mem_sdiff.mpr ⟨?_, fun hP => hnp ((yl q m hq hlp d d' z).mpr (Or.inl hP))⟩
          change z ∈ zp q m hq hlp G₀
          rw [← u1.2.1]; exact mem_filter.mpr ⟨mem_univ _, (w8 q m hq hlp Gf d d' z).mp hbc'⟩
        exact mem_filter.mpr ⟨v6, (hadj_d' z v6).mp hadj.symm⟩
      · intro hzE
        rcases mem_filter.mp hzE with ⟨v6, hadj1⟩
        rcases mem_sdiff.mp v6 with ⟨hzBc', hzNotP⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [w8]
          have : z ∈ zp q m hq hlp Gf := by rwa [u1.2.1]
          exact (mem_filter.mp this).2
        · rw [z14']; exact ((hadj_d' z v6).mpr hadj1).symm
        · rw [yl]; rintro (hP | rfl | rfl)
          · exact hzNotP hP
          · exact (mem_filter.mp (v4 hd)).2.2.2.1 (mem_filter.mp hzBc').2
          · exact (mem_filter.mp (hV0_sub hd'_V0)).2.2.2.1 (mem_filter.mp hzBc').2
    exact z23 q m hq hlp S₁ f₁ d' V0 V1 V2 E vb v0 Bc0 Bc'0 v9 u4 u2
      subset_union_left hd'_V0
      (vh.2.2.symm ▸ hV0_sub) (vh.2.2.symm ▸ v5) (vh.2.2.symm ▸ v4)
      hV0_card hV2_card u6 u7 hV01 hV02 hV12 (vh.2.2.symm ▸ vv)
      (vh.1.symm ▸ rfl) (vh.2.1.symm ▸ rfl) rfl rfl hE_sub hE_card
      vt v7 u0 vo
      vd vm v8 vl vp vw u9
lemma z0d (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) :
    gProb (nOf q m) ((ROf m : ℝ)⁻¹)
      (EventE1 q (nOf q m) (KOf q m) ∩ EventEdeg q (nOf q m) (ROf m) ∩
        EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ) ≤ 1 / 16 := by
  classical
  set R := ROf m
  set p : ℝ := (R : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  let S₀ := ze (zn q m hq hlp)
  let Good0 : Set (SimpleGraph (Fin (nOf q m))) :=
    {G | ((R : ℝ) / 3 ≤ ((zr q m hq hlp G).card : ℝ) ∧ ((zr q m hq hlp G).card : ℝ) ≤ 2 * (R : ℝ)) ∧
         ((R : ℝ) / 3 ≤ ((zp q m hq hlp G).card : ℝ) ∧ ((zp q m hq hlp G).card : ℝ) ≤ 2 * (R : ℝ)) ∧
         ((zr q m hq hlp G ∩ zp q m hq hlp G).card < KOf q m) ∧
         ((1 / 4 : ℝ) * ((R : ℝ) ^ 2) ≤ ((zj q m hq hlp G).card : ℝ) ∧
           ((zj q m hq hlp G).card : ℝ) ≤ 2 * ((R : ℝ) ^ 2))}
  let Bad : Set (SimpleGraph (Fin (nOf q m))) :=
    EventE1 q (nOf q m) (KOf q m) ∩ EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ
  have hsub : EventE1 q (nOf q m) (KOf q m) ∩ EventEdeg q (nOf q m) R ∩
      EventE2 q hq (nOf q m) m ∩ (EventE4 q hq (nOf q m))ᶜ ⊆ Good0 ∩ Bad := by
    rintro G ⟨⟨⟨hE1, hEdeg⟩, hE2⟩, hnotE4⟩
    exact ⟨z1k q m hq hlp hE1 hEdeg, ⟨⟨hE1, hE2⟩, hnotE4⟩⟩
  refine ((gProb_mono hp0 hp1 hsub).trans (w4 hp0 hp1 S₀ Good0 Bad ?_ (10 / 256) (by norm_num) ?_)).trans (by norm_num)
  · intro f₀ f₂ f₂'
    have hfix := zz q m hq hlp (z0 S₀ f₀ f₂) (z0 S₀ f₀ f₂')
      (fun e he => by simp only [z0, dif_pos (show e ∈ S₀ from he)])
    simp only [Good0, Set.mem_ofPred_eq, hfix.1, hfix.2.1, hfix.2.2]
  · intro f₀ hGood0
    rcases hGood0 (fun _ => false) with ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, ⟨h6, h7⟩⟩
    exact z24 q m hq hlp f₀ h1 h2 h3 h4 h5 h6 h7
end
section
open scoped Classical
open Finset Real Nat
lemma gProb_good_miss_ge (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) :
    (3 / 4 : ℝ) ≤ gProb (nOf q m) ((ROf m : ℝ)⁻¹)
      (EventE1 q (nOf q m) (KOf q m) ∩ EventEdeg q (nOf q m) (ROf m) ∩
        EventE2 q hq (nOf q m) m ∩ EventE3 q hq (nOf q m) m) := by
  set n := nOf q m
  set p : ℝ := ((ROf m : ℝ))⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  set A1 := EventE1 q n (KOf q m)
  set Ad := EventEdeg q n (ROf m)
  set A2 := EventE2 q hq n m
  set A3 := EventE3 q hq n m
  have hsub : (A1 ∩ Ad ∩ A2 ∩ A3)ᶜ ⊆ A1ᶜ ∪ Adᶜ ∪ (A1 ∩ Ad ∩ A2ᶜ) ∪ (A1 ∩ Ad ∩ A3ᶜ) := by
    intro G hG
    by_cases h1 : G ∈ A1
    · by_cases hd : G ∈ Ad
      · by_cases h2 : G ∈ A2
        · by_cases h3 : G ∈ A3
          · exact absurd ⟨⟨⟨h1, hd⟩, h2⟩, h3⟩ hG
          · exact Or.inr ⟨⟨h1, hd⟩, h3⟩
        · exact Or.inl (Or.inr ⟨⟨h1, hd⟩, h2⟩)
      · exact Or.inl (Or.inl (Or.inr hd))
    · exact Or.inl (Or.inl (Or.inl h1))
  have v1 : gProb n p (A1 ∩ Ad ∩ A2 ∩ A3)ᶜ ≤ 4 / 64 := by
    have h1 := z0y q m hlp
    have h2 := z0h q m hq hlp
    have h3 := wm q m hq hlp
    have h4 := wl q m hq hlp
    have hu1 := yg hp0 hp1 (A1ᶜ ∪ Adᶜ ∪ (A1 ∩ Ad ∩ A2ᶜ)) (A1 ∩ Ad ∩ A3ᶜ)
    have hu2 := yg hp0 hp1 (A1ᶜ ∪ Adᶜ) (A1 ∩ Ad ∩ A2ᶜ)
    have hu3 := yg hp0 hp1 A1ᶜ Adᶜ
    have hm := gProb_mono hp0 hp1 hsub
    linarith
  have v0 := z1g p (A1 ∩ Ad ∩ A2 ∩ A3)
  linarith
lemma gProb_good_hit_ge (q m : ℕ) (hq : 2 ≤ q) (hlp : LargeParams q m) :
    (3 / 4 : ℝ) ≤ gProb (nOf q m) ((ROf m : ℝ)⁻¹)
      (EventE1 q (nOf q m) (KOf q m) ∩ EventEdeg q (nOf q m) (ROf m) ∩
        EventE2 q hq (nOf q m) m ∩ EventE3 q hq (nOf q m) m ∩ EventE4 q hq (nOf q m)) := by
  set n := nOf q m
  set p : ℝ := ((ROf m : ℝ))⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast R_pos m)
  set A1 := EventE1 q n (KOf q m)
  set Ad := EventEdeg q n (ROf m)
  set A2 := EventE2 q hq n m
  set A3 := EventE3 q hq n m
  set A4 := EventE4 q hq n
  have hsub : (A1 ∩ Ad ∩ A2 ∩ A3 ∩ A4)ᶜ ⊆
      A1ᶜ ∪ Adᶜ ∪ (A1 ∩ Ad ∩ A2ᶜ) ∪ (A1 ∩ Ad ∩ A3ᶜ) ∪ (A1 ∩ Ad ∩ A2 ∩ A4ᶜ) := by
    intro G hG
    by_cases h1 : G ∈ A1
    · by_cases hd : G ∈ Ad
      · by_cases h2 : G ∈ A2
        · by_cases h3 : G ∈ A3
          · by_cases h4 : G ∈ A4
            · exact absurd ⟨⟨⟨⟨h1, hd⟩, h2⟩, h3⟩, h4⟩ hG
            · exact Or.inr ⟨⟨⟨h1, hd⟩, h2⟩, h4⟩
          · exact Or.inl (Or.inr ⟨⟨h1, hd⟩, h3⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨⟨h1, hd⟩, h2⟩))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hd)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
  have v1 : gProb n p (A1 ∩ Ad ∩ A2 ∩ A3 ∩ A4)ᶜ ≤ 1 / 8 := by
    have h1 := z0y q m hlp
    have h2 := z0h q m hq hlp
    have h3 := wm q m hq hlp
    have h4 := wl q m hq hlp
    have h5 := z0d q m hq hlp
    have hu1 := yg hp0 hp1 (A1ᶜ ∪ Adᶜ ∪ (A1 ∩ Ad ∩ A2ᶜ) ∪ (A1 ∩ Ad ∩ A3ᶜ)) (A1 ∩ Ad ∩ A2 ∩ A4ᶜ)
    have hu2 := yg hp0 hp1 (A1ᶜ ∪ Adᶜ ∪ (A1 ∩ Ad ∩ A2ᶜ)) (A1 ∩ Ad ∩ A3ᶜ)
    have hu3 := yg hp0 hp1 (A1ᶜ ∪ Adᶜ) (A1 ∩ Ad ∩ A2ᶜ)
    have hu4 := yg hp0 hp1 A1ᶜ Adᶜ
    have hm := gProb_mono hp0 hp1 hsub
    linarith
  have v0 := z1g p (A1 ∩ Ad ∩ A2 ∩ A3 ∩ A4)
  linarith
lemma m_le_nOf (q m : ℕ) (hq : 2 ≤ q) (hm : 2 ≤ m) : m ≤ nOf q m := by
  have hmT : m ≤ zd (m - 1) := y9 m hm
  have hTE : zd (m - 1) ≤ EOf m := Nat.le_self_pow (by norm_num) _
  have hE8 : EOf m ≤ 8 * q * EOf m := by nlinarith
  have h2 : 8 * q * EOf m ≤ 2 ^ (8 * q * EOf m) := Nat.le_of_lt Nat.lt_two_pow_self
  exact le_trans (le_trans hmT hTE) (le_trans hE8 h2)
end
end ShelahSpencerH1

theorem OMA.solution : OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1.H1 := by
  intro q hq hα
  obtain ⟨M₀, hM₀⟩ := ShelahSpencerH1.exists_largeParams q hq
  refine ⟨ShelahSpencerH1.kOf q,
    ShelahSpencerH1.validFormula q hq,
    ShelahSpencerH1.domFormula q hq,
    ShelahSpencerH1.ltFormula q hq,
    ShelahSpencerH1.memFormula q hq, ?_, ?_⟩
  ·
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨m, hm_ge, hm_N, hm_mod⟩ : ∃ m : ℕ, M₀ ≤ m ∧ N ≤ m ∧ (m - 1) % 100 = 25 :=
      ⟨100 * (max M₀ N) + 26, by omega, by omega, by omega⟩
    have hlp : ShelahSpencerH1.LargeParams q m := hM₀ m hm_ge
    have v5 : N ≤ ShelahSpencerH1.nOf q m :=
      le_trans hm_N (ShelahSpencerH1.m_le_nOf q m hq (by have := hlp.hm; omega))
    refine ⟨ShelahSpencerH1.nOf q m, v5, ?_⟩
    set n := ShelahSpencerH1.nOf q m
    set p : ℝ := ((ShelahSpencerH1.ROf m : ℝ))⁻¹
    have hp0 : 0 ≤ p := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast ShelahSpencerH1.R_pos m)
    have v2 : ((n : ℝ) ^ (-((1 : ℝ) / (q : ℝ)))) = p :=
      ShelahSpencerH1.nOf_rpow_neg_inv q m hq
    have v4 :
        ShelahSpencerH1.EventE1 q n (ShelahSpencerH1.KOf q m) ∩
        ShelahSpencerH1.EventEdeg q n (ShelahSpencerH1.ROf m) ∩
        ShelahSpencerH1.EventE2 q hq n m ∩
        ShelahSpencerH1.EventE3 q hq n m ∩
        ShelahSpencerH1.EventE4 q hq n ⊆
        {G : SimpleGraph (Fin n) | ∃ (a : Fin (ShelahSpencerH1.kOf q) → Fin n) (D : Finset (Fin n)),
          ((@FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.validFormula q hq) a ∧
            (∀ x, x ∈ D ↔ @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.domFormula q hq) (Fin.snoc a x)) ∧
            D.Nonempty ∧
            (∀ x ∈ D, ¬ @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a x) x)) ∧
            (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a x) y) →
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a y) z) →
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a x) z)) ∧
            (∀ x ∈ D, ∀ y ∈ D,
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a x) y) ∨
              x = y ∨
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a y) x))) ∧
          (∀ S ⊆ D, ∃ v, ∀ x ∈ D,
            @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.memFormula q hq) (Fin.snoc (Fin.snoc a v) x) ↔ x ∈ S) ∧
          10 ≤ (D.card - 1) % 100 ∧ (D.card - 1) % 100 ≤ 40)} := by
      rintro G ⟨⟨⟨⟨hE1, _⟩, hE2⟩, hE3⟩, ⟨a, v0⟩⟩
      let D := ShelahSpencerH1.domFinset q hq G a
      have v3 : ∀ x, x ∈ D ↔ ShelahSpencerH1.inDom q hq G a x := fun x =>
        ShelahSpencerH1.mem_domFinset q hq G a x
      obtain ⟨hcard_m, huniv⟩ := ShelahSpencerH1.card_eq_m_of_events q hq
        (by have := hlp.hm; omega) hlp.hK_le_tower hE1 hE2 hE3 a D v0 v3
      refine ⟨a, D, ?_, ?_, ?_, ?_⟩
      · refine ⟨(ShelahSpencerH1.realize_validFormula q hq G a).mpr v0,
          fun x => (v3 x).trans (ShelahSpencerH1.realize_domFormula q hq G a x).symm,
          ?_, ?_, ?_, ?_⟩
        · rcases v0.2.1 with ⟨x₀, hx₀⟩; exact ⟨x₀, (v3 x₀).mpr hx₀⟩
        · intro x _ hlt
          exact ShelahSpencerH1.ltRel_irrefl q hq G a x
            ((ShelahSpencerH1.realize_ltFormula q hq G a x x).mp hlt)
        · intro x _ y _ z _ hxy hyz
          exact (ShelahSpencerH1.realize_ltFormula q hq G a x z).mpr
            (ShelahSpencerH1.ltRel_trans q hq G a
              ((ShelahSpencerH1.realize_ltFormula q hq G a x y).mp hxy)
              ((ShelahSpencerH1.realize_ltFormula q hq G a y z).mp hyz))
        · intro x hx y hy
          rcases v0.2.2.1 x y ((v3 x).mp hx) ((v3 y).mp hy) with h1 | h2 | h3
          · exact Or.inl ((ShelahSpencerH1.realize_ltFormula q hq G a x y).mpr h1)
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr ((ShelahSpencerH1.realize_ltFormula q hq G a y x).mpr h3))
      · intro S hS
        obtain ⟨v, hv⟩ := huniv S hS
        exact ⟨v, fun x hx => (ShelahSpencerH1.realize_memFormula q hq G a v x).trans (hv x hx)⟩
      · rw [hcard_m, hm_mod]; norm_num
      · rw [hcard_m, hm_mod]; norm_num
    have v1 : (3 / 4 : ℝ) ≤ ShelahSpencerH1.gProb n p _ :=
      (ShelahSpencerH1.gProb_good_hit_ge q m hq hlp).trans (ShelahSpencerH1.gProb_mono hp0 hp1 v4)
    have hsp := ShelahSpencerH1.sparseRandomGraph_ge_of_gProb (n := n) (r := (3 / 4 : ℝ)) hα
      (by rw [v2]; exact v1)
    have h34 : ENNReal.ofReal (3 / 4 : ℝ) = (3 : ENNReal) / 4 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]; simp
    rwa [h34] at hsp
  ·
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨m, hm_ge, hm_N, hm_mod⟩ : ∃ m : ℕ, M₀ ≤ m ∧ N ≤ m ∧ (m - 1) % 100 = 75 :=
      ⟨100 * (max M₀ N) + 76, by omega, by omega, by omega⟩
    have hlp : ShelahSpencerH1.LargeParams q m := hM₀ m hm_ge
    have v5 : N ≤ ShelahSpencerH1.nOf q m :=
      le_trans hm_N (ShelahSpencerH1.m_le_nOf q m hq (by have := hlp.hm; omega))
    refine ⟨ShelahSpencerH1.nOf q m, v5, ?_⟩
    set n := ShelahSpencerH1.nOf q m
    set p : ℝ := ((ShelahSpencerH1.ROf m : ℝ))⁻¹
    have hp0 : 0 ≤ p := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast ShelahSpencerH1.R_pos m)
    have v2 : ((n : ℝ) ^ (-((1 : ℝ) / (q : ℝ)))) = p :=
      ShelahSpencerH1.nOf_rpow_neg_inv q m hq
    have v4 :
        ShelahSpencerH1.EventE1 q n (ShelahSpencerH1.KOf q m) ∩
        ShelahSpencerH1.EventEdeg q n (ShelahSpencerH1.ROf m) ∩
        ShelahSpencerH1.EventE2 q hq n m ∩
        ShelahSpencerH1.EventE3 q hq n m ⊆
        {G : SimpleGraph (Fin n) | ∀ (a : Fin (ShelahSpencerH1.kOf q) → Fin n) (D : Finset (Fin n)),
          (@FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.validFormula q hq) a ∧
            (∀ x, x ∈ D ↔ @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.domFormula q hq) (Fin.snoc a x)) ∧
            D.Nonempty ∧
            (∀ x ∈ D, ¬ @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a x) x)) ∧
            (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a x) y) →
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a y) z) →
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a x) z)) ∧
            (∀ x ∈ D, ∀ y ∈ D,
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a x) y) ∨
              x = y ∨
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ (ShelahSpencerH1.ltFormula q hq) (Fin.snoc (Fin.snoc a y) x))) →
          ¬ (10 ≤ (D.card - 1) % 100 ∧ (D.card - 1) % 100 ≤ 40)} := by
      rintro G ⟨⟨⟨hE1, _⟩, hE2⟩, hE3⟩ a D ⟨hval_f, hdom_f, _, _, _, _⟩
      have v0 := (ShelahSpencerH1.realize_validFormula q hq G a).mp hval_f
      have v3 : ∀ x, x ∈ D ↔ ShelahSpencerH1.inDom q hq G a x := fun x =>
        (hdom_f x).trans (ShelahSpencerH1.realize_domFormula q hq G a x)
      obtain ⟨hcard_m, _⟩ := ShelahSpencerH1.card_eq_m_of_events q hq
        (by have := hlp.hm; omega) hlp.hK_le_tower hE1 hE2 hE3 a D v0 v3
      rw [hcard_m, hm_mod]; omega
    have v1 : (3 / 4 : ℝ) ≤ ShelahSpencerH1.gProb n p _ :=
      (ShelahSpencerH1.gProb_good_miss_ge q m hq hlp).trans (ShelahSpencerH1.gProb_mono hp0 hp1 v4)
    have hsp := ShelahSpencerH1.sparseRandomGraph_ge_of_gProb (n := n) (r := (3 / 4 : ℝ)) hα
      (by rw [v2]; exact v1)
    have h34 : ENNReal.ofReal (3 / 4 : ℝ) = (3 : ENNReal) / 4 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]; simp
    rwa [h34] at hsp
