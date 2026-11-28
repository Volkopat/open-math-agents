import OMAReductions.R_Erdos19_erdos_19_variants_kahn_R1
import Mathlib

-- Problem: Erdős Problem 19 — kahn (R1.H2: bounded-rank linear hypergraphs have chromatic index <= 2D)
-- Target: OMA.R_Erdos19_erdos_19_variants_kahn_R1.H2
-- Credit: @gdyan2022

/-!
Proof of `OMA.R_Erdos19_erdos_19_variants_kahn_R1.H2`:
Bounded-rank linear hypergraphs of large maximum degree `D` have chromatic index at most `2 * D`.

Architecture:
1. Finite-sample-space Symmetric Lovász Local Lemma (`lll_symmetric`) and coordinate-dependency
   independence (`DependsOn`, `lll_of_dependsOn`).
2. Two-sided `p`-weighted McDiarmid bounded-differences inequality (`bernoulli_mcdiarmid_sub`)
   and weighted Chernoff bound (`weighted_chernoff_sub`) over finite product spaces `X → Fin Q`.
3. Single Rödl nibble round (`nibble_round`) deleting `V(S)` while retaining the isolated-edge
   matching `M_bite ⊆ S`, with deterministic two-part waste bound and exponential concentration
   via LLL.
4. Multi-round iteration (`locally_covering_matching`) proving the Pippenger–Spencer locally
   covering matching theorem for all uniformities `k = s + 1 ≥ 4`.
5. Elementary regularization, padding, assignment hypergraph, and two-palette coloring reduction
   yielding `OMA.solution`.
-/

namespace Erdos19H2

open Finset
open scoped BigOperators Classical

/- ### Section 1: Finite Probability Space and Symmetric Lovász Local Lemma -/

section LLL

noncomputable def good {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : I → Finset Ω) (T : Finset I) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ j ∈ T, ω ∉ A j)

lemma good_empty {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] (A : I → Finset Ω) :
    good A ∅ = Finset.univ := by
  ext ω; simp [good]

lemma good_insert {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]
    (A : I → Finset Ω) (i : I) (T : Finset I) :
    good A (insert i T) = (good A T).filter (fun ω => ω ∉ A i) := by
  ext ω
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    forall_eq_or_imp]
  exact and_comm

lemma good_card_split {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]
    (A : I → Finset Ω) (i : I) (T : Finset I) :
    (good A T).card = (good A (insert i T)).card + (A i ∩ good A T).card := by
  rw [good_insert]
  have hsub : A i ∩ good A T = (good A T).filter (fun ω => ω ∈ A i) := by
    ext ω; simp [and_comm]
  rw [hsub]
  have h := Finset.card_filter_add_card_filter_not (s := good A T) (p := fun ω => ω ∈ A i)
  omega

lemma good_antitone {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : I → Finset Ω) {T₁ T₂ : Finset I} (h : T₁ ⊆ T₂) :
    good A T₂ ⊆ good A T₁ := by
  intro ω hω
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
  exact fun j hj => hω j (h hj)

lemma one_sub_mul_le_pow_aux (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ n : ℕ, 1 - (n : ℝ) * a ≤ (1 - a) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := one_sub_mul_le_pow_aux a ha0 ha1 n
    have hmul : (1 - (n : ℝ) * a) * (1 - a) ≤ (1 - a) ^ n * (1 - a) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have hsq : 0 ≤ (n : ℝ) * a ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg a)
    rw [pow_succ]
    push_cast
    nlinarith

lemma lll_step_chain {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]
    (A : I → Finset Ω) (α : ℝ) (hα1 : α ≤ 1) (n : ℕ)
    (ih : ∀ U : Finset I, U.card < n → ∀ j ∉ U,
      ((good A U).card : ℝ) * (1 - α) ≤ ((good A (insert j U)).card : ℝ)) :
    ∀ S T₂ : Finset I, Disjoint S T₂ → (S ∪ T₂).card ≤ n →
      ((good A T₂).card : ℝ) * (1 - α) ^ S.card ≤ ((good A (S ∪ T₂)).card : ℝ) := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro T₂ _ _; simp
  | @insert x S₀ hx ihS =>
    intro T₂ hdisj hcard
    have hdisj₀ : Disjoint S₀ T₂ := hdisj.mono_left (Finset.subset_insert x S₀)
    have hxT₂ : x ∉ T₂ := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self x S₀)
    have hxU : x ∉ S₀ ∪ T₂ := by simp [hx, hxT₂]
    have hsub : S₀ ∪ T₂ ⊂ insert x S₀ ∪ T₂ := by
      rw [Finset.insert_union]; exact Finset.ssubset_insert hxU
    have hcard₀_lt : (S₀ ∪ T₂).card < n := lt_of_lt_of_le (Finset.card_lt_card hsub) hcard
    have h1 := ihS T₂ hdisj₀ hcard₀_lt.le
    have h2 := ih (S₀ ∪ T₂) hcard₀_lt x hxU
    rw [Finset.insert_union, Finset.card_insert_of_notMem hx, pow_succ]
    calc ((good A T₂).card : ℝ) * ((1 - α) ^ S₀.card * (1 - α))
        = ((good A T₂).card : ℝ) * (1 - α) ^ S₀.card * (1 - α) := by ring
      _ ≤ ((good A (S₀ ∪ T₂)).card : ℝ) * (1 - α) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ ((good A (insert x (S₀ ∪ T₂))).card : ℝ) := h2

theorem lll_symmetric {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I] [DecidableEq I]
    [Nonempty Ω]
    (A : I → Finset Ω) (Γ : I → Finset I) (p : ℝ) (d : ℕ)
    (hp : 0 ≤ p) (hpd : 4 * p * ((d : ℝ) + 1) ≤ 1)
    (hΓ : ∀ i, (Γ i).card ≤ d)
    (hlop : ∀ i : I, ∀ T : Finset I, i ∉ T → (∀ j ∈ T, j ∉ Γ i) →
      ((A i ∩ good A T).card : ℝ) ≤ p * ((good A T).card : ℝ)) :
    ∃ ω : Ω, ∀ i : I, ω ∉ A i := by
  have hp4 : 4 * p ≤ 1 := by
    have hd0 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
    nlinarith
  have h2p0 : 0 ≤ 2 * p := by linarith
  have h2p1 : 2 * p ≤ 1 := by linarith
  have hmain : ∀ n : ℕ, ∀ T : Finset I, T.card ≤ n → ∀ i ∉ T,
      ((good A T).card : ℝ) * (1 - 2 * p) ≤ ((good A (insert i T)).card : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hTn i hiT
      let S₁ : Finset I := T ∩ Γ i
      let S₂ : Finset I := T \ Γ i
      have hT_eq : S₁ ∪ S₂ = T := by
        ext x; simp only [S₁, S₂, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
      have hdisj : Disjoint S₁ S₂ := disjoint_sdiff_self_right.mono_left Finset.inter_subset_right
      have hS₁_le : S₁.card ≤ d := (Finset.card_le_card Finset.inter_subset_right).trans (hΓ i)
      have hiS₂ : i ∉ S₂ := fun h => hiT (Finset.sdiff_subset h)
      have hS₂_Γ : ∀ j ∈ S₂, j ∉ Γ i := fun j hj => (Finset.mem_sdiff.mp hj).2
      have hbad_le : ((A i ∩ good A T).card : ℝ) ≤ p * ((good A S₂).card : ℝ) := by
        have hsub : A i ∩ good A T ⊆ A i ∩ good A S₂ :=
          Finset.inter_subset_inter_left (good_antitone A Finset.sdiff_subset)
        exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hlop i S₂ hiS₂ hS₂_Γ)
      have hgood_ge : (1 / 2 : ℝ) * ((good A S₂).card : ℝ) ≤ ((good A T).card : ℝ) := by
        have hih : ∀ U : Finset I, U.card < n → ∀ j ∉ U,
            ((good A U).card : ℝ) * (1 - 2 * p) ≤ ((good A (insert j U)).card : ℝ) :=
          fun U hU => ih U.card hU U le_rfl
        have hchain := lll_step_chain A (2 * p) h2p1 n hih S₁ S₂ hdisj
          (by rw [hT_eq]; exact hTn)
        rw [hT_eq] at hchain
        have hpow_ge : (1 / 2 : ℝ) ≤ (1 - 2 * p) ^ S₁.card := by
          rcases Nat.eq_zero_or_pos S₁.card with h0 | _
          · rw [h0, pow_zero]; norm_num
          · have hpow_mono : (1 - 2 * p) ^ d ≤ (1 - 2 * p) ^ S₁.card :=
              pow_le_pow_of_le_one (by linarith) (by linarith) hS₁_le
            have hbern := one_sub_mul_le_pow_aux (2 * p) h2p0 h2p1 d
            have h4pd : 4 * p * (d : ℝ) ≤ 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
            linarith
        calc (1 / 2 : ℝ) * ((good A S₂).card : ℝ)
            ≤ (1 - 2 * p) ^ S₁.card * ((good A S₂).card : ℝ) :=
              mul_le_mul_of_nonneg_right hpow_ge (Nat.cast_nonneg _)
          _ = ((good A S₂).card : ℝ) * (1 - 2 * p) ^ S₁.card := mul_comm _ _
          _ ≤ ((good A T).card : ℝ) := hchain
      have hbad_T : ((A i ∩ good A T).card : ℝ) ≤ 2 * p * ((good A T).card : ℝ) := by
        linarith [mul_le_mul_of_nonneg_left hgood_ge (by linarith : 0 ≤ 2 * p)]
      have hsplit : ((good A T).card : ℝ) =
          ((good A (insert i T)).card : ℝ) + ((A i ∩ good A T).card : ℝ) := by
        exact_mod_cast good_card_split A i T
      linarith
  have hpos_all : ∀ S : Finset I, 0 < (good A S).card := by
    intro S
    induction S using Finset.induction_on with
    | empty => rw [good_empty, Finset.card_univ]; exact Fintype.card_pos
    | @insert i S hi ih =>
      have hstep := hmain S.card S le_rfl i hi
      have hS_pos : (0 : ℝ) < (good A S).card := Nat.cast_pos.mpr ih
      have h12p : (0 : ℝ) < 1 - 2 * p := by linarith
      exact Nat.cast_pos.mp (lt_of_lt_of_le (mul_pos hS_pos h12p) hstep)
  obtain ⟨ω, hω⟩ := Finset.card_pos.mp (hpos_all Finset.univ)
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hω
  exact ⟨ω, fun i => hω i trivial⟩

def DependsOn {X α : Type*} (S : Finset X) (E : Finset (X → α)) : Prop :=
  ∀ f g : X → α, (∀ x ∈ S, f x = g x) → (f ∈ E ↔ g ∈ E)

lemma dependsOn_mono {X α : Type*} {S T : Finset X} {E : Finset (X → α)}
    (hST : S ⊆ T) (hE : DependsOn S E) : DependsOn T E :=
  fun f g hfg => hE f g fun x hx => hfg x (hST hx)

lemma dependsOn_union {X α : Type*} [DecidableEq X] [Fintype X] [Fintype α] [DecidableEq α]
    {S : Finset X} {E F : Finset (X → α)}
    (hE : DependsOn S E) (hF : DependsOn S F) : DependsOn S (E ∪ F) := by
  intro f g hfg
  simp only [Finset.mem_union]
  exact or_congr (hE f g hfg) (hF f g hfg)

lemma dependsOn_good {X α I : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (A : I → Finset (X → α)) (S : I → Finset X)
    (hS : ∀ i, DependsOn (S i) (A i)) (T : Finset I) :
    DependsOn (T.biUnion S) (good A T) := by
  intro f g hfg
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf j hj hmem
    exact hf j hj ((hS j f g (fun x hx => hfg x (Finset.mem_biUnion.mpr ⟨j, hj, hx⟩))).mpr hmem)
  · intro hg j hj hmem
    exact hg j hj ((hS j f g (fun x hx => hfg x (Finset.mem_biUnion.mpr ⟨j, hj, hx⟩))).mp hmem)

def splitProdEquiv {X α : Type*} (S : Finset X) [DecidablePred (fun x => x ∈ S)] :
    (X → α) ≃ (({x : X // x ∈ S} → α) × ({x : X // x ∉ S} → α)) where
  toFun f := (fun x => f x.1, fun y => f y.1)
  invFun p x := if hx : x ∈ S then p.1 ⟨x, hx⟩ else p.2 ⟨x, hx⟩
  left_inv f := funext fun x => by by_cases hx : x ∈ S <;> simp [hx]
  right_inv p := by ext x <;> simp [x.2]

theorem card_inter_of_dependsOn_disjoint {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Nonempty α]
    {S T : Finset X} (hdisj : Disjoint S T) {E F : Finset (X → α)}
    (hE : DependsOn S E) (hF : DependsOn T F) :
    (E ∩ F).card * Fintype.card (X → α) = E.card * F.card := by
  obtain ⟨a₀⟩ := ‹Nonempty α›
  let e := splitProdEquiv (α := α) S
  let E₁ : Finset ({x : X // x ∈ S} → α) :=
    Finset.univ.filter (fun g => e.symm (g, fun _ => a₀) ∈ E)
  let F₂ : Finset ({x : X // x ∉ S} → α) :=
    Finset.univ.filter (fun h => e.symm (fun _ => a₀, h) ∈ F)
  have hEiff : ∀ f : X → α, f ∈ E ↔ (e f).1 ∈ E₁ := fun f => by
    simp only [E₁, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hE f (e.symm ((e f).1, fun _ => a₀)) fun x hx => by simp [e, splitProdEquiv, hx]
  have hFiff : ∀ f : X → α, f ∈ F ↔ (e f).2 ∈ F₂ := fun f => by
    simp only [F₂, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hF f (e.symm (fun _ => a₀, (e f).2)) fun x hx => by
      have hxS : x ∉ S := Finset.disjoint_right.mp hdisj hx
      simp [e, splitProdEquiv, hxS]
  have himE : E.image e = E₁ ×ˢ Finset.univ := by
    ext p; simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨fun ⟨f, hf, hfp⟩ => hfp ▸ (hEiff f).mp hf,
      fun hp => ⟨e.symm p, (hEiff (e.symm p)).mpr (by simpa using hp), e.apply_symm_apply p⟩⟩
  have himF : F.image e = Finset.univ ×ˢ F₂ := by
    ext p; simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨fun ⟨f, hf, hfp⟩ => hfp ▸ (hFiff f).mp hf,
      fun hp => ⟨e.symm p, (hFiff (e.symm p)).mpr (by simpa using hp), e.apply_symm_apply p⟩⟩
  have himEF : (E ∩ F).image e = E₁ ×ˢ F₂ := by
    ext p; simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_product]
    exact ⟨fun ⟨f, ⟨hfE, hfF⟩, hfp⟩ => hfp ▸ ⟨(hEiff f).mp hfE, (hFiff f).mp hfF⟩,
      fun ⟨hp1, hp2⟩ => ⟨e.symm p, ⟨(hEiff (e.symm p)).mpr (by simpa using hp1),
        (hFiff (e.symm p)).mpr (by simpa using hp2)⟩, e.apply_symm_apply p⟩⟩
  have hcE : E.card = E₁.card * Fintype.card ({x : X // x ∉ S} → α) := by
    rw [← Finset.card_image_of_injective E e.injective, himE, Finset.card_product, Finset.card_univ]
  have hcF : F.card = Fintype.card ({x : X // x ∈ S} → α) * F₂.card := by
    rw [← Finset.card_image_of_injective F e.injective, himF, Finset.card_product, Finset.card_univ]
  have hcEF : (E ∩ F).card = E₁.card * F₂.card := by
    rw [← Finset.card_image_of_injective (E ∩ F) e.injective, himEF, Finset.card_product]
  have hcTot : Fintype.card (X → α) =
      Fintype.card ({x : X // x ∈ S} → α) * Fintype.card ({x : X // x ∉ S} → α) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [hcEF, hcTot, hcE, hcF]; ring

theorem lll_of_dependsOn {X α I : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype I] [DecidableEq I]
    (A : I → Finset (X → α)) (S : I → Finset X) (p : ℝ) (d : ℕ)
    (hp : 0 ≤ p) (hpd : 4 * p * ((d : ℝ) + 1) ≤ 1)
    (hdep : ∀ i, DependsOn (S i) (A i))
    (hprob : ∀ i, ((A i).card : ℝ) ≤ p * (Fintype.card (X → α) : ℝ))
    (hdeg : ∀ i, (Finset.univ.filter (fun j : I => j ≠ i ∧ ¬ Disjoint (S i) (S j))).card ≤ d) :
    ∃ ω : X → α, ∀ i : I, ω ∉ A i := by
  let Γ : I → Finset I := fun i =>
    Finset.univ.filter (fun j : I => j ≠ i ∧ ¬ Disjoint (S i) (S j))
  refine lll_symmetric A Γ p d hp hpd hdeg fun i T hiT hTΓ => ?_
  have hdisj : Disjoint (S i) (T.biUnion S) := by
    rw [Finset.disjoint_biUnion_right]
    intro j hj
    by_contra hnd
    have hji : j ≠ i := fun h => hiT (h ▸ hj)
    exact hTΓ j hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, hnd⟩)
  have hmul : ((A i ∩ good A T).card : ℝ) * (Fintype.card (X → α) : ℝ) =
      ((A i).card : ℝ) * ((good A T).card : ℝ) := by
    exact_mod_cast card_inter_of_dependsOn_disjoint hdisj (hdep i) (dependsOn_good A S hdep T)
  have hpos : (0 : ℝ) < (Fintype.card (X → α) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hle : ((A i ∩ good A T).card : ℝ) * (Fintype.card (X → α) : ℝ) ≤
      (p * ((good A T).card : ℝ)) * (Fintype.card (X → α) : ℝ) := by
    rw [hmul]
    calc ((A i).card : ℝ) * ((good A T).card : ℝ)
        ≤ (p * (Fintype.card (X → α) : ℝ)) * ((good A T).card : ℝ) :=
          mul_le_mul_of_nonneg_right (hprob i) (Nat.cast_nonneg _)
      _ = (p * ((good A T).card : ℝ)) * (Fintype.card (X → α) : ℝ) := by ring
  exact le_of_mul_le_mul_right hle hpos

end LLL

/- ### Section 2: Elementary Exponential Bounds, p-Weighted McDiarmid, and Weighted Chernoff -/

section Concentration

lemma exp_sub_one_sub_le_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x - 1 - x ≤ x ^ 2 := by
  have h := Real.exp_bound (x := x) (n := 2) hx (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have h1 := (le_abs_self _).trans h
  nlinarith [sq_nonneg x]

lemma bernoulli_mgf_step {p x : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (hx : |x| ≤ 1) :
    p * Real.exp ((1 - p) * x) + (1 - p) * Real.exp (-p * x) ≤ Real.exp (p * x ^ 2) := by
  have hfac : p * Real.exp ((1 - p) * x) + (1 - p) * Real.exp (-p * x) =
      Real.exp (-p * x) * (1 + p * (Real.exp x - 1)) := by
    have he : Real.exp ((1 - p) * x) = Real.exp (-p * x) * Real.exp x := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he]; ring
  rw [hfac]
  have h1 : 1 + p * (Real.exp x - 1) ≤ Real.exp (p * (Real.exp x - 1)) := by
    linarith [Real.add_one_le_exp (p * (Real.exp x - 1))]
  calc Real.exp (-p * x) * (1 + p * (Real.exp x - 1))
      ≤ Real.exp (-p * x) * Real.exp (p * (Real.exp x - 1)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (p * (Real.exp x - 1 - x)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (p * x ^ 2) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (exp_sub_one_sub_le_sq hx) hp0)

lemma one_sub_ge_exp_neg_sub_sq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    Real.exp (-p - p ^ 2) ≤ 1 - p := by
  have hmono : MonotoneOn (fun t : ℝ => (1 - t) * Real.exp (t + t ^ 2)) (Set.Icc 0 (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
    · exact ((continuous_const.sub continuous_id).mul
        (Real.continuous_exp.comp (continuous_id.add (continuous_id.pow 2)))).continuousOn
    · intro x _
      exact ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) |>.mul
        (((hasDerivAt_id x).add ((hasDerivAt_pow 2 x))).exp)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hd : HasDerivAt (fun t : ℝ => (1 - t) * Real.exp (t + t ^ 2))
          ((0 - 1) * Real.exp (x + x ^ 2) +
            (1 - x) * (Real.exp (x + x ^ 2) * (1 + (2 : ℕ) * x ^ (2 - 1)))) x :=
        ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).mul
          (((hasDerivAt_id x).add (hasDerivAt_pow 2 x)).exp)
      rw [hd.deriv]
      have hx0 : 0 ≤ x := le_of_lt hx.1
      have hx1 : x ≤ 1 / 2 := le_of_lt hx.2
      have hfac : (0 - 1) * Real.exp (x + x ^ 2) +
          (1 - x) * (Real.exp (x + x ^ 2) * (1 + (2 : ℕ) * x ^ (2 - 1))) =
          x * (1 - 2 * x) * Real.exp (x + x ^ 2) := by norm_num; ring
      rw [hfac]
      exact mul_nonneg (mul_nonneg hx0 (by linarith)) (Real.exp_pos _).le
  have h01 : (1 : ℝ) ≤ (1 - p) * Real.exp (p + p ^ 2) := by
    have h0 := hmono (Set.left_mem_Icc.mpr (by norm_num)) ⟨hp0, hp1⟩ hp0
    simpa using h0
  calc Real.exp (-p - p ^ 2)
      = (Real.exp (p + p ^ 2))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
    _ = 1 * (Real.exp (p + p ^ 2))⁻¹ := (one_mul _).symm
    _ ≤ ((1 - p) * Real.exp (p + p ^ 2)) * (Real.exp (p + p ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_right h01 (inv_nonneg.mpr (Real.exp_pos _).le)
    _ = 1 - p := mul_inv_cancel_right₀ (Real.exp_pos _).ne' _

lemma one_sub_pow_le_quad {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ n : ℕ, (1 - p) ^ n ≤ 1 - (n : ℝ) * p + ((n : ℝ) * ((n : ℝ) - 1) / 2) * p ^ 2
  | 0 => by simp
  | n + 1 => by
    have ih := one_sub_pow_le_quad hp0 hp1 n
    have hmul : (1 - p) ^ n * (1 - p) ≤
        (1 - (n : ℝ) * p + ((n : ℝ) * ((n : ℝ) - 1) / 2) * p ^ 2) * (1 - p) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have hnn : 0 ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * p ^ 3 := by
      rcases n with _ | n
      · simp
      · push_cast
        have : (n : ℝ) + 1 - 1 = (n : ℝ) := by ring
        rw [this]
        positivity
    rw [pow_succ]
    push_cast
    nlinarith

lemma exp_ge_pow_five_div {x : ℝ} (hx : 0 ≤ x) : x ^ 5 / 120 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have h0 : (0 : ℝ) ≤ x ^ 0 / (Nat.factorial 0 : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ x ^ 1 / (Nat.factorial 1 : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ x ^ 2 / (Nat.factorial 2 : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ x ^ 3 / (Nat.factorial 3 : ℝ) := by positivity
  have h4 : (0 : ℝ) ≤ x ^ 4 / (Nat.factorial 4 : ℝ) := by positivity
  have h5 : x ^ 5 / (Nat.factorial 5 : ℝ) = x ^ 5 / 120 := by norm_num [Nat.factorial]
  linarith

lemma exp_mul_sub_one_le {t u : ℝ} (_ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (t * u) - 1 ≤ u * (Real.exp t - 1) := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
    (show 0 ≤ 1 - u by linarith) hu0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  rw [mul_comm t u]
  linarith

/-- Induction core for two-sided `p`-weighted McDiarmid over `Fin m → Fin Q`. -/
lemma mgf_bernoulli_mcdiarmid (Q : ℕ) (hQ : 0 < Q) (lam : ℝ) :
    ∀ (m : ℕ) (c : Fin m → ℝ) (f : (Fin m → Fin Q) → ℝ),
    (∀ i, 0 ≤ c i) → (∀ i, |lam| * c i ≤ 1) →
    (∀ i ω (a b : Fin Q), a.val ≠ 0 → b.val ≠ 0 →
      f (Function.update ω i a) = f (Function.update ω i b)) →
    (∀ i ω (a : Fin Q), a.val ≠ 0 →
      |f (Function.update ω i ⟨0, hQ⟩) - f (Function.update ω i a)| ≤ c i) →
    ((∑ ω : Fin m → Fin Q, Real.exp (lam * (f ω -
      (∑ τ : Fin m → Fin Q, f τ) / (Q ^ m : ℝ)))) / (Q ^ m : ℝ)) ≤
      Real.exp (lam ^ 2 / (Q : ℝ) * ∑ i : Fin m, (c i) ^ 2) := by
  intro m
  induction m with
  | zero =>
    intro c f _ _ _ _
    have hcard : Fintype.card (Fin 0 → Fin Q) = 1 := by simp
    have hsum : ∀ g : (Fin 0 → Fin Q) → ℝ, ∑ ω : Fin 0 → Fin Q, g ω = g Fin.elim0 := by
      intro g
      rw [Finset.sum_eq_single Fin.elim0]
      · intro ω _ hne; exact absurd (Subsingleton.elim ω Fin.elim0) hne
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, hsum]
    simp
  | succ m ih =>
    intro c f hc0 hlam hconst hlip
    have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
    have hQmpos : (0 : ℝ) < (Q ^ m : ℝ) := pow_pos hQpos m
    have hQm1pos : (0 : ℝ) < (Q ^ (m + 1) : ℝ) := pow_pos hQpos (m + 1)
    let e : (Fin (m + 1) → Fin Q) ≃ Fin Q × (Fin m → Fin Q) :=
      Fin.consEquiv (fun _ => Fin Q) |>.symm
    let h : Fin Q → (Fin m → Fin Q) → ℝ := fun a ω' => f (Fin.cons a ω')
    let μ : Fin Q → ℝ := fun a => (∑ ω' : Fin m → Fin Q, h a ω') / (Q ^ m : ℝ)
    let μtot : ℝ := (∑ τ : Fin (m + 1) → Fin Q, f τ) / (Q ^ (m + 1) : ℝ)
    have hsum_split : ∀ g : (Fin (m + 1) → Fin Q) → ℝ,
        ∑ ω : Fin (m + 1) → Fin Q, g ω = ∑ a : Fin Q, ∑ ω' : Fin m → Fin Q, g (Fin.cons a ω') := by
      intro g
      rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
      rfl
    have hμtot : μtot = (∑ a : Fin Q, μ a) / (Q : ℝ) := by
      simp only [μtot, μ, hsum_split f, h]
      rw [← Finset.sum_div, div_div, ← pow_succ]
    have hcons_upd : ∀ (a : Fin Q) (ω' : Fin m → Fin Q) (b : Fin Q),
        Function.update (Fin.cons (α := fun _ => Fin Q) a ω') (0 : Fin (m + 1)) b =
          Fin.cons (α := fun _ => Fin Q) b ω' := by
      intro a ω' b; ext j; refine Fin.cases ?_ ?_ j <;> simp
    have hcons_succ : ∀ (a : Fin Q) (ω' : Fin m → Fin Q) (i : Fin m) (b : Fin Q),
        Fin.cons (α := fun _ => Fin Q) a (Function.update ω' i b) =
          Function.update (Fin.cons (α := fun _ => Fin Q) a ω') i.succ b := by
      intro a ω' i b; ext j; refine Fin.cases ?_ ?_ j
      · simp [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      · intro k; by_cases hk : k = i <;> simp [hk]
    have hih : ∀ a : Fin Q,
        (∑ ω' : Fin m → Fin Q, Real.exp (lam * (h a ω' - μ a))) / (Q ^ m : ℝ) ≤
          Real.exp (lam ^ 2 / (Q : ℝ) * ∑ i : Fin m, (c i.succ) ^ 2) := by
      intro a
      refine ih (fun i => c i.succ) (h a) (fun i => hc0 i.succ) (fun i => hlam i.succ) ?_ ?_
      · intro i ω' b₁ b₂ hb₁ hb₂
        simp only [h, hcons_succ]
        exact hconst i.succ (Fin.cons a ω') b₁ b₂ hb₁ hb₂
      · intro i ω' b hb
        simp only [h, hcons_succ]
        exact hlip i.succ (Fin.cons a ω') b hb
    have hstep_sum :
        (∑ ω : Fin (m + 1) → Fin Q, Real.exp (lam * (f ω - μtot))) / (Q ^ (m + 1) : ℝ) ≤
          ((∑ a : Fin Q, Real.exp (lam * (μ a - μtot))) / (Q : ℝ)) *
            Real.exp (lam ^ 2 / (Q : ℝ) * ∑ i : Fin m, (c i.succ) ^ 2) := by
      rw [hsum_split]
      have hrewrite : ∀ a : Fin Q,
          ∑ ω' : Fin m → Fin Q, Real.exp (lam * (h a ω' - μtot)) =
            Real.exp (lam * (μ a - μtot)) *
              ∑ ω' : Fin m → Fin Q, Real.exp (lam * (h a ω' - μ a)) := by
        intro a
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω' _ => ?_
        rw [← Real.exp_add]; congr 1; ring
      have hterm : ∀ a : Fin Q,
          (∑ ω' : Fin m → Fin Q, Real.exp (lam * (h a ω' - μtot))) / (Q ^ m : ℝ) ≤
            Real.exp (lam * (μ a - μtot)) *
              Real.exp (lam ^ 2 / (Q : ℝ) * ∑ i : Fin m, (c i.succ) ^ 2) := by
        intro a
        rw [hrewrite a, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hih a) (Real.exp_pos _).le
      calc (∑ a : Fin Q, ∑ ω' : Fin m → Fin Q, Real.exp (lam * (h a ω' - μtot))) / (Q ^ (m + 1) : ℝ)
          = (∑ a : Fin Q, (∑ ω' : Fin m → Fin Q, Real.exp (lam * (h a ω' - μtot))) / (Q ^ m : ℝ)) /
              (Q : ℝ) := by rw [← Finset.sum_div, div_div, ← pow_succ]
        _ ≤ (∑ a : Fin Q, Real.exp (lam * (μ a - μtot)) *
              Real.exp (lam ^ 2 / (Q : ℝ) * ∑ i : Fin m, (c i.succ) ^ 2)) / (Q : ℝ) :=
            div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => hterm a) hQpos.le
        _ = ((∑ a : Fin Q, Real.exp (lam * (μ a - μtot))) / (Q : ℝ)) *
              Real.exp (lam ^ 2 / (Q : ℝ) * ∑ i : Fin m, (c i.succ) ^ 2) := by
            rw [← Finset.sum_mul, mul_div_right_comm]
    have h0_bound : (∑ a : Fin Q, Real.exp (lam * (μ a - μtot))) / (Q : ℝ) ≤
        Real.exp (lam ^ 2 / (Q : ℝ) * (c 0) ^ 2) := by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hQ) with hQ1 | hQ2
      · have hsub : Subsingleton (Fin Q) := by
          rw [← hQ1]; infer_instance
        have hzero : ∀ a : Fin Q, a = ⟨0, hQ⟩ := fun a => Subsingleton.elim a ⟨0, hQ⟩
        have hQ1R : (Q : ℝ) = 1 := by exact_mod_cast hQ1.symm
        have hμeq : μtot = μ ⟨0, hQ⟩ := by
          rw [hμtot, Finset.sum_eq_single ⟨0, hQ⟩]
          · rw [hQ1R, div_one]
          · intro b _ hb; exact absurd (hzero b) hb
          · intro h0; exact absurd (Finset.mem_univ _) h0
        rw [Finset.sum_eq_single ⟨0, hQ⟩]
        · rw [hμeq, sub_self, mul_zero, Real.exp_zero, hQ1R, div_one]
          exact Real.one_le_exp (by positivity)
        · intro b _ hb; exact absurd (hzero b) hb
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · let a₁ : Fin Q := ⟨1, hQ2⟩
        have ha₁ : a₁.val ≠ 0 := by simp [a₁]
        have hμ_eq : ∀ a : Fin Q, a.val ≠ 0 → μ a = μ a₁ := by
          intro a ha
          simp only [μ, h]
          congr 1
          refine Finset.sum_congr rfl fun ω' _ => ?_
          have h1 := hconst 0 (Fin.cons a ω') a a₁ ha ha₁
          simpa only [hcons_upd] using h1
        let z0 : Fin Q := ⟨0, hQ⟩
        have hsplitQ : ∀ g : Fin Q → ℝ, (∀ a : Fin Q, a.val ≠ 0 → g a = g a₁) →
            (∑ a : Fin Q, g a) / (Q : ℝ) = (1 / (Q : ℝ)) * g z0 + (1 - 1 / (Q : ℝ)) * g a₁ := by
          intro g hg
          have h1 : ∑ a : Fin Q, g a = g z0 + ∑ a ∈ Finset.univ.erase z0, g a :=
            (Finset.add_sum_erase _ _ (Finset.mem_univ z0)).symm
          have h2 : ∑ a ∈ Finset.univ.erase z0, g a = ((Q - 1 : ℕ) : ℝ) * g a₁ := by
            calc ∑ a ∈ Finset.univ.erase z0, g a
                = ∑ _a ∈ Finset.univ.erase z0, g a₁ :=
                  Finset.sum_congr rfl fun a ha => hg a (fun h0 => (Finset.mem_erase.mp ha).1 (Fin.ext h0))
              _ = ((Finset.univ.erase z0).card : ℝ) * g a₁ := by simp
              _ = ((Q - 1 : ℕ) : ℝ) * g a₁ := by simp
          rw [h1, h2, Nat.cast_sub (Nat.succ_le_of_lt hQ), Nat.cast_one]
          field_simp
        have hμtot' : μtot = (1 / (Q : ℝ)) * μ z0 + (1 - 1 / (Q : ℝ)) * μ a₁ := by
          rw [hμtot]; exact hsplitQ μ hμ_eq
        let u : ℝ := μ z0 - μ a₁
        have hu_le : |u| ≤ c 0 := by
          have hsub : u = (∑ ω' : Fin m → Fin Q, (h z0 ω' - h a₁ ω')) / (Q ^ m : ℝ) := by
            simp only [u, μ, ← sub_div, ← Finset.sum_sub_distrib]
          rw [hsub, abs_div, abs_of_pos hQmpos]
          rw [div_le_iff₀ hQmpos]
          calc |∑ ω' : Fin m → Fin Q, (h z0 ω' - h a₁ ω')|
              ≤ ∑ ω' : Fin m → Fin Q, |h z0 ω' - h a₁ ω'| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _ω' : Fin m → Fin Q, c 0 := Finset.sum_le_sum fun ω' _ => by
                have h1 := hlip 0 (Fin.cons z0 ω') a₁ ha₁
                simpa only [h, hcons_upd] using h1
            _ = c 0 * (Q ^ m : ℝ) := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
                  nsmul_eq_mul, Nat.cast_pow, mul_comm]
        have hdiff0 : μ z0 - μtot = (1 - 1 / (Q : ℝ)) * u := by rw [hμtot']; dsimp [u]; ring
        have hdiff1 : μ a₁ - μtot = -(1 / (Q : ℝ)) * u := by rw [hμtot']; dsimp [u]; ring
        have hexp_split := hsplitQ (fun a => Real.exp (lam * (μ a - μtot)))
          (fun a ha => by rw [hμ_eq a ha])
        rw [hexp_split, hdiff0, hdiff1]
        have hx1 : |lam * u| ≤ 1 := by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_left hu_le (abs_nonneg lam)).trans (hlam 0)
        have hp0 : (0 : ℝ) ≤ 1 / (Q : ℝ) := by positivity
        have hp1 : (1 / (Q : ℝ)) ≤ 1 := by
          rw [div_le_one hQpos]; exact_mod_cast Nat.succ_le_of_lt hQ
        have hmgf := bernoulli_mgf_step hp0 hp1 hx1
        have hmul_eq1 : lam * ((1 - 1 / (Q : ℝ)) * u) = (1 - 1 / (Q : ℝ)) * (lam * u) := by ring
        have hmul_eq2 : lam * (-(1 / (Q : ℝ)) * u) = -(1 / (Q : ℝ)) * (lam * u) := by ring
        rw [hmul_eq1, hmul_eq2]
        refine hmgf.trans (Real.exp_le_exp.mpr ?_)
        have hu_sq : u ^ 2 ≤ (c 0) ^ 2 := by
          nlinarith [abs_le.mp hu_le, hc0 0]
        calc 1 / (Q : ℝ) * (lam * u) ^ 2
            = lam ^ 2 / (Q : ℝ) * u ^ 2 := by ring
          _ ≤ lam ^ 2 / (Q : ℝ) * (c 0) ^ 2 :=
              mul_le_mul_of_nonneg_left hu_sq (by positivity)
    calc (∑ ω : Fin (m + 1) → Fin Q, Real.exp (lam * (f ω - μtot))) / (Q ^ (m + 1) : ℝ)
        ≤ Real.exp (lam ^ 2 / (Q : ℝ) * (c 0) ^ 2) *
            Real.exp (lam ^ 2 / (Q : ℝ) * ∑ i : Fin m, (c i.succ) ^ 2) :=
          hstep_sum.trans (mul_le_mul_of_nonneg_right h0_bound (Real.exp_pos _).le)
      _ = Real.exp (lam ^ 2 / (Q : ℝ) * ((c 0) ^ 2 + ∑ i : Fin m, (c i.succ) ^ 2)) := by
          rw [← Real.exp_add]; congr 1; ring
      _ = Real.exp (lam ^ 2 / (Q : ℝ) * ∑ i : Fin (m + 1), (c i) ^ 2) := by
          rw [Fin.sum_univ_succ]

/-- Two-sided `p`-weighted McDiarmid inequality on `X → Fin Q` for a function depending on `S ⊆ X`. -/
theorem bernoulli_mcdiarmid_sub {X : Type*} [Fintype X] [DecidableEq X]
    (Q : ℕ) (hQ : 0 < Q) (S : Finset X) (c : X → ℝ) (f : (X → Fin Q) → ℝ)
    (k_max V t : ℝ) (hk : 0 < k_max) (hV : 0 < V) (ht : 0 < t)
    (hc0 : ∀ x ∈ S, 0 ≤ c x) (hck : ∀ x ∈ S, c x ≤ k_max)
    (hV_ge : (∑ x ∈ S, (c x) ^ 2) / (Q : ℝ) ≤ V)
    (hdep : ∀ ω₁ ω₂ : X → Fin Q, (∀ x ∈ S, ω₁ x = ω₂ x) → f ω₁ = f ω₂)
    (hconst : ∀ x ∈ S, ∀ ω (a b : Fin Q), a.val ≠ 0 → b.val ≠ 0 →
      f (Function.update ω x a) = f (Function.update ω x b))
    (hlip : ∀ x ∈ S, ∀ ω (a : Fin Q), a.val ≠ 0 →
      |f (Function.update ω x ⟨0, hQ⟩) - f (Function.update ω x a)| ≤ c x) :
    let μ : ℝ := (∑ ω : X → Fin Q, f ω) / (Fintype.card (X → Fin Q) : ℝ)
    ((Finset.univ.filter (fun ω : X → Fin Q => t ≤ |f ω - μ|)).card : ℝ) ≤
      2 * Real.exp (-min (t ^ 2 / (4 * V)) (t / (2 * k_max))) * (Fintype.card (X → Fin Q) : ℝ) := by
  intro μ
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  let a₀ : Fin Q := ⟨0, hQ⟩
  let eS := splitProdEquiv (α := Fin Q) S
  let eFin : {x : X // x ∈ S} ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  let g : (Fin S.card → Fin Q) → ℝ := fun τ => f (eS.symm (τ ∘ eFin, fun _ => a₀))
  have hf_eq : ∀ ω : X → Fin Q, f ω = g ((eS ω).1 ∘ eFin.symm) := fun ω => by
    apply hdep
    intro x hx
    simp only [eS, splitProdEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, hx, dite_true,
      Function.comp_apply, Equiv.symm_apply_apply]
  let E_all : (X → Fin Q) ≃ (Fin S.card → Fin Q) × ({x : X // x ∉ S} → Fin Q) :=
    eS.trans (Equiv.prodCongr (Equiv.arrowCongr eFin (Equiv.refl (Fin Q))) (Equiv.refl _))
  have hf_E : ∀ ω : X → Fin Q, f ω = g (E_all ω).1 := fun ω => by
    simpa [E_all, Equiv.arrowCongr] using hf_eq ω
  have hcardQ : (Fintype.card (Fin S.card → Fin Q) : ℝ) = (Q ^ S.card : ℝ) := by
    simp
  have hcardTot : (Fintype.card (X → Fin Q) : ℝ) =
      (Q ^ S.card : ℝ) * (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) := by
    have h1 : Fintype.card (X → Fin Q) =
        Fintype.card (Fin S.card → Fin Q) * Fintype.card ({x : X // x ∉ S} → Fin Q) := by
      rw [Fintype.card_congr E_all, Fintype.card_prod]
    rw [← hcardQ]; exact_mod_cast h1
  have hRest_pos : (0 : ℝ) < (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hQmpos : (0 : ℝ) < (Q ^ S.card : ℝ) := pow_pos hQpos S.card
  have hμ_eq : μ = (∑ τ : Fin S.card → Fin Q, g τ) / (Q ^ S.card : ℝ) := by
    have hsum : ∑ ω : X → Fin Q, f ω =
        (∑ τ : Fin S.card → Fin Q, g τ) * (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) := by
      calc ∑ ω : X → Fin Q, f ω
          = ∑ ω : X → Fin Q, g (E_all ω).1 := Finset.sum_congr rfl fun ω _ => hf_E ω
        _ = ∑ p : (Fin S.card → Fin Q) × ({x : X // x ∉ S} → Fin Q), g p.1 :=
            Equiv.sum_comp E_all (fun p => g p.1)
        _ = ∑ τ : Fin S.card → Fin Q, ∑ _r : {x : X // x ∉ S} → Fin Q, g τ :=
            Fintype.sum_prod_type _
        _ = (∑ τ : Fin S.card → Fin Q, g τ) * (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [← Finset.mul_sum, mul_comm]
    simp only [μ, hsum, hcardTot]
    rw [mul_div_mul_right _ _ hRest_pos.ne']
  have hsum_c : ∑ i : Fin S.card, (c (eFin.symm i).1) ^ 2 = ∑ x ∈ S, (c x) ^ 2 := by
    calc ∑ i : Fin S.card, (c (eFin.symm i).1) ^ 2
        = ∑ s : {x : X // x ∈ S}, (c s.1) ^ 2 := Equiv.sum_comp eFin.symm (fun s => (c s.1) ^ 2)
      _ = ∑ x ∈ S, (c x) ^ 2 := Finset.sum_coe_sort S (fun x => (c x) ^ 2)
  have hg_upd : ∀ (i : Fin S.card) (τ : Fin S.card → Fin Q) (a : Fin Q),
      g (Function.update τ i a) =
        f (Function.update (eS.symm (τ ∘ eFin, fun _ => a₀)) (eFin.symm i).1 a) := by
    intro i τ a
    apply hdep
    intro x hx
    by_cases hxi : x = (eFin.symm i).1
    · subst hxi
      have heq : eFin ⟨(eFin.symm i).1, hx⟩ = i := by
        have hsub : (⟨(eFin.symm i).1, hx⟩ : {y : X // y ∈ S}) = eFin.symm i := Subtype.ext rfl
        rw [hsub, eFin.apply_symm_apply]
      simp only [eS, splitProdEquiv, Equiv.coe_fn_symm_mk, hx, dite_true, Function.comp_apply,
        heq, Function.update_self]
    · have hne : eFin ⟨x, hx⟩ ≠ i := fun h => hxi (by
        have := congrArg (fun s : {y : X // y ∈ S} => s.1) (eFin.symm_apply_eq.mpr h.symm)
        exact this.symm)
      simp only [eS, splitProdEquiv, Equiv.coe_fn_symm_mk, hx, dite_true, Function.comp_apply,
        Function.update_of_ne hne, Function.update_of_ne hxi]
  have hone_side : ∀ (sgn : ℝ), (sgn = 1 ∨ sgn = -1) →
      ((Finset.univ.filter (fun τ : Fin S.card → Fin Q => t ≤ sgn * (g τ - μ))).card : ℝ) ≤
        Real.exp (-min (t ^ 2 / (4 * V)) (t / (2 * k_max))) * (Q ^ S.card : ℝ) := by
    intro sgn hsgn
    let θ : ℝ := min (1 / k_max) (t / (2 * V))
    have hθ_pos : 0 < θ := lt_min (one_div_pos.mpr hk) (div_pos ht (by linarith))
    have hθ_k : θ ≤ 1 / k_max := min_le_left _ _
    have hθ_V : θ ≤ t / (2 * V) := min_le_right _ _
    let lam : ℝ := sgn * θ
    have habs_sgn : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
    have hlam_abs : |lam| = θ := by rw [abs_mul, habs_sgn, one_mul, abs_of_pos hθ_pos]
    have hmgf := mgf_bernoulli_mcdiarmid Q hQ lam S.card (fun i => c (eFin.symm i).1) g
      (fun i => hc0 _ (eFin.symm i).2)
      (fun i => by
        rw [hlam_abs]
        calc θ * c (eFin.symm i).1 ≤ (1 / k_max) * k_max :=
              mul_le_mul hθ_k (hck _ (eFin.symm i).2) (hc0 _ (eFin.symm i).2) (by positivity)
          _ = 1 := one_div_mul_cancel hk.ne')
      (fun i τ a b ha hb => by
        rw [hg_upd, hg_upd]; exact hconst _ (eFin.symm i).2 _ a b ha hb)
      (fun i τ a ha => by
        rw [hg_upd, hg_upd]; exact hlip _ (eFin.symm i).2 _ a ha)
    rw [← hμ_eq, hsum_c] at hmgf
    have hlam_sq : lam ^ 2 = θ ^ 2 := by
      rcases hsgn with rfl | rfl <;> simp [lam]
    have hmgf' : (∑ τ : Fin S.card → Fin Q, Real.exp (lam * (g τ - μ))) ≤
        Real.exp (θ ^ 2 * V) * (Q ^ S.card : ℝ) := by
      have h1 : (∑ τ : Fin S.card → Fin Q, Real.exp (lam * (g τ - μ))) ≤
          Real.exp (lam ^ 2 / (Q : ℝ) * ∑ x ∈ S, (c x) ^ 2) * (Q ^ S.card : ℝ) :=
        (div_le_iff₀ hQmpos).mp hmgf
      refine h1.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hQmpos.le)
      rw [hlam_sq]
      calc θ ^ 2 / (Q : ℝ) * ∑ x ∈ S, (c x) ^ 2
          = θ ^ 2 * ((∑ x ∈ S, (c x) ^ 2) / (Q : ℝ)) := by ring
        _ ≤ θ ^ 2 * V := mul_le_mul_of_nonneg_left hV_ge (sq_nonneg θ)
    have hmarkov : Real.exp (θ * t) *
        ((Finset.univ.filter (fun τ : Fin S.card → Fin Q => t ≤ sgn * (g τ - μ))).card : ℝ) ≤
        ∑ τ : Fin S.card → Fin Q, Real.exp (lam * (g τ - μ)) := by
      calc Real.exp (θ * t) *
            ((Finset.univ.filter (fun τ : Fin S.card → Fin Q => t ≤ sgn * (g τ - μ))).card : ℝ)
          = ∑ _τ ∈ Finset.univ.filter (fun τ : Fin S.card → Fin Q => t ≤ sgn * (g τ - μ)),
              Real.exp (θ * t) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ τ ∈ Finset.univ.filter (fun τ : Fin S.card → Fin Q => t ≤ sgn * (g τ - μ)),
              Real.exp (lam * (g τ - μ)) := by
            refine Finset.sum_le_sum fun τ hτ => Real.exp_le_exp.mpr ?_
            have hle : t ≤ sgn * (g τ - μ) := (Finset.mem_filter.mp hτ).2
            calc θ * t ≤ θ * (sgn * (g τ - μ)) := mul_le_mul_of_nonneg_left hle hθ_pos.le
              _ = lam * (g τ - μ) := by simp only [lam]; ring
        _ ≤ ∑ τ : Fin S.card → Fin Q, Real.exp (lam * (g τ - μ)) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le
    have hcomb := (le_div_iff₀' (Real.exp_pos (θ * t))).mpr (hmarkov.trans hmgf')
    have hexp_bound : θ ^ 2 * V - θ * t ≤ -min (t ^ 2 / (4 * V)) (t / (2 * k_max)) := by
      have hquad : θ ^ 2 * V - θ * t ≤ -(θ * t) / 2 := by
        have h1 : θ * V ≤ t / 2 := by
          have := mul_le_mul_of_nonneg_right hθ_V hV.le
          have h2 : t / (2 * V) * V = t / 2 := by field_simp
          linarith
        nlinarith
      have hmin : min (t ^ 2 / (4 * V)) (t / (2 * k_max)) ≤ (θ * t) / 2 := by
        rcases le_total (1 / k_max) (t / (2 * V)) with hle | hle
        · have hθe : θ = 1 / k_max := min_eq_left hle
          rw [hθe]
          calc min (t ^ 2 / (4 * V)) (t / (2 * k_max)) ≤ t / (2 * k_max) := min_le_right _ _
            _ = 1 / k_max * t / 2 := by ring
        · have hθe : θ = t / (2 * V) := min_eq_right hle
          rw [hθe]
          calc min (t ^ 2 / (4 * V)) (t / (2 * k_max)) ≤ t ^ 2 / (4 * V) := min_le_left _ _
            _ = t / (2 * V) * t / 2 := by ring
      linarith
    calc ((Finset.univ.filter (fun τ : Fin S.card → Fin Q => t ≤ sgn * (g τ - μ))).card : ℝ)
        ≤ Real.exp (θ ^ 2 * V) * (Q ^ S.card : ℝ) / Real.exp (θ * t) := hcomb
      _ = Real.exp (θ ^ 2 * V - θ * t) * (Q ^ S.card : ℝ) := by
          rw [mul_div_right_comm, ← Real.exp_sub]
      _ ≤ Real.exp (-min (t ^ 2 / (4 * V)) (t / (2 * k_max))) * (Q ^ S.card : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp_bound) hQmpos.le
  let E_sub : Finset (Fin S.card → Fin Q) :=
    Finset.univ.filter (fun τ => t ≤ |g τ - μ|)
  have hE_sub : (E_sub.card : ℝ) ≤
      2 * Real.exp (-min (t ^ 2 / (4 * V)) (t / (2 * k_max))) * (Q ^ S.card : ℝ) := by
    have hcov : E_sub ⊆
        Finset.univ.filter (fun τ => t ≤ (1 : ℝ) * (g τ - μ)) ∪
        Finset.univ.filter (fun τ => t ≤ (-1 : ℝ) * (g τ - μ)) := by
      intro τ hτ
      simp only [E_sub, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hτ ⊢
      rcases le_or_gt 0 (g τ - μ) with hnn | hneg
      · left; rw [abs_of_nonneg hnn] at hτ; linarith
      · right; rw [abs_of_neg hneg] at hτ; linarith
    have hcu : (E_sub.card : ℝ) ≤
        ((Finset.univ.filter (fun τ => t ≤ (1 : ℝ) * (g τ - μ))).card : ℝ) +
        ((Finset.univ.filter (fun τ => t ≤ (-1 : ℝ) * (g τ - μ))).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
    linarith [hone_side 1 (Or.inl rfl), hone_side (-1) (Or.inr rfl)]
  have him : (Finset.univ.filter (fun ω : X → Fin Q => t ≤ |f ω - μ|)).image E_all =
      E_sub ×ˢ Finset.univ := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      and_true, E_sub]
    constructor
    · rintro ⟨ω, hω, rfl⟩; rwa [← hf_E ω]
    · intro hp; refine ⟨E_all.symm p, ?_, E_all.apply_symm_apply p⟩
      rw [hf_E (E_all.symm p), E_all.apply_symm_apply p]; exact hp
  have hcard_eq : ((Finset.univ.filter (fun ω : X → Fin Q => t ≤ |f ω - μ|)).card : ℝ) =
      (E_sub.card : ℝ) * (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) := by
    have h1 : (Finset.univ.filter (fun ω : X → Fin Q => t ≤ |f ω - μ|)).card =
        E_sub.card * Fintype.card ({x : X // x ∉ S} → Fin Q) := by
      rw [← Finset.card_image_of_injective _ E_all.injective, him, Finset.card_product,
        Finset.card_univ]
    exact_mod_cast h1
  rw [hcard_eq, hcardTot]
  calc (E_sub.card : ℝ) * (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ)
      ≤ (2 * Real.exp (-min (t ^ 2 / (4 * V)) (t / (2 * k_max))) * (Q ^ S.card : ℝ)) *
          (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) :=
        mul_le_mul_of_nonneg_right hE_sub hRest_pos.le
    _ = 2 * Real.exp (-min (t ^ 2 / (4 * V)) (t / (2 * k_max))) *
          ((Q ^ S.card : ℝ) * (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ)) := by ring

/-- Weighted Chernoff upper tail for `∑ x ∈ S, w x * 1_{ω x = 0}` with `0 ≤ w x ≤ k`. -/
theorem weighted_chernoff_sub {X : Type*} [Fintype X] [DecidableEq X]
    (Q : ℕ) (hQ : 0 < Q) (S : Finset X) (w : X → ℝ) (k μ₀ : ℝ)
    (hk : 0 < k) (hμ₀ : 0 ≤ μ₀)
    (hw0 : ∀ x ∈ S, 0 ≤ w x) (hwk : ∀ x ∈ S, w x ≤ k)
    (hmean : (∑ x ∈ S, w x) / (Q : ℝ) ≤ μ₀) :
    ((Finset.univ.filter (fun ω : X → Fin Q =>
        2 * μ₀ ≤ ∑ x ∈ S, if (ω x).val = 0 then w x else 0)).card : ℝ) ≤
      Real.exp (-(1 / (3 * k)) * μ₀) * (Fintype.card (X → Fin Q) : ℝ) := by
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  let eS := splitProdEquiv (α := Fin Q) S
  let lam : ℝ := Real.log 2 / k
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlam_pos : 0 < lam := div_pos hlog2_pos hk
  have hexp_sum :
      ∑ τ : {x : X // x ∈ S} → Fin Q,
        Real.exp (lam * ∑ s : {x : X // x ∈ S}, if (τ s).val = 0 then w s.1 else 0) =
      ∏ s : {x : X // x ∈ S}, (((Q - 1 : ℕ) : ℝ) + Real.exp (lam * w s.1)) := by
    have hterm : ∀ τ : {x : X // x ∈ S} → Fin Q,
        Real.exp (lam * ∑ s : {x : X // x ∈ S}, if (τ s).val = 0 then w s.1 else 0) =
        ∏ s : {x : X // x ∈ S}, if (τ s).val = 0 then Real.exp (lam * w s.1) else 1 := by
      intro τ
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun s _ => ?_
      split_ifs <;> simp
    simp_rw [hterm]
    have hpi : (Finset.univ : Finset ({x : X // x ∈ S} → Fin Q)) =
        Fintype.piFinset (fun _ : {x : X // x ∈ S} => (Finset.univ : Finset (Fin Q))) := by
      ext τ; simp
    have hswap := (Finset.prod_univ_sum (fun _ : {x : X // x ∈ S} => (Finset.univ : Finset (Fin Q)))
      (fun (s : {x : X // x ∈ S}) (a : Fin Q) =>
        if a.val = 0 then Real.exp (lam * w s.1) else (1 : ℝ))).symm
    rw [hpi, hswap]
    refine Finset.prod_congr rfl fun s _ => ?_
    let z0 : Fin Q := ⟨0, hQ⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z0)]
    have hz0 : (if z0.val = 0 then Real.exp (lam * w s.1) else (1 : ℝ)) = Real.exp (lam * w s.1) := by
      simp [z0]
    have hrest : ∑ a ∈ Finset.univ.erase z0,
        (if a.val = 0 then Real.exp (lam * w s.1) else (1 : ℝ)) = ((Q - 1 : ℕ) : ℝ) := by
      calc ∑ a ∈ Finset.univ.erase z0, (if a.val = 0 then Real.exp (lam * w s.1) else (1 : ℝ))
          = ∑ _a ∈ Finset.univ.erase z0, (1 : ℝ) :=
            Finset.sum_congr rfl fun a ha => by
              have hne : a.val ≠ 0 := fun h0 => (Finset.mem_erase.mp ha).1 (Fin.ext h0)
              simp [hne]
        _ = ((Q - 1 : ℕ) : ℝ) := by simp
    rw [hz0, hrest, add_comm]
  have hprod_le :
      (∏ s : {x : X // x ∈ S}, (((Q - 1 : ℕ) : ℝ) + Real.exp (lam * w s.1))) ≤
        Real.exp (μ₀ / k) * (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) := by
    have hcardS : (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) =
        ∏ _s : {x : X // x ∈ S}, (Q : ℝ) := by
      rw [Fintype.card_fun, Nat.cast_pow, Finset.prod_const, Finset.card_univ]; simp
    have hfac : (∏ s : {x : X // x ∈ S}, (((Q - 1 : ℕ) : ℝ) + Real.exp (lam * w s.1))) =
        (∏ s : {x : X // x ∈ S}, (1 + (Real.exp (lam * w s.1) - 1) / (Q : ℝ))) *
          (∏ _s : {x : X // x ∈ S}, (Q : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [Nat.cast_sub (Nat.succ_le_of_lt hQ), Nat.cast_one]
      field_simp; ring
    have hexp_bound : (∏ s : {x : X // x ∈ S}, (1 + (Real.exp (lam * w s.1) - 1) / (Q : ℝ))) ≤
        Real.exp (μ₀ / k) := by
      calc (∏ s : {x : X // x ∈ S}, (1 + (Real.exp (lam * w s.1) - 1) / (Q : ℝ)))
          ≤ ∏ s : {x : X // x ∈ S}, Real.exp ((Real.exp (lam * w s.1) - 1) / (Q : ℝ)) := by
            refine Finset.prod_le_prod (fun s _ => ?_) (fun s _ => ?_)
            · have hge : (1 : ℝ) ≤ Real.exp (lam * w s.1) :=
                Real.one_le_exp (mul_nonneg hlam_pos.le (hw0 s.1 s.2))
              have : 0 ≤ (Real.exp (lam * w s.1) - 1) / (Q : ℝ) :=
                div_nonneg (by linarith) hQpos.le
              linarith
            · linarith [Real.add_one_le_exp ((Real.exp (lam * w s.1) - 1) / (Q : ℝ))]
        _ = Real.exp (∑ s : {x : X // x ∈ S}, (Real.exp (lam * w s.1) - 1) / (Q : ℝ)) := by
            rw [Real.exp_sum]
        _ ≤ Real.exp (μ₀ / k) := by
            apply Real.exp_le_exp.mpr
            have hterm_le : ∀ s : {x : X // x ∈ S},
                (Real.exp (lam * w s.1) - 1) / (Q : ℝ) ≤ (w s.1 / k) / (Q : ℝ) := by
              intro s
              refine div_le_div_of_nonneg_right ?_ hQpos.le
              have hcv := exp_mul_sub_one_le (t := Real.log 2) (u := w s.1 / k) hlog2_pos.le
                (div_nonneg (hw0 s.1 s.2) hk.le) ((div_le_one hk).mpr (hwk s.1 s.2))
              have harg : Real.log 2 * (w s.1 / k) = lam * w s.1 := by simp only [lam]; ring
              rw [harg, Real.exp_log (by norm_num)] at hcv
              linarith
            calc ∑ s : {x : X // x ∈ S}, (Real.exp (lam * w s.1) - 1) / (Q : ℝ)
                ≤ ∑ s : {x : X // x ∈ S}, (w s.1 / k) / (Q : ℝ) :=
                  Finset.sum_le_sum fun s _ => hterm_le s
              _ = ((∑ x ∈ S, w x) / (Q : ℝ)) / k := by
                  rw [← Finset.sum_coe_sort S w, Finset.sum_div, Finset.sum_div]
                  refine Finset.sum_congr rfl fun s _ => ?_; ring
              _ ≤ μ₀ / k := div_le_div_of_nonneg_right hmean hk.le
    rw [hfac, hcardS]
    exact mul_le_mul_of_nonneg_right hexp_bound (Finset.prod_nonneg fun _ _ => hQpos.le)
  let E₁ : Finset ({x : X // x ∈ S} → Fin Q) :=
    Finset.univ.filter (fun τ => 2 * μ₀ ≤ ∑ s : {x : X // x ∈ S}, if (τ s).val = 0 then w s.1 else 0)
  have hE₁ : (E₁.card : ℝ) ≤
      Real.exp (-(1 / (3 * k)) * μ₀) * (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) := by
    have hmarkov : Real.exp (lam * (2 * μ₀)) * (E₁.card : ℝ) ≤
        ∑ τ : {x : X // x ∈ S} → Fin Q,
          Real.exp (lam * ∑ s : {x : X // x ∈ S}, if (τ s).val = 0 then w s.1 else 0) := by
      calc Real.exp (lam * (2 * μ₀)) * (E₁.card : ℝ)
          = ∑ _τ ∈ E₁, Real.exp (lam * (2 * μ₀)) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ τ ∈ E₁, Real.exp (lam * ∑ s : {x : X // x ∈ S}, if (τ s).val = 0 then w s.1 else 0) :=
            Finset.sum_le_sum fun τ hτ =>
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hτ).2 hlam_pos.le)
        _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le
    have hcomb := (le_div_iff₀' (Real.exp_pos (lam * (2 * μ₀)))).mpr
      (hmarkov.trans (hexp_sum ▸ hprod_le))
    have hlog2_lb : (2 / 3 : ℝ) < Real.log 2 := by
      have h1 : Real.exp (2 / 3 : ℝ) < 2 := by
        have hb := Real.exp_bound (x := 2 / 3) (n := 3) (by norm_num) (by norm_num)
        norm_num [Finset.sum_range_succ, Nat.factorial] at hb
        linarith [(le_abs_self _).trans hb]
      calc (2 / 3 : ℝ) = Real.log (Real.exp (2 / 3)) := (Real.log_exp _).symm
        _ < Real.log 2 := Real.log_lt_log (Real.exp_pos _) h1
    have hexp_le : μ₀ / k - lam * (2 * μ₀) ≤ -(1 / (3 * k)) * μ₀ := by
      have h1 : (1 / k - 2 * Real.log 2 / k) ≤ -(1 / (3 * k)) := by
        have : 1 - 2 * Real.log 2 ≤ -(1 / 3 : ℝ) := by linarith
        calc 1 / k - 2 * Real.log 2 / k = (1 - 2 * Real.log 2) / k := by ring
          _ ≤ (-(1 / 3 : ℝ)) / k := div_le_div_of_nonneg_right this hk.le
          _ = -(1 / (3 * k)) := by ring
      calc μ₀ / k - lam * (2 * μ₀) = (1 / k - 2 * Real.log 2 / k) * μ₀ := by simp only [lam]; ring
        _ ≤ -(1 / (3 * k)) * μ₀ := mul_le_mul_of_nonneg_right h1 hμ₀
    calc (E₁.card : ℝ)
        ≤ Real.exp (μ₀ / k) * (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) /
            Real.exp (lam * (2 * μ₀)) := hcomb
      _ = Real.exp (μ₀ / k - lam * (2 * μ₀)) * (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) := by
          rw [mul_div_right_comm, ← Real.exp_sub]
      _ ≤ Real.exp (-(1 / (3 * k)) * μ₀) * (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp_le) (Nat.cast_nonneg _)
  have him : (Finset.univ.filter (fun ω : X → Fin Q =>
      2 * μ₀ ≤ ∑ x ∈ S, if (ω x).val = 0 then w x else 0)).image eS = E₁ ×ˢ Finset.univ := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      and_true, E₁]
    have hsum_eq : ∀ ω : X → Fin Q,
        (∑ x ∈ S, if (ω x).val = 0 then w x else 0) =
        (∑ s : {x : X // x ∈ S}, if ((eS ω).1 s).val = 0 then w s.1 else 0) := fun ω => by
      rw [← Finset.sum_coe_sort S]; rfl
    constructor
    · rintro ⟨ω, hω, rfl⟩; rwa [← hsum_eq ω]
    · intro hp; refine ⟨eS.symm p, ?_, eS.apply_symm_apply p⟩
      rw [hsum_eq (eS.symm p), eS.apply_symm_apply p]; exact hp
  have hcardE : ((Finset.univ.filter (fun ω : X → Fin Q =>
      2 * μ₀ ≤ ∑ x ∈ S, if (ω x).val = 0 then w x else 0)).card : ℝ) =
      (E₁.card : ℝ) * (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) := by
    have h1 : (Finset.univ.filter (fun ω : X → Fin Q =>
        2 * μ₀ ≤ ∑ x ∈ S, if (ω x).val = 0 then w x else 0)).card =
        E₁.card * Fintype.card ({x : X // x ∉ S} → Fin Q) := by
      rw [← Finset.card_image_of_injective _ eS.injective, him, Finset.card_product, Finset.card_univ]
    exact_mod_cast h1
  have hcardTot : (Fintype.card (X → Fin Q) : ℝ) =
      (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) *
      (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) := by
    have h1 : Fintype.card (X → Fin Q) =
        Fintype.card ({x : X // x ∈ S} → Fin Q) * Fintype.card ({x : X // x ∉ S} → Fin Q) := by
      rw [Fintype.card_congr eS, Fintype.card_prod]
    exact_mod_cast h1
  rw [hcardE, hcardTot]
  calc (E₁.card : ℝ) * (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ)
      ≤ (Real.exp (-(1 / (3 * k)) * μ₀) * (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ)) *
          (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) :=
        mul_le_mul_of_nonneg_right hE₁ (Nat.cast_nonneg _)
    _ = Real.exp (-(1 / (3 * k)) * μ₀) *
          ((Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) *
          (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ)) := by ring

end Concentration

/- ### Section 3: Single Rödl Nibble Round -/

section NibbleRound

def liftH {α : Type*} [DecidableEq α] (H A : Finset (Finset α)) : Finset ↥H :=
  Finset.univ.filter (fun e : ↥H => e.1 ∈ A)

lemma mem_liftH {α : Type*} [DecidableEq α] {H A : Finset (Finset α)} {e : ↥H} :
    e ∈ liftH H A ↔ e.1 ∈ A := by
  simp [liftH]

lemma card_liftH {α : Type*} [DecidableEq α] {H A : Finset (Finset α)} (hA : A ⊆ H) :
    (liftH H A).card = A.card := by
  refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
  · intro e he; exact (Finset.mem_filter.mp he).2
  · intro e₁ _ e₂ _ h; exact Subtype.ext h
  · intro E hE; exact ⟨⟨E, hA hE⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩, rfl⟩

lemma sum_liftH {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {H A : Finset (Finset α)} (hA : A ⊆ H) (g : Finset α → β) :
    ∑ e ∈ liftH H A, g e.1 = ∑ E ∈ A, g E := by
  refine Finset.sum_bij (fun e _ => e.1) ?_ ?_ ?_ ?_
  · intro e he; exact (Finset.mem_filter.mp he).2
  · intro e₁ _ e₂ _ h; exact Subtype.ext h
  · intro E hE; exact ⟨⟨E, hA hE⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩, rfl⟩
  · intro _ _; rfl

lemma liftH_union {α : Type*} [DecidableEq α] (H A B : Finset (Finset α)) :
    liftH H (A ∪ B) = liftH H A ∪ liftH H B := by
  ext e; simp [liftH]

noncomputable def selSet {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {Q : ℕ}
    (ω : ↥H → Fin Q) : Finset (Finset α) :=
  H.filter (fun E => ∃ h : E ∈ H, (ω ⟨E, h⟩).val = 0)

lemma selSet_subset {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {Q : ℕ}
    (ω : ↥H → Fin Q) : selSet ω ⊆ H :=
  Finset.filter_subset _ _

lemma mem_selSet_iff {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {Q : ℕ}
    (ω : ↥H → Fin Q) (e : ↥H) : e.1 ∈ selSet ω ↔ (ω e).val = 0 := by
  simp only [selSet, Finset.mem_filter]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨e.2, e.2, h⟩⟩

lemma selSet_update_of_ne_zero {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {Q : ℕ}
    (ω : ↥H → Fin Q) (e : ↥H) {a b : Fin Q} (ha : a.val ≠ 0) (hb : b.val ≠ 0) :
    selSet (Function.update ω e a) = selSet (Function.update ω e b) := by
  ext E
  simp only [selSet, Finset.mem_filter]
  constructor
  · rintro ⟨hE, _, h0⟩
    refine ⟨hE, hE, ?_⟩
    by_cases he : (⟨E, hE⟩ : ↥H) = e
    · subst he; simp only [Function.update_self] at h0; exact absurd h0 ha
    · simpa only [Function.update_of_ne he] using h0
  · rintro ⟨hE, _, h0⟩
    refine ⟨hE, hE, ?_⟩
    by_cases he : (⟨E, hE⟩ : ↥H) = e
    · subst he; simp only [Function.update_self] at h0; exact absurd h0 hb
    · simpa only [Function.update_of_ne he] using h0

lemma selSet_update_zero {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {Q : ℕ} (hQ : 0 < Q)
    (ω : ↥H → Fin Q) (e : ↥H) {a : Fin Q} (ha : a.val ≠ 0) :
    selSet (Function.update ω e ⟨0, hQ⟩) = insert e.1 (selSet (Function.update ω e a)) := by
  ext E
  simp only [selSet, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hE, _, h0⟩
    by_cases he : (⟨E, hE⟩ : ↥H) = e
    · left; exact congrArg Subtype.val he
    · right; refine ⟨hE, hE, ?_⟩; simpa only [Function.update_of_ne he] using h0
  · rintro (rfl | ⟨hE, _, h0⟩)
    · exact ⟨e.2, e.2, by simp⟩
    · refine ⟨hE, hE, ?_⟩
      by_cases he : (⟨E, hE⟩ : ↥H) = e
      · subst he; simp only [Function.update_self] at h0; exact absurd h0 ha
      · simpa only [Function.update_of_ne he] using h0

lemma abs_card_sub_le {β : Type*} [DecidableEq β] {A B C : Finset β}
    (hAB : A ⊆ B) (hBC : B ⊆ A ∪ C) :
    |(A.card : ℝ) - (B.card : ℝ)| ≤ (C.card : ℝ) := by
  have h1 : A.card ≤ B.card := Finset.card_le_card hAB
  have h2 : B.card ≤ A.card + C.card := (Finset.card_le_card hBC).trans (Finset.card_union_le A C)
  have h1' : (A.card : ℝ) ≤ (B.card : ℝ) := Nat.cast_le.mpr h1
  have h2' : (B.card : ℝ) ≤ (A.card : ℝ) + (C.card : ℝ) := by exact_mod_cast h2
  rw [abs_le]; constructor <;> linarith

lemma avg_forall_ne_zero {X : Type*} [Fintype X] [DecidableEq X]
    (Q : ℕ) (hQ : 0 < Q) (A : Finset X) :
    ((Finset.univ.filter (fun ω : X → Fin Q => ∀ x ∈ A, (ω x).val ≠ 0)).card : ℝ) =
      (1 - 1 / (Q : ℝ)) ^ A.card * (Fintype.card (X → Fin Q) : ℝ) := by
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  let e := splitProdEquiv (α := Fin Q) A
  let z0 : Fin Q := ⟨0, hQ⟩
  let G₁ : Finset ({x : X // x ∈ A} → Fin Q) :=
    Fintype.piFinset (fun _ : {x : X // x ∈ A} => Finset.univ.erase z0)
  have him : (Finset.univ.filter (fun ω : X → Fin Q => ∀ x ∈ A, (ω x).val ≠ 0)).image e =
      G₁ ×ˢ Finset.univ := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      and_true, G₁, Fintype.mem_piFinset, Finset.mem_erase, z0]
    constructor
    · rintro ⟨ω, hω, rfl⟩ s
      exact fun h => hω s.1 s.2 (congrArg Fin.val h)
    · intro hp
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      intro x hx h0
      have hne := hp ⟨x, hx⟩
      have heq : (e.symm p) x = p.1 ⟨x, hx⟩ := by simp [e, splitProdEquiv, hx]
      rw [heq] at h0
      exact hne (Fin.ext h0)
  have hG₁ : G₁.card = (Q - 1) ^ A.card := by
    simp only [G₁, Fintype.card_piFinset, Finset.card_erase_of_mem (Finset.mem_univ z0),
      Finset.card_univ, Fintype.card_fin, Finset.prod_const, Fintype.card_coe]
  have hcA : Fintype.card ({x : X // x ∈ A} → Fin Q) = Q ^ A.card := by simp
  have hcTot : Fintype.card (X → Fin Q) = Q ^ A.card * Fintype.card ({x : X // x ∉ A} → Fin Q) := by
    rw [Fintype.card_congr e, Fintype.card_prod, hcA]
  have hcF : (Finset.univ.filter (fun ω : X → Fin Q => ∀ x ∈ A, (ω x).val ≠ 0)).card =
      (Q - 1) ^ A.card * Fintype.card ({x : X // x ∉ A} → Fin Q) := by
    rw [← Finset.card_image_of_injective _ e.injective, him, Finset.card_product, Finset.card_univ,
      hG₁]
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hrat : (1 - 1 / (Q : ℝ)) ^ A.card * (Q : ℝ) ^ A.card = ((Q - 1 : ℕ) : ℝ) ^ A.card := by
    rw [← mul_pow, Nat.cast_sub (Nat.succ_le_of_lt hQ), Nat.cast_one]
    congr 1
    field_simp
  rw [hcF, hcTot]
  push_cast
  rw [← hrat]
  ring

lemma avg_sum_disjoint_filter {X ι : Type*} [Fintype X] [DecidableEq X] [DecidableEq ι]
    (Q : ℕ) (hQ : 0 < Q) (J : Finset ι) (B : ι → Finset X) :
    (∑ ω : X → Fin Q, ((J.filter (fun j => ∀ x ∈ B j, (ω x).val ≠ 0)).card : ℝ)) /
        (Fintype.card (X → Fin Q) : ℝ) =
      ∑ j ∈ J, (1 - 1 / (Q : ℝ)) ^ (B j).card := by
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hTot_pos : (0 : ℝ) < (Fintype.card (X → Fin Q) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hrew : ∀ ω : X → Fin Q,
      ((J.filter (fun j => ∀ x ∈ B j, (ω x).val ≠ 0)).card : ℝ) =
      ∑ j ∈ J, if ∀ x ∈ B j, (ω x).val ≠ 0 then (1 : ℝ) else 0 := fun ω => by
    rw [Finset.card_filter]; simp
  simp_rw [hrew]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcard : (∑ ω : X → Fin Q, if ∀ x ∈ B j, (ω x).val ≠ 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun ω : X → Fin Q => ∀ x ∈ B j, (ω x).val ≠ 0)).card : ℝ) := by
    rw [Finset.card_filter]; simp
  rw [hcard, avg_forall_ne_zero Q hQ (B j), mul_div_cancel_right₀ _ hTot_pos.ne']

lemma avg_sum_card_filter_zero {X : Type*} [Fintype X] [DecidableEq X]
    (Q : ℕ) (hQ : 0 < Q) (A : Finset X) :
    (∑ ω : X → Fin Q, ((A.filter (fun x => (ω x).val = 0)).card : ℝ)) /
        (Fintype.card (X → Fin Q) : ℝ) =
      (A.card : ℝ) / (Q : ℝ) := by
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hTot_pos : (0 : ℝ) < (Fintype.card (X → Fin Q) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcomp : ∀ ω : X → Fin Q,
      ((A.filter (fun x => (ω x).val = 0)).card : ℝ) =
      (A.card : ℝ) - ((A.filter (fun x => ∀ y ∈ ({x} : Finset X), (ω y).val ≠ 0)).card : ℝ) := by
    intro ω
    have h1 : (A.filter (fun x => (ω x).val = 0)).card +
        (A.filter (fun x => ¬ (ω x).val = 0)).card = A.card :=
      Finset.card_filter_add_card_filter_not _
    have h2 : A.filter (fun x => ∀ y ∈ ({x} : Finset X), (ω y).val ≠ 0) =
        A.filter (fun x => ¬ (ω x).val = 0) := by
      ext x; simp
    rw [h2]
    have h1' : ((A.filter (fun x => (ω x).val = 0)).card : ℝ) +
        ((A.filter (fun x => ¬ (ω x).val = 0)).card : ℝ) = (A.card : ℝ) := by exact_mod_cast h1
    linarith
  simp_rw [hcomp]
  rw [Finset.sum_sub_distrib, sub_div, avg_sum_disjoint_filter Q hQ A (fun x => {x})]
  have hc1 : (∑ _ω : X → Fin Q, (A.card : ℝ)) / (Fintype.card (X → Fin Q) : ℝ) = (A.card : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hTot_pos.ne']
  rw [hc1]
  have hc2 : ∑ x ∈ A, (1 - 1 / (Q : ℝ)) ^ ({x} : Finset X).card =
      (A.card : ℝ) * (1 - 1 / (Q : ℝ)) := by
    simp [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hc2]; ring

/-- In a linear `k`-uniform hypergraph, the number of edges meeting `E.erase v` is exact. -/
lemma card_touching_erase_eq {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (k : ℕ) (hk : 2 ≤ k)
    (hH_unif : ∀ E ∈ H, E.card = k)
    (hH_lin : ∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).card ≤ 1)
    {E : Finset α} (hE : E ∈ H) {v : α} (hv : v ∈ E) :
    ((H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card : ℝ) =
      1 + ∑ w ∈ E.erase v, (((H.filter (fun F => w ∈ F)).card : ℝ) - 1) := by
  have hEr_ne : (E.erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hv, hH_unif E hE]; omega
  let B : α → Finset (Finset α) := fun w => (H.filter (fun F => w ∈ F)).erase E
  have hEq : H.filter (fun F => ((E.erase v) ∩ F).Nonempty) = insert E ((E.erase v).biUnion B) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_biUnion, B]
    constructor
    · rintro ⟨hF, ⟨w, hw⟩⟩
      rw [Finset.mem_inter] at hw
      by_cases hFE : F = E
      · exact Or.inl hFE
      · exact Or.inr ⟨w, hw.1, Finset.mem_erase.mpr ⟨hFE, Finset.mem_filter.mpr ⟨hF, hw.2⟩⟩⟩
    · rintro (rfl | ⟨w, hw, hFB⟩)
      · obtain ⟨w, hw⟩ := hEr_ne
        exact ⟨hE, ⟨w, Finset.mem_inter.mpr ⟨hw, Finset.mem_of_mem_erase hw⟩⟩⟩
      · rcases Finset.mem_erase.mp hFB with ⟨_, hFmem⟩
        rcases Finset.mem_filter.mp hFmem with ⟨hF, hwF⟩
        exact ⟨hF, ⟨w, Finset.mem_inter.mpr ⟨hw, hwF⟩⟩⟩
  have hE_notMem : E ∉ (E.erase v).biUnion B := by
    simp [B]
  have hdisj : ((E.erase v) : Set α).PairwiseDisjoint B := by
    intro w₁ hw₁ w₂ hw₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro F hF₁ hF₂
    simp only [B, Finset.mem_erase, Finset.mem_filter] at hF₁ hF₂
    have hsub : ({w₁, w₂} : Finset α) ⊆ E ∩ F := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx2
      · exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hw₁, hF₁.2.2⟩
      · rw [Finset.mem_singleton.mp hx2]
        exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hw₂, hF₂.2.2⟩
    have h2 : 2 ≤ (E ∩ F).card := by
      calc 2 = ({w₁, w₂} : Finset α).card := (Finset.card_pair hne).symm
        _ ≤ (E ∩ F).card := Finset.card_le_card hsub
    have h1 := hH_lin E hE F hF₁.2.1 (Ne.symm hF₁.1)
    omega
  rw [hEq, Finset.card_insert_of_notMem hE_notMem, Finset.card_biUnion hdisj]
  push_cast
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun w hw => ?_
  have hEmem : E ∈ H.filter (fun F => w ∈ F) :=
    Finset.mem_filter.mpr ⟨hE, Finset.mem_of_mem_erase hw⟩
  have hpos : 1 ≤ (H.filter (fun F => w ∈ F)).card := Finset.card_pos.mpr ⟨E, hEmem⟩
  rw [Finset.card_erase_of_mem hEmem, Nat.cast_sub hpos, Nat.cast_one]

/-- By linearity, at most `F.card` edges containing `v` can meet `F` outside `v`. -/
lemma card_hv_touching_le {α : Type*} [DecidableEq α]
    (H : Finset (Finset α))
    (hH_lin : ∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).card ≤ 1)
    (v : α) (F : Finset α) :
    ((H.filter (fun E => v ∈ E)).filter (fun E => ((E.erase v) ∩ F).Nonempty)).card ≤ F.card := by
  let S := (H.filter (fun E => v ∈ E)).filter (fun E => ((E.erase v) ∩ F).Nonempty)
  let pick : Finset α → α := fun E =>
    if h : ((E.erase v) ∩ F).Nonempty then h.choose else v
  refine Finset.card_le_card_of_injOn pick ?_ ?_
  · intro E hE
    have hne : ((E.erase v) ∩ F).Nonempty := (Finset.mem_filter.mp hE).2
    simp only [pick, dif_pos hne]
    exact (Finset.mem_inter.mp hne.choose_spec).2
  · intro E₁ hE₁ E₂ hE₂ heq
    have hne₁ : ((E₁.erase v) ∩ F).Nonempty := (Finset.mem_filter.mp hE₁).2
    have hne₂ : ((E₂.erase v) ∩ F).Nonempty := (Finset.mem_filter.mp hE₂).2
    have h1 := Finset.mem_filter.mp (Finset.mem_filter.mp hE₁).1
    have h2 := Finset.mem_filter.mp (Finset.mem_filter.mp hE₂).1
    simp only [pick, dif_pos hne₁, dif_pos hne₂] at heq
    set w := hne₁.choose
    have hw₁ : w ∈ E₁.erase v := (Finset.mem_inter.mp hne₁.choose_spec).1
    have hw₂ : w ∈ E₂.erase v := by rw [heq]; exact (Finset.mem_inter.mp hne₂.choose_spec).1
    have hwv : w ≠ v := (Finset.mem_erase.mp hw₁).1
    by_contra hEne
    have hsub : ({w, v} : Finset α) ⊆ E₁ ∩ E₂ := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx2
      · exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hw₁, Finset.mem_of_mem_erase hw₂⟩
      · rw [Finset.mem_singleton.mp hx2]; exact Finset.mem_inter.mpr ⟨h1.2, h2.2⟩
    have hle := hH_lin E₁ h1.1 E₂ h2.1 hEne
    have hge : 2 ≤ (E₁ ∩ E₂).card := by
      calc 2 = ({w, v} : Finset α).card := (Finset.card_pair hwv).symm
        _ ≤ (E₁ ∩ E₂).card := Finset.card_le_card hsub
    omega

/-- Deterministic two-part waste bound for isolated-edge matching inside a random bite `S`. -/
lemma card_wasted_le {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (k : ℕ)
    (hH_unif : ∀ E ∈ H, E.card = k)
    (U_t : Finset α) (S : Finset (Finset α)) (hS_sub : S ⊆ H) :
    let H_U := H.filter (fun E => (E ∩ U_t).Nonempty)
    let M_bite := S.filter (fun E => ∀ F ∈ S, F ≠ E → Disjoint E F)
    let S_U := S ∩ H_U
    let S_out := S \ S_U
    ((U_t ∩ (S.biUnion id \ M_bite.biUnion id)).card : ℝ) ≤
      2 * (k : ℝ) * ((k : ℝ) * (S_U.card : ℝ) - ((S_U.biUnion id).card : ℝ)) +
        (k : ℝ) * ∑ F ∈ S_out, ((F ∩ S_U.biUnion id).card : ℝ) := by
  intro H_U M_bite S_U S_out
  let Over : Finset (Finset α) :=
    S_U.filter (fun E => ∃ E' ∈ S_U, E' ≠ E ∧ (E ∩ E').Nonempty)
  let Isol : Finset (Finset α) := S_U \ Over
  let Hit : Finset (Finset α) :=
    Isol.filter (fun E => ∃ F ∈ S_out, (E ∩ F).Nonempty)
  have hS_U_sub : S_U ⊆ H := Finset.inter_subset_left.trans hS_sub
  have hOver_sub : Over ⊆ H := (Finset.filter_subset _ _).trans hS_U_sub
  have hHit_sub : Hit ⊆ H := ((Finset.filter_subset _ _).trans Finset.sdiff_subset).trans hS_U_sub
  have hcov : U_t ∩ (S.biUnion id \ M_bite.biUnion id) ⊆ Over.biUnion id ∪ Hit.biUnion id := by
    intro u hu
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hu
    rcases hu with ⟨huU, ⟨E, hES, huE⟩, huM⟩
    have hE_HU : E ∈ H_U := Finset.mem_filter.mpr ⟨hS_sub hES, ⟨u, Finset.mem_inter.mpr ⟨huE, huU⟩⟩⟩
    have hE_SU : E ∈ S_U := Finset.mem_inter.mpr ⟨hES, hE_HU⟩
    have hE_notM : E ∉ M_bite := fun hEM => huM ⟨E, hEM, huE⟩
    simp only [M_bite, Finset.mem_filter, hES, true_and, not_forall] at hE_notM
    rcases hE_notM with ⟨F, hFS, hFE, hnd⟩
    have hEF_ne : (E ∩ F).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hnd
    by_cases hE_over : E ∈ Over
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨E, hE_over, huE⟩)
    · have hF_notSU : F ∉ S_U := fun hFSU =>
        hE_over (Finset.mem_filter.mpr ⟨hE_SU, ⟨F, hFSU, hFE, hEF_ne⟩⟩)
      have hF_out : F ∈ S_out := Finset.mem_sdiff.mpr ⟨hFS, hF_notSU⟩
      have hE_isol : E ∈ Isol := Finset.mem_sdiff.mpr ⟨hE_SU, hE_over⟩
      have hE_hit : E ∈ Hit := Finset.mem_filter.mpr ⟨hE_isol, ⟨F, hF_out, hEF_ne⟩⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨E, hE_hit, huE⟩)
  have hbi_le : ∀ A : Finset (Finset α), A ⊆ H → (A.biUnion id).card ≤ k * A.card := by
    intro A hA
    calc (A.biUnion id).card ≤ ∑ E ∈ A, E.card := Finset.card_biUnion_le
      _ = ∑ _E ∈ A, k := Finset.sum_congr rfl fun E hE => hH_unif E (hA hE)
      _ = k * A.card := by simp [mul_comm]
  have hstep1 : (U_t ∩ (S.biUnion id \ M_bite.biUnion id)).card ≤ k * Over.card + k * Hit.card := by
    calc (U_t ∩ (S.biUnion id \ M_bite.biUnion id)).card
        ≤ (Over.biUnion id ∪ Hit.biUnion id).card := Finset.card_le_card hcov
      _ ≤ (Over.biUnion id).card + (Hit.biUnion id).card := Finset.card_union_le _ _
      _ ≤ k * Over.card + k * Hit.card := Nat.add_le_add (hbi_le Over hOver_sub) (hbi_le Hit hHit_sub)
  have hOver_le : (Over.card : ℝ) ≤ 2 * ((k : ℝ) * (S_U.card : ℝ) - ((S_U.biUnion id).card : ℝ)) := by
    let V_SU := S_U.biUnion id
    let W2 := V_SU.filter (fun w => 2 ≤ (S_U.filter (fun E => w ∈ E)).card)
    have hOver_cov : Over ⊆ W2.biUnion (fun w => S_U.filter (fun E => w ∈ E)) := by
      intro E hE
      rcases Finset.mem_filter.mp hE with ⟨hESU, E', hE'SU, hne, ⟨w, hw⟩⟩
      rcases Finset.mem_inter.mp hw with ⟨hwE, hwE'⟩
      have hwV : w ∈ V_SU := Finset.mem_biUnion.mpr ⟨E, hESU, hwE⟩
      have h2 : 2 ≤ (S_U.filter (fun F => w ∈ F)).card := by
        have hpair : ({E, E'} : Finset (Finset α)) ⊆ S_U.filter (fun F => w ∈ F) := by
          intro F hF
          rcases Finset.mem_insert.mp hF with rfl | hF2
          · exact Finset.mem_filter.mpr ⟨hESU, hwE⟩
          · rw [Finset.mem_singleton.mp hF2]; exact Finset.mem_filter.mpr ⟨hE'SU, hwE'⟩
        calc 2 = ({E, E'} : Finset (Finset α)).card := (Finset.card_pair hne.symm).symm
          _ ≤ (S_U.filter (fun F => w ∈ F)).card := Finset.card_le_card hpair
      exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hwV, h2⟩,
        Finset.mem_filter.mpr ⟨hESU, hwE⟩⟩
    have hO_nat : Over.card ≤ 2 * ∑ w ∈ V_SU, ((S_U.filter (fun E => w ∈ E)).card - 1) := by
      calc Over.card
          ≤ (W2.biUnion (fun w => S_U.filter (fun E => w ∈ E))).card := Finset.card_le_card hOver_cov
        _ ≤ ∑ w ∈ W2, (S_U.filter (fun E => w ∈ E)).card := Finset.card_biUnion_le
        _ ≤ ∑ w ∈ W2, 2 * ((S_U.filter (fun E => w ∈ E)).card - 1) := by
            refine Finset.sum_le_sum fun w hw => ?_
            have h2 := (Finset.mem_filter.mp hw).2
            omega
        _ ≤ ∑ w ∈ V_SU, 2 * ((S_U.filter (fun E => w ∈ E)).card - 1) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = 2 * ∑ w ∈ V_SU, ((S_U.filter (fun E => w ∈ E)).card - 1) := by rw [Finset.mul_sum]
    have hsum_deg : ∑ w ∈ V_SU, (S_U.filter (fun E => w ∈ E)).card = k * S_U.card := by
      calc ∑ w ∈ V_SU, (S_U.filter (fun E => w ∈ E)).card
          = ∑ w ∈ V_SU, ∑ E ∈ S_U, if w ∈ E then 1 else 0 := by
            refine Finset.sum_congr rfl fun w _ => by rw [Finset.card_filter]
        _ = ∑ E ∈ S_U, ∑ w ∈ V_SU, if w ∈ E then 1 else 0 := Finset.sum_comm
        _ = ∑ E ∈ S_U, E.card := by
            refine Finset.sum_congr rfl fun E hE => ?_
            have hEV : E ⊆ V_SU := fun w hw => Finset.mem_biUnion.mpr ⟨E, hE, hw⟩
            rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hEV]
        _ = ∑ _E ∈ S_U, k := Finset.sum_congr rfl fun E hE => hH_unif E (hS_U_sub hE)
        _ = k * S_U.card := by simp [mul_comm]
    have hsum_sub : (∑ w ∈ V_SU, ((S_U.filter (fun E => w ∈ E)).card - 1)) + V_SU.card = k * S_U.card := by
      rw [← hsum_deg]
      have h1 : V_SU.card = ∑ _w ∈ V_SU, 1 := by simp
      rw [h1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w hw => ?_
      rcases Finset.mem_biUnion.mp hw with ⟨E, hESU, hwE⟩
      have hpos : 1 ≤ (S_U.filter (fun F => w ∈ F)).card :=
        Finset.card_pos.mpr ⟨E, Finset.mem_filter.mpr ⟨hESU, hwE⟩⟩
      omega
    have hO_nat' : Over.card ≤ 2 * (k * S_U.card - V_SU.card) := by omega
    have hV_le : V_SU.card ≤ k * S_U.card := by omega
    have hO_real : (Over.card : ℝ) ≤ (2 * (k * S_U.card - V_SU.card) : ℕ) := Nat.cast_le.mpr hO_nat'
    push_cast [Nat.cast_sub hV_le] at hO_real
    exact hO_real
  have hHit_le : Hit.card ≤ ∑ F ∈ S_out, (F ∩ S_U.biUnion id).card := by
    have hHit_cov : Hit ⊆ S_out.biUnion (fun F => Isol.filter (fun E => (E ∩ F).Nonempty)) := by
      intro E hE
      rcases Finset.mem_filter.mp hE with ⟨hE_isol, F, hF_out, hne⟩
      exact Finset.mem_biUnion.mpr ⟨F, hF_out, Finset.mem_filter.mpr ⟨hE_isol, hne⟩⟩
    calc Hit.card
        ≤ (S_out.biUnion (fun F => Isol.filter (fun E => (E ∩ F).Nonempty))).card :=
          Finset.card_le_card hHit_cov
      _ ≤ ∑ F ∈ S_out, (Isol.filter (fun E => (E ∩ F).Nonempty)).card := Finset.card_biUnion_le
      _ ≤ ∑ F ∈ S_out, (F ∩ S_U.biUnion id).card := by
          refine Finset.sum_le_sum fun F _ => ?_
          set A := Isol.filter (fun E => (E ∩ F).Nonempty)
          by_cases hA : A.Nonempty
          · obtain ⟨E₀, hE₀⟩ := hA
            have hne₀ : (E₀ ∩ F).Nonempty := (Finset.mem_filter.mp hE₀).2
            let w₀ := hne₀.choose
            let pick : Finset α → α := fun E =>
              if h : (E ∩ F).Nonempty then h.choose else w₀
            refine Finset.card_le_card_of_injOn pick ?_ ?_
            · intro E hE
              rcases Finset.mem_filter.mp hE with ⟨hE_isol, hne⟩
              have hE_SU : E ∈ S_U := (Finset.mem_sdiff.mp hE_isol).1
              simp only [pick, dif_pos hne]
              rcases Finset.mem_inter.mp hne.choose_spec with ⟨hwE, hwF⟩
              exact Finset.mem_inter.mpr ⟨hwF, Finset.mem_biUnion.mpr ⟨E, hE_SU, hwE⟩⟩
            · intro E₁ hE₁ E₂ hE₂ heq
              rcases Finset.mem_filter.mp hE₁ with ⟨hE₁_isol, hne₁⟩
              rcases Finset.mem_filter.mp hE₂ with ⟨hE₂_isol, hne₂⟩
              simp only [pick, dif_pos hne₁, dif_pos hne₂] at heq
              by_contra hneE
              have hE₁_notOver : E₁ ∉ Over := (Finset.mem_sdiff.mp hE₁_isol).2
              have hE₁_SU : E₁ ∈ S_U := (Finset.mem_sdiff.mp hE₁_isol).1
              have hE₂_SU : E₂ ∈ S_U := (Finset.mem_sdiff.mp hE₂_isol).1
              have hw1 : hne₁.choose ∈ E₁ := (Finset.mem_inter.mp hne₁.choose_spec).1
              have hw2 : hne₁.choose ∈ E₂ := by rw [heq]; exact (Finset.mem_inter.mp hne₂.choose_spec).1
              exact hE₁_notOver (Finset.mem_filter.mpr
                ⟨hE₁_SU, ⟨E₂, hE₂_SU, Ne.symm hneE, ⟨hne₁.choose, Finset.mem_inter.mpr ⟨hw1, hw2⟩⟩⟩⟩)
          · rw [Finset.not_nonempty_iff_eq_empty.mp hA]; simp
  have hstep1' : ((U_t ∩ (S.biUnion id \ M_bite.biUnion id)).card : ℝ) ≤
      (k : ℝ) * (Over.card : ℝ) + (k : ℝ) * (Hit.card : ℝ) := by exact_mod_cast hstep1
  have hHit_le' : (Hit.card : ℝ) ≤ ∑ F ∈ S_out, ((F ∩ S_U.biUnion id).card : ℝ) := by
    exact_mod_cast hHit_le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

/-- Conditional weighted Chernoff bound for cross-intersections `S_out` hitting `V(S_U)`. -/
lemma card_cross_bad_le {α : Type*} [DecidableEq α]
    (H H_U H_U2 : Finset (Finset α)) (Q : ℕ) (hQ : 0 < Q)
    (_hH_U : H_U ⊆ H) (hH_U2 : H_U2 ⊆ H) (hdisj : Disjoint H_U H_U2)
    (k B_size μ₀ : ℝ) (hk : 0 < k) (hμ₀ : 0 ≤ μ₀)
    (hF_card : ∀ F ∈ H_U2, (F.card : ℝ) ≤ k)
    (hmean : ∀ S_U : Finset (Finset α), S_U ⊆ H_U → (S_U.card : ℝ) ≤ B_size →
      (∑ F ∈ H_U2, ((F ∩ S_U.biUnion id).card : ℝ)) / (Q : ℝ) ≤ μ₀) :
    ((Finset.univ.filter (fun ω : ↥H → Fin Q =>
        ((selSet ω ∩ H_U).card : ℝ) ≤ B_size ∧
        2 * μ₀ ≤ ∑ F ∈ selSet ω ∩ H_U2, ((F ∩ (selSet ω ∩ H_U).biUnion id).card : ℝ))).card : ℝ) ≤
      Real.exp (-(1 / (3 * k)) * μ₀) * (Fintype.card (↥H → Fin Q) : ℝ) := by
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  let a₀ : Fin Q := ⟨0, hQ⟩
  let L₁ : Finset ↥H := liftH H H_U
  let e := splitProdEquiv (α := Fin Q) L₁
  let SU : ({x : ↥H // x ∈ L₁} → Fin Q) → Finset (Finset α) :=
    fun τ => selSet (e.symm (τ, fun _ => a₀)) ∩ H_U
  have hSU_eq : ∀ ω : ↥H → Fin Q, selSet ω ∩ H_U = SU (e ω).1 := by
    intro ω
    ext E
    simp only [SU, Finset.mem_inter, selSet, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hE, _, h0⟩, hEU⟩
      have hx : (⟨E, hE⟩ : ↥H) ∈ L₁ := mem_liftH.mpr hEU
      refine ⟨⟨hE, hE, ?_⟩, hEU⟩
      simpa [e, splitProdEquiv, hx] using h0
    · rintro ⟨⟨hE, _, h0⟩, hEU⟩
      have hx : (⟨E, hE⟩ : ↥H) ∈ L₁ := mem_liftH.mpr hEU
      refine ⟨⟨hE, hE, ?_⟩, hEU⟩
      simpa [e, splitProdEquiv, hx] using h0
  let A₂ : Finset {x : ↥H // x ∉ L₁} := Finset.univ.filter (fun y => y.1.1 ∈ H_U2)
  have hsum_A₂ : ∀ (ω : ↥H → Fin Q) (V : Finset α),
      ∑ F ∈ selSet ω ∩ H_U2, ((F ∩ V).card : ℝ) =
      ∑ y ∈ A₂, if ((e ω).2 y).val = 0 then ((y.1.1 ∩ V).card : ℝ) else 0 := by
    intro ω V
    rw [← Finset.sum_filter]
    refine (Finset.sum_bij (fun y _ => y.1.1) ?_ ?_ ?_ ?_).symm
    · intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyA, h0⟩
      have hy2 : y.1.1 ∈ H_U2 := (Finset.mem_filter.mp hyA).2
      exact Finset.mem_inter.mpr ⟨(mem_selSet_iff ω y.1).mpr h0, hy2⟩
    · intro y₁ _ y₂ _ h
      exact Subtype.ext (Subtype.ext h)
    · intro F hF
      rcases Finset.mem_inter.mp hF with ⟨hFS, hF2⟩
      have hFH : F ∈ H := hH_U2 hF2
      have hnotL₁ : (⟨F, hFH⟩ : ↥H) ∉ L₁ := by
        rw [mem_liftH]; exact Finset.disjoint_right.mp hdisj hF2
      let y : {x : ↥H // x ∉ L₁} := ⟨⟨F, hFH⟩, hnotL₁⟩
      have hyA : y ∈ A₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF2⟩
      have h0 : ((e ω).2 y).val = 0 := (mem_selSet_iff ω ⟨F, hFH⟩).mp hFS
      exact ⟨y, Finset.mem_filter.mpr ⟨hyA, h0⟩, rfl⟩
    · intro _ _; rfl
  have hsum_full : ∀ V : Finset α,
      ∑ y ∈ A₂, ((y.1.1 ∩ V).card : ℝ) = ∑ F ∈ H_U2, ((F ∩ V).card : ℝ) := by
    intro V
    refine Finset.sum_bij (fun y _ => y.1.1) ?_ ?_ ?_ ?_
    · intro y hy; exact (Finset.mem_filter.mp hy).2
    · intro y₁ _ y₂ _ h; exact Subtype.ext (Subtype.ext h)
    · intro F hF
      have hFH : F ∈ H := hH_U2 hF
      have hnotL₁ : (⟨F, hFH⟩ : ↥H) ∉ L₁ := by
        rw [mem_liftH]; exact Finset.disjoint_right.mp hdisj hF
      exact ⟨⟨⟨F, hFH⟩, hnotL₁⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF⟩, rfl⟩
    · intro _ _; rfl
  let E_bad : Finset (↥H → Fin Q) := Finset.univ.filter (fun ω : ↥H → Fin Q =>
    ((selSet ω ∩ H_U).card : ℝ) ≤ B_size ∧
    2 * μ₀ ≤ ∑ F ∈ selSet ω ∩ H_U2, ((F ∩ (selSet ω ∩ H_U).biUnion id).card : ℝ))
  have hcard_split : (E_bad.card : ℝ) =
      ∑ τ : {x : ↥H // x ∈ L₁} → Fin Q,
        ((Finset.univ.filter (fun σ : {x : ↥H // x ∉ L₁} → Fin Q =>
          ((SU τ).card : ℝ) ≤ B_size ∧
          2 * μ₀ ≤ ∑ y ∈ A₂, if (σ y).val = 0 then ((y.1.1 ∩ (SU τ).biUnion id).card : ℝ) else 0)).card : ℝ) := by
    have h1 : (E_bad.card : ℝ) = ∑ ω : ↥H → Fin Q, if ω ∈ E_bad then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]; simp
    rw [h1, ← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hiff : e.symm (τ, σ) ∈ E_bad ↔
        ((SU τ).card : ℝ) ≤ B_size ∧
        2 * μ₀ ≤ ∑ y ∈ A₂, if (σ y).val = 0 then ((y.1.1 ∩ (SU τ).biUnion id).card : ℝ) else 0 := by
      simp only [E_bad, Finset.mem_filter, Finset.mem_univ, true_and]
      have hSU' : selSet (e.symm (τ, σ)) ∩ H_U = SU τ := by
        rw [hSU_eq, e.apply_symm_apply]
      rw [hSU', hsum_A₂ (e.symm (τ, σ)) ((SU τ).biUnion id)]
      have h2 : (e (e.symm (τ, σ))).2 = σ := by rw [e.apply_symm_apply]
      rw [h2]
    by_cases h : e.symm (τ, σ) ∈ E_bad
    · simp [h, hiff.mp h]
    · simp [h, mt hiff.mpr h]
  have hslice : ∀ τ : {x : ↥H // x ∈ L₁} → Fin Q,
      ((Finset.univ.filter (fun σ : {x : ↥H // x ∉ L₁} → Fin Q =>
        ((SU τ).card : ℝ) ≤ B_size ∧
        2 * μ₀ ≤ ∑ y ∈ A₂, if (σ y).val = 0 then ((y.1.1 ∩ (SU τ).biUnion id).card : ℝ) else 0)).card : ℝ) ≤
      Real.exp (-(1 / (3 * k)) * μ₀) * (Fintype.card ({x : ↥H // x ∉ L₁} → Fin Q) : ℝ) := by
    intro τ
    by_cases hB : ((SU τ).card : ℝ) ≤ B_size
    · have hfilt : Finset.univ.filter (fun σ : {x : ↥H // x ∉ L₁} → Fin Q =>
          ((SU τ).card : ℝ) ≤ B_size ∧
          2 * μ₀ ≤ ∑ y ∈ A₂, if (σ y).val = 0 then ((y.1.1 ∩ (SU τ).biUnion id).card : ℝ) else 0) =
          Finset.univ.filter (fun σ : {x : ↥H // x ∉ L₁} → Fin Q =>
          2 * μ₀ ≤ ∑ y ∈ A₂, if (σ y).val = 0 then ((y.1.1 ∩ (SU τ).biUnion id).card : ℝ) else 0) := by
        ext σ; simp [hB]
      rw [hfilt]
      refine weighted_chernoff_sub Q hQ A₂
        (fun y => ((y.1.1 ∩ (SU τ).biUnion id).card : ℝ)) k μ₀ hk hμ₀
        (fun _ _ => Nat.cast_nonneg _)
        (fun y hy => by
          have hy2 : y.1.1 ∈ H_U2 := (Finset.mem_filter.mp hy).2
          have hle : ((y.1.1 ∩ (SU τ).biUnion id).card : ℝ) ≤ (y.1.1.card : ℝ) :=
            Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
          exact hle.trans (hF_card y.1.1 hy2))
        (by
          rw [hsum_full]
          exact hmean (SU τ) Finset.inter_subset_right hB)
    · have hempty : Finset.univ.filter (fun σ : {x : ↥H // x ∉ L₁} → Fin Q =>
          ((SU τ).card : ℝ) ≤ B_size ∧
          2 * μ₀ ≤ ∑ y ∈ A₂, if (σ y).val = 0 then ((y.1.1 ∩ (SU τ).biUnion id).card : ℝ) else 0) = ∅ := by
        ext σ; simp [hB]
      rw [hempty]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hcardTot : (Fintype.card (↥H → Fin Q) : ℝ) =
      (Fintype.card ({x : ↥H // x ∈ L₁} → Fin Q) : ℝ) *
      (Fintype.card ({x : ↥H // x ∉ L₁} → Fin Q) : ℝ) := by
    have h1 : Fintype.card (↥H → Fin Q) =
        Fintype.card ({x : ↥H // x ∈ L₁} → Fin Q) * Fintype.card ({x : ↥H // x ∉ L₁} → Fin Q) := by
      rw [Fintype.card_congr e, Fintype.card_prod]
    exact_mod_cast h1
  rw [hcard_split, hcardTot]
  calc ∑ τ : {x : ↥H // x ∈ L₁} → Fin Q,
        ((Finset.univ.filter (fun σ : {x : ↥H // x ∉ L₁} → Fin Q =>
          ((SU τ).card : ℝ) ≤ B_size ∧
          2 * μ₀ ≤ ∑ y ∈ A₂, if (σ y).val = 0 then ((y.1.1 ∩ (SU τ).biUnion id).card : ℝ) else 0)).card : ℝ)
      ≤ ∑ _τ : {x : ↥H // x ∈ L₁} → Fin Q,
          Real.exp (-(1 / (3 * k)) * μ₀) * (Fintype.card ({x : ↥H // x ∉ L₁} → Fin Q) : ℝ) :=
        Finset.sum_le_sum fun τ _ => hslice τ
    _ = Real.exp (-(1 / (3 * k)) * μ₀) *
          ((Fintype.card ({x : ↥H // x ∈ L₁} → Fin Q) : ℝ) *
          (Fintype.card ({x : ↥H // x ∉ L₁} → Fin Q) : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

def depV {α : Type*} [DecidableEq α] (H : Finset (Finset α)) (v : α) : Finset (Finset α) :=
  H.filter (fun F => ∃ E ∈ H.filter (fun E => v ∈ E), ((E.erase v) ∩ F).Nonempty)

lemma depV_subset {α : Type*} [DecidableEq α] (H : Finset (Finset α)) (v : α) :
    depV H v ⊆ H := Finset.filter_subset _ _

def depU {α : Type*} [DecidableEq α] (H : Finset (Finset α)) (W U : Finset α) : Finset (Finset α) :=
  let H_U := H.filter (fun E => (E ∩ (U ∩ W)).Nonempty)
  let H_U2 := (H \ H_U).filter (fun F => ∃ E ∈ H_U, (E ∩ F).Nonempty)
  H_U ∪ H_U2

noncomputable def degBad {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (Q : ℕ) (Dt1 η : ℝ) (v : α) : Finset (↥H → Fin Q) :=
  let H_v := H.filter (fun E => v ∈ E)
  let f : (↥H → Fin Q) → ℝ := fun ω =>
    ((H_v.filter (fun E => Disjoint (E.erase v) ((selSet ω).biUnion id))).card : ℝ)
  let μ : ℝ := (∑ ω : ↥H → Fin Q, f ω) / (Fintype.card (↥H → Fin Q) : ℝ)
  Finset.univ.filter (fun ω : ↥H → Fin Q => η * Dt1 ≤ |f ω - μ|)

/-- Concentration and expectation bounds for vertex degrees in one nibble round. -/
lemma deg_bad_bound {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (k Q : ℕ)
    (Dt ε δ η : ℝ)
    (hk : 4 ≤ k) (hQ : 0 < Q)
    (hH_sub : ∀ E ∈ H, E ⊆ W)
    (hH_unif : ∀ E ∈ H, E.card = k)
    (hH_lin : ∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).card ≤ 1)
    (hε0 : 0 < ε) (hε_small : 4 * (k : ℝ) * ε ≤ 1 / 4)
    (hδ0 : 0 ≤ δ) (hδ_small : δ ≤ 1 / 40)
    (hη0 : 0 < η) (hη_small : η ≤ ε ^ 2)
    (hDt_pos : 0 < Dt) (hDt_err : 4 * (k : ℝ) * ε / Dt ≤ η)
    (hp_hi : 1 / (Q : ℝ) ≤ ε / Dt)
    (hp_lo : ε / Dt - ε ^ 2 / Dt ^ 2 ≤ 1 / (Q : ℝ))
    (hdeg_lo : ∀ v ∈ W, (1 - δ) * Dt ≤ ((H.filter (fun E => v ∈ E)).card : ℝ))
    (hdeg_hi : ∀ v ∈ W, ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ (1 + δ) * Dt)
    (v : α) (hv : v ∈ W) :
    let Dt1 := Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Dt
    DependsOn (liftH H (depV H v)) (degBad H Q Dt1 η v) ∧
    ((degBad H Q Dt1 η v).card : ℝ) ≤
      2 * Real.exp (-(η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) ∧
    (∀ ω : ↥H → Fin Q, ω ∉ degBad H Q Dt1 η v →
      v ∈ W \ (selSet ω).biUnion id →
      let H' := H.filter (fun E => E ⊆ W \ (selSet ω).biUnion id)
      (1 - (δ * (1 + 3 * (k : ℝ) * ε) + 2 * η)) * Dt1 ≤
        ((H'.filter (fun E => v ∈ E)).card : ℝ) ∧
      ((H'.filter (fun E => v ∈ E)).card : ℝ) ≤
        (1 + (δ * (1 + 3 * (k : ℝ) * ε) + 2 * η)) * Dt1) := by
  intro Dt1
  let H_v := H.filter (fun E => v ∈ E)
  let f : (↥H → Fin Q) → ℝ := fun ω =>
    ((H_v.filter (fun E => Disjoint (E.erase v) ((selSet ω).biUnion id))).card : ℝ)
  let μ : ℝ := (∑ ω : ↥H → Fin Q, f ω) / (Fintype.card (↥H → Fin Q) : ℝ)
  have hk_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk1_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hε_le1 : ε ≤ 1 / 16 := by nlinarith
  have hη_leε : η ≤ ε := hη_small.trans (by nlinarith)
  have hp_nn : (0 : ℝ) ≤ 1 / (Q : ℝ) := by positivity
  have hp_half : 1 / (Q : ℝ) ≤ 1 / 2 := by
    have h1 : ε / Dt ≤ η / (4 * (k : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ))]
      calc ε / Dt * (4 * (k : ℝ)) = 4 * (k : ℝ) * ε / Dt := by ring
        _ ≤ η := hDt_err
    have h2 : η / (4 * (k : ℝ)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ))]; nlinarith
    exact hp_hi.trans (h1.trans h2)
  have hDt1_pos : 0 < Dt1 := mul_pos (Real.exp_pos _) hDt_pos
  have hDt1_half : Dt / 2 ≤ Dt1 := by
    have hexp : (1 / 2 : ℝ) ≤ Real.exp (-((k - 1 : ℕ) : ℝ) * ε) := by
      have h1 := Real.add_one_le_exp (-((k - 1 : ℕ) : ℝ) * ε)
      rw [hk1_cast] at h1 ⊢; nlinarith
    calc Dt / 2 = (1 / 2 : ℝ) * Dt := by ring
      _ ≤ Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Dt := mul_le_mul_of_nonneg_right hexp hDt_pos.le
  -- Dependence of `f` on `liftH H (depV H v)`
  have hf_dep : ∀ ω₁ ω₂ : ↥H → Fin Q,
      (∀ e ∈ liftH H (depV H v), ω₁ e = ω₂ e) → f ω₁ = f ω₂ := by
    intro ω₁ ω₂ hagree
    simp only [f]
    congr 2
    ext E
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hEHv
    have hdisj_iff : ∀ ω : ↥H → Fin Q,
        Disjoint (E.erase v) ((selSet ω).biUnion id) ↔
        ∀ F ∈ H.filter (fun F => ((E.erase v) ∩ F).Nonempty),
          ∀ hF : F ∈ H, (ω ⟨F, hF⟩).val ≠ 0 := by
      intro ω
      rw [Finset.disjoint_biUnion_right]
      constructor
      · intro h F hF hFH h0
        rcases Finset.mem_filter.mp hF with ⟨_, hne⟩
        have hFS : F ∈ selSet ω := (mem_selSet_iff ω ⟨F, hFH⟩).mpr h0
        exact Finset.not_disjoint_iff_nonempty_inter.mpr hne (h F hFS)
      · intro h F hFS
        by_contra hnd
        have hFH : F ∈ H := selSet_subset ω hFS
        have hne : ((E.erase v) ∩ F).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hnd
        exact h F (Finset.mem_filter.mpr ⟨hFH, hne⟩) hFH ((mem_selSet_iff ω ⟨F, hFH⟩).mp hFS)
    rw [hdisj_iff ω₁, hdisj_iff ω₂]
    refine forall_congr' fun F => forall_congr' fun hF => forall_congr' fun hFH => ?_
    have hFdep : F ∈ depV H v :=
      Finset.mem_filter.mpr ⟨hFH, ⟨E, hEHv, (Finset.mem_filter.mp hF).2⟩⟩
    rw [hagree ⟨F, hFH⟩ (mem_liftH.mpr hFdep)]
  have hDep : DependsOn (liftH H (depV H v)) (degBad H Q Dt1 η v) := by
    intro ω₁ ω₂ hagree
    simp only [degBad, Finset.mem_filter, Finset.mem_univ, true_and]
    change η * Dt1 ≤ |f ω₁ - μ| ↔ η * Dt1 ≤ |f ω₂ - μ|
    rw [hf_dep ω₁ ω₂ hagree]
  -- Size of `depV H v`
  have hAE_bounds : ∀ E ∈ H_v,
      ((k - 1 : ℕ) : ℝ) * (1 - δ) * Dt - (k : ℝ) ≤
        ((H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card : ℝ) ∧
      ((H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * (1 + δ) * Dt := by
    intro E hE
    rcases Finset.mem_filter.mp hE with ⟨hEH, hvE⟩
    rw [card_touching_erase_eq H k (by omega) hH_unif hH_lin hEH hvE]
    have hcard_er : ((E.erase v).card : ℝ) = ((k - 1 : ℕ) : ℝ) := by
      rw [Finset.card_erase_of_mem hvE, hH_unif E hEH]
    have hlo : ∑ w ∈ E.erase v, (((H.filter (fun F => w ∈ F)).card : ℝ) - 1) ≥
        ((k - 1 : ℕ) : ℝ) * ((1 - δ) * Dt - 1) := by
      calc ∑ w ∈ E.erase v, (((H.filter (fun F => w ∈ F)).card : ℝ) - 1)
          ≥ ∑ _w ∈ E.erase v, ((1 - δ) * Dt - 1) :=
            Finset.sum_le_sum fun w hw => by
              linarith [hdeg_lo w (hH_sub E hEH (Finset.mem_of_mem_erase hw))]
        _ = ((k - 1 : ℕ) : ℝ) * ((1 - δ) * Dt - 1) := by
            simp [Finset.sum_const, nsmul_eq_mul, hcard_er]; ring
    have hhi : ∑ w ∈ E.erase v, (((H.filter (fun F => w ∈ F)).card : ℝ) - 1) ≤
        ((k - 1 : ℕ) : ℝ) * ((1 + δ) * Dt - 1) := by
      calc ∑ w ∈ E.erase v, (((H.filter (fun F => w ∈ F)).card : ℝ) - 1)
          ≤ ∑ _w ∈ E.erase v, ((1 + δ) * Dt - 1) :=
            Finset.sum_le_sum fun w hw => by
              linarith [hdeg_hi w (hH_sub E hEH (Finset.mem_of_mem_erase hw))]
        _ = ((k - 1 : ℕ) : ℝ) * ((1 + δ) * Dt - 1) := by
            simp [Finset.sum_const, nsmul_eq_mul, hcard_er]; ring
    rw [hk1_cast] at hlo hhi ⊢
    constructor <;> linarith
  have hdepV_card : ((depV H v).card : ℝ) ≤ 2 * (k : ℝ) * Dt ^ 2 := by
    have hsub : depV H v ⊆ H_v.biUnion (fun E => H.filter (fun F => ((E.erase v) ∩ F).Nonempty)) := by
      intro F hF
      rcases Finset.mem_filter.mp hF with ⟨hFH, E, hEHv, hne⟩
      exact Finset.mem_biUnion.mpr ⟨E, hEHv, Finset.mem_filter.mpr ⟨hFH, hne⟩⟩
    have h1 : ((depV H v).card : ℝ) ≤
        ∑ E ∈ H_v, ((H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∑ E ∈ H_v, ((H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card : ℝ) ≤
        (H_v.card : ℝ) * (((k - 1 : ℕ) : ℝ) * (1 + δ) * Dt) := by
      calc ∑ E ∈ H_v, ((H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card : ℝ)
          ≤ ∑ _E ∈ H_v, (((k - 1 : ℕ) : ℝ) * (1 + δ) * Dt) :=
            Finset.sum_le_sum fun E hE => (hAE_bounds E hE).2
        _ = (H_v.card : ℝ) * (((k - 1 : ℕ) : ℝ) * (1 + δ) * Dt) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have hHv : (H_v.card : ℝ) ≤ (1 + δ) * Dt := hdeg_hi v hv
    have hk1_le : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by rw [hk1_cast]; linarith
    have hsq : (1 + δ) ^ 2 ≤ 2 := by nlinarith only [hδ0, hδ_small]
    calc ((depV H v).card : ℝ)
        ≤ (H_v.card : ℝ) * (((k - 1 : ℕ) : ℝ) * (1 + δ) * Dt) := h1.trans h2
      _ ≤ ((1 + δ) * Dt) * ((k : ℝ) * (1 + δ) * Dt) := by
          refine mul_le_mul hHv ?_ (by positivity) (by positivity)
          have h3 : ((k - 1 : ℕ) : ℝ) * ((1 + δ) * Dt) ≤ (k : ℝ) * ((1 + δ) * Dt) :=
            mul_le_mul_of_nonneg_right hk1_le (by positivity)
          linarith
      _ = (1 + δ) ^ 2 * ((k : ℝ) * Dt ^ 2) := by ring
      _ ≤ 2 * ((k : ℝ) * Dt ^ 2) := mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 2 * (k : ℝ) * Dt ^ 2 := by ring
  -- McDiarmid bound for `degBad`
  have hProb : ((degBad H Q Dt1 η v).card : ℝ) ≤
      2 * Real.exp (-(η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) := by
    have hmcd := bernoulli_mcdiarmid_sub Q hQ (liftH H (depV H v))
      (fun _ => (k : ℝ)) f (k : ℝ) (2 * (k : ℝ) ^ 3 * ε * Dt) (η * Dt1)
      hk_pos (by positivity) (mul_pos hη0 hDt1_pos)
      (fun _ _ => hk_pos.le) (fun _ _ => le_rfl)
      (by
        rw [Finset.sum_const, nsmul_eq_mul, card_liftH (depV_subset H v)]
        calc ((depV H v).card : ℝ) * (k : ℝ) ^ 2 / (Q : ℝ)
            = ((depV H v).card : ℝ) * (k : ℝ) ^ 2 * (1 / (Q : ℝ)) := by ring
          _ ≤ (2 * (k : ℝ) * Dt ^ 2) * (k : ℝ) ^ 2 * (ε / Dt) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right hdepV_card (sq_nonneg _)) hp_hi
                hp_nn (by positivity)
          _ = 2 * (k : ℝ) ^ 3 * ε * Dt := by field_simp)
      hf_dep
      (fun e _ ω a b ha hb => by
        simp only [f, selSet_update_of_ne_zero ω e ha hb])
      (fun e _ ω a ha => by
        simp only [f]
        have hS1 := selSet_update_zero hQ ω e ha
        set S₀ := selSet (Function.update ω e a)
        set A₁ := H_v.filter (fun E => Disjoint (E.erase v) ((insert e.1 S₀).biUnion id))
        set A₀ := H_v.filter (fun E => Disjoint (E.erase v) (S₀.biUnion id))
        set C := H_v.filter (fun E => ((E.erase v) ∩ e.1).Nonempty)
        rw [hS1]
        have hsub1 : A₁ ⊆ A₀ := by
          intro E hE
          rcases Finset.mem_filter.mp hE with ⟨hEHv, hd⟩
          refine Finset.mem_filter.mpr ⟨hEHv, hd.mono_right ?_⟩
          exact Finset.biUnion_subset_biUnion_of_subset_left id (Finset.subset_insert e.1 S₀)
        have hsub2 : A₀ ⊆ A₁ ∪ C := by
          intro E hE
          rcases Finset.mem_filter.mp hE with ⟨hEHv, hd⟩
          by_cases ht : ((E.erase v) ∩ e.1).Nonempty
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hEHv, ht⟩)
          · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hEHv, ?_⟩)
            rw [Finset.biUnion_insert, id_eq, Finset.disjoint_union_right]
            exact ⟨Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp ht), hd⟩
        have hC : (C.card : ℝ) ≤ (k : ℝ) := by
          have h1 : C.card ≤ e.1.card := card_hv_touching_le H hH_lin v e.1
          rw [hH_unif e.1 e.2] at h1
          exact_mod_cast h1
        exact (abs_card_sub_le hsub1 hsub2).trans hC)
    refine hmcd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)) (Nat.cast_nonneg _))
    rw [neg_mul, neg_le_neg_iff]
    refine le_min ?_ ?_
    · have h1 : (η * (Dt / 2)) ^ 2 ≤ (η * Dt1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hDt1_half hη0.le) 2
      calc (η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt
          = (η * (Dt / 2)) ^ 2 / (4 * (2 * (k : ℝ) ^ 3 * ε * Dt)) := by field_simp; ring
        _ ≤ (η * Dt1) ^ 2 / (4 * (2 * (k : ℝ) ^ 3 * ε * Dt)) :=
            div_le_div_of_nonneg_right h1 (by positivity)
    · have h1 : η * (Dt / 2) ≤ η * Dt1 := mul_le_mul_of_nonneg_left hDt1_half hη0.le
      calc (η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt
          ≤ (η / (4 * (k : ℝ))) * Dt := by
            refine mul_le_mul_of_nonneg_right ?_ hDt_pos.le
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk_real]
            have hk3 : 4 * (k : ℝ) ≤ 32 * (k : ℝ) ^ 3 := by nlinarith only [hk_real, hk2]
            calc η ^ 2 * (4 * (k : ℝ)) = η * (η * (4 * (k : ℝ))) := by ring
              _ ≤ η * (ε * (32 * (k : ℝ) ^ 3)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul hη_leε hk3 (by positivity) hε0.le) hη0.le
              _ = η * (32 * (k : ℝ) ^ 3 * ε) := by ring
        _ = (η * (Dt / 2)) / (2 * (k : ℝ)) := by ring
        _ ≤ (η * Dt1) / (2 * (k : ℝ)) := div_le_div_of_nonneg_right h1 (by positivity)
  -- Exact expectation `μ` and good-event degree bounds
  have hμ_formula : μ = ∑ E ∈ H_v, (1 - 1 / (Q : ℝ)) ^
      (H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card := by
    have hf_rew : ∀ ω : ↥H → Fin Q,
        f ω = ((H_v.filter (fun E => ∀ e ∈ liftH H (H.filter (fun F => ((E.erase v) ∩ F).Nonempty)),
          (ω e).val ≠ 0)).card : ℝ) := by
      intro ω
      simp only [f]
      congr 2
      ext E
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _
      rw [Finset.disjoint_biUnion_right]
      constructor
      · intro h e he h0
        have hF := (Finset.mem_filter.mp (mem_liftH.mp he)).2
        exact Finset.not_disjoint_iff_nonempty_inter.mpr hF (h e.1 ((mem_selSet_iff ω e).mpr h0))
      · intro h F hFS
        by_contra hnd
        have hFH : F ∈ H := selSet_subset ω hFS
        have hne := Finset.not_disjoint_iff_nonempty_inter.mp hnd
        exact h ⟨F, hFH⟩ (mem_liftH.mpr (Finset.mem_filter.mpr ⟨hFH, hne⟩))
          ((mem_selSet_iff ω ⟨F, hFH⟩).mp hFS)
    simp only [μ]
    simp_rw [hf_rew]
    rw [avg_sum_disjoint_filter Q hQ H_v (fun E => liftH H (H.filter (fun F => ((E.erase v) ∩ F).Nonempty)))]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [card_liftH (Finset.filter_subset _ _)]
  have hμ_hi : μ ≤ (1 + δ * (1 + 3 * (k : ℝ) * ε) + η) * Dt1 := by
    let a : ℝ := ((k - 1 : ℕ) : ℝ) * δ * ε + 2 * (k : ℝ) * ε / Dt
    have ha_nn : 0 ≤ a := by positivity
    have hk1_le : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by rw [hk1_cast]; linarith
    have ha_le : a ≤ 1 / 4 := by
      have h1 : ((k - 1 : ℕ) : ℝ) * δ * ε ≤ (1 / 4) * (1 / 40) := by
        have hkε : ((k - 1 : ℕ) : ℝ) * ε ≤ 1 / 4 := by
          nlinarith only [hk1_le, hε0, hε_small]
        nlinarith only [hkε, hδ0, hδ_small]
      have h2 : 2 * (k : ℝ) * ε / Dt ≤ η / 2 := by
        have : 2 * (k : ℝ) * ε / Dt = (4 * (k : ℝ) * ε / Dt) / 2 := by ring
        linarith only [this, hDt_err]
      linarith only [h1, h2, hη_leε, hε_le1]
    have hterm : ∀ E ∈ H_v, (1 - 1 / (Q : ℝ)) ^
        (H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card ≤
        Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Real.exp a := by
      intro E hE
      set m := (H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card
      have h1 : (1 - 1 / (Q : ℝ)) ^ m ≤ Real.exp (-(1 / (Q : ℝ)) * (m : ℝ)) := by
        calc (1 - 1 / (Q : ℝ)) ^ m
            ≤ (Real.exp (-(1 / (Q : ℝ)))) ^ m :=
              pow_le_pow_left₀ (by linarith only [hp_half])
                (by linarith [Real.add_one_le_exp (-(1 / (Q : ℝ)))]) m
          _ = Real.exp ((m : ℝ) * (-(1 / (Q : ℝ)))) := (Real.exp_nat_mul _ m).symm
          _ = Real.exp (-(1 / (Q : ℝ)) * (m : ℝ)) := by ring_nf
      refine h1.trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm_lo : ((k - 1 : ℕ) : ℝ) * (1 - δ) * Dt - (k : ℝ) ≤ (m : ℝ) := (hAE_bounds E hE).1
      have hpm : ((k - 1 : ℕ) : ℝ) * ε - a ≤ (1 / (Q : ℝ)) * (m : ℝ) := by
        have hA : (1 / (Q : ℝ)) * (((k - 1 : ℕ) : ℝ) * (1 - δ) * Dt - (k : ℝ)) ≤
            (1 / (Q : ℝ)) * (m : ℝ) := mul_le_mul_of_nonneg_left hm_lo hp_nn
        rw [mul_sub] at hA
        have hB : (ε / Dt - ε ^ 2 / Dt ^ 2) * (((k - 1 : ℕ) : ℝ) * (1 - δ) * Dt) ≤
            (1 / (Q : ℝ)) * (((k - 1 : ℕ) : ℝ) * (1 - δ) * Dt) :=
          mul_le_mul_of_nonneg_right hp_lo
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith only [hδ_small])) hDt_pos.le)
        have hC : (1 / (Q : ℝ)) * (k : ℝ) ≤ (ε / Dt) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right hp_hi hk_pos.le
        have hsimp : (ε / Dt - ε ^ 2 / Dt ^ 2) * (((k - 1 : ℕ) : ℝ) * (1 - δ) * Dt) =
            ((k - 1 : ℕ) : ℝ) * (1 - δ) * ε - ((k - 1 : ℕ) : ℝ) * (1 - δ) * ε ^ 2 / Dt := by
          field_simp
        have hsq_le : ((k - 1 : ℕ) : ℝ) * (1 - δ) * ε ^ 2 / Dt ≤ (k : ℝ) * ε / Dt := by
          refine div_le_div_of_nonneg_right ?_ hDt_pos.le
          have h1dε : (1 - δ) * ε ≤ 1 := by nlinarith only [hδ0, hδ_small, hε0, hε_le1]
          calc ((k - 1 : ℕ) : ℝ) * (1 - δ) * ε ^ 2
              = (((k - 1 : ℕ) : ℝ) * ((1 - δ) * ε)) * ε := by ring
            _ ≤ ((k : ℝ) * 1) * ε :=
                mul_le_mul_of_nonneg_right (mul_le_mul hk1_le h1dε
                  (mul_nonneg (by linarith only [hδ_small]) hε0.le) hk_pos.le) hε0.le
            _ = (k : ℝ) * ε := by ring
        have hC' : (ε / Dt) * (k : ℝ) = (k : ℝ) * ε / Dt := by ring
        have hexp1 : ((k - 1 : ℕ) : ℝ) * (1 - δ) * ε =
            ((k - 1 : ℕ) : ℝ) * ε - ((k - 1 : ℕ) : ℝ) * δ * ε := by ring
        have h2k : 2 * (k : ℝ) * ε / Dt = (k : ℝ) * ε / Dt + (k : ℝ) * ε / Dt := by ring
        dsimp [a]
        linarith only [hA, hB, hC, hC', hsimp, hexp1, hsq_le, h2k]
      linarith only [hpm]
    have hexp_a : Real.exp a ≤ 1 + (5 / 4 : ℝ) * a := by
      have h1 := exp_sub_one_sub_le_sq (x := a) (by rw [abs_of_nonneg ha_nn]; linarith only [ha_le])
      nlinarith only [h1, ha_nn, ha_le]
    calc μ
        ≤ ∑ _E ∈ H_v, (Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Real.exp a) := by
          rw [hμ_formula]; exact Finset.sum_le_sum hterm
      _ = (H_v.card : ℝ) * Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Real.exp a := by
          simp [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ((1 + δ) * Dt) * Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * (1 + (5 / 4 : ℝ) * a) := by
          have hHv := hdeg_hi v hv
          have h1 : (H_v.card : ℝ) * Real.exp (-((k - 1 : ℕ) : ℝ) * ε) ≤
              ((1 + δ) * Dt) * Real.exp (-((k - 1 : ℕ) : ℝ) * ε) :=
            mul_le_mul_of_nonneg_right hHv (Real.exp_pos _).le
          exact mul_le_mul h1 hexp_a (Real.exp_pos _).le (by positivity)
      _ = ((1 + δ) * (1 + (5 / 4 : ℝ) * a)) * Dt1 := by simp only [Dt1]; ring
      _ ≤ (1 + δ * (1 + 3 * (k : ℝ) * ε) + η) * Dt1 := by
          refine mul_le_mul_of_nonneg_right ?_ hDt1_pos.le
          dsimp [a]
          have h1 : (1 + δ) * ((5 / 4 : ℝ) * (((k - 1 : ℕ) : ℝ) * δ * ε)) ≤ 3 * (k : ℝ) * ε * δ := by
            have hc1 : (1 + δ) * (5 / 4 : ℝ) ≤ 3 := by linarith only [hδ_small]
            calc (1 + δ) * ((5 / 4 : ℝ) * (((k - 1 : ℕ) : ℝ) * δ * ε))
                = ((1 + δ) * (5 / 4 : ℝ)) * (((k - 1 : ℕ) : ℝ) * (ε * δ)) := by ring
              _ ≤ 3 * ((k : ℝ) * (ε * δ)) :=
                  mul_le_mul hc1 (mul_le_mul_of_nonneg_right hk1_le (mul_nonneg hε0.le hδ0))
                    (by positivity) (by norm_num)
              _ = 3 * (k : ℝ) * ε * δ := by ring
          have h2 : (1 + δ) * ((5 / 4 : ℝ) * (2 * (k : ℝ) * ε / Dt)) ≤ η := by
            have hc2 : (1 + δ) * (5 / 4 : ℝ) * 2 ≤ 4 := by linarith only [hδ_small]
            calc (1 + δ) * ((5 / 4 : ℝ) * (2 * (k : ℝ) * ε / Dt))
                = ((1 + δ) * (5 / 4 : ℝ) * 2) * ((k : ℝ) * ε / Dt) := by ring
              _ ≤ 4 * ((k : ℝ) * ε / Dt) := mul_le_mul_of_nonneg_right hc2 (by positivity)
              _ = 4 * (k : ℝ) * ε / Dt := by ring
              _ ≤ η := hDt_err
          linarith only [h1, h2]
  have hμ_lo : (1 - δ * (1 + 3 * (k : ℝ) * ε) - η) * Dt1 ≤ μ := by
    let b : ℝ := ((k - 1 : ℕ) : ℝ) * δ * ε + ((k - 1 : ℕ) : ℝ) * (1 + δ) * ε ^ 2 / Dt
    have hb_nn : 0 ≤ b := by positivity
    have hk1_le : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by rw [hk1_cast]; linarith
    have hterm : ∀ E ∈ H_v,
        Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Real.exp (-b) ≤
        (1 - 1 / (Q : ℝ)) ^ (H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card := by
      intro E hE
      set m := (H.filter (fun F => ((E.erase v) ∩ F).Nonempty)).card
      have h1 : Real.exp (-(1 / (Q : ℝ) + (1 / (Q : ℝ)) ^ 2) * (m : ℝ)) ≤ (1 - 1 / (Q : ℝ)) ^ m := by
        have hstep := one_sub_ge_exp_neg_sub_sq hp_nn hp_half
        calc Real.exp (-(1 / (Q : ℝ) + (1 / (Q : ℝ)) ^ 2) * (m : ℝ))
            = Real.exp ((m : ℝ) * (-(1 / (Q : ℝ)) - (1 / (Q : ℝ)) ^ 2)) := by congr 1; ring
          _ = (Real.exp (-(1 / (Q : ℝ)) - (1 / (Q : ℝ)) ^ 2)) ^ m := Real.exp_nat_mul _ m
          _ ≤ (1 - 1 / (Q : ℝ)) ^ m := pow_le_pow_left₀ (Real.exp_pos _).le hstep m
      refine le_trans ?_ h1
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm_hi : (m : ℝ) ≤ ((k - 1 : ℕ) : ℝ) * (1 + δ) * Dt := (hAE_bounds E hE).2
      have hp_sq : (1 / (Q : ℝ)) ^ 2 ≤ (ε / Dt) ^ 2 :=
        pow_le_pow_left₀ hp_nn hp_hi 2
      have hprod : (1 / (Q : ℝ) + (1 / (Q : ℝ)) ^ 2) * (m : ℝ) ≤
          ((k - 1 : ℕ) : ℝ) * ε + b := by
        calc (1 / (Q : ℝ) + (1 / (Q : ℝ)) ^ 2) * (m : ℝ)
            ≤ (ε / Dt + (ε / Dt) ^ 2) * (((k - 1 : ℕ) : ℝ) * (1 + δ) * Dt) :=
              mul_le_mul (by linarith only [hp_hi, hp_sq]) hm_hi (Nat.cast_nonneg _) (by positivity)
          _ = ((k - 1 : ℕ) : ℝ) * ε + b := by dsimp [b]; field_simp; ring
      linarith only [hprod]
    have hexp_b : 1 - b ≤ Real.exp (-b) := by linarith [Real.add_one_le_exp (-b)]
    have hb2 : ((k - 1 : ℕ) : ℝ) * (1 + δ) * ε ^ 2 / Dt ≤ η := by
      have hnum : ((k - 1 : ℕ) : ℝ) * (1 + δ) * ε ^ 2 ≤ 4 * (k : ℝ) * ε := by
        have hc : (1 + δ) * ε ≤ 4 := by nlinarith only [hδ_small, hε0, hε_le1]
        calc ((k - 1 : ℕ) : ℝ) * (1 + δ) * ε ^ 2
            = (((k - 1 : ℕ) : ℝ) * ((1 + δ) * ε)) * ε := by ring
          _ ≤ ((k : ℝ) * 4) * ε :=
              mul_le_mul_of_nonneg_right (mul_le_mul hk1_le hc (by positivity) hk_pos.le) hε0.le
          _ = 4 * (k : ℝ) * ε := by ring
      exact (div_le_div_of_nonneg_right hnum hDt_pos.le).trans hDt_err
    have hcoeff : 1 - δ * (1 + 3 * (k : ℝ) * ε) - η ≤ (1 - δ) * (1 - b) := by
      have h1 : ((k - 1 : ℕ) : ℝ) * δ * ε ≤ 3 * (k : ℝ) * ε * δ := by
        calc ((k - 1 : ℕ) : ℝ) * δ * ε = ((k - 1 : ℕ) : ℝ) * (ε * δ) := by ring
          _ ≤ (3 * (k : ℝ)) * (ε * δ) :=
              mul_le_mul_of_nonneg_right (by linarith only [hk1_le, hk_pos]) (mul_nonneg hε0.le hδ0)
          _ = 3 * (k : ℝ) * ε * δ := by ring
      have hbd : 0 ≤ δ * b := mul_nonneg hδ0 hb_nn
      dsimp [b] at h1 hb2 hbd ⊢
      linarith only [h1, hb2, hbd]
    have h1b_nn : 0 ≤ 1 - b := by
      have h1 : ((k - 1 : ℕ) : ℝ) * δ * ε ≤ 1 / 10 := by
        have hkε : ((k - 1 : ℕ) : ℝ) * ε ≤ 1 / 4 := by nlinarith only [hk1_le, hε0, hε_small]
        nlinarith only [hkε, hδ0, hδ_small]
      dsimp [b]
      linarith only [h1, hb2, hη_leε, hε_le1]
    calc (1 - δ * (1 + 3 * (k : ℝ) * ε) - η) * Dt1
        ≤ ((1 - δ) * (1 - b)) * Dt1 := mul_le_mul_of_nonneg_right hcoeff hDt1_pos.le
      _ = ((1 - δ) * Dt) * Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * (1 - b) := by simp only [Dt1]; ring
      _ ≤ (H_v.card : ℝ) * Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Real.exp (-b) := by
          have h1 : ((1 - δ) * Dt) * Real.exp (-((k - 1 : ℕ) : ℝ) * ε) ≤
              (H_v.card : ℝ) * Real.exp (-((k - 1 : ℕ) : ℝ) * ε) :=
            mul_le_mul_of_nonneg_right (hdeg_lo v hv) (Real.exp_pos _).le
          exact mul_le_mul h1 hexp_b h1b_nn (by positivity)
      _ = ∑ _E ∈ H_v, (Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Real.exp (-b)) := by
          simp [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ μ := by rw [hμ_formula]; exact Finset.sum_le_sum hterm
  refine ⟨hDep, hProb, fun ω hgood hv' => ?_⟩
  intro H'
  have hlt : |f ω - μ| < η * Dt1 := by
    simp only [degBad, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hgood
    exact hgood
  have hcard_eq : ((H'.filter (fun E => v ∈ E)).card : ℝ) = f ω := by
    simp only [f]
    congr 2
    ext E
    simp only [H', H_v, Finset.mem_filter]
    have hv_notS : v ∉ (selSet ω).biUnion id := (Finset.mem_sdiff.mp hv').2
    constructor
    · rintro ⟨⟨hEH, hEW'⟩, hvE⟩
      refine ⟨⟨hEH, hvE⟩, Finset.disjoint_left.mpr fun w hw hwS => ?_⟩
      exact (Finset.mem_sdiff.mp (hEW' (Finset.mem_of_mem_erase hw))).2 hwS
    · rintro ⟨⟨hEH, hvE⟩, hdisj⟩
      refine ⟨⟨hEH, fun w hwE => Finset.mem_sdiff.mpr ⟨hH_sub E hEH hwE, ?_⟩⟩, hvE⟩
      by_cases hwv : w = v
      · subst hwv; exact hv_notS
      · exact Finset.disjoint_left.mp hdisj (Finset.mem_erase.mpr ⟨hwv, hwE⟩)
  rw [hcard_eq]
  rcases abs_lt.mp hlt with ⟨hlo, hhi⟩
  constructor <;> linarith

noncomputable def biteMatch {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {Q : ℕ}
    (ω : ↥H → Fin Q) : Finset (Finset α) :=
  (selSet ω).filter (fun E => ∀ F ∈ selSet ω, F ≠ E → Disjoint E F)

noncomputable def survBad {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (Q D : ℕ) (η : ℝ) (U : Finset α) :
    Finset (↥H → Fin Q) :=
  let U_t := U ∩ W
  let f : (↥H → Fin Q) → ℝ := fun ω => ((U_t \ (selSet ω).biUnion id).card : ℝ)
  let μ : ℝ := (∑ ω : ↥H → Fin Q, f ω) / (Fintype.card (↥H → Fin Q) : ℝ)
  Finset.univ.filter (fun ω : ↥H → Fin Q => η * (D : ℝ) ≤ |f ω - μ|)

noncomputable def sizeBad {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (Q D : ℕ) (η : ℝ) (U : Finset α) :
    Finset (↥H → Fin Q) :=
  let H_U := H.filter (fun E => (E ∩ (U ∩ W)).Nonempty)
  let f : (↥H → Fin Q) → ℝ := fun ω => ((selSet ω ∩ H_U).card : ℝ)
  let μ : ℝ := (∑ ω : ↥H → Fin Q, f ω) / (Fintype.card (↥H → Fin Q) : ℝ)
  Finset.univ.filter (fun ω : ↥H → Fin Q => η * (D : ℝ) ≤ |f ω - μ|)

noncomputable def spanBad {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (Q D : ℕ) (η : ℝ) (U : Finset α) :
    Finset (↥H → Fin Q) :=
  let H_U := H.filter (fun E => (E ∩ (U ∩ W)).Nonempty)
  let f : (↥H → Fin Q) → ℝ := fun ω => (((selSet ω ∩ H_U).biUnion id).card : ℝ)
  let μ : ℝ := (∑ ω : ↥H → Fin Q, f ω) / (Fintype.card (↥H → Fin Q) : ℝ)
  Finset.univ.filter (fun ω : ↥H → Fin Q => η * (D : ℝ) ≤ |f ω - μ|)

noncomputable def crossBad {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (k Q D : ℕ) (ε : ℝ) (U : Finset α) :
    Finset (↥H → Fin Q) :=
  let H_U := H.filter (fun E => (E ∩ (U ∩ W)).Nonempty)
  let H_U2 := (H \ H_U).filter (fun F => ∃ E ∈ H_U, (E ∩ F).Nonempty)
  Finset.univ.filter (fun ω : ↥H → Fin Q =>
    ((selSet ω ∩ H_U).card : ℝ) ≤ 3 * ε * (D : ℝ) ∧
    12 * (k : ℝ) * ε ^ 2 * (D : ℝ) ≤
      ∑ F ∈ selSet ω ∩ H_U2, ((F ∩ (selSet ω ∩ H_U).biUnion id).card : ℝ))

noncomputable def targetBad {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (k Q D : ℕ) (ε η : ℝ) (U : Finset α) :
    Finset (↥H → Fin Q) :=
  survBad W H Q D η U ∪ sizeBad W H Q D η U ∪ spanBad W H Q D η U ∪ crossBad W H k Q D ε U

lemma selSet_inter_agree {α : Type*} [DecidableEq α] {H A : Finset (Finset α)} {Q : ℕ}
    (ω₁ ω₂ : ↥H → Fin Q) (hag : ∀ e ∈ liftH H A, ω₁ e = ω₂ e) :
    selSet ω₁ ∩ A = selSet ω₂ ∩ A := by
  ext E
  simp only [Finset.mem_inter, selSet, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hEH, _, h0⟩, hEA⟩
    exact ⟨⟨hEH, hEH, by rw [← hag ⟨E, hEH⟩ (mem_liftH.mpr hEA)]; exact h0⟩, hEA⟩
  · rintro ⟨⟨hEH, _, h0⟩, hEA⟩
    exact ⟨⟨hEH, hEH, by rw [hag ⟨E, hEH⟩ (mem_liftH.mpr hEA)]; exact h0⟩, hEA⟩

lemma card_HU_bounds {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (Q D : ℕ) (Dt ε δ : ℝ)
    (hD : 1 ≤ D) (hε0 : 0 < ε) (hδ0 : 0 ≤ δ) (hδ_small : δ ≤ 1 / 40)
    (hDt_pos : 0 < Dt) (hp_hi : 1 / (Q : ℝ) ≤ ε / Dt)
    (hdeg_hi : ∀ v ∈ W, ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ (1 + δ) * Dt)
    (U : Finset α) (hUt_leD : ((U ∩ W).card : ℝ) ≤ (D : ℝ)) :
    let H_U := H.filter (fun E => (E ∩ (U ∩ W)).Nonempty)
    (H_U.card : ℝ) ≤ (1 + δ) * (D : ℝ) * Dt ∧ (H_U.card : ℝ) / (Q : ℝ) ≤ 2 * ε * (D : ℝ) := by
  intro H_U
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  have hHU_card : (H_U.card : ℝ) ≤ (1 + δ) * (D : ℝ) * Dt := by
    have hsub : H_U ⊆ (U ∩ W).biUnion (fun u => H.filter (fun E => u ∈ E)) := by
      intro E hE
      rcases Finset.mem_filter.mp hE with ⟨hEH, ⟨u, hu⟩⟩
      rcases Finset.mem_inter.mp hu with ⟨huE, huUt⟩
      exact Finset.mem_biUnion.mpr ⟨u, huUt, Finset.mem_filter.mpr ⟨hEH, huE⟩⟩
    have h1 : (H_U.card : ℝ) ≤ ∑ u ∈ U ∩ W, ((H.filter (fun E => u ∈ E)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    calc (H_U.card : ℝ)
        ≤ ∑ _u ∈ U ∩ W, ((1 + δ) * Dt) :=
          h1.trans (Finset.sum_le_sum fun u hu => hdeg_hi u (Finset.mem_inter.mp hu).2)
      _ = ((U ∩ W).card : ℝ) * ((1 + δ) * Dt) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (D : ℝ) * ((1 + δ) * Dt) := mul_le_mul_of_nonneg_right hUt_leD (by positivity)
      _ = (1 + δ) * (D : ℝ) * Dt := by ring
  refine ⟨hHU_card, ?_⟩
  have hp_nn : (0 : ℝ) ≤ 1 / (Q : ℝ) := by positivity
  calc (H_U.card : ℝ) / (Q : ℝ) = (H_U.card : ℝ) * (1 / (Q : ℝ)) := by ring
    _ ≤ ((1 + δ) * (D : ℝ) * Dt) * (ε / Dt) := mul_le_mul hHU_card hp_hi hp_nn (by positivity)
    _ = (1 + δ) * (ε * (D : ℝ)) := by field_simp
    _ ≤ 2 * (ε * (D : ℝ)) := mul_le_mul_of_nonneg_right (by linarith only [hδ_small]) (by positivity)
    _ = 2 * ε * (D : ℝ) := by ring

lemma c_exp_le_lin {k D : ℕ} {Dt ε η : ℝ}
    (hk : 4 ≤ k) (hD : 1 ≤ D) (hε0 : 0 < ε) (hη0 : 0 < η) (hη_leε : η ≤ ε) (hDt_le : Dt ≤ (D : ℝ)) :
    (η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt ≤ η * (D : ℝ) / (2 * (k : ℝ)) := by
  have hk_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk_real]
  have hk3 : 2 * (k : ℝ) ≤ 32 * (k : ℝ) ^ 3 := by nlinarith only [hk_real, hk2]
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  calc (η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt
      ≤ (η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * (D : ℝ) := mul_le_mul_of_nonneg_left hDt_le (by positivity)
    _ ≤ (η / (2 * (k : ℝ))) * (D : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hD_pos.le
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc η ^ 2 * (2 * (k : ℝ)) = η * (η * (2 * (k : ℝ))) := by ring
          _ ≤ η * (ε * (32 * (k : ℝ) ^ 3)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hη_leε hk3 (by positivity) hε0.le) hη0.le
          _ = η * (32 * (k : ℝ) ^ 3 * ε) := by ring
    _ = η * (D : ℝ) / (2 * (k : ℝ)) := by ring

lemma target_surv_size_prob {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (k Q D : ℕ) (Dt ε δ η : ℝ)
    (hk : 4 ≤ k) (hQ : 0 < Q) (hD : 1 ≤ D)
    (hH_unif : ∀ E ∈ H, E.card = k)
    (hε0 : 0 < ε) (hδ0 : 0 ≤ δ) (hδ_small : δ ≤ 1 / 40)
    (hη0 : 0 < η) (hη_leε : η ≤ ε)
    (hDt_pos : 0 < Dt) (hDt_le : Dt ≤ (D : ℝ))
    (hp_hi : 1 / (Q : ℝ) ≤ ε / Dt)
    (hdeg_hi : ∀ v ∈ W, ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ (1 + δ) * Dt)
    (U : Finset α) (hUt_leD : ((U ∩ W).card : ℝ) ≤ (D : ℝ)) :
    let c_exp : ℝ := η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)
    DependsOn (liftH H (depU H W U)) (survBad W H Q D η U) ∧
    DependsOn (liftH H (depU H W U)) (sizeBad W H Q D η U) ∧
    ((survBad W H Q D η U).card : ℝ) ≤ 2 * Real.exp (-c_exp * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) ∧
    ((sizeBad W H Q D η U).card : ℝ) ≤ 2 * Real.exp (-c_exp * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) := by
  intro c_exp
  let U_t := U ∩ W
  let H_U := H.filter (fun E => (E ∩ U_t).Nonempty)
  let f_surv : (↥H → Fin Q) → ℝ := fun ω => ((U_t \ (selSet ω).biUnion id).card : ℝ)
  let f_size : (↥H → Fin Q) → ℝ := fun ω => ((selSet ω ∩ H_U).card : ℝ)
  have hk_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk_real]
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp_nn : (0 : ℝ) ≤ 1 / (Q : ℝ) := by positivity
  have hH_U_sub : H_U ⊆ H := Finset.filter_subset _ _
  have hHU_b := card_HU_bounds W H Q D Dt ε δ hD hε0 hδ0 hδ_small hDt_pos hp_hi hdeg_hi U hUt_leD
  have hc_lin := c_exp_le_lin hk hD hε0 hη0 hη_leε hDt_le
  have hsub1 : liftH H H_U ⊆ liftH H (depU H W U) := by
    rw [depU, liftH_union]; exact Finset.subset_union_left
  have hf_surv_dep : ∀ ω₁ ω₂ : ↥H → Fin Q,
      (∀ e ∈ liftH H H_U, ω₁ e = ω₂ e) → f_surv ω₁ = f_surv ω₂ := by
    intro ω₁ ω₂ hag
    have hEq := selSet_inter_agree ω₁ ω₂ hag
    simp only [f_surv]; congr 2; ext u
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, id_eq, and_congr_right_iff]
    intro hu
    have hrew : ∀ ω : ↥H → Fin Q, (∃ E ∈ selSet ω, u ∈ E) ↔ (∃ E ∈ selSet ω ∩ H_U, u ∈ E) := fun ω =>
      ⟨fun ⟨E, hES, huE⟩ => ⟨E, Finset.mem_inter.mpr ⟨hES, Finset.mem_filter.mpr
        ⟨selSet_subset ω hES, ⟨u, Finset.mem_inter.mpr ⟨huE, hu⟩⟩⟩⟩, huE⟩,
       fun ⟨E, hE, huE⟩ => ⟨E, (Finset.mem_inter.mp hE).1, huE⟩⟩
    rw [hrew ω₁, hrew ω₂, hEq]
  have hf_size_dep : ∀ ω₁ ω₂ : ↥H → Fin Q,
      (∀ e ∈ liftH H H_U, ω₁ e = ω₂ e) → f_size ω₁ = f_size ω₂ := by
    intro ω₁ ω₂ hag; simp only [f_size, selSet_inter_agree ω₁ ω₂ hag]
  have hd1 : DependsOn (liftH H (depU H W U)) (survBad W H Q D η U) :=
    dependsOn_mono hsub1 fun ω₁ ω₂ hag => by
      simp only [survBad, Finset.mem_filter, Finset.mem_univ, true_and]
      change η * (D : ℝ) ≤ |f_surv ω₁ - _| ↔ η * (D : ℝ) ≤ |f_surv ω₂ - _|
      rw [hf_surv_dep ω₁ ω₂ hag]
  have hd2 : DependsOn (liftH H (depU H W U)) (sizeBad W H Q D η U) :=
    dependsOn_mono hsub1 fun ω₁ ω₂ hag => by
      simp only [sizeBad, Finset.mem_filter, Finset.mem_univ, true_and]
      change η * (D : ℝ) ≤ |f_size ω₁ - _| ↔ η * (D : ℝ) ≤ |f_size ω₂ - _|
      rw [hf_size_dep ω₁ ω₂ hag]
  have hP_surv : ((survBad W H Q D η U).card : ℝ) ≤
      2 * Real.exp (-c_exp * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) := by
    have hV : (∑ e ∈ liftH H H_U, ((e.1 ∩ U_t).card : ℝ) ^ 2) / (Q : ℝ) ≤
        2 * (k : ℝ) * ε * (D : ℝ) := by
      rw [sum_liftH hH_U_sub (fun E => ((E ∩ U_t).card : ℝ) ^ 2)]
      have hsum1 : ∑ E ∈ H_U, ((E ∩ U_t).card : ℝ) ^ 2 ≤
          (k : ℝ) * ∑ E ∈ H_U, ((E ∩ U_t).card : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun E hE => ?_
        have hle : ((E ∩ U_t).card : ℝ) ≤ (k : ℝ) := by
          have : (E ∩ U_t).card ≤ E.card := Finset.card_le_card Finset.inter_subset_left
          rw [hH_unif E (hH_U_sub hE)] at this; exact_mod_cast this
        have hnn : (0 : ℝ) ≤ ((E ∩ U_t).card : ℝ) := Nat.cast_nonneg _
        nlinarith only [hle, hnn]
      have hsum2 : ∑ E ∈ H_U, ((E ∩ U_t).card : ℝ) ≤ (1 + δ) * (D : ℝ) * Dt := by
        have hnat : ∑ E ∈ H_U, (E ∩ U_t).card = ∑ u ∈ U_t, (H_U.filter (fun E => u ∈ E)).card := by
          calc ∑ E ∈ H_U, (E ∩ U_t).card
              = ∑ E ∈ H_U, ∑ u ∈ U_t, if u ∈ E then 1 else 0 := by
                refine Finset.sum_congr rfl fun E _ => ?_
                rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
            _ = ∑ u ∈ U_t, ∑ E ∈ H_U, if u ∈ E then 1 else 0 := Finset.sum_comm
            _ = ∑ u ∈ U_t, (H_U.filter (fun E => u ∈ E)).card := by
                refine Finset.sum_congr rfl fun u _ => by rw [Finset.card_filter]
        have hcast : ∑ E ∈ H_U, ((E ∩ U_t).card : ℝ) =
            ∑ u ∈ U_t, ((H_U.filter (fun E => u ∈ E)).card : ℝ) := by exact_mod_cast hnat
        rw [hcast]
        calc ∑ u ∈ U_t, ((H_U.filter (fun E => u ∈ E)).card : ℝ)
            ≤ ∑ u ∈ U_t, ((H.filter (fun E => u ∈ E)).card : ℝ) :=
              Finset.sum_le_sum fun u _ =>
                Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hH_U_sub))
          _ ≤ ∑ _u ∈ U_t, ((1 + δ) * Dt) :=
              Finset.sum_le_sum fun u hu => hdeg_hi u (Finset.mem_inter.mp hu).2
          _ = (U_t.card : ℝ) * ((1 + δ) * Dt) := by simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (D : ℝ) * ((1 + δ) * Dt) := mul_le_mul_of_nonneg_right hUt_leD (by positivity)
          _ = (1 + δ) * (D : ℝ) * Dt := by ring
      calc (∑ E ∈ H_U, ((E ∩ U_t).card : ℝ) ^ 2) / (Q : ℝ)
          = (∑ E ∈ H_U, ((E ∩ U_t).card : ℝ) ^ 2) * (1 / (Q : ℝ)) := by ring
        _ ≤ ((k : ℝ) * ((1 + δ) * (D : ℝ) * Dt)) * (ε / Dt) :=
            mul_le_mul (hsum1.trans (mul_le_mul_of_nonneg_left hsum2 hk_pos.le)) hp_hi hp_nn (by positivity)
        _ = (1 + δ) * ((k : ℝ) * ε * (D : ℝ)) := by field_simp
        _ ≤ 2 * ((k : ℝ) * ε * (D : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith only [hδ_small]) (by positivity)
        _ = 2 * (k : ℝ) * ε * (D : ℝ) := by ring
    have hmcd := bernoulli_mcdiarmid_sub Q hQ (liftH H H_U)
      (fun e => ((e.1 ∩ U_t).card : ℝ)) f_surv (k : ℝ) (2 * (k : ℝ) * ε * (D : ℝ)) (η * (D : ℝ))
      hk_pos (by positivity) (mul_pos hη0 hD_pos)
      (fun _ _ => Nat.cast_nonneg _)
      (fun e _ => by
        have h1 : (e.1 ∩ U_t).card ≤ e.1.card := Finset.card_le_card Finset.inter_subset_left
        rw [hH_unif e.1 e.2] at h1; exact_mod_cast h1)
      hV hf_surv_dep
      (fun e _ ω a b ha hb => by simp only [f_surv, selSet_update_of_ne_zero ω e ha hb])
      (fun e _ ω a ha => by
        simp only [f_surv, selSet_update_zero hQ ω e ha]
        set S₀ := selSet (Function.update ω e a)
        have hsub1' : U_t \ (insert e.1 S₀).biUnion id ⊆ U_t \ S₀.biUnion id :=
          Finset.sdiff_subset_sdiff Subset.rfl
            (Finset.biUnion_subset_biUnion_of_subset_left id (Finset.subset_insert e.1 S₀))
        have hsub2' : U_t \ S₀.biUnion id ⊆ (U_t \ (insert e.1 S₀).biUnion id) ∪ (e.1 ∩ U_t) := by
          intro u hu
          rcases Finset.mem_sdiff.mp hu with ⟨huU, huS₀⟩
          by_cases hue : u ∈ e.1
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hue, huU⟩)
          · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨huU, ?_⟩)
            rw [Finset.biUnion_insert, id_eq, Finset.mem_union]; tauto
        exact abs_card_sub_le hsub1' hsub2')
    refine hmcd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)) (Nat.cast_nonneg _))
    rw [neg_mul, neg_le_neg_iff]
    refine le_min ?_ hc_lin
    calc c_exp * Dt
        ≤ c_exp * (D : ℝ) := mul_le_mul_of_nonneg_left hDt_le (by positivity)
      _ ≤ (η ^ 2 / (8 * (k : ℝ) * ε)) * (D : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hD_pos.le
          dsimp [c_exp]
          refine div_le_div_of_nonneg_left (sq_nonneg η) (by positivity) ?_
          have hk3 : 8 * (k : ℝ) ≤ 32 * (k : ℝ) ^ 3 := by nlinarith only [hk_real, hk2]
          exact mul_le_mul_of_nonneg_right hk3 hε0.le
      _ = (η * (D : ℝ)) ^ 2 / (4 * (2 * (k : ℝ) * ε * (D : ℝ))) := by field_simp; ring
  have hP_size : ((sizeBad W H Q D η U).card : ℝ) ≤
      2 * Real.exp (-c_exp * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) := by
    have hmcd := bernoulli_mcdiarmid_sub Q hQ (liftH H H_U)
      (fun _ => (1 : ℝ)) f_size (k : ℝ) (2 * ε * (D : ℝ)) (η * (D : ℝ))
      hk_pos (by positivity) (mul_pos hη0 hD_pos)
      (fun _ _ => by norm_num) (fun _ _ => by linarith only [hk_real])
      (by rw [Finset.sum_const, nsmul_eq_mul, card_liftH hH_U_sub]; simpa using hHU_b.2)
      hf_size_dep
      (fun e _ ω a b ha hb => by simp only [f_size, selSet_update_of_ne_zero ω e ha hb])
      (fun e _ ω a ha => by
        simp only [f_size, selSet_update_zero hQ ω e ha]
        set S₀ := selSet (Function.update ω e a)
        have hsub1' : S₀ ∩ H_U ⊆ insert e.1 S₀ ∩ H_U := fun E hE =>
          Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_inter.mp hE).1,
            (Finset.mem_inter.mp hE).2⟩
        have hsub2' : insert e.1 S₀ ∩ H_U ⊆ (S₀ ∩ H_U) ∪ {e.1} := by
          intro E hE
          rcases Finset.mem_inter.mp hE with ⟨hEi, hEHU⟩
          rcases Finset.mem_insert.mp hEi with rfl | hES₀
          · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hES₀, hEHU⟩)
        rw [abs_sub_comm]
        simpa using abs_card_sub_le hsub1' hsub2')
    refine hmcd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)) (Nat.cast_nonneg _))
    rw [neg_mul, neg_le_neg_iff]
    refine le_min ?_ hc_lin
    calc c_exp * Dt
        ≤ c_exp * (D : ℝ) := mul_le_mul_of_nonneg_left hDt_le (by positivity)
      _ ≤ (η ^ 2 / (8 * ε)) * (D : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hD_pos.le
          dsimp [c_exp]
          refine div_le_div_of_nonneg_left (sq_nonneg η) (by positivity) ?_
          have hk3 : (8 : ℝ) ≤ 32 * (k : ℝ) ^ 3 := by nlinarith only [hk_real, hk2]
          exact mul_le_mul_of_nonneg_right hk3 hε0.le
      _ = (η * (D : ℝ)) ^ 2 / (4 * (2 * ε * (D : ℝ))) := by field_simp; ring
  exact ⟨hd1, hd2, hP_surv, hP_size⟩

lemma target_span_cross_prob {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (k Q D : ℕ) (Dt ε δ η : ℝ)
    (hk : 4 ≤ k) (hQ : 0 < Q) (hD : 1 ≤ D)
    (hH_sub : ∀ E ∈ H, E ⊆ W) (hH_unif : ∀ E ∈ H, E.card = k)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 16) (hδ0 : 0 ≤ δ) (hδ_small : δ ≤ 1 / 40)
    (hη0 : 0 < η) (hη_small : η ≤ ε ^ 2)
    (hDt_pos : 0 < Dt) (hDt_le : Dt ≤ (D : ℝ))
    (hp_hi : 1 / (Q : ℝ) ≤ ε / Dt)
    (hdeg_hi : ∀ v ∈ W, ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ (1 + δ) * Dt)
    (U : Finset α) (hUt_leD : ((U ∩ W).card : ℝ) ≤ (D : ℝ)) :
    let c_exp : ℝ := η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)
    DependsOn (liftH H (depU H W U)) (spanBad W H Q D η U) ∧
    DependsOn (liftH H (depU H W U)) (crossBad W H k Q D ε U) ∧
    ((spanBad W H Q D η U).card : ℝ) ≤ 2 * Real.exp (-c_exp * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) ∧
    ((crossBad W H k Q D ε U).card : ℝ) ≤ Real.exp (-c_exp * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) := by
  intro c_exp
  let U_t := U ∩ W
  let H_U := H.filter (fun E => (E ∩ U_t).Nonempty)
  let H_U2 := (H \ H_U).filter (fun F => ∃ E ∈ H_U, (E ∩ F).Nonempty)
  let f_span : (↥H → Fin Q) → ℝ := fun ω => (((selSet ω ∩ H_U).biUnion id).card : ℝ)
  have hk_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk_real]
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  have hη_leε : η ≤ ε := hη_small.trans (by nlinarith only [hε0, hε_le])
  have hp_nn : (0 : ℝ) ≤ 1 / (Q : ℝ) := by positivity
  have hH_U_sub : H_U ⊆ H := Finset.filter_subset _ _
  have hH_U2_sub : H_U2 ⊆ H := (Finset.filter_subset _ _).trans Finset.sdiff_subset
  have hdisj_U : Disjoint H_U H_U2 :=
    disjoint_sdiff_self_right.mono_right (Finset.filter_subset _ _)
  have hHU_b := card_HU_bounds W H Q D Dt ε δ hD hε0 hδ0 hδ_small hDt_pos hp_hi hdeg_hi U hUt_leD
  have hc_lin := c_exp_le_lin hk hD hε0 hη0 hη_leε hDt_le
  have hsub1 : liftH H H_U ⊆ liftH H (depU H W U) := by
    rw [depU, liftH_union]; exact Finset.subset_union_left
  have hsub2 : liftH H H_U2 ⊆ liftH H (depU H W U) := by
    rw [depU, liftH_union]; exact Finset.subset_union_right
  have hf_span_dep : ∀ ω₁ ω₂ : ↥H → Fin Q,
      (∀ e ∈ liftH H H_U, ω₁ e = ω₂ e) → f_span ω₁ = f_span ω₂ := by
    intro ω₁ ω₂ hag; simp only [f_span, selSet_inter_agree ω₁ ω₂ hag]
  have hd3 : DependsOn (liftH H (depU H W U)) (spanBad W H Q D η U) :=
    dependsOn_mono hsub1 fun ω₁ ω₂ hag => by
      simp only [spanBad, Finset.mem_filter, Finset.mem_univ, true_and]
      change η * (D : ℝ) ≤ |f_span ω₁ - _| ↔ η * (D : ℝ) ≤ |f_span ω₂ - _|
      rw [hf_span_dep ω₁ ω₂ hag]
  have hd4 : DependsOn (liftH H (depU H W U)) (crossBad W H k Q D ε U) := by
    intro ω₁ ω₂ hag
    have h1 := selSet_inter_agree (A := H_U) ω₁ ω₂ (fun e he => hag e (hsub1 he))
    have h2 := selSet_inter_agree (A := H_U2) ω₁ ω₂ (fun e he => hag e (hsub2 he))
    have hmem : ∀ ω : ↥H → Fin Q, ω ∈ crossBad W H k Q D ε U ↔
        ((selSet ω ∩ H_U).card : ℝ) ≤ 3 * ε * (D : ℝ) ∧
        12 * (k : ℝ) * ε ^ 2 * (D : ℝ) ≤
          ∑ F ∈ selSet ω ∩ H_U2, ((F ∩ (selSet ω ∩ H_U).biUnion id).card : ℝ) := fun ω => by
      dsimp only [crossBad, H_U, H_U2, U_t]
      exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
    rw [hmem ω₁, hmem ω₂, h1, h2]
  have hP_span : ((spanBad W H Q D η U).card : ℝ) ≤
      2 * Real.exp (-c_exp * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) := by
    have hmcd := bernoulli_mcdiarmid_sub Q hQ (liftH H H_U)
      (fun _ => (k : ℝ)) f_span (k : ℝ) (2 * (k : ℝ) ^ 2 * ε * (D : ℝ)) (η * (D : ℝ))
      hk_pos (by positivity) (mul_pos hη0 hD_pos)
      (fun _ _ => hk_pos.le) (fun _ _ => le_rfl)
      (by
        rw [Finset.sum_const, nsmul_eq_mul, card_liftH hH_U_sub]
        calc (H_U.card : ℝ) * (k : ℝ) ^ 2 / (Q : ℝ)
            = (k : ℝ) ^ 2 * ((H_U.card : ℝ) / (Q : ℝ)) := by ring
          _ ≤ (k : ℝ) ^ 2 * (2 * ε * (D : ℝ)) := mul_le_mul_of_nonneg_left hHU_b.2 (sq_nonneg _)
          _ = 2 * (k : ℝ) ^ 2 * ε * (D : ℝ) := by ring)
      hf_span_dep
      (fun e _ ω a b ha hb => by simp only [f_span, selSet_update_of_ne_zero ω e ha hb])
      (fun e _ ω a ha => by
        simp only [f_span, selSet_update_zero hQ ω e ha]
        set S₀ := selSet (Function.update ω e a)
        have hsub1' : (S₀ ∩ H_U).biUnion id ⊆ (insert e.1 S₀ ∩ H_U).biUnion id :=
          Finset.biUnion_subset_biUnion_of_subset_left id fun E hE =>
            Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_inter.mp hE).1,
              (Finset.mem_inter.mp hE).2⟩
        have hsub2' : (insert e.1 S₀ ∩ H_U).biUnion id ⊆ (S₀ ∩ H_U).biUnion id ∪ e.1 := by
          intro w hw
          rcases Finset.mem_biUnion.mp hw with ⟨E, hE, hwE⟩
          rcases Finset.mem_inter.mp hE with ⟨hEi, hEHU⟩
          rcases Finset.mem_insert.mp hEi with rfl | hES₀
          · exact Finset.mem_union_right _ hwE
          · exact Finset.mem_union_left _
              (Finset.mem_biUnion.mpr ⟨E, Finset.mem_inter.mpr ⟨hES₀, hEHU⟩, hwE⟩)
        rw [abs_sub_comm]
        have hle := abs_card_sub_le hsub1' hsub2'
        rw [hH_unif e.1 e.2] at hle
        exact hle)
    refine hmcd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)) (Nat.cast_nonneg _))
    rw [neg_mul, neg_le_neg_iff]
    refine le_min ?_ hc_lin
    calc c_exp * Dt
        ≤ c_exp * (D : ℝ) := mul_le_mul_of_nonneg_left hDt_le (by positivity)
      _ ≤ (η ^ 2 / (8 * (k : ℝ) ^ 2 * ε)) * (D : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hD_pos.le
          dsimp [c_exp]
          refine div_le_div_of_nonneg_left (sq_nonneg η) (by positivity) ?_
          have hk3 : 8 * (k : ℝ) ^ 2 ≤ 32 * (k : ℝ) ^ 3 := by nlinarith only [hk_real, hk2]
          exact mul_le_mul_of_nonneg_right hk3 hε0.le
      _ = (η * (D : ℝ)) ^ 2 / (4 * (2 * (k : ℝ) ^ 2 * ε * (D : ℝ))) := by field_simp; ring
  have hP_cross : ((crossBad W H k Q D ε U).card : ℝ) ≤
      Real.exp (-c_exp * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) := by
    have hch := card_cross_bad_le H H_U H_U2 Q hQ hH_U_sub hH_U2_sub hdisj_U
      (k : ℝ) (3 * ε * (D : ℝ)) (6 * (k : ℝ) * ε ^ 2 * (D : ℝ)) hk_pos (by positivity)
      (fun F hF => by rw [hH_unif F (hH_U2_sub hF)])
      (fun S_U hSU hSU_le => by
        have hV_sub : S_U.biUnion id ⊆ W := by
          intro w hw
          rcases Finset.mem_biUnion.mp hw with ⟨E, hESU, hwE⟩
          exact hH_sub E (hH_U_sub (hSU hESU)) hwE
        have hV_card : ((S_U.biUnion id).card : ℝ) ≤ 3 * (k : ℝ) * ε * (D : ℝ) := by
          have h1 : (S_U.biUnion id).card ≤ k * S_U.card := by
            calc (S_U.biUnion id).card ≤ ∑ E ∈ S_U, E.card := Finset.card_biUnion_le
              _ = ∑ _E ∈ S_U, k := Finset.sum_congr rfl fun E hE => hH_unif E (hH_U_sub (hSU hE))
              _ = k * S_U.card := by simp [mul_comm]
          have h1' : ((S_U.biUnion id).card : ℝ) ≤ (k : ℝ) * (S_U.card : ℝ) := by exact_mod_cast h1
          nlinarith only [h1', hSU_le, hk_pos]
        have hsum_le : ∑ F ∈ H_U2, ((F ∩ S_U.biUnion id).card : ℝ) ≤
            (1 + δ) * Dt * ((S_U.biUnion id).card : ℝ) := by
          have hnat : ∑ F ∈ H_U2, (F ∩ S_U.biUnion id).card ≤
              ∑ w ∈ S_U.biUnion id, (H.filter (fun F => w ∈ F)).card := by
            calc ∑ F ∈ H_U2, (F ∩ S_U.biUnion id).card
                = ∑ F ∈ H_U2, ∑ w ∈ S_U.biUnion id, if w ∈ F then 1 else 0 := by
                  refine Finset.sum_congr rfl fun F _ => ?_
                  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
              _ = ∑ w ∈ S_U.biUnion id, ∑ F ∈ H_U2, if w ∈ F then 1 else 0 := Finset.sum_comm
              _ = ∑ w ∈ S_U.biUnion id, (H_U2.filter (fun F => w ∈ F)).card := by
                  refine Finset.sum_congr rfl fun w _ => by rw [Finset.card_filter]
              _ ≤ ∑ w ∈ S_U.biUnion id, (H.filter (fun F => w ∈ F)).card :=
                  Finset.sum_le_sum fun w _ =>
                    Finset.card_le_card (Finset.filter_subset_filter _ hH_U2_sub)
          have hcast : ∑ F ∈ H_U2, ((F ∩ S_U.biUnion id).card : ℝ) ≤
              ∑ w ∈ S_U.biUnion id, ((H.filter (fun F => w ∈ F)).card : ℝ) := by exact_mod_cast hnat
          calc ∑ F ∈ H_U2, ((F ∩ S_U.biUnion id).card : ℝ)
              ≤ ∑ _w ∈ S_U.biUnion id, ((1 + δ) * Dt) :=
                hcast.trans (Finset.sum_le_sum fun w hw => hdeg_hi w (hV_sub hw))
            _ = (1 + δ) * Dt * ((S_U.biUnion id).card : ℝ) := by
                simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
        calc (∑ F ∈ H_U2, ((F ∩ S_U.biUnion id).card : ℝ)) / (Q : ℝ)
            = (∑ F ∈ H_U2, ((F ∩ S_U.biUnion id).card : ℝ)) * (1 / (Q : ℝ)) := by ring
          _ ≤ ((1 + δ) * Dt * (3 * (k : ℝ) * ε * (D : ℝ))) * (ε / Dt) :=
              mul_le_mul (hsum_le.trans (mul_le_mul_of_nonneg_left hV_card (by positivity)))
                hp_hi hp_nn (by positivity)
          _ = (3 * (1 + δ)) * ((k : ℝ) * ε ^ 2 * (D : ℝ)) := by field_simp
          _ ≤ 6 * ((k : ℝ) * ε ^ 2 * (D : ℝ)) :=
              mul_le_mul_of_nonneg_right (by linarith only [hδ_small]) (by positivity)
          _ = 6 * (k : ℝ) * ε ^ 2 * (D : ℝ) := by ring)
    have hmul12 : 2 * (6 * (k : ℝ) * ε ^ 2 * (D : ℝ)) = 12 * (k : ℝ) * ε ^ 2 * (D : ℝ) := by ring
    rw [hmul12] at hch
    refine hch.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _))
    have hexp_eq : -(1 / (3 * (k : ℝ))) * (6 * (k : ℝ) * ε ^ 2 * (D : ℝ)) = -2 * ε ^ 2 * (D : ℝ) := by
      field_simp; ring
    rw [hexp_eq]
    have hc_le_eps : c_exp ≤ 2 * ε ^ 2 := by
      dsimp [c_exp]
      rw [div_le_iff₀ (by positivity)]
      have hη2 : η ^ 2 ≤ ε ^ 4 := by
        have := pow_le_pow_left₀ hη0.le hη_small 2; linarith only [this]
      have hk3 : (1 : ℝ) ≤ 64 * (k : ℝ) ^ 3 := by nlinarith only [hk_real, hk2]
      have hε3 : ε ^ 4 ≤ ε ^ 3 := by
        calc ε ^ 4 = ε ^ 3 * ε := by ring
          _ ≤ ε ^ 3 * 1 := mul_le_mul_of_nonneg_left (by linarith only [hε_le]) (by positivity)
          _ = ε ^ 3 := mul_one _
      calc η ^ 2 ≤ ε ^ 3 := hη2.trans hε3
        _ = 1 * ε ^ 3 := (one_mul _).symm
        _ ≤ (64 * (k : ℝ) ^ 3) * ε ^ 3 := mul_le_mul_of_nonneg_right hk3 (by positivity)
        _ = 2 * ε ^ 2 * (32 * (k : ℝ) ^ 3 * ε) := by ring
    have h1 : c_exp * Dt ≤ (2 * ε ^ 2) * (D : ℝ) :=
      mul_le_mul hc_le_eps hDt_le hDt_pos.le (by positivity)
    linarith only [h1]
  exact ⟨hd3, hd4, hP_span, hP_cross⟩

lemma target_expect_gap {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (k Q D : ℕ) (Dt ε δ : ℝ)
    (hk : 4 ≤ k) (hQ : 0 < Q) (hD : 1 ≤ D)
    (hH_sub : ∀ E ∈ H, E ⊆ W) (hH_unif : ∀ E ∈ H, E.card = k)
    (hε0 : 0 < ε) (hδ0 : 0 ≤ δ) (hδ_small : δ ≤ 1 / 40)
    (hDt_pos : 0 < Dt) (hp_hi : 1 / (Q : ℝ) ≤ ε / Dt)
    (hdeg_hi : ∀ v ∈ W, ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ (1 + δ) * Dt)
    (U : Finset α) (hUt_leD : ((U ∩ W).card : ℝ) ≤ (D : ℝ)) :
    let H_U := H.filter (fun E => (E ∩ (U ∩ W)).Nonempty)
    let f_span : (↥H → Fin Q) → ℝ := fun ω => (((selSet ω ∩ H_U).biUnion id).card : ℝ)
    let μ_span : ℝ := (∑ ω : ↥H → Fin Q, f_span ω) / (Fintype.card (↥H → Fin Q) : ℝ)
    (k : ℝ) * ((H_U.card : ℝ) / (Q : ℝ)) - μ_span ≤ (k : ℝ) * ε ^ 2 * (D : ℝ) := by
  intro H_U f_span μ_span
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  have hTot_pos : (0 : ℝ) < (Fintype.card (↥H → Fin Q) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hp_nn : (0 : ℝ) ≤ 1 / (Q : ℝ) := by positivity
  have hp_le1 : 1 / (Q : ℝ) ≤ 1 := by
    rw [div_le_one (Nat.cast_pos.mpr hQ)]; exact_mod_cast Nat.succ_le_of_lt hQ
  have hH_U_sub : H_U ⊆ H := Finset.filter_subset _ _
  have hHU_b := card_HU_bounds W H Q D Dt ε δ hD hε0 hδ0 hδ_small hDt_pos hp_hi hdeg_hi U hUt_leD
  have hf_span_rew : ∀ ω : ↥H → Fin Q,
      f_span ω = (W.card : ℝ) -
        ((W.filter (fun w => ∀ e ∈ liftH H (H_U.filter (fun E => w ∈ E)), (ω e).val ≠ 0)).card : ℝ) := by
    intro ω
    have hsubW : (selSet ω ∩ H_U).biUnion id ⊆ W := fun w hw => by
      rcases Finset.mem_biUnion.mp hw with ⟨E, hE, hwE⟩
      exact hH_sub E (hH_U_sub (Finset.mem_inter.mp hE).2) hwE
    have hcomp : W \ (selSet ω ∩ H_U).biUnion id =
        W.filter (fun w => ∀ e ∈ liftH H (H_U.filter (fun E => w ∈ E)), (ω e).val ≠ 0) := by
      ext w; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_biUnion, id_eq, and_congr_right_iff]
      intro _
      exact ⟨fun h e he h0 => by
          rcases Finset.mem_filter.mp (mem_liftH.mp he) with ⟨hEHU, hwE⟩
          exact h ⟨e.1, Finset.mem_inter.mpr ⟨(mem_selSet_iff ω e).mpr h0, hEHU⟩, hwE⟩,
        fun h ⟨E, hE, hwE⟩ => by
          rcases Finset.mem_inter.mp hE with ⟨hES, hEHU⟩
          exact h ⟨E, selSet_subset ω hES⟩
            (mem_liftH.mpr (Finset.mem_filter.mpr ⟨hEHU, hwE⟩))
            ((mem_selSet_iff ω ⟨E, selSet_subset ω hES⟩).mp hES)⟩
    have hadd' : ((W \ (selSet ω ∩ H_U).biUnion id).card : ℝ) +
        (((selSet ω ∩ H_U).biUnion id).card : ℝ) = (W.card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hsubW
    rw [← hcomp]; dsimp [f_span]; linarith only [hadd']
  have hμ_span : μ_span = ∑ w ∈ W, (1 - (1 - 1 / (Q : ℝ)) ^ (H_U.filter (fun E => w ∈ E)).card) := by
    simp only [μ_span]; simp_rw [hf_span_rew]
    rw [Finset.sum_sub_distrib, sub_div,
      avg_sum_disjoint_filter Q hQ W (fun w => liftH H (H_U.filter (fun E => w ∈ E)))]
    have hcW : (∑ _ω : ↥H → Fin Q, (W.card : ℝ)) / (Fintype.card (↥H → Fin Q) : ℝ) = (W.card : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hTot_pos.ne']
    rw [hcW, Finset.sum_sub_distrib]
    have hcW' : ∑ _w ∈ W, (1 : ℝ) = (W.card : ℝ) := by simp
    rw [hcW']; congr 1
    exact Finset.sum_congr rfl fun w _ => by rw [card_liftH ((Finset.filter_subset _ _).trans hH_U_sub)]
  have hHU_sum : (k : ℝ) * (H_U.card : ℝ) = ∑ w ∈ W, ((H_U.filter (fun E => w ∈ E)).card : ℝ) := by
    have hnat : k * H_U.card = ∑ w ∈ W, (H_U.filter (fun E => w ∈ E)).card := by
      calc k * H_U.card = ∑ E ∈ H_U, E.card := by
            rw [Finset.sum_congr rfl fun E hE => hH_unif E (hH_U_sub hE)]; simp [mul_comm]
        _ = ∑ E ∈ H_U, ∑ w ∈ W, if w ∈ E then 1 else 0 := by
            refine Finset.sum_congr rfl fun E hE => ?_
            rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
              Finset.inter_eq_right.mpr (hH_sub E (hH_U_sub hE))]
        _ = ∑ w ∈ W, ∑ E ∈ H_U, if w ∈ E then 1 else 0 := Finset.sum_comm
        _ = ∑ w ∈ W, (H_U.filter (fun E => w ∈ E)).card := by
            exact Finset.sum_congr rfl fun w _ => by rw [Finset.card_filter]
    exact_mod_cast hnat
  have hgap_eq : (k : ℝ) * ((H_U.card : ℝ) / (Q : ℝ)) - μ_span =
      ∑ w ∈ W, (((H_U.filter (fun E => w ∈ E)).card : ℝ) * (1 / (Q : ℝ)) -
        (1 - (1 - 1 / (Q : ℝ)) ^ (H_U.filter (fun E => w ∈ E)).card)) := by
    have h1 : (k : ℝ) * ((H_U.card : ℝ) / (Q : ℝ)) =
        ∑ w ∈ W, ((H_U.filter (fun E => w ∈ E)).card : ℝ) * (1 / (Q : ℝ)) := by
      rw [← Finset.sum_mul, ← hHU_sum]; ring
    rw [hμ_span, h1, ← Finset.sum_sub_distrib]
  have hsum_sq : ∑ w ∈ W, ((H_U.filter (fun E => w ∈ E)).card : ℝ) ^ 2 ≤
      (1 + δ) ^ 2 * (k : ℝ) * (D : ℝ) * Dt ^ 2 := by
    calc ∑ w ∈ W, ((H_U.filter (fun E => w ∈ E)).card : ℝ) ^ 2
        ≤ ∑ w ∈ W, ((1 + δ) * Dt) * ((H_U.filter (fun E => w ∈ E)).card : ℝ) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hdw : ((H_U.filter (fun E => w ∈ E)).card : ℝ) ≤ (1 + δ) * Dt :=
            (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hH_U_sub))).trans
              (hdeg_hi w hw)
          have hnn : (0 : ℝ) ≤ ((H_U.filter (fun E => w ∈ E)).card : ℝ) := Nat.cast_nonneg _
          nlinarith only [hdw, hnn]
      _ = ((1 + δ) * Dt) * ((k : ℝ) * (H_U.card : ℝ)) := by rw [← Finset.mul_sum, hHU_sum]
      _ ≤ ((1 + δ) * Dt) * ((k : ℝ) * ((1 + δ) * (D : ℝ) * Dt)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHU_b.1 hk_pos.le) (by positivity)
      _ = (1 + δ) ^ 2 * (k : ℝ) * (D : ℝ) * Dt ^ 2 := by ring
  calc (k : ℝ) * ((H_U.card : ℝ) / (Q : ℝ)) - μ_span
      = ∑ w ∈ W, (((H_U.filter (fun E => w ∈ E)).card : ℝ) * (1 / (Q : ℝ)) -
          (1 - (1 - 1 / (Q : ℝ)) ^ (H_U.filter (fun E => w ∈ E)).card)) := hgap_eq
    _ ≤ ∑ w ∈ W, (((H_U.filter (fun E => w ∈ E)).card : ℝ) ^ 2 / 2) * (1 / (Q : ℝ)) ^ 2 := by
        refine Finset.sum_le_sum fun w _ => ?_
        set n := (H_U.filter (fun E => w ∈ E)).card
        have hq := one_sub_pow_le_quad hp_nn hp_le1 n
        have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hn2 : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by nlinarith only [hnn]
        have hq2 : (n : ℝ) * ((n : ℝ) - 1) / 2 * (1 / (Q : ℝ)) ^ 2 ≤
            (n : ℝ) ^ 2 / 2 * (1 / (Q : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hn2]) (sq_nonneg _)
        linarith only [hq, hq2]
    _ = (∑ w ∈ W, ((H_U.filter (fun E => w ∈ E)).card : ℝ) ^ 2) * ((1 / (Q : ℝ)) ^ 2 / 2) := by
        rw [← Finset.sum_mul, ← Finset.sum_div]; ring
    _ ≤ ((1 + δ) ^ 2 * (k : ℝ) * (D : ℝ) * Dt ^ 2) * ((ε / Dt) ^ 2 / 2) :=
        mul_le_mul hsum_sq (div_le_div_of_nonneg_right (pow_le_pow_left₀ hp_nn hp_hi 2) (by norm_num))
          (by positivity) (by positivity)
    _ = ((1 + δ) ^ 2 / 2) * ((k : ℝ) * ε ^ 2 * (D : ℝ)) := by field_simp
    _ ≤ 1 * ((k : ℝ) * ε ^ 2 * (D : ℝ)) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hδ0, hδ_small]) (by positivity)
    _ = (k : ℝ) * ε ^ 2 * (D : ℝ) := one_mul _

lemma target_bad_expect {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (k Q D : ℕ)
    (Dt ε δ η ut : ℝ)
    (hk : 4 ≤ k) (hQ : 0 < Q) (hD : 1 ≤ D)
    (hH_sub : ∀ E ∈ H, E ⊆ W) (hH_unif : ∀ E ∈ H, E.card = k)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 16)
    (hδ0 : 0 ≤ δ) (hδ_small : δ ≤ 1 / 40)
    (hη0 : 0 < η) (hη_leε : η ≤ ε)
    (_hut0 : 0 ≤ ut) (hut1 : ut ≤ 1)
    (hDt_pos : 0 < Dt) (hDt_err : 4 * (k : ℝ) * ε / Dt ≤ η)
    (hp_hi : 1 / (Q : ℝ) ≤ ε / Dt) (hp_lo : ε / Dt - ε ^ 2 / Dt ^ 2 ≤ 1 / (Q : ℝ))
    (hdeg_lo : ∀ v ∈ W, (1 - δ) * Dt ≤ ((H.filter (fun E => v ∈ E)).card : ℝ))
    (hdeg_hi : ∀ v ∈ W, ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ (1 + δ) * Dt)
    (U : Finset α) (hU_hi : ((U ∩ W).card : ℝ) ≤ ut * (D : ℝ)) :
    ∀ ω : ↥H → Fin Q, ω ∉ targetBad W H k Q D ε η U →
      ((U ∩ (W \ (selSet ω).biUnion id)).card : ℝ) ≤
        (ut * Real.exp (-(3 / 4 : ℝ) * ε) + η) * (D : ℝ) ∧
      (((U ∩ (W \ (W \ (selSet ω).biUnion id))) \ (biteMatch ω).biUnion id).card : ℝ) ≤
        (14 * (k : ℝ) ^ 2 * ε ^ 2 + 4 * (k : ℝ) ^ 2 * η) * (D : ℝ) := by
  let U_t := U ∩ W
  let H_U := H.filter (fun E => (E ∩ U_t).Nonempty)
  let H_U2 := (H \ H_U).filter (fun F => ∃ E ∈ H_U, (E ∩ F).Nonempty)
  let f_surv : (↥H → Fin Q) → ℝ := fun ω => ((U_t \ (selSet ω).biUnion id).card : ℝ)
  let μ_surv : ℝ := (∑ ω : ↥H → Fin Q, f_surv ω) / (Fintype.card (↥H → Fin Q) : ℝ)
  let f_size : (↥H → Fin Q) → ℝ := fun ω => ((selSet ω ∩ H_U).card : ℝ)
  let μ_size : ℝ := (∑ ω : ↥H → Fin Q, f_size ω) / (Fintype.card (↥H → Fin Q) : ℝ)
  let f_span : (↥H → Fin Q) → ℝ := fun ω => (((selSet ω ∩ H_U).biUnion id).card : ℝ)
  let μ_span : ℝ := (∑ ω : ↥H → Fin Q, f_span ω) / (Fintype.card (↥H → Fin Q) : ℝ)
  have hk_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp_nn : (0 : ℝ) ≤ 1 / (Q : ℝ) := by positivity
  have hp_le1 : 1 / (Q : ℝ) ≤ 1 := by
    rw [div_le_one (Nat.cast_pos.mpr hQ)]; exact_mod_cast Nat.succ_le_of_lt hQ
  have hH_U_sub : H_U ⊆ H := Finset.filter_subset _ _
  have hdisj_U : Disjoint H_U H_U2 :=
    disjoint_sdiff_self_right.mono_right (Finset.filter_subset _ _)
  have hUt_leD : (U_t.card : ℝ) ≤ (D : ℝ) := hU_hi.trans (by nlinarith only [hut1, hD_pos])
  have hHU_b := card_HU_bounds W H Q D Dt ε δ hD hε0 hδ0 hδ_small hDt_pos hp_hi hdeg_hi U hUt_leD
  have hμ_surv : μ_surv ≤ ut * Real.exp (-(3 / 4 : ℝ) * ε) * (D : ℝ) := by
    have hrew : ∀ ω : ↥H → Fin Q,
        f_surv ω = ((U_t.filter (fun u => ∀ e ∈ liftH H (H.filter (fun E => u ∈ E)),
          (ω e).val ≠ 0)).card : ℝ) := by
      intro ω; simp only [f_surv]; congr 2; ext u
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_biUnion, id_eq, and_congr_right_iff]
      intro _
      exact ⟨fun h e he h0 => h ⟨e.1, (mem_selSet_iff ω e).mpr h0,
        (Finset.mem_filter.mp (mem_liftH.mp he)).2⟩,
        fun h ⟨E, hES, huE⟩ => h ⟨E, selSet_subset ω hES⟩
          (mem_liftH.mpr (Finset.mem_filter.mpr ⟨selSet_subset ω hES, huE⟩))
          ((mem_selSet_iff ω ⟨E, selSet_subset ω hES⟩).mp hES)⟩
    have havg : μ_surv = ∑ u ∈ U_t, (1 - 1 / (Q : ℝ)) ^ (H.filter (fun E => u ∈ E)).card := by
      simp only [μ_surv]; simp_rw [hrew]
      rw [avg_sum_disjoint_filter Q hQ U_t (fun u => liftH H (H.filter (fun E => u ∈ E)))]
      exact Finset.sum_congr rfl fun u _ => by rw [card_liftH (Finset.filter_subset _ _)]
    have hterm : ∀ u ∈ U_t, (1 - 1 / (Q : ℝ)) ^ (H.filter (fun E => u ∈ E)).card ≤
        Real.exp (-(3 / 4 : ℝ) * ε) := by
      intro u hu
      set d := (H.filter (fun E => u ∈ E)).card
      have hd : (1 - δ) * Dt ≤ (d : ℝ) := hdeg_lo u (Finset.mem_inter.mp hu).2
      have h1 : (1 - 1 / (Q : ℝ)) ^ d ≤ Real.exp (-(1 / (Q : ℝ)) * (d : ℝ)) := by
        calc (1 - 1 / (Q : ℝ)) ^ d
            ≤ (Real.exp (-(1 / (Q : ℝ)))) ^ d :=
              pow_le_pow_left₀ (by linarith only [hp_le1])
                (by linarith [Real.add_one_le_exp (-(1 / (Q : ℝ)))]) d
          _ = Real.exp ((d : ℝ) * (-(1 / (Q : ℝ)))) := (Real.exp_nat_mul _ d).symm
          _ = Real.exp (-(1 / (Q : ℝ)) * (d : ℝ)) := by ring_nf
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      have hεDt : ε / Dt ≤ 1 / 40 := by
        have h1' : ε / Dt ≤ η / (4 * (k : ℝ)) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ))]
          calc ε / Dt * (4 * (k : ℝ)) = 4 * (k : ℝ) * ε / Dt := by ring
            _ ≤ η := hDt_err
        have h2' : η / (4 * (k : ℝ)) ≤ 1 / 40 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ))]
          nlinarith only [hk_real, hη_leε, hε_le]
        exact h1'.trans h2'
      have hprod : (3 / 4 : ℝ) * ε ≤ (1 / (Q : ℝ)) * (d : ℝ) := by
        have hfac : (3 / 4 : ℝ) ≤ (1 - δ) * (1 - ε / Dt) := by
          nlinarith only [hδ0, hδ_small, hεDt]
        calc (3 / 4 : ℝ) * ε
            ≤ ((1 - δ) * (1 - ε / Dt)) * ε := mul_le_mul_of_nonneg_right hfac hε0.le
          _ = (ε / Dt - ε ^ 2 / Dt ^ 2) * ((1 - δ) * Dt) := by field_simp
          _ ≤ (1 / (Q : ℝ)) * (d : ℝ) :=
              mul_le_mul hp_lo hd (mul_nonneg (by linarith only [hδ_small]) hDt_pos.le) hp_nn
      linarith only [hprod]
    calc μ_surv
        ≤ ∑ _u ∈ U_t, Real.exp (-(3 / 4 : ℝ) * ε) := by rw [havg]; exact Finset.sum_le_sum hterm
      _ = (U_t.card : ℝ) * Real.exp (-(3 / 4 : ℝ) * ε) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (ut * (D : ℝ)) * Real.exp (-(3 / 4 : ℝ) * ε) :=
          mul_le_mul_of_nonneg_right hU_hi (Real.exp_pos _).le
      _ = ut * Real.exp (-(3 / 4 : ℝ) * ε) * (D : ℝ) := by ring
  have hμ_size : μ_size = (H_U.card : ℝ) / (Q : ℝ) := by
    have hrew : ∀ ω : ↥H → Fin Q,
        f_size ω = (((liftH H H_U).filter (fun e => (ω e).val = 0)).card : ℝ) := by
      intro ω; simp only [f_size]; congr 1; symm
      refine Finset.card_bij (fun e _ => e.1) ?_ (fun _ _ _ _ h => Subtype.ext h) ?_
      · intro e he; rcases Finset.mem_filter.mp he with ⟨heL, h0⟩
        exact Finset.mem_inter.mpr ⟨(mem_selSet_iff ω e).mpr h0, mem_liftH.mp heL⟩
      · intro E hE; rcases Finset.mem_inter.mp hE with ⟨hES, hEHU⟩
        exact ⟨⟨E, selSet_subset ω hES⟩, Finset.mem_filter.mpr
          ⟨mem_liftH.mpr hEHU, (mem_selSet_iff ω ⟨E, selSet_subset ω hES⟩).mp hES⟩, rfl⟩
    simp only [μ_size]; simp_rw [hrew]
    rw [avg_sum_card_filter_zero Q hQ (liftH H H_U), card_liftH hH_U_sub]
  have hμ_gap : (k : ℝ) * μ_size - μ_span ≤ (k : ℝ) * ε ^ 2 * (D : ℝ) := by
    rw [hμ_size]
    exact target_expect_gap W H k Q D Dt ε δ hk hQ hD hH_sub hH_unif hε0 hδ0 hδ_small
      hDt_pos hp_hi hdeg_hi U hUt_leD
  intro ω hgood
  simp only [targetBad, Finset.mem_union, not_or] at hgood
  rcases hgood with ⟨⟨⟨hnsurv, hnsize⟩, hnspan⟩, hncross⟩
  have hsurv_lt : |f_surv ω - μ_surv| < η * (D : ℝ) :=
    lt_of_not_ge fun h => hnsurv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hsize_lt : |f_size ω - μ_size| < η * (D : ℝ) :=
    lt_of_not_ge fun h => hnsize (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hspan_lt : |f_span ω - μ_span| < η * (D : ℝ) :=
    lt_of_not_ge fun h => hnspan (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  constructor
  · have hset : U ∩ (W \ (selSet ω).biUnion id) = U_t \ (selSet ω).biUnion id := by
      ext u; simp only [U_t, Finset.mem_inter, Finset.mem_sdiff]; tauto
    rw [hset]; change f_surv ω ≤ _
    linarith only [(abs_lt.mp hsurv_lt).2, hμ_surv]
  · have hset : (U ∩ (W \ (W \ (selSet ω).biUnion id))) \ (biteMatch ω).biUnion id =
        U_t ∩ ((selSet ω).biUnion id \ (biteMatch ω).biUnion id) := by
      ext u
      simp only [U_t, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨huU, huW, hnot⟩, huM⟩
        refine ⟨⟨huU, huW⟩, ?_, huM⟩
        by_contra huS; exact hnot ⟨huW, huS⟩
      · rintro ⟨⟨huU, huW⟩, huS, huM⟩
        exact ⟨⟨huU, huW, fun h => h.2 huS⟩, huM⟩
    rw [hset]
    have hwaste := card_wasted_le H k hH_unif U_t (selSet ω) (selSet_subset ω)
    have hsz_le : ((selSet ω ∩ H_U).card : ℝ) ≤ 3 * ε * (D : ℝ) := by
      change f_size ω ≤ _
      have h1 : f_size ω < μ_size + η * (D : ℝ) := by linarith only [(abs_lt.mp hsize_lt).2]
      rw [hμ_size] at h1
      nlinarith only [h1, hHU_b.2, hη_leε, hD_pos]
    have hcross_lt : ∑ F ∈ selSet ω ∩ H_U2, ((F ∩ (selSet ω ∩ H_U).biUnion id).card : ℝ) <
        12 * (k : ℝ) * ε ^ 2 * (D : ℝ) :=
      lt_of_not_ge fun h => hncross (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsz_le, h⟩)
    have hsum_out : ∑ F ∈ selSet ω \ (selSet ω ∩ H_U), ((F ∩ (selSet ω ∩ H_U).biUnion id).card : ℝ) =
        ∑ F ∈ selSet ω ∩ H_U2, ((F ∩ (selSet ω ∩ H_U).biUnion id).card : ℝ) := by
      refine (Finset.sum_subset (fun F hF => by
        rcases Finset.mem_inter.mp hF with ⟨hFS, hF2⟩
        exact Finset.mem_sdiff.mpr ⟨hFS, fun h => Finset.disjoint_left.mp hdisj_U (Finset.mem_inter.mp h).2 hF2⟩)
        (fun F hF hnot => ?_)).symm
      rcases Finset.mem_sdiff.mp hF with ⟨hFS, hnotI⟩
      have hFH : F ∈ H := selSet_subset ω hFS
      have hFnotHU : F ∉ H_U := fun h => hnotI (Finset.mem_inter.mpr ⟨hFS, h⟩)
      have hFnot2 : F ∉ H_U2 := fun h => hnot (Finset.mem_inter.mpr ⟨hFS, h⟩)
      have hdisjF : F ∩ (selSet ω ∩ H_U).biUnion id = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        rcases Finset.mem_inter.mp hw with ⟨hwF, hwbi⟩
        rcases Finset.mem_biUnion.mp hwbi with ⟨E, hESU, hwE⟩
        exact hFnot2 (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hFH, hFnotHU⟩,
          ⟨E, (Finset.mem_inter.mp hESU).2, ⟨w, Finset.mem_inter.mpr ⟨hwE, hwF⟩⟩⟩⟩)
      rw [hdisjF]; simp
    have hgap_ω : (k : ℝ) * ((selSet ω ∩ H_U).card : ℝ) - (((selSet ω ∩ H_U).biUnion id).card : ℝ) ≤
        (k : ℝ) * ε ^ 2 * (D : ℝ) + 2 * (k : ℝ) * η * (D : ℝ) := by
      change (k : ℝ) * f_size ω - f_span ω ≤ _
      have h1 : f_size ω < μ_size + η * (D : ℝ) := by linarith only [(abs_lt.mp hsize_lt).2]
      have h2 : μ_span - η * (D : ℝ) < f_span ω := by linarith only [(abs_lt.mp hspan_lt).1]
      have h3 : (k : ℝ) * f_size ω ≤ (k : ℝ) * (μ_size + η * (D : ℝ)) :=
        mul_le_mul_of_nonneg_left h1.le hk_pos.le
      have h4 : η * (D : ℝ) ≤ (k : ℝ) * (η * (D : ℝ)) := by
        calc η * (D : ℝ) = 1 * (η * (D : ℝ)) := (one_mul _).symm
          _ ≤ (k : ℝ) * (η * (D : ℝ)) :=
              mul_le_mul_of_nonneg_right (by linarith only [hk_real]) (by positivity)
      linarith only [h3, h2, hμ_gap, h4]
    dsimp only at hwaste
    rw [hsum_out] at hwaste
    have ha : 2 * (k : ℝ) * ((k : ℝ) * ((selSet ω ∩ H_U).card : ℝ) -
          (((selSet ω ∩ H_U).biUnion id).card : ℝ)) ≤
        2 * (k : ℝ) * ((k : ℝ) * ε ^ 2 * (D : ℝ) + 2 * (k : ℝ) * η * (D : ℝ)) :=
      mul_le_mul_of_nonneg_left hgap_ω (by positivity)
    have hb : (k : ℝ) * ∑ F ∈ selSet ω ∩ H_U2, ((F ∩ (selSet ω ∩ H_U).biUnion id).card : ℝ) ≤
        (k : ℝ) * (12 * (k : ℝ) * ε ^ 2 * (D : ℝ)) :=
      mul_le_mul_of_nonneg_left hcross_lt.le hk_pos.le
    exact hwaste.trans (by linarith only [ha, hb])

/-- Concentration and waste bounds for a single target set `U ∈ T` in one nibble round. -/
lemma target_bad_bound {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (k Q D : ℕ)
    (Dt ε δ η ut : ℝ)
    (hk : 4 ≤ k) (hQ : 0 < Q) (hD : 1 ≤ D)
    (hH_sub : ∀ E ∈ H, E ⊆ W)
    (hH_unif : ∀ E ∈ H, E.card = k)
    (hε0 : 0 < ε) (hε_small : 4 * (k : ℝ) * ε ≤ 1 / 4)
    (hδ0 : 0 ≤ δ) (hδ_small : δ ≤ 1 / 40)
    (hη0 : 0 < η) (hη_small : η ≤ ε ^ 2)
    (hut0 : 0 ≤ ut) (hut1 : ut ≤ 1)
    (hDt_pos : 0 < Dt) (hDt_le : Dt ≤ (D : ℝ))
    (hDt_err : 4 * (k : ℝ) * ε / Dt ≤ η)
    (hp_hi : 1 / (Q : ℝ) ≤ ε / Dt)
    (hp_lo : ε / Dt - ε ^ 2 / Dt ^ 2 ≤ 1 / (Q : ℝ))
    (hdeg_lo : ∀ v ∈ W, (1 - δ) * Dt ≤ ((H.filter (fun E => v ∈ E)).card : ℝ))
    (hdeg_hi : ∀ v ∈ W, ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ (1 + δ) * Dt)
    (U : Finset α) (hU_hi : ((U ∩ W).card : ℝ) ≤ ut * (D : ℝ)) :
    DependsOn (liftH H (depU H W U)) (targetBad W H k Q D ε η U) ∧
    ((targetBad W H k Q D ε η U).card : ℝ) ≤
      7 * Real.exp (-(η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) ∧
    (∀ ω : ↥H → Fin Q, ω ∉ targetBad W H k Q D ε η U →
      ((U ∩ (W \ (selSet ω).biUnion id)).card : ℝ) ≤
        (ut * Real.exp (-(3 / 4 : ℝ) * ε) + η) * (D : ℝ) ∧
      (((U ∩ (W \ (W \ (selSet ω).biUnion id))) \ (biteMatch ω).biUnion id).card : ℝ) ≤
        (14 * (k : ℝ) ^ 2 * ε ^ 2 + 4 * (k : ℝ) ^ 2 * η) * (D : ℝ)) := by
  have hk_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  have hε_le : ε ≤ 1 / 16 := by nlinarith only [hk_real, hε0, hε_small]
  have hη_leε : η ≤ ε := hη_small.trans (by nlinarith only [hε0, hε_le])
  have hUt_leD : ((U ∩ W).card : ℝ) ≤ (D : ℝ) := hU_hi.trans (by nlinarith only [hut1, hD_pos])
  obtain ⟨hd1, hd2, hP1, hP2⟩ := target_surv_size_prob W H k Q D Dt ε δ η hk hQ hD hH_unif
    hε0 hδ0 hδ_small hη0 hη_leε hDt_pos hDt_le hp_hi hdeg_hi U hUt_leD
  obtain ⟨hd3, hd4, hP3, hP4⟩ := target_span_cross_prob W H k Q D Dt ε δ η hk hQ hD hH_sub hH_unif
    hε0 hε_le hδ0 hδ_small hη0 hη_small hDt_pos hDt_le hp_hi hdeg_hi U hUt_leD
  have hDep : DependsOn (liftH H (depU H W U)) (targetBad W H k Q D ε η U) :=
    dependsOn_union (dependsOn_union (dependsOn_union hd1 hd2) hd3) hd4
  have hProb : ((targetBad W H k Q D ε η U).card : ℝ) ≤
      7 * Real.exp (-(η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt) * (Fintype.card (↥H → Fin Q) : ℝ) := by
    have hu : ((targetBad W H k Q D ε η U).card : ℝ) ≤
        ((survBad W H Q D η U).card : ℝ) + ((sizeBad W H Q D η U).card : ℝ) +
        ((spanBad W H Q D η U).card : ℝ) + ((crossBad W H k Q D ε U).card : ℝ) := by
      have h1 := Finset.card_union_le (survBad W H Q D η U ∪ sizeBad W H Q D η U ∪ spanBad W H Q D η U)
        (crossBad W H k Q D ε U)
      have h2 := Finset.card_union_le (survBad W H Q D η U ∪ sizeBad W H Q D η U)
        (spanBad W H Q D η U)
      have h3 := Finset.card_union_le (survBad W H Q D η U) (sizeBad W H Q D η U)
      change ((survBad W H Q D η U ∪ sizeBad W H Q D η U ∪ spanBad W H Q D η U ∪
        crossBad W H k Q D ε U).card : ℝ) ≤ _
      exact_mod_cast (show (survBad W H Q D η U ∪ sizeBad W H Q D η U ∪ spanBad W H Q D η U ∪
        crossBad W H k Q D ε U).card ≤
        (survBad W H Q D η U).card + (sizeBad W H Q D η U).card +
        (spanBad W H Q D η U).card + (crossBad W H k Q D ε U).card by omega)
    linarith only [hu, hP1, hP2, hP3, hP4]
  exact ⟨hDep, hProb, target_bad_expect W H k Q D Dt ε δ η ut hk hQ hD hH_sub hH_unif
    hε0 hε_le hδ0 hδ_small hη0 hη_leε hut0 hut1 hDt_pos hDt_err hp_hi hp_lo hdeg_lo hdeg_hi U hU_hi⟩

/-- LLL dependency degree bound `≤ 20 * k^4 * D^4` on `I = ↥W ⊕ ↥T`. -/
lemma dep_deg_bound {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (T : Finset (Finset α))
    (k D : ℕ) (Dt δ : ℝ)
    (hk : 4 ≤ k) (hD : 1 ≤ D)
    (hH_sub : ∀ E ∈ H, E ⊆ W)
    (hH_unif : ∀ E ∈ H, E.card = k)
    (hT_deg : ∀ v : α, (T.filter (fun U => v ∈ U)).card ≤ k)
    (hδ0 : 0 ≤ δ) (hδ_small : δ ≤ 1 / 40)
    (hDt_pos : 0 < Dt) (hDt_le : Dt ≤ (D : ℝ))
    (hdeg_hi : ∀ v ∈ W, ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ (1 + δ) * Dt)
    (hU_hi : ∀ U ∈ T, ((U ∩ W).card : ℝ) ≤ (D : ℝ)) :
    let Dep : ↥W ⊕ ↥T → Finset ↥H := fun i =>
      Sum.elim (fun v => liftH H (depV H v.1)) (fun U => liftH H (depU H W U.1)) i
    ∀ i : ↥W ⊕ ↥T,
      (Finset.univ.filter (fun j : ↥W ⊕ ↥T => j ≠ i ∧ ¬ Disjoint (Dep i) (Dep j))).card ≤
        20 * k ^ 4 * D ^ 4 := by
  intro Dep i
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hdeg_2D : ∀ v ∈ W, (H.filter (fun E => v ∈ E)).card ≤ 2 * D := by
    intro v hv
    have h1 : ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ 2 * (D : ℝ) := by
      have := hdeg_hi v hv; nlinarith
    exact_mod_cast h1
  -- Step 1: Every `Dep i` has cardinality `≤ 5 * k * D ^ 3`
  have hDep_card : (Dep i).card ≤ 5 * k * D ^ 3 := by
    rcases i with v | U
    · simp only [Dep, Sum.elim_inl]
      rw [card_liftH (depV_subset H v.1)]
      have hsub : depV H v.1 ⊆
          (H.filter (fun E => v.1 ∈ E)).biUnion (fun E => E.biUnion (fun w => H.filter (fun F => w ∈ F))) := by
        intro F hF
        rcases Finset.mem_filter.mp hF with ⟨hFH, E, hEv, ⟨w, hw⟩⟩
        rcases Finset.mem_inter.mp hw with ⟨hwEr, hwF⟩
        exact Finset.mem_biUnion.mpr ⟨E, hEv, Finset.mem_biUnion.mpr
          ⟨w, Finset.mem_of_mem_erase hwEr, Finset.mem_filter.mpr ⟨hFH, hwF⟩⟩⟩
      have hle : (depV H v.1).card ≤ 4 * k * D ^ 2 := by
        calc (depV H v.1).card
            ≤ ∑ E ∈ H.filter (fun E => v.1 ∈ E), ∑ w ∈ E, (H.filter (fun F => w ∈ F)).card :=
              (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
                (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le))
          _ ≤ ∑ E ∈ H.filter (fun E => v.1 ∈ E), ∑ _w ∈ E, (2 * D) :=
              Finset.sum_le_sum fun E hE => Finset.sum_le_sum fun w hw =>
                hdeg_2D w (hH_sub E (Finset.mem_filter.mp hE).1 hw)
          _ = ∑ E ∈ H.filter (fun E => v.1 ∈ E), (k * (2 * D)) := by
              refine Finset.sum_congr rfl fun E hE => ?_
              rw [Finset.sum_const, smul_eq_mul, hH_unif E (Finset.mem_filter.mp hE).1]
          _ ≤ (2 * D) * (k * (2 * D)) := by
              rw [Finset.sum_const, smul_eq_mul]
              exact Nat.mul_le_mul_right _ (hdeg_2D v.1 v.2)
          _ = 4 * k * D ^ 2 := by ring
      have hD3 : D ^ 2 ≤ D ^ 3 := by
        calc D ^ 2 = D ^ 2 * 1 := (mul_one _).symm
          _ ≤ D ^ 2 * D := Nat.mul_le_mul_left _ hD
          _ = D ^ 3 := by ring
      calc (depV H v.1).card ≤ 4 * k * D ^ 2 := hle
        _ ≤ 4 * k * D ^ 3 := Nat.mul_le_mul_left _ hD3
        _ ≤ 5 * k * D ^ 3 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    · simp only [Dep, Sum.elim_inr]
      let H_U := H.filter (fun E => (E ∩ (U.1 ∩ W)).Nonempty)
      let H_U2 := (H \ H_U).filter (fun F => ∃ E ∈ H_U, (E ∩ F).Nonempty)
      have hsub_H : depU H W U.1 ⊆ H :=
        Finset.union_subset (Finset.filter_subset _ _) ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
      rw [card_liftH hsub_H]
      have hU_nat : (U.1 ∩ W).card ≤ D := by exact_mod_cast hU_hi U.1 U.2
      have hHU_le : H_U.card ≤ 2 * D ^ 2 := by
        have hsub : H_U ⊆ (U.1 ∩ W).biUnion (fun u => H.filter (fun E => u ∈ E)) := by
          intro E hE
          rcases Finset.mem_filter.mp hE with ⟨hEH, ⟨u, hu⟩⟩
          rcases Finset.mem_inter.mp hu with ⟨huE, huUW⟩
          exact Finset.mem_biUnion.mpr ⟨u, huUW, Finset.mem_filter.mpr ⟨hEH, huE⟩⟩
        calc H_U.card
            ≤ ∑ u ∈ U.1 ∩ W, (H.filter (fun E => u ∈ E)).card :=
              (Finset.card_le_card hsub).trans Finset.card_biUnion_le
          _ ≤ ∑ _u ∈ U.1 ∩ W, (2 * D) :=
              Finset.sum_le_sum fun u hu => hdeg_2D u (Finset.mem_inter.mp hu).2
          _ = (U.1 ∩ W).card * (2 * D) := by simp
          _ ≤ D * (2 * D) := Nat.mul_le_mul_right _ hU_nat
          _ = 2 * D ^ 2 := by ring
      have hHU2_le : H_U2.card ≤ 4 * k * D ^ 3 := by
        have hsub : H_U2 ⊆ H_U.biUnion (fun E => E.biUnion (fun w => H.filter (fun F => w ∈ F))) := by
          intro F hF
          rcases Finset.mem_filter.mp hF with ⟨hFdiff, E, hEHU, ⟨w, hw⟩⟩
          rcases Finset.mem_inter.mp hw with ⟨hwE, hwF⟩
          exact Finset.mem_biUnion.mpr ⟨E, hEHU, Finset.mem_biUnion.mpr
            ⟨w, hwE, Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hFdiff).1, hwF⟩⟩⟩
        calc H_U2.card
            ≤ ∑ E ∈ H_U, ∑ w ∈ E, (H.filter (fun F => w ∈ F)).card :=
              (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
                (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le))
          _ ≤ ∑ E ∈ H_U, ∑ _w ∈ E, (2 * D) :=
              Finset.sum_le_sum fun E hE => Finset.sum_le_sum fun w hw =>
                hdeg_2D w (hH_sub E (Finset.mem_filter.mp hE).1 hw)
          _ = ∑ E ∈ H_U, (k * (2 * D)) := by
              refine Finset.sum_congr rfl fun E hE => ?_
              rw [Finset.sum_const, smul_eq_mul, hH_unif E (Finset.mem_filter.mp hE).1]
          _ = H_U.card * (k * (2 * D)) := by simp
          _ ≤ (2 * D ^ 2) * (k * (2 * D)) := Nat.mul_le_mul_right _ hHU_le
          _ = 4 * k * D ^ 3 := by ring
      have hD23 : 2 * D ^ 2 ≤ k * D ^ 3 := by
        have h1 : 2 ≤ k := by omega
        have h2 : D ^ 2 ≤ D ^ 3 := by
          calc D ^ 2 = D ^ 2 * 1 := (mul_one _).symm
            _ ≤ D ^ 2 * D := Nat.mul_le_mul_left _ hD
            _ = D ^ 3 := by ring
        calc 2 * D ^ 2 ≤ k * D ^ 2 := Nat.mul_le_mul_right _ h1
          _ ≤ k * D ^ 3 := Nat.mul_le_mul_left _ h2
      change (H_U ∪ H_U2).card ≤ 5 * k * D ^ 3
      calc (H_U ∪ H_U2).card ≤ H_U.card + H_U2.card := Finset.card_union_le _ _
        _ ≤ 2 * D ^ 2 + 4 * k * D ^ 3 := Nat.add_le_add hHU_le hHU2_le
        _ ≤ k * D ^ 3 + 4 * k * D ^ 3 := Nat.add_le_add_right hD23 _
        _ = 5 * k * D ^ 3 := by ring
  -- Step 2: Each edge `e : ↥H` belongs to `≤ 4 * k^3 * D` sets `Dep j`
  have hEdge_deg : ∀ e : ↥H,
      (Finset.univ.filter (fun j : ↥W ⊕ ↥T => e ∈ Dep j)).card ≤ 4 * k ^ 3 * D := by
    intro e
    set F := e.1
    have hFH : F ∈ H := e.2
    have hF_card : F.card = k := hH_unif F hFH
    let S_v : Finset ↥W := Finset.univ.filter (fun v : ↥W => F ∈ depV H v.1)
    let S_U : Finset ↥T := Finset.univ.filter (fun U : ↥T => F ∈ depU H W U.1)
    have hsplit : (Finset.univ.filter (fun j : ↥W ⊕ ↥T => e ∈ Dep j)).card ≤ S_v.card + S_U.card := by
      have hsub : Finset.univ.filter (fun j : ↥W ⊕ ↥T => e ∈ Dep j) ⊆
          S_v.image Sum.inl ∪ S_U.image Sum.inr := by
        intro j hj
        have hmem : e ∈ Dep j := (Finset.mem_filter.mp hj).2
        rcases j with v | U
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_liftH.mp hmem⟩, rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_liftH.mp hmem⟩, rfl⟩)
      exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
    have hSv : S_v.card ≤ 2 * k ^ 2 * D := by
      have hinj : S_v.card ≤ (F.biUnion (fun w => (H.filter (fun E => w ∈ E)).biUnion id)).card := by
        refine Finset.card_le_card_of_injOn (fun v : ↥W => v.1) ?_ ?_
        · intro v hv
          rcases Finset.mem_filter.mp (Finset.mem_filter.mp hv).2 with ⟨_, E, hEv, ⟨w, hw⟩⟩
          rcases Finset.mem_filter.mp hEv with ⟨hEH, hvE⟩
          rcases Finset.mem_inter.mp hw with ⟨hwEr, hwF⟩
          exact Finset.mem_biUnion.mpr ⟨w, hwF, Finset.mem_biUnion.mpr
            ⟨E, Finset.mem_filter.mpr ⟨hEH, Finset.mem_of_mem_erase hwEr⟩, hvE⟩⟩
        · intro v₁ _ v₂ _ h; exact Subtype.ext h
      calc S_v.card
          ≤ ∑ w ∈ F, ∑ E ∈ H.filter (fun E => w ∈ E), E.card :=
            hinj.trans (Finset.card_biUnion_le.trans
              (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le))
        _ = ∑ w ∈ F, ∑ _E ∈ H.filter (fun E => w ∈ E), k :=
            Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun E hE =>
              hH_unif E (Finset.mem_filter.mp hE).1
        _ ≤ ∑ _w ∈ F, ((2 * D) * k) :=
            Finset.sum_le_sum fun w hw => by
              rw [Finset.sum_const, smul_eq_mul]
              exact Nat.mul_le_mul_right k (hdeg_2D w (hH_sub F hFH hw))
        _ = k * ((2 * D) * k) := by rw [Finset.sum_const, smul_eq_mul, hF_card]
        _ = 2 * k ^ 2 * D := by ring
    have hSU : S_U.card ≤ 3 * k ^ 3 * D := by
      let B1 : Finset (Finset α) := F.biUnion (fun u => T.filter (fun U => u ∈ U))
      let B2 : Finset (Finset α) :=
        F.biUnion (fun w => (H.filter (fun E => w ∈ E)).biUnion
          (fun E => E.biUnion (fun u => T.filter (fun U => u ∈ U))))
      have hinj : S_U.card ≤ (B1 ∪ B2).card := by
        refine Finset.card_le_card_of_injOn (fun U : ↥T => U.1) ?_ ?_
        · intro U hU
          have hmem := (Finset.mem_filter.mp hU).2
          rcases Finset.mem_union.mp hmem with h1 | h2
          · rcases Finset.mem_filter.mp h1 with ⟨_, ⟨u, hu⟩⟩
            rcases Finset.mem_inter.mp hu with ⟨huF, huUW⟩
            exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
              ⟨u, huF, Finset.mem_filter.mpr ⟨U.2, (Finset.mem_inter.mp huUW).1⟩⟩)
          · rcases Finset.mem_filter.mp h2 with ⟨_, E, hEHU, ⟨w, hw⟩⟩
            rcases Finset.mem_filter.mp hEHU with ⟨hEH, ⟨u, hu⟩⟩
            rcases Finset.mem_inter.mp hw with ⟨hwE, hwF⟩
            rcases Finset.mem_inter.mp hu with ⟨huE, huUW⟩
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
              ⟨w, hwF, Finset.mem_biUnion.mpr ⟨E, Finset.mem_filter.mpr ⟨hEH, hwE⟩,
                Finset.mem_biUnion.mpr ⟨u, huE, Finset.mem_filter.mpr
                  ⟨U.2, (Finset.mem_inter.mp huUW).1⟩⟩⟩⟩)
        · intro U₁ _ U₂ _ h; exact Subtype.ext h
      have hB1 : B1.card ≤ k ^ 2 := by
        calc B1.card ≤ ∑ u ∈ F, (T.filter (fun U => u ∈ U)).card := Finset.card_biUnion_le
          _ ≤ ∑ _u ∈ F, k := Finset.sum_le_sum fun u _ => hT_deg u
          _ = k ^ 2 := by rw [Finset.sum_const, smul_eq_mul, hF_card]; ring
      have hB2 : B2.card ≤ 2 * k ^ 3 * D := by
        calc B2.card
            ≤ ∑ w ∈ F, ∑ E ∈ H.filter (fun E => w ∈ E), ∑ u ∈ E, (T.filter (fun U => u ∈ U)).card :=
              Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ =>
                Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le))
          _ ≤ ∑ w ∈ F, ∑ E ∈ H.filter (fun E => w ∈ E), ∑ _u ∈ E, k :=
              Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
                Finset.sum_le_sum fun u _ => hT_deg u
          _ = ∑ w ∈ F, ∑ _E ∈ H.filter (fun E => w ∈ E), k ^ 2 :=
              Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun E hE => by
                rw [Finset.sum_const, smul_eq_mul, hH_unif E (Finset.mem_filter.mp hE).1]; ring
          _ ≤ ∑ _w ∈ F, ((2 * D) * k ^ 2) :=
              Finset.sum_le_sum fun w hw => by
                rw [Finset.sum_const, smul_eq_mul]
                exact Nat.mul_le_mul_right (k ^ 2) (hdeg_2D w (hH_sub F hFH hw))
          _ = k * ((2 * D) * k ^ 2) := by rw [Finset.sum_const, smul_eq_mul, hF_card]
          _ = 2 * k ^ 3 * D := by ring
      have hk2_le : k ^ 2 ≤ k ^ 3 * D := by
        have h1 : k ^ 2 ≤ k ^ 3 := by
          calc k ^ 2 = k ^ 2 * 1 := (mul_one _).symm
            _ ≤ k ^ 2 * k := Nat.mul_le_mul_left _ (by omega)
            _ = k ^ 3 := by ring
        calc k ^ 2 ≤ k ^ 3 := h1
          _ = k ^ 3 * 1 := (mul_one _).symm
          _ ≤ k ^ 3 * D := Nat.mul_le_mul_left _ hD
      calc S_U.card ≤ (B1 ∪ B2).card := hinj
        _ ≤ B1.card + B2.card := Finset.card_union_le _ _
        _ ≤ k ^ 2 + 2 * k ^ 3 * D := Nat.add_le_add hB1 hB2
        _ ≤ k ^ 3 * D + 2 * k ^ 3 * D := Nat.add_le_add_right hk2_le _
        _ = 3 * k ^ 3 * D := by ring
    have h2k2 : 2 * k ^ 2 * D ≤ k ^ 3 * D := by
      have h1 : 2 * k ^ 2 ≤ k ^ 3 := by
        calc 2 * k ^ 2 ≤ k * k ^ 2 := Nat.mul_le_mul_right _ (by omega)
          _ = k ^ 3 := by ring
      exact Nat.mul_le_mul_right D h1
    calc (Finset.univ.filter (fun j : ↥W ⊕ ↥T => e ∈ Dep j)).card
        ≤ S_v.card + S_U.card := hsplit
      _ ≤ 2 * k ^ 2 * D + 3 * k ^ 3 * D := Nat.add_le_add hSv hSU
      _ ≤ k ^ 3 * D + 3 * k ^ 3 * D := Nat.add_le_add_right h2k2 _
      _ = 4 * k ^ 3 * D := by ring
  -- Step 3: Combine Step 1 and Step 2
  have hcov : Finset.univ.filter (fun j : ↥W ⊕ ↥T => j ≠ i ∧ ¬ Disjoint (Dep i) (Dep j)) ⊆
      (Dep i).biUnion (fun e => Finset.univ.filter (fun j : ↥W ⊕ ↥T => e ∈ Dep j)) := by
    intro j hj
    rcases (Finset.mem_filter.mp hj).2 with ⟨_, hnd⟩
    rcases Finset.not_disjoint_iff.mp hnd with ⟨e, he1, he2⟩
    exact Finset.mem_biUnion.mpr ⟨e, he1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he2⟩⟩
  calc (Finset.univ.filter (fun j : ↥W ⊕ ↥T => j ≠ i ∧ ¬ Disjoint (Dep i) (Dep j))).card
      ≤ ∑ e ∈ Dep i, (Finset.univ.filter (fun j : ↥W ⊕ ↥T => e ∈ Dep j)).card :=
        (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ Dep i, (4 * k ^ 3 * D) := Finset.sum_le_sum fun e _ => hEdge_deg e
    _ = (Dep i).card * (4 * k ^ 3 * D) := by simp
    _ ≤ (5 * k * D ^ 3) * (4 * k ^ 3 * D) := Nat.mul_le_mul_right _ hDep_card
    _ = 20 * k ^ 4 * D ^ 4 := by ring

/-- One Rödl nibble round: finds a matching `M_bite ⊆ H` and surviving `(W', H')`. -/
theorem nibble_round {α : Type*} [DecidableEq α]
    (W : Finset α) (H : Finset (Finset α)) (T : Finset (Finset α))
    (k D : ℕ) (Dt ε δ η ut : ℝ)
    (hk : 4 ≤ k) (hD : 1 ≤ D)
    (hH_sub : ∀ E ∈ H, E ⊆ W)
    (hH_unif : ∀ E ∈ H, E.card = k)
    (hH_lin : ∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).card ≤ 1)
    (hT_deg : ∀ v : α, (T.filter (fun U => v ∈ U)).card ≤ k)
    (hε0 : 0 < ε) (hε_small : 4 * (k : ℝ) * ε ≤ 1 / 4)
    (hδ0 : 0 ≤ δ) (hδ_small : δ ≤ 1 / 40)
    (hη0 : 0 < η) (hη_small : η ≤ ε ^ 2)
    (hut0 : 0 ≤ ut) (hut1 : ut ≤ 1)
    (hDt_pos : 0 < Dt) (hDt_le : Dt ≤ (D : ℝ))
    (hDt_err : 4 * (k : ℝ) * ε / Dt ≤ η)
    (hdeg_lo : ∀ v ∈ W, (1 - δ) * Dt ≤ ((H.filter (fun E => v ∈ E)).card : ℝ))
    (hdeg_hi : ∀ v ∈ W, ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ (1 + δ) * Dt)
    (hU_hi : ∀ U ∈ T, ((U ∩ W).card : ℝ) ≤ ut * (D : ℝ))
    (hLLL : 28 * Real.exp (-(η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt) *
      (((20 * k ^ 4 * D ^ 4 : ℕ) : ℝ) + 1) ≤ 1) :
    ∃ (M_bite : Finset (Finset α)) (W' : Finset α) (H' : Finset (Finset α)),
      M_bite ⊆ H ∧
      (∀ E ∈ M_bite, ∀ F ∈ M_bite, E ≠ F → Disjoint E F) ∧
      W' ⊆ W ∧
      M_bite.biUnion id ⊆ W \ W' ∧
      H' ⊆ H ∧
      (∀ E ∈ H', E ⊆ W') ∧
      (∀ v ∈ W',
        (1 - (δ * (1 + 3 * (k : ℝ) * ε) + 2 * η)) * (Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Dt) ≤
          ((H'.filter (fun E => v ∈ E)).card : ℝ) ∧
        ((H'.filter (fun E => v ∈ E)).card : ℝ) ≤
          (1 + (δ * (1 + 3 * (k : ℝ) * ε) + 2 * η)) * (Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Dt)) ∧
      (∀ U ∈ T, ((U ∩ W').card : ℝ) ≤ (ut * Real.exp (-(3 / 4 : ℝ) * ε) + η) * (D : ℝ)) ∧
      (∀ U ∈ T, (((U ∩ (W \ W')) \ M_bite.biUnion id).card : ℝ) ≤
        (14 * (k : ℝ) ^ 2 * ε ^ 2 + 4 * (k : ℝ) ^ 2 * η) * (D : ℝ)) := by
  let Q : ℕ := Nat.floor (Dt / ε) + 1
  have hQ : 0 < Q := Nat.succ_pos _
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hp_hi : 1 / (Q : ℝ) ≤ ε / Dt := by
    have hlt : Dt / ε < (Q : ℝ) := by
      simp only [Q, Nat.cast_add, Nat.cast_one]; exact Nat.lt_floor_add_one (Dt / ε)
    rw [div_le_div_iff₀ hQ_pos hDt_pos]
    have h1 := (div_lt_iff₀ hε0).mp hlt
    linarith
  have hp_lo : ε / Dt - ε ^ 2 / Dt ^ 2 ≤ 1 / (Q : ℝ) := by
    have hle : (Q : ℝ) ≤ Dt / ε + 1 := by
      simp only [Q, Nat.cast_add, Nat.cast_one]
      linarith [Nat.floor_le (div_nonneg hDt_pos.le hε0.le)]
    have hDtε : 0 < Dt + ε := by linarith
    have h1 : ε / (Dt + ε) ≤ 1 / (Q : ℝ) := by
      rw [div_le_div_iff₀ hDtε hQ_pos]
      have h2 := mul_le_mul_of_nonneg_left hle hε0.le
      have h3 : ε * (Dt / ε + 1) = Dt + ε := by field_simp
      linarith
    have h2 : ε / Dt - ε ^ 2 / Dt ^ 2 ≤ ε / (Dt + ε) := by
      rw [show ε / Dt - ε ^ 2 / Dt ^ 2 = ε * (Dt - ε) / Dt ^ 2 by field_simp]
      rw [div_le_div_iff₀ (sq_pos_of_pos hDt_pos) hDtε]
      nlinarith only [sq_nonneg ε, hε0]
    exact h2.trans h1
  let Dt1 : ℝ := Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Dt
  let Bad : ↥W ⊕ ↥T → Finset (↥H → Fin Q) :=
    Sum.elim (fun v => degBad H Q Dt1 η v.1) (fun U => targetBad W H k Q D ε η U.1)
  let Dep : ↥W ⊕ ↥T → Finset ↥H :=
    Sum.elim (fun v => liftH H (depV H v.1)) (fun U => liftH H (depU H W U.1))
  let p_bad : ℝ := 7 * Real.exp (-(η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt)
  have hdeg_all : ∀ v : ↥W,
      DependsOn (Dep (Sum.inl v)) (Bad (Sum.inl v)) ∧
      ((Bad (Sum.inl v)).card : ℝ) ≤ p_bad * (Fintype.card (↥H → Fin Q) : ℝ) := by
    intro v
    have h := deg_bad_bound W H k Q Dt ε δ η hk hQ hH_sub hH_unif hH_lin hε0 hε_small
      hδ0 hδ_small hη0 hη_small hDt_pos hDt_err hp_hi hp_lo hdeg_lo hdeg_hi v.1 v.2
    refine ⟨h.1, h.2.1.trans ?_⟩
    have hexp_nn : 0 ≤ Real.exp (-(η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt) := (Real.exp_pos _).le
    have hcard_nn : (0 : ℝ) ≤ (Fintype.card (↥H → Fin Q) : ℝ) := Nat.cast_nonneg _
    dsimp [p_bad]; nlinarith
  have hU_leD : ∀ U ∈ T, ((U ∩ W).card : ℝ) ≤ (D : ℝ) := fun U hU =>
    (hU_hi U hU).trans (by nlinarith [Nat.cast_nonneg (α := ℝ) D])
  have htgt_all : ∀ U : ↥T,
      DependsOn (Dep (Sum.inr U)) (Bad (Sum.inr U)) ∧
      ((Bad (Sum.inr U)).card : ℝ) ≤ p_bad * (Fintype.card (↥H → Fin Q) : ℝ) := by
    intro U
    have h := target_bad_bound W H k Q D Dt ε δ η ut hk hQ hD hH_sub hH_unif hε0 hε_small
      hδ0 hδ_small hη0 hη_small hut0 hut1 hDt_pos hDt_le hDt_err hp_hi hp_lo hdeg_lo hdeg_hi
      U.1 (hU_hi U.1 U.2)
    exact ⟨h.1, h.2.1⟩
  have hlll := lll_of_dependsOn Bad Dep p_bad (20 * k ^ 4 * D ^ 4)
    (by dsimp [p_bad]; positivity)
    (by dsimp [p_bad]; linarith)
    (fun i => by rcases i with v | U; exact (hdeg_all v).1; exact (htgt_all U).1)
    (fun i => by rcases i with v | U; exact (hdeg_all v).2; exact (htgt_all U).2)
    (dep_deg_bound W H T k D Dt δ hk hD hH_sub hH_unif hT_deg hδ0 hδ_small hDt_pos hDt_le
      hdeg_hi hU_leD)
  obtain ⟨ω, hω⟩ := hlll
  refine ⟨biteMatch ω, W \ (selSet ω).biUnion id,
    H.filter (fun E => E ⊆ W \ (selSet ω).biUnion id), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Finset.filter_subset _ _).trans (selSet_subset ω)
  · intro E hE F hF hne
    exact (Finset.mem_filter.mp hE).2 F (Finset.mem_filter.mp hF).1 hne.symm
  · exact Finset.sdiff_subset
  · intro w hw
    rcases Finset.mem_biUnion.mp hw with ⟨E, hEM, hwE⟩
    have hES : E ∈ selSet ω := (Finset.mem_filter.mp hEM).1
    exact Finset.mem_sdiff.mpr ⟨hH_sub E (selSet_subset ω hES) hwE,
      fun hw' => (Finset.mem_sdiff.mp hw').2 (Finset.mem_biUnion.mpr ⟨E, hES, hwE⟩)⟩
  · exact Finset.filter_subset _ _
  · intro E hE; exact (Finset.mem_filter.mp hE).2
  · intro v hv'
    have hvW : v ∈ W := (Finset.mem_sdiff.mp hv').1
    have h := deg_bad_bound W H k Q Dt ε δ η hk hQ hH_sub hH_unif hH_lin hε0 hε_small
      hδ0 hδ_small hη0 hη_small hDt_pos hDt_err hp_hi hp_lo hdeg_lo hdeg_hi v hvW
    exact h.2.2 ω (hω (Sum.inl ⟨v, hvW⟩)) hv'
  · intro U hU
    have h := target_bad_bound W H k Q D Dt ε δ η ut hk hQ hD hH_sub hH_unif hε0 hε_small
      hδ0 hδ_small hη0 hη_small hut0 hut1 hDt_pos hDt_le hDt_err hp_hi hp_lo hdeg_lo hdeg_hi
      U (hU_hi U hU)
    exact (h.2.2 ω (hω (Sum.inr ⟨U, hU⟩))).1
  · intro U hU
    have h := target_bad_bound W H k Q D Dt ε δ η ut hk hQ hD hH_sub hH_unif hε0 hε_small
      hδ0 hδ_small hη0 hη_small hut0 hut1 hDt_pos hDt_le hDt_err hp_hi hp_lo hdeg_lo hdeg_hi
      U (hU_hi U hU)
    exact (h.2.2 ω (hω (Sum.inr ⟨U, hU⟩))).2

end NibbleRound

/- ### Section 4: Multi-Round Rödl Nibble Iteration (`locally_covering_matching`) -/

section MatchingTheorem

/-- Recurrence for degree-error parameter `δ_t`. -/
noncomputable def deltaSeq (k : ℕ) (ε η : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => deltaSeq k ε η t * (1 + 3 * (k : ℝ) * ε) + 2 * η

/-- Recurrence for surviving-target-fraction parameter `u_t`. -/
noncomputable def uSeq (ε η : ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => uSeq ε η t * Real.exp (-(3 / 4 : ℝ) * ε) + η

lemma deltaSeq_bounds (k : ℕ) (ε η : ℝ) (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η) :
    ∀ t : ℕ, 0 ≤ deltaSeq k ε η t ∧
      deltaSeq k ε η t ≤ 2 * η * (t : ℝ) * (1 + 3 * (k : ℝ) * ε) ^ t
  | 0 => by simp [deltaSeq]
  | t + 1 => by
    obtain ⟨h0, hle⟩ := deltaSeq_bounds k ε η hε0 hη0 t
    have hfac1 : (1 : ℝ) ≤ 1 + 3 * (k : ℝ) * ε := by
      have : (0 : ℝ) ≤ 3 * (k : ℝ) * ε := by positivity
      linarith
    have hpow1 : (1 : ℝ) ≤ (1 + 3 * (k : ℝ) * ε) ^ (t + 1) := one_le_pow₀ hfac1
    refine ⟨by simp only [deltaSeq]; positivity, ?_⟩
    simp only [deltaSeq, Nat.cast_add, Nat.cast_one]
    calc deltaSeq k ε η t * (1 + 3 * (k : ℝ) * ε) + 2 * η
        ≤ (2 * η * (t : ℝ) * (1 + 3 * (k : ℝ) * ε) ^ t) * (1 + 3 * (k : ℝ) * ε) +
            2 * η * (1 + 3 * (k : ℝ) * ε) ^ (t + 1) := by
          refine add_le_add (mul_le_mul_of_nonneg_right hle (by linarith)) ?_
          calc 2 * η = 2 * η * 1 := (mul_one _).symm
            _ ≤ 2 * η * (1 + 3 * (k : ℝ) * ε) ^ (t + 1) :=
                mul_le_mul_of_nonneg_left hpow1 (by positivity)
      _ = 2 * η * ((t : ℝ) + 1) * (1 + 3 * (k : ℝ) * ε) ^ (t + 1) := by
          rw [pow_succ]; ring

lemma uSeq_bounds (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 16) (hη0 : 0 ≤ η) (hη_sq : η ≤ ε ^ 2) :
    ∀ t : ℕ, 0 ≤ uSeq ε η t ∧ uSeq ε η t ≤ 1 ∧
      uSeq ε η t ≤ Real.exp (-(3 / 4 : ℝ) * (t : ℝ) * ε) + (t : ℝ) * η
  | 0 => by simp [uSeq]
  | t + 1 => by
    obtain ⟨h0, h1, hle⟩ := uSeq_bounds ε η hε0 hε1 hη0 hη_sq t
    have hexp_le1 : Real.exp (-(3 / 4 : ℝ) * ε) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hstep1 : Real.exp (-(3 / 4 : ℝ) * ε) + η ≤ 1 := by
      have hpos : (0 : ℝ) < 1 + (3 / 4 : ℝ) * ε := by linarith
      have hinv : Real.exp (-(3 / 4 : ℝ) * ε) ≤ (1 + (3 / 4 : ℝ) * ε)⁻¹ := by
        rw [show -(3 / 4 : ℝ) * ε = -((3 / 4 : ℝ) * ε) by ring, Real.exp_neg]
        exact inv_anti₀ hpos (by linarith [Real.add_one_le_exp ((3 / 4 : ℝ) * ε)])
      have hη_le : η ≤ (3 / 8 : ℝ) * ε := hη_sq.trans (by nlinarith only [hε0, hε1])
      have hgap : (3 / 8 : ℝ) * ε ≤ 1 - (1 + (3 / 4 : ℝ) * ε)⁻¹ := by
        rw [show 1 - (1 + (3 / 4 : ℝ) * ε)⁻¹ = (3 / 4 : ℝ) * ε / (1 + (3 / 4 : ℝ) * ε) by
          field_simp; ring]
        rw [le_div_iff₀ hpos]
        nlinarith only [hε0, hε1]
      linarith only [hinv, hη_le, hgap]
    refine ⟨by simp only [uSeq]; positivity, ?_, ?_⟩
    · simp only [uSeq]
      calc uSeq ε η t * Real.exp (-(3 / 4 : ℝ) * ε) + η
          ≤ 1 * Real.exp (-(3 / 4 : ℝ) * ε) + η :=
            add_le_add (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) le_rfl
        _ ≤ 1 := by linarith only [hstep1]
    · simp only [uSeq, Nat.cast_add, Nat.cast_one]
      calc uSeq ε η t * Real.exp (-(3 / 4 : ℝ) * ε) + η
          ≤ (Real.exp (-(3 / 4 : ℝ) * (t : ℝ) * ε) + (t : ℝ) * η) * Real.exp (-(3 / 4 : ℝ) * ε) + η :=
            add_le_add (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le) le_rfl
        _ = Real.exp (-(3 / 4 : ℝ) * ((t : ℝ) + 1) * ε) +
              (t : ℝ) * η * Real.exp (-(3 / 4 : ℝ) * ε) + η := by
            rw [add_mul, ← Real.exp_add]; congr 2; ring
        _ ≤ Real.exp (-(3 / 4 : ℝ) * ((t : ℝ) + 1) * ε) + (t : ℝ) * η * 1 + η := by
            have hnn : (0 : ℝ) ≤ (t : ℝ) * η := by positivity
            linarith only [mul_le_mul_of_nonneg_left hexp_le1 hnn]
        _ = Real.exp (-(3 / 4 : ℝ) * ((t : ℝ) + 1) * ε) + ((t : ℝ) + 1) * η := by ring

/-- Pippenger–Spencer locally covering matching theorem for all uniformities `k = s + 1 ≥ 4`. -/
theorem locally_covering_matching :
    ∀ s : ℕ, 3 ≤ s → ∃ D₀ : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α] (D : ℕ), D₀ ≤ D →
      ∀ (G T : Finset (Finset α)), (∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ E ∈ G, E.card = s + 1) → (∀ x, (G.filter fun E => x ∈ E).card = D) →
      (∀ U ∈ T, U.card ≤ D) → (∀ x, (T.filter fun U => x ∈ U).card ≤ s + 1) →
      ∃ M : Finset (Finset α), M ⊆ G ∧ (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
        ∀ U ∈ T, (U \ M.biUnion id).card ≤ D / s := by
  intro s hs
  let k : ℕ := s + 1
  have hk : 4 ≤ k := by omega
  have hk_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk_real]
  have hk3 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := by nlinarith only [hk_real, hk2]
  let M_param : ℕ := 400 * k ^ 4
  have hM_pos : (0 : ℝ) < (M_param : ℝ) := by dsimp [M_param]; positivity
  let ε : ℝ := 1 / (M_param : ℝ)
  have hε0 : 0 < ε := one_div_pos.mpr hM_pos
  have hε_small : 4 * (k : ℝ) * ε ≤ 1 / 4 := by
    dsimp [ε, M_param]
    rw [show 4 * (k : ℝ) * (1 / ((400 * k ^ 4 : ℕ) : ℝ)) = 4 * (k : ℝ) / ((400 * k ^ 4 : ℕ) : ℝ) by ring]
    rw [div_le_iff₀ (by positivity)]
    push_cast
    have : (1 : ℝ) ≤ (k : ℝ) ^ 3 := hk3
    nlinarith only [hk_real, this]
  have hε_le16 : ε ≤ 1 / 16 := by nlinarith only [hk_real, hε0, hε_small]
  let R : ℕ := 6 * k * M_param
  have hR_pos : (0 : ℝ) < (R : ℝ) := by dsimp [R]; positivity
  have hR_eps : (R : ℝ) * ε = 6 * (k : ℝ) := by
    simp only [R, ε, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hM_pos.ne']
  let η : ℝ := 1 / (1000 * (k : ℝ) ^ 3 * (R : ℝ) * Real.exp (24 * (k : ℝ) ^ 2))
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hη_small : η ≤ ε ^ 2 := by
    simp only [η, ε, one_div, inv_pow]
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    have hexp1 : (1 : ℝ) ≤ Real.exp (24 * (k : ℝ) ^ 2) := Real.one_le_exp (by positivity)
    have h1 : (M_param : ℝ) ^ 2 ≤ 1000 * (k : ℝ) ^ 3 * (R : ℝ) := by
      simp only [M_param, R, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      have h8 : (0 : ℝ) ≤ (k : ℝ) ^ 8 := by positivity
      linarith [show (400 * (k : ℝ) ^ 4) ^ 2 = 160000 * (k : ℝ) ^ 8 by ring,
                show 1000 * (k : ℝ) ^ 3 * (6 * (k : ℝ) * (400 * (k : ℝ) ^ 4)) =
                  2400000 * (k : ℝ) ^ 8 by ring]
    calc (M_param : ℝ) ^ 2 = (M_param : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (1000 * (k : ℝ) ^ 3 * (R : ℝ)) * Real.exp (24 * (k : ℝ) ^ 2) :=
          mul_le_mul h1 hexp1 zero_le_one (by positivity)
  let c_D : ℝ := (η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Real.exp (-(6 * (k : ℝ) ^ 2))
  have hcD_pos : 0 < c_D := by dsimp [c_D]; positivity
  let D₁ : ℕ := Nat.ceil (4 * (k : ℝ) * ε * Real.exp (6 * (k : ℝ) ^ 2) / η) + 1
  let D₂ : ℕ := Nat.ceil (120 * 28 * (20 * (k : ℝ) ^ 4 + 1) / c_D ^ 5) + 1
  refine ⟨max 1 (max D₁ D₂), ?_⟩
  intro α _ _ D hD_ge G T hG_lin hG_unif hG_reg hT_card hT_deg
  have hD1 : 1 ≤ D := (le_max_left _ _).trans hD_ge
  have hD_D1 : D₁ ≤ D := ((le_max_left _ _).trans (le_max_right _ _)).trans hD_ge
  have hD_D2 : D₂ ≤ D := ((le_max_right _ _).trans (le_max_right _ _)).trans hD_ge
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  let Dt_seq : ℕ → ℝ := fun t => Real.exp (-((k - 1 : ℕ) : ℝ) * (t : ℝ) * ε) * (D : ℝ)
  have hDt_bounds : ∀ t ≤ R,
      Real.exp (-(6 * (k : ℝ) ^ 2)) * (D : ℝ) ≤ Dt_seq t ∧ Dt_seq t ≤ (D : ℝ) := by
    intro t ht
    constructor
    · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hD_pos.le
      have htR : (t : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr ht
      have hk1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
      have h1 : ((k - 1 : ℕ) : ℝ) * (t : ℝ) * ε ≤ (k : ℝ) * (R : ℝ) * ε :=
        mul_le_mul_of_nonneg_right (mul_le_mul hk1 htR (Nat.cast_nonneg _) hk_pos.le) hε0.le
      have h2 : (k : ℝ) * (R : ℝ) * ε = 6 * (k : ℝ) ^ 2 := by
        calc (k : ℝ) * (R : ℝ) * ε = (k : ℝ) * ((R : ℝ) * ε) := by ring
          _ = (k : ℝ) * (6 * (k : ℝ)) := by rw [hR_eps]
          _ = 6 * (k : ℝ) ^ 2 := by ring
      linarith only [h1, h2]
    · calc Dt_seq t ≤ 1 * (D : ℝ) :=
            mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by
              have : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) * (t : ℝ) * ε := by positivity
              linarith)) hD_pos.le
        _ = (D : ℝ) := one_mul _
  have hdelta_le : ∀ t ≤ R, deltaSeq k ε η t ≤ 1 / 40 := by
    intro t ht
    have hb := (deltaSeq_bounds k ε η hε0.le hη0.le t).2
    have hpow_le : (1 + 3 * (k : ℝ) * ε) ^ t ≤ Real.exp (24 * (k : ℝ) ^ 2) := by
      calc (1 + 3 * (k : ℝ) * ε) ^ t
          ≤ (1 + 3 * (k : ℝ) * ε) ^ R :=
            pow_le_pow_right₀ (by linarith [show (0 : ℝ) ≤ 3 * (k : ℝ) * ε by positivity]) ht
        _ ≤ (Real.exp (3 * (k : ℝ) * ε)) ^ R :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (3 * (k : ℝ) * ε)]) R
        _ = Real.exp ((R : ℝ) * (3 * (k : ℝ) * ε)) := (Real.exp_nat_mul _ R).symm
        _ = Real.exp (18 * (k : ℝ) ^ 2) := by
            congr 1
            calc (R : ℝ) * (3 * (k : ℝ) * ε) = 3 * (k : ℝ) * ((R : ℝ) * ε) := by ring
              _ = 3 * (k : ℝ) * (6 * (k : ℝ)) := by rw [hR_eps]
              _ = 18 * (k : ℝ) ^ 2 := by ring
        _ ≤ Real.exp (24 * (k : ℝ) ^ 2) := Real.exp_le_exp.mpr (by nlinarith only [hk2])
    have htR : (t : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr ht
    calc deltaSeq k ε η t
        ≤ 2 * η * (t : ℝ) * (1 + 3 * (k : ℝ) * ε) ^ t := hb
      _ ≤ 2 * η * (R : ℝ) * Real.exp (24 * (k : ℝ) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left htR (by positivity)) hpow_le (by positivity) (by positivity)
      _ = 2 / (1000 * (k : ℝ) ^ 3) := by
          dsimp [η]; field_simp [(Real.exp_pos _).ne', hR_pos.ne', hk_pos.ne']
      _ ≤ 1 / 40 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith only [hk3]
  have hDt_err_all : ∀ t ≤ R, 4 * (k : ℝ) * ε / Dt_seq t ≤ η := by
    intro t ht
    have hDt_lo := (hDt_bounds t ht).1
    have hDt_pos : 0 < Dt_seq t := lt_of_lt_of_le (by positivity) hDt_lo
    have hD_ceil : 4 * (k : ℝ) * ε * Real.exp (6 * (k : ℝ) ^ 2) / η ≤ (D : ℝ) := by
      have h1 : (D₁ : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr hD_D1
      have h2 : 4 * (k : ℝ) * ε * Real.exp (6 * (k : ℝ) ^ 2) / η ≤ (Nat.ceil _ : ℝ) := Nat.le_ceil _
      dsimp [D₁] at h1; push_cast at h1; linarith only [h1, h2]
    rw [div_le_iff₀ hDt_pos]
    have h3 : 4 * (k : ℝ) * ε * Real.exp (6 * (k : ℝ) ^ 2) ≤ η * (D : ℝ) := by
      have := (div_le_iff₀ hη0).mp hD_ceil; linarith only [this]
    have h4 : 4 * (k : ℝ) * ε ≤ η * (Real.exp (-(6 * (k : ℝ) ^ 2)) * (D : ℝ)) := by
      have := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-(6 * (k : ℝ) ^ 2))).le
      have heq : Real.exp (6 * (k : ℝ) ^ 2) * Real.exp (-(6 * (k : ℝ) ^ 2)) = 1 := by
        rw [← Real.exp_add]; simp
      calc 4 * (k : ℝ) * ε = 4 * (k : ℝ) * ε * (Real.exp (6 * (k : ℝ) ^ 2) * Real.exp (-(6 * (k : ℝ) ^ 2))) := by
            rw [heq, mul_one]
        _ = 4 * (k : ℝ) * ε * Real.exp (6 * (k : ℝ) ^ 2) * Real.exp (-(6 * (k : ℝ) ^ 2)) := by ring
        _ ≤ η * (D : ℝ) * Real.exp (-(6 * (k : ℝ) ^ 2)) := this
        _ = η * (Real.exp (-(6 * (k : ℝ) ^ 2)) * (D : ℝ)) := by ring
    exact h4.trans (mul_le_mul_of_nonneg_left hDt_lo hη0.le)
  have hLLL_all : ∀ t ≤ R,
      28 * Real.exp (-(η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt_seq t) *
        (((20 * k ^ 4 * D ^ 4 : ℕ) : ℝ) + 1) ≤ 1 := by
    intro t ht
    have hDt_lo := (hDt_bounds t ht).1
    let x : ℝ := (η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt_seq t
    have hx_ge : c_D * (D : ℝ) ≤ x := by
      dsimp [x, c_D]
      calc (η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Real.exp (-(6 * (k : ℝ) ^ 2)) * (D : ℝ)
          = (η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * (Real.exp (-(6 * (k : ℝ) ^ 2)) * (D : ℝ)) := by ring
        _ ≤ (η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt_seq t :=
            mul_le_mul_of_nonneg_left hDt_lo (by positivity)
    have hexp_inv : Real.exp (-x) ≤ 120 / (c_D ^ 5 * (D : ℝ) ^ 5) := by
      have h5 : (c_D * (D : ℝ)) ^ 5 / 120 ≤ Real.exp x :=
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hx_ge 5) (by norm_num)).trans
          (exp_ge_pow_five_div (by positivity))
      rw [Real.exp_neg]
      have hpos5 : (0 : ℝ) < (c_D * (D : ℝ)) ^ 5 / 120 := by positivity
      calc (Real.exp x)⁻¹ ≤ ((c_D * (D : ℝ)) ^ 5 / 120)⁻¹ := inv_anti₀ hpos5 h5
        _ = 120 / (c_D ^ 5 * (D : ℝ) ^ 5) := by rw [inv_div, mul_pow]
    have hpoly : (((20 * k ^ 4 * D ^ 4 : ℕ) : ℝ) + 1) ≤ (20 * (k : ℝ) ^ 4 + 1) * (D : ℝ) ^ 4 := by
      push_cast
      have h1D4 : (1 : ℝ) ≤ (D : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hD1)
      linarith only [h1D4]
    have hD_ceil : 120 * 28 * (20 * (k : ℝ) ^ 4 + 1) / c_D ^ 5 ≤ (D : ℝ) := by
      have h1 : (D₂ : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr hD_D2
      have h2 : 120 * 28 * (20 * (k : ℝ) ^ 4 + 1) / c_D ^ 5 ≤ (Nat.ceil _ : ℝ) := Nat.le_ceil _
      dsimp [D₂] at h1; push_cast at h1; linarith only [h1, h2]
    have hneg : -(η ^ 2 / (32 * (k : ℝ) ^ 3 * ε)) * Dt_seq t = -x := by dsimp [x]; ring
    rw [hneg]
    calc 28 * Real.exp (-x) * (((20 * k ^ 4 * D ^ 4 : ℕ) : ℝ) + 1)
        ≤ 28 * (120 / (c_D ^ 5 * (D : ℝ) ^ 5)) * ((20 * (k : ℝ) ^ 4 + 1) * (D : ℝ) ^ 4) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp_inv (by norm_num)) hpoly (by positivity) (by positivity)
      _ = (120 * 28 * (20 * (k : ℝ) ^ 4 + 1) / c_D ^ 5) / (D : ℝ) := by
          field_simp [hcD_pos.ne', hD_pos.ne']
      _ ≤ 1 := (div_le_one hD_pos).mpr hD_ceil
  -- Induction over rounds `t ≤ R`
  have hiter : ∀ t : ℕ, t ≤ R →
      ∃ (M : Finset (Finset α)) (W : Finset α) (H : Finset (Finset α)),
        M ⊆ G ∧
        (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
        M.biUnion id ⊆ Finset.univ \ W ∧
        H ⊆ G ∧
        (∀ E ∈ H, E ⊆ W) ∧
        (∀ v ∈ W,
          (1 - deltaSeq k ε η t) * Dt_seq t ≤ ((H.filter (fun E => v ∈ E)).card : ℝ) ∧
          ((H.filter (fun E => v ∈ E)).card : ℝ) ≤ (1 + deltaSeq k ε η t) * Dt_seq t) ∧
        (∀ U ∈ T, ((U ∩ W).card : ℝ) ≤ uSeq ε η t * (D : ℝ)) ∧
        (∀ U ∈ T, (((U \ W) \ M.biUnion id).card : ℝ) ≤
          (t : ℝ) * (14 * (k : ℝ) ^ 2 * ε ^ 2 + 4 * (k : ℝ) ^ 2 * η) * (D : ℝ)) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨∅, Finset.univ, G, Finset.empty_subset G, by simp, by simp, Subset.rfl,
        fun _ _ _ _ => Finset.mem_univ _, ?_, ?_, ?_⟩
      · intro v _
        simp only [deltaSeq, Dt_seq, Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero, one_mul,
          sub_zero, add_zero, hG_reg v, le_refl, and_self]
      · intro U hU
        simp only [uSeq, Finset.inter_univ, one_mul]
        exact_mod_cast hT_card U hU
      · intro U _
        simp
    | succ t ih =>
      intro ht1
      have ht : t ≤ R := Nat.le_of_succ_le ht1
      obtain ⟨M_t, W_t, H_t, hM_sub, hM_disj, hM_W, hH_subG, hH_W, hdeg, hU_hi, hwaste_t⟩ := ih ht
      have hDt_lo := (hDt_bounds t ht).1
      have hDt_pos : 0 < Dt_seq t := lt_of_lt_of_le (by positivity) hDt_lo
      have hu_b := uSeq_bounds ε η hε0 hε_le16 hη0.le hη_small t
      obtain ⟨M_bite, W', H', hMb_H, hMb_disj, hW'_sub, hMb_diff, hH'_sub, hH'_W', hdeg', hU', hwaste'⟩ :=
        nibble_round W_t H_t T k D (Dt_seq t) ε (deltaSeq k ε η t) η (uSeq ε η t)
          hk hD1 hH_W
          (fun E hE => hG_unif E (hH_subG hE))
          (fun E hE F hF hne => hG_lin E (hH_subG hE) F (hH_subG hF) hne)
          hT_deg hε0 hε_small
          (deltaSeq_bounds k ε η hε0.le hη0.le t).1 (hdelta_le t ht)
          hη0 hη_small hu_b.1 hu_b.2.1 hDt_pos (hDt_bounds t ht).2 (hDt_err_all t ht)
          (fun v hv => (hdeg v hv).1) (fun v hv => (hdeg v hv).2) hU_hi (hLLL_all t ht)
      have hDt_step : Real.exp (-((k - 1 : ℕ) : ℝ) * ε) * Dt_seq t = Dt_seq (t + 1) := by
        simp only [Dt_seq, Nat.cast_add, Nat.cast_one]
        rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
      refine ⟨M_t ∪ M_bite, W', H',
        Finset.union_subset hM_sub (hMb_H.trans hH_subG), ?_, ?_,
        hH'_sub.trans hH_subG, hH'_W', ?_, ?_, ?_⟩
      · intro E hE F hF hne
        have hcross : ∀ A ∈ M_t, ∀ B ∈ M_bite, Disjoint A B := fun A hA B hB =>
          Finset.disjoint_left.mpr fun w hwA hwB =>
            (Finset.mem_sdiff.mp (hM_W (Finset.mem_biUnion.mpr ⟨A, hA, hwA⟩))).2
              (hH_W B (hMb_H hB) hwB)
        rcases Finset.mem_union.mp hE with hEt | hEb <;> rcases Finset.mem_union.mp hF with hFt | hFb
        · exact hM_disj E hEt F hFt hne
        · exact hcross E hEt F hFb
        · exact (hcross F hFt E hEb).symm
        · exact hMb_disj E hEb F hFb hne
      · intro w hw
        rw [Finset.union_biUnion] at hw
        rcases Finset.mem_union.mp hw with hwt | hwb
        · have h1 := hM_W hwt
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, fun hw' => (Finset.mem_sdiff.mp h1).2 (hW'_sub hw')⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, (Finset.mem_sdiff.mp (hMb_diff hwb)).2⟩
      · intro v hv'
        have hv := hdeg' v hv'
        rw [hDt_step] at hv
        exact hv
      · intro U hU
        simpa only [uSeq] using hU' U hU
      · intro U hU
        have hcov : (U \ W') \ (M_t ∪ M_bite).biUnion id ⊆
            ((U \ W_t) \ M_t.biUnion id) ∪ ((U ∩ (W_t \ W')) \ M_bite.biUnion id) := by
          intro u hu
          rcases Finset.mem_sdiff.mp hu with ⟨huUW', huM⟩
          rcases Finset.mem_sdiff.mp huUW' with ⟨huU, huW'⟩
          rw [Finset.union_biUnion, Finset.mem_union, not_or] at huM
          by_cases huWt : u ∈ W_t
          · exact Finset.mem_union_right _
              (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huU, Finset.mem_sdiff.mpr ⟨huWt, huW'⟩⟩, huM.2⟩)
          · exact Finset.mem_union_left _
              (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨huU, huWt⟩, huM.1⟩)
        have hcard : (((U \ W') \ (M_t ∪ M_bite).biUnion id).card : ℝ) ≤
            (((U \ W_t) \ M_t.biUnion id).card : ℝ) +
            (((U ∩ (W_t \ W')) \ M_bite.biUnion id).card : ℝ) := by
          exact_mod_cast (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
        push_cast
        linarith only [hcard, hwaste_t U hU, hwaste' U hU]
  -- Extract final matching at `t = R`
  obtain ⟨M, W_R, _, hM_sub, hM_disj, _, _, _, _, hUR, hwaste_R⟩ := hiter R le_rfl
  refine ⟨M, hM_sub, hM_disj, fun U hU => ?_⟩
  have hcov : U \ M.biUnion id ⊆ (U ∩ W_R) ∪ ((U \ W_R) \ M.biUnion id) := by
    intro u hu
    rcases Finset.mem_sdiff.mp hu with ⟨huU, huM⟩
    by_cases huW : u ∈ W_R
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨huU, huW⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨huU, huW⟩, huM⟩)
  have hcard : ((U \ M.biUnion id).card : ℝ) ≤
      ((U ∩ W_R).card : ℝ) + (((U \ W_R) \ M.biUnion id).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have huR_le : uSeq ε η R ≤ 1 / (4 * (k : ℝ)) + 1 / (4 * (k : ℝ)) := by
    have h1 := (uSeq_bounds ε η hε0 hε_le16 hη0.le hη_small R).2.2
    have hexp_R : Real.exp (-(3 / 4 : ℝ) * (R : ℝ) * ε) ≤ 1 / (4 * (k : ℝ)) := by
      have harg : -(3 / 4 : ℝ) * (R : ℝ) * ε = -((9 / 2 : ℝ) * (k : ℝ)) := by
        calc -(3 / 4 : ℝ) * (R : ℝ) * ε = -(3 / 4 : ℝ) * ((R : ℝ) * ε) := by ring
          _ = -(3 / 4 : ℝ) * (6 * (k : ℝ)) := by rw [hR_eps]
          _ = -((9 / 2 : ℝ) * (k : ℝ)) := by ring
      rw [harg, Real.exp_neg, one_div]
      refine inv_anti₀ (by positivity) ?_
      linarith [Real.add_one_le_exp ((9 / 2 : ℝ) * (k : ℝ))]
    have hRη : (R : ℝ) * η ≤ 1 / (4 * (k : ℝ)) := by
      have hexp1 : (1 : ℝ) ≤ Real.exp (24 * (k : ℝ) ^ 2) := Real.one_le_exp (by positivity)
      calc (R : ℝ) * η = 1 / (1000 * (k : ℝ) ^ 3 * Real.exp (24 * (k : ℝ) ^ 2)) := by
            dsimp [η]; field_simp [hR_pos.ne', hk_pos.ne', (Real.exp_pos _).ne']
        _ ≤ 1 / (4 * (k : ℝ)) := by
            rw [one_div_le_one_div (by positivity) (by positivity)]
            have h4 : 4 * (k : ℝ) ≤ 1000 * (k : ℝ) ^ 3 := by nlinarith only [hk_real, hk2]
            calc 4 * (k : ℝ) = 4 * (k : ℝ) * 1 := (mul_one _).symm
              _ ≤ (1000 * (k : ℝ) ^ 3) * Real.exp (24 * (k : ℝ) ^ 2) :=
                  mul_le_mul h4 hexp1 zero_le_one (by positivity)
    linarith only [h1, hexp_R, hRη]
  have hwaste_coef : (R : ℝ) * (14 * (k : ℝ) ^ 2 * ε ^ 2 + 4 * (k : ℝ) ^ 2 * η) ≤
      1 / (4 * (k : ℝ)) + 1 / (4 * (k : ℝ)) := by
    have h1 : (R : ℝ) * (14 * (k : ℝ) ^ 2 * ε ^ 2) ≤ 1 / (4 * (k : ℝ)) := by
      have heq : (R : ℝ) * (14 * (k : ℝ) ^ 2 * ε ^ 2) = 84 / (400 * (k : ℝ)) := by
        calc (R : ℝ) * (14 * (k : ℝ) ^ 2 * ε ^ 2)
            = 14 * (k : ℝ) ^ 2 * ((R : ℝ) * ε) * ε := by ring
          _ = 14 * (k : ℝ) ^ 2 * (6 * (k : ℝ)) * (1 / ((400 * k ^ 4 : ℕ) : ℝ)) := by
              rw [hR_eps]
          _ = 84 / (400 * (k : ℝ)) := by push_cast; field_simp [hk_pos.ne']; ring
      rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith only [hk_pos]
    have h2 : (R : ℝ) * (4 * (k : ℝ) ^ 2 * η) ≤ 1 / (4 * (k : ℝ)) := by
      have hexp1 : (1 : ℝ) ≤ Real.exp (24 * (k : ℝ) ^ 2) := Real.one_le_exp (by positivity)
      calc (R : ℝ) * (4 * (k : ℝ) ^ 2 * η)
          = 4 / (1000 * (k : ℝ) * Real.exp (24 * (k : ℝ) ^ 2)) := by
            dsimp [η]; field_simp [hR_pos.ne', hk_pos.ne', (Real.exp_pos _).ne']
        _ ≤ 1 / (4 * (k : ℝ)) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have h16 : 16 * (k : ℝ) ≤ 1000 * (k : ℝ) := by linarith only [hk_pos]
            calc 4 * (4 * (k : ℝ)) = 16 * (k : ℝ) * 1 := by ring
              _ ≤ (1000 * (k : ℝ)) * Real.exp (24 * (k : ℝ) ^ 2) :=
                  mul_le_mul h16 hexp1 zero_le_one (by positivity)
              _ = 1 * (1000 * (k : ℝ) * Real.exp (24 * (k : ℝ) ^ 2)) := by ring
    linarith only [h1, h2]
  have hreal_le : ((U \ M.biUnion id).card : ℝ) * (k : ℝ) ≤ (D : ℝ) := by
    have hsum_le : ((U \ M.biUnion id).card : ℝ) ≤ (1 / (k : ℝ)) * (D : ℝ) := by
      have htot : uSeq ε η R + (R : ℝ) * (14 * (k : ℝ) ^ 2 * ε ^ 2 + 4 * (k : ℝ) ^ 2 * η) ≤
          1 / (k : ℝ) := by
        have hsum4 : 1 / (4 * (k : ℝ)) + 1 / (4 * (k : ℝ)) +
            (1 / (4 * (k : ℝ)) + 1 / (4 * (k : ℝ))) = 1 / (k : ℝ) := by field_simp; ring
        linarith only [huR_le, hwaste_coef, hsum4]
      calc ((U \ M.biUnion id).card : ℝ)
          ≤ uSeq ε η R * (D : ℝ) +
              (R : ℝ) * (14 * (k : ℝ) ^ 2 * ε ^ 2 + 4 * (k : ℝ) ^ 2 * η) * (D : ℝ) :=
            by linarith only [hcard, hUR U hU, hwaste_R U hU]
        _ = (uSeq ε η R + (R : ℝ) * (14 * (k : ℝ) ^ 2 * ε ^ 2 + 4 * (k : ℝ) ^ 2 * η)) * (D : ℝ) := by
            ring
        _ ≤ (1 / (k : ℝ)) * (D : ℝ) := mul_le_mul_of_nonneg_right htot hD_pos.le
    calc ((U \ M.biUnion id).card : ℝ) * (k : ℝ)
        ≤ ((1 / (k : ℝ)) * (D : ℝ)) * (k : ℝ) := mul_le_mul_of_nonneg_right hsum_le hk_pos.le
      _ = (D : ℝ) := by field_simp [hk_pos.ne']
  have hnat_k : (U \ M.biUnion id).card * k ≤ D := by exact_mod_cast hreal_le
  have hnat_s : (U \ M.biUnion id).card * s ≤ D :=
    (Nat.mul_le_mul_left _ (Nat.le_succ s)).trans hnat_k
  exact (Nat.le_div_iff_mul_le (by omega : 0 < s)).mpr hnat_s

end MatchingTheorem

/- ### Section 5: Elementary Reduction and Final Theorem `OMA.solution` -/

section Reduction

theorem greedy_color {α : Type*} [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    (hsymm : ∀ a b, R a b → R b a) (m k : ℕ) (hk : k < m) :
    ∀ H : Finset α, (∀ A ∈ H, (H.filter (fun B => B ≠ A ∧ R A B)).card ≤ k) →
    ∃ c : α → Fin m, ∀ A ∈ H, ∀ B ∈ H, A ≠ B → R A B → c A ≠ c B := by
  intro H
  induction H using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨fun _ => ⟨0, by omega⟩, by simp⟩
  | insert a s ha ih =>
    intro hdeg
    obtain ⟨c, hc⟩ := ih (fun A hA => by
      refine le_trans (Finset.card_le_card ?_) (hdeg A (Finset.mem_insert_of_mem hA))
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_insert_of_mem hx.1, hx.2⟩)
    let N := (s.filter (fun B => R a B)).image c
    have hN : N.card < m := by
      have h1 : N.card ≤ (s.filter (fun B => R a B)).card := Finset.card_image_le
      have h2 : (s.filter (fun B => R a B)).card ≤ k := by
        refine le_trans (Finset.card_le_card ?_) (hdeg a (Finset.mem_insert_self a s))
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_insert_of_mem hx.1, fun h => ha (h ▸ hx.1), hx.2⟩
      omega
    have hex : ∃ x : Fin m, x ∉ N := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin m)) ⊆ N := fun x _ => hcon x
      have hcard := Finset.card_le_card hsub
      simp at hcard
      omega
    obtain ⟨x, hx⟩ := hex
    refine ⟨Function.update c a x, ?_⟩
    intro A hA B hB hAB hR
    have hne : ∀ y ∈ s, y ≠ a := fun y hy h => ha (h ▸ hy)
    rcases Finset.mem_insert.1 hA with hAa | hA'
    · subst hAa
      rcases Finset.mem_insert.1 hB with hBa | hB'
      · exact absurd hBa.symm hAB
      · rw [Function.update_self, Function.update_of_ne (hne B hB')]
        intro h
        exact hx (Finset.mem_image.2 ⟨B, Finset.mem_filter.2 ⟨hB', hR⟩, h.symm⟩)
    · rcases Finset.mem_insert.1 hB with hBa | hB'
      · subst hBa
        rw [Function.update_self, Function.update_of_ne (hne A hA')]
        intro h
        exact hx (Finset.mem_image.2 ⟨A, Finset.mem_filter.2 ⟨hA', hsymm _ _ hR⟩, h⟩)
      · rw [Function.update_of_ne (hne A hA'), Function.update_of_ne (hne B hB')]
        exact hc A hA' B hB' hAB hR

theorem nbr_card_le {n D : ℕ} (H : Finset (Finset (Fin n)))
    (hdeg : ∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) (A : Finset (Fin n)) (hA : A ∈ H) :
    (H.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty)).card ≤ A.card * (D - 1) := by
  have hsub : H.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty) ⊆
      A.biUnion (fun i => (H.filter (fun B => i ∈ B)).erase A) := by
    intro B hB
    simp only [Finset.mem_filter] at hB
    obtain ⟨hBH, hBA, ⟨i, hi⟩⟩ := hB
    rw [Finset.mem_inter] at hi
    exact Finset.mem_biUnion.2 ⟨i, hi.1, Finset.mem_erase.2 ⟨hBA, Finset.mem_filter.2 ⟨hBH, hi.2⟩⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  have h1 : ∀ i ∈ A, ((H.filter (fun B => i ∈ B)).erase A).card ≤ D - 1 := by
    intro i hi
    rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hA, hi⟩)]
    have := hdeg i
    omega
  simpa using Finset.sum_le_sum h1

theorem color_small_rank {n D r : ℕ} (H : Finset (Finset (Fin n)))
    (hrank : ∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ r)
    (hdeg : ∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) (m : ℕ) (hm : r * (D - 1) < m) :
    ∃ c : Finset (Fin n) → Fin m,
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  refine greedy_color (fun A B : Finset (Fin n) => (A ∩ B).Nonempty)
    (fun _ _ h => by rwa [Finset.inter_comm]) m (r * (D - 1)) hm H ?_
  intro A hA
  exact le_trans (nbr_card_le H hdeg A hA) (Nat.mul_le_mul_right _ (hrank A hA).2)

def copyEdge {α : Type*} {r : ℕ} (i : Fin r) (A : Finset α) : Finset (Fin r × α) :=
  A.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩

def fillEdge {α : Type*} (r : ℕ) (x : α) : Finset (Fin r × α) :=
  (Finset.univ : Finset (Fin r)).map ⟨fun i => (i, x), fun _ _ h => congrArg Prod.fst h⟩

lemma mem_copyEdge {α : Type*} {r : ℕ} {i j : Fin r} {A : Finset α} {x : α} :
    (j, x) ∈ copyEdge i A ↔ i = j ∧ x ∈ A := by
  rw [copyEdge, Finset.mem_map]
  change (∃ a ∈ A, (i, a) = (j, x)) ↔ _
  simp [and_left_comm]

lemma mem_fillEdge {α : Type*} {r : ℕ} {i : Fin r} {x y : α} :
    (i, y) ∈ fillEdge r x ↔ x = y := by
  rw [fillEdge, Finset.mem_map]
  change (∃ a ∈ (Finset.univ : Finset (Fin r)), (a, x) = (i, y)) ↔ _
  simp

lemma card_copyEdge {α : Type*} {r : ℕ} (i : Fin r) (A : Finset α) :
    (copyEdge i A).card = A.card := Finset.card_map _

lemma card_fillEdge {α : Type*} (r : ℕ) (x : α) :
    (fillEdge r x).card = r := by simp [fillEdge]

lemma copyEdge_injective {α : Type*} {r : ℕ} (i : Fin r) :
    Function.Injective (copyEdge (α := α) i) := fun _ _ h => Finset.map_injective _ h

def layers {α : Type*} [DecidableEq α] (r : ℕ) (H : Finset (Finset α)) :
    Finset (Finset (Fin r × α)) :=
  (Finset.univ : Finset (Fin r)).biUnion fun i => H.image (copyEdge i)

def fills {α : Type*} [Fintype α] [DecidableEq α] (r D : ℕ) (H : Finset (Finset α)) :
    Finset (Finset (Fin r × α)) :=
  (Finset.univ.filter fun x : α => (H.filter fun A => x ∈ A).card < D).image (fillEdge r)

lemma mem_layers {α : Type*} [DecidableEq α] {r : ℕ} {H : Finset (Finset α)}
    {A : Finset (Fin r × α)} :
    A ∈ layers r H ↔ ∃ i B, B ∈ H ∧ copyEdge i B = A := by
  simp [layers]

lemma mem_fills {α : Type*} [Fintype α] [DecidableEq α] {r D : ℕ} {H : Finset (Finset α)}
    {A : Finset (Fin r × α)} :
    A ∈ fills r D H ↔ ∃ x, (H.filter fun A => x ∈ A).card < D ∧ fillEdge r x = A := by
  simp [fills]

lemma disjoint_layers_fills {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ} (hr : 2 ≤ r)
    (D : ℕ) (H : Finset (Finset α)) : Disjoint (layers r H) (fills r D H) := by
  rw [Finset.disjoint_left]
  intro A hA hA'
  obtain ⟨i, B, _, rfl⟩ := mem_layers.mp hA
  obtain ⟨x, _, hEq⟩ := mem_fills.mp hA'
  let z : Fin r := ⟨0, by omega⟩
  let o : Fin r := ⟨1, by omega⟩
  have hz : (z, x) ∈ copyEdge i B := hEq ▸ mem_fillEdge.mpr rfl
  have ho : (o, x) ∈ copyEdge i B := hEq ▸ mem_fillEdge.mpr rfl
  have he := congrArg Fin.val ((mem_copyEdge.mp hz).1.symm.trans (mem_copyEdge.mp ho).1)
  simp [z, o] at he

lemma linear_layers_fills {α : Type*} [Fintype α] [DecidableEq α] {r D : ℕ}
    {H : Finset (Finset α)} (hH : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) :
    ∀ A ∈ layers r H ∪ fills r D H, ∀ B ∈ layers r H ∪ fills r D H, A ≠ B → (A ∩ B).card ≤ 1 := by
  have cross : ∀ (i : Fin r) (A : Finset α) (x : α), (copyEdge i A ∩ fillEdge r x).card ≤ 1 := by
    intro i A x
    apply Finset.card_le_one.mpr
    rintro ⟨j, y⟩ hp ⟨k, z⟩ hq
    simp only [Finset.mem_inter, mem_copyEdge, mem_fillEdge] at hp hq
    exact Prod.ext (hp.1.1.symm.trans hq.1.1) (hp.2.symm.trans hq.2)
  intro A hA B hB hne
  rcases Finset.mem_union.mp hA with hA | hA <;> rcases Finset.mem_union.mp hB with hB | hB
  · obtain ⟨i, A, hA0, rfl⟩ := mem_layers.mp hA
    obtain ⟨j, B, hB0, rfl⟩ := mem_layers.mp hB
    apply Finset.card_le_one.mpr
    rintro ⟨k, x⟩ hp ⟨l, y⟩ hq
    simp only [Finset.mem_inter, mem_copyEdge] at hp hq
    have hij : i = j := hp.1.1.trans hp.2.1.symm
    subst j
    have hAB : A ≠ B := fun he => hne (congrArg (copyEdge i) he)
    exact Prod.ext (hp.1.1.symm.trans hq.1.1)
      (Finset.card_le_one.mp (hH A hA0 B hB0 hAB) x
        (Finset.mem_inter.mpr ⟨hp.1.2, hp.2.2⟩) y
        (Finset.mem_inter.mpr ⟨hq.1.2, hq.2.2⟩))
  · obtain ⟨i, A, _, rfl⟩ := mem_layers.mp hA
    obtain ⟨x, _, rfl⟩ := mem_fills.mp hB
    exact cross i A x
  · obtain ⟨x, _, rfl⟩ := mem_fills.mp hA
    obtain ⟨i, B, _, rfl⟩ := mem_layers.mp hB
    rw [Finset.inter_comm]
    exact cross i B x
  · obtain ⟨x, _, rfl⟩ := mem_fills.mp hA
    obtain ⟨y, _, rfl⟩ := mem_fills.mp hB
    apply Finset.card_le_one.mpr
    rintro ⟨i, z⟩ hp _ _
    simp only [Finset.mem_inter, mem_fillEdge] at hp
    exact False.elim (hne (congrArg (fillEdge r) (hp.1.trans hp.2.symm)))

lemma deg_layers {α : Type*} [DecidableEq α] {r : ℕ} (H : Finset (Finset α)) (i : Fin r) (x : α) :
    ((layers r H).filter fun A => (i, x) ∈ A).card = (H.filter fun A => x ∈ A).card := by
  have heq : (layers r H).filter (fun A => (i, x) ∈ A) =
      (H.filter fun A => x ∈ A).image (copyEdge i) := by
    ext A
    simp only [Finset.mem_filter, mem_layers, Finset.mem_image]
    constructor
    · rintro ⟨⟨j, B, hB, rfl⟩, hmem⟩
      obtain ⟨rfl, hx⟩ := mem_copyEdge.mp hmem
      exact ⟨B, ⟨hB, hx⟩, rfl⟩
    · rintro ⟨B, ⟨hB, hx⟩, rfl⟩
      exact ⟨⟨i, B, hB, rfl⟩, mem_copyEdge.mpr ⟨rfl, hx⟩⟩
  rw [heq, Finset.card_image_of_injective _ (copyEdge_injective i)]

lemma deg_fills {α : Type*} [Fintype α] [DecidableEq α] {r D : ℕ} (H : Finset (Finset α))
    (i : Fin r) (x : α) :
    ((fills r D H).filter fun A => (i, x) ∈ A).card =
      if (H.filter fun A => x ∈ A).card < D then 1 else 0 := by
  have hm : ∀ A : Finset (Fin r × α),
      A ∈ (fills r D H).filter (fun A => (i, x) ∈ A) ↔
        (H.filter fun A => x ∈ A).card < D ∧ A = fillEdge r x := by
    intro A
    simp only [Finset.mem_filter, mem_fills]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, him⟩
      simpa only [mem_fillEdge.mp him, and_true] using hy
    · rintro ⟨hx, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, mem_fillEdge.mpr rfl⟩
  split_ifs with hx
  · have heq : (fills r D H).filter (fun A => (i, x) ∈ A) = {fillEdge r x} := by
      ext A; simp [hm, hx]
    simp [heq]
  · have heq : (fills r D H).filter (fun A => (i, x) ∈ A) = ∅ := by
      ext A; simp [hm, hx]
    simp [heq]

lemma deg_regular_step {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ} (hr : 2 ≤ r)
    (D : ℕ) (H : Finset (Finset α)) (i : Fin r) (x : α) :
    ((layers r H ∪ fills r D H).filter fun A => (i, x) ∈ A).card =
      (H.filter fun A => x ∈ A).card + if (H.filter fun A => x ∈ A).card < D then 1 else 0 := by
  have hd := disjoint_layers_fills hr D H
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  · exact congrArg₂ (· + ·) (deg_layers H i x) (deg_fills H i x)
  · exact hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

lemma uniform_layers_fills {α : Type*} [Fintype α] [DecidableEq α] {r D : ℕ}
    {H : Finset (Finset α)} (hH : ∀ A ∈ H, A.card = r) :
    ∀ A ∈ layers r H ∪ fills r D H, A.card = r := by
  intro A hA
  rcases Finset.mem_union.mp hA with hA | hA
  · obtain ⟨i, B, hB, rfl⟩ := mem_layers.mp hA
    rw [card_copyEdge]; exact hH B hB
  · obtain ⟨x, _, rfl⟩ := mem_fills.mp hA
    exact card_fillEdge r x

lemma linear_mapFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) {H : Finset (Finset α)} (hH : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) :
    ∀ A ∈ H.image (Finset.map f), ∀ B ∈ H.image (Finset.map f), A ≠ B → (A ∩ B).card ≤ 1 := by
  intro A hA B hB hAB
  obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
  rw [← Finset.map_inter, Finset.card_map]
  exact hH A₀ hA₀ B₀ hB₀ (fun he => hAB (congrArg (Finset.map f) he))

lemma deg_mapFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (H : Finset (Finset α)) (x : α) :
    ((H.image (Finset.map f)).filter fun A => f x ∈ A).card = (H.filter fun A => x ∈ A).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ (Finset.map_injective f)]
  simp [Finset.mem_map']

theorem regularize (r D k : ℕ) (hr : 2 ≤ r) :
    ∀ {α : Type} [Fintype α] [DecidableEq α] (H : Finset (Finset α)),
    (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) → (∀ A ∈ H, A.card = r) →
    (∀ x, (H.filter fun A => x ∈ A).card ≤ D ∧ D ≤ (H.filter fun A => x ∈ A).card + k) →
    ∃ (N : ℕ) (f : α ↪ Fin N) (K : Finset (Finset (Fin N))),
      (∀ A ∈ H, A.map f ∈ K) ∧ (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) ∧
      (∀ A ∈ K, A.card = r) ∧ (∀ x, (K.filter fun A => x ∈ A).card = D) := by
  induction k with
  | zero =>
    intro α _ _ H hlin hu hd
    let e := Fintype.equivFin α
    let K := H.image (Finset.map e.toEmbedding)
    refine ⟨Fintype.card α, e.toEmbedding, K, ?_, linear_mapFamily _ hlin, ?_, ?_⟩
    · intro A hA; exact Finset.mem_image_of_mem _ hA
    · intro A hA
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      simpa using hu B hB
    · intro x
      obtain ⟨x, rfl⟩ := e.surjective x
      change (K.filter fun A => e.toEmbedding x ∈ A).card = D
      rw [deg_mapFamily]
      have := hd x; omega
  | succ k ih =>
    intro α _ _ H hlin hu hd
    let L := layers r H ∪ fills r D H
    have hd' : ∀ v, (L.filter fun A => v ∈ A).card ≤ D ∧ D ≤ (L.filter fun A => v ∈ A).card + k := by
      rintro ⟨i, x⟩
      rw [deg_regular_step hr]
      have := hd x
      split_ifs <;> omega
    obtain ⟨N, f, K, hf, hlin', hu', hd''⟩ :=
      ih L (linear_layers_fills hlin) (uniform_layers_fills hu) hd'
    let i : Fin r := ⟨0, by omega⟩
    let g : α ↪ Fin r × α := ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩
    refine ⟨N, g.trans f, K, ?_, hlin', hu', hd''⟩
    intro A hA
    rw [← Finset.map_map]
    apply hf
    exact Finset.mem_union_left _ (mem_layers.mpr ⟨i, A, hA, rfl⟩)

def padEdge {α : Type*} [DecidableEq α] (r : ℕ) (A : Finset α) :
    Finset (α ⊕ (Finset α × Fin r)) :=
  A.map Function.Embedding.inl ∪
    (Finset.univ : Finset (Fin (r - A.card))).map
      ⟨fun i => Sum.inr (A, Fin.castLE (Nat.sub_le r A.card) i),
       fun _ _ h => Fin.ext (congrArg (fun p : Finset α × Fin r => p.2.val) (Sum.inr.inj h))⟩

lemma inl_mem_padEdge {α : Type*} [DecidableEq α] {r : ℕ} {A : Finset α} {x : α} :
    Sum.inl x ∈ padEdge r A ↔ x ∈ A := by
  simp [padEdge]

lemma eq_of_inr_mem_padEdge {α : Type*} [DecidableEq α] {r : ℕ} {A B : Finset α} {j : Fin r}
    (h : Sum.inr (B, j) ∈ padEdge r A) : A = B := by
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨a, _, ha⟩ := Finset.mem_map.mp h
    exact (Sum.inl_ne_inr ha).elim
  · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
    exact congrArg Prod.fst (Sum.inr.inj hi)

lemma card_padEdge {α : Type*} [DecidableEq α] {r : ℕ} {A : Finset α} (hA : A.card ≤ r) :
    (padEdge r A).card = r := by
  have hd : Disjoint (A.map (Function.Embedding.inl (β := Finset α × Fin r)))
      ((Finset.univ : Finset (Fin (r - A.card))).map
        ⟨fun i => Sum.inr (A, Fin.castLE (Nat.sub_le r A.card) i),
         fun _ _ h => Fin.ext (congrArg (fun p : Finset α × Fin r => p.2.val) (Sum.inr.inj h))⟩) := by
    rw [Finset.disjoint_left]
    rintro (x | ⟨B, j⟩) hx hy
    · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hy; exact Sum.inr_ne_inl hi
    · obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hx; exact Sum.inl_ne_inr ha
  rw [padEdge, Finset.card_union_of_disjoint hd]
  simp [Nat.add_sub_of_le hA]

lemma padEdge_injective {α : Type*} [DecidableEq α] (r : ℕ) :
    Function.Injective (padEdge (α := α) r) := by
  intro A B h
  ext x
  have hm : Sum.inl x ∈ padEdge r A ↔ Sum.inl x ∈ padEdge r B := by rw [h]
  simpa only [inl_mem_padEdge] using hm

lemma linear_padded {α : Type*} [DecidableEq α] {r : ℕ} {H : Finset (Finset α)}
    (hH : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) :
    ∀ A ∈ H.image (padEdge r), ∀ B ∈ H.image (padEdge r), A ≠ B → (A ∩ B).card ≤ 1 := by
  intro A hA B hB hne
  obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
  have hne₀ : A₀ ≠ B₀ := fun he => hne (congrArg (padEdge r) he)
  have hshared : ∀ {v : α ⊕ (Finset α × Fin r)}, v ∈ padEdge r A₀ ∩ padEdge r B₀ →
      ∃ x ∈ A₀ ∩ B₀, v = Sum.inl x := by
    intro v hv
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
    rcases v with x | ⟨C, j⟩
    · exact ⟨x, Finset.mem_inter.mpr ⟨inl_mem_padEdge.mp h1, inl_mem_padEdge.mp h2⟩, rfl⟩
    · exact (hne₀ ((eq_of_inr_mem_padEdge h1).trans (eq_of_inr_mem_padEdge h2).symm)).elim
  apply Finset.card_le_one.mpr
  intro v hv w hw
  obtain ⟨x, hx, rfl⟩ := hshared hv
  obtain ⟨y, hy, rfl⟩ := hshared hw
  exact congrArg Sum.inl (Finset.card_le_one.mp (hH A₀ hA₀ B₀ hB₀ hne₀) x hx y hy)

lemma deg_padded_inl {α : Type*} [DecidableEq α] (r : ℕ) (H : Finset (Finset α)) (x : α) :
    ((H.image (padEdge r)).filter fun A => Sum.inl x ∈ A).card =
      (H.filter fun A => x ∈ A).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ (padEdge_injective r)]
  simp only [inl_mem_padEdge]

lemma deg_padded_inr_le_one {α : Type*} [DecidableEq α] {r : ℕ} (H : Finset (Finset α))
    (B : Finset α) (j : Fin r) :
    ((H.image (padEdge r)).filter fun A => Sum.inr (B, j) ∈ A).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  have heq : ∀ A ∈ (H.image (padEdge r)).filter (fun A => Sum.inr (B, j) ∈ A), A = padEdge r B := by
    intro A hA
    obtain ⟨hA, hm⟩ := Finset.mem_filter.mp hA
    obtain ⟨A₀, _, rfl⟩ := Finset.mem_image.mp hA
    rw [eq_of_inr_mem_padEdge hm]
  exact fun A hA C hC => (heq A hA).trans (heq C hC).symm

theorem color_from_uniform_regular {r D m : ℕ} (hr : 2 ≤ r) (hD : 1 ≤ D)
    (hcolor : ∀ N (K : Finset (Finset (Fin N))),
      (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ K, A.card = r) → (∀ x, (K.filter fun A => x ∈ A).card = D) →
      ∃ c : Finset (Fin N) → Fin m,
        ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B)
    {n : ℕ} (H : Finset (Finset (Fin n))) (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (hrank : ∀ A ∈ H, A.card ≤ r) (hdeg : ∀ x, (H.filter fun A => x ∈ A).card ≤ D) :
    ∃ c : Finset (Fin n) → Fin m,
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  let J := H.image (padEdge r)
  have hu : ∀ A ∈ J, A.card = r := by
    intro A hA
    obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_image.mp hA
    exact card_padEdge (hrank A₀ hA₀)
  have hd : ∀ x, (J.filter fun A => x ∈ A).card ≤ D ∧ D ≤ (J.filter fun A => x ∈ A).card + D := by
    intro x
    refine ⟨?_, by omega⟩
    rcases x with x | ⟨B, j⟩
    · rw [deg_padded_inl]; exact hdeg x
    · exact (deg_padded_inr_le_one H B j).trans hD
  obtain ⟨N, f, K, hf, hlin', hu', hd'⟩ :=
    regularize r D D hr J (linear_padded hlin) hu hd
  obtain ⟨c, hc⟩ := hcolor N K hlin' hu' hd'
  refine ⟨fun A => c ((padEdge r A).map f), ?_⟩
  intro A hA B hB hne hmeet
  apply hc _ (hf _ (Finset.mem_image_of_mem _ hA)) _ (hf _ (Finset.mem_image_of_mem _ hB))
  · exact fun he => hne (padEdge_injective r (Finset.map_injective f he))
  · obtain ⟨x, hx⟩ := hmeet
    obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
    exact ⟨f (Sum.inl x), Finset.mem_inter.mpr
      ⟨Finset.mem_map_of_mem f (inl_mem_padEdge.mpr hxA),
        Finset.mem_map_of_mem f (inl_mem_padEdge.mpr hxB)⟩⟩

def assignmentEdge {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    (A : ↥H) (j : Fin D) : Finset (↥H ⊕ (α × Fin D)) :=
  insert (Sum.inl A)
    (A.1.map ⟨fun x => Sum.inr (x, j), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩)

lemma inl_mem_assignmentEdge {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    {A B : ↥H} {j : Fin D} :
    Sum.inl B ∈ assignmentEdge A j ↔ B = A := by
  simp [assignmentEdge]

lemma inr_mem_assignmentEdge {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    {A : ↥H} {j k : Fin D} {x : α} :
    Sum.inr (x, k) ∈ assignmentEdge A j ↔ k = j ∧ x ∈ A.1 := by
  rw [assignmentEdge, Finset.mem_insert, Finset.mem_map]
  change Sum.inr (x, k) = Sum.inl A ∨ (∃ y ∈ A.1, Sum.inr (y, j) = Sum.inr (x, k)) ↔ _
  simp only [Sum.inr_ne_inl, false_or, Sum.inr.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨y, hy, rfl, hjk⟩; exact ⟨hjk.symm, hy⟩
  · rintro ⟨rfl, hx⟩; exact ⟨x, hx, rfl, rfl⟩

lemma card_assignmentEdge {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    (A : ↥H) (j : Fin D) : (assignmentEdge A j).card = A.1.card + 1 := by
  rw [assignmentEdge, Finset.card_insert_of_notMem, Finset.card_map]
  intro h
  obtain ⟨_, _, hx⟩ := Finset.mem_map.mp h
  exact Sum.inr_ne_inl hx

lemma assignmentEdge_injective {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    (hH : ∀ A ∈ H, A.Nonempty) :
    Function.Injective (fun p : ↥H × Fin D => assignmentEdge p.1 p.2) := by
  rintro ⟨A, j⟩ ⟨B, k⟩ h
  dsimp only at h
  have hA : Sum.inl A ∈ assignmentEdge B k := h ▸ inl_mem_assignmentEdge.mpr rfl
  have hAB := inl_mem_assignmentEdge.mp hA
  subst B
  obtain ⟨x, hx⟩ := hH A.1 A.2
  have hj : Sum.inr (x, j) ∈ assignmentEdge A k := h ▸ inr_mem_assignmentEdge.mpr ⟨rfl, hx⟩
  exact Prod.ext rfl (inr_mem_assignmentEdge.mp hj).1

def assignments {α : Type*} [DecidableEq α] (H : Finset (Finset α)) (D : ℕ) :
    Finset (Finset (↥H ⊕ (α × Fin D))) :=
  (Finset.univ : Finset (↥H × Fin D)).image (fun p => assignmentEdge p.1 p.2)

lemma mem_assignments {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    {E : Finset (↥H ⊕ (α × Fin D))} :
    E ∈ assignments H D ↔ ∃ (A : ↥H) (j : Fin D), assignmentEdge A j = E := by
  simp [assignments, Prod.exists]

lemma linear_assignments {α : Type*} [DecidableEq α] {H : Finset (Finset α)}
    (hH : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) (D : ℕ) :
    ∀ E ∈ assignments H D, ∀ F ∈ assignments H D, E ≠ F → (E ∩ F).card ≤ 1 := by
  intro E hE F hF hne
  obtain ⟨A, j, rfl⟩ := mem_assignments.mp hE
  obtain ⟨B, k, rfl⟩ := mem_assignments.mp hF
  apply Finset.card_le_one.mpr
  rintro (C | ⟨x, l⟩) hp (C' | ⟨y, m⟩) hq
  · simp only [Finset.mem_inter, inl_mem_assignmentEdge] at hp hq
    exact congrArg Sum.inl (hp.1.trans hq.1.symm)
  · simp only [Finset.mem_inter, inl_mem_assignmentEdge] at hp
    simp only [Finset.mem_inter, inr_mem_assignmentEdge] at hq
    exact (hne (congrArg₂ assignmentEdge (hp.1.symm.trans hp.2) (hq.1.1.symm.trans hq.2.1))).elim
  · simp only [Finset.mem_inter, inr_mem_assignmentEdge] at hp
    simp only [Finset.mem_inter, inl_mem_assignmentEdge] at hq
    exact (hne (congrArg₂ assignmentEdge (hq.1.symm.trans hq.2) (hp.1.1.symm.trans hp.2.1))).elim
  · simp only [Finset.mem_inter, inr_mem_assignmentEdge] at hp hq
    have hjk : j = k := hp.1.1.symm.trans hp.2.1
    have hAB : A.1 ≠ B.1 := fun h => hne (congrArg₂ assignmentEdge (Subtype.ext h) hjk)
    have hxy := Finset.card_le_one.mp (hH A.1 A.2 B.1 B.2 hAB) x
      (Finset.mem_inter.mpr ⟨hp.1.2, hp.2.2⟩) y
      (Finset.mem_inter.mpr ⟨hq.1.2, hq.2.2⟩)
    exact congrArg Sum.inr (Prod.ext hxy (hp.1.1.trans hq.1.1.symm))

lemma deg_assignments_inl {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    (hH : ∀ A ∈ H, A.Nonempty) (A : ↥H) :
    ((assignments H D).filter fun E => Sum.inl A ∈ E).card = D := by
  have heq : (assignments H D).filter (fun E => Sum.inl A ∈ E) =
      (Finset.univ : Finset (Fin D)).image (assignmentEdge A) := by
    ext E
    simp only [Finset.mem_filter, mem_assignments, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨B, j, rfl⟩, h⟩
      obtain rfl := inl_mem_assignmentEdge.mp h
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨A, j, rfl⟩, inl_mem_assignmentEdge.mpr rfl⟩
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro j k h
    exact congrArg Prod.snd (assignmentEdge_injective hH (a₁ := (A, j)) (a₂ := (A, k)) h)

lemma card_incident {α : Type*} [DecidableEq α] (H : Finset (Finset α)) (x : α) :
    ((Finset.univ : Finset ↥H).filter (fun A => x ∈ A.1)).card =
      (H.filter fun A => x ∈ A).card := by
  have heq : ((Finset.univ : Finset ↥H).filter (fun A => x ∈ A.1)).image Subtype.val =
      H.filter (fun A => x ∈ A) := by
    ext A
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨B, hx, rfl⟩; exact ⟨B.2, hx⟩
    · rintro ⟨hA, hx⟩; exact ⟨⟨A, hA⟩, hx, rfl⟩
  rw [← heq, Finset.card_image_of_injective _ Subtype.val_injective]

lemma deg_assignments_inr {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    (hH : ∀ A ∈ H, A.Nonempty) (x : α) (j : Fin D) :
    ((assignments H D).filter fun E => Sum.inr (x, j) ∈ E).card =
      (H.filter fun A => x ∈ A).card := by
  have heq : (assignments H D).filter (fun E => Sum.inr (x, j) ∈ E) =
      ((Finset.univ : Finset ↥H).filter (fun A => x ∈ A.1)).image (fun A => assignmentEdge A j) := by
    ext E
    simp only [Finset.mem_filter, mem_assignments, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨A, k, rfl⟩, h⟩
      obtain ⟨rfl, hx⟩ := inr_mem_assignmentEdge.mp h
      exact ⟨A, hx, rfl⟩
    · rintro ⟨A, hx, rfl⟩
      exact ⟨⟨A, j, rfl⟩, inr_mem_assignmentEdge.mpr ⟨rfl, hx⟩⟩
  rw [heq, Finset.card_image_of_injective]
  · exact card_incident H x
  · intro A B h
    exact congrArg Prod.fst (assignmentEdge_injective hH (a₁ := (A, j)) (a₂ := (B, j)) h)

def targetSet {α : Type*} [DecidableEq α] (H : Finset (Finset α)) (D : ℕ) (x : α) :
    Finset (↥H ⊕ (α × Fin D)) :=
  ((Finset.univ : Finset ↥H).filter (fun A => x ∈ A.1)).map Function.Embedding.inl

lemma inl_mem_target {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    {A : ↥H} {x : α} :
    (Sum.inl A : ↥H ⊕ (α × Fin D)) ∈ targetSet H D x ↔ x ∈ A.1 := by
  change Function.Embedding.inl A ∈ _ ↔ _
  simp [targetSet]

lemma inr_not_mem_target {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    {x y : α} {j : Fin D} :
    Sum.inr (y, j) ∉ targetSet H D x := by
  intro h
  obtain ⟨_, _, hA⟩ := Finset.mem_map.mp h
  exact Sum.inl_ne_inr hA

lemma card_target {α : Type*} [DecidableEq α] (H : Finset (Finset α)) (D : ℕ) (x : α) :
    (targetSet H D x).card = (H.filter fun A => x ∈ A).card := by
  rw [targetSet, Finset.card_map, card_incident]

lemma deg_targets_le {α : Type*} [Fintype α] [DecidableEq α] {H : Finset (Finset α)} {D r : ℕ}
    (hr : ∀ A ∈ H, A.card ≤ r) (x : ↥H ⊕ (α × Fin D)) :
    (((Finset.univ : Finset α).image (targetSet H D)).filter fun U => x ∈ U).card ≤ r := by
  rw [Finset.filter_image]
  refine Finset.card_image_le.trans ?_
  rcases x with A | ⟨x, j⟩
  · simpa only [inl_mem_target, Finset.filter_mem_eq_inter, Finset.univ_inter] using hr A.1 A.2
  · simp [inr_not_mem_target]

lemma mem_cover_iff {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    {M : Finset (Finset (↥H ⊕ (α × Fin D)))} (hM : M ⊆ assignments H D) (a : ↥H) :
    Sum.inl a ∈ M.biUnion id ↔ ∃ j : Fin D, ∃ b : ↥H, b.1 = a.1 ∧ assignmentEdge b j ∈ M := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨E, hE, hm⟩
    obtain ⟨b, j, rfl⟩ := mem_assignments.mp (hM hE)
    obtain rfl := inl_mem_assignmentEdge.mp hm
    exact ⟨j, a, rfl, hE⟩
  · rintro ⟨j, b, hb, hm⟩
    exact ⟨assignmentEdge b j, hm, inl_mem_assignmentEdge.mpr (Subtype.ext hb.symm)⟩

lemma deg_unassigned {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {D : ℕ}
    {M : Finset (Finset (↥H ⊕ (α × Fin D)))} (hM : M ⊆ assignments H D) (x : α) :
    ((H.filter fun A => ¬ ∃ j : Fin D, ∃ a : ↥H, a.1 = A ∧ assignmentEdge a j ∈ M).filter
      fun A => x ∈ A).card = (targetSet H D x \ M.biUnion id).card := by
  let t := (Finset.univ : Finset ↥H).filter
    (fun a => x ∈ a.1 ∧ ¬ ∃ j : Fin D, ∃ b : ↥H, b.1 = a.1 ∧ assignmentEdge b j ∈ M)
  have hleft : t.image Subtype.val =
      (H.filter fun A => ¬ ∃ j : Fin D, ∃ a : ↥H, a.1 = A ∧ assignmentEdge a j ∈ M).filter
        (fun A => x ∈ A) := by
    ext A
    simp only [t, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ⟨hx, hna⟩, rfl⟩; exact ⟨⟨a.2, hna⟩, hx⟩
    · rintro ⟨⟨hA, hnA⟩, hx⟩; exact ⟨⟨A, hA⟩, ⟨hx, hnA⟩, rfl⟩
  have hright : t.map Function.Embedding.inl = targetSet H D x \ M.biUnion id := by
    ext v
    rcases v with a | ⟨y, j⟩
    · change Function.Embedding.inl a ∈ t.map Function.Embedding.inl ↔ _
      simp [t, inl_mem_target, mem_cover_iff hM]
    · simp only [Finset.mem_sdiff, inr_not_mem_target, false_and, iff_false]
      intro h
      obtain ⟨_, _, hA⟩ := Finset.mem_map.mp h
      exact Sum.inl_ne_inr hA
  rw [← hleft, ← hright, Finset.card_map, Finset.card_image_of_injective _ Subtype.val_injective]

theorem color_from_assignment_matching {n r D : ℕ} (hr : 0 < r) (hD : 0 < D)
    (H : Finset (Finset (Fin n))) (hrank : ∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ r)
    (M : Finset (Finset (↥H ⊕ (Fin n × Fin D)))) (hsub : M ⊆ assignments H D)
    (hM : ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F)
    (hcover : ∀ x, (targetSet H D x \ M.biUnion id).card ≤ D / r) :
    ∃ c : Finset (Fin n) → Fin (2 * D),
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  let R := H.filter fun A => ¬ ∃ j : Fin D, ∃ a : ↥H, a.1 = A ∧ assignmentEdge a j ∈ M
  have hm : r * (D / r - 1) < D := by
    by_cases hq : D / r = 0
    · simp [hq, hD]
    · calc r * (D / r - 1)
          < r * (D / r) := Nat.mul_lt_mul_of_pos_left (Nat.sub_lt (Nat.pos_of_ne_zero hq) Nat.zero_lt_one) hr
        _ ≤ D := by simpa [Nat.mul_comm] using Nat.div_mul_le_self D r
  obtain ⟨d, hd⟩ := color_small_rank R
    (fun A hA => hrank A (Finset.mem_filter.mp hA).1)
    (fun x => (deg_unassigned hsub x).trans_le (hcover x)) D hm
  let c : Finset (Fin n) → Fin (D + D) := fun A =>
    if h : ∃ j : Fin D, ∃ a : ↥H, a.1 = A ∧ assignmentEdge a j ∈ M
    then Fin.castAdd D (Classical.choose h) else Fin.natAdd D (d A)
  have hcast : D + D = 2 * D := by omega
  refine ⟨fun A => Fin.cast hcast (c A), ?_⟩
  intro A hA B hB hAB hmeet heq
  have hc := Fin.cast_injective hcast heq
  by_cases hMA : ∃ j : Fin D, ∃ a : ↥H, a.1 = A ∧ assignmentEdge a j ∈ M <;>
  by_cases hMB : ∃ j : Fin D, ∃ a : ↥H, a.1 = B ∧ assignmentEdge a j ∈ M
  · simp only [c, dif_pos hMA, dif_pos hMB] at hc
    have hj : Classical.choose hMA = Classical.choose hMB := Fin.castAdd_injective D D hc
    obtain ⟨a, ha, hma⟩ := Classical.choose_spec hMA
    obtain ⟨b, hb, hmb⟩ := Classical.choose_spec hMB
    rw [← hj] at hmb
    let j := Classical.choose hMA
    have hne : assignmentEdge a j ≠ assignmentEdge b j := by
      intro h
      have hleft : Sum.inl a ∈ assignmentEdge b j := h ▸ inl_mem_assignmentEdge.mpr rfl
      exact hAB (ha.symm.trans ((congrArg Subtype.val (inl_mem_assignmentEdge.mp hleft)).trans hb))
    obtain ⟨x, hx⟩ := hmeet
    obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
    exact (Finset.disjoint_left.mp (hM _ hma _ hmb hne))
      (inr_mem_assignmentEdge.mpr ⟨rfl, ha.symm ▸ hxA⟩)
      (inr_mem_assignmentEdge.mpr ⟨rfl, hb.symm ▸ hxB⟩)
  · simp only [c, dif_pos hMA, dif_neg hMB] at hc
    have he := congrArg Fin.val hc; simp at he; omega
  · simp only [c, dif_neg hMA, dif_pos hMB] at hc
    have he := congrArg Fin.val hc; simp at he; omega
  · simp only [c, dif_neg hMA, dif_neg hMB] at hc
    exact hd A (Finset.mem_filter.mpr ⟨hA, hMA⟩) B (Finset.mem_filter.mpr ⟨hB, hMB⟩)
      hAB hmeet (Fin.natAdd_injective D D hc)

theorem core_uniform_regular_of (r : ℕ) (hr : 3 ≤ r)
    (hc0 : ∃ D₀ : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α] (D : ℕ), D₀ ≤ D →
      ∀ (G T : Finset (Finset α)), (∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ E ∈ G, E.card = r + 1) → (∀ x, (G.filter fun E => x ∈ E).card = D) →
      (∀ U ∈ T, U.card ≤ D) → (∀ x, (T.filter fun U => x ∈ U).card ≤ r + 1) →
      ∃ M : Finset (Finset α), M ⊆ G ∧ (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
        ∀ U ∈ T, (U \ M.biUnion id).card ≤ D / r) :
    ∃ D₀ : ℕ, ∀ n D : ℕ, D₀ ≤ D → ∀ H : Finset (Finset (Fin n)),
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) → (∀ A ∈ H, A.card = r) →
      (∀ x, (H.filter fun A => x ∈ A).card = D) →
      ∃ c : Finset (Fin n) → Fin (2 * D),
        ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  obtain ⟨D₀, hc⟩ := hc0
  refine ⟨max 1 D₀, ?_⟩
  intro n D hD H hlin hu hd
  have hne : ∀ A ∈ H, A.Nonempty := fun A hA => by rw [← Finset.card_pos, hu A hA]; omega
  let G := assignments H D
  let T := (Finset.univ : Finset (Fin n)).image (targetSet H D)
  have hdeg : ∀ x : ↥H ⊕ (Fin n × Fin D), (G.filter fun E => x ∈ E).card = D := by
    rintro (A | ⟨x, j⟩)
    · exact deg_assignments_inl hne A
    · rw [deg_assignments_inr hne, hd]
  have huG : ∀ E ∈ G, E.card = r + 1 := fun E hE => by
    obtain ⟨A, j, rfl⟩ := mem_assignments.mp hE
    rw [card_assignmentEdge, hu A.1 A.2]
  have hTU : ∀ U ∈ T, U.card ≤ D := fun U hU => by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hU
    rw [card_target, hd]
  have hTd : ∀ x, (T.filter fun U => x ∈ U).card ≤ r + 1 := fun x =>
    (deg_targets_le (fun A hA => (hu A hA).le) x).trans (Nat.le_succ r)
  obtain ⟨M, hsub, hM, hcover⟩ :=
    hc (↥H ⊕ (Fin n × Fin D)) D (by omega) G T (linear_assignments hlin D) huG hdeg hTU hTd
  exact color_from_assignment_matching (r := r) (by omega) (by omega) H
    (fun A hA => by rw [hu A hA]; omega) M hsub hM
    (fun x => hcover _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))

theorem rank_ge3_of
    (hcore : ∀ s : ℕ, 3 ≤ s → ∃ D₀ : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α] (D : ℕ), D₀ ≤ D →
      ∀ (G T : Finset (Finset α)), (∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ E ∈ G, E.card = s + 1) → (∀ x, (G.filter fun E => x ∈ E).card = D) →
      (∀ U ∈ T, U.card ≤ D) → (∀ x, (T.filter fun U => x ∈ U).card ≤ s + 1) →
      ∃ M : Finset (Finset α), M ⊆ G ∧ (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
        ∀ U ∈ T, (U \ M.biUnion id).card ≤ D / s)
    (r : ℕ) (hr : 3 ≤ r) :
    ∃ D₀ : ℕ, ∀ n D : ℕ, D₀ ≤ D →
      ∀ H : Finset (Finset (Fin n)),
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ r) →
      (∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) →
      ∃ c : Finset (Fin n) → Fin (2 * D),
        ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  obtain ⟨D₀, h⟩ := core_uniform_regular_of r hr (hcore r hr)
  refine ⟨max 1 D₀, ?_⟩
  intro n D hD H hlin hrank hdeg
  exact color_from_uniform_regular (by omega) (by omega : 1 ≤ D)
    (fun N K => h N D (by omega) K) H hlin (fun A hA => (hrank A hA).2) hdeg

end Reduction

end Erdos19H2

theorem OMA.solution : OMA.R_Erdos19_erdos_19_variants_kahn_R1.H2 := by
  intro r
  by_cases hr : r ≤ 2
  · refine ⟨1, fun n D hD H _ hrank hdeg => ?_⟩
    refine Erdos19H2.color_small_rank H hrank hdeg (2 * D) ?_
    have : r * (D - 1) ≤ 2 * (D - 1) := Nat.mul_le_mul_right _ hr
    omega
  · exact Erdos19H2.rank_ge3_of Erdos19H2.locally_covering_matching r (by omega)
