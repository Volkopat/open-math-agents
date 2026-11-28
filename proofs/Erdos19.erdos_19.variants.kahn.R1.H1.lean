import OMAReductions.R_Erdos19_erdos_19_variants_kahn_R1
import Mathlib

-- Problem: Erdős Problem 19 — kahn (R1.H1: asymptotic list edge-coloring of bounded-rank linear hypergraphs)
-- Target: OMA.R_Erdos19_erdos_19_variants_kahn_R1.H1
-- Credit: @gdyan2022

/-!
Proof of `OMA.R_Erdos19_erdos_19_variants_kahn_R1.H1`:
Every bounded-rank linear hypergraph of large maximum degree `D` is list edge-colorable from
lists of size `D + D / q` (Kahn 1996).

Architecture:
1. Finite-sample-space Symmetric Lovász Local Lemma (`lll_symmetric`) and coordinate-dependency
   independence (`DependsOn`, `lll_of_dependsOn`).
2. Two-sided `p`-weighted McDiarmid bounded-differences inequality (`bernoulli_mcdiarmid_sub`),
   weighted Chernoff bound (`weighted_chernoff_sub`), and elementary exponential inequalities.
3. Single equalized Kahn list-nibble round (`list_nibble_round`) with dummy equalizing coins
   on a non-dependent product space `Coord → Fin Q`, proving simultaneous concentration of
   surviving list sizes, vertex degrees, and vertex-color codegrees via LLL.
4. Multi-round deterministic ODE tracking and `R`-round iteration (`uniform_list_coloring`),
   finishing greedily once `r * D_R < L_R`.
5. Rank-2 greedy case (`case_one`) and uniform padding reduction (`padding`) yielding `OMA.solution`.
-/

namespace Erdos19H1

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


lemma exp_ge_pow_six_div {x : ℝ} (hx : 0 ≤ x) : x ^ 6 / 720 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 7
  have h6 : x ^ 6 / (Nat.factorial 6 : ℝ) ≤ ∑ i ∈ Finset.range 7, x ^ i / (Nat.factorial i : ℝ) :=
    Finset.single_le_sum (f := fun i => x ^ i / (Nat.factorial i : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (by decide))
  have hf6 : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hf6] at h6
  exact h6.trans h

lemma exp_neg_le_one_sub_add_sq {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 := by
  have hsum : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
    have h := Real.sum_le_exp_of_nonneg hx 3
    simp [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hprod : 1 ≤ (1 + x + x ^ 2 / 2) * (1 - x + x ^ 2) := by
    nlinarith [sq_nonneg x]
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀' hexp_pos]
  have hnn : 0 ≤ 1 - x + x ^ 2 := by nlinarith [sq_nonneg (x - 1 / 2)]
  exact hprod.trans (mul_le_mul_of_nonneg_right hsum hnn)

lemma one_sub_ge_exp_neg_sub_sq_half {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    Real.exp (-p - p ^ 2) ≤ 1 - p := by
  have hu : 0 ≤ p + p ^ 2 := by nlinarith
  have hsum : 1 + (p + p ^ 2) + (p + p ^ 2) ^ 2 / 2 ≤ Real.exp (p + p ^ 2) := by
    have h := Real.sum_le_exp_of_nonneg hu 3
    simp [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hprod : 1 ≤ (1 + (p + p ^ 2) + (p + p ^ 2) ^ 2 / 2) * (1 - p) := by
    have h2 : p ^ 2 ≤ p / 2 := by nlinarith
    have h3 : p ^ 3 ≤ p ^ 2 / 2 := by nlinarith
    have h4 : p ^ 4 ≤ p ^ 2 / 4 := by nlinarith
    have h5 : p ^ 5 ≤ p ^ 2 / 8 := by nlinarith
    nlinarith [sq_nonneg p]
  have hneg : -p - p ^ 2 = -(p + p ^ 2) := by ring
  rw [hneg, Real.exp_neg, inv_le_iff_one_le_mul₀' (Real.exp_pos _)]
  exact hprod.trans (mul_le_mul_of_nonneg_right hsum (by linarith))

lemma exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : 1 ≤ (1 - x) * (1 + 2 * x) := by nlinarith
  have h3 : 1 ≤ Real.exp (-x) * (1 + 2 * x) :=
    h2.trans (mul_le_mul_of_nonneg_right h1 (by linarith))
  have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos x).le
  rw [mul_one, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h4
  exact h4

lemma exp_le_one_add_add_two_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + 2 * x ^ 2 := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : 1 ≤ (1 - x) * (1 + x + 2 * x ^ 2) := by
    have hsq : 0 ≤ x ^ 2 * (1 - 2 * x) := mul_nonneg (sq_nonneg x) (by linarith)
    nlinarith
  have h3 : 1 ≤ Real.exp (-x) * (1 + x + 2 * x ^ 2) :=
    h2.trans (mul_le_mul_of_nonneg_right h1 (by nlinarith))
  have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos x).le
  rw [mul_one, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h4
  exact h4

lemma one_sub_pow_bounds {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    (m : ℝ) * p - ((m : ℝ) * p) ^ 2 ≤ 1 - (1 - p) ^ m ∧ 1 - (1 - p) ^ m ≤ (m : ℝ) * p := by
  constructor
  · have h1 : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
    have h2 : (1 - p) ^ m ≤ Real.exp (-((m : ℝ) * p)) := by
      calc (1 - p) ^ m ≤ (Real.exp (-p)) ^ m := pow_le_pow_left₀ (by linarith) h1 m
        _ = Real.exp ((m : ℝ) * (-p)) := (Real.exp_nat_mul (-p) m).symm
        _ = Real.exp (-((m : ℝ) * p)) := by ring_nf
    have h3 : Real.exp (-((m : ℝ) * p)) ≤ 1 - (m : ℝ) * p + ((m : ℝ) * p) ^ 2 :=
      exp_neg_le_one_sub_add_sq (mul_nonneg (Nat.cast_nonneg m) hp0)
    linarith
  · have h1 := one_sub_mul_le_pow_aux p hp0 hp1 m
    linarith

lemma card_filter_cond_split {X : Type*} [Fintype X] [DecidableEq X]
    {Q : ℕ} (hQ : 0 < Q) (S : Finset X) {ι : Type*}
    (idx : (X → Fin Q) → ι)
    (hidx : ∀ ω₁ ω₂, (∀ x ∈ S, ω₁ x = ω₂ x) → idx ω₁ = idx ω₂)
    (P : ι → (X → Fin Q) → Prop)
    (hP_indep : ∀ i ω₁ ω₂, (∀ x, x ∉ S → ω₁ x = ω₂ x) → (P i ω₁ ↔ P i ω₂))
    (p : ℝ)
    (hP_bound : ∀ i, ((Finset.univ.filter (fun ω : X → Fin Q => P i ω)).card : ℝ) ≤
      p * (Fintype.card (X → Fin Q) : ℝ)) :
    ((Finset.univ.filter (fun ω : X → Fin Q => P (idx ω) ω)).card : ℝ) ≤
      p * (Fintype.card (X → Fin Q) : ℝ) := by
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  let a₀ : Fin Q := ⟨0, hQ⟩
  let eS := splitProdEquiv (α := Fin Q) S
  have hcardTot : (Fintype.card (X → Fin Q) : ℝ) =
      (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) *
      (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) := by
    have h1 : Fintype.card (X → Fin Q) =
        Fintype.card ({x : X // x ∈ S} → Fin Q) * Fintype.card ({x : X // x ∉ S} → Fin Q) := by
      rw [Fintype.card_congr eS, Fintype.card_prod]
    exact_mod_cast h1
  have hSpos : (0 : ℝ) < (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  let i₀ : ({x : X // x ∈ S} → Fin Q) → ι := fun τ => idx (eS.symm (τ, fun _ => a₀))
  have hidx_eq : ∀ τ σ, idx (eS.symm (τ, σ)) = i₀ τ := fun τ σ => by
    apply hidx
    intro x hx
    simp [eS, splitProdEquiv, hx]
  let G : ({x : X // x ∈ S} → Fin Q) → Finset ({x : X // x ∉ S} → Fin Q) :=
    fun τ => Finset.univ.filter (fun σ => P (i₀ τ) (eS.symm (τ, σ)))
  have hG_bound : ∀ τ, ((G τ).card : ℝ) ≤ p * (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) := by
    intro τ
    have him : (Finset.univ.filter (fun ω : X → Fin Q => P (i₀ τ) ω)).image eS =
        Finset.univ ×ˢ G τ := by
      ext q
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        G]
      constructor
      · rintro ⟨ω, hω, rfl⟩
        have hEq : ∀ x, x ∉ S → ω x = (eS.symm (τ, (eS ω).2)) x := fun x hx => by
          simp [eS, splitProdEquiv, hx]
        exact (hP_indep (i₀ τ) ω _ hEq).mp hω
      · intro hq
        refine ⟨eS.symm q, ?_, eS.apply_symm_apply q⟩
        have hEq : ∀ x, x ∉ S → (eS.symm (τ, q.2)) x = (eS.symm q) x := fun x hx => by
          simp [eS, splitProdEquiv, hx]
        exact (hP_indep (i₀ τ) _ _ hEq).mp hq
    have hcard_i : ((Finset.univ.filter (fun ω : X → Fin Q => P (i₀ τ) ω)).card : ℝ) =
        (Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) * ((G τ).card : ℝ) := by
      have h1 : (Finset.univ.filter (fun ω : X → Fin Q => P (i₀ τ) ω)).card =
          Fintype.card ({x : X // x ∈ S} → Fin Q) * (G τ).card := by
        rw [← Finset.card_image_of_injective _ eS.injective, him, Finset.card_product,
          Finset.card_univ]
      exact_mod_cast h1
    have hb := hP_bound (i₀ τ)
    rw [hcard_i, hcardTot] at hb
    nlinarith only [hb, hSpos]
  have hsum_card : ((Finset.univ.filter (fun ω : X → Fin Q => P (idx ω) ω)).card : ℝ) =
      ∑ τ : {x : X // x ∈ S} → Fin Q, ((G τ).card : ℝ) := by
    have h1 : ((Finset.univ.filter (fun ω : X → Fin Q => P (idx ω) ω)).card : ℝ) =
        ∑ ω : X → Fin Q, if P (idx ω) ω then (1 : ℝ) else 0 := by
      rw [Finset.card_filter]; simp
    rw [h1, ← Equiv.sum_comp eS.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h2 : ((G τ).card : ℝ) =
        ∑ σ : {x : X // x ∉ S} → Fin Q, if P (i₀ τ) (eS.symm (τ, σ)) then (1 : ℝ) else 0 := by
      simp only [G, Finset.card_filter]; simp
    rw [h2]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hidx_eq τ σ]
  rw [hsum_card, hcardTot]
  calc ∑ τ : {x : X // x ∈ S} → Fin Q, ((G τ).card : ℝ)
      ≤ ∑ _τ : {x : X // x ∈ S} → Fin Q, p * (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ) :=
        Finset.sum_le_sum fun τ _ => hG_bound τ
    _ = p * ((Fintype.card ({x : X // x ∈ S} → Fin Q) : ℝ) *
          (Fintype.card ({x : X // x ∉ S} → Fin Q) : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring


/- ### Section 3: Single Equalized Kahn List-Nibble Round -/

section ListNibbleRound

/-- Non-dependent coordinate space for one equalized Kahn list-nibble round. -/
abbrev LCoord {n : ℕ} (K : Finset (Finset (Fin n))) (m C_int : ℕ) : Type :=
  (↥K × Fin m) ⊕ (Fin n × Fin m × Fin C_int)

/-- Color index associated with a coordinate. -/
def coordColor {n m C_int : ℕ} {K : Finset (Finset (Fin n))} :
    LCoord K m C_int → Fin m
  | Sum.inl (_, c) => c
  | Sum.inr (_, c, _) => c

/-- Real `(edge, color)` coordinates incident to vertex `x` with color `c`. -/
def realVC {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (x : Fin n) (c : Fin m) :
    Finset (LCoord K m C_int) :=
  ((Finset.univ : Finset ↥K).filter (fun A => x ∈ A.1 ∧ c ∈ L A.1)).image
    (fun A => Sum.inl (A, c))

/-- Dummy equalizing coordinates for `(x, c)` padding its color-degree up to `C_int`. -/
def dummyCoord {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (x : Fin n) (c : Fin m) :
    Finset (LCoord K m C_int) :=
  (Finset.univ.filter (fun j : Fin C_int =>
    j.val < C_int - (K.filter (fun A => x ∈ A ∧ c ∈ L A)).card)).image
      (fun j => Sum.inr (x, c, j))

/-- Full equalized pool of `C_int` coordinates at `(x, c)`. -/
def blockCoord {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (x : Fin n) (c : Fin m) :
    Finset (LCoord K m C_int) :=
  realVC K L x c ∪ dummyCoord K L x c

/-- Equalized pool of `C_int - 1` coordinates blocking `(A, c)` at vertex `x`. -/
def blockCoordNe {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (A : ↥K) (x : Fin n) (c : Fin m) :
    Finset (LCoord K m C_int) :=
  (blockCoord K L x c).erase (Sum.inl (A, c))

/-- All coordinates blocking color `c` on edge `A`. -/
def edgeColorBlock {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (A : ↥K) (c : Fin m) :
    Finset (LCoord K m C_int) :=
  A.1.biUnion (fun y => blockCoordNe K L A y c)

/-- Coordinates determining the surviving list of edge `A`. -/
def depList {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (A : ↥K) :
    Finset (LCoord K m C_int) :=
  (L A.1).biUnion (fun c => edgeColorBlock K L A c)

/-- All coordinates relevant to edge `A` (its own trials plus its list blockers). -/
def depEdge {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (A : ↥K) :
    Finset (LCoord K m C_int) :=
  ((L A.1).image (fun c => Sum.inl (A, c))) ∪ depList K L A

/-- Dependency set for a subset `F` of edges. -/
def depSubset {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) :
    Finset (LCoord K m C_int) :=
  F.biUnion (fun A => depEdge K L A)

/-- List of edge `A` with an optional excluded color removed. -/
def listSub {n m : ℕ} {K : Finset (Finset (Fin n))}
    (L : Finset (Fin n) → Finset (Fin m)) (c_excl : Option (Fin m)) (A : ↥K) :
    Finset (Fin m) :=
  match c_excl with
  | none => L A.1
  | some c => (L A.1).erase c

/-- Refined dependency set for coloring edges of `F` using only colors in `listSub`. -/
def depSubsetExcl {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m)) :
    Finset (LCoord K m C_int) :=
  F.biUnion (fun A =>
    ((L A.1).image (fun c' => Sum.inl (A, c'))) ∪
    (listSub L c_excl A).biUnion (fun c' => edgeColorBlock K L A c'))

/-- Edges incident to vertex `x` carrying color `c`, as a subtype finset of `↥K`. -/
def incVC {n m : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (x : Fin n) (c : Fin m) : Finset ↥K :=
  Finset.univ.filter (fun A : ↥K => x ∈ A.1 ∧ c ∈ L A.1)

/-- External color-`c` coordinates around `(x, c)` (excluding vertex `x`). -/
def extVC {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (x : Fin n) (c : Fin m) :
    Finset (LCoord K m C_int) :=
  (incVC K L x c).biUnion (fun A => (A.1.erase x).biUnion (fun y => blockCoordNe K L A y c))

/-- Whether edge `A` successfully receives color `c` under assignment `ω`. -/
def isColored {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (ω : LCoord K m C_int → Fin Q)
    (A : ↥K) (c : Fin m) : Prop :=
  c ∈ L A.1 ∧ (ω (Sum.inl (A, c))).val = 0 ∧
  (∀ c' ∈ L A.1, c' ≠ c → (ω (Sum.inl (A, c'))).val ≠ 0) ∧
  (∀ e ∈ edgeColorBlock K L A c, (ω e).val ≠ 0)

/-- Surviving color list of edge `A` after one equalized round. -/
noncomputable def nextList {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (ω : LCoord K m C_int → Fin Q)
    (A : ↥K) : Finset (Fin m) :=
  (L A.1).filter (fun c => ∀ e ∈ edgeColorBlock K L A c, (ω e).val ≠ 0)

/-- Surviving uncolored edges after one round. -/
noncomputable def survEdges {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (ω : LCoord K m C_int → Fin Q) :
    Finset (Finset (Fin n)) :=
  K.filter (fun A => ∀ hA : A ∈ K, ∀ c ∈ L A, ¬ isColored K L ω ⟨A, hA⟩ c)

/-- Partial coloring assigned to colored edges in one round. -/
noncomputable def roundColoring {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (hm : 0 < m)
    (ω : LCoord K m C_int → Fin Q) (A : Finset (Fin n)) : Fin m :=
  if h : ∃ (hA : A ∈ K) (c : Fin m), isColored K L ω ⟨A, hA⟩ c then
    Classical.choose (Classical.choose_spec h)
  else ⟨0, hm⟩

lemma coordColor_mem_blockCoord {n m C_int : ℕ} {K : Finset (Finset (Fin n))}
    {L : Finset (Fin n) → Finset (Fin m)} {x : Fin n} {c : Fin m} {e : LCoord K m C_int}
    (he : e ∈ blockCoord K L x c) : coordColor e = c := by
  simp only [blockCoord, realVC, dummyCoord, Finset.mem_union, Finset.mem_image] at he
  rcases he with ⟨A, _, rfl⟩ | ⟨j, _, rfl⟩ <;> rfl

lemma coordColor_mem_blockCoordNe {n m C_int : ℕ} {K : Finset (Finset (Fin n))}
    {L : Finset (Fin n) → Finset (Fin m)} {A : ↥K} {x : Fin n} {c : Fin m}
    {e : LCoord K m C_int} (he : e ∈ blockCoordNe K L A x c) : coordColor e = c :=
  coordColor_mem_blockCoord (Finset.mem_of_mem_erase he)

lemma coordColor_mem_edgeColorBlock {n m C_int : ℕ} {K : Finset (Finset (Fin n))}
    {L : Finset (Fin n) → Finset (Fin m)} {A : ↥K} {c : Fin m} {e : LCoord K m C_int}
    (he : e ∈ edgeColorBlock K L A c) : coordColor e = c := by
  simp only [edgeColorBlock, Finset.mem_biUnion] at he
  rcases he with ⟨y, _, hy⟩
  exact coordColor_mem_blockCoordNe hy

lemma coordColor_mem_extVC {n m C_int : ℕ} {K : Finset (Finset (Fin n))}
    {L : Finset (Fin n) → Finset (Fin m)} {x : Fin n} {c : Fin m} {e : LCoord K m C_int}
    (he : e ∈ extVC K L x c) : coordColor e = c := by
  simp only [extVC, Finset.mem_biUnion] at he
  rcases he with ⟨A, _, y, _, hy⟩
  exact coordColor_mem_blockCoordNe hy

lemma card_incVC {n m : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (x : Fin n) (c : Fin m) :
    (incVC K L x c).card = (K.filter (fun A => x ∈ A ∧ c ∈ L A)).card := by
  refine Finset.card_bij (fun A _ => A.1) ?_ ?_ ?_
  · intro A hA
    simp only [incVC, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    exact Finset.mem_filter.mpr ⟨A.2, hA⟩
  · intro A₁ _ A₂ _ h; exact Subtype.ext h
  · intro A hA
    rcases Finset.mem_filter.mp hA with ⟨hAK, hx, hc⟩
    exact ⟨⟨A, hAK⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hc⟩, rfl⟩

lemma card_realVC {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (x : Fin n) (c : Fin m) :
    (realVC K L (C_int := C_int) x c).card = (K.filter (fun A => x ∈ A ∧ c ∈ L A)).card := by
  unfold realVC
  rw [Finset.card_image_of_injective]
  · exact card_incVC K L x c
  · intro A₁ A₂ h
    exact congrArg Prod.fst (Sum.inl.inj h)

lemma card_dummyCoord {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (x : Fin n) (c : Fin m)
    (_hdeg : (K.filter (fun A => x ∈ A ∧ c ∈ L A)).card ≤ C_int) :
    (dummyCoord K L (C_int := C_int) x c).card =
      C_int - (K.filter (fun A => x ∈ A ∧ c ∈ L A)).card := by
  unfold dummyCoord
  rw [Finset.card_image_of_injective]
  · set d := C_int - (K.filter (fun A => x ∈ A ∧ c ∈ L A)).card
    have hd : d ≤ C_int := Nat.sub_le _ _
    let emb : Fin d ↪ Fin C_int :=
      ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hd⟩,
       fun _ _ h => Fin.ext (congrArg (fun j : Fin C_int => j.val) h)⟩
    have heq : Finset.univ.filter (fun j : Fin C_int => j.val < d) = Finset.univ.map emb := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, emb]
      constructor
      · intro hj; exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
      · rintro ⟨i, rfl⟩; exact i.isLt
    rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro j₁ j₂ h
    exact congrArg (fun p : Fin n × Fin m × Fin C_int => p.2.2) (Sum.inr.inj h)

lemma card_blockCoord {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (x : Fin n) (c : Fin m)
    (hdeg : (K.filter (fun A => x ∈ A ∧ c ∈ L A)).card ≤ C_int) :
    (blockCoord K L (C_int := C_int) x c).card = C_int := by
  unfold blockCoord
  have hdisj : Disjoint (realVC K L (C_int := C_int) x c) (dummyCoord K L x c) := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    simp only [realVC, Finset.mem_image] at he₁
    simp only [dummyCoord, Finset.mem_image] at he₂
    rcases he₁ with ⟨_, _, rfl⟩
    rcases he₂ with ⟨_, _, h⟩
    exact Sum.inl_ne_inr h.symm
  rw [Finset.card_union_of_disjoint hdisj, card_realVC, card_dummyCoord K L x c hdeg]
  omega

lemma mem_blockCoord_self {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) {A : ↥K} {x : Fin n} {c : Fin m}
    (hx : x ∈ A.1) (hc : c ∈ L A.1) :
    (Sum.inl (A, c) : LCoord K m C_int) ∈ blockCoord K L x c := by
  apply Finset.mem_union_left
  simp only [realVC, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨A, ⟨hx, hc⟩, rfl⟩

lemma card_blockCoordNe {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) {A : ↥K} {x : Fin n} {c : Fin m}
    (hdeg : (K.filter (fun B => x ∈ B ∧ c ∈ L B)).card ≤ C_int)
    (hx : x ∈ A.1) (hc : c ∈ L A.1) :
    (blockCoordNe K L (C_int := C_int) A x c).card = C_int - 1 := by
  unfold blockCoordNe
  rw [Finset.card_erase_of_mem (mem_blockCoord_self K L hx hc), card_blockCoord K L x c hdeg]

lemma disjoint_blockCoordNe_vert {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m))
    (hlin : ∀ E ∈ K, ∀ F ∈ K, E ≠ F → (E ∩ F).card ≤ 1)
    (A : ↥K) (c : Fin m) {y₁ y₂ : Fin n}
    (hy₁ : y₁ ∈ A.1) (hy₂ : y₂ ∈ A.1) (hne : y₁ ≠ y₂) :
    Disjoint (blockCoordNe K L (C_int := C_int) A y₁ c) (blockCoordNe K L A y₂ c) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  have hneA : e ≠ Sum.inl (A, c) := (Finset.mem_erase.mp he₁).1
  have hb₁ := Finset.mem_of_mem_erase he₁
  have hb₂ := Finset.mem_of_mem_erase he₂
  simp only [blockCoord, realVC, dummyCoord, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and] at hb₁ hb₂
  rcases hb₁ with ⟨B₁, ⟨hy₁B₁, _⟩, rfl⟩ | ⟨j₁, _, rfl⟩
  · rcases hb₂ with ⟨B₂, ⟨hy₂B₂, _⟩, hEq⟩ | ⟨_, _, hEq⟩
    · have hB : B₁ = B₂ := congrArg Prod.fst (Sum.inl.inj hEq.symm)
      subst hB
      have hAB : A.1 ≠ B₁.1 := fun h => hneA (by rw [Subtype.ext h])
      have h2 : ({y₁, y₂} : Finset (Fin n)) ⊆ A.1 ∩ B₁.1 := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hy₁, hy₁B₁⟩
        · exact Finset.mem_inter.mpr ⟨hy₂, hy₂B₂⟩
      have hcard : 2 ≤ (A.1 ∩ B₁.1).card := by
        have hp : ({y₁, y₂} : Finset (Fin n)).card = 2 := Finset.card_pair hne
        exact hp ▸ Finset.card_le_card h2
      have hle := hlin A.1 A.2 B₁.1 B₁.2 hAB
      omega
    · exact Sum.inl_ne_inr hEq.symm
  · rcases hb₂ with ⟨_, _, hEq⟩ | ⟨j₂, _, hEq⟩
    · exact Sum.inl_ne_inr hEq
    · exact hne (congrArg Prod.fst (Sum.inr.inj hEq.symm))

lemma card_edgeColorBlock {n m C_int r : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m))
    (hunif : ∀ E ∈ K, E.card = r)
    (hlin : ∀ E ∈ K, ∀ F ∈ K, E ≠ F → (E ∩ F).card ≤ 1)
    (hdeg : ∀ x c, (K.filter (fun B => x ∈ B ∧ c ∈ L B)).card ≤ C_int)
    (A : ↥K) {c : Fin m} (hc : c ∈ L A.1) :
    (edgeColorBlock K L (C_int := C_int) A c).card = r * (C_int - 1) := by
  unfold edgeColorBlock
  rw [Finset.card_biUnion]
  · calc ∑ y ∈ A.1, (blockCoordNe K L (C_int := C_int) A y c).card
        = ∑ _y ∈ A.1, (C_int - 1) :=
          Finset.sum_congr rfl fun y hy => card_blockCoordNe K L (hdeg y c) hy hc
      _ = A.1.card * (C_int - 1) := by simp
      _ = r * (C_int - 1) := by rw [hunif A.1 A.2]
  · intro y₁ hy₁ y₂ hy₂ hne
    exact disjoint_blockCoordNe_vert K L hlin A c hy₁ hy₂ hne

lemma card_edgeColorBlock_erase {n m C_int r : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m))
    (hunif : ∀ E ∈ K, E.card = r)
    (hlin : ∀ E ∈ K, ∀ F ∈ K, E ≠ F → (E ∩ F).card ≤ 1)
    (hdeg : ∀ x c, (K.filter (fun B => x ∈ B ∧ c ∈ L B)).card ≤ C_int)
    (A : ↥K) {x : Fin n} (hx : x ∈ A.1) {c : Fin m} (hc : c ∈ L A.1) :
    ((A.1.erase x).biUnion (fun y => blockCoordNe K L (C_int := C_int) A y c)).card =
      (r - 1) * (C_int - 1) := by
  rw [Finset.card_biUnion]
  · calc ∑ y ∈ A.1.erase x, (blockCoordNe K L (C_int := C_int) A y c).card
        = ∑ _y ∈ A.1.erase x, (C_int - 1) :=
          Finset.sum_congr rfl fun y hy =>
            card_blockCoordNe K L (hdeg y c) (Finset.mem_of_mem_erase hy) hc
      _ = (A.1.erase x).card * (C_int - 1) := by simp
      _ = (r - 1) * (C_int - 1) := by rw [Finset.card_erase_of_mem hx, hunif A.1 A.2]
  · intro y₁ hy₁ y₂ hy₂ hne
    exact disjoint_blockCoordNe_vert K L hlin A c
      (Finset.mem_of_mem_erase hy₁) (Finset.mem_of_mem_erase hy₂) hne

lemma isColored_proper {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (ω : LCoord K m C_int → Fin Q)
    {A B : ↥K} (hAB : A ≠ B) (hinter : (A.1 ∩ B.1).Nonempty)
    {c₁ c₂ : Fin m} (hA : isColored K L ω A c₁) (hB : isColored K L ω B c₂) :
    c₁ ≠ c₂ := by
  intro heq
  subst heq
  rcases hinter with ⟨y, hy⟩
  rcases Finset.mem_inter.mp hy with ⟨hyA, hyB⟩
  have hmem : (Sum.inl (B, c₁) : LCoord K m C_int) ∈ edgeColorBlock K L A c₁ := by
    refine Finset.mem_biUnion.mpr ⟨y, hyA, Finset.mem_erase.mpr ⟨?_, mem_blockCoord_self K L hyB hB.1⟩⟩
    intro h
    exact hAB (congrArg Prod.fst (Sum.inl.inj h)).symm
  exact hA.2.2.2 _ hmem hB.2.1

lemma isColored_disjoint_nextList {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (ω : LCoord K m C_int → Fin Q)
    {A B : ↥K} (hAB : A ≠ B) (hinter : (A.1 ∩ B.1).Nonempty)
    {c : Fin m} (hB : isColored K L ω B c) :
    c ∉ nextList K L ω A := by
  intro hc
  rcases hinter with ⟨y, hy⟩
  rcases Finset.mem_inter.mp hy with ⟨hyA, hyB⟩
  have hmem : (Sum.inl (B, c) : LCoord K m C_int) ∈ edgeColorBlock K L A c := by
    refine Finset.mem_biUnion.mpr ⟨y, hyA, Finset.mem_erase.mpr ⟨?_, mem_blockCoord_self K L hyB hB.1⟩⟩
    intro h
    exact hAB (congrArg Prod.fst (Sum.inl.inj h)).symm
  exact (Finset.mem_filter.mp hc).2 _ hmem hB.2.1

lemma roundColoring_isColored {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (hm : 0 < m)
    (ω : LCoord K m C_int → Fin Q) {A : Finset (Fin n)} (hA : A ∈ K \ survEdges K L ω) :
    ∃ hAK : A ∈ K, isColored K L ω ⟨A, hAK⟩ (roundColoring K L hm ω A) := by
  rcases Finset.mem_sdiff.mp hA with ⟨hAK, hns⟩
  simp only [survEdges, Finset.mem_filter] at hns
  push Not at hns
  rcases hns hAK with ⟨_, c, _, hc⟩
  have hex : ∃ (hAK'' : A ∈ K) (c : Fin m), isColored K L ω ⟨A, hAK''⟩ c := ⟨hAK, c, hc⟩
  refine ⟨hAK, ?_⟩
  have hspec := Classical.choose_spec (Classical.choose_spec hex)
  simpa only [roundColoring, dif_pos hex] using hspec

/-- Concentration bound for the surviving list size of a fixed edge `A`. -/
lemma list_bad_bound {n m C_int r Q L_int : ℕ}
    (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hr : 4 ≤ r) (hQ : 0 < Q)
    (hunif : ∀ E ∈ K, E.card = r)
    (hlin : ∀ E ∈ K, ∀ F ∈ K, E ≠ F → (E ∩ F).card ≤ 1)
    (hL_card : ∀ E ∈ K, (L E).card = L_int)
    (hdeg : ∀ x c, (K.filter (fun B => x ∈ B ∧ c ∈ L B)).card ≤ C_int)
    (ε η L_t C_t : ℝ)
    (hε0 : 0 < ε) (hη0 : 0 < η) (hηε : η ≤ ε) (hrε : (r : ℝ) * ε ^ 2 ≤ 1)
    (hC0 : 0 < C_t) (hCL : C_t ≤ L_t)
    (hC_int_le : (C_int : ℝ) ≤ C_t)
    (hL_int_lo : L_t - 1 ≤ (L_int : ℝ)) (hL_int_hi : (L_int : ℝ) ≤ L_t)
    (hQp : 1 / (Q : ℝ) ≤ ε / L_t) (hQ2 : 1 / (Q : ℝ) ≤ 1 / 2)
    (hL_big : 2 / η ≤ L_t)
    (A : ↥K) :
    ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      ((nextList K L ω A).card : ℝ) <
        L_t * (Real.exp (-(r : ℝ) * ε * (C_t / L_t)) - 2 * η))).card : ℝ) ≤
      2 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
        (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
  have hL0 : 0 < L_t := lt_of_lt_of_le hC0 hCL
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  let f : (LCoord K m C_int → Fin Q) → ℝ := fun ω => ((nextList K L ω A).card : ℝ)
  let S := depList K L (C_int := C_int) A
  have hS_card : (S.card : ℝ) ≤ (r : ℝ) * L_t * C_t := by
    have h1 : S.card ≤ ∑ c ∈ L A.1, (edgeColorBlock K L (C_int := C_int) A c).card :=
      Finset.card_biUnion_le
    have h2 : ∑ c ∈ L A.1, (edgeColorBlock K L (C_int := C_int) A c).card =
        L_int * (r * (C_int - 1)) := by
      calc ∑ c ∈ L A.1, (edgeColorBlock K L (C_int := C_int) A c).card
          = ∑ _c ∈ L A.1, (r * (C_int - 1)) :=
            Finset.sum_congr rfl fun c hc => card_edgeColorBlock K L hunif hlin hdeg A hc
        _ = (L A.1).card * (r * (C_int - 1)) := by simp
        _ = L_int * (r * (C_int - 1)) := by rw [hL_card A.1 A.2]
    have h3 : S.card ≤ L_int * (r * C_int) :=
      h1.trans (h2.le.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))))
    have h3' : (S.card : ℝ) ≤ (L_int : ℝ) * ((r : ℝ) * (C_int : ℝ)) := by exact_mod_cast h3
    have h4 : (L_int : ℝ) * ((r : ℝ) * (C_int : ℝ)) ≤ L_t * ((r : ℝ) * C_t) := by
      have hrc : (r : ℝ) * (C_int : ℝ) ≤ (r : ℝ) * C_t :=
        mul_le_mul_of_nonneg_left hC_int_le hr_pos.le
      exact mul_le_mul hL_int_hi hrc (by positivity) hL0.le
    linarith [h3', h4]
  have hV_ge : (∑ _e ∈ S, (1 : ℝ) ^ 2) / (Q : ℝ) ≤ (r : ℝ) * ε * C_t := by
    simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    calc (S.card : ℝ) / (Q : ℝ) = (S.card : ℝ) * (1 / (Q : ℝ)) := by ring
      _ ≤ ((r : ℝ) * L_t * C_t) * (ε / L_t) :=
        mul_le_mul hS_card hQp (by positivity) (by positivity)
      _ = (r : ℝ) * ε * C_t := by field_simp
  have hdep : ∀ ω₁ ω₂ : LCoord K m C_int → Fin Q, (∀ e ∈ S, ω₁ e = ω₂ e) → f ω₁ = f ω₂ := by
    intro ω₁ ω₂ hEq
    simp only [f, nextList]
    congr 2
    refine Finset.filter_congr fun c hc => forall₂_congr fun e he => ?_
    rw [hEq e (Finset.mem_biUnion.mpr ⟨c, hc, he⟩)]
  have hconst : ∀ e ∈ S, ∀ ω (a b : Fin Q), a.val ≠ 0 → b.val ≠ 0 →
      f (Function.update ω e a) = f (Function.update ω e b) := by
    intro e _ ω a b ha hb
    simp only [f, nextList]
    congr 2
    refine Finset.filter_congr fun c _ => forall₂_congr fun e' _ => ?_
    by_cases h : e' = e
    · subst h; simp [ha, hb]
    · simp [Function.update_of_ne h]
  have hlip : ∀ e ∈ S, ∀ ω (a : Fin Q), a.val ≠ 0 →
      |f (Function.update ω e ⟨0, hQ⟩) - f (Function.update ω e a)| ≤ 1 := by
    intro e _ ω a ha
    have hsub₁ : nextList K L (Function.update ω e ⟨0, hQ⟩) A ⊆
        nextList K L (Function.update ω e a) A := by
      intro c hc
      rcases Finset.mem_filter.mp hc with ⟨hcL, hall⟩
      refine Finset.mem_filter.mpr ⟨hcL, fun e' he' => ?_⟩
      by_cases h : e' = e
      · subst h; simpa using ha
      · simpa [Function.update_of_ne h] using hall e' he'
    have hsub₂ : nextList K L (Function.update ω e a) A ⊆
        nextList K L (Function.update ω e ⟨0, hQ⟩) A ∪ {coordColor e} := by
      intro c hc
      rcases Finset.mem_filter.mp hc with ⟨hcL, hall⟩
      by_cases hcc : c = coordColor e
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hcc)
      · apply Finset.mem_union_left
        refine Finset.mem_filter.mpr ⟨hcL, fun e' he' => ?_⟩
        have hne : e' ≠ e := fun h => hcc (h ▸ coordColor_mem_edgeColorBlock he').symm
        simpa [Function.update_of_ne hne] using hall e' he'
    have habs := abs_card_sub_le hsub₁ hsub₂
    simpa [f] using habs
  have hμ_eq : (∑ ω : LCoord K m C_int → Fin Q, f ω) /
      (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) =
      (L_int : ℝ) * (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) := by
    have havg := avg_sum_disjoint_filter (X := LCoord K m C_int) Q hQ (L A.1)
      (fun c => edgeColorBlock K L A c)
    have hμ1 : (∑ ω : LCoord K m C_int → Fin Q, f ω) /
        (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) =
        ∑ c ∈ L A.1, (1 - 1 / (Q : ℝ)) ^ (edgeColorBlock K L (C_int := C_int) A c).card := by
      refine (congrArg (· / (Fintype.card (LCoord K m C_int → Fin Q) : ℝ))
        (Finset.sum_congr rfl fun ω _ => ?_)).trans havg
      simp only [f, nextList]
      exact congrArg (fun s : Finset (Fin m) => (s.card : ℝ)) (by ext c; simp only [Finset.mem_filter])
    rw [hμ1]
    calc ∑ c ∈ L A.1, (1 - 1 / (Q : ℝ)) ^ (edgeColorBlock K L (C_int := C_int) A c).card
        = ∑ _c ∈ L A.1, (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) :=
          Finset.sum_congr rfl fun c hc => by rw [card_edgeColorBlock K L hunif hlin hdeg A hc]
      _ = (L_int : ℝ) * (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hL_card A.1 A.2]
  have hμ_lo : L_t * (Real.exp (-(r : ℝ) * ε * (C_t / L_t)) - 2 * η) + η * L_t ≤
      (L_int : ℝ) * (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) := by
    have hp0 : 0 ≤ 1 / (Q : ℝ) := by positivity
    have hbase : Real.exp (-(1 / (Q : ℝ)) - (1 / (Q : ℝ)) ^ 2) ≤ 1 - 1 / (Q : ℝ) :=
      one_sub_ge_exp_neg_sub_sq_half hp0 hQ2
    have hpow : Real.exp (-((r * (C_int - 1) : ℕ) : ℝ) * (1 / (Q : ℝ) + (1 / (Q : ℝ)) ^ 2)) ≤
        (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) := by
      calc Real.exp (-((r * (C_int - 1) : ℕ) : ℝ) * (1 / (Q : ℝ) + (1 / (Q : ℝ)) ^ 2))
          = Real.exp (((r * (C_int - 1) : ℕ) : ℝ) * (-(1 / (Q : ℝ)) - (1 / (Q : ℝ)) ^ 2)) := by
            congr 1; ring
        _ = (Real.exp (-(1 / (Q : ℝ)) - (1 / (Q : ℝ)) ^ 2)) ^ (r * (C_int - 1)) :=
            Real.exp_nat_mul _ _
        _ ≤ (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) :=
            pow_le_pow_left₀ (Real.exp_pos _).le hbase _
    have hCsub : ((C_int - 1 : ℕ) : ℝ) ≤ C_t :=
      (Nat.cast_le.mpr (Nat.sub_le C_int 1)).trans hC_int_le
    have harg_le : ((r * (C_int - 1) : ℕ) : ℝ) * (1 / (Q : ℝ) + (1 / (Q : ℝ)) ^ 2) ≤
        (r : ℝ) * ε * (C_t / L_t) + (r : ℝ) * ε ^ 2 / L_t := by
      have hrc : ((r * (C_int - 1) : ℕ) : ℝ) ≤ (r : ℝ) * C_t := by
        rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_left hCsub hr_pos.le
      have hqsq : (1 / (Q : ℝ)) ^ 2 ≤ (ε / L_t) ^ 2 :=
        pow_le_pow_left₀ hp0 hQp 2
      have hsum : 1 / (Q : ℝ) + (1 / (Q : ℝ)) ^ 2 ≤ ε / L_t + (ε / L_t) ^ 2 := add_le_add hQp hqsq
      have h1 : ((r * (C_int - 1) : ℕ) : ℝ) * (1 / (Q : ℝ) + (1 / (Q : ℝ)) ^ 2) ≤
          ((r : ℝ) * C_t) * (ε / L_t + (ε / L_t) ^ 2) :=
        mul_le_mul hrc hsum (by positivity) (by positivity)
      have h2 : ((r : ℝ) * C_t) * (ε / L_t) ^ 2 ≤ (r : ℝ) * ε ^ 2 / L_t := by
        have hCL' : C_t / L_t ≤ 1 := (div_le_one hL0).mpr hCL
        calc ((r : ℝ) * C_t) * (ε / L_t) ^ 2 = (C_t / L_t) * ((r : ℝ) * ε ^ 2 / L_t) := by
              field_simp
          _ ≤ 1 * ((r : ℝ) * ε ^ 2 / L_t) :=
              mul_le_mul_of_nonneg_right hCL' (by positivity)
          _ = (r : ℝ) * ε ^ 2 / L_t := one_mul _
      have h3 : ((r : ℝ) * C_t) * (ε / L_t + (ε / L_t) ^ 2) =
          (r : ℝ) * ε * (C_t / L_t) + ((r : ℝ) * C_t) * (ε / L_t) ^ 2 := by ring
      linarith [h1, h2, h3]
    have hexp_lo : Real.exp (-(r : ℝ) * ε * (C_t / L_t)) - (r : ℝ) * ε ^ 2 / L_t ≤
        (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) := by
      have ha : 0 ≤ (r : ℝ) * ε * (C_t / L_t) := by positivity
      have hb : 0 ≤ (r : ℝ) * ε ^ 2 / L_t := by positivity
      have hstep1 : Real.exp (-(r : ℝ) * ε * (C_t / L_t) - (r : ℝ) * ε ^ 2 / L_t) ≤
          (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) := by
        refine (Real.exp_le_exp.mpr ?_).trans hpow
        linarith [harg_le]
      have hstep2 : Real.exp (-(r : ℝ) * ε * (C_t / L_t)) - (r : ℝ) * ε ^ 2 / L_t ≤
          Real.exp (-(r : ℝ) * ε * (C_t / L_t) - (r : ℝ) * ε ^ 2 / L_t) := by
        rw [show -(r : ℝ) * ε * (C_t / L_t) - (r : ℝ) * ε ^ 2 / L_t =
            -(r : ℝ) * ε * (C_t / L_t) + -((r : ℝ) * ε ^ 2 / L_t) by ring, Real.exp_add]
        have h1 : 1 - (r : ℝ) * ε ^ 2 / L_t ≤ Real.exp (-((r : ℝ) * ε ^ 2 / L_t)) := by
          linarith [Real.add_one_le_exp (-((r : ℝ) * ε ^ 2 / L_t))]
        have hle1 : Real.exp (-(r : ℝ) * ε * (C_t / L_t)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [ha]
        have h2 : Real.exp (-(r : ℝ) * ε * (C_t / L_t)) * (1 - (r : ℝ) * ε ^ 2 / L_t) ≤
            Real.exp (-(r : ℝ) * ε * (C_t / L_t)) * Real.exp (-((r : ℝ) * ε ^ 2 / L_t)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        have h3 : Real.exp (-(r : ℝ) * ε * (C_t / L_t)) * ((r : ℝ) * ε ^ 2 / L_t) ≤
            (r : ℝ) * ε ^ 2 / L_t := by
          calc Real.exp (-(r : ℝ) * ε * (C_t / L_t)) * ((r : ℝ) * ε ^ 2 / L_t)
              ≤ 1 * ((r : ℝ) * ε ^ 2 / L_t) := mul_le_mul_of_nonneg_right hle1 hb
            _ = (r : ℝ) * ε ^ 2 / L_t := one_mul _
        linarith [h2, h3]
      exact hstep2.trans hstep1
    have hL_eta : 2 ≤ η * L_t := by
      have := mul_le_mul_of_nonneg_left hL_big hη0.le
      have hcan : η * (2 / η) = 2 := by field_simp
      linarith [this, hcan]
    have hL1_nn : 0 ≤ L_t - 1 := by
      have hε_half : ε ≤ 1 / 2 := by nlinarith only [hr4, hrε, hε0]
      nlinarith only [hL_eta, hηε, hε_half, hL0, hη0]
    have hprod1 : (L_t - 1) * (Real.exp (-(r : ℝ) * ε * (C_t / L_t)) - (r : ℝ) * ε ^ 2 / L_t) ≤
        (L_int : ℝ) * (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) := by
      have hpow_nn : 0 ≤ (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) := pow_nonneg (by linarith) _
      calc (L_t - 1) * (Real.exp (-(r : ℝ) * ε * (C_t / L_t)) - (r : ℝ) * ε ^ 2 / L_t)
          ≤ (L_t - 1) * (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) :=
            mul_le_mul_of_nonneg_left hexp_lo hL1_nn
        _ ≤ (L_int : ℝ) * (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) :=
            mul_le_mul_of_nonneg_right hL_int_lo hpow_nn
    have hle1 : Real.exp (-(r : ℝ) * ε * (C_t / L_t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (r : ℝ) * ε * (C_t / L_t) := by positivity
      linarith
    have hmul_eq : L_t * ((r : ℝ) * ε ^ 2 / L_t) = (r : ℝ) * ε ^ 2 := by field_simp
    have hdiv_nn : 0 ≤ (r : ℝ) * ε ^ 2 / L_t := by positivity
    linarith [hprod1, hle1, hmul_eq, hdiv_nn, hrε, hL_eta]
  have hmc := bernoulli_mcdiarmid_sub Q hQ S (fun _ => 1) f 1 ((r : ℝ) * ε * C_t) (η * L_t)
    one_pos (by positivity) (by positivity)
    (fun _ _ => zero_le_one) (fun _ _ => le_rfl) hV_ge hdep hconst hlip
  have hsub_ev : Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      f ω < L_t * (Real.exp (-(r : ℝ) * ε * (C_t / L_t)) - 2 * η)) ⊆
      Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
        η * L_t ≤ |f ω - (∑ ω' : LCoord K m C_int → Fin Q, f ω') /
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ)|) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rw [hμ_eq]
    have : η * L_t ≤ (L_int : ℝ) * (1 - 1 / (Q : ℝ)) ^ (r * (C_int - 1)) - f ω := by
      linarith [hω, hμ_lo]
    exact this.trans (by rw [← neg_sub]; exact neg_le_abs _)
  have hexp_cmp : η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) * C_t ≤
      min ((η * L_t) ^ 2 / (4 * ((r : ℝ) * ε * C_t))) (η * L_t / (2 * 1)) := by
    apply le_min
    · have h1 : (η * L_t) ^ 2 / (4 * ((r : ℝ) * ε * C_t)) ≥
          (η * C_t) ^ 2 / (4 * ((r : ℝ) * ε * C_t)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hCL hη0.le) 2
      have h2 : (η * C_t) ^ 2 / (4 * ((r : ℝ) * ε * C_t)) = η ^ 2 / (4 * (r : ℝ) * ε) * C_t := by
        field_simp
      have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith only [hr4]
      have hden : 4 * (r : ℝ) * ε ≤ 32 * (r : ℝ) ^ 3 * ε := by
        have : (r : ℝ) ≤ 8 * (r : ℝ) ^ 3 := by nlinarith only [hr4, hr2]
        nlinarith only [this, hε0]
      have h3 : η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) ≤ η ^ 2 / (4 * (r : ℝ) * ε) :=
        div_le_div_of_nonneg_left (sq_nonneg η) (by positivity) hden
      have h4 := mul_le_mul_of_nonneg_right h3 hC0.le
      linarith [h1, h2, h4]
    · have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith only [hr4]
      have hr3 : (1 : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith only [hr4, hr2]
      have hrat : η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) ≤ η / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : 2 * η ≤ 32 * (r : ℝ) ^ 3 * ε := by nlinarith only [hηε, hr3, hε0]
        nlinarith only [h1, hη0]
      calc η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) * C_t ≤ (η / 2) * C_t :=
            mul_le_mul_of_nonneg_right hrat hC0.le
        _ ≤ (η / 2) * L_t := mul_le_mul_of_nonneg_left hCL (by positivity)
        _ = η * L_t / (2 * 1) := by ring
  calc ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
          f ω < L_t * (Real.exp (-(r : ℝ) * ε * (C_t / L_t)) - 2 * η))).card : ℝ)
      ≤ ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
          η * L_t ≤ |f ω - (∑ ω' : LCoord K m C_int → Fin Q, f ω') /
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ)|)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub_ev)
    _ ≤ 2 * Real.exp (-min ((η * L_t) ^ 2 / (4 * ((r : ℝ) * ε * C_t))) (η * L_t / (2 * 1))) *
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := hmc
    _ ≤ 2 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (Nat.cast_nonneg _)
        rw [Real.exp_le_exp]; linarith [hexp_cmp]

/-- Active trial coordinates on edge subset `F` using lists `listSub L c_excl`. -/
def subTrials {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m)) :
    Finset (LCoord K m C_int) :=
  F.biUnion (fun A => (listSub L c_excl A).image (fun c' => Sum.inl (A, c')))

/-- Selected trial coordinates inside `subTrials`. -/
noncomputable def selTrials {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m))
    (ω : LCoord K m C_int → Fin Q) : Finset (LCoord K m C_int) :=
  (subTrials K L F c_excl).filter (fun e => (ω e).val = 0)

/-- Edges in `F` that have at least one selected trial in `listSub`. -/
noncomputable def rowHit {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m))
    (ω : LCoord K m C_int → Fin Q) : Finset ↥K :=
  F.filter (fun A => ∃ c' ∈ listSub L c_excl A, (ω (Sum.inl (A, c'))).val = 0)

/-- Colors that appear in at least one selected trial of `F`. -/
noncomputable def colHit {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m))
    (ω : LCoord K m C_int → Fin Q) : Finset (Fin m) :=
  Finset.univ.filter (fun c' => ∃ A ∈ F, c' ∈ listSub L c_excl A ∧ (ω (Sum.inl (A, c'))).val = 0)

/-- Clean selected pairs `(A, c')` that are unique both in row `A` and in column `c'`. -/
noncomputable def cleanPairs {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m))
    (ω : LCoord K m C_int → Fin Q) : Finset (↥K × Fin m) :=
  (F ×ˢ (Finset.univ : Finset (Fin m))).filter (fun p =>
    p.2 ∈ listSub L c_excl p.1 ∧ (ω (Sum.inl p)).val = 0 ∧
    (∀ c'' ∈ listSub L c_excl p.1, c'' ≠ p.2 → (ω (Sum.inl (p.1, c''))).val ≠ 0) ∧
    (∀ B ∈ F, B ≠ p.1 → p.2 ∈ listSub L c_excl B → (ω (Sum.inl (B, p.2))).val ≠ 0))

/-- External blocking coordinates for a clean pair `p = (A, c')` outside `subTrials`. -/
def hitCoords {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m))
    (p : ↥K × Fin m) : Finset (LCoord K m C_int) :=
  ((L p.1.1 \ listSub L c_excl p.1).image (fun c'' => Sum.inl (p.1, c''))) ∪
  (edgeColorBlock K L p.1 p.2 \ subTrials K L F c_excl)

/-- Clean pairs blocked by some coordinate in `hitCoords`. -/
noncomputable def hitClean {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m))
    (ω : LCoord K m C_int → Fin Q) : Finset (↥K × Fin m) :=
  (cleanPairs K L F c_excl ω).filter (fun p => ∃ e ∈ hitCoords K L F c_excl p, (ω e).val = 0)

/-- Edges in `F` not colored by any color in `listSub`. -/
noncomputable def uncoloredSub {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m))
    (ω : LCoord K m C_int → Fin Q) : Finset ↥K :=
  F.filter (fun A => ∀ c' ∈ listSub L c_excl A, ¬ isColored K L ω A c')

/-- Deterministic waste decomposition for `uncoloredSub`. -/
lemma card_uncoloredSub_le {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m))
    (ω : LCoord K m C_int → Fin Q) :
    ((uncoloredSub K L F c_excl ω).card : ℝ) ≤
      ((F.card : ℝ) - ((rowHit K L F c_excl ω).card : ℝ)) +
      (((selTrials K L F c_excl ω).card : ℝ) - ((rowHit K L F c_excl ω).card : ℝ)) +
      2 * (((selTrials K L F c_excl ω).card : ℝ) - ((colHit K L F c_excl ω).card : ℝ)) +
      ((hitClean K L F c_excl ω).card : ℝ) := by
  let S := selTrials K L F c_excl ω
  let U := rowHit K L F c_excl ω
  let Col := colHit K L F c_excl ω
  let rowS : ↥K → Finset (Fin m) := fun A =>
    (listSub L c_excl A).filter (fun c' => (ω (Sum.inl (A, c'))).val = 0)
  let colS : Fin m → Finset ↥K := fun c' =>
    F.filter (fun A => c' ∈ listSub L c_excl A ∧ (ω (Sum.inl (A, c'))).val = 0)
  have hS_row : S.card = ∑ A ∈ U, (rowS A).card := by
    have heq : S = U.biUnion (fun A => (rowS A).image (fun c' => Sum.inl (A, c'))) := by
      ext e
      simp only [S, selTrials, subTrials, U, rowHit, rowS, Finset.mem_filter, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨A, hAF, c', hc', rfl⟩, h0⟩
        exact ⟨A, ⟨hAF, c', hc', h0⟩, c', ⟨hc', h0⟩, rfl⟩
      · rintro ⟨A, ⟨hAF, _⟩, c', ⟨hc', h0⟩, rfl⟩
        exact ⟨⟨A, hAF, c', hc', rfl⟩, h0⟩
    rw [heq, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun A _ => Finset.card_image_of_injective _ ?_
      intro c₁ c₂ h; exact congrArg Prod.snd (Sum.inl.inj h)
    · intro A₁ _ A₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro e h₁ h₂
      rcases Finset.mem_image.mp h₁ with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp h₂ with ⟨_, _, hEq⟩
      exact hne (congrArg Prod.fst (Sum.inl.inj hEq.symm))
  have hS_col : S.card = ∑ c' ∈ Col, (colS c').card := by
    have heq : S = Col.biUnion (fun c' => (colS c').image (fun A => Sum.inl (A, c'))) := by
      ext e
      simp only [S, selTrials, subTrials, Col, colHit, colS, Finset.mem_filter, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨A, hAF, c', hc', rfl⟩, h0⟩
        exact ⟨c', ⟨A, hAF, hc', h0⟩, A, ⟨hAF, hc', h0⟩, rfl⟩
      · rintro ⟨c', _, A, ⟨hAF, hc', h0⟩, rfl⟩
        exact ⟨⟨A, hAF, c', hc', rfl⟩, h0⟩
    rw [heq, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun c' _ => Finset.card_image_of_injective _ ?_
      intro A₁ A₂ h; exact congrArg Prod.fst (Sum.inl.inj h)
    · intro c₁ _ c₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro e h₁ h₂
      rcases Finset.mem_image.mp h₁ with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp h₂ with ⟨_, _, hEq⟩
      exact hne (congrArg Prod.snd (Sum.inl.inj hEq.symm))
  have hU_le_F : U.card ≤ F.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hU_le_S : U.card ≤ S.card := by
    rw [hS_row]
    calc U.card = ∑ _A ∈ U, 1 := by simp
      _ ≤ ∑ A ∈ U, (rowS A).card := Finset.sum_le_sum fun A hA => by
          rcases (Finset.mem_filter.mp hA).2 with ⟨c', hc', h0⟩
          exact Finset.card_pos.mpr ⟨c', Finset.mem_filter.mpr ⟨hc', h0⟩⟩
  have hCol_le_S : Col.card ≤ S.card := by
    rw [hS_col]
    calc Col.card = ∑ _c' ∈ Col, 1 := by simp
      _ ≤ ∑ c' ∈ Col, (colS c').card := Finset.sum_le_sum fun c' hc' => by
          rcases (Finset.mem_filter.mp hc').2 with ⟨A, hAF, hcL, h0⟩
          exact Finset.card_pos.mpr ⟨A, Finset.mem_filter.mpr ⟨hAF, hcL, h0⟩⟩
  let P1 := F \ U
  let P2 := U.filter (fun A => 2 ≤ (rowS A).card)
  let P3 := (U \ P2).filter (fun A => ∃ c' ∈ rowS A, 2 ≤ (colS c').card)
  let P4 := (uncoloredSub K L F c_excl ω).filter
    (fun A => A ∈ U ∧ (rowS A).card = 1 ∧ ∀ c' ∈ rowS A, (colS c').card = 1)
  have hcov : uncoloredSub K L F c_excl ω ⊆ P1 ∪ P2 ∪ P3 ∪ P4 := by
    intro A hA
    have hAF : A ∈ F := (Finset.mem_filter.mp hA).1
    by_cases hAU : A ∈ U
    · have hpos : 1 ≤ (rowS A).card := by
        rcases (Finset.mem_filter.mp hAU).2 with ⟨c', hc', h0⟩
        exact Finset.card_pos.mpr ⟨c', Finset.mem_filter.mpr ⟨hc', h0⟩⟩
      by_cases h2 : 2 ≤ (rowS A).card
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hAU, h2⟩)))
      · have hr1 : (rowS A).card = 1 := by omega
        by_cases h3 : ∃ c' ∈ rowS A, 2 ≤ (colS c').card
        · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hAU, fun h => h2 (Finset.mem_filter.mp h).2⟩, h3⟩
        · push Not at h3
          refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA, hAU, hr1, fun c' hc' => ?_⟩)
          have hcp : 1 ≤ (colS c').card := by
            rcases Finset.mem_filter.mp hc' with ⟨hcL, h0⟩
            exact Finset.card_pos.mpr ⟨A, Finset.mem_filter.mpr ⟨hAF, hcL, h0⟩⟩
          have hlt := h3 c' hc'
          omega
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hAF, hAU⟩)))
  have hP1 : P1.card = F.card - U.card := by
    have h1 : P1.card + U.card = F.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ F : U ⊆ F)
    omega
  have hP2 : P2.card ≤ S.card - U.card := by
    have hsum : ∑ A ∈ U, 1 + P2.card ≤ ∑ A ∈ U, (rowS A).card := by
      have h1 : P2.card = ∑ A ∈ U, if 2 ≤ (rowS A).card then 1 else 0 := by
        dsimp only [P2]; rw [Finset.card_filter]
      rw [h1, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun A hA => ?_
      split_ifs with h2
      · omega
      · rcases (Finset.mem_filter.mp hA).2 with ⟨c', hc', h0⟩
        have hpos : 0 < (rowS A).card := by
          dsimp only [rowS]; exact Finset.card_pos.mpr ⟨c', Finset.mem_filter.mpr ⟨hc', h0⟩⟩
        omega
    rw [Finset.sum_const, smul_eq_mul, mul_one, ← hS_row] at hsum
    omega
  have hP3 : P3.card ≤ 2 * (S.card - Col.card) := by
    let colMulti := (Col.filter (fun c' => 2 ≤ (colS c').card)).biUnion
      (fun c' => (colS c').image (fun A => (A, c')))
    have hP3_sub : P3 ⊆ colMulti.image Prod.fst := by
      intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hAU2, c', hc'r, hc'2⟩
      have hAU : A ∈ U := (Finset.mem_sdiff.mp hAU2).1
      have hAF : A ∈ F := (Finset.mem_filter.mp hAU).1
      rcases Finset.mem_filter.mp hc'r with ⟨hc'L, h0⟩
      refine Finset.mem_image.mpr ⟨(A, c'), ?_, rfl⟩
      refine Finset.mem_biUnion.mpr ⟨c', Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨A, hAF, hc'L, h0⟩⟩, hc'2⟩,
        Finset.mem_image.mpr ⟨A, Finset.mem_filter.mpr ⟨hAF, hc'L, h0⟩, rfl⟩⟩
    have hP3_le_m : P3.card ≤ colMulti.card :=
      (Finset.card_le_card hP3_sub).trans Finset.card_image_le
    have hm_le : colMulti.card ≤ ∑ c' ∈ Col, if 2 ≤ (colS c').card then (colS c').card else 0 := by
      calc colMulti.card
          ≤ ∑ c' ∈ Col.filter (fun c' => 2 ≤ (colS c').card),
              ((colS c').image (fun A => (A, c'))).card := Finset.card_biUnion_le
        _ ≤ ∑ c' ∈ Col.filter (fun c' => 2 ≤ (colS c').card), (colS c').card :=
            Finset.sum_le_sum fun c' _ => Finset.card_image_le
        _ = ∑ c' ∈ Col, if 2 ≤ (colS c').card then (colS c').card else 0 := by
            rw [Finset.sum_filter]
    have hsum_le : (∑ c' ∈ Col, if 2 ≤ (colS c').card then (colS c').card else 0) + 2 * Col.card ≤
        2 * S.card := by
      rw [hS_col, Finset.mul_sum]
      have h2c : 2 * Col.card = ∑ _c' ∈ Col, 2 := by simp [mul_comm]
      rw [h2c, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun c' hc' => ?_
      split_ifs with h2
      · omega
      · rcases (Finset.mem_filter.mp hc').2 with ⟨A, hAF, hcL, h0⟩
        have hpos : 0 < (colS c').card := by
          dsimp only [colS]; exact Finset.card_pos.mpr ⟨A, Finset.mem_filter.mpr ⟨hAF, hcL, h0⟩⟩
        omega
    omega
  have hP4 : P4.card ≤ (hitClean K L F c_excl ω).card := by
    have hP4_sub : P4 ⊆ (hitClean K L F c_excl ω).image Prod.fst := by
      intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hAunc, hAU, hrow1, hcol1⟩
      have hAF : A ∈ F := (Finset.mem_filter.mp hAU).1
      rcases Finset.card_eq_one.mp hrow1 with ⟨c', hrc'⟩
      have hc'mem : c' ∈ rowS A := by rw [hrc']; exact Finset.mem_singleton_self c'
      rcases Finset.mem_filter.mp hc'mem with ⟨hc'L, h0⟩
      have hclean : (A, c') ∈ cleanPairs K L F c_excl ω := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hAF, Finset.mem_univ c'⟩,
          hc'L, h0, ?_, ?_⟩
        · intro c'' hc''L hne h0''
          have hmem'' : c'' ∈ rowS A := Finset.mem_filter.mpr ⟨hc''L, h0''⟩
          rw [hrc', Finset.mem_singleton] at hmem''
          exact hne hmem''
        · intro B hBF hBA hc'B h0B
          have hAcol : A ∈ colS c' := Finset.mem_filter.mpr ⟨hAF, hc'L, h0⟩
          have hBcol : B ∈ colS c' := Finset.mem_filter.mpr ⟨hBF, hc'B, h0B⟩
          have hcard1 := hcol1 c' hc'mem
          exact hBA (Finset.card_le_one.mp hcard1.le B hBcol A hAcol)
      have hnotcol : ¬ isColored K L ω A c' := (Finset.mem_filter.mp hAunc).2 c' hc'L
      have hc'LA : c' ∈ L A.1 := by
        cases c_excl with
        | none => exact hc'L
        | some c => exact Finset.mem_of_mem_erase hc'L
      have hhit : ∃ e ∈ hitCoords K L F c_excl (A, c'), (ω e).val = 0 := by
        by_contra hno
        push Not at hno
        apply hnotcol
        refine ⟨hc'LA, h0, ?_, ?_⟩
        · intro c'' hc''L hne
          by_cases hsub : c'' ∈ listSub L c_excl A
          · exact (Finset.mem_filter.mp hclean).2.2.2.1 c'' hsub hne
          · apply hno (Sum.inl (A, c''))
            exact Finset.mem_union_left _ (Finset.mem_image.mpr
              ⟨c'', Finset.mem_sdiff.mpr ⟨hc''L, hsub⟩, rfl⟩)
        · intro e he
          by_cases heT : e ∈ subTrials K L F c_excl
          · simp only [subTrials, Finset.mem_biUnion, Finset.mem_image] at heT
            rcases heT with ⟨B, hBF, c'', hc''B, rfl⟩
            have hc''_eq : c'' = c' := coordColor_mem_edgeColorBlock he
            subst hc''_eq
            have hBA : B ≠ A := by
              intro hEq
              subst hEq
              simp only [edgeColorBlock, blockCoordNe, Finset.mem_biUnion, Finset.mem_erase] at he
              rcases he with ⟨_, _, hne, _⟩
              exact hne rfl
            exact (Finset.mem_filter.mp hclean).2.2.2.2 B hBF hBA hc''B
          · exact hno e (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, heT⟩))
      exact Finset.mem_image.mpr ⟨(A, c'), Finset.mem_filter.mpr ⟨hclean, hhit⟩, rfl⟩
    exact (Finset.card_le_card hP4_sub).trans Finset.card_image_le
  have htot : (uncoloredSub K L F c_excl ω).card ≤ P1.card + P2.card + P3.card + P4.card := by
    calc (uncoloredSub K L F c_excl ω).card
        ≤ (P1 ∪ P2 ∪ P3 ∪ P4).card := Finset.card_le_card hcov
      _ ≤ (P1 ∪ P2 ∪ P3).card + P4.card := Finset.card_union_le _ _
      _ ≤ (P1 ∪ P2).card + P3.card + P4.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ P1.card + P2.card + P3.card + P4.card :=
          Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have htot_nat : (uncoloredSub K L F c_excl ω).card ≤
      (F.card - U.card) + (S.card - U.card) + 2 * (S.card - Col.card) +
        (hitClean K L F c_excl ω).card := by omega
  have h1 : ((F.card - U.card : ℕ) : ℝ) = (F.card : ℝ) - (U.card : ℝ) :=
    Nat.cast_sub hU_le_F
  have h2 : ((S.card - U.card : ℕ) : ℝ) = (S.card : ℝ) - (U.card : ℝ) :=
    Nat.cast_sub hU_le_S
  have h3 : ((S.card - Col.card : ℕ) : ℝ) = (S.card : ℝ) - (Col.card : ℝ) :=
    Nat.cast_sub hCol_le_S
  have htot_real : ((uncoloredSub K L F c_excl ω).card : ℝ) ≤
      ((F.card - U.card : ℕ) : ℝ) + ((S.card - U.card : ℕ) : ℝ) +
      2 * ((S.card - Col.card : ℕ) : ℝ) + ((hitClean K L F c_excl ω).card : ℝ) := by
    exact_mod_cast htot_nat
  linarith [htot_real, h1, h2, h3]

/-- Helper exponent comparison for `bernoulli_mcdiarmid_sub` with `V = ε * B_cap`, `t = η * B_cap`. -/
lemma sub_mcdiarmid_exp_le {r : ℕ} (hr : 4 ≤ r) {ε η C_t B_cap : ℝ}
    (hε0 : 0 < ε) (hη0 : 0 < η) (hηε : η ≤ ε) (hC0 : 0 < C_t) (hCB : C_t ≤ B_cap) :
    η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) * C_t ≤
      min ((η * B_cap) ^ 2 / (4 * (ε * B_cap))) (η * B_cap / (2 * 1)) := by
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith only [hr4]
  have hr3 : (1 : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith only [hr4, hr2]
  have hB0 : 0 < B_cap := lt_of_lt_of_le hC0 hCB
  apply le_min
  · have heq : (η * B_cap) ^ 2 / (4 * (ε * B_cap)) = η ^ 2 / (4 * ε) * B_cap := by field_simp
    rw [heq]
    have hden : 4 * ε ≤ 32 * (r : ℝ) ^ 3 * ε := by nlinarith only [hr3, hε0]
    have hrat : η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) ≤ η ^ 2 / (4 * ε) :=
      div_le_div_of_nonneg_left (sq_nonneg η) (by positivity) hden
    calc η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) * C_t
        ≤ η ^ 2 / (4 * ε) * C_t := mul_le_mul_of_nonneg_right hrat hC0.le
      _ ≤ η ^ 2 / (4 * ε) * B_cap := mul_le_mul_of_nonneg_left hCB (by positivity)
  · have hrat : η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) ≤ η / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 2 * η ≤ 32 * (r : ℝ) ^ 3 * ε := by nlinarith only [hηε, hr3, hε0]
      nlinarith only [h1, hη0]
    calc η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) * C_t
        ≤ (η / 2) * C_t := mul_le_mul_of_nonneg_right hrat hC0.le
      _ ≤ (η / 2) * B_cap := mul_le_mul_of_nonneg_left hCB (by positivity)
      _ = η * B_cap / (2 * 1) := by ring

lemma card_subTrials_le {n m C_int L_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (hL_card : ∀ E ∈ K, (L E).card = L_int)
    (F : Finset ↥K) (c_excl : Option (Fin m)) :
    (subTrials K L (C_int := C_int) F c_excl).card ≤ F.card * L_int := by
  calc (subTrials K L (C_int := C_int) F c_excl).card
      ≤ ∑ A ∈ F, ((listSub L c_excl A).image (fun c' => (Sum.inl (A, c') : LCoord K m C_int))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ A ∈ F, (listSub L c_excl A).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ ≤ ∑ _A ∈ F, L_int := Finset.sum_le_sum fun A _ => by
        cases c_excl with
        | none => exact (hL_card A.1 A.2).le
        | some c => exact (Finset.card_erase_le.trans (hL_card A.1 A.2).le)
    _ = F.card * L_int := by simp

lemma card_subTrials_eq_sum_col {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m)) :
    (subTrials K L (C_int := C_int) F c_excl).card =
      ∑ c' : Fin m, (F.filter (fun A => c' ∈ listSub L c_excl A)).card := by
  have heq : subTrials K L (C_int := C_int) F c_excl =
      (Finset.univ : Finset (Fin m)).biUnion
        (fun c' => (F.filter (fun A => c' ∈ listSub L c_excl A)).image (fun A => Sum.inl (A, c'))) := by
    ext e
    simp only [subTrials, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter]
    constructor
    · rintro ⟨A, hAF, c', hc', rfl⟩
      exact ⟨c', A, ⟨hAF, hc'⟩, rfl⟩
    · rintro ⟨c', A, ⟨hAF, hc'⟩, rfl⟩
      exact ⟨A, hAF, c', hc', rfl⟩
  rw [heq, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun c' _ => Finset.card_image_of_injective _ ?_
    intro A₁ A₂ h; exact congrArg Prod.fst (Sum.inl.inj h)
  · intro c₁ _ c₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro e h₁ h₂
    rcases Finset.mem_image.mp h₁ with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp h₂ with ⟨_, _, hEq⟩
    exact hne (congrArg Prod.snd (Sum.inl.inj hEq.symm))

/-- McDiarmid concentration for `rowHit`, `selTrials`, and `colHit` on `subTrials`. -/
lemma subset_mcdiarmid_bounds {n m C_int r Q L_int : ℕ}
    (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hr : 4 ≤ r) (hQ : 0 < Q)
    (hL_card : ∀ E ∈ K, (L E).card = L_int)
    (hdeg : ∀ x c, (K.filter (fun B => x ∈ B ∧ c ∈ L B)).card ≤ C_int)
    (ε η L_t C_t B_cap : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hη0 : 0 < η) (hηε : η ≤ ε)
    (hC0 : 0 < C_t) (hCL : C_t ≤ L_t) (hCB : C_t ≤ B_cap)
    (hC_int_le : (C_int : ℝ) ≤ C_t)
    (hL_int_lo : L_t - 1 ≤ (L_int : ℝ)) (hL_int_hi : (L_int : ℝ) ≤ L_t)
    (hQp_lo : (ε / L_t) * (1 - ε / L_t) ≤ 1 / (Q : ℝ))
    (hQp_hi : 1 / (Q : ℝ) ≤ ε / L_t) (hQ2 : 1 / (Q : ℝ) ≤ 1 / 2)
    (hL_big : 8 / η ≤ L_t)
    (x : Fin n) (F : Finset ↥K) (hFx : ∀ A ∈ F, x ∈ A.1) (hFB : (F.card : ℝ) ≤ B_cap)
    (c_excl : Option (Fin m)) :
    let μS : ℝ := ((subTrials K L (C_int := C_int) F c_excl).card : ℝ) / (Q : ℝ)
    ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      ((rowHit K L F c_excl ω).card : ℝ) <
        (F.card : ℝ) * ε - (ε ^ 2 + 3 / 2 * η) * B_cap)).card : ℝ) ≤
        2 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) ∧
    ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      μS + η * B_cap < ((selTrials K L F c_excl ω).card : ℝ))).card : ℝ) ≤
        2 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) ∧
    ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      ((colHit K L F c_excl ω).card : ℝ) < μS - (ε ^ 2 + η) * B_cap)).card : ℝ) ≤
        2 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
  intro μS
  have hL0 : 0 < L_t := lt_of_lt_of_le hC0 hCL
  have hB0 : 0 < B_cap := lt_of_lt_of_le hC0 hCB
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hp0 : 0 ≤ 1 / (Q : ℝ) := by positivity
  have hp1 : 1 / (Q : ℝ) ≤ 1 := by linarith [hQ2]
  let S := subTrials K L (C_int := C_int) F c_excl
  have hS_card : (S.card : ℝ) ≤ B_cap * L_t := by
    have h1 : (S.card : ℝ) ≤ (F.card : ℝ) * (L_int : ℝ) := by
      exact_mod_cast card_subTrials_le K L hL_card F c_excl
    exact h1.trans (mul_le_mul hFB hL_int_hi (Nat.cast_nonneg _) hB0.le)
  have hV_ge : (∑ _e ∈ S, (1 : ℝ) ^ 2) / (Q : ℝ) ≤ ε * B_cap := by
    simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    calc (S.card : ℝ) / (Q : ℝ) = (S.card : ℝ) * (1 / (Q : ℝ)) := by ring
      _ ≤ (B_cap * L_t) * (ε / L_t) := mul_le_mul hS_card hQp_hi hp0 (by positivity)
      _ = ε * B_cap := by field_simp
  have hexp_le := sub_mcdiarmid_exp_le hr hε0 hη0 hηε hC0 hCB
  have hμS_le : μS ≤ ε * B_cap := by
    calc μS = (S.card : ℝ) * (1 / (Q : ℝ)) := by simp only [μS, S]; ring
      _ ≤ (B_cap * L_t) * (ε / L_t) := mul_le_mul hS_card hQp_hi hp0 (by positivity)
      _ = ε * B_cap := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: `rowHit`
    let fU : (LCoord K m C_int → Fin Q) → ℝ := fun ω => ((rowHit K L F c_excl ω).card : ℝ)
    have hdepU : ∀ ω₁ ω₂, (∀ e ∈ S, ω₁ e = ω₂ e) → fU ω₁ = fU ω₂ := by
      intro ω₁ ω₂ hEq
      simp only [fU, rowHit]; congr 2
      refine Finset.filter_congr fun A hAF => exists_congr fun c' => and_congr_right fun hc' => ?_
      rw [hEq (Sum.inl (A, c')) (Finset.mem_biUnion.mpr ⟨A, hAF, Finset.mem_image.mpr ⟨c', hc', rfl⟩⟩)]
    have hconstU : ∀ e ∈ S, ∀ ω (a b : Fin Q), a.val ≠ 0 → b.val ≠ 0 →
        fU (Function.update ω e a) = fU (Function.update ω e b) := by
      intro e _ ω a b ha hb
      simp only [fU, rowHit]; congr 2
      refine Finset.filter_congr fun A _ => exists_congr fun c' => and_congr_right fun _ => ?_
      by_cases h : (Sum.inl (A, c') : LCoord K m C_int) = e
      · rw [h]; simp [ha, hb]
      · simp [Function.update_of_ne h]
    have hlipU : ∀ e ∈ S, ∀ ω (a : Fin Q), a.val ≠ 0 →
        |fU (Function.update ω e ⟨0, hQ⟩) - fU (Function.update ω e a)| ≤ 1 := by
      intro e he ω a ha
      simp only [S, subTrials, Finset.mem_biUnion, Finset.mem_image] at he
      rcases he with ⟨A₀, _, c₀, _, rfl⟩
      have hsub₁ : rowHit K L F c_excl (Function.update ω (Sum.inl (A₀, c₀)) a) ⊆
          rowHit K L F c_excl (Function.update ω (Sum.inl (A₀, c₀)) ⟨0, hQ⟩) := by
        intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hAF, c', hc', h0⟩
        refine Finset.mem_filter.mpr ⟨hAF, c', hc', ?_⟩
        by_cases h : (Sum.inl (A, c') : LCoord K m C_int) = Sum.inl (A₀, c₀)
        · rw [h] at h0; simp only [Function.update_self] at h0; exact absurd h0 ha
        · simpa [Function.update_of_ne h] using h0
      have hsub₂ : rowHit K L F c_excl (Function.update ω (Sum.inl (A₀, c₀)) ⟨0, hQ⟩) ⊆
          rowHit K L F c_excl (Function.update ω (Sum.inl (A₀, c₀)) a) ∪ {A₀} := by
        intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hAF, c', hc', h0⟩
        by_cases hA0 : A = A₀
        · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hA0)
        · apply Finset.mem_union_left
          refine Finset.mem_filter.mpr ⟨hAF, c', hc', ?_⟩
          have hne : (Sum.inl (A, c') : LCoord K m C_int) ≠ Sum.inl (A₀, c₀) :=
            fun h => hA0 (congrArg Prod.fst (Sum.inl.inj h))
          simpa [Function.update_of_ne hne] using h0
      have habs := abs_card_sub_le hsub₁ hsub₂
      rw [abs_sub_comm] at habs
      simpa [fU] using habs
    have hμU_eq : (∑ ω : LCoord K m C_int → Fin Q, fU ω) /
        (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) =
        ∑ A ∈ F, (1 - (1 - 1 / (Q : ℝ)) ^ (listSub L c_excl A).card) := by
      have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
      have hTot_pos : (0 : ℝ) < (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) :=
        Nat.cast_pos.mpr Fintype.card_pos
      have hcomp : ∀ ω : LCoord K m C_int → Fin Q,
          fU ω = (F.card : ℝ) -
            ((F.filter (fun A => ∀ e ∈ (listSub L c_excl A).image
              (fun c' => (Sum.inl (A, c') : LCoord K m C_int)), (ω e).val ≠ 0)).card : ℝ) := by
        intro ω
        have h1 : (rowHit K L F c_excl ω).card +
            (F.filter (fun A => ¬ ∃ c' ∈ listSub L c_excl A, (ω (Sum.inl (A, c'))).val = 0)).card =
            F.card := Finset.card_filter_add_card_filter_not _
        have h2 : F.filter (fun A => ∀ e ∈ (listSub L c_excl A).image
              (fun c' => (Sum.inl (A, c') : LCoord K m C_int)), (ω e).val ≠ 0) =
            F.filter (fun A => ¬ ∃ c' ∈ listSub L c_excl A, (ω (Sum.inl (A, c'))).val = 0) := by
          ext A
          simp only [Finset.mem_filter, Finset.mem_image, not_exists, not_and]
          refine and_congr_right fun _ => ?_
          constructor
          · intro h c' hc' h0; exact h _ ⟨c', hc', rfl⟩ h0
          · rintro h e ⟨c', hc', rfl⟩ h0; exact h c' hc' h0
        rw [h2]
        have h1' : (fU ω) + ((F.filter (fun A =>
            ¬ ∃ c' ∈ listSub L c_excl A, (ω (Sum.inl (A, c'))).val = 0)).card : ℝ) =
            (F.card : ℝ) := by dsimp only [fU]; exact_mod_cast h1
        linarith
      simp_rw [hcomp]
      rw [Finset.sum_sub_distrib, sub_div]
      have havgU := avg_sum_disjoint_filter (X := LCoord K m C_int) Q hQ F
        (fun A => (listSub L c_excl A).image (fun c' => (Sum.inl (A, c') : LCoord K m C_int)))
      have havgU' : (∑ ω : LCoord K m C_int → Fin Q,
          ((F.filter (fun A => ∀ e ∈ (listSub L c_excl A).image
            (fun c' => (Sum.inl (A, c') : LCoord K m C_int)), (ω e).val ≠ 0)).card : ℝ)) /
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) =
          ∑ A ∈ F, (1 - 1 / (Q : ℝ)) ^
            ((listSub L c_excl A).image (fun c' => (Sum.inl (A, c') : LCoord K m C_int))).card := by
        refine (congrArg (· / (Fintype.card (LCoord K m C_int → Fin Q) : ℝ))
          (Finset.sum_congr rfl fun ω _ => ?_)).trans havgU
        exact congrArg (fun s : Finset ↥K => (s.card : ℝ)) (by ext A; simp only [Finset.mem_filter])
      rw [havgU']
      have hc1 : (∑ _ω : LCoord K m C_int → Fin Q, (F.card : ℝ)) /
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) = (F.card : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hTot_pos.ne']
      rw [hc1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun A _ => ?_
      rw [Finset.card_image_of_injective _ (fun (c₁ c₂ : Fin m)
        (h : (Sum.inl (A, c₁) : LCoord K m C_int) = Sum.inl (A, c₂)) =>
        congrArg Prod.snd (Sum.inl.inj h))]
    have hμU_lo : (F.card : ℝ) * ε - (ε ^ 2 + 1 / 2 * η) * B_cap ≤
        ∑ A ∈ F, (1 - (1 - 1 / (Q : ℝ)) ^ (listSub L c_excl A).card) := by
      have hterm : ∀ A ∈ F, ε - ε ^ 2 - 1 / 2 * η ≤
          1 - (1 - 1 / (Q : ℝ)) ^ (listSub L c_excl A).card := by
        intro A _
        have hpb := (one_sub_pow_bounds hp0 hp1 (listSub L c_excl A).card).1
        have hle_L : ((listSub L c_excl A).card : ℝ) ≤ L_t := by
          have h1 : (listSub L c_excl A).card ≤ L_int := by
            cases c_excl with
            | none => exact (hL_card A.1 A.2).le
            | some c => exact Finset.card_erase_le.trans (hL_card A.1 A.2).le
          exact (Nat.cast_le.mpr h1).trans hL_int_hi
        have hge_L : L_t - 2 ≤ ((listSub L c_excl A).card : ℝ) := by
          have hL_ge2 : (2 : ℝ) ≤ L_t := by
            have h1 : 8 ≤ η * L_t := by
              have := mul_le_mul_of_nonneg_left hL_big hη0.le
              have hc : η * (8 / η) = 8 := by field_simp
              linarith
            nlinarith only [h1, hηε, hε1, hL0, hη0]
          have h1 : L_int - 1 ≤ (listSub L c_excl A).card := by
            cases c_excl with
            | none => dsimp only [listSub]; rw [hL_card A.1 A.2]; omega
            | some c =>
              dsimp only [listSub]
              have := Finset.pred_card_le_card_erase (s := L A.1) (a := c)
              rw [hL_card A.1 A.2] at this; exact this
          have hL_int_pos : 1 ≤ L_int := by
            have : (1 : ℝ) ≤ (L_int : ℝ) := by linarith
            exact_mod_cast this
          have h1' : (L_int : ℝ) - 1 ≤ ((listSub L c_excl A).card : ℝ) := by
            have hsub : ((L_int - 1 : ℕ) : ℝ) = (L_int : ℝ) - 1 := by
              rw [Nat.cast_sub hL_int_pos, Nat.cast_one]
            linarith [Nat.cast_le (α := ℝ).mpr h1, hsub]
          linarith [h1', hL_int_lo]
        have hmp_hi : ((listSub L c_excl A).card : ℝ) * (1 / (Q : ℝ)) ≤ ε := by
          calc ((listSub L c_excl A).card : ℝ) * (1 / (Q : ℝ))
              ≤ L_t * (ε / L_t) := mul_le_mul hle_L hQp_hi hp0 hL0.le
            _ = ε := by field_simp
        have hmp_sq : (((listSub L c_excl A).card : ℝ) * (1 / (Q : ℝ))) ^ 2 ≤ ε ^ 2 :=
          pow_le_pow_left₀ (by positivity) hmp_hi 2
        have hmp_lo : ε - 1 / 2 * η ≤ ((listSub L c_excl A).card : ℝ) * (1 / (Q : ℝ)) := by
          have hL_eta : 8 ≤ η * L_t := by
            have := mul_le_mul_of_nonneg_left hL_big hη0.le
            have hc : η * (8 / η) = 8 := by field_simp
            linarith
          have hL2_nn : 0 ≤ L_t - 2 := by nlinarith only [hL_eta, hηε, hε1, hL0, hη0]
          have h1 : (L_t - 2) * ((ε / L_t) * (1 - ε / L_t)) ≤
              ((listSub L c_excl A).card : ℝ) * (1 / (Q : ℝ)) := by
            have hnn : 0 ≤ (ε / L_t) * (1 - ε / L_t) := by
              have : ε / L_t ≤ 1 := (div_le_one hL0).mpr (by nlinarith only [hL_eta, hηε, hε1, hL0, hη0])
              exact mul_nonneg (by positivity) (by linarith)
            exact mul_le_mul hge_L hQp_lo hnn (Nat.cast_nonneg _)
          have h2 : (L_t - 2) * ((ε / L_t) * (1 - ε / L_t)) =
              ε - (2 * ε + ε ^ 2) / L_t + 2 * ε ^ 2 / L_t ^ 2 := by field_simp; ring
          have h3 : (2 * ε + ε ^ 2) / L_t ≤ 1 / 2 * η := by
            rw [div_le_iff₀ hL0]
            have hnum : 2 * ε + ε ^ 2 ≤ 4 := by nlinarith only [hε0, hε1]
            nlinarith only [hnum, hL_eta]
          have h4 : 0 ≤ 2 * ε ^ 2 / L_t ^ 2 := by positivity
          linarith [h1, h2, h3, h4]
        linarith [hpb, hmp_sq, hmp_lo]
      have hsum : (F.card : ℝ) * (ε - ε ^ 2 - 1 / 2 * η) ≤
          ∑ A ∈ F, (1 - (1 - 1 / (Q : ℝ)) ^ (listSub L c_excl A).card) := by
        calc (F.card : ℝ) * (ε - ε ^ 2 - 1 / 2 * η)
            = ∑ _A ∈ F, (ε - ε ^ 2 - 1 / 2 * η) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ A ∈ F, (1 - (1 - 1 / (Q : ℝ)) ^ (listSub L c_excl A).card) :=
              Finset.sum_le_sum hterm
      have herr : (F.card : ℝ) * (ε ^ 2 + 1 / 2 * η) ≤ B_cap * (ε ^ 2 + 1 / 2 * η) :=
        mul_le_mul_of_nonneg_right hFB (by positivity)
      linarith [hsum, herr]
    have hmc := bernoulli_mcdiarmid_sub Q hQ S (fun _ => 1) fU 1 (ε * B_cap) (η * B_cap)
      one_pos (by positivity) (by positivity)
      (fun _ _ => zero_le_one) (fun _ _ => le_rfl) hV_ge hdepU hconstU hlipU
    have hsub : Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
        fU ω < (F.card : ℝ) * ε - (ε ^ 2 + 3 / 2 * η) * B_cap) ⊆
        Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
          η * B_cap ≤ |fU ω - (∑ ω' : LCoord K m C_int → Fin Q, fU ω') /
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ)|) := by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      rw [hμU_eq]
      have h1 : η * B_cap ≤ (∑ A ∈ F, (1 - (1 - 1 / (Q : ℝ)) ^ (listSub L c_excl A).card)) - fU ω := by
        linarith [hω, hμU_lo]
      exact h1.trans (by rw [← neg_sub]; exact neg_le_abs _)
    calc ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
            fU ω < (F.card : ℝ) * ε - (ε ^ 2 + 3 / 2 * η) * B_cap)).card : ℝ)
        ≤ ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
            η * B_cap ≤ |fU ω - (∑ ω' : LCoord K m C_int → Fin Q, fU ω') /
              (Fintype.card (LCoord K m C_int → Fin Q) : ℝ)|)).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ 2 * Real.exp (-min ((η * B_cap) ^ 2 / (4 * (ε * B_cap))) (η * B_cap / (2 * 1))) *
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := hmc
      _ ≤ 2 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (Nat.cast_nonneg _)
          rw [Real.exp_le_exp]; linarith [hexp_le]
  · -- Part 2: `selTrials`
    let fS : (LCoord K m C_int → Fin Q) → ℝ := fun ω => ((selTrials K L F c_excl ω).card : ℝ)
    have hdepS : ∀ ω₁ ω₂, (∀ e ∈ S, ω₁ e = ω₂ e) → fS ω₁ = fS ω₂ := by
      intro ω₁ ω₂ hEq
      simp only [fS, selTrials]; congr 2
      exact Finset.filter_congr fun e he => by rw [hEq e he]
    have hconstS : ∀ e ∈ S, ∀ ω (a b : Fin Q), a.val ≠ 0 → b.val ≠ 0 →
        fS (Function.update ω e a) = fS (Function.update ω e b) := by
      intro e _ ω a b ha hb
      simp only [fS, selTrials]; congr 2
      refine Finset.filter_congr fun e' _ => ?_
      by_cases h : e' = e
      · subst h; simp [ha, hb]
      · simp [Function.update_of_ne h]
    have hlipS : ∀ e ∈ S, ∀ ω (a : Fin Q), a.val ≠ 0 →
        |fS (Function.update ω e ⟨0, hQ⟩) - fS (Function.update ω e a)| ≤ 1 := by
      intro e _ ω a ha
      have hsub₁ : selTrials K L F c_excl (Function.update ω e a) ⊆
          selTrials K L F c_excl (Function.update ω e ⟨0, hQ⟩) := by
        intro e' he'
        rcases Finset.mem_filter.mp he' with ⟨he'S, h0⟩
        refine Finset.mem_filter.mpr ⟨he'S, ?_⟩
        by_cases h : e' = e
        · subst h; simp only [Function.update_self] at h0; exact absurd h0 ha
        · simpa [Function.update_of_ne h] using h0
      have hsub₂ : selTrials K L F c_excl (Function.update ω e ⟨0, hQ⟩) ⊆
          selTrials K L F c_excl (Function.update ω e a) ∪ {e} := by
        intro e' he'
        rcases Finset.mem_filter.mp he' with ⟨he'S, h0⟩
        by_cases h : e' = e
        · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨he'S, by simpa [Function.update_of_ne h] using h0⟩)
      have habs := abs_card_sub_le hsub₁ hsub₂
      rw [abs_sub_comm] at habs
      simpa [fS] using habs
    have hμS_eq : (∑ ω : LCoord K m C_int → Fin Q, fS ω) /
        (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) = μS :=
      avg_sum_card_filter_zero Q hQ S
    have hmc := bernoulli_mcdiarmid_sub Q hQ S (fun _ => 1) fS 1 (ε * B_cap) (η * B_cap)
      one_pos (by positivity) (by positivity)
      (fun _ _ => zero_le_one) (fun _ _ => le_rfl) hV_ge hdepS hconstS hlipS
    have hsub : Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
        μS + η * B_cap < fS ω) ⊆
        Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
          η * B_cap ≤ |fS ω - (∑ ω' : LCoord K m C_int → Fin Q, fS ω') /
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ)|) := by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      rw [hμS_eq]
      have h1 : η * B_cap ≤ fS ω - μS := by linarith [hω]
      exact h1.trans (le_abs_self _)
    calc ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
            μS + η * B_cap < fS ω)).card : ℝ)
        ≤ ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
            η * B_cap ≤ |fS ω - (∑ ω' : LCoord K m C_int → Fin Q, fS ω') /
              (Fintype.card (LCoord K m C_int → Fin Q) : ℝ)|)).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ 2 * Real.exp (-min ((η * B_cap) ^ 2 / (4 * (ε * B_cap))) (η * B_cap / (2 * 1))) *
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := hmc
      _ ≤ 2 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (Nat.cast_nonneg _)
          rw [Real.exp_le_exp]; linarith [hexp_le]
  · -- Part 3: `colHit`
    let fC : (LCoord K m C_int → Fin Q) → ℝ := fun ω => ((colHit K L F c_excl ω).card : ℝ)
    have hdepC : ∀ ω₁ ω₂, (∀ e ∈ S, ω₁ e = ω₂ e) → fC ω₁ = fC ω₂ := by
      intro ω₁ ω₂ hEq
      simp only [fC, colHit]; congr 2
      refine Finset.filter_congr fun c' _ => exists_congr fun A =>
        and_congr_right fun hAF => and_congr_right fun hc' => ?_
      rw [hEq (Sum.inl (A, c')) (Finset.mem_biUnion.mpr ⟨A, hAF, Finset.mem_image.mpr ⟨c', hc', rfl⟩⟩)]
    have hconstC : ∀ e ∈ S, ∀ ω (a b : Fin Q), a.val ≠ 0 → b.val ≠ 0 →
        fC (Function.update ω e a) = fC (Function.update ω e b) := by
      intro e _ ω a b ha hb
      simp only [fC, colHit]; congr 2
      refine Finset.filter_congr fun c' _ => exists_congr fun A =>
        and_congr_right fun _ => and_congr_right fun _ => ?_
      by_cases h : (Sum.inl (A, c') : LCoord K m C_int) = e
      · rw [h]; simp [ha, hb]
      · simp [Function.update_of_ne h]
    have hlipC : ∀ e ∈ S, ∀ ω (a : Fin Q), a.val ≠ 0 →
        |fC (Function.update ω e ⟨0, hQ⟩) - fC (Function.update ω e a)| ≤ 1 := by
      intro e he ω a ha
      simp only [S, subTrials, Finset.mem_biUnion, Finset.mem_image] at he
      rcases he with ⟨A₀, _, c₀, _, rfl⟩
      have hsub₁ : colHit K L F c_excl (Function.update ω (Sum.inl (A₀, c₀)) a) ⊆
          colHit K L F c_excl (Function.update ω (Sum.inl (A₀, c₀)) ⟨0, hQ⟩) := by
        intro c' hc'
        rcases Finset.mem_filter.mp hc' with ⟨_, A, hAF, hc'L, h0⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, A, hAF, hc'L, ?_⟩
        by_cases h : (Sum.inl (A, c') : LCoord K m C_int) = Sum.inl (A₀, c₀)
        · rw [h] at h0; simp only [Function.update_self] at h0; exact absurd h0 ha
        · simpa [Function.update_of_ne h] using h0
      have hsub₂ : colHit K L F c_excl (Function.update ω (Sum.inl (A₀, c₀)) ⟨0, hQ⟩) ⊆
          colHit K L F c_excl (Function.update ω (Sum.inl (A₀, c₀)) a) ∪ {c₀} := by
        intro c' hc'
        rcases Finset.mem_filter.mp hc' with ⟨_, A, hAF, hc'L, h0⟩
        by_cases hc0 : c' = c₀
        · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hc0)
        · apply Finset.mem_union_left
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, A, hAF, hc'L, ?_⟩
          have hne : (Sum.inl (A, c') : LCoord K m C_int) ≠ Sum.inl (A₀, c₀) :=
            fun h => hc0 (congrArg Prod.snd (Sum.inl.inj h))
          simpa [Function.update_of_ne hne] using h0
      have habs := abs_card_sub_le hsub₁ hsub₂
      rw [abs_sub_comm] at habs
      simpa [fC] using habs
    let dF : Fin m → ℕ := fun c' => (F.filter (fun A => c' ∈ listSub L c_excl A)).card
    have hμC_eq : (∑ ω : LCoord K m C_int → Fin Q, fC ω) /
        (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) =
        ∑ c' : Fin m, (1 - (1 - 1 / (Q : ℝ)) ^ dF c') := by
      have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
      have hTot_pos : (0 : ℝ) < (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) :=
        Nat.cast_pos.mpr Fintype.card_pos
      have hcomp : ∀ ω : LCoord K m C_int → Fin Q,
          fC ω = ((Finset.univ : Finset (Fin m)).card : ℝ) -
            (((Finset.univ : Finset (Fin m)).filter (fun c' =>
              ∀ e ∈ (F.filter (fun A => c' ∈ listSub L c_excl A)).image
                (fun A => (Sum.inl (A, c') : LCoord K m C_int)), (ω e).val ≠ 0)).card : ℝ) := by
        intro ω
        have h1 : (colHit K L F c_excl ω).card +
            ((Finset.univ : Finset (Fin m)).filter (fun c' =>
              ¬ ∃ A ∈ F, c' ∈ listSub L c_excl A ∧ (ω (Sum.inl (A, c'))).val = 0)).card =
            (Finset.univ : Finset (Fin m)).card := Finset.card_filter_add_card_filter_not _
        have h2 : (Finset.univ : Finset (Fin m)).filter (fun c' =>
              ∀ e ∈ (F.filter (fun A => c' ∈ listSub L c_excl A)).image
                (fun A => (Sum.inl (A, c') : LCoord K m C_int)), (ω e).val ≠ 0) =
            (Finset.univ : Finset (Fin m)).filter (fun c' =>
              ¬ ∃ A ∈ F, c' ∈ listSub L c_excl A ∧ (ω (Sum.inl (A, c'))).val = 0) := by
          ext c'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_exists,
            not_and]
          constructor
          · intro h A hAF hc'L h0
            exact h _ ⟨A, ⟨hAF, hc'L⟩, rfl⟩ h0
          · rintro h e ⟨A, ⟨hAF, hc'L⟩, rfl⟩ h0
            exact h A hAF hc'L h0
        rw [h2]
        have h1' : (fC ω) + (((Finset.univ : Finset (Fin m)).filter (fun c' =>
            ¬ ∃ A ∈ F, c' ∈ listSub L c_excl A ∧ (ω (Sum.inl (A, c'))).val = 0)).card : ℝ) =
            ((Finset.univ : Finset (Fin m)).card : ℝ) := by dsimp only [fC]; exact_mod_cast h1
        linarith
      simp_rw [hcomp]
      rw [Finset.sum_sub_distrib, sub_div]
      have havgC := avg_sum_disjoint_filter (X := LCoord K m C_int) Q hQ (Finset.univ : Finset (Fin m))
        (fun c' => (F.filter (fun A => c' ∈ listSub L c_excl A)).image
          (fun A => (Sum.inl (A, c') : LCoord K m C_int)))
      have havgC' : (∑ ω : LCoord K m C_int → Fin Q,
          (((Finset.univ : Finset (Fin m)).filter (fun c' =>
            ∀ e ∈ (F.filter (fun A => c' ∈ listSub L c_excl A)).image
              (fun A => (Sum.inl (A, c') : LCoord K m C_int)), (ω e).val ≠ 0)).card : ℝ)) /
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) =
          ∑ c' : Fin m, (1 - 1 / (Q : ℝ)) ^
            ((F.filter (fun A => c' ∈ listSub L c_excl A)).image
              (fun A => (Sum.inl (A, c') : LCoord K m C_int))).card := by
        refine (congrArg (· / (Fintype.card (LCoord K m C_int → Fin Q) : ℝ))
          (Finset.sum_congr rfl fun ω _ => ?_)).trans havgC
        exact congrArg (fun s : Finset (Fin m) => (s.card : ℝ))
          (by ext c'; simp only [Finset.mem_filter])
      rw [havgC']
      have hc1 : (∑ _ω : LCoord K m C_int → Fin Q, ((Finset.univ : Finset (Fin m)).card : ℝ)) /
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) = ((Finset.univ : Finset (Fin m)).card : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hTot_pos.ne']
      rw [hc1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [Finset.card_image_of_injective _ (fun (A₁ A₂ : ↥K)
        (h : (Sum.inl (A₁, c') : LCoord K m C_int) = Sum.inl (A₂, c')) =>
        congrArg Prod.fst (Sum.inl.inj h))]
    have hμC_lo : μS - ε ^ 2 * B_cap ≤ ∑ c' : Fin m, (1 - (1 - 1 / (Q : ℝ)) ^ dF c') := by
      have hdF_le : ∀ c' : Fin m, (dF c' : ℝ) ≤ C_t := fun c' => by
        have h1 : dF c' ≤ (incVC K L x c').card := by
          apply Finset.card_le_card
          intro A hA
          rcases Finset.mem_filter.mp hA with ⟨hAF, hc'L⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFx A hAF, ?_⟩
          cases c_excl with
          | none => exact hc'L
          | some c => exact Finset.mem_of_mem_erase hc'L
        have h2 : dF c' ≤ C_int := h1.trans ((card_incVC K L x c').le.trans (hdeg x c'))
        exact (Nat.cast_le.mpr h2).trans hC_int_le
      have hsum_dF : (∑ c' : Fin m, (dF c' : ℝ)) / (Q : ℝ) = μS := by
        have h1 : (S.card : ℝ) = ∑ c' : Fin m, (dF c' : ℝ) := by
          exact_mod_cast card_subTrials_eq_sum_col K L F c_excl
        simp only [μS, S, h1]
      have hterm : ∀ c' : Fin m,
          (dF c' : ℝ) * (1 / (Q : ℝ)) - ε * ((dF c' : ℝ) * (1 / (Q : ℝ))) ≤
          1 - (1 - 1 / (Q : ℝ)) ^ dF c' := fun c' => by
        have hpb := (one_sub_pow_bounds hp0 hp1 (dF c')).1
        have hdp_le : (dF c' : ℝ) * (1 / (Q : ℝ)) ≤ ε := by
          calc (dF c' : ℝ) * (1 / (Q : ℝ)) ≤ C_t * (ε / L_t) :=
                mul_le_mul (hdF_le c') hQp_hi hp0 hC0.le
            _ = (C_t / L_t) * ε := by ring
            _ ≤ 1 * ε := mul_le_mul_of_nonneg_right ((div_le_one hL0).mpr hCL) hε0.le
            _ = ε := one_mul ε
        have hsq : ((dF c' : ℝ) * (1 / (Q : ℝ))) ^ 2 ≤ ε * ((dF c' : ℝ) * (1 / (Q : ℝ))) := by
          rw [sq]; exact mul_le_mul_of_nonneg_right hdp_le (by positivity)
        linarith [hpb, hsq]
      have hsum_lo : ∑ c' : Fin m, ((dF c' : ℝ) * (1 / (Q : ℝ)) -
          ε * ((dF c' : ℝ) * (1 / (Q : ℝ)))) ≤
          ∑ c' : Fin m, (1 - (1 - 1 / (Q : ℝ)) ^ dF c') :=
        Finset.sum_le_sum fun c' _ => hterm c'
      have hsum_eval : ∑ c' : Fin m, ((dF c' : ℝ) * (1 / (Q : ℝ)) -
          ε * ((dF c' : ℝ) * (1 / (Q : ℝ)))) = (1 - ε) * μS := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← div_eq_mul_one_div,
          hsum_dF]
        ring
      have hprod : ε * μS ≤ ε ^ 2 * B_cap := by
        calc ε * μS ≤ ε * (ε * B_cap) := mul_le_mul_of_nonneg_left hμS_le hε0.le
          _ = ε ^ 2 * B_cap := by ring
      linarith [hsum_lo, hsum_eval, hprod]
    have hmc := bernoulli_mcdiarmid_sub Q hQ S (fun _ => 1) fC 1 (ε * B_cap) (η * B_cap)
      one_pos (by positivity) (by positivity)
      (fun _ _ => zero_le_one) (fun _ _ => le_rfl) hV_ge hdepC hconstC hlipC
    have hsub : Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
        fC ω < μS - (ε ^ 2 + η) * B_cap) ⊆
        Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
          η * B_cap ≤ |fC ω - (∑ ω' : LCoord K m C_int → Fin Q, fC ω') /
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ)|) := by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      rw [hμC_eq]
      have h1 : η * B_cap ≤ (∑ c' : Fin m, (1 - (1 - 1 / (Q : ℝ)) ^ dF c')) - fC ω := by
        linarith [hω, hμC_lo]
      exact h1.trans (by rw [← neg_sub]; exact neg_le_abs _)
    calc ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
            fC ω < μS - (ε ^ 2 + η) * B_cap)).card : ℝ)
        ≤ ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
            η * B_cap ≤ |fC ω - (∑ ω' : LCoord K m C_int → Fin Q, fC ω') /
              (Fintype.card (LCoord K m C_int → Fin Q) : ℝ)|)).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ 2 * Real.exp (-min ((η * B_cap) ^ 2 / (4 * (ε * B_cap))) (η * B_cap / (2 * 1))) *
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := hmc
      _ ≤ 2 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (Nat.cast_nonneg _)
          rw [Real.exp_le_exp]; linarith [hexp_le]

/-- Conditional Chernoff upper tail for `hitClean` conditioned on `subTrials`. -/
lemma hitClean_bad_bound {n m C_int r Q : ℕ}
    (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hr : 4 ≤ r) (hQ : 0 < Q)
    (hunif : ∀ E ∈ K, E.card = r)
    (hlin : ∀ E ∈ K, ∀ F ∈ K, E ≠ F → (E ∩ F).card ≤ 1)
    (hdeg : ∀ x c, (K.filter (fun B => x ∈ B ∧ c ∈ L B)).card ≤ C_int)
    (ε η L_t C_t B_cap : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hη0 : 0 < η) (hηε2 : η ≤ ε ^ 2)
    (hC0 : 0 < C_t) (hCL : C_t ≤ L_t) (hCB : C_t ≤ B_cap)
    (hC_int_le : (C_int : ℝ) ≤ C_t) (hC_int_pos : 1 ≤ C_int)
    (hQp_hi : 1 / (Q : ℝ) ≤ ε / L_t)
    (F : Finset ↥K) (c_excl : Option (Fin m)) :
    ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      ((cleanPairs K L F c_excl ω).card : ℝ) ≤ 2 * ε * B_cap ∧
      4 * (r : ℝ) * ε ^ 2 * B_cap ≤ ((hitClean K L F c_excl ω).card : ℝ))).card : ℝ) ≤
      Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
        (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
  have hL0 : 0 < L_t := lt_of_lt_of_le hC0 hCL
  have hB0 : 0 < B_cap := lt_of_lt_of_le hC0 hCB
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  let S := subTrials K L (C_int := C_int) F c_excl
  let isClean : Finset (↥K × Fin m) → Prop := fun C₀ =>
    (∀ p ∈ C₀, p.1 ∈ F ∧ p.2 ∈ listSub L c_excl p.1) ∧
    (∀ p₁ ∈ C₀, ∀ p₂ ∈ C₀, p₁ ≠ p₂ → p₁.1 ≠ p₂.1 ∧ p₁.2 ≠ p₂.2)
  have hclean_ok : ∀ ω : LCoord K m C_int → Fin Q, isClean (cleanPairs K L F c_excl ω) := by
    intro ω
    constructor
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hprod, hLsub, _⟩
      exact ⟨(Finset.mem_product.mp hprod).1, hLsub⟩
    · intro p₁ hp₁ p₂ hp₂ hne
      rcases Finset.mem_filter.mp hp₁ with ⟨hpr₁, hL₁, h0₁, hrow₁, hcol₁⟩
      rcases Finset.mem_filter.mp hp₂ with ⟨hpr₂, hL₂, h0₂, _, _⟩
      have hF₂ : p₂.1 ∈ F := (Finset.mem_product.mp hpr₂).1
      constructor
      · intro hA
        have hc_ne : p₂.2 ≠ p₁.2 := fun hc => hne (Prod.ext hA hc.symm)
        have hL₂' : p₂.2 ∈ listSub L c_excl p₁.1 := hA ▸ hL₂
        have h0₂' : (ω (Sum.inl (p₁.1, p₂.2))).val = 0 := hA ▸ h0₂
        exact hrow₁ p₂.2 hL₂' hc_ne h0₂'
      · intro hc
        have hA_ne : p₂.1 ≠ p₁.1 := fun hA => hne (Prod.ext hA.symm hc)
        have hL₂' : p₁.2 ∈ listSub L c_excl p₂.1 := hc ▸ hL₂
        have h0₂' : (ω (Sum.inl (p₂.1, p₁.2))).val = 0 := hc ▸ h0₂
        exact hcol₁ p₂.1 hF₂ hA_ne hL₂' h0₂'
  let P : Finset (↥K × Fin m) → (LCoord K m C_int → Fin Q) → Prop := fun C₀ ω =>
    isClean C₀ ∧ (C₀.card : ℝ) ≤ 2 * ε * B_cap ∧
    4 * (r : ℝ) * ε ^ 2 * B_cap ≤
      ((C₀.filter (fun p => ∃ e ∈ hitCoords K L F c_excl p, (ω e).val = 0)).card : ℝ)
  have hsub_ev : Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      ((cleanPairs K L F c_excl ω).card : ℝ) ≤ 2 * ε * B_cap ∧
      4 * (r : ℝ) * ε ^ 2 * B_cap ≤ ((hitClean K L F c_excl ω).card : ℝ)) ⊆
      Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
        P (cleanPairs K L F c_excl ω) ω) := by
    intro ω hω
    rcases (Finset.mem_filter.mp hω).2 with ⟨h1, h2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclean_ok ω, h1, h2⟩
  refine (Nat.cast_le.mpr (Finset.card_le_card hsub_ev)).trans ?_
  refine (le_of_eq (congrArg (fun s : Finset _ => (s.card : ℝ))
    (by ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and]))).trans
    (card_filter_cond_split hQ S (cleanPairs K L F c_excl) ?_ P ?_
      (Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t)) ?_)
  · intro ω₁ ω₂ hEq
    refine Finset.filter_congr fun p hp => ?_
    have hF1 : p.1 ∈ F := (Finset.mem_product.mp hp).1
    refine and_congr_right fun hL1 => ?_
    have hmem1 : (Sum.inl p : LCoord K m C_int) ∈ S :=
      Finset.mem_biUnion.mpr ⟨p.1, hF1, Finset.mem_image.mpr ⟨p.2, hL1, rfl⟩⟩
    rw [hEq _ hmem1]
    refine and_congr_right fun _ => and_congr ?_ ?_
    · refine forall₂_congr fun c'' hc'' => imp_congr_right fun _ => ?_
      have hm : (Sum.inl (p.1, c'') : LCoord K m C_int) ∈ S :=
        Finset.mem_biUnion.mpr ⟨p.1, hF1, Finset.mem_image.mpr ⟨c'', hc'', rfl⟩⟩
      rw [hEq _ hm]
    · refine forall₂_congr fun B hBF => imp_congr_right fun _ => imp_congr_right fun hcB => ?_
      have hm : (Sum.inl (B, p.2) : LCoord K m C_int) ∈ S :=
        Finset.mem_biUnion.mpr ⟨B, hBF, Finset.mem_image.mpr ⟨p.2, hcB, rfl⟩⟩
      rw [hEq _ hm]
  · intro C₀ ω₁ ω₂ hEq
    have hdisj : ∀ p ∈ C₀, ∀ e ∈ hitCoords K L F c_excl p, e ∉ S := by
      intro p _ e he heS
      rcases Finset.mem_union.mp he with he1 | he2
      · rcases Finset.mem_image.mp he1 with ⟨c'', hc''s, rfl⟩
        simp only [S, subTrials, Finset.mem_biUnion, Finset.mem_image] at heS
        rcases heS with ⟨B, _, c₃, hc₃, hInj⟩
        have hBp : B = p.1 := congrArg Prod.fst (Sum.inl.inj hInj)
        have hcp : c₃ = c'' := congrArg Prod.snd (Sum.inl.inj hInj)
        subst hBp; subst hcp
        exact (Finset.mem_sdiff.mp hc''s).2 hc₃
      · exact (Finset.mem_sdiff.mp he2).2 heS
    have hfilt : C₀.filter (fun p => ∃ e ∈ hitCoords K L F c_excl p, (ω₁ e).val = 0) =
        C₀.filter (fun p => ∃ e ∈ hitCoords K L F c_excl p, (ω₂ e).val = 0) := by
      refine Finset.filter_congr fun p hp => exists_congr fun e => and_congr_right fun he => ?_
      rw [hEq e (hdisj p hp e he)]
    simp only [P, hfilt]
  · intro C₀
    by_cases hcond : isClean C₀ ∧ (C₀.card : ℝ) ≤ 2 * ε * B_cap
    · rcases hcond with ⟨hC_clean, hC_card⟩
      let Out : Finset (LCoord K m C_int) := C₀.biUnion (hitCoords K L F c_excl)
      have hpair_disj : ∀ p₁ ∈ C₀, ∀ p₂ ∈ C₀, p₁ ≠ p₂ →
          Disjoint (hitCoords K L (C_int := C_int) F c_excl p₁) (hitCoords K L F c_excl p₂) := by
        intro p₁ hp₁ p₂ hp₂ hne
        have hne12 := hC_clean.2 p₁ hp₁ p₂ hp₂ hne
        have hL₁ := (hC_clean.1 p₁ hp₁).2
        have hL₂ := (hC_clean.1 p₂ hp₂).2
        rw [Finset.disjoint_left]
        intro e he₁ he₂
        rcases Finset.mem_union.mp he₁ with ha₁ | hb₁
        · rcases Finset.mem_image.mp ha₁ with ⟨c₁, hc₁, rfl⟩
          rcases Finset.mem_union.mp he₂ with ha₂ | hb₂
          · rcases Finset.mem_image.mp ha₂ with ⟨c₂, _, hEq⟩
            exact hne12.1 (congrArg Prod.fst (Sum.inl.inj hEq)).symm
          · have hcol : c₁ = p₂.2 := coordColor_mem_edgeColorBlock (Finset.mem_sdiff.mp hb₂).1
            cases c_excl with
            | none => exact (Finset.mem_sdiff.mp hc₁).2 (Finset.mem_sdiff.mp hc₁).1
            | some c =>
              have hc₁_eq : c₁ = c := by
                have h1 := (Finset.mem_sdiff.mp hc₁).1
                have h2 := (Finset.mem_sdiff.mp hc₁).2
                simp only [listSub, Finset.mem_erase, not_and] at h2
                by_contra hnc; exact h2 hnc h1
              have hne_c : p₂.2 ≠ c := (Finset.mem_erase.mp hL₂).1
              exact hne_c (hcol.symm.trans hc₁_eq)
        · rcases Finset.mem_union.mp he₂ with ha₂ | hb₂
          · rcases Finset.mem_image.mp ha₂ with ⟨c₂, hc₂, rfl⟩
            have hcol : c₂ = p₁.2 := coordColor_mem_edgeColorBlock (Finset.mem_sdiff.mp hb₁).1
            cases c_excl with
            | none => exact (Finset.mem_sdiff.mp hc₂).2 (Finset.mem_sdiff.mp hc₂).1
            | some c =>
              have hc₂_eq : c₂ = c := by
                have h1 := (Finset.mem_sdiff.mp hc₂).1
                have h2 := (Finset.mem_sdiff.mp hc₂).2
                simp only [listSub, Finset.mem_erase, not_and] at h2
                by_contra hnc; exact h2 hnc h1
              have hne_c : p₁.2 ≠ c := (Finset.mem_erase.mp hL₁).1
              exact hne_c (hcol.symm.trans hc₂_eq)
          · have hcol₁ : coordColor e = p₁.2 :=
              coordColor_mem_edgeColorBlock (Finset.mem_sdiff.mp hb₁).1
            have hcol₂ : coordColor e = p₂.2 :=
              coordColor_mem_edgeColorBlock (Finset.mem_sdiff.mp hb₂).1
            exact hne12.2 (hcol₁.symm.trans hcol₂)
      have hcard_le : ∀ ω : LCoord K m C_int → Fin Q,
          ((C₀.filter (fun p => ∃ e ∈ hitCoords K L F c_excl p, (ω e).val = 0)).card : ℝ) ≤
            ∑ e ∈ Out, if (ω e).val = 0 then (1 : ℝ) else 0 := by
        intro ω
        have hnat : (C₀.filter (fun p => ∃ e ∈ hitCoords K L F c_excl p, (ω e).val = 0)).card ≤
            (Out.filter (fun e => (ω e).val = 0)).card := by
          let H := C₀.filter (fun p => ∃ e ∈ hitCoords K L F c_excl p, (ω e).val = 0)
          have hpick : ∀ p ∈ H, ∃ e ∈ Out.filter (fun e => (ω e).val = 0),
              e ∈ hitCoords K L F c_excl p := fun p hp => by
            rcases (Finset.mem_filter.mp hp).2 with ⟨e, he, h0⟩
            exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr
              ⟨p, (Finset.mem_filter.mp hp).1, he⟩, h0⟩, he⟩
          let g : ↥K × Fin m → LCoord K m C_int := fun p =>
            if h : p ∈ H then Classical.choose (hpick p h) else Sum.inl p
          have hcard_eq : H.card = (H.image g).card := by
            symm
            refine Finset.card_image_of_injOn fun p₁ hp₁ p₂ hp₂ hEq => ?_
            have hp₁' : p₁ ∈ H := Finset.mem_coe.mp hp₁
            have hp₂' : p₂ ∈ H := Finset.mem_coe.mp hp₂
            have h1 := Classical.choose_spec (hpick p₁ hp₁')
            have h2 := Classical.choose_spec (hpick p₂ hp₂')
            simp only [g, dif_pos hp₁', dif_pos hp₂'] at hEq
            by_contra hne
            have hdisj := hpair_disj p₁ (Finset.mem_filter.mp hp₁').1
              p₂ (Finset.mem_filter.mp hp₂').1 hne
            exact Finset.disjoint_left.mp hdisj h1.2 (hEq ▸ h2.2)
          rw [hcard_eq]
          apply Finset.card_le_card
          intro e he
          rcases Finset.mem_image.mp he with ⟨p, hp, rfl⟩
          simp only [g, dif_pos hp]
          exact (Classical.choose_spec (hpick p hp)).1
        have hreal : ((Out.filter (fun e => (ω e).val = 0)).card : ℝ) =
            ∑ e ∈ Out, if (ω e).val = 0 then (1 : ℝ) else 0 := by
          rw [Finset.card_filter]; simp
        rw [← hreal]; exact_mod_cast hnat
      have hOut_card : (Out.card : ℝ) ≤ (C₀.card : ℝ) * ((r : ℝ) * C_t) := by
        have h1 : Out.card ≤ ∑ p ∈ C₀, (hitCoords K L F c_excl p).card := Finset.card_biUnion_le
        have h2 : ∀ p ∈ C₀, (hitCoords K L F c_excl p).card ≤ r * C_int := fun p hp => by
          have hp2L : p.2 ∈ L p.1.1 := by
            have hLsub := (hC_clean.1 p hp).2
            cases c_excl with
            | none => exact hLsub
            | some c => exact Finset.mem_of_mem_erase hLsub
          have hpart1 : ((L p.1.1 \ listSub L c_excl p.1).image
              (fun c'' => (Sum.inl (p.1, c'') : LCoord K m C_int))).card ≤ 1 := by
            refine Finset.card_image_le.trans ?_
            cases c_excl with
            | none => simp [listSub]
            | some c =>
              have hsub : L p.1.1 \ (L p.1.1).erase c ⊆ {c} := by
                intro c'' hc''
                rcases Finset.mem_sdiff.mp hc'' with ⟨h1, h2⟩
                simp only [Finset.mem_erase, not_and] at h2
                exact Finset.mem_singleton.mpr (by by_contra hne; exact h2 hne h1)
              exact (Finset.card_le_card hsub).trans (by simp)
          have hpart2 : (edgeColorBlock K L (C_int := C_int) p.1 p.2 \ S).card ≤ r * (C_int - 1) := by
            exact (Finset.card_le_card Finset.sdiff_subset).trans
              (card_edgeColorBlock K L hunif hlin hdeg p.1 hp2L).le
          have hun := Finset.card_union_le
            ((L p.1.1 \ listSub L c_excl p.1).image (fun c'' => (Sum.inl (p.1, c'') : LCoord K m C_int)))
            (edgeColorBlock K L p.1 p.2 \ S)
          have hrc : 1 + r * (C_int - 1) ≤ r * C_int := by
            have h1' : r * (C_int - 1) + r = r * C_int := by
              rw [← Nat.mul_add_one, Nat.sub_add_cancel hC_int_pos]
            omega
          exact hun.trans ((Nat.add_le_add hpart1 hpart2).trans hrc)
        have h3 : Out.card ≤ C₀.card * (r * C_int) :=
          h1.trans ((Finset.sum_le_sum h2).trans (by simp))
        have h3' : (Out.card : ℝ) ≤ (C₀.card : ℝ) * ((r : ℝ) * (C_int : ℝ)) := by exact_mod_cast h3
        exact h3'.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hC_int_le (by positivity)) (Nat.cast_nonneg _))
      let μ₀ : ℝ := 2 * (r : ℝ) * ε ^ 2 * B_cap
      have hmean : (∑ _e ∈ Out, (1 : ℝ)) / (Q : ℝ) ≤ μ₀ := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        calc (Out.card : ℝ) / (Q : ℝ) = (Out.card : ℝ) * (1 / (Q : ℝ)) := by ring
          _ ≤ ((C₀.card : ℝ) * ((r : ℝ) * C_t)) * (ε / L_t) :=
              mul_le_mul hOut_card hQp_hi (by positivity) (by positivity)
          _ ≤ ((2 * ε * B_cap) * ((r : ℝ) * C_t)) * (ε / L_t) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC_card (by positivity))
                (by positivity)
          _ = (C_t / L_t) * μ₀ := by simp only [μ₀]; field_simp
          _ ≤ 1 * μ₀ := mul_le_mul_of_nonneg_right ((div_le_one hL0).mpr hCL) (by positivity)
          _ = μ₀ := one_mul μ₀
      have hch := weighted_chernoff_sub Q hQ Out (fun _ => 1) 1 μ₀ one_pos (by positivity)
        (fun _ _ => zero_le_one) (fun _ _ => le_rfl) hmean
      have hsub_ch : Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q => P C₀ ω) ⊆
          Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
            2 * μ₀ ≤ ∑ e ∈ Out, if (ω e).val = 0 then (1 : ℝ) else 0) := by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, P] at hω ⊢
        have h2μ : 2 * μ₀ = 4 * (r : ℝ) * ε ^ 2 * B_cap := by simp only [μ₀]; ring
        rw [h2μ]
        exact hω.2.2.trans (hcard_le ω)
      have hexp_cmp : η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) * C_t ≤ (1 / (3 * 1)) * μ₀ := by
        have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith only [hr4]
        have hr3 : (1 : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith only [hr4, hr2]
        have hη_sq : η ^ 2 ≤ ε ^ 4 := by
          have := mul_le_mul hηε2 hηε2 hη0.le (sq_nonneg ε)
          linarith [show ε ^ 2 * ε ^ 2 = ε ^ 4 by ring]
        have hrat : η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) ≤ 2 / 3 * (r : ℝ) * ε ^ 2 := by
          rw [div_le_iff₀ (by positivity)]
          have h1 : ε ^ 4 ≤ ε ^ 3 := by
            have h2 : ε ^ 3 * ε ≤ ε ^ 3 * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            linarith [show ε ^ 3 * ε = ε ^ 4 by ring]
          have h2 : 1 ≤ 2 / 3 * (r : ℝ) * (32 * (r : ℝ) ^ 3) := by nlinarith only [hr4, hr3]
          have h3 : ε ^ 3 ≤ (2 / 3 * (r : ℝ) * (32 * (r : ℝ) ^ 3)) * ε ^ 3 := by
            nlinarith only [h2, pow_pos hε0 3]
          linarith [hη_sq, h1, h3, show 2 / 3 * (r : ℝ) * ε ^ 2 * (32 * (r : ℝ) ^ 3 * ε) =
            2 / 3 * (r : ℝ) * (32 * (r : ℝ) ^ 3) * ε ^ 3 by ring]
        calc η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) * C_t
            ≤ (2 / 3 * (r : ℝ) * ε ^ 2) * C_t := mul_le_mul_of_nonneg_right hrat hC0.le
          _ ≤ (2 / 3 * (r : ℝ) * ε ^ 2) * B_cap := mul_le_mul_of_nonneg_left hCB (by positivity)
          _ = (1 / (3 * 1)) * μ₀ := by simp only [μ₀]; ring
      calc ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q => P C₀ ω)).card : ℝ)
          ≤ ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
              2 * μ₀ ≤ ∑ e ∈ Out, if (ω e).val = 0 then (1 : ℝ) else 0)).card : ℝ) :=
            Nat.cast_le.mpr (Finset.card_le_card hsub_ch)
        _ ≤ Real.exp (-(1 / (3 * 1)) * μ₀) * (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := hch
        _ ≤ Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
              (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
            rw [Real.exp_le_exp]; linarith [hexp_cmp]
    · have hemp : Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q => P C₀ ω) = ∅ := by
        ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, P]
        intro h; exact hcond ⟨h.1, h.2.1⟩
      rw [hemp, Finset.card_empty, Nat.cast_zero]
      positivity

/-- Unified probability bound for the number of uncolored edges in any `F ⊆ K(x)`. -/
lemma subset_colored_bad_bound {n m C_int r Q L_int : ℕ}
    (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hr : 4 ≤ r) (hQ : 0 < Q)
    (hunif : ∀ E ∈ K, E.card = r)
    (hlin : ∀ E ∈ K, ∀ F ∈ K, E ≠ F → (E ∩ F).card ≤ 1)
    (hL_card : ∀ E ∈ K, (L E).card = L_int)
    (hdeg : ∀ x c, (K.filter (fun B => x ∈ B ∧ c ∈ L B)).card ≤ C_int)
    (ε η L_t C_t B_cap : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hη0 : 0 < η) (hηε : η ≤ ε) (hηε2 : η ≤ ε ^ 2)
    (hC0 : 0 < C_t) (hCL : C_t ≤ L_t) (hCB : C_t ≤ B_cap)
    (hC_int_le : (C_int : ℝ) ≤ C_t) (hC_int_pos : 1 ≤ C_int)
    (hL_int_lo : L_t - 1 ≤ (L_int : ℝ)) (hL_int_hi : (L_int : ℝ) ≤ L_t)
    (hQp_lo : (ε / L_t) * (1 - ε / L_t) ≤ 1 / (Q : ℝ))
    (hQp_hi : 1 / (Q : ℝ) ≤ ε / L_t) (hQ2 : 1 / (Q : ℝ) ≤ 1 / 2)
    (hL_big : 8 / η ≤ L_t)
    (x : Fin n) (F : Finset ↥K) (hFx : ∀ A ∈ F, x ∈ A.1) (hFB : (F.card : ℝ) ≤ B_cap)
    (c_excl : Option (Fin m)) :
    ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      (F.card : ℝ) * (1 - ε) + (8 * (r : ℝ) * ε ^ 2 + 8 * η) * B_cap <
        ((uncoloredSub K L F c_excl ω).card : ℝ))).card : ℝ) ≤
      7 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
        (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hB0 : 0 < B_cap := lt_of_lt_of_le hC0 hCB
  have hL0 : 0 < L_t := lt_of_lt_of_le hC0 hCL
  let μS : ℝ := ((subTrials K L (C_int := C_int) F c_excl).card : ℝ) / (Q : ℝ)
  have hμS_le_F : μS ≤ (F.card : ℝ) * ε := by
    have h1 : ((subTrials K L (C_int := C_int) F c_excl).card : ℝ) ≤ (F.card : ℝ) * L_t := by
      have h0 : ((subTrials K L (C_int := C_int) F c_excl).card : ℝ) ≤ (F.card : ℝ) * (L_int : ℝ) := by
        exact_mod_cast card_subTrials_le K L hL_card F c_excl
      exact h0.trans (mul_le_mul_of_nonneg_left hL_int_hi (Nat.cast_nonneg _))
    calc μS = ((subTrials K L (C_int := C_int) F c_excl).card : ℝ) * (1 / (Q : ℝ)) := by
          simp only [μS]; ring
      _ ≤ ((F.card : ℝ) * L_t) * (ε / L_t) := mul_le_mul h1 hQp_hi (by positivity) (by positivity)
      _ = (F.card : ℝ) * ε := by field_simp
  have hμS_le_B : μS ≤ ε * B_cap := hμS_le_F.trans (by
    calc (F.card : ℝ) * ε ≤ B_cap * ε := mul_le_mul_of_nonneg_right hFB hε0.le
      _ = ε * B_cap := mul_comm _ _)
  let E1 := Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
    ((rowHit K L F c_excl ω).card : ℝ) < (F.card : ℝ) * ε - (ε ^ 2 + 3 / 2 * η) * B_cap)
  let E2 := Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
    μS + η * B_cap < ((selTrials K L F c_excl ω).card : ℝ))
  let E3 := Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
    ((colHit K L F c_excl ω).card : ℝ) < μS - (ε ^ 2 + η) * B_cap)
  let E4 := Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
    ((cleanPairs K L F c_excl ω).card : ℝ) ≤ 2 * ε * B_cap ∧
    4 * (r : ℝ) * ε ^ 2 * B_cap ≤ ((hitClean K L F c_excl ω).card : ℝ))
  have hcov : Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      (F.card : ℝ) * (1 - ε) + (8 * (r : ℝ) * ε ^ 2 + 8 * η) * B_cap <
        ((uncoloredSub K L F c_excl ω).card : ℝ)) ⊆ E1 ∪ E2 ∪ E3 ∪ E4 := by
    intro ω hω
    have hbad : (F.card : ℝ) * (1 - ε) + (8 * (r : ℝ) * ε ^ 2 + 8 * η) * B_cap <
        ((uncoloredSub K L F c_excl ω).card : ℝ) := (Finset.mem_filter.mp hω).2
    by_contra hnot
    simp only [Finset.mem_union, not_or, E1, E2, E3, E4, Finset.mem_filter, Finset.mem_univ,
      true_and, not_lt, not_and, not_le] at hnot
    rcases hnot with ⟨⟨⟨hU, hS⟩, hCol⟩, hHit⟩
    have hclean_le_S : (cleanPairs K L F c_excl ω).card ≤ (selTrials K L F c_excl ω).card := by
      have him : (cleanPairs K L F c_excl ω).image (fun p => (Sum.inl p : LCoord K m C_int)) ⊆
          selTrials K L F c_excl ω := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨p, hp, rfl⟩
        rcases Finset.mem_filter.mp hp with ⟨hprod, hLsub, h0, _⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr
          ⟨p.1, (Finset.mem_product.mp hprod).1, Finset.mem_image.mpr ⟨p.2, hLsub, rfl⟩⟩, h0⟩
      rw [← Finset.card_image_of_injective (cleanPairs K L F c_excl ω)
        (fun (p₁ p₂ : ↥K × Fin m) (h : (Sum.inl p₁ : LCoord K m C_int) = Sum.inl p₂) =>
          Sum.inl.inj h)]
      exact Finset.card_le_card him
    have hclean_le : ((cleanPairs K L F c_excl ω).card : ℝ) ≤ 2 * ε * B_cap := by
      have h1 : ((cleanPairs K L F c_excl ω).card : ℝ) ≤ ((selTrials K L F c_excl ω).card : ℝ) :=
        Nat.cast_le.mpr hclean_le_S
      have hηB : η * B_cap ≤ ε * B_cap := mul_le_mul_of_nonneg_right hηε hB0.le
      linarith [h1, hS, hμS_le_B, hηB]
    have hhit_lt := hHit hclean_le
    have hdet := card_uncoloredSub_le K L F c_excl ω
    have hr_slack : (4 * (r : ℝ) + 4) * ε ^ 2 * B_cap ≤ 8 * (r : ℝ) * ε ^ 2 * B_cap := by
      have h1 : 4 * (r : ℝ) + 4 ≤ 8 * (r : ℝ) := by linarith
      have h2 : 0 ≤ ε ^ 2 * B_cap := by positivity
      nlinarith only [h1, h2]
    linarith [hbad, hdet, hU, hS, hCol, hhit_lt, hμS_le_F, hr_slack]
  have hmc := subset_mcdiarmid_bounds K L hr hQ hL_card hdeg ε η L_t C_t B_cap
    hε0 hε1 hη0 hηε hC0 hCL hCB hC_int_le hL_int_lo hL_int_hi hQp_lo hQp_hi hQ2 hL_big
    x F hFx hFB c_excl
  have hch := hitClean_bad_bound K L hr hQ hunif hlin hdeg ε η L_t C_t B_cap
    hε0 hε1 hη0 hηε2 hC0 hCL hCB hC_int_le hC_int_pos hQp_hi F c_excl
  have hcard_u : ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      (F.card : ℝ) * (1 - ε) + (8 * (r : ℝ) * ε ^ 2 + 8 * η) * B_cap <
        ((uncoloredSub K L F c_excl ω).card : ℝ))).card : ℝ) ≤
      (E1.card : ℝ) + (E2.card : ℝ) + (E3.card : ℝ) + (E4.card : ℝ) := by
    have hnat : (Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
        (F.card : ℝ) * (1 - ε) + (8 * (r : ℝ) * ε ^ 2 + 8 * η) * B_cap <
          ((uncoloredSub K L F c_excl ω).card : ℝ))).card ≤
        E1.card + E2.card + E3.card + E4.card := by
      calc _ ≤ (E1 ∪ E2 ∪ E3 ∪ E4).card := Finset.card_le_card hcov
        _ ≤ (E1 ∪ E2 ∪ E3).card + E4.card := Finset.card_union_le _ _
        _ ≤ (E1 ∪ E2).card + E3.card + E4.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ ≤ E1.card + E2.card + E3.card + E4.card :=
            Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    exact_mod_cast hnat
  linarith [hcard_u, hmc.1, hmc.2.1, hmc.2.2, hch]


/-- External survivors of `incVC K L x c`: edges incident to `x` whose color `c` is not blocked
at any other vertex `y ∈ A \ {x}`. -/
noncomputable def extSurvVC {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (x : Fin n) (c : Fin m)
    (ω : LCoord K m C_int → Fin Q) : Finset ↥K :=
  (incVC K L x c).filter (fun A =>
    ∀ y ∈ A.1.erase x, ∀ e ∈ blockCoordNe K L A y c, (ω e).val ≠ 0)

/-- `extVC` and `depSubsetExcl F (some c)` are disjoint for `F ⊆ incVC K L x c`. -/
lemma disjoint_depSubsetExcl_extVC {n m C_int : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m))
    (hlin : ∀ E ∈ K, ∀ F ∈ K, E ≠ F → (E ∩ F).card ≤ 1)
    (x : Fin n) (c : Fin m) (F : Finset ↥K) (hF : F ⊆ incVC K L x c) :
    Disjoint (depSubsetExcl K L (C_int := C_int) F (some c)) (extVC K L x c) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  have hcol_c : coordColor e = c := coordColor_mem_extVC he2
  simp only [depSubsetExcl, Finset.mem_biUnion, Finset.mem_union] at he1
  rcases he1 with ⟨A, hAF, hA1 | hA2⟩
  · rcases Finset.mem_image.mp hA1 with ⟨c', _, rfl⟩
    have hc' : c' = c := hcol_c
    subst hc'
    simp only [extVC, Finset.mem_biUnion] at he2
    rcases he2 with ⟨B, hBinc, y, hyB, hyblk⟩
    have hAB : A ≠ B := fun hEq => by
      subst hEq; exact (Finset.mem_erase.mp hyblk).1 rfl
    have hmem_blk := Finset.mem_of_mem_erase hyblk
    simp only [blockCoord, realVC, dummyCoord, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and] at hmem_blk
    rcases hmem_blk with ⟨A', ⟨hyA', _⟩, hEq⟩ | ⟨_, _, hEq⟩
    · have hAA' : A' = A := congrArg Prod.fst (Sum.inl.inj hEq)
      subst hAA'
      have hxA : x ∈ A'.1 := (Finset.mem_filter.mp (hF hAF)).2.1
      have hxB : x ∈ B.1 := (Finset.mem_filter.mp hBinc).2.1
      have hy_ne : y ≠ x := (Finset.mem_erase.mp hyB).1
      have hyB' : y ∈ B.1 := Finset.mem_of_mem_erase hyB
      have hsub : ({x, y} : Finset (Fin n)) ⊆ A'.1 ∩ B.1 := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hxA, hxB⟩
        · exact Finset.mem_inter.mpr ⟨hyA', hyB'⟩
      have hcard2 : 2 ≤ (A'.1 ∩ B.1).card := by
        have hp : ({x, y} : Finset (Fin n)).card = 2 := Finset.card_pair hy_ne.symm
        exact hp ▸ Finset.card_le_card hsub
      have hle1 := hlin A'.1 A'.2 B.1 B.2 (fun h => hAB (Subtype.ext h))
      omega
    · exact Sum.inl_ne_inr hEq.symm
  · rcases hA2 with ⟨c', hc'sub, heblk⟩
    have hne : c' ≠ c := (Finset.mem_erase.mp hc'sub).1
    have hcol' : coordColor e = c' := coordColor_mem_edgeColorBlock heblk
    exact hne (hcol'.symm.trans hcol_c)

/-- `uncoloredSub` depends only on `depSubsetExcl`. -/
lemma uncoloredSub_dependsOn {n m C_int Q : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (F : Finset ↥K) (c_excl : Option (Fin m))
    (ω₁ ω₂ : LCoord K m C_int → Fin Q)
    (hEq : ∀ e ∈ depSubsetExcl K L F c_excl, ω₁ e = ω₂ e) :
    uncoloredSub K L F c_excl ω₁ = uncoloredSub K L F c_excl ω₂ := by
  refine Finset.filter_congr fun A hAF => forall₂_congr fun c' hc' => not_congr ?_
  have hmem_inl : ∀ c'' ∈ L A.1, (Sum.inl (A, c'') : LCoord K m C_int) ∈ depSubsetExcl K L F c_excl :=
    fun c'' hc'' => Finset.mem_biUnion.mpr
      ⟨A, hAF, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c'', hc'', rfl⟩)⟩
  have hmem_blk : ∀ e ∈ edgeColorBlock K L (C_int := C_int) A c', e ∈ depSubsetExcl K L F c_excl :=
    fun e he => Finset.mem_biUnion.mpr
      ⟨A, hAF, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c', hc', he⟩)⟩
  have hc'L : c' ∈ L A.1 := by
    cases c_excl with
    | none => exact hc'
    | some c => exact Finset.mem_of_mem_erase hc'
  simp only [isColored, hEq _ (hmem_inl c' hc'L)]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
  · refine forall₂_congr fun c'' hc'' => imp_congr_right fun _ => ?_
    rw [hEq _ (hmem_inl c'' hc'')]
  · refine forall₂_congr fun e he => ?_
    rw [hEq _ (hmem_blk e he)]

/-- McDiarmid concentration for `extSurvVC` (the first half of `ColDegBad`). -/
lemma colF_bad_bound {n m C_int r Q : ℕ}
    (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hr : 4 ≤ r) (hQ : 0 < Q)
    (hunif : ∀ E ∈ K, E.card = r)
    (hlin : ∀ E ∈ K, ∀ F ∈ K, E ≠ F → (E ∩ F).card ≤ 1)
    (hdeg : ∀ x c, (K.filter (fun B => x ∈ B ∧ c ∈ L B)).card ≤ C_int)
    (ε η L_t C_t : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hη0 : 0 < η) (hηε : η ≤ ε) (hrε : (r : ℝ) * ε ≤ 1 / 8)
    (hC0 : 0 < C_t) (hCL : C_t ≤ L_t) (_hC2 : 2 ≤ C_t)
    (hC_int_lo : C_t - 1 ≤ (C_int : ℝ)) (hC_int_le : (C_int : ℝ) ≤ C_t) (hC_int_pos : 1 ≤ C_int)
    (hQp_lo : (ε / L_t) * (1 - ε / L_t) ≤ 1 / (Q : ℝ))
    (hQp_hi : 1 / (Q : ℝ) ≤ ε / L_t) (hQ2 : 1 / (Q : ℝ) ≤ 1 / 2)
    (hL_big : 8 / η ≤ L_t)
    (x : Fin n) (c : Fin m) :
    ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      C_t * Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) + 2 * η * C_t <
        ((extSurvVC K L x c ω).card : ℝ))).card : ℝ) ≤
      2 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
        (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
  have hL0 : 0 < L_t := lt_of_lt_of_le hC0 hCL
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hp0 : 0 ≤ 1 / (Q : ℝ) := by positivity
  let S := extVC K L (C_int := C_int) x c
  let f : (LCoord K m C_int → Fin Q) → ℝ := fun ω => ((extSurvVC K L x c ω).card : ℝ)
  have hinc_le : (incVC K L x c).card ≤ C_int := (card_incVC K L x c).le.trans (hdeg x c)
  have hS_card : (S.card : ℝ) ≤ (r : ℝ) * C_t ^ 2 := by
    have h1 : S.card ≤ ∑ A ∈ incVC K L x c,
        ((A.1.erase x).biUnion (fun y => blockCoordNe K L (C_int := C_int) A y c)).card :=
      Finset.card_biUnion_le
    have h2 : ∑ A ∈ incVC K L x c,
        ((A.1.erase x).biUnion (fun y => blockCoordNe K L (C_int := C_int) A y c)).card =
        (incVC K L x c).card * ((r - 1) * (C_int - 1)) := by
      calc _ = ∑ _A ∈ incVC K L x c, ((r - 1) * (C_int - 1)) :=
            Finset.sum_congr rfl fun A hA => by
              rcases (Finset.mem_filter.mp hA).2 with ⟨hxA, hcA⟩
              exact card_edgeColorBlock_erase K L hunif hlin hdeg A hxA hcA
        _ = (incVC K L x c).card * ((r - 1) * (C_int - 1)) := by simp
    have h3 : S.card ≤ C_int * (r * C_int) :=
      h1.trans (h2.le.trans (Nat.mul_le_mul hinc_le
        (Nat.mul_le_mul (Nat.sub_le r 1) (Nat.sub_le C_int 1))))
    have h3' : (S.card : ℝ) ≤ (C_int : ℝ) * ((r : ℝ) * (C_int : ℝ)) := by exact_mod_cast h3
    have h4 : (C_int : ℝ) * ((r : ℝ) * (C_int : ℝ)) ≤ C_t * ((r : ℝ) * C_t) :=
      mul_le_mul hC_int_le (mul_le_mul_of_nonneg_left hC_int_le hr_pos.le) (by positivity) hC0.le
    linarith [h3', h4]
  have hV_ge : (∑ _e ∈ S, ((r : ℝ)) ^ 2) / (Q : ℝ) ≤ (r : ℝ) ^ 3 * ε * C_t := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc ((S.card : ℝ) * (r : ℝ) ^ 2) / (Q : ℝ)
        = (S.card : ℝ) * (r : ℝ) ^ 2 * (1 / (Q : ℝ)) := by ring
      _ ≤ ((r : ℝ) * C_t ^ 2) * (r : ℝ) ^ 2 * (ε / L_t) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hS_card (sq_nonneg _)) hQp_hi hp0 (by positivity)
      _ = (C_t / L_t) * ((r : ℝ) ^ 3 * ε * C_t) := by field_simp
      _ ≤ 1 * ((r : ℝ) ^ 3 * ε * C_t) :=
          mul_le_mul_of_nonneg_right ((div_le_one hL0).mpr hCL) (by positivity)
      _ = (r : ℝ) ^ 3 * ε * C_t := one_mul _
  have hdep : ∀ ω₁ ω₂, (∀ e ∈ S, ω₁ e = ω₂ e) → f ω₁ = f ω₂ := by
    intro ω₁ ω₂ hEq
    simp only [f, extSurvVC]; congr 2
    refine Finset.filter_congr fun A hA => forall₂_congr fun y hy => forall₂_congr fun e he => ?_
    rw [hEq e (Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_biUnion.mpr ⟨y, hy, he⟩⟩)]
  have hconst : ∀ e ∈ S, ∀ ω (a b : Fin Q), a.val ≠ 0 → b.val ≠ 0 →
      f (Function.update ω e a) = f (Function.update ω e b) := by
    intro e _ ω a b ha hb
    simp only [f, extSurvVC]; congr 2
    refine Finset.filter_congr fun A _ => forall₂_congr fun y _ => forall₂_congr fun e' _ => ?_
    by_cases h : e' = e
    · subst h; simp [ha, hb]
    · simp [Function.update_of_ne h]
  have hlip : ∀ e ∈ S, ∀ ω (a : Fin Q), a.val ≠ 0 →
      |f (Function.update ω e ⟨0, hQ⟩) - f (Function.update ω e a)| ≤ (r : ℝ) := by
    intro e _ ω a ha
    let touch := (incVC K L x c).filter (fun A => ∃ y ∈ A.1.erase x, e ∈ blockCoordNe K L A y c)
    have hsub₁ : extSurvVC K L x c (Function.update ω e ⟨0, hQ⟩) ⊆
        extSurvVC K L x c (Function.update ω e a) := by
      intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hAinc, hall⟩
      refine Finset.mem_filter.mpr ⟨hAinc, fun y hy e' he' => ?_⟩
      by_cases h : e' = e
      · subst h; simpa using ha
      · simpa [Function.update_of_ne h] using hall y hy e' he'
    have hsub₂ : extSurvVC K L x c (Function.update ω e a) ⊆
        extSurvVC K L x c (Function.update ω e ⟨0, hQ⟩) ∪ touch := by
      intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hAinc, hall⟩
      by_cases ht : ∃ y ∈ A.1.erase x, e ∈ blockCoordNe K L A y c
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hAinc, ht⟩)
      · push Not at ht
        apply Finset.mem_union_left
        refine Finset.mem_filter.mpr ⟨hAinc, fun y hy e' he' => ?_⟩
        have hne : e' ≠ e := fun h => ht y hy (h ▸ he')
        simpa [Function.update_of_ne hne] using hall y hy e' he'
    have hlin_pair : ∀ y : Fin n, y ≠ x →
        ((incVC K L x c).filter (fun A => y ∈ A.1)).card ≤ 1 := by
      intro y hyne
      refine Finset.card_le_one.mpr fun A₁ hA₁ A₂ hA₂ => ?_
      by_contra hne
      have hx₁ : x ∈ A₁.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hA₁).1).2.1
      have hx₂ : x ∈ A₂.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hA₂).1).2.1
      have hy₁ : y ∈ A₁.1 := (Finset.mem_filter.mp hA₁).2
      have hy₂ : y ∈ A₂.1 := (Finset.mem_filter.mp hA₂).2
      have hsubp : ({x, y} : Finset (Fin n)) ⊆ A₁.1 ∩ A₂.1 := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hx₁, hx₂⟩
        · exact Finset.mem_inter.mpr ⟨hy₁, hy₂⟩
      have hc2 : 2 ≤ (A₁.1 ∩ A₂.1).card := by
        have hp : ({x, y} : Finset (Fin n)).card = 2 := Finset.card_pair hyne.symm
        exact hp ▸ Finset.card_le_card hsubp
      have hle1 := hlin A₁.1 A₁.2 A₂.1 A₂.2 (fun h => hne (Subtype.ext h))
      omega
    have htouch_le : touch.card ≤ r := by
      cases e with
      | inr p =>
        rcases p with ⟨y, c', j⟩
        by_cases hyx : y = x
        · have hemp : touch = ∅ := by
            ext A
            simp only [touch, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro _ ⟨y', hy', hmem⟩
            have hmem' := Finset.mem_of_mem_erase hmem
            simp only [blockCoord, realVC, dummyCoord, Finset.mem_union, Finset.mem_image] at hmem'
            rcases hmem' with ⟨_, _, hEq⟩ | ⟨_, _, hEq⟩
            · exact Sum.inl_ne_inr hEq
            · have hy_eq : y' = y := congrArg Prod.fst (Sum.inr.inj hEq)
              exact (Finset.mem_erase.mp hy').1 (hy_eq.trans hyx)
          rw [hemp]; simp
        · have htsub : touch ⊆ (incVC K L x c).filter (fun A => y ∈ A.1) := by
            intro A hA
            rcases Finset.mem_filter.mp hA with ⟨hAinc, y', hy', hmem⟩
            have hmem' := Finset.mem_of_mem_erase hmem
            simp only [blockCoord, realVC, dummyCoord, Finset.mem_union, Finset.mem_image] at hmem'
            rcases hmem' with ⟨_, _, hEq⟩ | ⟨_, _, hEq⟩
            · exact (Sum.inl_ne_inr hEq).elim
            · have hy_eq : y' = y := congrArg Prod.fst (Sum.inr.inj hEq)
              exact Finset.mem_filter.mpr ⟨hAinc, hy_eq ▸ Finset.mem_of_mem_erase hy'⟩
          exact ((Finset.card_le_card htsub).trans (hlin_pair y hyx)).trans (by omega)
      | inl q =>
        rcases q with ⟨B, c'⟩
        have htsub : touch ⊆ (B.1.erase x).biUnion
            (fun y => (incVC K L x c).filter (fun A => y ∈ A.1)) := by
          intro A hA
          rcases Finset.mem_filter.mp hA with ⟨hAinc, y, hyA, hmem⟩
          have hmem' := Finset.mem_of_mem_erase hmem
          simp only [blockCoord, realVC, dummyCoord, Finset.mem_union, Finset.mem_image,
            Finset.mem_filter, Finset.mem_univ, true_and] at hmem'
          rcases hmem' with ⟨B', ⟨hyB', _⟩, hEq⟩ | ⟨_, _, hEq⟩
          · have hBB' : B' = B := congrArg Prod.fst (Sum.inl.inj hEq)
            subst hBB'
            refine Finset.mem_biUnion.mpr ⟨y, Finset.mem_erase.mpr
              ⟨(Finset.mem_erase.mp hyA).1, hyB'⟩,
              Finset.mem_filter.mpr ⟨hAinc, Finset.mem_of_mem_erase hyA⟩⟩
          · exact (Sum.inl_ne_inr hEq.symm).elim
        calc touch.card
            ≤ ((B.1.erase x).biUnion (fun y => (incVC K L x c).filter (fun A => y ∈ A.1))).card :=
              Finset.card_le_card htsub
          _ ≤ ∑ y ∈ B.1.erase x, ((incVC K L x c).filter (fun A => y ∈ A.1)).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _y ∈ B.1.erase x, 1 :=
              Finset.sum_le_sum fun y hy => hlin_pair y (Finset.mem_erase.mp hy).1
          _ = (B.1.erase x).card := by simp
          _ ≤ B.1.card := Finset.card_erase_le
          _ = r := hunif B.1 B.2
    have habs := abs_card_sub_le hsub₁ hsub₂
    have htr : (touch.card : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr htouch_le
    exact habs.trans htr
  have hμ_eq : (∑ ω : LCoord K m C_int → Fin Q, f ω) /
      (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) =
      ((incVC K L x c).card : ℝ) * (1 - 1 / (Q : ℝ)) ^ ((r - 1) * (C_int - 1)) := by
    have hrew : ∀ ω : LCoord K m C_int → Fin Q,
        extSurvVC K L x c ω = (incVC K L x c).filter (fun A =>
          ∀ e ∈ (A.1.erase x).biUnion (fun y => blockCoordNe K L A y c), (ω e).val ≠ 0) := by
      intro ω
      refine Finset.filter_congr fun A _ => ?_
      constructor
      · intro h e he
        rcases Finset.mem_biUnion.mp he with ⟨y, hy, hye⟩
        exact h y hy e hye
      · intro h y hy e hye
        exact h e (Finset.mem_biUnion.mpr ⟨y, hy, hye⟩)
    have havg := avg_sum_disjoint_filter (X := LCoord K m C_int) Q hQ (incVC K L x c)
      (fun A => (A.1.erase x).biUnion (fun y => blockCoordNe K L A y c))
    have hμ1 : (∑ ω : LCoord K m C_int → Fin Q, f ω) /
        (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) =
        ∑ A ∈ incVC K L x c,
          (1 - 1 / (Q : ℝ)) ^ ((A.1.erase x).biUnion (fun y => blockCoordNe K L (C_int := C_int) A y c)).card := by
      refine (congrArg (· / (Fintype.card (LCoord K m C_int → Fin Q) : ℝ))
        (Finset.sum_congr rfl fun ω _ => ?_)).trans havg
      simp only [f, hrew ω]
      exact congrArg (fun s : Finset ↥K => (s.card : ℝ)) (by ext A; simp only [Finset.mem_filter])
    rw [hμ1]
    calc ∑ A ∈ incVC K L x c,
          (1 - 1 / (Q : ℝ)) ^ ((A.1.erase x).biUnion (fun y => blockCoordNe K L (C_int := C_int) A y c)).card
        = ∑ _A ∈ incVC K L x c, (1 - 1 / (Q : ℝ)) ^ ((r - 1) * (C_int - 1)) :=
          Finset.sum_congr rfl fun A hA => by
            rcases (Finset.mem_filter.mp hA).2 with ⟨hxA, hcA⟩
            rw [card_edgeColorBlock_erase K L hunif hlin hdeg A hxA hcA]
      _ = ((incVC K L x c).card : ℝ) * (1 - 1 / (Q : ℝ)) ^ ((r - 1) * (C_int - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hμ_hi : ((incVC K L x c).card : ℝ) * (1 - 1 / (Q : ℝ)) ^ ((r - 1) * (C_int - 1)) ≤
      C_t * Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) + η * C_t := by
    have hpow : (1 - 1 / (Q : ℝ)) ^ ((r - 1) * (C_int - 1)) ≤
        Real.exp (-(((r - 1) * (C_int - 1) : ℕ) : ℝ) * (1 / (Q : ℝ))) := by
      have h1 : 1 - 1 / (Q : ℝ) ≤ Real.exp (-(1 / (Q : ℝ))) := by
        linarith [Real.add_one_le_exp (-(1 / (Q : ℝ)))]
      calc (1 - 1 / (Q : ℝ)) ^ ((r - 1) * (C_int - 1))
          ≤ (Real.exp (-(1 / (Q : ℝ)))) ^ ((r - 1) * (C_int - 1)) :=
            pow_le_pow_left₀ (by linarith [hQ2]) h1 _
        _ = Real.exp ((((r - 1) * (C_int - 1) : ℕ) : ℝ) * (-(1 / (Q : ℝ)))) :=
            (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(((r - 1) * (C_int - 1) : ℕ) : ℝ) * (1 / (Q : ℝ))) := by congr 1; ring
    have hCsub : C_t - 2 ≤ ((C_int - 1 : ℕ) : ℝ) := by
      have h1 : ((C_int - 1 : ℕ) : ℝ) = (C_int : ℝ) - 1 := by
        rw [Nat.cast_sub hC_int_pos, Nat.cast_one]
      linarith [h1, hC_int_lo]
    have hL_eta : 8 ≤ η * L_t := by
      have := mul_le_mul_of_nonneg_left hL_big hη0.le
      have hc : η * (8 / η) = 8 := by field_simp
      linarith
    have hεL1 : ε / L_t ≤ 1 := (div_le_one hL0).mpr (by nlinarith only [hL_eta, hηε, hε1, hL0, hη0])
    have hcp : C_t * (ε / L_t) - 3 * ε / L_t ≤ ((C_int - 1 : ℕ) : ℝ) * (1 / (Q : ℝ)) := by
      have h1 : (C_t - 2) * ((ε / L_t) * (1 - ε / L_t)) ≤ ((C_int - 1 : ℕ) : ℝ) * (1 / (Q : ℝ)) :=
        mul_le_mul hCsub hQp_lo (mul_nonneg (by positivity) (by linarith)) (Nat.cast_nonneg _)
      have h2 : (C_t - 2) * ((ε / L_t) * (1 - ε / L_t)) =
          C_t * (ε / L_t) - (C_t / L_t) * (ε ^ 2 / L_t) - 2 * ε / L_t + 2 * ε ^ 2 / L_t ^ 2 := by
        field_simp; ring
      have h3 : (C_t / L_t) * (ε ^ 2 / L_t) ≤ ε / L_t := by
        calc (C_t / L_t) * (ε ^ 2 / L_t) ≤ 1 * (ε ^ 2 / L_t) :=
              mul_le_mul_of_nonneg_right ((div_le_one hL0).mpr hCL) (by positivity)
          _ = ε * (ε / L_t) := by ring
          _ ≤ 1 * (ε / L_t) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = ε / L_t := one_mul _
      have h4 : 0 ≤ 2 * ε ^ 2 / L_t ^ 2 := by positivity
      linarith [h1, h2, h3, h4, show 3 * ε / L_t = ε / L_t + 2 * ε / L_t by ring]
    have harg : ((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t) - 3 * (r : ℝ) * ε / L_t ≤
        (((r - 1) * (C_int - 1) : ℕ) : ℝ) * (1 / (Q : ℝ)) := by
      have hrmul : ((r - 1 : ℕ) : ℝ) * (C_t * (ε / L_t) - 3 * ε / L_t) ≤
          ((r - 1 : ℕ) : ℝ) * (((C_int - 1 : ℕ) : ℝ) * (1 / (Q : ℝ))) :=
        mul_le_mul_of_nonneg_left hcp (Nat.cast_nonneg _)
      have hle_r : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr (Nat.sub_le r 1)
      have h3r : ((r - 1 : ℕ) : ℝ) * (3 * ε / L_t) ≤ (r : ℝ) * (3 * ε / L_t) :=
        mul_le_mul_of_nonneg_right hle_r (by positivity)
      rw [Nat.cast_mul]
      linarith [hrmul, h3r,
        show ((r - 1 : ℕ) : ℝ) * (C_t * (ε / L_t) - 3 * ε / L_t) =
          ((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t) - ((r - 1 : ℕ) : ℝ) * (3 * ε / L_t) by ring,
        show (r : ℝ) * (3 * ε / L_t) = 3 * (r : ℝ) * ε / L_t by ring,
        show ((r - 1 : ℕ) : ℝ) * (((C_int - 1 : ℕ) : ℝ) * (1 / (Q : ℝ))) =
          ((r - 1 : ℕ) : ℝ) * ((C_int - 1 : ℕ) : ℝ) * (1 / (Q : ℝ)) by ring]
    have herr_le : 3 * (r : ℝ) * ε / L_t ≤ η / 2 := by
      rw [div_le_iff₀ hL0]
      have h1 : 3 * (r : ℝ) * ε ≤ 4 := by linarith [hrε]
      nlinarith only [h1, hL_eta]
    have hexp_err : Real.exp (3 * (r : ℝ) * ε / L_t) ≤ 1 + η := by
      have hhalf : 3 * (r : ℝ) * ε / L_t ≤ 1 / 2 := by nlinarith only [herr_le, hηε, hε1]
      have h1 := exp_le_one_add_two_mul (by positivity) hhalf
      linarith [h1, herr_le]
    have hpow_hi : (1 - 1 / (Q : ℝ)) ^ ((r - 1) * (C_int - 1)) ≤
        Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) * (1 + η) := by
      calc (1 - 1 / (Q : ℝ)) ^ ((r - 1) * (C_int - 1))
          ≤ Real.exp (-(((r - 1) * (C_int - 1) : ℕ) : ℝ) * (1 / (Q : ℝ))) := hpow
        _ ≤ Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t) + 3 * (r : ℝ) * ε / L_t) := by
            rw [Real.exp_le_exp]; linarith [harg]
        _ = Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) *
              Real.exp (3 * (r : ℝ) * ε / L_t) := Real.exp_add _ _
        _ ≤ Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) * (1 + η) :=
            mul_le_mul_of_nonneg_left hexp_err (Real.exp_pos _).le
    have hinc_real : ((incVC K L x c).card : ℝ) ≤ C_t :=
      (Nat.cast_le.mpr hinc_le).trans hC_int_le
    have hexp_le1 : Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t) := by positivity
      linarith
    calc ((incVC K L x c).card : ℝ) * (1 - 1 / (Q : ℝ)) ^ ((r - 1) * (C_int - 1))
        ≤ C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) * (1 + η)) :=
          mul_le_mul hinc_real hpow_hi (pow_nonneg (by linarith [hQ2]) _) hC0.le
      _ = C_t * Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) +
            η * C_t * Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) := by ring
      _ ≤ C_t * Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) + η * C_t * 1 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp_le1 (by positivity))
      _ = C_t * Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) + η * C_t := by rw [mul_one]
  have hmc := bernoulli_mcdiarmid_sub Q hQ S (fun _ => (r : ℝ)) f (r : ℝ)
    ((r : ℝ) ^ 3 * ε * C_t) (η * C_t) hr_pos (by positivity) (by positivity)
    (fun _ _ => hr_pos.le) (fun _ _ => le_rfl) hV_ge hdep hconst hlip
  have hsub : Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      C_t * Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) + 2 * η * C_t < f ω) ⊆
      Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
        η * C_t ≤ |f ω - (∑ ω' : LCoord K m C_int → Fin Q, f ω') /
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ)|) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rw [hμ_eq]
    have h1 : η * C_t ≤ f ω - ((incVC K L x c).card : ℝ) *
        (1 - 1 / (Q : ℝ)) ^ ((r - 1) * (C_int - 1)) := by
      linarith [hω, hμ_hi]
    exact h1.trans (le_abs_self _)
  have hexp_cmp : η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) * C_t ≤
      min ((η * C_t) ^ 2 / (4 * ((r : ℝ) ^ 3 * ε * C_t))) (η * C_t / (2 * (r : ℝ))) := by
    apply le_min
    · have heq : (η * C_t) ^ 2 / (4 * ((r : ℝ) ^ 3 * ε * C_t)) =
          η ^ 2 / (4 * (r : ℝ) ^ 3 * ε) * C_t := by field_simp
      rw [heq]
      have hden : 4 * (r : ℝ) ^ 3 * ε ≤ 32 * (r : ℝ) ^ 3 * ε := by
        have : 0 < (r : ℝ) ^ 3 * ε := by positivity
        linarith
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (sq_nonneg η) (by positivity) hden) hC0.le
    · have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith only [hr4]
      have hrat : η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) ≤ η / (2 * (r : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : 2 * (r : ℝ) * η ≤ 32 * (r : ℝ) ^ 3 * ε := by
          have : (r : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith only [hr4, hr2]
          nlinarith only [this, hηε, hr_pos, hε0]
        nlinarith only [h1, hη0]
      calc η ^ 2 / (32 * (r : ℝ) ^ 3 * ε) * C_t
          ≤ η / (2 * (r : ℝ)) * C_t := mul_le_mul_of_nonneg_right hrat hC0.le
        _ = η * C_t / (2 * (r : ℝ)) := by ring
  calc ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
          C_t * Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) + 2 * η * C_t < f ω)).card : ℝ)
      ≤ ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
          η * C_t ≤ |f ω - (∑ ω' : LCoord K m C_int → Fin Q, f ω') /
            (Fintype.card (LCoord K m C_int → Fin Q) : ℝ)|)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ 2 * Real.exp (-min ((η * C_t) ^ 2 / (4 * ((r : ℝ) ^ 3 * ε * C_t)))
          (η * C_t / (2 * (r : ℝ)))) *
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := hmc
    _ ≤ 2 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
          (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (Nat.cast_nonneg _)
        rw [Real.exp_le_exp]; linarith [hexp_cmp]

/-- Combined color-degree bad-event bound (`≤ 9 * exp(-c_exp * C_t)`). -/
lemma col_deg_bad_bound {n m C_int r Q L_int : ℕ}
    (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hr : 4 ≤ r) (hQ : 0 < Q)
    (hunif : ∀ E ∈ K, E.card = r)
    (hlin : ∀ E ∈ K, ∀ F ∈ K, E ≠ F → (E ∩ F).card ≤ 1)
    (hL_card : ∀ E ∈ K, (L E).card = L_int)
    (hdeg : ∀ x c, (K.filter (fun B => x ∈ B ∧ c ∈ L B)).card ≤ C_int)
    (ε η L_t C_t : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hη0 : 0 < η) (hηε : η ≤ ε) (hηε2 : η ≤ ε ^ 2)
    (hrε : (r : ℝ) * ε ≤ 1 / 8)
    (hC0 : 0 < C_t) (hCL : C_t ≤ L_t) (hC2 : 2 ≤ C_t)
    (hC_int_lo : C_t - 1 ≤ (C_int : ℝ)) (hC_int_le : (C_int : ℝ) ≤ C_t) (hC_int_pos : 1 ≤ C_int)
    (hL_int_lo : L_t - 1 ≤ (L_int : ℝ)) (hL_int_hi : (L_int : ℝ) ≤ L_t)
    (hQp_lo : (ε / L_t) * (1 - ε / L_t) ≤ 1 / (Q : ℝ))
    (hQp_hi : 1 / (Q : ℝ) ≤ ε / L_t) (hQ2 : 1 / (Q : ℝ) ≤ 1 / 2)
    (hL_big : 8 / η ≤ L_t)
    (x : Fin n) (c : Fin m) :
    ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) * (1 - ε) +
        8 * (r : ℝ) * ε ^ 2 + 10 * η) <
        (((survEdges K L ω).filter (fun A =>
          x ∈ A ∧ ∃ hA : A ∈ K, c ∈ nextList K L ω ⟨A, hA⟩)).card : ℝ))).card : ℝ) ≤
      9 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
        (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
  let E_F := Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
    C_t * Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) + 2 * η * C_t <
      ((extSurvVC K L x c ω).card : ℝ))
  let P_G : Finset ↥K → (LCoord K m C_int → Fin Q) → Prop := fun F ω =>
    F ⊆ incVC K L x c ∧
    (F.card : ℝ) * (1 - ε) + (8 * (r : ℝ) * ε ^ 2 + 8 * η) * C_t <
      ((uncoloredSub K L F (some c) ω).card : ℝ)
  let E_G := Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
    P_G (extSurvVC K L x c ω) ω)
  have hcov : Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) * (1 - ε) +
        8 * (r : ℝ) * ε ^ 2 + 10 * η) <
        (((survEdges K L ω).filter (fun A =>
          x ∈ A ∧ ∃ hA : A ∈ K, c ∈ nextList K L ω ⟨A, hA⟩)).card : ℝ)) ⊆ E_F ∪ E_G := by
    intro ω hω
    have hbad := (Finset.mem_filter.mp hω).2
    by_contra hnot
    simp only [Finset.mem_union, not_or, E_F, E_G, P_G, Finset.mem_filter, Finset.mem_univ,
      true_and, not_lt, not_and] at hnot
    rcases hnot with ⟨hF_le, hG_le⟩
    have hG_le' := hG_le (Finset.filter_subset _ _)
    have hcard_surv : ((survEdges K L ω).filter (fun A =>
        x ∈ A ∧ ∃ hA : A ∈ K, c ∈ nextList K L ω ⟨A, hA⟩)).card ≤
        (uncoloredSub K L (extSurvVC K L x c ω) (some c) ω).card := by
      have hsub_im : (survEdges K L ω).filter (fun A =>
          x ∈ A ∧ ∃ hA : A ∈ K, c ∈ nextList K L ω ⟨A, hA⟩) ⊆
          (uncoloredSub K L (extSurvVC K L x c ω) (some c) ω).image Subtype.val := by
        intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hAs, hxA, hAK, hc_nl⟩
        rcases Finset.mem_filter.mp hc_nl with ⟨hcL, hblk⟩
        rcases Finset.mem_filter.mp hAs with ⟨_, hnot⟩
        refine Finset.mem_image.mpr ⟨⟨A, hAK⟩, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA, hcL⟩, ?_⟩
          intro y hy e he
          exact hblk e (Finset.mem_biUnion.mpr ⟨y, Finset.mem_of_mem_erase hy, he⟩)
        · intro c' hc'
          exact hnot hAK c' (Finset.mem_of_mem_erase hc')
      exact (Finset.card_le_card hsub_im).trans Finset.card_image_le
    have hcard_surv' : (((survEdges K L ω).filter (fun A =>
        x ∈ A ∧ ∃ hA : A ∈ K, c ∈ nextList K L ω ⟨A, hA⟩)).card : ℝ) ≤
        ((uncoloredSub K L (extSurvVC K L x c ω) (some c) ω).card : ℝ) :=
      Nat.cast_le.mpr hcard_surv
    have h1 : ((extSurvVC K L x c ω).card : ℝ) * (1 - ε) ≤
        (C_t * Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) + 2 * η * C_t) * (1 - ε) :=
      mul_le_mul_of_nonneg_right hF_le (by linarith)
    have h2 : (2 * η * C_t) * (1 - ε) ≤ 2 * η * C_t := by
      have : 0 ≤ 2 * η * C_t * ε := by positivity
      linarith
    linarith [hbad, hcard_surv', hG_le', h1, h2]
  have hEF := colF_bad_bound K L hr hQ hunif hlin hdeg ε η L_t C_t
    hε0 hε1 hη0 hηε hrε hC0 hCL hC2 hC_int_lo hC_int_le hC_int_pos hQp_lo hQp_hi hQ2 hL_big x c
  have hEG : (E_G.card : ℝ) ≤ 7 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
      (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
    refine (le_of_eq (congrArg (fun s : Finset _ => (s.card : ℝ))
      (by ext ω; simp only [E_G, Finset.mem_filter, Finset.mem_univ, true_and]))).trans
      (card_filter_cond_split hQ (extVC K L x c) (extSurvVC K L x c) ?_ P_G ?_
        (7 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t)) ?_)
    · intro ω₁ ω₂ hEq
      refine Finset.filter_congr fun A hA => forall₂_congr fun y hy => forall₂_congr fun e he => ?_
      rw [hEq e (Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_biUnion.mpr ⟨y, hy, he⟩⟩)]
    · intro F ω₁ ω₂ hEq
      by_cases hFsub : F ⊆ incVC K L x c
      · have hdisj := disjoint_depSubsetExcl_extVC (C_int := C_int) K L hlin x c F hFsub
        have hunc := uncoloredSub_dependsOn K L F (some c) ω₁ ω₂ fun e he =>
          hEq e (Finset.disjoint_left.mp hdisj he)
        simp only [P_G, hunc]
      · simp only [P_G, hFsub, false_and]
    · intro F
      by_cases hFsub : F ⊆ incVC K L x c
      · have hFx : ∀ A ∈ F, x ∈ A.1 := fun A hA => (Finset.mem_filter.mp (hFsub hA)).2.1
        have hFB : (F.card : ℝ) ≤ C_t := by
          have h1 : F.card ≤ C_int :=
            (Finset.card_le_card hFsub).trans ((card_incVC K L x c).le.trans (hdeg x c))
          exact (Nat.cast_le.mpr h1).trans hC_int_le
        refine (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans
          (subset_colored_bad_bound K L hr hQ hunif hlin hL_card hdeg ε η L_t C_t C_t
            hε0 hε1 hη0 hηε hηε2 hC0 hCL le_rfl hC_int_le hC_int_pos hL_int_lo hL_int_hi
            hQp_lo hQp_hi hQ2 hL_big x F hFx hFB (some c))
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, P_G] at hω ⊢
        exact hω.2
      · refine (le_of_eq (congrArg (fun s : Finset _ => (s.card : ℝ))
          (by ext ω; simp [P_G, hFsub] : _ = (∅ : Finset (LCoord K m C_int → Fin Q))))).trans ?_
        simp only [Finset.card_empty, Nat.cast_zero]
        positivity
  have hcu : ((Finset.univ.filter (fun ω : LCoord K m C_int → Fin Q =>
      C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) * (1 - ε) +
        8 * (r : ℝ) * ε ^ 2 + 10 * η) <
        (((survEdges K L ω).filter (fun A =>
          x ∈ A ∧ ∃ hA : A ∈ K, c ∈ nextList K L ω ⟨A, hA⟩)).card : ℝ))).card : ℝ) ≤
      (E_F.card : ℝ) + (E_G.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  linarith [hcu, hEF, hEG]

/-- Active `(vertex, color)` pairs with positive color-degree. -/
def activeVC {n m : ℕ} (K : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) : Finset (Fin n × Fin m) :=
  Finset.univ.filter (fun p => (incVC K L p.1 p.2).Nonempty)

/-- Dependency degree bound across all three bad-event families. -/
lemma list_dep_deg_bound {n m C_int r L_int D_int : ℕ}
    (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hr : 4 ≤ r) (hC_pos : 1 ≤ C_int)
    (hunif : ∀ E ∈ K, E.card = r)
    (hL_card : ∀ E ∈ K, (L E).card = L_int)
    (hD_deg : ∀ x, (K.filter (fun A => x ∈ A)).card ≤ D_int)
    (hC_deg : ∀ x c, (K.filter (fun A => x ∈ A ∧ c ∈ L A)).card ≤ C_int)
    (hCL : C_int ≤ L_int) :
    let I := ↥K ⊕ Fin n ⊕ ↥(activeVC K L)
    let dep : I → Finset (LCoord K m C_int) := fun i =>
      match i with
      | Sum.inl A => depList K L A
      | Sum.inr (Sum.inl x) => depSubset K L (Finset.univ.filter (fun A : ↥K => x ∈ A.1))
      | Sum.inr (Sum.inr p) => depSubset K L (incVC K L p.1.1 p.1.2)
    ∀ i : I, ((Finset.univ : Finset I).filter (fun j => ¬ Disjoint (dep i) (dep j))).card ≤
      8 * r ^ 3 * (D_int + L_int + 1) ^ 5 := by
  intro I dep i
  set M := D_int + L_int + 1
  have hL_le : L_int ≤ M := by omega
  have hC_le : C_int ≤ M := by omega
  have hD_le : D_int ≤ M := by omega
  have h1_le : 1 ≤ M := by omega
  have hblk_le : ∀ (A : ↥K) (y : Fin n) (c : Fin m),
      (blockCoordNe K L (C_int := C_int) A y c).card ≤ C_int := fun A y c =>
    Finset.card_erase_le.trans (card_blockCoord K L y c (hC_deg y c)).le
  have hdepList_le : ∀ A : ↥K, (depList K L (C_int := C_int) A).card ≤ r * L_int * C_int := fun A => by
    calc (depList K L (C_int := C_int) A).card
        ≤ ∑ c ∈ L A.1, (edgeColorBlock K L (C_int := C_int) A c).card := Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ L A.1, (r * C_int) := Finset.sum_le_sum fun c _ => by
          calc (edgeColorBlock K L (C_int := C_int) A c).card
              ≤ ∑ y ∈ A.1, (blockCoordNe K L (C_int := C_int) A y c).card := Finset.card_biUnion_le
            _ ≤ ∑ _y ∈ A.1, C_int := Finset.sum_le_sum fun y _ => hblk_le A y c
            _ = A.1.card * C_int := by simp
            _ = r * C_int := by rw [hunif A.1 A.2]
      _ = (L A.1).card * (r * C_int) := by simp
      _ = r * L_int * C_int := by rw [hL_card A.1 A.2]; ring
  have hdepEdge_le : ∀ A : ↥K, (depEdge K L (C_int := C_int) A).card ≤ 2 * r * L_int * C_int := fun A => by
    have h1 : (((L A.1).image (fun c => (Sum.inl (A, c) : LCoord K m C_int))).card) ≤ L_int :=
      Finset.card_image_le.trans (hL_card A.1 A.2).le
    have h2 : L_int ≤ r * L_int * C_int := by
      calc L_int = 1 * L_int * 1 := by ring
        _ ≤ r * L_int * C_int := Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) hC_pos
    exact (Finset.card_union_le _ _).trans
      ((Nat.add_le_add h1 (hdepList_le A)).trans (by nlinarith [h2]))
  have hdep_i : (dep i).card ≤ 2 * r * M ^ 3 := by
    rcases i with A | x | p
    · have h1 := hdepList_le A
      have h2 : r * L_int * C_int ≤ r * M * M :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl hL_le) hC_le
      have h3 : r * M * M ≤ 2 * r * M ^ 3 := by
        have hM1 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right h1_le (by decide)
        nlinarith [hM1]
      exact h1.trans (h2.trans h3)
    · have hFx : (Finset.univ.filter (fun A : ↥K => x ∈ A.1)).card ≤ D_int := by
        have hbij : (Finset.univ.filter (fun A : ↥K => x ∈ A.1)).card =
            (K.filter (fun A => x ∈ A)).card := by
          refine Finset.card_bij (fun A _ => A.1) ?_ ?_ ?_
          · intro A hA; exact Finset.mem_filter.mpr ⟨A.2, (Finset.mem_filter.mp hA).2⟩
          · intro _ _ _ _ h; exact Subtype.ext h
          · intro A hA
            rcases Finset.mem_filter.mp hA with ⟨hAK, hx⟩
            exact ⟨⟨A, hAK⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
        rw [hbij]; exact hD_deg x
      calc (depSubset K L (C_int := C_int) (Finset.univ.filter (fun A : ↥K => x ∈ A.1))).card
          ≤ ∑ A ∈ Finset.univ.filter (fun A : ↥K => x ∈ A.1),
              (depEdge K L (C_int := C_int) A).card := Finset.card_biUnion_le
        _ ≤ ∑ _A ∈ Finset.univ.filter (fun A : ↥K => x ∈ A.1), (2 * r * L_int * C_int) :=
            Finset.sum_le_sum fun A _ => hdepEdge_le A
        _ = (Finset.univ.filter (fun A : ↥K => x ∈ A.1)).card * (2 * r * L_int * C_int) := by simp
        _ ≤ D_int * (2 * r * L_int * C_int) := Nat.mul_le_mul_right _ hFx
        _ ≤ M * (2 * r * M * M) :=
            Nat.mul_le_mul hD_le (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hL_le) hC_le)
        _ = 2 * r * M ^ 3 := by ring
    · have hFvc : (incVC K L p.1.1 p.1.2).card ≤ C_int :=
        (card_incVC K L p.1.1 p.1.2).le.trans (hC_deg p.1.1 p.1.2)
      calc (depSubset K L (C_int := C_int) (incVC K L p.1.1 p.1.2)).card
          ≤ ∑ A ∈ incVC K L p.1.1 p.1.2, (depEdge K L (C_int := C_int) A).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _A ∈ incVC K L p.1.1 p.1.2, (2 * r * L_int * C_int) :=
            Finset.sum_le_sum fun A _ => hdepEdge_le A
        _ = (incVC K L p.1.1 p.1.2).card * (2 * r * L_int * C_int) := by simp
        _ ≤ C_int * (2 * r * L_int * C_int) := Nat.mul_le_mul_right _ hFvc
        _ ≤ M * (2 * r * M * M) :=
            Nat.mul_le_mul hC_le (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hL_le) hC_le)
        _ = 2 * r * M ^ 3 := by ring
  have howner : ∀ e : LCoord K m C_int,
      ((Finset.univ : Finset ↥K).filter (fun A => e ∈ depEdge K L A)).card ≤ 2 * r * C_int := by
    intro e
    cases e with
    | inl q =>
      rcases q with ⟨B, c⟩
      have hsub : (Finset.univ : Finset ↥K).filter (fun A => Sum.inl (B, c) ∈ depEdge K L (C_int := C_int) A) ⊆
          insert B (B.1.biUnion (fun y => incVC K L y c)) := by
        intro A hA
        have hmem := (Finset.mem_filter.mp hA).2
        rcases Finset.mem_union.mp hmem with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨_, _, hEq⟩
          exact Finset.mem_insert.mpr (Or.inl (congrArg Prod.fst (Sum.inl.inj hEq)))
        · simp only [depList, edgeColorBlock, Finset.mem_biUnion] at h2
          rcases h2 with ⟨c', hc'L, y, hyA, hblk⟩
          have hc' : c' = c := (coordColor_mem_blockCoordNe hblk).symm
          subst hc'
          have hblk' := Finset.mem_of_mem_erase hblk
          simp only [blockCoord, realVC, dummyCoord, Finset.mem_union, Finset.mem_image,
            Finset.mem_filter, Finset.mem_univ, true_and] at hblk'
          rcases hblk' with ⟨B', ⟨hyB', _⟩, hEq⟩ | ⟨_, _, hEq⟩
          · have hBB' : B' = B := congrArg Prod.fst (Sum.inl.inj hEq)
            subst hBB'
            exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
              ⟨y, hyB', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyA, hc'L⟩⟩)
          · exact (Sum.inl_ne_inr hEq.symm).elim
      calc ((Finset.univ : Finset ↥K).filter (fun A => Sum.inl (B, c) ∈ depEdge K L (C_int := C_int) A)).card
          ≤ (insert B (B.1.biUnion (fun y => incVC K L y c))).card := Finset.card_le_card hsub
        _ ≤ (B.1.biUnion (fun y => incVC K L y c)).card + 1 := Finset.card_insert_le _ _
        _ ≤ (∑ y ∈ B.1, (incVC K L y c).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le 1
        _ ≤ (∑ _y ∈ B.1, C_int) + 1 :=
            Nat.add_le_add_right (Finset.sum_le_sum fun y _ =>
              (card_incVC K L y c).le.trans (hC_deg y c)) 1
        _ = r * C_int + 1 := by simp [hunif B.1 B.2]
        _ ≤ 2 * r * C_int := by nlinarith [hr, hC_pos]
    | inr q =>
      rcases q with ⟨y, c, j⟩
      have hsub : (Finset.univ : Finset ↥K).filter
          (fun A => Sum.inr (y, c, j) ∈ depEdge K L (C_int := C_int) A) ⊆ incVC K L y c := by
        intro A hA
        have hmem := (Finset.mem_filter.mp hA).2
        rcases Finset.mem_union.mp hmem with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨_, _, hEq⟩
          exact (Sum.inl_ne_inr hEq).elim
        · simp only [depList, edgeColorBlock, Finset.mem_biUnion] at h2
          rcases h2 with ⟨c', hc'L, y', hy'A, hblk⟩
          have hblk' := Finset.mem_of_mem_erase hblk
          simp only [blockCoord, realVC, dummyCoord, Finset.mem_union, Finset.mem_image] at hblk'
          rcases hblk' with ⟨_, _, hEq⟩ | ⟨_, _, hEq⟩
          · exact (Sum.inl_ne_inr hEq).elim
          · have hy_eq : y' = y := congrArg Prod.fst (Sum.inr.inj hEq)
            have hc_eq : c' = c := congrArg (fun p : Fin n × Fin m × Fin C_int => p.2.1) (Sum.inr.inj hEq)
            subst hy_eq; subst hc_eq
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'A, hc'L⟩
      exact ((Finset.card_le_card hsub).trans ((card_incVC K L y c).le.trans (hC_deg y c))).trans
        (by nlinarith [hr])
  have hhit_e : ∀ e : LCoord K m C_int,
      ((Finset.univ : Finset I).filter (fun j => e ∈ dep j)).card ≤ 4 * r ^ 2 * M ^ 2 := by
    intro e
    let own := (Finset.univ : Finset ↥K).filter (fun A => e ∈ depEdge K L A)
    have hown_card : own.card ≤ 2 * r * C_int := howner e
    let S1 : Finset I := own.image Sum.inl
    let S2 : Finset I := (own.biUnion (fun A => A.1)).image (fun x => Sum.inr (Sum.inl x))
    let S3 : Finset I := (Finset.univ : Finset ↥(activeVC K L)).filter
      (fun p => ∃ A ∈ own, p.1.1 ∈ A.1 ∧ p.1.2 ∈ L A.1) |>.image (fun p => Sum.inr (Sum.inr p))
    have hcov : (Finset.univ : Finset I).filter (fun j => e ∈ dep j) ⊆ S1 ∪ S2 ∪ S3 := by
      intro j hj
      have hmem := (Finset.mem_filter.mp hj).2
      rcases j with A | x | p
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨A, ?_, rfl⟩))
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union_right _ hmem⟩
      · simp only [dep, depSubset, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
          true_and] at hmem
        rcases hmem with ⟨A, hxA, hAe⟩
        refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, ?_, rfl⟩))
        exact Finset.mem_biUnion.mpr ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAe⟩, hxA⟩
      · simp only [dep, depSubset, incVC, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
          true_and] at hmem
        rcases hmem with ⟨A, ⟨hxA, hcA⟩, hAe⟩
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, ?_, rfl⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, A,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAe⟩, hxA, hcA⟩
    have hS1 : S1.card ≤ 2 * r * C_int := Finset.card_image_le.trans hown_card
    have hS2 : S2.card ≤ 2 * r ^ 2 * C_int := by
      calc S2.card ≤ (own.biUnion (fun A => A.1)).card := Finset.card_image_le
        _ ≤ ∑ A ∈ own, A.1.card := Finset.card_biUnion_le
        _ = own.card * r := by
            rw [Finset.sum_congr rfl fun A _ => hunif A.1 A.2]; simp
        _ ≤ (2 * r * C_int) * r := Nat.mul_le_mul_right r hown_card
        _ = 2 * r ^ 2 * C_int := by ring
    have hS3 : S3.card ≤ 2 * r ^ 2 * L_int * C_int := by
      have hsub3 : ((Finset.univ : Finset ↥(activeVC K L)).filter
          (fun p => ∃ A ∈ own, p.1.1 ∈ A.1 ∧ p.1.2 ∈ L A.1)).image Subtype.val ⊆
          own.biUnion (fun A => A.1 ×ˢ L A.1) := by
        intro q hq
        rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
        rcases (Finset.mem_filter.mp hp).2 with ⟨A, hAown, hxA, hcA⟩
        exact Finset.mem_biUnion.mpr ⟨A, hAown, Finset.mem_product.mpr ⟨hxA, hcA⟩⟩
      have hcard3 : ((Finset.univ : Finset ↥(activeVC K L)).filter
          (fun p => ∃ A ∈ own, p.1.1 ∈ A.1 ∧ p.1.2 ∈ L A.1)).card ≤
          (own.biUnion (fun A => A.1 ×ˢ L A.1)).card := by
        rw [← Finset.card_image_of_injective _ Subtype.val_injective]
        exact Finset.card_le_card hsub3
      calc S3.card
          ≤ ((Finset.univ : Finset ↥(activeVC K L)).filter
              (fun p => ∃ A ∈ own, p.1.1 ∈ A.1 ∧ p.1.2 ∈ L A.1)).card := Finset.card_image_le
        _ ≤ (own.biUnion (fun A => A.1 ×ˢ L A.1)).card := hcard3
        _ ≤ ∑ A ∈ own, (A.1 ×ˢ L A.1).card := Finset.card_biUnion_le
        _ = own.card * (r * L_int) := by
            rw [Finset.sum_congr rfl fun A _ => by
              rw [Finset.card_product, hunif A.1 A.2, hL_card A.1 A.2]]
            simp
        _ ≤ (2 * r * C_int) * (r * L_int) := Nat.mul_le_mul_right _ hown_card
        _ = 2 * r ^ 2 * L_int * C_int := by ring
    have htot : ((Finset.univ : Finset I).filter (fun j => e ∈ dep j)).card ≤
        2 * r * C_int + 2 * r ^ 2 * C_int + 2 * r ^ 2 * L_int * C_int := by
      calc _ ≤ (S1 ∪ S2 ∪ S3).card := Finset.card_le_card hcov
        _ ≤ (S1 ∪ S2).card + S3.card := Finset.card_union_le _ _
        _ ≤ S1.card + S2.card + S3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ ≤ _ := Nat.add_le_add (Nat.add_le_add hS1 hS2) hS3
    have h1 : 2 * r * C_int ≤ r ^ 2 * M ^ 2 := by
      have hC_M2 : C_int ≤ M ^ 2 := hC_le.trans (by nlinarith [h1_le])
      have h2r : 2 * r ≤ r ^ 2 := by nlinarith [hr]
      exact Nat.mul_le_mul h2r hC_M2
    have h2 : 2 * r ^ 2 * C_int ≤ r ^ 2 * M ^ 2 := by
      have hCM : C_int + 1 ≤ M := by omega
      have : 2 * C_int ≤ M ^ 2 := by nlinarith [hCM]
      nlinarith [this]
    have h3 : 2 * r ^ 2 * L_int * C_int ≤ 2 * r ^ 2 * M ^ 2 := by
      have : L_int * C_int ≤ M ^ 2 := by
        calc L_int * C_int ≤ M * M := Nat.mul_le_mul hL_le hC_le
          _ = M ^ 2 := by ring
      nlinarith [this]
    linarith [htot, h1, h2, h3,
      show r ^ 2 * M ^ 2 + r ^ 2 * M ^ 2 + 2 * r ^ 2 * M ^ 2 = 4 * r ^ 2 * M ^ 2 by ring]
  have hnd_sub : (Finset.univ : Finset I).filter (fun j => ¬ Disjoint (dep i) (dep j)) ⊆
      (dep i).biUnion (fun e => (Finset.univ : Finset I).filter (fun j => e ∈ dep j)) := by
    intro j hj
    have hnd := (Finset.mem_filter.mp hj).2
    rw [Finset.not_disjoint_iff] at hnd
    rcases hnd with ⟨e, hei, hej⟩
    exact Finset.mem_biUnion.mpr ⟨e, hei, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hej⟩⟩
  calc ((Finset.univ : Finset I).filter (fun j => ¬ Disjoint (dep i) (dep j))).card
      ≤ ((dep i).biUnion (fun e => (Finset.univ : Finset I).filter (fun j => e ∈ dep j))).card :=
        Finset.card_le_card hnd_sub
    _ ≤ ∑ e ∈ dep i, ((Finset.univ : Finset I).filter (fun j => e ∈ dep j)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ dep i, (4 * r ^ 2 * M ^ 2) := Finset.sum_le_sum fun e _ => hhit_e e
    _ = (dep i).card * (4 * r ^ 2 * M ^ 2) := by simp
    _ ≤ (2 * r * M ^ 3) * (4 * r ^ 2 * M ^ 2) := Nat.mul_le_mul_right _ hdep_i
    _ = 8 * r ^ 3 * M ^ 5 := by ring

/-- Single equalized Kahn list-nibble round via the Symmetric Lovász Local Lemma. -/
theorem list_nibble_round {n m r : ℕ} (hr : 4 ≤ r) (hm : 0 < m)
    (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hunif : ∀ E ∈ K, E.card = r)
    (hlin : ∀ E ∈ K, ∀ F ∈ K, E ≠ F → (E ∩ F).card ≤ 1)
    (ε η D_t L_t C_t : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hη0 : 0 < η) (hηε : η ≤ ε) (hηε2 : η ≤ ε ^ 2)
    (hrε : (r : ℝ) * ε ≤ 1 / 8)
    (hC0 : 0 < C_t) (hCD : C_t ≤ D_t) (hCL : C_t ≤ L_t) (hC2 : 2 ≤ C_t)
    (hL_big : 8 / η ≤ L_t)
    (hD_deg : ∀ x, ((K.filter (fun A => x ∈ A)).card : ℝ) ≤ D_t)
    (hL_ge : ∀ A ∈ K, L_t ≤ ((L A).card : ℝ))
    (hC_deg : ∀ x c, ((K.filter (fun A => x ∈ A ∧ c ∈ L A)).card : ℝ) ≤ C_t)
    (hLLL : 36 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) *
      ((8 * r ^ 3 * (Nat.floor D_t + Nat.floor L_t + 1) ^ 5 : ℕ) + 1 : ℝ) ≤ 1) :
    ∃ (K' : Finset (Finset (Fin n))) (L' : Finset (Fin n) → Finset (Fin m))
      (col : Finset (Fin n) → Fin m),
      K' ⊆ K ∧
      (∀ A ∈ K \ K', col A ∈ L A) ∧
      (∀ A ∈ K \ K', ∀ B ∈ K \ K', A ≠ B → (A ∩ B).Nonempty → col A ≠ col B) ∧
      (∀ A ∈ K', L' A ⊆ L A) ∧
      (∀ A ∈ K', ∀ B ∈ K \ K', (A ∩ B).Nonempty → col B ∉ L' A) ∧
      (∀ x, ((K'.filter (fun A => x ∈ A)).card : ℝ) ≤
        D_t * (1 - ε + 8 * (r : ℝ) * ε ^ 2 + 8 * η)) ∧
      (∀ A ∈ K', L_t * (Real.exp (-(r : ℝ) * ε * (C_t / L_t)) - 2 * η) ≤ ((L' A).card : ℝ)) ∧
      (∀ x c, ((K'.filter (fun A => x ∈ A ∧ c ∈ L' A)).card : ℝ) ≤
        C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) * (1 - ε) +
          8 * (r : ℝ) * ε ^ 2 + 10 * η)) := by
  have hL0 : 0 < L_t := lt_of_lt_of_le hC0 hCL
  have hD0 : 0 < D_t := lt_of_lt_of_le hC0 hCD
  let L_int : ℕ := Nat.floor L_t
  let C_int : ℕ := Nat.floor C_t
  let D_int : ℕ := Nat.floor D_t
  have hL_int_hi : (L_int : ℝ) ≤ L_t := Nat.floor_le hL0.le
  have hL_int_lo : L_t - 1 ≤ (L_int : ℝ) := by linarith [Nat.lt_floor_add_one L_t]
  have hC_int_le : (C_int : ℝ) ≤ C_t := Nat.floor_le hC0.le
  have hC_int_lo : C_t - 1 ≤ (C_int : ℝ) := by linarith [Nat.lt_floor_add_one C_t]
  have hC_int_pos : 1 ≤ C_int := Nat.le_floor (by norm_num; linarith [hC2])
  have hCL_int : C_int ≤ L_int := Nat.floor_mono hCL
  have hD_deg_nat : ∀ x, (K.filter (fun A => x ∈ A)).card ≤ D_int :=
    fun x => Nat.le_floor (hD_deg x)
  -- Trim each list `L A` (`A ∈ K`) to an arbitrary subset `L0 A ⊆ L A` of exact size `L_int`.
  have htrim_ex : ∀ A ∈ K, ∃ S ⊆ L A, S.card = L_int := fun A hA =>
    Finset.exists_subset_card_eq (by
      have h1 : (L_int : ℝ) ≤ ((L A).card : ℝ) := hL_int_hi.trans (hL_ge A hA)
      exact_mod_cast h1)
  let L0 : Finset (Fin n) → Finset (Fin m) := fun A =>
    if hA : A ∈ K then Classical.choose (htrim_ex A hA) else ∅
  have hL0_sub : ∀ A ∈ K, L0 A ⊆ L A := fun A hA => by
    simp only [L0, dif_pos hA]; exact (Classical.choose_spec (htrim_ex A hA)).1
  have hL0_card : ∀ A ∈ K, (L0 A).card = L_int := fun A hA => by
    simp only [L0, dif_pos hA]; exact (Classical.choose_spec (htrim_ex A hA)).2
  have hC_deg0 : ∀ x c, (K.filter (fun A => x ∈ A ∧ c ∈ L0 A)).card ≤ C_int := fun x c => by
    have hsub : K.filter (fun A => x ∈ A ∧ c ∈ L0 A) ⊆ K.filter (fun A => x ∈ A ∧ c ∈ L A) := by
      intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hAK, hx, hc⟩
      exact Finset.mem_filter.mpr ⟨hAK, hx, hL0_sub A hAK hc⟩
    exact (Finset.card_le_card hsub).trans (Nat.le_floor (hC_deg x c))
  let Q : ℕ := Nat.floor (L_t / ε) + 1
  have hQ : 0 < Q := Nat.succ_pos _
  have hQ_gt : L_t / ε < (Q : ℝ) := by
    simp only [Q, Nat.cast_add, Nat.cast_one]; exact Nat.lt_floor_add_one (L_t / ε)
  have hQ_le : (Q : ℝ) ≤ L_t / ε + 1 := by
    simp only [Q, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le (div_nonneg hL0.le hε0.le)]
  have hQp_hi : 1 / (Q : ℝ) ≤ ε / L_t := by
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr hQ) hL0, one_mul]
    have := (div_lt_iff₀ hε0).mp hQ_gt
    linarith
  have hQp_lo : (ε / L_t) * (1 - ε / L_t) ≤ 1 / (Q : ℝ) := by
    have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
    rw [le_div_iff₀ hQpos]
    calc (ε / L_t) * (1 - ε / L_t) * (Q : ℝ)
        ≤ (ε / L_t) * (1 - ε / L_t) * (L_t / ε + 1) := by
          have hL_eta : 8 ≤ η * L_t := by
            have := mul_le_mul_of_nonneg_left hL_big hη0.le
            have hc : η * (8 / η) = 8 := by field_simp
            linarith
          have hεL : ε / L_t ≤ 1 := (div_le_one hL0).mpr (by nlinarith only [hL_eta, hηε, hε1, hL0, hη0])
          exact mul_le_mul_of_nonneg_left hQ_le (mul_nonneg (by positivity) (by linarith))
      _ = 1 - (ε / L_t) ^ 2 := by field_simp; ring
      _ ≤ 1 := by linarith [sq_nonneg (ε / L_t)]
  have hQ2 : 1 / (Q : ℝ) ≤ 1 / 2 := by
    have hL_eta : 8 ≤ η * L_t := by
      have := mul_le_mul_of_nonneg_left hL_big hη0.le
      have hc : η * (8 / η) = 8 := by field_simp
      linarith
    have hεL : ε / L_t ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hL0 two_pos]; nlinarith only [hL_eta, hηε, hε1, hL0, hη0]
    exact hQp_hi.trans hεL
  have hrε2 : (r : ℝ) * ε ^ 2 ≤ 1 := by
    have : (r : ℝ) * ε * ε ≤ (1 / 8) * (1 / 2) := mul_le_mul hrε hε1 hε0.le (by positivity)
    linarith [show (r : ℝ) * ε * ε = (r : ℝ) * ε ^ 2 by ring]
  let I := ↥K ⊕ Fin n ⊕ ↥(activeVC K L0)
  let dep : I → Finset (LCoord K m C_int) := fun i =>
    match i with
    | Sum.inl A => depList K L0 A
    | Sum.inr (Sum.inl x) => depSubset K L0 (Finset.univ.filter (fun A : ↥K => x ∈ A.1))
    | Sum.inr (Sum.inr p) => depSubset K L0 (incVC K L0 p.1.1 p.1.2)
  let Bad : I → Finset (LCoord K m C_int → Fin Q) := fun i =>
    match i with
    | Sum.inl A => Finset.univ.filter (fun ω =>
        ((nextList K L0 ω A).card : ℝ) <
          L_t * (Real.exp (-(r : ℝ) * ε * (C_t / L_t)) - 2 * η))
    | Sum.inr (Sum.inl x) => Finset.univ.filter (fun ω =>
        (((Finset.univ.filter (fun A : ↥K => x ∈ A.1)).card : ℝ) * (1 - ε) +
          (8 * (r : ℝ) * ε ^ 2 + 8 * η) * D_t) <
          ((uncoloredSub K L0 (Finset.univ.filter (fun A : ↥K => x ∈ A.1)) none ω).card : ℝ))
    | Sum.inr (Sum.inr p) => Finset.univ.filter (fun ω =>
        C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) * (1 - ε) +
          8 * (r : ℝ) * ε ^ 2 + 10 * η) <
          (((survEdges K L0 ω).filter (fun A =>
            p.1.1 ∈ A ∧ ∃ hA : A ∈ K, p.1.2 ∈ nextList K L0 ω ⟨A, hA⟩)).card : ℝ))
  have hDep : ∀ i : I, DependsOn (dep i) (Bad i) := by
    intro i ω₁ ω₂ hEq
    rcases i with A | x | p
    · have hnl : nextList K L0 ω₁ A = nextList K L0 ω₂ A := by
        refine Finset.filter_congr fun c hc => forall₂_congr fun e he => ?_
        rw [hEq e (Finset.mem_biUnion.mpr ⟨c, hc, he⟩)]
      simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, hnl]
    · have hsub : depSubsetExcl K L0 (C_int := C_int)
          (Finset.univ.filter (fun A : ↥K => x ∈ A.1)) none ⊆
          dep (Sum.inr (Sum.inl x)) := by
        intro e he
        simp only [depSubsetExcl, dep, depSubset, depEdge, depList, listSub,
          Finset.mem_biUnion, Finset.mem_union] at he ⊢
        exact he
      have hunc := uncoloredSub_dependsOn K L0 (Finset.univ.filter (fun A : ↥K => x ∈ A.1))
        none ω₁ ω₂ (fun e he => hEq e (hsub he))
      simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, hunc]
    · have hfilt : (survEdges K L0 ω₁).filter (fun A =>
          p.1.1 ∈ A ∧ ∃ hA : A ∈ K, p.1.2 ∈ nextList K L0 ω₁ ⟨A, hA⟩) =
        (survEdges K L0 ω₂).filter (fun A =>
          p.1.1 ∈ A ∧ ∃ hA : A ∈ K, p.1.2 ∈ nextList K L0 ω₂ ⟨A, hA⟩) := by
        ext A
        simp only [survEdges, nextList, Finset.mem_filter]
        constructor <;> rintro ⟨⟨hAK, hnot⟩, hxA, _, hcL, hblk⟩
        · have hAinc : (⟨A, hAK⟩ : ↥K) ∈ incVC K L0 p.1.1 p.1.2 :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA, hcL⟩
          have hmem_edge : ∀ e ∈ depEdge K L0 (C_int := C_int) ⟨A, hAK⟩, ω₁ e = ω₂ e :=
            fun e he => hEq e (Finset.mem_biUnion.mpr ⟨⟨A, hAK⟩, hAinc, he⟩)
          refine ⟨⟨hAK, fun hAK' c hc hcol => hnot hAK' c hc ?_⟩, hxA, hAK, hcL, fun e he => ?_⟩
          · refine ⟨hcol.1, ?_, ?_, ?_⟩
            · rw [hmem_edge _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c, hcol.1, rfl⟩))]
              exact hcol.2.1
            · intro c' hc' hne
              rw [hmem_edge _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c', hc', rfl⟩))]
              exact hcol.2.2.1 c' hc' hne
            · intro e he
              rw [hmem_edge _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hcol.1, he⟩))]
              exact hcol.2.2.2 e he
          · rw [← hmem_edge _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p.1.2, hcL, he⟩))]
            exact hblk e he
        · have hAinc : (⟨A, hAK⟩ : ↥K) ∈ incVC K L0 p.1.1 p.1.2 :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA, hcL⟩
          have hmem_edge : ∀ e ∈ depEdge K L0 (C_int := C_int) ⟨A, hAK⟩, ω₁ e = ω₂ e :=
            fun e he => hEq e (Finset.mem_biUnion.mpr ⟨⟨A, hAK⟩, hAinc, he⟩)
          refine ⟨⟨hAK, fun hAK' c hc hcol => hnot hAK' c hc ?_⟩, hxA, hAK, hcL, fun e he => ?_⟩
          · refine ⟨hcol.1, ?_, ?_, ?_⟩
            · rw [← hmem_edge _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c, hcol.1, rfl⟩))]
              exact hcol.2.1
            · intro c' hc' hne
              rw [← hmem_edge _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c', hc', rfl⟩))]
              exact hcol.2.2.1 c' hc' hne
            · intro e he
              rw [← hmem_edge _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hcol.1, he⟩))]
              exact hcol.2.2.2 e he
          · rw [hmem_edge _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p.1.2, hcL, he⟩))]
            exact hblk e he
      simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, hfilt]
  let p_bad : ℝ := 9 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t)
  have hProb : ∀ i : I, ((Bad i).card : ℝ) ≤ p_bad * (Fintype.card (LCoord K m C_int → Fin Q) : ℝ) := by
    intro i
    rcases i with A | x | p
    · have hb := list_bad_bound K L0 hr hQ hunif hlin hL0_card hC_deg0 ε η L_t C_t
        hε0 hη0 hηε hrε2 hC0 hCL hC_int_le hL_int_lo hL_int_hi hQp_hi hQ2
        (by linarith [hL_big, show 2 / η ≤ 8 / η by exact div_le_div_of_nonneg_right (by norm_num) hη0.le]) A
      have h29 : (2 : ℝ) * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) ≤ p_bad := by
        simp only [p_bad]; linarith [Real.exp_pos (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t)]
      exact hb.trans (mul_le_mul_of_nonneg_right h29 (Nat.cast_nonneg _))
    · have hFx : ∀ A ∈ Finset.univ.filter (fun A : ↥K => x ∈ A.1), x ∈ A.1 :=
        fun _ hA => (Finset.mem_filter.mp hA).2
      have hFB : ((Finset.univ.filter (fun A : ↥K => x ∈ A.1)).card : ℝ) ≤ D_t := by
        have hbij : (Finset.univ.filter (fun A : ↥K => x ∈ A.1)).card =
            (K.filter (fun A => x ∈ A)).card := by
          refine Finset.card_bij (fun A _ => A.1) ?_ ?_ ?_
          · intro A hA; exact Finset.mem_filter.mpr ⟨A.2, (Finset.mem_filter.mp hA).2⟩
          · intro _ _ _ _ h; exact Subtype.ext h
          · intro A hA
            rcases Finset.mem_filter.mp hA with ⟨hAK, hx⟩
            exact ⟨⟨A, hAK⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
        rw [hbij]; exact hD_deg x
      have hb := subset_colored_bad_bound K L0 hr hQ hunif hlin hL0_card hC_deg0 ε η L_t C_t D_t
        hε0 hε1 hη0 hηε hηε2 hC0 hCL hCD hC_int_le hC_int_pos hL_int_lo hL_int_hi
        hQp_lo hQp_hi hQ2 hL_big x _ hFx hFB none
      have h79 : (7 : ℝ) * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) ≤ p_bad := by
        simp only [p_bad]; linarith [Real.exp_pos (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t)]
      exact hb.trans (mul_le_mul_of_nonneg_right h79 (Nat.cast_nonneg _))
    · exact col_deg_bad_bound K L0 hr hQ hunif hlin hL0_card hC_deg0 ε η L_t C_t
        hε0 hε1 hη0 hηε hηε2 hrε hC0 hCL hC2 hC_int_lo hC_int_le hC_int_pos hL_int_lo hL_int_hi
        hQp_lo hQp_hi hQ2 hL_big p.1.1 p.1.2
  have hDeg := list_dep_deg_bound K L0 hr hC_int_pos hunif hL0_card hD_deg_nat hC_deg0 hCL_int
  have hLLL' : 4 * p_bad * ((8 * r ^ 3 * (D_int + L_int + 1) ^ 5 : ℕ) + 1 : ℝ) ≤ 1 := by
    simpa only [p_bad, D_int, L_int, show 4 * (9 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t)) =
      36 * Real.exp (-(η ^ 2 / (32 * (r : ℝ) ^ 3 * ε)) * C_t) by ring] using hLLL
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  obtain ⟨ω, hω⟩ := lll_of_dependsOn Bad dep p_bad (8 * r ^ 3 * (D_int + L_int + 1) ^ 5)
    (by positivity) hLLL' hDep hProb (fun i => by
      refine (Finset.card_le_card ?_).trans (hDeg i)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj.2)
  refine ⟨survEdges K L0 ω,
    fun A => if hA : A ∈ K then nextList K L0 ω ⟨A, hA⟩ else ∅,
    roundColoring K L0 hm ω,
    Finset.filter_subset _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    rcases roundColoring_isColored K L0 hm ω hA with ⟨hAK, hcol⟩
    exact hL0_sub A hAK hcol.1
  · intro A hA B hB hAB hinter
    rcases roundColoring_isColored K L0 hm ω hA with ⟨hAK, hcolA⟩
    rcases roundColoring_isColored K L0 hm ω hB with ⟨hBK, hcolB⟩
    exact isColored_proper K L0 ω (fun h => hAB (congrArg Subtype.val h)) hinter hcolA hcolB
  · intro A hA
    have hAK : A ∈ K := Finset.filter_subset _ _ hA
    simp only [dif_pos hAK]
    exact (Finset.filter_subset _ _).trans (hL0_sub A hAK)
  · intro A hA B hB hinter
    have hAK : A ∈ K := Finset.filter_subset _ _ hA
    rcases roundColoring_isColored K L0 hm ω hB with ⟨hBK, hcolB⟩
    have hAB : (⟨A, hAK⟩ : ↥K) ≠ ⟨B, hBK⟩ := fun h => by
      have hEq : A = B := congrArg Subtype.val h
      exact (Finset.mem_sdiff.mp hB).2 (hEq ▸ hA)
    simp only [dif_pos hAK]
    exact isColored_disjoint_nextList K L0 ω hAB hinter hcolB
  · intro x
    have hgood := hω (Sum.inr (Sum.inl x))
    simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hgood
    have hsub_eq : ((survEdges K L0 ω).filter (fun A => x ∈ A)).card =
        (uncoloredSub K L0 (Finset.univ.filter (fun A : ↥K => x ∈ A.1)) none ω).card := by
      refine Finset.card_bij (fun A hA => ⟨A, (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1⟩)
        ?_ ?_ ?_
      · intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hAs, hxA⟩
        rcases Finset.mem_filter.mp hAs with ⟨hAK, hnot⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA⟩,
          fun c' hc' => hnot hAK c' hc'⟩
      · intro A₁ _ A₂ _ h; exact congrArg Subtype.val h
      · intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hAx, hnot⟩
        exact ⟨A.1, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨A.2, fun _ c' hc' => hnot c' hc'⟩, (Finset.mem_filter.mp hAx).2⟩, Subtype.ext rfl⟩
    have hFx_le : ((Finset.univ.filter (fun A : ↥K => x ∈ A.1)).card : ℝ) ≤ D_t := by
      have hbij : (Finset.univ.filter (fun A : ↥K => x ∈ A.1)).card =
          (K.filter (fun A => x ∈ A)).card := by
        refine Finset.card_bij (fun A _ => A.1) ?_ ?_ ?_
        · intro A hA; exact Finset.mem_filter.mpr ⟨A.2, (Finset.mem_filter.mp hA).2⟩
        · intro _ _ _ _ h; exact Subtype.ext h
        · intro A hA
          rcases Finset.mem_filter.mp hA with ⟨hAK, hx⟩
          exact ⟨⟨A, hAK⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
      rw [hbij]; exact hD_deg x
    rw [hsub_eq]
    have h1 : ((Finset.univ.filter (fun A : ↥K => x ∈ A.1)).card : ℝ) * (1 - ε) ≤ D_t * (1 - ε) :=
      mul_le_mul_of_nonneg_right hFx_le (by linarith)
    linarith [hgood, h1]
  · intro A hA
    have hAK : A ∈ K := Finset.filter_subset _ _ hA
    have hgood := hω (Sum.inl ⟨A, hAK⟩)
    simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hgood
    simpa only [dif_pos hAK] using hgood
  · intro x c
    by_cases hact : (x, c) ∈ activeVC K L0
    · have hgood := hω (Sum.inr (Sum.inr ⟨(x, c), hact⟩))
      simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hgood
      have hfeq : (survEdges K L0 ω).filter (fun A => x ∈ A ∧
          c ∈ (if hA : A ∈ K then nextList K L0 ω ⟨A, hA⟩ else ∅)) =
          (survEdges K L0 ω).filter (fun A => x ∈ A ∧ ∃ hA : A ∈ K, c ∈ nextList K L0 ω ⟨A, hA⟩) := by
        refine Finset.filter_congr fun A hA => and_congr_right fun _ => ?_
        have hAK : A ∈ K := Finset.filter_subset _ _ hA
        simp only [dif_pos hAK]
        exact ⟨fun hc => ⟨hAK, hc⟩, fun ⟨_, hc⟩ => hc⟩
      rw [hfeq]
      exact hgood
    · have hemp : (survEdges K L0 ω).filter (fun A => x ∈ A ∧
          c ∈ (if hA : A ∈ K then nextList K L0 ω ⟨A, hA⟩ else ∅)) = ∅ := by
        ext A
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hAs hxA hc
        have hAK : A ∈ K := Finset.filter_subset _ _ hAs
        simp only [dif_pos hAK] at hc
        have hcL0 : c ∈ L0 A := (Finset.mem_filter.mp hc).1
        exact hact (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨⟨A, hAK⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA, hcL0⟩⟩⟩)
      rw [hemp, Finset.card_empty, Nat.cast_zero]
      have h1 : 0 ≤ Real.exp (-((r - 1 : ℕ) : ℝ) * ε * (C_t / L_t)) * (1 - ε) :=
        mul_nonneg (Real.exp_pos _).le (by linarith)
      have h2 : 0 ≤ 8 * (r : ℝ) * ε ^ 2 + 10 * η := by positivity
      nlinarith only [hC0, h1, h2]

end ListNibbleRound

/- ### Section 4: Multi-Round ODE Tracking and Uniform List Coloring -/

section UniformListColoring

/-- Greedy neighbourhood bound for a hypergraph of maximum degree `d`. -/
lemma meet_le {n : ℕ} (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (d : ℕ) (hd : ∀ i ∈ A, (H.filter (fun B => i ∈ B)).card ≤ d) :
    (H.filter (fun B => (A ∩ B).Nonempty)).card ≤ A.card * d := by
  have heq : H.filter (fun B => (A ∩ B).Nonempty) =
      A.biUnion (fun i => H.filter (fun B => i ∈ B)) := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.Nonempty, Finset.mem_inter]
    constructor
    · rintro ⟨hB, i, hiA, hiB⟩; exact ⟨i, hiA, hB, hiB⟩
    · rintro ⟨i, hiA, hB, hiB⟩; exact ⟨hB, i, hiA, hiB⟩
  rw [heq]
  calc (A.biUnion (fun i => H.filter (fun B => i ∈ B))).card
      ≤ ∑ i ∈ A, (H.filter (fun B => i ∈ B)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, d := Finset.sum_le_sum hd
    _ = A.card * d := by simp

/-- Greedy list edge-coloring. -/
lemma greedy {n m : ℕ} (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hm : 0 < m)
    (hL : ∀ A ∈ H, ((H.erase A).filter (fun B => (A ∩ B).Nonempty)).card < (L A).card) :
    ∃ c : Finset (Fin n) → Fin m,
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A := by
  induction H using Finset.strongInductionOn with
  | _ H ih =>
    by_cases hH : H.Nonempty
    · obtain ⟨A, hA⟩ := hH
      let K := H.erase A
      have hKH : K ⊆ H := Finset.erase_subset _ _
      obtain ⟨c, hc, hcL⟩ := ih K (Finset.erase_ssubset hA) (by
        intro B hB
        refine lt_of_le_of_lt ?_ (hL B (hKH hB))
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset_erase _ hKH)))
      let blocked := (K.filter (fun B => (A ∩ B).Nonempty)).image c
      have hblocked : blocked.card < (L A).card :=
        lt_of_le_of_lt Finset.card_image_le (hL A hA)
      have hfree : (L A \ blocked).Nonempty := by
        apply Finset.card_pos.mp
        have := Finset.le_card_sdiff blocked (L A)
        omega
      obtain ⟨w, hw⟩ := hfree
      have hne : ∀ B ∈ K, (A ∩ B).Nonempty → w ≠ c B := by
        intro B hB hi he
        exact (Finset.mem_sdiff.mp hw).2
          (he ▸ Finset.mem_image_of_mem c (Finset.mem_filter.mpr ⟨hB, hi⟩))
      refine ⟨fun B => if B = A then w else c B, ?_, ?_⟩
      · intro B hB D hD hBD hi
        by_cases hBA : B = A
        · subst B
          have hDA := Ne.symm hBD
          simpa only [if_pos rfl, if_true, if_neg hDA] using
            hne D (Finset.mem_erase.mpr ⟨hDA, hD⟩) hi
        by_cases hDA : D = A
        · subst D
          have hi' : (A ∩ B).Nonempty := by simpa only [Finset.inter_comm] using hi
          simpa only [if_pos rfl, if_true, if_neg hBA] using
            (hne B (Finset.mem_erase.mpr ⟨hBA, hB⟩) hi').symm
        simpa only [if_neg hBA, if_neg hDA] using
          hc B (Finset.mem_erase.mpr ⟨hBA, hB⟩) D (Finset.mem_erase.mpr ⟨hDA, hD⟩) hBD hi
      · intro B hB
        by_cases hBA : B = A
        · subst B; simpa using (Finset.mem_sdiff.mp hw).1
        · simpa only [if_neg hBA] using hcL B (Finset.mem_erase.mpr ⟨hBA, hB⟩)
    · exact ⟨fun _ => ⟨0, hm⟩, fun A hA => (hH ⟨A, hA⟩).elim, fun A hA => (hH ⟨A, hA⟩).elim⟩

/-- Neighbourhood bound in a hypergraph of maximum degree `D`. -/
lemma nbhd_le {n : ℕ} (H : Finset (Finset (Fin n))) (D : ℕ) (A : Finset (Fin n)) (hA : A ∈ H)
    (hdeg : ∀ i, (H.filter (fun B => i ∈ B)).card ≤ D) :
    ((H.erase A).filter (fun B => (A ∩ B).Nonempty)).card ≤ A.card * (D - 1) := by
  apply meet_le
  intro i hi
  have heq : (H.erase A).filter (fun B => i ∈ B) = (H.filter (fun B => i ∈ B)).erase A := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, hBH⟩, hiB⟩; exact ⟨hne, hBH, hiB⟩
    · rintro ⟨hne, hBH, hiB⟩; exact ⟨⟨hne, hBH⟩, hiB⟩
  rw [heq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hA, hi⟩)]
  have := hdeg i
  omega

/-- Extending a partial list coloring when residual degrees fall below residual list sizes. -/
lemma finish_with_reserve {n m r d : ℕ} (hm : 0 < m) (H K : Finset (Finset (Fin n)))
    (L R : Finset (Fin n) → Finset (Fin m)) (c : Finset (Fin n) → Fin m)
    (hproper : ∀ A ∈ H \ K, ∀ B ∈ H \ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B)
    (hc : ∀ A ∈ H \ K, c A ∈ L A)
    (hsize : ∀ A ∈ K, A.card ≤ r)
    (hdeg : ∀ v, (K.filter (fun A => v ∈ A)).card ≤ d)
    (hR : ∀ A ∈ K, r * (d - 1) < (R A).card ∧ R A ⊆ L A)
    (hfree : ∀ A ∈ K, ∀ B ∈ H \ K, (A ∩ B).Nonempty → c B ∉ R A) :
    ∃ f : Finset (Fin n) → Fin m,
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → f A ≠ f B) ∧ ∀ A ∈ H, f A ∈ L A := by
  obtain ⟨g, hg, hgR⟩ := greedy K R hm (fun A hA =>
    ((nbhd_le K d A hA hdeg).trans (Nat.mul_le_mul_right _ (hsize A hA))).trans_lt (hR A hA).1)
  refine ⟨fun A => if A ∈ K then g A else c A, ?_, ?_⟩
  · intro A hA B hB hAB hi
    by_cases hAK : A ∈ K <;> by_cases hBK : B ∈ K <;> simp only [hAK, hBK, if_true, if_false]
    · exact hg A hAK B hBK hAB hi
    · exact fun he => hfree A hAK B (Finset.mem_sdiff.mpr ⟨hB, hBK⟩) hi (he ▸ hgR A hAK)
    · have hi' : (B ∩ A).Nonempty := by simpa only [Finset.inter_comm] using hi
      exact fun he => hfree B hBK A (Finset.mem_sdiff.mpr ⟨hA, hAK⟩) hi' (he.symm ▸ hgR B hBK)
    · exact hproper A (Finset.mem_sdiff.mpr ⟨hA, hAK⟩) B (Finset.mem_sdiff.mpr ⟨hB, hBK⟩) hAB hi
  · intro A hA
    by_cases hAK : A ∈ K
    · simpa only [if_pos hAK] using (hR A hAK).2 (hgR A hAK)
    · simpa only [if_neg hAK] using hc A (Finset.mem_sdiff.mpr ⟨hA, hAK⟩)

def M_param (r : ℕ) : ℕ := 200 * r ^ 2
noncomputable def ε_val (r : ℕ) : ℝ := 1 / (M_param r : ℝ)
def R_rounds (r : ℕ) : ℕ := 16 * r ^ 2 * M_param r
noncomputable def η_val (r : ℕ) : ℝ := 1 / (8 * (R_rounds r : ℝ) * (M_param r : ℝ) ^ 2)
noncomputable def δ_val (r : ℕ) : ℝ := 1 / ((r : ℝ) + 1)

/-- Deterministic ODE trajectory `(D_t, L_t, C_t)` for `R_rounds r` rounds of the list nibble. -/
noncomputable def odeState (r : ℕ) (D : ℝ) : ℕ → ℝ × ℝ × ℝ
  | 0 => (D, (1 + 1 / (r : ℝ)) * D, D)
  | t + 1 =>
    let st := odeState r D t
    let D_t := st.1
    let L_t := st.2.1
    let C_t := st.2.2
    let ε := ε_val r
    let η := η_val r
    let ρ := C_t / L_t
    (D_t * Real.exp (-ε / 2),
     L_t * (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η),
     C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
       8 * (r : ℝ) * ε ^ 2 + 10 * η))

lemma params_basic {r : ℕ} (hr : 4 ≤ r) :
    0 < ε_val r ∧ ε_val r ≤ 1 / 2 ∧
    0 < η_val r ∧ η_val r ≤ ε_val r ∧ η_val r ≤ (ε_val r) ^ 2 ∧
    (r : ℝ) * ε_val r ≤ 1 / 8 ∧
    (R_rounds r : ℝ) * ε_val r = 16 * (r : ℝ) ^ 2 ∧
    8 * (R_rounds r : ℝ) * η_val r ≤ 1 ∧
    8 * (r : ℝ) * (ε_val r) ^ 2 + 10 * η_val r ≤ ε_val r / 2 := by
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr2 : (16 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith only [hr4]
  have hM_eq : (M_param r : ℝ) = 200 * (r : ℝ) ^ 2 := by simp [M_param]
  have hR_eq : (R_rounds r : ℝ) = 16 * (r : ℝ) ^ 2 * (M_param r : ℝ) := by simp [R_rounds]
  have hM_ge : (3200 : ℝ) ≤ (M_param r : ℝ) := by linarith [hM_eq, hr2]
  have hM_pos : (0 : ℝ) < (M_param r : ℝ) := by linarith
  have hR_ge : (1 : ℝ) ≤ (R_rounds r : ℝ) := by nlinarith only [hR_eq, hr2, hM_ge]
  have hR_pos : (0 : ℝ) < (R_rounds r : ℝ) := by linarith
  have hε0 : 0 < ε_val r := by simp only [ε_val]; positivity
  have hε1 : ε_val r ≤ 1 / 2 := by
    simp only [ε_val]
    rw [div_le_div_iff₀ hM_pos two_pos]; linarith
  have hη0 : 0 < η_val r := by simp only [η_val]; positivity
  have hηε2 : η_val r ≤ (ε_val r) ^ 2 := by
    simp only [η_val, ε_val, one_div, inv_pow]
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith only [hR_ge, sq_nonneg (M_param r : ℝ)]
  have hηε : η_val r ≤ ε_val r := hηε2.trans (by
    rw [sq]; exact mul_le_of_le_one_right hε0.le (by linarith))
  have hrε : (r : ℝ) * ε_val r ≤ 1 / 8 := by
    simp only [ε_val, hM_eq]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [hr4, hr2]
  have hRε : (R_rounds r : ℝ) * ε_val r = 16 * (r : ℝ) ^ 2 := by
    simp only [ε_val, hR_eq]; field_simp
  have h8Rη : 8 * (R_rounds r : ℝ) * η_val r ≤ 1 := by
    simp only [η_val]
    have heq : 8 * (R_rounds r : ℝ) * (1 / (8 * (R_rounds r : ℝ) * (M_param r : ℝ) ^ 2)) =
        1 / (M_param r : ℝ) ^ 2 := by field_simp
    rw [heq]
    rw [div_le_one (by positivity)]
    nlinarith only [hM_ge]
  have hdrift : 8 * (r : ℝ) * (ε_val r) ^ 2 + 10 * η_val r ≤ ε_val r / 2 := by
    have h1 : 8 * (r : ℝ) * (ε_val r) ^ 2 + 10 * η_val r ≤
        (8 * (r : ℝ) + 10) * (ε_val r) ^ 2 := by linarith [hηε2]
    have h2 : (8 * (r : ℝ) + 10) * ε_val r ≤ 1 / 2 := by
      simp only [ε_val, hM_eq]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith only [hr4, hr2]
    have h3 : (8 * (r : ℝ) + 10) * (ε_val r) ^ 2 ≤ (1 / 2) * ε_val r := by
      calc (8 * (r : ℝ) + 10) * (ε_val r) ^ 2 = ((8 * (r : ℝ) + 10) * ε_val r) * ε_val r := by ring
        _ ≤ (1 / 2) * ε_val r := mul_le_mul_of_nonneg_right h2 hε0.le
    linarith [h1, h3]
  exact ⟨hε0, hε1, hη0, hηε, hηε2, hrε, hRε, h8Rη, hdrift⟩

lemma ode_D_eq (r : ℕ) (D : ℝ) :
    ∀ t : ℕ, (odeState r D t).1 = D * Real.exp (-(t : ℝ) * ε_val r / 2)
  | 0 => by simp [odeState]
  | t + 1 => by
    simp only [odeState, ode_D_eq r D t, Nat.cast_add, Nat.cast_one]
    rw [mul_assoc, ← Real.exp_add]
    congr 2; ring

lemma ode_pos_and_ratio {r : ℕ} (hr : 4 ≤ r) {D : ℝ} (hD : 0 < D) :
    ∀ t : ℕ,
      0 < (odeState r D t).1 ∧
      0 < (odeState r D t).2.1 ∧
      (odeState r D t).2.1 ≤ (1 + 1 / (r : ℝ)) * D ∧
      0 < (odeState r D t).2.2 ∧
      (odeState r D t).2.2 ≤ (odeState r D t).1 ∧
      (odeState r D t).2.2 / (odeState r D t).2.1 ≤
        (1 - δ_val r) * Real.exp (-(δ_val r / 2) * (t : ℝ) * ε_val r) := by
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hpb := params_basic hr
  rcases hpb with ⟨hε0, hε1, hη0, hηε, hηε2, hrε, _, _, hdrift⟩
  have hδ0 : 0 < δ_val r := by simp only [δ_val]; positivity
  have hδ1 : δ_val r ≤ 1 / 5 := by
    simp only [δ_val]; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  intro t
  induction t with
  | zero =>
    simp only [odeState, Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero, mul_one]
    have hL0_pos : 0 < (1 + 1 / (r : ℝ)) * D := by positivity
    refine ⟨hD, hL0_pos, le_rfl, hD, le_rfl, ?_⟩
    simp only [δ_val]
    have heq : D / ((1 + 1 / (r : ℝ)) * D) = 1 - 1 / ((r : ℝ) + 1) := by
      field_simp; ring
    linarith [heq]
  | succ t ih =>
    rcases ih with ⟨hDt, hLt, hLt_hi, hCt, hCD, hρ⟩
    set D_t := (odeState r D t).1
    set L_t := (odeState r D t).2.1
    set C_t := (odeState r D t).2.2
    set ε := ε_val r
    set η := η_val r
    set δ := δ_val r
    set ρ := C_t / L_t
    have hρ_pos : 0 < ρ := div_pos hCt hLt
    have hρ_le_sub : ρ ≤ 1 - δ := by
      have hexp1 : Real.exp (-(δ / 2) * (t : ℝ) * ε) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (δ / 2) * (t : ℝ) * ε := by positivity
        linarith
      calc ρ ≤ (1 - δ) * Real.exp (-(δ / 2) * (t : ℝ) * ε) := hρ
        _ ≤ (1 - δ) * 1 := mul_le_mul_of_nonneg_left hexp1 (by linarith)
        _ = 1 - δ := mul_one _
    have hρ1 : ρ ≤ 1 := by linarith
    have hrερ : (r : ℝ) * ε * ρ ≤ 1 / 8 := by
      calc (r : ℝ) * ε * ρ ≤ (r : ℝ) * ε * 1 := mul_le_mul_of_nonneg_left hρ1 (by positivity)
        _ ≤ 1 / 8 := by linarith
    have hexp_ge_half : 1 / 2 ≤ Real.exp (-(r : ℝ) * ε * ρ) := by
      have h1 : 1 - (r : ℝ) * ε * ρ ≤ Real.exp (-(r : ℝ) * ε * ρ) := by
        linarith [Real.add_one_le_exp (-(r : ℝ) * ε * ρ)]
      linarith
    have hLfac_pos : 0 < Real.exp (-(r : ℝ) * ε * ρ) - 2 * η := by
      have hε_small : ε ≤ 1 / 32 := by nlinarith only [hr4, hrε, hε0]
      have h2η : 2 * η ≤ 1 / 4 := by nlinarith only [hηε2, hε0, hε_small]
      linarith
    have hLfac_le1 : Real.exp (-(r : ℝ) * ε * ρ) - 2 * η ≤ 1 := by
      have h1 : Real.exp (-(r : ℝ) * ε * ρ) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (r : ℝ) * ε * ρ := by positivity
        linarith
      linarith
    have hCfac_pos : 0 < Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
        8 * (r : ℝ) * ε ^ 2 + 10 * η := by
      have h1 : 0 < Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) :=
        mul_pos (Real.exp_pos _) (by linarith)
      positivity
    have hD1 : 0 < D_t * Real.exp (-ε / 2) := mul_pos hDt (Real.exp_pos _)
    have hL1 : 0 < L_t * (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η) := mul_pos hLt hLfac_pos
    have hL1_hi : L_t * (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η) ≤ (1 + 1 / (r : ℝ)) * D := by
      calc L_t * (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η) ≤ L_t * 1 :=
            mul_le_mul_of_nonneg_left hLfac_le1 hLt.le
        _ = L_t := mul_one _
        _ ≤ (1 + 1 / (r : ℝ)) * D := hLt_hi
    have hC1 : 0 < C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
        8 * (r : ℝ) * ε ^ 2 + 10 * η) := mul_pos hCt hCfac_pos
    have hCD1 : C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
        8 * (r : ℝ) * ε ^ 2 + 10 * η) ≤ D_t * Real.exp (-ε / 2) := by
      have hexp1 : Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ ((r - 1 : ℕ) : ℝ) * ε * ρ := by positivity
        linarith
      have hfac : Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
          8 * (r : ℝ) * ε ^ 2 + 10 * η ≤ Real.exp (-ε / 2) := by
        have h1 : Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) ≤ 1 - ε := by
          calc _ ≤ 1 * (1 - ε) := mul_le_mul_of_nonneg_right hexp1 (by linarith)
            _ = 1 - ε := one_mul _
        have h2 : 1 - ε / 2 ≤ Real.exp (-ε / 2) := by
          linarith [Real.add_one_le_exp (-ε / 2)]
        linarith [h1, hdrift, h2]
      exact mul_le_mul hCD hfac hCfac_pos.le hDt.le
    have hρ_step : (C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
        8 * (r : ℝ) * ε ^ 2 + 10 * η)) / (L_t * (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η)) ≤
        ρ * Real.exp (-(δ / 2) * ε) := by
      have hrew : (C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
          8 * (r : ℝ) * ε ^ 2 + 10 * η)) / (L_t * (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η)) =
          ρ * ((Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
            8 * (r : ℝ) * ε ^ 2 + 10 * η) / (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η)) := by
        simp only [ρ]
        rw [mul_div_mul_comm]
      rw [hrew]
      apply mul_le_mul_of_nonneg_left _ hρ_pos.le
      rw [div_le_iff₀ hLfac_pos]
      have hexp_pos : 0 < Real.exp ((r : ℝ) * ε * ρ) := Real.exp_pos _
      suffices hmul :
          (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) + 8 * (r : ℝ) * ε ^ 2 + 10 * η) *
            Real.exp ((r : ℝ) * ε * ρ) ≤
          (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η) * Real.exp (-(δ / 2) * ε) *
            Real.exp ((r : ℝ) * ε * ρ) by
        rw [mul_comm (Real.exp (-(δ / 2) * ε))]
        exact le_of_mul_le_mul_right hmul hexp_pos
      have hr1_cast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
      have hcancel1 : Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * Real.exp ((r : ℝ) * ε * ρ) =
          Real.exp (ε * ρ) := by
        rw [← Real.exp_add, hr1_cast]; congr 1; ring
      have hcancel2 : Real.exp (-(r : ℝ) * ε * ρ) * Real.exp ((r : ℝ) * ε * ρ) = 1 := by
        rw [← Real.exp_add]; simp
      have hexp_r_le2 : Real.exp ((r : ℝ) * ε * ρ) ≤ 2 := by
        have h1 := exp_le_one_add_two_mul (by positivity : 0 ≤ (r : ℝ) * ε * ρ) (by linarith)
        linarith
      have hexp_ερ : Real.exp (ε * ρ) ≤ 1 + ε * ρ + 2 * ε ^ 2 := by
        have hερ_le : ε * ρ ≤ 1 / 2 := by nlinarith only [hε0, hε1, hρ_pos, hρ1]
        have h1 := exp_le_one_add_add_two_sq (by positivity : 0 ≤ ε * ρ) hερ_le
        have hsq : (ε * ρ) ^ 2 ≤ ε ^ 2 := by
          have : ε * ρ ≤ ε := by nlinarith only [hε0, hρ1]
          exact pow_le_pow_left₀ (by positivity) this 2
        linarith
      have hLHS : (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
            8 * (r : ℝ) * ε ^ 2 + 10 * η) * Real.exp ((r : ℝ) * ε * ρ) ≤
          1 - δ * ε + (16 * (r : ℝ) + 2) * ε ^ 2 + 20 * η := by
        have heq1 : (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
              8 * (r : ℝ) * ε ^ 2 + 10 * η) * Real.exp ((r : ℝ) * ε * ρ) =
            Real.exp (ε * ρ) * (1 - ε) +
              (8 * (r : ℝ) * ε ^ 2 + 10 * η) * Real.exp ((r : ℝ) * ε * ρ) := by
          rw [add_mul, add_mul, mul_right_comm, hcancel1]; ring
        rw [heq1]
        have hA : Real.exp (ε * ρ) * (1 - ε) ≤ (1 + ε * ρ + 2 * ε ^ 2) * (1 - ε) :=
          mul_le_mul_of_nonneg_right hexp_ερ (by linarith)
        have hB : (8 * (r : ℝ) * ε ^ 2 + 10 * η) * Real.exp ((r : ℝ) * ε * ρ) ≤
            (8 * (r : ℝ) * ε ^ 2 + 10 * η) * 2 :=
          mul_le_mul_of_nonneg_left hexp_r_le2 (by positivity)
        have hC : (1 + ε * ρ + 2 * ε ^ 2) * (1 - ε) ≤ 1 - δ * ε + 2 * ε ^ 2 := by
          have h1 : ε * δ ≤ ε * (1 - ρ) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
          have h2 : 0 ≤ ε ^ 2 * ρ + 2 * ε ^ 3 := by positivity
          nlinarith only [h1, h2]
        linarith [hA, hB, hC]
      have hRHS : 1 - (δ / 2) * ε - 4 * η ≤
          (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η) * Real.exp (-(δ / 2) * ε) *
            Real.exp ((r : ℝ) * ε * ρ) := by
        have heq2 : (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η) * Real.exp (-(δ / 2) * ε) *
              Real.exp ((r : ℝ) * ε * ρ) =
            (1 - 2 * η * Real.exp ((r : ℝ) * ε * ρ)) * Real.exp (-(δ / 2) * ε) := by
          rw [mul_right_comm, sub_mul, hcancel2]
        rw [heq2]
        have h1 : 1 - 4 * η ≤ 1 - 2 * η * Real.exp ((r : ℝ) * ε * ρ) := by
          have : 2 * η * Real.exp ((r : ℝ) * ε * ρ) ≤ 2 * η * 2 :=
            mul_le_mul_of_nonneg_left hexp_r_le2 (by positivity)
          linarith
        have h2 : 1 - (δ / 2) * ε ≤ Real.exp (-(δ / 2) * ε) := by
          linarith [Real.add_one_le_exp (-(δ / 2) * ε)]
        have h1_nn : 0 ≤ 1 - 4 * η := by nlinarith only [hηε2, hε0, hε1]
        have h2_nn : 0 ≤ 1 - (δ / 2) * ε := by nlinarith only [hδ0, hδ1, hε0, hε1]
        have hprod : (1 - 4 * η) * (1 - (δ / 2) * ε) ≤
            (1 - 2 * η * Real.exp ((r : ℝ) * ε * ρ)) * Real.exp (-(δ / 2) * ε) :=
          mul_le_mul h1 h2 h2_nn (by linarith)
        have hcross : 0 ≤ 4 * η * ((δ / 2) * ε) := by positivity
        linarith [hprod, hcross]
      have hgap : (16 * (r : ℝ) + 2) * ε ^ 2 + 24 * η ≤ (δ / 2) * ε := by
        have h1 : (16 * (r : ℝ) + 2) * ε ^ 2 + 24 * η ≤ (16 * (r : ℝ) + 26) * ε ^ 2 := by
          linarith [hηε2]
        have h2 : (16 * (r : ℝ) + 26) * ε ≤ δ / 2 := by
          have hM_eq : (M_param r : ℝ) = 200 * (r : ℝ) ^ 2 := by simp [M_param]
          simp only [ε, ε_val, δ, δ_val, hM_eq]
          rw [mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have hr2 : (16 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith only [hr4]
          nlinarith only [hr4, hr2]
        have h3 : (16 * (r : ℝ) + 26) * ε ^ 2 ≤ (δ / 2) * ε := by
          calc (16 * (r : ℝ) + 26) * ε ^ 2 = ((16 * (r : ℝ) + 26) * ε) * ε := by ring
            _ ≤ (δ / 2) * ε := mul_le_mul_of_nonneg_right h2 hε0.le
        linarith [h1, h3]
      linarith [hLHS, hRHS, hgap]
    have hρ_next : (C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε * ρ) * (1 - ε) +
        8 * (r : ℝ) * ε ^ 2 + 10 * η)) / (L_t * (Real.exp (-(r : ℝ) * ε * ρ) - 2 * η)) ≤
        (1 - δ) * Real.exp (-(δ / 2) * ((t + 1 : ℕ) : ℝ) * ε) := by
      calc _ ≤ ρ * Real.exp (-(δ / 2) * ε) := hρ_step
        _ ≤ ((1 - δ) * Real.exp (-(δ / 2) * (t : ℝ) * ε)) * Real.exp (-(δ / 2) * ε) :=
            mul_le_mul_of_nonneg_right hρ (Real.exp_pos _).le
        _ = (1 - δ) * Real.exp (-(δ / 2) * ((t + 1 : ℕ) : ℝ) * ε) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring
    exact ⟨hD1, hL1, hL1_hi, hC1, hCD1, hρ_next⟩

lemma geom_sum_mul_one_sub (q : ℝ) :
    ∀ t : ℕ, (1 - q) * ∑ j ∈ Finset.range t, q ^ j = 1 - q ^ t
  | 0 => by simp
  | t + 1 => by
    rw [Finset.sum_range_succ, mul_add, geom_sum_mul_one_sub q t, pow_succ]
    ring

lemma ode_L_C_lower {r : ℕ} (hr : 4 ≤ r) {D : ℝ} (hD : 0 < D) :
    ∀ t ≤ R_rounds r,
      D * Real.exp (-6 * (r : ℝ) ^ 2) ≤ (odeState r D t).2.1 ∧
      D * Real.exp (-24 * (r : ℝ) ^ 3) ≤ (odeState r D t).2.2 := by
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr2 : (16 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith only [hr4]
  have hpb := params_basic hr
  rcases hpb with ⟨hε0, hε1, hη0, hηε, hηε2, hrε, hRε, h8Rη, _⟩
  have hδ0 : 0 < δ_val r := by simp only [δ_val]; positivity
  have hδ1 : δ_val r ≤ 1 / 5 := by
    simp only [δ_val]; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hL_prod : ∀ t : ℕ,
      (1 + 1 / (r : ℝ)) * D *
        Real.exp (-(r : ℝ) * ε_val r *
          (∑ j ∈ Finset.range t, (odeState r D j).2.2 / (odeState r D j).2.1) -
          8 * (t : ℝ) * η_val r) ≤ (odeState r D t).2.1 := by
    intro t
    induction t with
    | zero => simp [odeState]
    | succ t ih =>
      have hst := ode_pos_and_ratio hr hD t
      set L_t := (odeState r D t).2.1
      set C_t := (odeState r D t).2.2
      set ρ_t := C_t / L_t
      have hρ_le1 : ρ_t ≤ 1 := by
        have hexp1 : Real.exp (-(δ_val r / 2) * (t : ℝ) * ε_val r) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ (δ_val r / 2) * (t : ℝ) * ε_val r := by positivity
          linarith
        have h1 : ρ_t ≤ (1 - δ_val r) * 1 := hst.2.2.2.2.2.trans
          (mul_le_mul_of_nonneg_left hexp1 (by linarith))
        linarith
      have hρ_nn : 0 ≤ ρ_t := div_nonneg hst.2.2.2.1.le hst.2.1.le
      have hstep : Real.exp (-(r : ℝ) * ε_val r * ρ_t - 8 * η_val r) ≤
          Real.exp (-(r : ℝ) * ε_val r * ρ_t) - 2 * η_val r := by
        rw [sub_eq_add_neg, Real.exp_add]
        have hexp_half : 1 / 2 ≤ Real.exp (-(r : ℝ) * ε_val r * ρ_t) := by
          have h1 : 1 - (r : ℝ) * ε_val r * ρ_t ≤ Real.exp (-(r : ℝ) * ε_val r * ρ_t) := by
            linarith [Real.add_one_le_exp (-(r : ℝ) * ε_val r * ρ_t)]
          have h2 : (r : ℝ) * ε_val r * ρ_t ≤ 1 / 8 := by
            calc _ ≤ (r : ℝ) * ε_val r * 1 := mul_le_mul_of_nonneg_left hρ_le1 (by positivity)
              _ ≤ 1 / 8 := by linarith
          linarith
        have h8η_le : 8 * η_val r ≤ 1 / 2 := by
          have hM_ge : (3200 : ℝ) ≤ (M_param r : ℝ) := by
            have : (M_param r : ℝ) = 200 * (r : ℝ) ^ 2 := by simp [M_param]
            linarith
          have hε_small : ε_val r ≤ 1 / 3200 := by
            simp only [ε_val]; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
          nlinarith only [hηε2, hε0, hε_small]
        have hneg := exp_neg_le_one_sub_add_sq (by positivity : 0 ≤ 8 * η_val r)
        have hdiff : 4 * η_val r ≤ 1 - Real.exp (-(8 * η_val r)) := by
          nlinarith only [hneg, h8η_le, hη0]
        have hprod : 2 * η_val r ≤
            Real.exp (-(r : ℝ) * ε_val r * ρ_t) * (1 - Real.exp (-(8 * η_val r))) := by
          calc 2 * η_val r = (1 / 2) * (4 * η_val r) := by ring
            _ ≤ Real.exp (-(r : ℝ) * ε_val r * ρ_t) * (1 - Real.exp (-(8 * η_val r))) :=
                mul_le_mul hexp_half hdiff (by positivity) (Real.exp_pos _).le
        linarith
      simp only [odeState]
      calc (1 + 1 / (r : ℝ)) * D *
            Real.exp (-(r : ℝ) * ε_val r *
              (∑ j ∈ Finset.range (t + 1), (odeState r D j).2.2 / (odeState r D j).2.1) -
              8 * ((t + 1 : ℕ) : ℝ) * η_val r)
          = ((1 + 1 / (r : ℝ)) * D *
              Real.exp (-(r : ℝ) * ε_val r *
                (∑ j ∈ Finset.range t, (odeState r D j).2.2 / (odeState r D j).2.1) -
                8 * (t : ℝ) * η_val r)) *
            Real.exp (-(r : ℝ) * ε_val r * ρ_t - 8 * η_val r) := by
              symm
              rw [mul_assoc ((1 + 1 / (r : ℝ)) * D), ← Real.exp_add, Finset.sum_range_succ]
              congr 2; push_cast; ring
        _ ≤ L_t * (Real.exp (-(r : ℝ) * ε_val r * ρ_t) - 2 * η_val r) :=
            mul_le_mul ih hstep (Real.exp_pos _).le hst.2.1.le
  have hC_prod : ∀ t : ℕ,
      D * Real.exp (-(t : ℝ) * ((r : ℝ) + 2) * ε_val r) ≤ (odeState r D t).2.2 := by
    intro t
    induction t with
    | zero => simp [odeState]
    | succ t ih =>
      have hst := ode_pos_and_ratio hr hD t
      set L_t := (odeState r D t).2.1
      set C_t := (odeState r D t).2.2
      set ρ_t := C_t / L_t
      have hρ_le1 : ρ_t ≤ 1 := by
        have hexp1 : Real.exp (-(δ_val r / 2) * (t : ℝ) * ε_val r) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ (δ_val r / 2) * (t : ℝ) * ε_val r := by positivity
          linarith
        have h1 : ρ_t ≤ (1 - δ_val r) * 1 := hst.2.2.2.2.2.trans
          (mul_le_mul_of_nonneg_left hexp1 (by linarith))
        linarith
      have hstep : Real.exp (-((r : ℝ) + 2) * ε_val r) ≤
          Real.exp (-((r - 1 : ℕ) : ℝ) * ε_val r * ρ_t) * (1 - ε_val r) +
            8 * (r : ℝ) * (ε_val r) ^ 2 + 10 * η_val r := by
        have h1 : Real.exp (-(r : ℝ) * ε_val r) ≤ Real.exp (-((r - 1 : ℕ) : ℝ) * ε_val r * ρ_t) := by
          rw [Real.exp_le_exp]
          have hrm : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr (Nat.sub_le r 1)
          have hprod : ((r - 1 : ℕ) : ℝ) * ε_val r * ρ_t ≤ (r : ℝ) * ε_val r := by
            calc _ ≤ ((r - 1 : ℕ) : ℝ) * ε_val r * 1 :=
                  mul_le_mul_of_nonneg_left hρ_le1 (by positivity)
              _ = ((r - 1 : ℕ) : ℝ) * ε_val r := mul_one _
              _ ≤ (r : ℝ) * ε_val r := mul_le_mul_of_nonneg_right hrm hε0.le
          linarith
        have h2 : Real.exp (-2 * ε_val r) ≤ 1 - ε_val r := by
          have ha : 1 + 2 * ε_val r ≤ Real.exp (2 * ε_val r) := by
            linarith [Real.add_one_le_exp (2 * ε_val r)]
          have hb : 1 ≤ (1 + 2 * ε_val r) * (1 - ε_val r) := by nlinarith only [hε0, hε1]
          have hc : 1 ≤ Real.exp (2 * ε_val r) * (1 - ε_val r) :=
            hb.trans (mul_le_mul_of_nonneg_right ha (by linarith))
          have hd := mul_le_mul_of_nonneg_left hc (Real.exp_pos (-2 * ε_val r)).le
          rw [mul_one, ← mul_assoc, ← Real.exp_add] at hd
          have hz : -2 * ε_val r + 2 * ε_val r = 0 := by ring
          rw [hz, Real.exp_zero, one_mul] at hd
          exact hd
        have h3 : Real.exp (-((r : ℝ) + 2) * ε_val r) ≤
            Real.exp (-((r - 1 : ℕ) : ℝ) * ε_val r * ρ_t) * (1 - ε_val r) := by
          have heq : Real.exp (-((r : ℝ) + 2) * ε_val r) =
              Real.exp (-(r : ℝ) * ε_val r) * Real.exp (-2 * ε_val r) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [heq]
          exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
        have hpos_add : 0 ≤ 8 * (r : ℝ) * (ε_val r) ^ 2 + 10 * η_val r := by positivity
        linarith [h3, hpos_add]
      simp only [odeState]
      calc D * Real.exp (-((t + 1 : ℕ) : ℝ) * ((r : ℝ) + 2) * ε_val r)
          = (D * Real.exp (-(t : ℝ) * ((r : ℝ) + 2) * ε_val r)) *
              Real.exp (-((r : ℝ) + 2) * ε_val r) := by
            symm
            rw [mul_assoc D, ← Real.exp_add]; congr 2; push_cast; ring
        _ ≤ C_t * (Real.exp (-((r - 1 : ℕ) : ℝ) * ε_val r * ρ_t) * (1 - ε_val r) +
              8 * (r : ℝ) * (ε_val r) ^ 2 + 10 * η_val r) :=
            mul_le_mul ih hstep (Real.exp_pos _).le hst.2.2.2.1.le
  intro t htR
  constructor
  · let α : ℝ := (δ_val r / 2) * ε_val r
    have hα0 : 0 < α := by positivity
    have hα_half : α ≤ 1 / 2 := by dsimp only [α]; nlinarith only [hδ0, hδ1, hε0, hε1]
    have hsum_ρ : ∑ j ∈ Finset.range t, (odeState r D j).2.2 / (odeState r D j).2.1 ≤
        2 / α := by
      have hterm : ∀ j ∈ Finset.range t,
          (odeState r D j).2.2 / (odeState r D j).2.1 ≤ (Real.exp (-α)) ^ j := fun j _ => by
        have h1 := (ode_pos_and_ratio hr hD j).2.2.2.2.2
        have heq : Real.exp (-(δ_val r / 2) * (j : ℝ) * ε_val r) = (Real.exp (-α)) ^ j := by
          rw [← Real.exp_nat_mul]; congr 1; simp only [α]; ring
        rw [heq] at h1
        exact h1.trans (mul_le_of_le_one_left (pow_nonneg (Real.exp_pos _).le j) (by linarith))
      have hsum1 : ∑ j ∈ Finset.range t, (odeState r D j).2.2 / (odeState r D j).2.1 ≤
          ∑ j ∈ Finset.range t, (Real.exp (-α)) ^ j := Finset.sum_le_sum hterm
      have h1sub : α / 2 ≤ 1 - Real.exp (-α) := by
        have hneg := exp_neg_le_one_sub_add_sq hα0.le
        nlinarith only [hneg, hα_half, hα0]
      have hgeom := geom_sum_mul_one_sub (Real.exp (-α)) t
      have hle1 : (1 - Real.exp (-α)) * ∑ j ∈ Finset.range t, (Real.exp (-α)) ^ j ≤ 1 := by
        rw [hgeom]; linarith [pow_nonneg (Real.exp_pos (-α)).le t]
      have hsum2 : ∑ j ∈ Finset.range t, (Real.exp (-α)) ^ j ≤ 2 / α := by
        rw [le_div_iff₀ hα0]
        have hnn : 0 ≤ ∑ j ∈ Finset.range t, (Real.exp (-α)) ^ j :=
          Finset.sum_nonneg fun j _ => pow_nonneg (Real.exp_pos _).le j
        have hmul := mul_le_mul_of_nonneg_right h1sub hnn
        linarith [hmul, hle1]
      exact hsum1.trans hsum2
    have hmul_sum : (r : ℝ) * ε_val r *
        (∑ j ∈ Finset.range t, (odeState r D j).2.2 / (odeState r D j).2.1) ≤
        4 * (r : ℝ) * ((r : ℝ) + 1) := by
      have h1 : (r : ℝ) * ε_val r * (2 / α) = 4 * (r : ℝ) * ((r : ℝ) + 1) := by
        simp only [α, δ_val]; field_simp; ring
      calc _ ≤ (r : ℝ) * ε_val r * (2 / α) := mul_le_mul_of_nonneg_left hsum_ρ (by positivity)
        _ = 4 * (r : ℝ) * ((r : ℝ) + 1) := h1
    have h8tη : 8 * (t : ℝ) * η_val r ≤ 1 := by
      have htR' : (t : ℝ) ≤ (R_rounds r : ℝ) := Nat.cast_le.mpr htR
      calc 8 * (t : ℝ) * η_val r ≤ 8 * (R_rounds r : ℝ) * η_val r := by nlinarith only [htR', hη0]
        _ ≤ 1 := h8Rη
    have hexp_le : -6 * (r : ℝ) ^ 2 ≤
        -(r : ℝ) * ε_val r *
          (∑ j ∈ Finset.range t, (odeState r D j).2.2 / (odeState r D j).2.1) -
          8 * (t : ℝ) * η_val r := by
      nlinarith only [hmul_sum, h8tη, hr4, hr2]
    have hD_le_L0 : D ≤ (1 + 1 / (r : ℝ)) * D := by
      have : 0 ≤ 1 / (r : ℝ) * D := by positivity
      linarith
    calc D * Real.exp (-6 * (r : ℝ) ^ 2)
        ≤ ((1 + 1 / (r : ℝ)) * D) *
            Real.exp (-(r : ℝ) * ε_val r *
              (∑ j ∈ Finset.range t, (odeState r D j).2.2 / (odeState r D j).2.1) -
              8 * (t : ℝ) * η_val r) :=
          mul_le_mul hD_le_L0 (Real.exp_le_exp.mpr hexp_le) (Real.exp_pos _).le (by positivity)
      _ ≤ (odeState r D t).2.1 := hL_prod t
  · have htR' : (t : ℝ) ≤ (R_rounds r : ℝ) := Nat.cast_le.mpr htR
    have hexp_le : -24 * (r : ℝ) ^ 3 ≤ -(t : ℝ) * ((r : ℝ) + 2) * ε_val r := by
      have h1 : (t : ℝ) * ((r : ℝ) + 2) * ε_val r ≤ (R_rounds r : ℝ) * ((r : ℝ) + 2) * ε_val r := by
        have : 0 ≤ ((r : ℝ) + 2) * ε_val r := by positivity
        nlinarith only [htR', this]
      have h2 : (R_rounds r : ℝ) * ((r : ℝ) + 2) * ε_val r = 16 * (r : ℝ) ^ 2 * ((r : ℝ) + 2) := by
        calc _ = ((R_rounds r : ℝ) * ε_val r) * ((r : ℝ) + 2) := by ring
          _ = 16 * (r : ℝ) ^ 2 * ((r : ℝ) + 2) := by rw [hRε]
      have h3 : 16 * (r : ℝ) ^ 2 * ((r : ℝ) + 2) ≤ 24 * (r : ℝ) ^ 3 := by
        have : (r : ℝ) + 2 ≤ 3 / 2 * (r : ℝ) := by linarith
        nlinarith only [this, hr2]
      linarith [h1, h2, h3]
    calc D * Real.exp (-24 * (r : ℝ) ^ 3)
        ≤ D * Real.exp (-(t : ℝ) * ((r : ℝ) + 2) * ε_val r) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) hD.le
      _ ≤ (odeState r D t).2.2 := hC_prod t

/-- Multi-round uniform list edge-coloring theorem for `r ≥ 4`. -/
theorem uniform_list_coloring (r : ℕ) (hr : 4 ≤ r) :
    ∃ D₀ : ℕ, ∀ n D m : ℕ, D₀ ≤ D → 0 < m →
      ∀ (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
        (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
        (∀ A ∈ K, A.card = r) →
        (∀ i, (K.filter (fun A => i ∈ A)).card ≤ D) →
        (∀ A ∈ K, (1 + 1 / (r : ℝ)) * (D : ℝ) ≤ ((L A).card : ℝ)) →
        ∃ c : Finset (Fin n) → Fin m,
          (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ K, c A ∈ L A := by
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr2 : (16 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith only [hr4]
  have hr3 : (64 : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith only [hr4, hr2]
  have hpb := params_basic hr
  rcases hpb with ⟨hε0, hε1, hη0, hηε, hηε2, hrε, hRε, _, hdrift⟩
  let c_exp : ℝ := (η_val r) ^ 2 / (32 * (r : ℝ) ^ 3 * ε_val r)
  let γ_C : ℝ := Real.exp (-24 * (r : ℝ) ^ 3)
  let γ_L : ℝ := Real.exp (-6 * (r : ℝ) ^ 2)
  have hc_pos : 0 < c_exp := by positivity
  have hγC_pos : 0 < γ_C := Real.exp_pos _
  have hγL_pos : 0 < γ_L := Real.exp_pos _
  let B_thresh : ℝ := max (max 2 (max (2 / γ_C) ((8 / η_val r) / γ_L)))
    (36 * 720 * 9000 * (r : ℝ) ^ 3 / (c_exp * γ_C) ^ 6)
  refine ⟨Nat.ceil B_thresh + 1, fun n D m hD hm K L hlin hunif hdeg hL => ?_⟩
  have hD_ge_B : B_thresh ≤ (D : ℝ) := by
    have h1 : (Nat.ceil B_thresh : ℝ) ≤ (D : ℝ) := by
      have : Nat.ceil B_thresh ≤ D := by omega
      exact_mod_cast this
    exact (Nat.le_ceil B_thresh).trans h1
  have hD_ge2 : (2 : ℝ) ≤ (D : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_left _ _)).trans hD_ge_B
  have hD_pos : (0 : ℝ) < (D : ℝ) := by linarith
  have hD_C : 2 / γ_C ≤ (D : ℝ) :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)).trans hD_ge_B
  have hD_L : (8 / η_val r) / γ_L ≤ (D : ℝ) :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)).trans hD_ge_B
  have hD_LLL : 36 * 720 * 9000 * (r : ℝ) ^ 3 / (c_exp * γ_C) ^ 6 ≤ (D : ℝ) :=
    (le_max_right _ _).trans hD_ge_B
  have hiter : ∀ t ≤ R_rounds r,
      ∃ (K_t : Finset (Finset (Fin n))) (L_t : Finset (Fin n) → Finset (Fin m))
        (c_t : Finset (Fin n) → Fin m),
        K_t ⊆ K ∧
        (∀ A ∈ K \ K_t, c_t A ∈ L A) ∧
        (∀ A ∈ K \ K_t, ∀ B ∈ K \ K_t, A ≠ B → (A ∩ B).Nonempty → c_t A ≠ c_t B) ∧
        (∀ A ∈ K_t, L_t A ⊆ L A) ∧
        (∀ A ∈ K_t, ∀ B ∈ K \ K_t, (A ∩ B).Nonempty → c_t B ∉ L_t A) ∧
        (∀ x, ((K_t.filter (fun A => x ∈ A)).card : ℝ) ≤ (odeState r (D : ℝ) t).1) ∧
        (∀ A ∈ K_t, (odeState r (D : ℝ) t).2.1 ≤ ((L_t A).card : ℝ)) ∧
        (∀ x c, ((K_t.filter (fun A => x ∈ A ∧ c ∈ L_t A)).card : ℝ) ≤
          (odeState r (D : ℝ) t).2.2) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨K, L, fun _ => ⟨0, hm⟩, Subset.rfl, ?_, ?_, fun _ _ => Subset.rfl, ?_, ?_, ?_, ?_⟩
      · intro A hA; simp at hA
      · intro A hA; simp at hA
      · intro _ _ B hB; simp at hB
      · intro x; simp only [odeState]; exact_mod_cast hdeg x
      · intro A hA; simp only [odeState]; exact hL A hA
      · intro x c
        simp only [odeState]
        have hsub : K.filter (fun A => x ∈ A ∧ c ∈ L A) ⊆ K.filter (fun A => x ∈ A) :=
          fun A hA => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1, (Finset.mem_filter.mp hA).2.1⟩
        exact_mod_cast (Finset.card_le_card hsub).trans (hdeg x)
    | succ t ih =>
      intro ht1
      have ht : t ≤ R_rounds r := Nat.le_of_succ_le ht1
      obtain ⟨K_t, L_t, c_t, hsubK, hc_L, hc_prop, hL_sub, hfree, hD_inv, hL_inv, hC_inv⟩ := ih ht
      have hst := ode_pos_and_ratio hr hD_pos t
      have hlo := ode_L_C_lower hr hD_pos t ht
      set D_s := (odeState r (D : ℝ) t).1
      set L_s := (odeState r (D : ℝ) t).2.1
      set C_s := (odeState r (D : ℝ) t).2.2
      have hCL_s : C_s ≤ L_s := by
        have hδ0 : 0 < δ_val r := by simp only [δ_val]; positivity
        have hexp1 : Real.exp (-(δ_val r / 2) * (t : ℝ) * ε_val r) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ (δ_val r / 2) * (t : ℝ) * ε_val r := by positivity
          linarith
        have h1 : C_s / L_s ≤ 1 := by
          have h2 := hst.2.2.2.2.2
          have h3 : (1 - δ_val r) * Real.exp (-(δ_val r / 2) * (t : ℝ) * ε_val r) ≤ 1 := by
            calc _ ≤ (1 - δ_val r) * 1 :=
                  mul_le_mul_of_nonneg_left hexp1 (by
                    simp only [δ_val]; rw [sub_nonneg, div_le_one (by linarith)]; linarith)
              _ ≤ 1 := by linarith
          exact h2.trans h3
        exact (div_le_one hst.2.1).mp h1
      have hC_ge2 : 2 ≤ C_s := by
        have h1 : 2 ≤ (D : ℝ) * γ_C := by
          have := mul_le_mul_of_nonneg_right hD_C hγC_pos.le
          have hc : 2 / γ_C * γ_C = 2 := by field_simp
          linarith
        exact h1.trans hlo.2
      have hL_ge_big : 8 / η_val r ≤ L_s := by
        have h1 : 8 / η_val r ≤ (D : ℝ) * γ_L := by
          have := mul_le_mul_of_nonneg_right hD_L hγL_pos.le
          have hc : (8 / η_val r) / γ_L * γ_L = 8 / η_val r := by field_simp
          linarith
        exact h1.trans hlo.1
      have hD_le_D : D_s ≤ (D : ℝ) := by
        rw [show D_s = (D : ℝ) * Real.exp (-(t : ℝ) * ε_val r / 2) from ode_D_eq r (D : ℝ) t]
        have hexp1 : Real.exp (-(t : ℝ) * ε_val r / 2) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ (t : ℝ) * ε_val r / 2 := by positivity
          linarith
        calc (D : ℝ) * Real.exp (-(t : ℝ) * ε_val r / 2) ≤ (D : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hexp1 hD_pos.le
          _ = (D : ℝ) := mul_one _
      have hL_le_2D : L_s ≤ 2 * (D : ℝ) := by
        have h1 : 1 + 1 / (r : ℝ) ≤ 2 := by
          have : 1 / (r : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
          linarith
        exact hst.2.2.1.trans (mul_le_mul_of_nonneg_right h1 hD_pos.le)
      have hLLL_s : 36 * Real.exp (-(η_val r ^ 2 / (32 * (r : ℝ) ^ 3 * ε_val r)) * C_s) *
          ((8 * r ^ 3 * (Nat.floor D_s + Nat.floor L_s + 1) ^ 5 : ℕ) + 1 : ℝ) ≤ 1 := by
        have hfl_sum : ((Nat.floor D_s + Nat.floor L_s + 1 : ℕ) : ℝ) ≤ 4 * (D : ℝ) := by
          push_cast
          have h1 : (Nat.floor D_s : ℝ) ≤ D_s := Nat.floor_le hst.1.le
          have h2 : (Nat.floor L_s : ℝ) ≤ L_s := Nat.floor_le hst.2.1.le
          linarith [h1, h2, hD_le_D, hL_le_2D, hD_ge2]
        have hdeg_le : ((8 * r ^ 3 * (Nat.floor D_s + Nat.floor L_s + 1) ^ 5 : ℕ) + 1 : ℝ) ≤
            9000 * (r : ℝ) ^ 3 * (D : ℝ) ^ 5 := by
          push_cast
          have hpow5 : ((Nat.floor D_s : ℝ) + (Nat.floor L_s : ℝ) + 1) ^ 5 ≤
              (4 * (D : ℝ)) ^ 5 := by
            have h1 : (Nat.floor D_s : ℝ) + (Nat.floor L_s : ℝ) + 1 ≤ 4 * (D : ℝ) := by
              simpa using hfl_sum
            exact pow_le_pow_left₀ (by positivity) h1 5
          have h1 : 8 * (r : ℝ) ^ 3 * ((Nat.floor D_s : ℝ) + (Nat.floor L_s : ℝ) + 1) ^ 5 ≤
              8 * (r : ℝ) ^ 3 * (4 * (D : ℝ)) ^ 5 :=
            mul_le_mul_of_nonneg_left hpow5 (by positivity)
          have h2 : (1 : ℝ) ≤ (r : ℝ) ^ 3 * (D : ℝ) ^ 5 := by
            have hD5 : (1 : ℝ) ≤ (D : ℝ) ^ 5 := one_le_pow₀ (by linarith)
            nlinarith only [hr3, hD5]
          have h45 : (4 * (D : ℝ)) ^ 5 = 1024 * (D : ℝ) ^ 5 := by ring
          nlinarith only [h1, h2, h45]
        have hexp_inv : Real.exp (-(c_exp * C_s)) ≤
            720 / ((c_exp * γ_C * (D : ℝ)) ^ 6) := by
          have harg : c_exp * γ_C * (D : ℝ) ≤ c_exp * C_s := by
            calc c_exp * γ_C * (D : ℝ) = c_exp * ((D : ℝ) * γ_C) := by ring
              _ ≤ c_exp * C_s := mul_le_mul_of_nonneg_left hlo.2 hc_pos.le
          have hge : (c_exp * γ_C * (D : ℝ)) ^ 6 / 720 ≤ Real.exp (c_exp * C_s) :=
            (exp_ge_pow_six_div (by positivity)).trans (Real.exp_le_exp.mpr harg)
          rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
          linarith [show (c_exp * γ_C * (D : ℝ)) ^ 6 ≤ 720 * Real.exp (c_exp * C_s) by
            have := mul_le_mul_of_nonneg_left hge (by norm_num : (0 : ℝ) ≤ 720)
            linarith]
        have hfinal : 36 * (720 / ((c_exp * γ_C * (D : ℝ)) ^ 6)) *
            (9000 * (r : ℝ) ^ 3 * (D : ℝ) ^ 5) ≤ 1 := by
          have heq : 36 * (720 / ((c_exp * γ_C * (D : ℝ)) ^ 6)) *
              (9000 * (r : ℝ) ^ 3 * (D : ℝ) ^ 5) =
              (36 * 720 * 9000 * (r : ℝ) ^ 3 / (c_exp * γ_C) ^ 6) / (D : ℝ) := by
            field_simp
          rw [heq, div_le_one hD_pos]
          exact hD_LLL
        calc 36 * Real.exp (-(η_val r ^ 2 / (32 * (r : ℝ) ^ 3 * ε_val r)) * C_s) *
              ((8 * r ^ 3 * (Nat.floor D_s + Nat.floor L_s + 1) ^ 5 : ℕ) + 1 : ℝ)
            = 36 * Real.exp (-(c_exp * C_s)) *
                ((8 * r ^ 3 * (Nat.floor D_s + Nat.floor L_s + 1) ^ 5 : ℕ) + 1 : ℝ) := by
              simp only [c_exp]; congr 3; ring
          _ ≤ 36 * (720 / ((c_exp * γ_C * (D : ℝ)) ^ 6)) *
                (9000 * (r : ℝ) ^ 3 * (D : ℝ) ^ 5) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hexp_inv (by positivity)) hdeg_le
                (by positivity) (by positivity)
          _ ≤ 1 := hfinal
      obtain ⟨K_next, L_next, col_step, hsub_t, hcs_L, hcs_prop, hLn_sub, hLn_free,
        hDn_inv, hLn_inv, hCn_inv⟩ := list_nibble_round hr hm K_t L_t
          (fun E hE => hunif E (hsubK hE))
          (fun E hE F hF => hlin E (hsubK hE) F (hsubK hF))
          (ε_val r) (η_val r) D_s L_s C_s
          hε0 hε1 hη0 hηε hηε2 hrε hst.2.2.2.1 hst.2.2.2.2.1 hCL_s hC_ge2 hL_ge_big
          hD_inv hL_inv hC_inv hLLL_s
      refine ⟨K_next, L_next, fun A => if A ∈ K_t then col_step A else c_t A,
        hsub_t.trans hsubK, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A hA
        rcases Finset.mem_sdiff.mp hA with ⟨hAK, hAnext⟩
        by_cases hAt : A ∈ K_t
        · simpa only [if_pos hAt] using hL_sub A hAt (hcs_L A (Finset.mem_sdiff.mpr ⟨hAt, hAnext⟩))
        · simpa only [if_neg hAt] using hc_L A (Finset.mem_sdiff.mpr ⟨hAK, hAt⟩)
      · intro A hA B hB hAB hinter
        rcases Finset.mem_sdiff.mp hA with ⟨hAK, hAnext⟩
        rcases Finset.mem_sdiff.mp hB with ⟨hBK, hBnext⟩
        by_cases hAt : A ∈ K_t <;> by_cases hBt : B ∈ K_t <;>
          simp only [hAt, hBt, if_true, if_false]
        · exact hcs_prop A (Finset.mem_sdiff.mpr ⟨hAt, hAnext⟩)
            B (Finset.mem_sdiff.mpr ⟨hBt, hBnext⟩) hAB hinter
        · intro heq
          have hmem := hcs_L A (Finset.mem_sdiff.mpr ⟨hAt, hAnext⟩)
          exact hfree A hAt B (Finset.mem_sdiff.mpr ⟨hBK, hBt⟩) hinter (heq ▸ hmem)
        · intro heq
          have hmem := hcs_L B (Finset.mem_sdiff.mpr ⟨hBt, hBnext⟩)
          have hi' : (B ∩ A).Nonempty := by simpa only [Finset.inter_comm] using hinter
          exact hfree B hBt A (Finset.mem_sdiff.mpr ⟨hAK, hAt⟩) hi' (heq.symm ▸ hmem)
        · exact hc_prop A (Finset.mem_sdiff.mpr ⟨hAK, hAt⟩)
            B (Finset.mem_sdiff.mpr ⟨hBK, hBt⟩) hAB hinter
      · intro A hA
        exact (hLn_sub A hA).trans (hL_sub A (hsub_t hA))
      · intro A hA B hB hinter
        rcases Finset.mem_sdiff.mp hB with ⟨hBK, hBnext⟩
        by_cases hBt : B ∈ K_t
        · simpa only [if_pos hBt] using
            hLn_free A hA B (Finset.mem_sdiff.mpr ⟨hBt, hBnext⟩) hinter
        · simpa only [if_neg hBt] using fun hmem =>
            hfree A (hsub_t hA) B (Finset.mem_sdiff.mpr ⟨hBK, hBt⟩) hinter (hLn_sub A hA hmem)
      · intro x
        simp only [odeState]
        have h1 : 1 - ε_val r + 8 * (r : ℝ) * (ε_val r) ^ 2 + 8 * η_val r ≤
            Real.exp (-ε_val r / 2) := by
          have ha : 1 - ε_val r / 2 ≤ Real.exp (-ε_val r / 2) := by
            linarith [Real.add_one_le_exp (-ε_val r / 2)]
          linarith [hdrift, hη0, ha]
        exact (hDn_inv x).trans (mul_le_mul_of_nonneg_left h1 hst.1.le)
      · intro A hA
        simp only [odeState]
        exact hLn_inv A hA
      · intro x c
        simp only [odeState]
        exact hCn_inv x c
  -- Finish greedily after `R_rounds r` rounds.
  obtain ⟨K_R, L_R, c_R, hsubK, hc_L, hc_prop, hL_sub, hfree, hD_inv, hL_inv, _⟩ :=
    hiter (R_rounds r) le_rfl
  let d_R : ℕ := Nat.floor (odeState r (D : ℝ) (R_rounds r)).1
  have hd_deg : ∀ v, (K_R.filter (fun A => v ∈ A)).card ≤ d_R :=
    fun v => Nat.le_floor (hD_inv v)
  have hD_R_eq : (odeState r (D : ℝ) (R_rounds r)).1 = (D : ℝ) * Real.exp (-8 * (r : ℝ) ^ 2) := by
    rw [ode_D_eq, show -(R_rounds r : ℝ) * ε_val r / 2 = -8 * (r : ℝ) ^ 2 by
      have : (R_rounds r : ℝ) * ε_val r = 16 * (r : ℝ) ^ 2 := hRε
      linarith]
  have hL_R_lo : (D : ℝ) * Real.exp (-6 * (r : ℝ) ^ 2) ≤
      (odeState r (D : ℝ) (R_rounds r)).2.1 := (ode_L_C_lower hr hD_pos (R_rounds r) le_rfl).1
  have hr_lt_exp : (r : ℝ) < Real.exp (2 * (r : ℝ) ^ 2) := by
    have h1 : 1 + 2 * (r : ℝ) ^ 2 ≤ Real.exp (2 * (r : ℝ) ^ 2) := by
      linarith [Real.add_one_le_exp (2 * (r : ℝ) ^ 2)]
    nlinarith only [h1, hr4, hr2]
  have hgap_R : (r : ℝ) * (d_R : ℝ) < (odeState r (D : ℝ) (R_rounds r)).2.1 := by
    have hd_le : (d_R : ℝ) ≤ (D : ℝ) * Real.exp (-8 * (r : ℝ) ^ 2) := by
      rw [← hD_R_eq]; exact Nat.floor_le (ode_pos_and_ratio hr hD_pos (R_rounds r)).1.le
    have hmul : (r : ℝ) * ((D : ℝ) * Real.exp (-8 * (r : ℝ) ^ 2)) <
        (D : ℝ) * Real.exp (-6 * (r : ℝ) ^ 2) := by
      have heq : (D : ℝ) * Real.exp (-6 * (r : ℝ) ^ 2) =
          Real.exp (2 * (r : ℝ) ^ 2) * ((D : ℝ) * Real.exp (-8 * (r : ℝ) ^ 2)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      rw [heq]
      exact mul_lt_mul_of_pos_right hr_lt_exp (mul_pos hD_pos (Real.exp_pos _))
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hd_le (by linarith))
      (lt_of_lt_of_le hmul hL_R_lo)
  exact finish_with_reserve hm K K_R L L_R c_R hc_prop hc_L
    (fun A hA => (hunif A (hsubK hA)).le) hd_deg
    (fun A hA => ⟨by
      have h1 : ((r * (d_R - 1) : ℕ) : ℝ) < ((L_R A).card : ℝ) := by
        have hsub : ((r * (d_R - 1) : ℕ) : ℝ) ≤ (r : ℝ) * (d_R : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left r (Nat.sub_le d_R 1)
        exact lt_of_le_of_lt hsub (lt_of_lt_of_le hgap_R (hL_inv A hA))
      exact_mod_cast h1, hL_sub A hA⟩)
    hfree

end UniformListColoring

/- ### Section 5: Rank-2 Case, Uniform Padding, and `OMA.solution` -/

section FinalReduction

/-- The case `q = 1` (rank at most 2): greedy works with lists of size `2 * D`. -/
lemma case_one : ∃ D₀ : ℕ, ∀ n D m : ℕ, D₀ ≤ D → 0 < m →
    ∀ (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ 2 * 1) →
      (∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) → (∀ A ∈ H, D + D / 1 ≤ (L A).card) →
      ∃ c : Finset (Fin n) → Fin m,
        (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A := by
  refine ⟨1, fun n D m hD hm H L _ hsize hdeg hL => greedy H L hm ?_⟩
  intro A hA
  have h1 := nbhd_le H D A hA hdeg
  have h2 := hsize A hA
  have h3 := hL A hA
  rw [Nat.div_one] at h3
  have h4 : A.card * (D - 1) ≤ 2 * (D - 1) := Nat.mul_le_mul_right _ h2.2
  omega

/-- Pad every edge of rank `≤ r` with fresh private vertices to obtain an `r`-uniform linear
hypergraph of maximum degree at most `D`. -/
lemma padding {V : Type} [Fintype V] [DecidableEq V] (r D : ℕ) (hD : 0 < D)
    (H : Finset (Finset V))
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (hrank : ∀ A ∈ H, A.card ≤ r)
    (hdeg : ∀ v, (H.filter (fun A => v ∈ A)).card ≤ D) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (f : V ↪ W)
      (g : Finset V ↪ Finset W) (K : Finset (Finset W)),
      K = H.map g ∧
      (∀ A v, f v ∈ g A ↔ v ∈ A) ∧
      (∀ A ∈ K, A.card = r) ∧
      (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) ∧
      ∀ v, (K.filter (fun A => v ∈ A)).card ≤ D := by
  let W := V ⊕ (Finset V × Fin r)
  let f : V ↪ W := ⟨Sum.inl, Sum.inl_injective⟩
  let pad (A : Finset V) : Finset W :=
    A.map f ∪ (Finset.univ.filter fun i : Fin r => i.val < r - A.card).image (fun i => Sum.inr (A, i))
  have hin (A : Finset V) (v : V) : f v ∈ pad A ↔ v ∈ A := by simp [pad, f]
  have hout (A B : Finset V) (i : Fin r) :
      Sum.inr (B, i) ∈ pad A ↔ B = A ∧ i.val < r - A.card := by
    simp [pad, f, eq_comm, and_comm]
  let g : Finset V ↪ Finset W := ⟨pad, fun A B h => by
    ext v; rw [← hin A v, ← hin B v, h]⟩
  let K := H.map g
  refine ⟨W, inferInstance, inferInstance, f, g, K, rfl, hin, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_map.mp hA
    change (pad B).card = r
    have hdis : Disjoint (B.map f)
        ((Finset.univ.filter fun i : Fin r => i.val < r - B.card).image (fun i => Sum.inr (B, i))) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hx
      simp [f] at hy
    have hcount : (Finset.univ.filter fun i : Fin r => i.val < r - B.card).card = r - B.card := by
      let e : Fin (r - B.card) ↪ Fin r := ⟨fun i => ⟨i.val, i.isLt.trans_le (Nat.sub_le ..)⟩,
        fun _ _ h => Fin.ext (congrArg (fun j : Fin r => j.val) h)⟩
      have he : Finset.univ.filter (fun i : Fin r => i.val < r - B.card) = Finset.univ.map e := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, e]
        constructor
        · intro h; exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩
        · rintro ⟨j, rfl⟩; exact j.isLt
      rw [he, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    unfold pad
    rw [Finset.card_union_of_disjoint hdis, Finset.card_map,
      Finset.card_image_of_injective _ (fun _ _ he => congrArg Prod.snd (Sum.inr.inj he)), hcount]
    have := hrank B hB
    omega
  · intro E hE F hF hAB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_map.mp hE
    obtain ⟨B, hB, rfl⟩ := Finset.mem_map.mp hF
    have hn : A ≠ B := fun h => hAB (congrArg g h)
    apply Finset.card_le_one.mpr
    have old (x : W) (hx : x ∈ g A ∩ g B) : ∃ v ∈ A ∩ B, f v = x := by
      rcases x with x | ⟨C, i⟩
      · exact ⟨x, Finset.mem_inter.mpr ⟨(hin A x).mp (Finset.mem_inter.mp hx).1,
          (hin B x).mp (Finset.mem_inter.mp hx).2⟩, rfl⟩
      · exact (hn (((hout A C i).mp (Finset.mem_inter.mp hx).1).1.symm.trans
          ((hout B C i).mp (Finset.mem_inter.mp hx).2).1)).elim
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := old x hx
    obtain ⟨v, hv, rfl⟩ := old y hy
    exact congrArg f (Finset.card_le_one.mp (hlin A hA B hB hn) u hu v hv)
  · intro v
    rcases v with v | ⟨A, i⟩
    · have he : K.filter (fun E => f v ∈ E) = (H.filter (fun E => v ∈ E)).map g := by
        ext E
        simp only [K, Finset.mem_filter, Finset.mem_map]
        constructor
        · rintro ⟨⟨A, hA, rfl⟩, hv⟩; exact ⟨A, ⟨hA, (hin A v).mp hv⟩, rfl⟩
        · rintro ⟨A, ⟨hA, hv⟩, rfl⟩; exact ⟨⟨A, hA, rfl⟩, (hin A v).mpr hv⟩
      change (K.filter (fun E => f v ∈ E)).card ≤ D
      rw [he, Finset.card_map]
      exact hdeg v
    · apply le_trans _ hD
      apply Finset.card_le_one.mpr
      intro E hE F hF
      obtain ⟨hE, hVE⟩ := Finset.mem_filter.mp hE
      obtain ⟨hF, hVF⟩ := Finset.mem_filter.mp hF
      obtain ⟨B, _, rfl⟩ := Finset.mem_map.mp hE
      obtain ⟨C, _, rfl⟩ := Finset.mem_map.mp hF
      exact congrArg g (((hout B A i).mp hVE).1.symm.trans ((hout C A i).mp hVF).1)

end FinalReduction

end Erdos19H1

theorem OMA.solution : OMA.R_Erdos19_erdos_19_variants_kahn_R1.H1 := by
  intro q hq
  by_cases hq1 : q = 1
  · subst hq1; exact Erdos19H1.case_one
  · have hq2 : 2 ≤ q := by omega
    have hr : 4 ≤ 2 * q := by omega
    obtain ⟨D₀, hD₀⟩ := Erdos19H1.uniform_list_coloring (2 * q) hr
    refine ⟨max D₀ (2 * q), fun n D m hD hm H L hlin hsize hdeg hL => ?_⟩
    have hD_ge_D0 : D₀ ≤ D := (le_max_left _ _).trans hD
    have hD_ge_r : 2 * q ≤ D := (le_max_right _ _).trans hD
    obtain ⟨W, _, _, f, g, K, hKeq, hin, hunif, hKlin, hKdeg⟩ :=
      Erdos19H1.padding (2 * q) D (by omega) H hlin (fun A hA => (hsize A hA).2) hdeg
    let eW : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
    let mapE : Finset W ↪ Finset (Fin (Fintype.card W)) :=
      (Finset.mapEmbedding eW.toEmbedding).toEmbedding
    have hmapE_apply : ∀ s : Finset W, mapE s = s.map eW.toEmbedding := fun _ => rfl
    let emb : Finset (Fin n) ↪ Finset (Fin (Fintype.card W)) := g.trans mapE
    let K' : Finset (Finset (Fin (Fintype.card W))) := K.map mapE
    have hK'_eq : K' = H.map emb := by
      simp only [K', hKeq, emb, Finset.map_map]
    let L' : Finset (Fin (Fintype.card W)) → Finset (Fin m) := fun E =>
      if h : ∃ A ∈ H, emb A = E then L (Classical.choose h) else ∅
    have hL'_emb : ∀ A ∈ H, L' (emb A) = L A := fun A hA => by
      have hex : ∃ B ∈ H, emb B = emb A := ⟨A, hA, rfl⟩
      simp only [L', dif_pos hex]
      have hspec := Classical.choose_spec hex
      rw [emb.injective hspec.2]
    have hK'_unif : ∀ E ∈ K', E.card = 2 * q := by
      intro E hE
      rcases Finset.mem_map.mp hE with ⟨E₀, hE₀, rfl⟩
      simpa only [hmapE_apply, Finset.card_map] using hunif E₀ hE₀
    have hK'_lin : ∀ E ∈ K', ∀ F ∈ K', E ≠ F → (E ∩ F).card ≤ 1 := by
      intro E hE F hF hne
      rcases Finset.mem_map.mp hE with ⟨E₀, hE₀, rfl⟩
      rcases Finset.mem_map.mp hF with ⟨F₀, hF₀, rfl⟩
      have hne0 : E₀ ≠ F₀ := fun h => hne (congrArg mapE h)
      have hinter : mapE E₀ ∩ mapE F₀ = mapE (E₀ ∩ F₀) := by
        ext v
        simp only [hmapE_apply, Finset.mem_inter, Finset.mem_map]
        constructor
        · rintro ⟨⟨w₁, hw₁, rfl⟩, ⟨w₂, hw₂, hEq⟩⟩
          have hw : w₂ = w₁ := eW.injective hEq
          exact ⟨w₁, ⟨hw₁, hw ▸ hw₂⟩, rfl⟩
        · rintro ⟨w, ⟨hw₁, hw₂⟩, rfl⟩
          exact ⟨⟨w, hw₁, rfl⟩, ⟨w, hw₂, rfl⟩⟩
      rw [hinter]
      simpa only [hmapE_apply, Finset.card_map] using hKlin E₀ hE₀ F₀ hF₀ hne0
    have hK'_deg : ∀ i : Fin (Fintype.card W), (K'.filter (fun E => i ∈ E)).card ≤ D := by
      intro i
      have heq : K'.filter (fun E => i ∈ E) = (K.filter (fun E₀ => eW.symm i ∈ E₀)).map mapE := by
        ext E
        simp only [K', Finset.mem_filter, Finset.mem_map]
        constructor
        · rintro ⟨⟨E₀, hE₀, rfl⟩, hi⟩
          rw [hmapE_apply] at hi
          rcases Finset.mem_map.mp hi with ⟨w, hw, hwi⟩
          have hw' : w = eW.symm i := eW.injective (by rw [eW.apply_symm_apply]; exact hwi)
          exact ⟨E₀, ⟨hE₀, hw' ▸ hw⟩, rfl⟩
        · rintro ⟨E₀, ⟨hE₀, hw⟩, rfl⟩
          refine ⟨⟨E₀, hE₀, rfl⟩, ?_⟩
          rw [hmapE_apply]
          exact Finset.mem_map.mpr ⟨eW.symm i, hw, by simp⟩
      rw [heq, Finset.card_map]
      exact hKdeg (eW.symm i)
    have hK'_L : ∀ E ∈ K', (1 + 1 / ((2 * q : ℕ) : ℝ)) * (D : ℝ) ≤ ((L' E).card : ℝ) := by
      intro E hE
      rw [hK'_eq] at hE
      rcases Finset.mem_map.mp hE with ⟨A, hA, rfl⟩
      rw [hL'_emb A hA]
      have hdiv : D ≤ 2 * q * (D / q) := by
        have hmod := Nat.div_add_mod D q
        have hlt := Nat.mod_lt D hq
        have h4 : 2 ≤ D / q := (Nat.le_div_iff_mul_le hq).mpr (by omega)
        have h5 : q ≤ q * (D / q) := by nlinarith
        have h2c : 2 * q * (D / q) = 2 * (q * (D / q)) := by ring
        omega
      have hdivR : (D : ℝ) / ((2 * q : ℕ) : ℝ) ≤ ((D / q : ℕ) : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        have : (D : ℝ) ≤ ((2 * q : ℕ) : ℝ) * ((D / q : ℕ) : ℝ) := by
          exact_mod_cast hdiv
        linarith
      have hLA : ((D + D / q : ℕ) : ℝ) ≤ ((L A).card : ℝ) := Nat.cast_le.mpr (hL A hA)
      push_cast at hLA
      linarith [hdivR, hLA, show (1 + 1 / ((2 * q : ℕ) : ℝ)) * (D : ℝ) =
        (D : ℝ) + (D : ℝ) / ((2 * q : ℕ) : ℝ) by ring]
    obtain ⟨c', hc'_prop, hc'_L⟩ :=
      hD₀ (Fintype.card W) D m hD_ge_D0 hm K' L' hK'_lin hK'_unif hK'_deg hK'_L
    refine ⟨fun A => c' (emb A), ?_, ?_⟩
    · intro A hA B hB hAB hinter
      have hEA : emb A ∈ K' := by rw [hK'_eq]; exact Finset.mem_map.mpr ⟨A, hA, rfl⟩
      have hEB : emb B ∈ K' := by rw [hK'_eq]; exact Finset.mem_map.mpr ⟨B, hB, rfl⟩
      have hEne : emb A ≠ emb B := fun h => hAB (emb.injective h)
      have hEint : (emb A ∩ emb B).Nonempty := by
        rcases hinter with ⟨v, hv⟩
        rcases Finset.mem_inter.mp hv with ⟨hvA, hvB⟩
        refine ⟨eW (f v), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · change eW (f v) ∈ mapE (g A)
          rw [hmapE_apply]; exact Finset.mem_map.mpr ⟨f v, (hin A v).mpr hvA, rfl⟩
        · change eW (f v) ∈ mapE (g B)
          rw [hmapE_apply]; exact Finset.mem_map.mpr ⟨f v, (hin B v).mpr hvB, rfl⟩
      exact hc'_prop (emb A) hEA (emb B) hEB hEne hEint
    · intro A hA
      have hEA : emb A ∈ K' := by rw [hK'_eq]; exact Finset.mem_map.mpr ⟨A, hA, rfl⟩
      simpa only [hL'_emb A hA] using hc'_L (emb A) hEA
