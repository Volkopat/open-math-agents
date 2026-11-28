import OMAReductions.R_Erdos774_erdos_774_R1_H2_R1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Pi
import Mathlib.Tactic

/-!
# Quantitative Bourgain Bounded-Length Decomposition for Proportionately Dissociated Sets

Proves `OMA.R_Erdos774_erdos_774_R1_H2_R1.H1` following Bourgain (1983), Proposition 3.1--3.2:
if every subset `B ⊆ F` of a finite set `F ⊆ ℕ` contains a dissociated subset of size at least
`δ * |B|`, then `F` can be covered by `k(δ, r)` subsets having no non-dissociated subset of
size at most `r`.

The proof proceeds in three self-contained elementary steps:
1. A generating-function bound on the integer L1 ball shows that any dissociated subset of the
   length-`l` `{-1, 0, 1}`-span `S_l(A)` has size at most `2 * (8 * l + 2) * |A|`, giving
   `|S_l(A) ∩ F| ≤ (2 * (8 * l + 2) / δ) * |A|`.
2. Finite averaging over colorings `f : Λ → Fin D` shows that if every element of `Λ` lies in
   the length-`l` span of `K` pairwise disjoint subsets of `Λ` of size at most `l`, then
   `(1 - (1 - D^(-l))^K) * |Λ| ≤ (C / D) * |Λ|`.
3. Strong induction on `|Λ|` with `D = ⌈2 * C⌉₊ + 1` and `K = D^l` yields a pairwise-disjoint
   `K`-partition of `F` whose parts contain no non-dissociated subset of size at most `r`.
-/

namespace OMA.Erdos774H1

open Finset
open scoped BigOperators Classical

/-- `x` lies in the length-`l` `{-1, 0, 1}`-span of `A`. -/
def InSpan (l : ℕ) (A : Finset ℕ) (x : ℕ) : Prop :=
  ∃ X Y : Finset ℕ, X ⊆ A ∧ Y ⊆ A ∧ Disjoint X Y ∧ X.card + Y.card ≤ l ∧
    x + ∑ a ∈ X, a = ∑ b ∈ Y, b

/-- A finite set `B` has no non-dissociated subset of cardinality at most `r`. -/
def IsRDis (r : ℕ) (B : Finset ℕ) : Prop :=
  ∀ T ⊆ B, T.card ≤ r → Set.IsDissociated (↑T : Set ℕ)

private lemma inSpan_mono {l : ℕ} {A₁ A₂ : Finset ℕ} {x : ℕ} (hsub : A₁ ⊆ A₂)
    (hx : InSpan l A₁ x) : InSpan l A₂ x := by
  obtain ⟨X, Y, hX, hY, hdis, hcard, heq⟩ := hx
  exact ⟨X, Y, hX.trans hsub, hY.trans hsub, hdis, hcard, heq⟩

/-- Geometric sum upper bound over `Icc (-M) M`. -/
private lemma geom_int_sum_le (q : ℝ) (hq : 0 < q) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) M, ((1 + q)⁻¹ : ℝ) ^ k.natAbs ≤ 2 * (1 + q) / q := by
  set t : ℝ := (1 + q)⁻¹
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr (by linarith)
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  have hgeom : ∑ j ∈ Finset.range (M + 1), t ^ j ≤ (1 - t)⁻¹ := by
    have hmul : (∑ j ∈ Finset.range (M + 1), t ^ j) * (1 - t) = 1 - t ^ (M + 1) := by
      have h := geom_sum_mul t (M + 1)
      linarith
    have hpow : 0 ≤ t ^ (M + 1) := pow_nonneg ht0 _
    rw [← one_div, le_div_iff₀ h1t]
    linarith
  set P : Finset ℤ := (Finset.range (M + 1)).image (fun j : ℕ => (j : ℤ))
  set N : Finset ℤ := (Finset.range (M + 1)).image (fun j : ℕ => -(j : ℤ))
  have hsub : Finset.Icc (-(M : ℤ)) M ⊆ P ∪ N := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    by_cases hkn : 0 ≤ k
    · left
      refine ⟨k.natAbs, Finset.mem_range.mpr ?_, Int.natAbs_of_nonneg hkn⟩
      omega
    · right
      refine ⟨k.natAbs, Finset.mem_range.mpr ?_, ?_⟩ <;> omega
  have hpos_img : ∑ k ∈ P, t ^ k.natAbs = ∑ j ∈ Finset.range (M + 1), t ^ j := by
    rw [Finset.sum_image (fun a _ b _ hab => by exact_mod_cast hab)]
    simp
  have hneg_img : ∑ k ∈ N, t ^ k.natAbs = ∑ j ∈ Finset.range (M + 1), t ^ j := by
    rw [Finset.sum_image (fun a _ b _ hab => by omega)]
    simp
  have hunion_le : ∑ k ∈ P ∪ N, t ^ k.natAbs ≤
      (∑ k ∈ P, t ^ k.natAbs) + (∑ k ∈ N, t ^ k.natAbs) := by
    have h := Finset.sum_union_inter (s₁ := P) (s₂ := N) (f := fun k : ℤ => t ^ k.natAbs)
    have hinter : 0 ≤ ∑ k ∈ P ∩ N, t ^ k.natAbs :=
      Finset.sum_nonneg (fun _ _ => pow_nonneg ht0 _)
    linarith
  have hstep1 : ∑ k ∈ Finset.Icc (-(M : ℤ)) M, t ^ k.natAbs ≤
      2 * ∑ j ∈ Finset.range (M + 1), t ^ j := by
    calc ∑ k ∈ Finset.Icc (-(M : ℤ)) M, t ^ k.natAbs
        ≤ ∑ k ∈ P ∪ N, t ^ k.natAbs :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg ht0 _)
      _ ≤ (∑ k ∈ P, t ^ k.natAbs) + (∑ k ∈ N, t ^ k.natAbs) := hunion_le
      _ = 2 * ∑ j ∈ Finset.range (M + 1), t ^ j := by rw [hpos_img, hneg_img]; ring
  have hinv : (1 - t)⁻¹ = (1 + q) / q := by
    have hq1 : (1 + q : ℝ) ≠ 0 := by linarith
    have h1 : 1 - t = q / (1 + q) := by
      dsimp [t]
      field_simp
      ring
    rw [h1, inv_div]
  calc ∑ k ∈ Finset.Icc (-(M : ℤ)) M, t ^ k.natAbs
      ≤ 2 * ∑ j ∈ Finset.range (M + 1), t ^ j := hstep1
    _ ≤ 2 * (1 - t)⁻¹ := by linarith
    _ = 2 * (1 + q) / q := by rw [hinv]; ring

/-- Generating-function bound on the cardinality of the integer L1 ball of radius `M` on `A`. -/
private lemma card_l1_ball_le (A : Finset ℕ) (M : ℕ) (q : ℝ) (hq : 0 < q) :
    (((Fintype.piFinset (fun _ : A => Finset.Icc (-(M : ℤ)) M)).filter
      (fun c => ∑ a : A, (c a).natAbs ≤ M)).card : ℝ) ≤
      (1 + q) ^ M * (2 * (1 + q) / q) ^ A.card := by
  set I : Finset ℤ := Finset.Icc (-(M : ℤ)) M
  set Box : Finset (A → ℤ) := Fintype.piFinset (fun _ : A => I)
  set Ball : Finset (A → ℤ) := Box.filter (fun c => ∑ a : A, (c a).natAbs ≤ M)
  set t : ℝ := (1 + q)⁻¹
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr (by linarith)
  have h1q : 0 < 1 + q := by linarith
  have hterm : ∀ c ∈ Ball, (1 : ℝ) ≤ (1 + q) ^ M * ∏ a : A, t ^ (c a).natAbs := by
    intro c hc
    have hle : ∑ a : A, (c a).natAbs ≤ M := (Finset.mem_filter.mp hc).2
    rw [Finset.prod_pow_eq_pow_sum]
    have hpow : t ^ M ≤ t ^ (∑ a : A, (c a).natAbs) := pow_le_pow_of_le_one ht0 ht1 hle
    have hmul : (1 + q) ^ M * t ^ M = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ h1q.ne', one_pow]
    calc (1 : ℝ) = (1 + q) ^ M * t ^ M := hmul.symm
      _ ≤ (1 + q) ^ M * t ^ (∑ a : A, (c a).natAbs) :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg h1q.le M)
  have hsum1 : (Ball.card : ℝ) ≤
      (1 + q) ^ M * ∑ c ∈ Box, ∏ a : A, t ^ (c a).natAbs := by
    calc (Ball.card : ℝ) = ∑ _c ∈ Ball, (1 : ℝ) := by simp
      _ ≤ ∑ c ∈ Ball, (1 + q) ^ M * ∏ a : A, t ^ (c a).natAbs :=
        Finset.sum_le_sum hterm
      _ = (1 + q) ^ M * ∑ c ∈ Ball, ∏ a : A, t ^ (c a).natAbs := by
        rw [Finset.mul_sum]
      _ ≤ (1 + q) ^ M * ∑ c ∈ Box, ∏ a : A, t ^ (c a).natAbs := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg h1q.le M)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Finset.prod_nonneg (fun _ _ => pow_nonneg ht0 _))
  have hprod : ∑ c ∈ Box, ∏ a : A, t ^ (c a).natAbs =
      ∏ _a : A, ∑ k ∈ I, t ^ k.natAbs :=
    (Finset.prod_univ_sum (t := fun _ : A => I) (f := fun (_ : A) (k : ℤ) => t ^ k.natAbs)).symm
  rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_coe] at hsum1
  have hgeom := geom_int_sum_le q hq M
  have hgeom0 : 0 ≤ ∑ k ∈ I, t ^ k.natAbs := Finset.sum_nonneg (fun _ _ => pow_nonneg ht0 _)
  calc (Ball.card : ℝ)
      ≤ (1 + q) ^ M * (∑ k ∈ I, t ^ k.natAbs) ^ A.card := hsum1
    _ ≤ (1 + q) ^ M * (2 * (1 + q) / q) ^ A.card := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg h1q.le M)
      exact pow_le_pow_left₀ hgeom0 hgeom A.card

/-- Helper: summing `a.1` over `a : A` satisfying `a.1 ∈ W` equals summing over `W` when `W ⊆ A`. -/
private lemma sum_coe_ite_eq {A W : Finset ℕ} (hWA : W ⊆ A) :
    ∑ a : A, (if a.1 ∈ W then (a.1 : ℤ) else 0) = ∑ b ∈ W, (b : ℤ) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => a.1) ?_ ?_ ?_ ?_
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a₁ _ a₂ _ h
    exact Subtype.ext h
  · intro b hb
    exact ⟨⟨b, hWA hb⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩
  · intro _ _
    rfl

/-- Helper: counting `a : A` with `a.1 ∈ W` equals `W.card` when `W ⊆ A`. -/
private lemma card_coe_ite_eq {A W : Finset ℕ} (hWA : W ⊆ A) :
    (∑ a : A, if a.1 ∈ W then (1 : ℕ) else 0) = W.card := by
  rw [Finset.sum_boole, Nat.cast_id]
  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a₁ _ a₂ _ h
    exact Subtype.ext h
  · intro b hb
    exact ⟨⟨b, hWA hb⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

/-- Any dissociated subset of the length-`l` span of `A` has size at most `2 * (8 * l + 2) * |A|`. -/
private lemma dissociated_card_le_of_inSpan (l : ℕ) (hl : 1 ≤ l) (A S : Finset ℕ)
    (hS : Set.IsDissociated (↑S : Set ℕ)) (hspan : ∀ x ∈ S, InSpan l A x) :
    S.card ≤ 2 * (8 * l + 2) * A.card := by
  have hchoose : ∀ x : S, ∃ X Y : Finset ℕ, X ⊆ A ∧ Y ⊆ A ∧ Disjoint X Y ∧
      X.card + Y.card ≤ l ∧ x.1 + ∑ a ∈ X, a = ∑ b ∈ Y, b :=
    fun x => hspan x.1 x.2
  choose X Y hXA hYA hdis hcard heq using hchoose
  set M : ℕ := l * S.card
  let X' (x : ℕ) : Finset ℕ := if h : x ∈ S then X ⟨x, h⟩ else ∅
  let Y' (x : ℕ) : Finset ℕ := if h : x ∈ S then Y ⟨x, h⟩ else ∅
  let coeff (U : Finset ℕ) (a : A) : ℤ :=
    ((U.filter fun x => a.1 ∈ Y' x).card : ℤ) - ((U.filter fun x => a.1 ∈ X' x).card : ℤ)
  have hsum_eq : ∀ U ∈ S.powerset, ∑ a : A, coeff U a * (a.1 : ℤ) = ∑ x ∈ U, (x : ℤ) := by
    intro U hU
    have hUS : U ⊆ S := Finset.mem_powerset.mp hU
    have hlin : ∀ a : A, coeff U a * (a.1 : ℤ) =
        ∑ x ∈ U, ((if a.1 ∈ Y' x then (a.1 : ℤ) else 0) -
          (if a.1 ∈ X' x then (a.1 : ℤ) else 0)) := by
      intro a
      simp only [coeff, Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul]
      ring
    simp_rw [hlin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxS : x ∈ S := hUS hx
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ a : A, (if a.1 ∈ Y' x then (a.1 : ℤ) else 0) = ∑ b ∈ Y ⟨x, hxS⟩, (b : ℤ) := by
      simp only [Y', hxS, ↓reduceDIte]
      exact sum_coe_ite_eq (hYA ⟨x, hxS⟩)
    have h2 : ∑ a : A, (if a.1 ∈ X' x then (a.1 : ℤ) else 0) = ∑ a ∈ X ⟨x, hxS⟩, (a : ℤ) := by
      simp only [X', hxS, ↓reduceDIte]
      exact sum_coe_ite_eq (hXA ⟨x, hxS⟩)
    rw [h1, h2]
    have hnat : (x : ℤ) + ∑ a ∈ X ⟨x, hxS⟩, (a : ℤ) = ∑ b ∈ Y ⟨x, hxS⟩, (b : ℤ) := by
      have h := congrArg (Nat.cast (R := ℤ)) (heq ⟨x, hxS⟩)
      simpa [Nat.cast_add, Nat.cast_sum] using h
    linarith
  have hl1 : ∀ U ∈ S.powerset, ∑ a : A, (coeff U a).natAbs ≤ M := by
    intro U hU
    have hUS : U ⊆ S := Finset.mem_powerset.mp hU
    have hle_a : ∀ a : A, (coeff U a).natAbs ≤
        (U.filter fun x => a.1 ∈ Y' x).card + (U.filter fun x => a.1 ∈ X' x).card := by
      intro a
      dsimp only [coeff]
      omega
    calc ∑ a : A, (coeff U a).natAbs
        ≤ ∑ a : A, ((U.filter fun x => a.1 ∈ Y' x).card + (U.filter fun x => a.1 ∈ X' x).card) :=
          Finset.sum_le_sum (fun a _ => hle_a a)
      _ = ∑ a : A, ∑ x ∈ U, ((if a.1 ∈ Y' x then 1 else 0) + (if a.1 ∈ X' x then 1 else 0)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
      _ = ∑ x ∈ U, ∑ a : A, ((if a.1 ∈ Y' x then 1 else 0) + (if a.1 ∈ X' x then 1 else 0)) :=
          Finset.sum_comm
      _ ≤ ∑ _x ∈ U, l := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hxS : x ∈ S := hUS hx
          rw [Finset.sum_add_distrib]
          have h1 : (∑ a : A, if a.1 ∈ Y' x then (1 : ℕ) else 0) = (Y ⟨x, hxS⟩).card := by
            simp only [Y', hxS, ↓reduceDIte]
            exact card_coe_ite_eq (hYA ⟨x, hxS⟩)
          have h2 : (∑ a : A, if a.1 ∈ X' x then (1 : ℕ) else 0) = (X ⟨x, hxS⟩).card := by
            simp only [X', hxS, ↓reduceDIte]
            exact card_coe_ite_eq (hXA ⟨x, hxS⟩)
          rw [h1, h2]
          have hc := hcard ⟨x, hxS⟩
          omega
      _ = U.card * l := by simp
      _ ≤ S.card * l := Nat.mul_le_mul_right l (Finset.card_le_card hUS)
      _ = M := by rw [Nat.mul_comm]
  set Ball := (Fintype.piFinset (fun _ : A => Finset.Icc (-(M : ℤ)) M)).filter
    (fun c => ∑ a : A, (c a).natAbs ≤ M)
  have hmaps : Set.MapsTo coeff (↑S.powerset : Set (Finset ℕ)) (↑Ball : Set (A → ℤ)) := by
    intro U hU
    rw [Finset.mem_coe] at hU ⊢
    refine Finset.mem_filter.mpr ⟨?_, hl1 U hU⟩
    rw [Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    have hsingle : (coeff U a).natAbs ≤ M :=
      (Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ a)).trans (hl1 U hU)
    omega
  have hinj : Set.InjOn coeff (↑S.powerset : Set (Finset ℕ)) := by
    intro U₁ hU₁ U₂ hU₂ heq_c
    rw [Finset.mem_coe] at hU₁ hU₂
    have hz : ∑ x ∈ U₁, (x : ℤ) = ∑ x ∈ U₂, (x : ℤ) := by
      rw [← hsum_eq U₁ hU₁, ← hsum_eq U₂ hU₂, heq_c]
    have hn : ∑ x ∈ U₁, x = ∑ x ∈ U₂, x := by
      rw [← Nat.cast_inj (R := ℤ)]
      simpa [Nat.cast_sum] using hz
    exact hS (Finset.coe_subset.mpr (Finset.mem_powerset.mp hU₁))
      (Finset.coe_subset.mpr (Finset.mem_powerset.mp hU₂)) hn
  have hcard_le : (2 ^ S.card : ℝ) ≤ (Ball.card : ℝ) := by
    have hc : S.powerset.card ≤ Ball.card := Finset.card_le_card_of_injOn coeff hmaps hinj
    rw [Finset.card_powerset] at hc
    exact_mod_cast hc
  set q : ℝ := (4 * (l : ℝ))⁻¹
  have hl_pos : (0 : ℝ) < l := by exact_mod_cast hl
  have hq : 0 < q := by positivity
  have hball := card_l1_ball_le A M q hq
  have hq_val : 2 * (1 + q) / q = (8 * l + 2 : ℕ) := by
    dsimp [q]
    push_cast
    field_simp
    ring
  rw [hq_val] at hball
  have hpow_bound : (1 + q) ^ M ≤ Real.exp ((S.card : ℝ) / 4) := by
    have h1 : 1 + q ≤ Real.exp q := by linarith [Real.add_one_le_exp q]
    calc (1 + q) ^ M
        ≤ (Real.exp q) ^ M := pow_le_pow_left₀ (by positivity) h1 M
      _ = Real.exp ((M : ℝ) * q) := by rw [← Real.exp_nat_mul]
      _ = Real.exp ((S.card : ℝ) / 4) := by
        congr 1
        dsimp [M, q]
        push_cast
        field_simp
  have hmain : (2 : ℝ) ^ S.card ≤ Real.exp ((S.card : ℝ) / 4) * ((8 * l + 2 : ℕ) : ℝ) ^ A.card := by
    calc (2 : ℝ) ^ S.card ≤ (Ball.card : ℝ) := hcard_le
      _ ≤ (1 + q) ^ M * ((8 * l + 2 : ℕ) : ℝ) ^ A.card := hball
      _ ≤ Real.exp ((S.card : ℝ) / 4) * ((8 * l + 2 : ℕ) : ℝ) ^ A.card := by
        apply mul_le_mul_of_nonneg_right hpow_bound (by positivity)
  have h4 : ((2 : ℝ) ^ S.card) ^ 4 ≤
      (Real.exp ((S.card : ℝ) / 4) * ((8 * l + 2 : ℕ) : ℝ) ^ A.card) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hmain 4
  have hexp4 : (Real.exp ((S.card : ℝ) / 4)) ^ 4 ≤ (4 : ℝ) ^ S.card := by
    rw [← Real.exp_nat_mul]
    have harg : ((4 : ℕ) : ℝ) * ((S.card : ℝ) / 4) = (S.card : ℝ) * 1 := by norm_num; ring
    rw [harg, Real.exp_nat_mul]
    have he4 : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le he4 S.card
  rw [mul_pow] at h4
  have h4' : (2 : ℝ) ^ (4 * S.card) ≤ (2 : ℝ) ^ (2 * S.card) * ((8 * l + 2 : ℕ) : ℝ) ^ (4 * A.card) := by
    have hpow2 : ((2 : ℝ) ^ S.card) ^ 4 = (2 : ℝ) ^ (4 * S.card) := by
      rw [← pow_mul, Nat.mul_comm]
    have hpow4 : (4 : ℝ) ^ S.card = (2 : ℝ) ^ (2 * S.card) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
    have hpow8 : (((8 * l + 2 : ℕ) : ℝ) ^ A.card) ^ 4 = ((8 * l + 2 : ℕ) : ℝ) ^ (4 * A.card) := by
      rw [← pow_mul, Nat.mul_comm A.card 4]
    rw [hpow2, hpow8] at h4
    calc (2 : ℝ) ^ (4 * S.card)
        ≤ (Real.exp ((S.card : ℝ) / 4)) ^ 4 * ((8 * l + 2 : ℕ) : ℝ) ^ (4 * A.card) := h4
      _ ≤ (4 : ℝ) ^ S.card * ((8 * l + 2 : ℕ) : ℝ) ^ (4 * A.card) :=
        mul_le_mul_of_nonneg_right hexp4 (by positivity)
      _ = (2 : ℝ) ^ (2 * S.card) * ((8 * l + 2 : ℕ) : ℝ) ^ (4 * A.card) := by rw [hpow4]
  have hcancel : (2 : ℝ) ^ (2 * S.card) ≤ ((8 * l + 2 : ℕ) : ℝ) ^ (4 * A.card) := by
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (2 * S.card) := by positivity
    have hsplit : (2 : ℝ) ^ (4 * S.card) = (2 : ℝ) ^ (2 * S.card) * (2 : ℝ) ^ (2 * S.card) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit] at h4'
    exact le_of_mul_le_mul_left h4' hpos2
  have hnat_le : 2 ^ (2 * S.card) ≤ (8 * l + 2) ^ (4 * A.card) := by exact_mod_cast hcancel
  have hbase : 8 * l + 2 ≤ 2 ^ (8 * l + 2) := Nat.lt_two_pow_self.le
  have hchain : 2 ^ (2 * S.card) ≤ 2 ^ ((8 * l + 2) * (4 * A.card)) := by
    calc 2 ^ (2 * S.card) ≤ (8 * l + 2) ^ (4 * A.card) := hnat_le
      _ ≤ (2 ^ (8 * l + 2)) ^ (4 * A.card) := Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((8 * l + 2) * (4 * A.card)) := by rw [← pow_mul]
  have hexp_le : 2 * S.card ≤ (8 * l + 2) * (4 * A.card) :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hchain
  have hrhs : (8 * l + 2) * (4 * A.card) = 2 * (2 * (8 * l + 2) * A.card) := by ring
  omega

/-- Proportional dissociation implies a linear bound on `|S_l(A) ∩ F|`. -/
private lemma inSpan_filter_card_le (l : ℕ) (hl : 1 ≤ l) (δ : ℝ) (hδ : 0 < δ) (F : Finset ℕ)
    (hextract : ∀ B ⊆ F, ∃ S ⊆ B, Set.IsDissociated (↑S : Set ℕ) ∧ (S.card : ℝ) ≥ δ * B.card)
    (A : Finset ℕ) :
    ((F.filter (InSpan l A)).card : ℝ) ≤ (2 * (8 * l + 2) : ℝ) / δ * (A.card : ℝ) := by
  obtain ⟨S, hSB, hSdis, hScard⟩ := hextract (F.filter (InSpan l A)) (Finset.filter_subset _ _)
  have hspan : ∀ x ∈ S, InSpan l A x := fun x hx => (Finset.mem_filter.mp (hSB hx)).2
  have hle : (S.card : ℝ) ≤ (2 * (8 * l + 2) : ℝ) * (A.card : ℝ) := by
    exact_mod_cast dissociated_card_le_of_inSpan l hl A S hSdis hspan
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  linarith

/-- Total cardinality of the zero-fiber summed over all colorings `U → Fin D`. -/
private lemma sum_zero_fiber_card (U : Finset ℕ) (D : ℕ) (hD : 0 < D) :
    D * ∑ f : U → Fin D, (Finset.univ.filter fun x : U => f x = ⟨0, hD⟩).card =
      U.card * D ^ U.card := by
  have hswap : ∑ f : U → Fin D, (Finset.univ.filter fun x : U => f x = ⟨0, hD⟩).card =
      ∑ x : U, (Finset.univ.filter fun f : U → Fin D => f x = ⟨0, hD⟩).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  have heach : ∀ x : U,
      D * (Finset.univ.filter fun f : U → Fin D => f x = ⟨0, hD⟩).card = D ^ U.card := by
    intro x
    let e : (U → Fin D) ≃ Fin D × ({y : U // y ≠ x} → Fin D) :=
      { toFun := fun f => (f x, fun y => f y.1)
        invFun := fun p y => if h : y = x then p.1 else p.2 ⟨y, h⟩
        left_inv := fun f => by
          funext y
          by_cases h : y = x
          · simp [h]
          · simp [h]
        right_inv := fun ⟨c, g⟩ =>
          Prod.ext (by simp) (funext fun ⟨y, hy⟩ => by simp [hy]) }
    have hfiber : (Finset.univ.filter fun f : U → Fin D => f x = ⟨0, hD⟩).card =
        Fintype.card ({y : U // y ≠ x} → Fin D) := by
      have hcard_eq : (Finset.univ.filter fun f : U → Fin D => f x = ⟨0, hD⟩).card =
          Fintype.card {f : U → Fin D // f x = ⟨0, hD⟩} :=
        (Fintype.card_subtype _).symm
      rw [hcard_eq]
      refine Fintype.card_congr
        { toFun := fun f => fun y => f.1 y.1
          invFun := fun g => ⟨fun y => if h : y = x then ⟨0, hD⟩ else g ⟨y, h⟩, by simp⟩
          left_inv := fun ⟨f, hf⟩ => by
            ext y
            by_cases h : y = x
            · subst h; simp [hf]
            · simp [h]
          right_inv := fun g => by
            funext ⟨y, hy⟩
            simp [hy] }
    rw [hfiber]
    have hprod := Fintype.card_congr e
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe] at hprod
    exact hprod.symm
  simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]

/-- Number of colorings `U → Fin D` avoiding `m` pairwise disjoint sets `P j ⊆ U` of size `≤ l`. -/
private lemma avoid_count_le (D : ℕ) (hD : 0 < D) (l : ℕ) :
    ∀ (m : ℕ) (U : Finset ℕ) (P : Fin m → Finset ℕ),
      (∀ j, P j ⊆ U) → (∀ j, (P j).card ≤ l) →
      Pairwise (fun i j => Disjoint (P i) (P j)) →
      ((Finset.univ.filter (fun f : U → Fin D =>
        ∀ j : Fin m, ∃ x : U, x.1 ∈ P j ∧ f x ≠ ⟨0, hD⟩)).card : ℝ) ≤
      (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ m * (D : ℝ) ^ U.card := by
  intro m
  induction m with
  | zero =>
    intro U P _ _ _
    have hfilt : (Finset.univ.filter (fun f : U → Fin D =>
        ∀ j : Fin 0, ∃ x : U, x.1 ∈ P j ∧ f x ≠ ⟨0, hD⟩)) = Finset.univ :=
      Finset.filter_true_of_mem (fun _ _ j => Fin.elim0 j)
    rw [hfilt, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    simp
  | succ m ih =>
    intro U P hPU hPl hPdis
    set P₀ : Finset ℕ := P 0
    set U' : Finset ℕ := U \ P₀
    have hP₀U : P₀ ⊆ U := hPU 0
    let e : (U → Fin D) ≃ (P₀ → Fin D) × (U' → Fin D) :=
      { toFun := fun f =>
          (fun x => f ⟨x.1, hP₀U x.2⟩, fun y => f ⟨y.1, (Finset.mem_sdiff.mp y.2).1⟩)
        invFun := fun p x =>
          if h : x.1 ∈ P₀ then p.1 ⟨x.1, h⟩ else p.2 ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, h⟩⟩
        left_inv := fun f => by
          funext x
          by_cases h : x.1 ∈ P₀
          · simp [h]
          · simp [h]
        right_inv := fun ⟨g₁, g₂⟩ =>
          Prod.ext
            (funext fun ⟨x, hx⟩ => by simp [hx])
            (funext fun ⟨y, hy⟩ => by
              have hy' : y ∉ P₀ := (Finset.mem_sdiff.mp hy).2
              simp [hy']) }
    set S₁ : Finset (P₀ → Fin D) := Finset.univ.filter (fun g => ∃ x : P₀, g x ≠ ⟨0, hD⟩)
    set S₂ : Finset (U' → Fin D) := Finset.univ.filter (fun g =>
      ∀ j : Fin m, ∃ y : U', y.1 ∈ P j.succ ∧ g y ≠ ⟨0, hD⟩)
    have hsub' : ∀ j : Fin m, P j.succ ⊆ U' := by
      intro j y hy
      exact Finset.mem_sdiff.mpr ⟨hPU j.succ hy,
        Finset.disjoint_right.mp (hPdis (Fin.succ_ne_zero j).symm) hy⟩
    have hcard_eq : (Finset.univ.filter (fun f : U → Fin D =>
        ∀ j : Fin (m + 1), ∃ x : U, x.1 ∈ P j ∧ f x ≠ ⟨0, hD⟩)).card = S₁.card * S₂.card := by
      rw [← Finset.card_product]
      refine Finset.card_bij (fun f _ => e f) ?_ ?_ ?_
      · intro f hf
        have hcond := (Finset.mem_filter.mp hf).2
        rw [Finset.mem_product]
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        · obtain ⟨x, hxP, hfx⟩ := hcond 0
          exact ⟨⟨x.1, hxP⟩, hfx⟩
        · intro j
          obtain ⟨x, hxP, hfx⟩ := hcond j.succ
          exact ⟨⟨x.1, hsub' j hxP⟩, hxP, hfx⟩
      · intro f₁ _ f₂ _ h
        exact e.injective h
      · intro p hp
        rw [Finset.mem_product] at hp
        have h1 := (Finset.mem_filter.mp hp.1).2
        have h2 := (Finset.mem_filter.mp hp.2).2
        refine ⟨e.symm p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply p⟩
        intro j
        refine Fin.cases ?_ ?_ j
        · obtain ⟨x, hgx⟩ := h1
          exact ⟨⟨x.1, hP₀U x.2⟩, x.2, by simpa [e, x.2] using hgx⟩
        · intro j'
          obtain ⟨y, hyP, hgy⟩ := h2 j'
          have hyn : y.1 ∉ P₀ := (Finset.mem_sdiff.mp y.2).2
          exact ⟨⟨y.1, (Finset.mem_sdiff.mp y.2).1⟩, hyP, by simpa [e, hyn] using hgy⟩
    have hS₁_card : S₁.card = D ^ P₀.card - 1 := by
      let z : P₀ → Fin D := fun _ => ⟨0, hD⟩
      have hcomp : S₁ = Finset.univ.erase z := by
        ext g
        simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
          and_true]
        constructor
        · rintro ⟨x, hx⟩ hg
          exact hx (congrFun hg x)
        · intro hg
          by_contra h
          push Not at h
          exact hg (funext h)
      rw [hcomp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe]
    have hS₁_real : (S₁.card : ℝ) ≤ (1 - (1 : ℝ) / (D : ℝ) ^ l) * (D : ℝ) ^ P₀.card := by
      have hposD : 1 ≤ D ^ P₀.card := Nat.one_le_pow _ _ hD
      rw [hS₁_card, Nat.cast_sub hposD, Nat.cast_pow, Nat.cast_one]
      have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
      have hpow_le : (D : ℝ) ^ P₀.card ≤ (D : ℝ) ^ l := pow_le_pow_right₀ hD1 (hPl 0)
      have hdiv : (D : ℝ) ^ P₀.card / (D : ℝ) ^ l ≤ 1 :=
        (div_le_one (by positivity)).mpr hpow_le
      nlinarith [show (1 - (1 : ℝ) / (D : ℝ) ^ l) * (D : ℝ) ^ P₀.card =
        (D : ℝ) ^ P₀.card - (D : ℝ) ^ P₀.card / (D : ℝ) ^ l by ring]
    have hIH := ih U' (fun j => P j.succ) hsub' (fun j => hPl j.succ)
      (fun i j hij => hPdis (fun h => hij (Fin.succ_injective _ h)))
    have hcard_add : P₀.card + U'.card = U.card := by
      rw [Finset.card_sdiff_of_subset hP₀U]
      exact Nat.add_sub_of_le (Finset.card_le_card hP₀U)
    have h1_nonneg : 0 ≤ 1 - (1 : ℝ) / (D : ℝ) ^ l := by
      have hD1 : (1 : ℝ) ≤ (D : ℝ) ^ l := one_le_pow₀ (by exact_mod_cast hD)
      rw [sub_nonneg, div_le_one (by positivity)]
      exact hD1
    rw [hcard_eq, Nat.cast_mul]
    calc (S₁.card : ℝ) * (S₂.card : ℝ)
        ≤ ((1 - (1 : ℝ) / (D : ℝ) ^ l) * (D : ℝ) ^ P₀.card) *
          ((1 - (1 : ℝ) / (D : ℝ) ^ l) ^ m * (D : ℝ) ^ U'.card) :=
          mul_le_mul hS₁_real hIH (Nat.cast_nonneg _) (mul_nonneg h1_nonneg (by positivity))
      _ = (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ (m + 1) * (D : ℝ) ^ (P₀.card + U'.card) := by
          rw [pow_succ', pow_add]
          ring
      _ = (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ (m + 1) * (D : ℝ) ^ U.card := by rw [hcard_add]

/-- Finite averaging step (Bourgain Lemma 3.4): if every `γ ∈ Λ` has `K` pairwise disjoint
length-`l` witnesses in `Λ`, then `(1 - (1 - D^(-l))^K) * |Λ| ≤ (C / D) * |Λ|`. -/
private lemma bourgain_averaging (Λ : Finset ℕ) (D l K : ℕ) (hD : 0 < D) (C : ℝ)
    (hbound : ∀ A' : Finset ℕ, A' ⊆ Λ → ((Λ.filter (InSpan l A')).card : ℝ) ≤ C * (A'.card : ℝ))
    (hwit : ∀ γ ∈ Λ, ∃ P : Fin K → Finset ℕ, (∀ j, P j ⊆ Λ) ∧ (∀ j, (P j).card ≤ l) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ ∀ j, InSpan l (P j) γ) :
    (1 - (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ K) * (Λ.card : ℝ) ≤ (C / (D : ℝ)) * (Λ.card : ℝ) := by
  let sub (f : Λ → Fin D) : Finset ℕ :=
    (Finset.univ.filter fun x : Λ => f x = ⟨0, hD⟩).map ⟨Subtype.val, Subtype.val_injective⟩
  have hsub_sub : ∀ f, sub f ⊆ Λ := by
    intro f x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
    exact y.2
  have hsub_card : ∀ f, (sub f).card = (Finset.univ.filter fun x : Λ => f x = ⟨0, hD⟩).card :=
    fun f => Finset.card_map _
  let hit (γ : ℕ) (f : Λ → Fin D) : Prop := InSpan l (sub f) γ
  have hpoint : ∀ f : Λ → Fin D,
      ((Λ.filter (fun γ => hit γ f)).card : ℝ) ≤ C * ((sub f).card : ℝ) :=
    fun f => hbound (sub f) (hsub_sub f)
  have hsum_le : (∑ f : Λ → Fin D, ((Λ.filter (fun γ => hit γ f)).card : ℝ)) ≤
      C * ∑ f : Λ → Fin D, ((sub f).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun f _ => hpoint f)
  have hRHS : C * ∑ f : Λ → Fin D, ((sub f).card : ℝ) =
      (C / (D : ℝ)) * (Λ.card : ℝ) * (D : ℝ) ^ Λ.card := by
    have hD_pos : (0 : ℝ) < D := by exact_mod_cast hD
    have hfib : (D : ℝ) * ∑ f : Λ → Fin D, ((sub f).card : ℝ) =
        (Λ.card : ℝ) * (D : ℝ) ^ Λ.card := by
      simp_rw [hsub_card]
      exact_mod_cast sum_zero_fiber_card Λ D hD
    have hfib' : ∑ f : Λ → Fin D, ((sub f).card : ℝ) =
        (Λ.card : ℝ) * (D : ℝ) ^ Λ.card / (D : ℝ) :=
      eq_div_of_mul_eq hD_pos.ne' (by linarith)
    rw [hfib']
    ring
  have hLHS_each : ∀ γ ∈ Λ,
      (1 - (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ K) * (D : ℝ) ^ Λ.card ≤
      ((Finset.univ.filter (fun f : Λ → Fin D => hit γ f)).card : ℝ) := by
    intro γ hγ
    obtain ⟨P, hPsub, hPl, hPdis, hPspan⟩ := hwit γ hγ
    set Bad := Finset.univ.filter (fun f : Λ → Fin D =>
      ∀ j : Fin K, ∃ x : Λ, x.1 ∈ P j ∧ f x ≠ ⟨0, hD⟩)
    set Good := Finset.univ.filter (fun f : Λ → Fin D => hit γ f)
    have hcompl : ∀ f : Λ → Fin D, f ∉ Good → f ∈ Bad := by
      intro f hnf
      rw [Finset.mem_filter] at hnf ⊢
      refine ⟨Finset.mem_univ _, fun j => ?_⟩
      by_contra h
      push Not at h
      have hPj_sub : P j ⊆ sub f := by
        intro x hx
        exact Finset.mem_map.mpr ⟨⟨x, hPsub j hx⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ⟨x, hPsub j hx⟩ hx⟩, rfl⟩
      exact hnf ⟨Finset.mem_univ _, inSpan_mono hPj_sub (hPspan j)⟩
    have htot : (Fintype.card (Λ → Fin D) : ℝ) ≤ (Good.card : ℝ) + (Bad.card : ℝ) := by
      have hu : (Finset.univ : Finset (Λ → Fin D)) ⊆ Good ∪ Bad := by
        intro f _
        by_cases hg : f ∈ Good
        · exact Finset.mem_union_left _ hg
        · exact Finset.mem_union_right _ (hcompl f hg)
      have hnat : Fintype.card (Λ → Fin D) ≤ Good.card + Bad.card :=
        (Finset.card_le_card hu).trans (Finset.card_union_le Good Bad)
      exact_mod_cast hnat
    have hcard_all : (Fintype.card (Λ → Fin D) : ℝ) = (D : ℝ) ^ Λ.card := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow]
    have hbad := avoid_count_le D hD l K Λ P hPsub hPl hPdis
    linarith
  have hLHS : (1 - (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ K) * (Λ.card : ℝ) * (D : ℝ) ^ Λ.card ≤
      ∑ f : Λ → Fin D, ((Λ.filter (fun γ => hit γ f)).card : ℝ) := by
    have hswap : (∑ f : Λ → Fin D, ((Λ.filter (fun γ => hit γ f)).card : ℝ)) =
        ∑ γ ∈ Λ, ((Finset.univ.filter (fun f : Λ → Fin D => hit γ f)).card : ℝ) := by
      norm_cast
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap]
    calc (1 - (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ K) * (Λ.card : ℝ) * (D : ℝ) ^ Λ.card
        = ∑ _γ ∈ Λ, (1 - (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ K) * (D : ℝ) ^ Λ.card := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ γ ∈ Λ, ((Finset.univ.filter (fun f : Λ → Fin D => hit γ f)).card : ℝ) :=
          Finset.sum_le_sum hLHS_each
  have hDpow : (0 : ℝ) < (D : ℝ) ^ Λ.card := by positivity
  exact le_of_mul_le_mul_right ((hLHS.trans hsum_le).trans_eq hRHS) hDpow

/-- If inserting `γ ∉ B` breaks `IsRDis r`, then `γ` lies in the length-`(r - 1)` span of some
subset `π ⊆ B` of size at most `r - 1`. -/
private lemma exists_inSpan_of_not_isRDis {r : ℕ} (hr : 1 ≤ r) {B : Finset ℕ} {γ : ℕ}
    (hγB : γ ∉ B) (hB : IsRDis r B) (hnot : ¬ IsRDis r (insert γ B)) :
    ∃ π : Finset ℕ, π ⊆ B ∧ π.card ≤ r - 1 ∧ InSpan (r - 1) π γ := by
  unfold IsRDis at hnot
  push Not at hnot
  obtain ⟨T, hTsub, hTcard, hTnot⟩ := hnot
  unfold Set.IsDissociated Set.InjOn at hTnot
  push Not at hTnot
  obtain ⟨U, hUT, V, hVT, hsum, hne⟩ := hTnot
  have hUsub : U ⊆ T := Finset.coe_subset.mp hUT
  have hVsub : V ⊆ T := Finset.coe_subset.mp hVT
  set U' : Finset ℕ := U \ V
  set V' : Finset ℕ := V \ U
  have hdis : Disjoint U' V' :=
    Finset.disjoint_left.mpr (fun x h1 h2 => (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1)
  have hU'T : U' ⊆ T := Finset.sdiff_subset.trans hUsub
  have hV'T : V' ⊆ T := Finset.sdiff_subset.trans hVsub
  have hne' : U' ≠ V' := by
    intro heq
    have hU'e : U' = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      exact Finset.disjoint_left.mp hdis hx (heq ▸ hx)
    have hV'e : V' = ∅ := heq.symm.trans hU'e
    exact hne (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hU'e)
      (Finset.sdiff_eq_empty_iff_subset.mp hV'e))
  have hsum' : ∑ u ∈ U', u = ∑ v ∈ V', v := by
    have h1 : (∑ u ∈ U', u) + (∑ u ∈ U ∩ V, u) = ∑ u ∈ U, u := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter U V), Finset.sdiff_union_inter]
    have h2 : (∑ v ∈ V', v) + (∑ v ∈ V ∩ U, v) = ∑ v ∈ V, v := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter V U), Finset.sdiff_union_inter]
    rw [Finset.inter_comm] at h2
    omega
  have hcard_uv : U'.card + V'.card ≤ r := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact (Finset.card_le_card (Finset.union_subset hU'T hV'T)).trans hTcard
  have hγ_mem : γ ∈ U' ∨ γ ∈ V' := by
    by_contra hno
    push Not at hno
    have hsubB : U' ∪ V' ⊆ B := by
      intro x hx
      have hxi : x ∈ insert γ B := hTsub (Finset.union_subset hU'T hV'T hx)
      rcases Finset.mem_insert.mp hxi with rfl | hxB
      · rcases Finset.mem_union.mp hx with h1 | h2
        · exact (hno.1 h1).elim
        · exact (hno.2 h2).elim
      · exact hxB
    have hdisUV := hB (U' ∪ V') hsubB
      ((Finset.card_le_card (Finset.union_subset hU'T hV'T)).trans hTcard)
    exact hne' (hdisUV (Finset.coe_subset.mpr Finset.subset_union_left)
      (Finset.coe_subset.mpr Finset.subset_union_right) hsum')
  have hbuild : ∀ (A₁ A₂ : Finset ℕ), Disjoint A₁ A₂ → A₁ ⊆ insert γ B → A₂ ⊆ insert γ B →
      A₁.card + A₂.card ≤ r → ∑ a ∈ A₁, a = ∑ b ∈ A₂, b → γ ∈ A₁ →
      ∃ π : Finset ℕ, π ⊆ B ∧ π.card ≤ r - 1 ∧ InSpan (r - 1) π γ := by
    intro A₁ A₂ hdisA hA₁ hA₂ hcardA hsumA hγA₁
    set X : Finset ℕ := A₁.erase γ
    set Y : Finset ℕ := A₂
    have hXB : X ⊆ B := by
      intro x hx
      have hne_x : x ≠ γ := (Finset.mem_erase.mp hx).1
      exact (Finset.mem_insert.mp (hA₁ (Finset.mem_of_mem_erase hx))).resolve_left hne_x
    have hYB : Y ⊆ B := by
      intro y hy
      have hne_y : y ≠ γ := fun h => Finset.disjoint_left.mp hdisA hγA₁ (h ▸ hy)
      exact (Finset.mem_insert.mp (hA₂ hy)).resolve_left hne_y
    have hdisXY : Disjoint X Y := hdisA.mono_left (Finset.erase_subset _ _)
    have hcardXY : X.card + Y.card ≤ r - 1 := by
      have he : X.card + 1 = A₁.card := Finset.card_erase_add_one hγA₁
      omega
    have hsumXY : γ + ∑ a ∈ X, a = ∑ b ∈ Y, b := by
      rw [Finset.add_sum_erase A₁ (fun a => a) hγA₁]
      exact hsumA
    refine ⟨X ∪ Y, Finset.union_subset hXB hYB, ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hdisXY]
      exact hcardXY
    · exact ⟨X, Y, Finset.subset_union_left, Finset.subset_union_right, hdisXY, hcardXY, hsumXY⟩
  rcases hγ_mem with h1 | h2
  · exact hbuild U' V' hdis (hU'T.trans hTsub) (hV'T.trans hTsub) hcard_uv hsum' h1
  · exact hbuild V' U' hdis.symm (hV'T.trans hTsub) (hU'T.trans hTsub) (by omega) hsum'.symm h2

/-- Strong induction on `|Λ|` producing a pairwise-disjoint `K`-partition into `IsRDis r` parts. -/
private lemma exists_k_partition (F : Finset ℕ) (r l D K : ℕ) (hr : 3 ≤ r) (hl : l = r - 1)
    (hD : 0 < D) (C : ℝ)
    (hbound : ∀ A' : Finset ℕ, A' ⊆ F → ((F.filter (InSpan l A')).card : ℝ) ≤ C * (A'.card : ℝ))
    (hstrict : C / (D : ℝ) < 1 - (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ K) :
    ∀ n : ℕ, ∀ Λ ⊆ F, Λ.card = n →
      ∃ B : Fin K → Finset ℕ, (∀ i, B i ⊆ Λ) ∧ (∀ x ∈ Λ, ∃ i, x ∈ B i) ∧
        Pairwise (fun i j => Disjoint (B i) (B j)) ∧ ∀ i, IsRDis r (B i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Λ hΛF hΛcard
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hΛe : Λ = ∅ := Finset.card_eq_zero.mp hΛcard
      subst hΛe
      refine ⟨fun _ => ∅, fun _ => Finset.empty_subset _, fun _ h => (Finset.notMem_empty _ h).elim,
        fun _ _ _ => Finset.disjoint_empty_left _, fun _ T hT _ => ?_⟩
      have hTe : T = ∅ := Finset.subset_empty.mp hT
      subst hTe
      intro U hU V hV _
      have hUe : U = ∅ := Finset.subset_empty.mp (Finset.coe_subset.mp hU)
      have hVe : V = ∅ := Finset.subset_empty.mp (Finset.coe_subset.mp hV)
      rw [hUe, hVe]
    · by_contra hno
      have hwit : ∀ γ ∈ Λ, ∃ P : Fin K → Finset ℕ, (∀ j, P j ⊆ Λ) ∧ (∀ j, (P j).card ≤ l) ∧
          Pairwise (fun i j => Disjoint (P i) (P j)) ∧ ∀ j, InSpan l (P j) γ := by
        intro γ hγ
        have herase_card : (Λ.erase γ).card < n := by
          rw [Finset.card_erase_of_mem hγ, hΛcard]
          omega
        obtain ⟨A, hAsub, hAcov, hAdis, hArdis⟩ :=
          ih (Λ.erase γ).card herase_card (Λ.erase γ) ((Finset.erase_subset _ _).trans hΛF) rfl
        have hfail : ∀ j : Fin K, ¬ IsRDis r (insert γ (A j)) := by
          intro j hok
          apply hno
          let B' : Fin K → Finset ℕ := Function.update A j (insert γ (A j))
          refine ⟨B', ?_, ?_, ?_, ?_⟩
          · intro i
            by_cases hij : i = j
            · subst hij
              simp only [B', Function.update_self]
              exact Finset.insert_subset hγ ((hAsub i).trans (Finset.erase_subset _ _))
            · simp only [B', Function.update_of_ne hij]
              exact (hAsub i).trans (Finset.erase_subset _ _)
          · intro x hx
            by_cases hxγ : x = γ
            · subst hxγ
              exact ⟨j, by simp [B']⟩
            · obtain ⟨i, hi⟩ := hAcov x (Finset.mem_erase.mpr ⟨hxγ, hx⟩)
              by_cases hij : i = j
              · subst hij
                exact ⟨i, by simp [B', hi]⟩
              · exact ⟨i, by simp [B', hij, hi]⟩
          · intro i₁ i₂ hne
            by_cases h1 : i₁ = j
            · subst h1
              simp only [B', Function.update_self, Function.update_of_ne hne.symm]
              have hγnot : γ ∉ A i₂ := fun h => (Finset.mem_erase.mp (hAsub i₂ h)).1 rfl
              exact Finset.disjoint_insert_left.mpr ⟨hγnot, hAdis hne⟩
            · by_cases h2 : i₂ = j
              · subst h2
                simp only [B', Function.update_self, Function.update_of_ne h1]
                have hγnot : γ ∉ A i₁ := fun h => (Finset.mem_erase.mp (hAsub i₁ h)).1 rfl
                exact Finset.disjoint_insert_right.mpr ⟨hγnot, hAdis hne⟩
              · simp only [B', Function.update_of_ne h1, Function.update_of_ne h2]
                exact hAdis hne
          · intro i
            by_cases hij : i = j
            · subst hij
              simpa [B'] using hok
            · simpa [B', hij] using hArdis i
        have hex : ∀ j : Fin K, ∃ π : Finset ℕ, π ⊆ A j ∧ π.card ≤ l ∧ InSpan l π γ := by
          intro j
          have hγnot : γ ∉ A j := fun h => (Finset.mem_erase.mp (hAsub j h)).1 rfl
          simpa [← hl] using exists_inSpan_of_not_isRDis (by omega : 1 ≤ r) hγnot (hArdis j) (hfail j)
        choose P hPsub hPl hPspan using hex
        refine ⟨P, fun j => (hPsub j).trans ((hAsub j).trans (Finset.erase_subset _ _)), hPl,
          fun i j hij => (hAdis hij).mono (hPsub i) (hPsub j), hPspan⟩
      have hboundΛ : ∀ A' : Finset ℕ, A' ⊆ Λ →
          ((Λ.filter (InSpan l A')).card : ℝ) ≤ C * (A'.card : ℝ) := by
        intro A' hA'
        have hsubF : Λ.filter (InSpan l A') ⊆ F.filter (InSpan l A') :=
          Finset.filter_subset_filter _ hΛF
        exact (Nat.cast_le.mpr (Finset.card_le_card hsubF)).trans (hbound A' (hA'.trans hΛF))
      have havg := bourgain_averaging Λ D l K hD C hboundΛ hwit
      have hposΛ : (0 : ℝ) < (Λ.card : ℝ) := by exact_mod_cast (hΛcard ▸ hn)
      have hle := le_of_mul_le_mul_right havg hposΛ
      linarith

end OMA.Erdos774H1

open scoped Classical in
theorem OMA.solution : OMA.R_Erdos774_erdos_774_R1_H2_R1.H1 := by
  intro δ hδ r hr
  set l : ℕ := r - 1
  have hl_pos : 1 ≤ l := by omega
  set C : ℝ := (2 * (8 * l + 2) : ℝ) / δ
  set D : ℕ := ⌈2 * C⌉₊ + 1
  have hD_pos : 0 < D := Nat.succ_pos _
  set K : ℕ := D ^ l
  have hK_pos : 0 < K := Nat.pow_pos hD_pos
  have hCD : C / (D : ℝ) < 1 / 2 := by
    have hD_gt : 2 * C < (D : ℝ) := by
      have hceil : 2 * C ≤ (⌈2 * C⌉₊ : ℝ) := Nat.le_ceil _
      push_cast [D]
      linarith
    rw [div_lt_iff₀ (by exact_mod_cast hD_pos : (0 : ℝ) < D)]
    linarith
  have hprob : (1 / 2 : ℝ) < 1 - (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ K := by
    have hKpos_r : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
    have hbase : 1 - (1 : ℝ) / (K : ℝ) ≤ Real.exp (-(1 / (K : ℝ))) := by
      linarith [Real.add_one_le_exp (-(1 / (K : ℝ)))]
    have hbase_nn : 0 ≤ 1 - (1 : ℝ) / (K : ℝ) := by
      have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
      rw [sub_nonneg, div_le_one hKpos_r]
      exact hK1
    have hpow : (1 - (1 : ℝ) / (D : ℝ) ^ l) ^ K ≤ Real.exp (-1) := by
      have hKe : (D : ℝ) ^ l = (K : ℝ) := by exact_mod_cast rfl
      rw [hKe]
      calc (1 - (1 : ℝ) / (K : ℝ)) ^ K
          ≤ (Real.exp (-(1 / (K : ℝ)))) ^ K := pow_le_pow_left₀ hbase_nn hbase K
        _ = Real.exp ((K : ℝ) * (-(1 / (K : ℝ)))) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (-1) := by
          congr 1
          field_simp
    have hexp_lt : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num
      linarith [Real.exp_one_gt_d9]
    linarith
  refine ⟨K, hK_pos, fun F hextract => ?_⟩
  have hbound : ∀ A' : Finset ℕ, A' ⊆ F →
      ((F.filter (OMA.Erdos774H1.InSpan l A')).card : ℝ) ≤ C * (A'.card : ℝ) :=
    fun A' _ => OMA.Erdos774H1.inSpan_filter_card_le l hl_pos δ hδ F hextract A'
  obtain ⟨B, hBsub, hBcov, _, hBrdis⟩ :=
    OMA.Erdos774H1.exists_k_partition F r l D K hr rfl hD_pos C hbound
      (hCD.trans hprob) F.card F Finset.Subset.rfl rfl
  exact ⟨B, hBsub, hBcov, hBrdis⟩
