import FormalConjectures.ErdosProblems.«1186»
import Mathlib

/-!
A cut in the directed graph of possible (endpoint, midpoint) pairs changes the mixed-pair
count by its signed weight. Complementary cuts have the same weight. Bound this weight
on the two sides of the 2/5 threshold of Carlos Toledo's proof, then evaluate the reference
colouring and pass from multiples of 1096 to all interval sizes. The 130-cell and 146-cell
certificates for the two cut estimates are formalized in Chandler Snively's release v1.0.0,
github.com/dreadpiratechan/erdos-1186, Theorem C (aiXiv:2610.02762).
The ordered-pair counting lemmas below are from the accepted PRS bounds step by @ptc-prover-bot.
The final finite upper-bound statement and subsequence argument are adapted from @dk8827's
PRS bounds reduction. Reduction and signed-cut argument by @ellisjr.
-/
open Finset Filter Erdos1186
open scoped BigOperators Classical

namespace OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1

/-- The gain from flipping a cut whose smaller side contains at most two fifths of the interval.
A severed same-colour reference pair contributes one, a severed mixed pair contributes minus one. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℕ, 1 ≤ w → ∀ d : ℕ → Bool,
    let n := 1096*w
    let ref := fun x : ℕ =>
      let b := (x - 1) / (2*w)
      b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
      (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
    let R := ((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ =>
      p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1 + n)
    let t := ((Icc 1 n).filter (fun x => d x = true)).card
    5 * min t (n - t) ≤ 2*n →
      ((∑ p ∈ R, (if d p.1 = d p.2 then 0 else
        if ref p.1 = ref p.2 then 1 else -1 : ℤ) : ℤ) : ℝ) ≤ C * n

/-- The signed cut estimate when the smaller side contains at least two fifths of the interval. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℕ, 1 ≤ w → ∀ d : ℕ → Bool,
    let n := 1096*w
    let ref := fun x : ℕ =>
      let b := (x - 1) / (2*w)
      b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
      (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
    let R := ((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ =>
      p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1 + n)
    let t := ((Icc 1 n).filter (fun x => d x = true)).card
    2*n ≤ 5 * min t (n - t) →
      ((∑ p ∈ R, (if d p.1 = d p.2 then 0 else
        if ref p.1 = ref p.2 then 1 else -1 : ℤ) : ℤ) : ℝ) ≤ C * n

/-- The mixed endpoint-midpoint pair count of the twelve-block reference colouring. -/
def H3 : Prop :=
  ∀ w : ℕ, 1 ≤ w →
    let n := 1096*w
    let ref := fun x : ℕ =>
      let b := (x - 1) / (2*w)
      b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
      (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
    let R := ((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ =>
      p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1 + n)
    (R.filter (fun p => ref p.1 ≠ ref p.2)).card ≤ 322224 * w^2

/-- The monochromatic progression count of the same twelve-block colouring. -/
def H4 : Prop :=
  ∀ q : ℕ, 0 < q →
    let c := fun x : ℕ =>
      let b := (x - 1) / (2 * q)
      b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
      (274 ≤ b && b < 390) || (449 ≤ b && b < 486) ||
      (514 ≤ b && b < 520)
    monoCount 3 (1096 * q) c ≤ 64116 * q ^ 2


lemma diff_pairs (P : Finset ℕ) (c : ℕ → Bool) :
    2 * ((P ×ˢ P).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2)).card ≤ P.card * P.card := by
  classical
  set R := P.filter (fun a => c a = true) with hR
  set B := P.filter (fun a => ¬ c a = true) with hB
  have hRB : R.card + B.card = P.card := card_filter_add_card_filter_not _
  have hsub : (P ×ˢ P).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2) ⊆ R ×ˢ B ∪ B ×ˢ R := by
    rintro ⟨a, b⟩ h
    simp only [mem_filter, mem_product] at h
    simp only [hR, hB, mem_union, mem_product, mem_filter]
    obtain ⟨⟨ha, hb⟩, hne⟩ := h
    cases hca : c a <;> cases hcb : c b <;> simp_all
  have h1 := card_le_card hsub
  have h2 := card_union_le (R ×ˢ B) (B ×ˢ R)
  rw [card_product, card_product] at h2
  have h3 : (4 * R.card * B.card : ℤ) ≤ ((R.card : ℤ) + B.card) ^ 2 := by
    nlinarith [sq_nonneg ((R.card : ℤ) - B.card)]
  have h4 : 4 * R.card * B.card ≤ (R.card + B.card) ^ 2 := by exact_mod_cast h3
  rw [hRB] at h4
  nlinarith

theorem main_ineq (n : ℕ) (c : ℕ → Bool) :
    let X := ((Icc 1 n ×ˢ Icc 1 n).filter
      (fun p => c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2 * p.2 ∧ 2 * p.2 ≤ p.1 + n)).card
    (n : ℝ) ^ 2 / 2 ≤ 2 * (monoCount 3 n c : ℝ) + n + X + ((n : ℝ) + 1) ^ 2 / 8 := by
  classical
  intro X
  set P0 := (Icc 1 n).filter (fun a => a % 2 = 0) with hP0
  set P1 := (Icc 1 n).filter (fun a => ¬ a % 2 = 0) with hP1
  set S := P0 ×ˢ P0 ∪ P1 ×ˢ P1 with hS
  have memS : ∀ p ∈ S, 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ n ∧ p.1 % 2 = p.2 % 2 := by
    intro p hp
    simp only [hS, hP0, hP1, mem_union, mem_product, mem_filter, mem_Icc] at hp
    omega
  -- (A) pointwise identity, summed
  have hpt : ∀ p ∈ S, 2 = 2 * (if c p.1 = c ((p.1 + p.2) / 2) ∧ c p.2 = c ((p.1 + p.2) / 2)
      then 1 else 0) + (if c p.1 ≠ c ((p.1 + p.2) / 2) then 1 else 0)
      + (if c p.2 ≠ c ((p.1 + p.2) / 2) then 1 else 0) + (if c p.1 ≠ c p.2 then 1 else 0) := by
    intro p _
    generalize c p.1 = x
    generalize c p.2 = y
    generalize c ((p.1 + p.2) / 2) = z
    cases x <;> cases y <;> cases z <;> decide
  have hsum := Finset.sum_congr rfl hpt
  simp only [sum_add_distrib, ← mul_sum, sum_boole, sum_const, smul_eq_mul, Nat.cast_id] at hsum
  set T := S.filter (fun p => c p.1 = c ((p.1 + p.2) / 2) ∧ c p.2 = c ((p.1 + p.2) / 2)) with hT
  set E1 := S.filter (fun p => c p.1 ≠ c ((p.1 + p.2) / 2)) with hE1
  set E2 := S.filter (fun p => c p.2 ≠ c ((p.1 + p.2) / 2)) with hE2
  set D := S.filter (fun p => c p.1 ≠ c p.2) with hD
  set Xs := (Icc 1 n ×ˢ Icc 1 n).filter
      (fun p : ℕ × ℕ => c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2 * p.2 ∧ 2 * p.2 ≤ p.1 + n) with hXs
  -- (B)
  have hB1 : E1.card ≤ X := by
    apply card_le_card_of_injOn (fun p => (p.1, (p.1 + p.2) / 2))
    · intro p hp
      rw [coe_filter, Set.mem_ofPred_eq] at hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := memS p hp.1
      simp only [mem_coe, hXs, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨h1, h2⟩, by omega, by omega⟩, hp.2, by omega, by omega⟩
    · intro p hp q hq hpq
      rw [coe_filter, Set.mem_ofPred_eq] at hp hq
      have := memS p hp.1
      have := memS q hq.1
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (by omega)
  have hB2 : E2.card ≤ X := by
    apply card_le_card_of_injOn (fun p => (p.2, (p.1 + p.2) / 2))
    · intro p hp
      rw [coe_filter, Set.mem_ofPred_eq] at hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := memS p hp.1
      simp only [mem_coe, hXs, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨h3, h4⟩, by omega, by omega⟩, hp.2, by omega, by omega⟩
    · intro p hp q hq hpq
      rw [coe_filter, Set.mem_ofPred_eq] at hp hq
      have := memS p hp.1
      have := memS q hq.1
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext (by omega) hpq.1
  -- (C)
  set Ms := (Icc 1 n ×ˢ Icc 1 n).filter (fun p : ℕ × ℕ =>
      p.1 + (3 - 1) * p.2 ≤ n ∧ ∀ i < 3, c (p.1 + i * p.2) = c p.1) with hMs
  have hM : monoCount 3 n c = Ms.card := by rw [hMs]; unfold monoCount; convert rfl
  have hlt : (T.filter (fun p => p.1 < p.2)).card ≤ Ms.card := by
    apply card_le_card_of_injOn (fun p => (p.1, (p.2 - p.1) / 2))
    · intro p hp
      simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp
      obtain ⟨⟨hpS, hc1, hc2⟩, hlt⟩ := hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := memS p hpS
      simp only [mem_coe, hMs, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨h1, h2⟩, by omega, by omega⟩, by omega, ?_⟩
      intro i hi
      interval_cases i
      · simp
      · rw [show p.1 + 1 * ((p.2 - p.1) / 2) = (p.1 + p.2) / 2 by omega]; exact hc1.symm
      · rw [show p.1 + 2 * ((p.2 - p.1) / 2) = p.2 by omega, hc2, hc1]
    · intro p hp q hq hpq
      simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp hq
      have := memS p hp.1.1
      have := memS q hq.1.1
      have := hp.2
      have := hq.2
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (by omega)
  have hgt : (T.filter (fun p => p.2 < p.1)).card ≤ Ms.card := by
    apply card_le_card_of_injOn (fun p => (p.2, (p.1 - p.2) / 2))
    · intro p hp
      simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp
      obtain ⟨⟨hpS, hc1, hc2⟩, hgt⟩ := hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := memS p hpS
      simp only [mem_coe, hMs, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨h3, h4⟩, by omega, by omega⟩, by omega, ?_⟩
      intro i hi
      interval_cases i
      · simp
      · rw [show p.2 + 1 * ((p.1 - p.2) / 2) = (p.1 + p.2) / 2 by omega]; exact hc2.symm
      · rw [show p.2 + 2 * ((p.1 - p.2) / 2) = p.1 by omega, hc1, hc2]
    · intro p hp q hq hpq
      simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp hq
      have := memS p hp.1.1
      have := memS q hq.1.1
      have := hp.2
      have := hq.2
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext (by omega) hpq.1
  have hdiag : (T.filter (fun p => p.1 = p.2)).card ≤ n := by
    calc (T.filter (fun p => p.1 = p.2)).card ≤ (Icc 1 n).card := by
          apply card_le_card_of_injOn (fun p => p.1)
          · intro p hp
            simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp
            obtain ⟨h1, h2, -⟩ := memS p hp.1.1
            simp only [mem_coe, mem_Icc]
            exact ⟨h1, h2⟩
          · intro p hp q hq hpq
            simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp hq
            exact Prod.ext hpq (by rw [← hp.2, ← hq.2]; exact hpq)
      _ = n := by simp
  have hTsplit : T.card ≤ (T.filter (fun p => p.1 = p.2)).card +
      (T.filter (fun p => p.1 < p.2)).card + (T.filter (fun p => p.2 < p.1)).card := by
    calc T.card ≤ ((T.filter (fun p => p.1 = p.2)) ∪ (T.filter (fun p => p.1 < p.2)) ∪
          (T.filter (fun p => p.2 < p.1))).card := by
          apply card_le_card
          intro p hp
          simp only [mem_union, mem_filter]
          rcases lt_trichotomy p.1 p.2 with h | h | h
          · exact Or.inl (Or.inr ⟨hp, h⟩)
          · exact Or.inl (Or.inl ⟨hp, h⟩)
          · exact Or.inr ⟨hp, h⟩
      _ ≤ _ := by
          refine (card_union_le _ _).trans ?_
          exact Nat.add_le_add_right (card_union_le _ _) _
  have hTle : T.card ≤ n + 2 * monoCount 3 n c := by rw [hM]; omega
  -- (D), (E)
  have hdisj : Disjoint (P0 ×ˢ P0) (P1 ×ˢ P1) := by
    rw [disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [hP0, hP1, mem_product, mem_filter] at h1 h2
    omega
  have hScard : S.card = P0.card * P0.card + P1.card * P1.card := by
    rw [hS, card_union_of_disjoint hdisj, card_product, card_product]
  have hP : P0.card + P1.card = n := by
    rw [hP0, hP1, card_filter_add_card_filter_not]
    simp
  have hDle : 2 * D.card ≤ S.card := by
    have hDsub : D ⊆ ((P0 ×ˢ P0).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2)) ∪
        ((P1 ×ˢ P1).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2)) := by
      intro p hp
      simp only [hD, hS, mem_filter, mem_union] at hp ⊢
      rcases hp.1 with h | h
      · exact Or.inl ⟨h, hp.2⟩
      · exact Or.inr ⟨h, hp.2⟩
    have := card_le_card hDsub
    have := card_union_le ((P0 ×ˢ P0).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2))
      ((P1 ×ˢ P1).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2))
    have := diff_pairs P0 c
    have := diff_pairs P1 c
    omega
  have hSge : n ^ 2 ≤ 2 * S.card := by
    rw [hScard, ← hP]
    nlinarith [sq_nonneg ((P0.card : ℤ) - P1.card)]
  -- combine
  have key : 4 * n ^ 2 ≤ 16 * monoCount 3 n c + 8 * n + 8 * X + (n + 1) ^ 2 := by
    nlinarith
  have keyR : (4 : ℝ) * (n : ℝ) ^ 2 ≤
      16 * (monoCount 3 n c : ℝ) + 8 * n + 8 * X + ((n : ℝ) + 1) ^ 2 := by
    exact_mod_cast key
  linarith


/-- Cutting exactly the vertices whose colours differ from the reference telescopes to the
difference of the two mixed-edge counts, for any finite set of directed edges. -/
lemma switch_identity (R : Finset (ℕ × ℕ)) (c b : ℕ → Bool) :
    (((R.filter (fun p => c p.1 ≠ c p.2)).card : ℕ) : ℤ) =
    ((R.filter (fun p => b p.1 ≠ b p.2)).card : ℤ) +
      ∑ p ∈ R, (if (c p.1 != b p.1) = (c p.2 != b p.2) then 0 else
        if b p.1 = b p.2 then 1 else -1 : ℤ) := by
  classical
  induction R using Finset.induction_on with
  | empty => simp
  | @insert p R hp ih =>
    rw [Finset.sum_insert hp]
    have hc : p ∉ R.filter (fun q => c q.1 ≠ c q.2) := by simp [hp]
    have hb : p ∉ R.filter (fun q => b q.1 ≠ b q.2) := by simp [hp]
    cases hc₁ : c p.1 <;> cases hc₂ : c p.2 <;> cases hb₁ : b p.1 <;> cases hb₂ : b p.2 <;>
      simp [Finset.filter_insert, hc₁, hc₂, hb₁, hb₂, hc, hb, ih] <;> ring

lemma finite_lower (near : H1) (far : H2) (pattern : H3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℕ, 1 ≤ w → ∀ c : ℕ → Bool,
      (117/2192 : ℝ) * ((1096*w : ℕ) : ℝ)^2 - K * (1096*w : ℕ) ≤
        (monoCount 3 (1096*w) c : ℝ) := by
  obtain ⟨C, hC, near_cut⟩ := near
  obtain ⟨D, hD, far_cut⟩ := far
  let E := max C D
  have hE : 0 ≤ E := hC.trans (le_max_left C D)
  refine ⟨E + 2, by linarith, fun w hw c => ?_⟩
  let n := 1096*w
  let b := fun x : ℕ =>
    let j := (x-1)/(2*w)
    j < 28 || (34 ≤ j && j < 62) || (99 ≤ j && j < 158) ||
    (274 ≤ j && j < 390) || (449 ≤ j && j < 486) || (514 ≤ j && j < 520)
  let R := ((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ => p.1+1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1+n)
  let d := fun x => c x != b x
  let t := ((Icc 1 n).filter (fun x => d x = true)).card
  let gain := ∑ p ∈ R, (if d p.1 = d p.2 then 0 else if b p.1 = b p.2 then 1 else -1 : ℤ)
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hgain : (gain : ℝ) ≤ E * n := by
    rcases le_total (5 * min t (n - t)) (2*n) with h | h
    · exact (near_cut w hw d h).trans (mul_le_mul_of_nonneg_right (le_max_left C D) hn₀)
    · exact (far_cut w hw d h).trans (mul_le_mul_of_nonneg_right (le_max_right C D) hn₀)
  have h0 : (((R.filter (fun p => b p.1 ≠ b p.2)).card : ℕ) : ℝ) ≤ 322224*(w : ℝ)^2 := by
    exact_mod_cast pattern w hw
  have hswitch : (((R.filter (fun p => c p.1 ≠ c p.2)).card : ℕ) : ℝ) =
      (R.filter (fun p => b p.1 ≠ b p.2)).card + (gain : ℝ) := by
    exact_mod_cast switch_identity R c b
  have hcount := main_ineq n c
  have hsets : ((Icc 1 n ×ˢ Icc 1 n).filter (fun p =>
      c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1+n)) =
        R.filter (fun p => c p.1 ≠ c p.2) := by
    ext p
    simp only [R, mem_filter]
    tauto
  dsimp only at hcount
  rw [hsets] at hcount
  have hn : (n : ℝ) = 1096*(w : ℝ) := by dsimp [n]; push_cast; ring
  have hpos : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by dsimp [n]; omega)
  change (117/2192 : ℝ) * (n : ℝ)^2 - (E + 2) * n ≤ (monoCount 3 n c : ℝ)
  have hnonneg : 0 ≤ E * (n : ℝ) := mul_nonneg hE hn₀
  nlinarith only [hcount, hswitch, h0, hgain, hnonneg, hpos, congrArg (fun z : ℝ => z^2) hn]

private theorem count_mono {m n : ℕ} (hmn : m ≤ n) (c : ℕ → Bool) :
    monoCount 3 m c ≤ monoCount 3 n c := by
  apply card_le_card
  intro p hp
  simp only [mem_filter, mem_product, mem_Icc] at hp ⊢
  exact ⟨⟨⟨hp.1.1.1, hp.1.1.2.trans hmn⟩, ⟨hp.1.2.1, hp.1.2.2.trans hmn⟩⟩,
    hp.2.1.trans hmn, hp.2.2⟩

private theorem all_sizes (K : ℝ) (hK : 0 ≤ K)
    (hfin : ∀ w : ℕ, 1 ≤ w → ∀ c : ℕ → Bool,
      (117/2192 : ℝ) * ((1096*w : ℕ) : ℝ)^2 - K * (1096*w : ℕ) ≤
        (monoCount 3 (1096*w) c : ℝ))
    (N : ℕ) (hN : 1096 ≤ N) :
    (117/2192 : ℝ) * (N : ℝ)^2 - (117 + K) * N ≤ (minMonoCount 3 N : ℝ) := by
  set w := N / 1096 with hw
  have h1 : 1 ≤ w := by omega
  have h2 : 1096*w ≤ N := by omega
  have h3 : N < 1096*w + 1096 := by omega
  have hex : Set.Nonempty {m : ℕ | ∃ c : ℕ → Bool, monoCount 3 N c = m} :=
    ⟨_, fun _ => true, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Bool, monoCount 3 N c = minMonoCount 3 N := csInf_mem hex
  have hm : (monoCount 3 (1096*w) c : ℝ) ≤ minMonoCount 3 N := by
    rw [← hc]
    exact_mod_cast count_mono h2 c
  have hlow := hfin w h1 c
  have hu : ((1096*w : ℕ) : ℝ) ≤ N := by exact_mod_cast h2
  have hl : (N : ℝ) < ((1096*w : ℕ) : ℝ) + 1096 := by exact_mod_cast h3
  have hn' : (1096 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : ((N : ℝ) - 1096)^2 ≤ ((1096*w : ℕ) : ℝ)^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  nlinarith only [hlow, hm, hs, mul_le_mul_of_nonneg_left hu hK]

private theorem count_le_sq (n : ℕ) (c : ℕ → Bool) : monoCount 3 n c ≤ n ^ 2 := by
  unfold monoCount
  exact (card_filter_le _ _).trans_eq (by simp [pow_two])

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos1186.erdos_1186.variants.prs_conjecture := by
  intro near far referenceCount upper
  obtain ⟨K, hK, hfin⟩ := finite_lower near far referenceCount
  let F (n : ℕ) := (minMonoCount 3 n : ℝ) / (n : ℝ)^2
  change liminf F atTop = (117/2192 : ℝ)
  have hF₀ : IsBoundedUnder (· ≥ ·) atTop F := isBoundedUnder_of_eventually_ge
    (a := 0) (Eventually.of_forall fun n => by dsimp only [F]; positivity)
  have hF₁ : IsBoundedUnder (· ≤ ·) atTop F := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have h := (minMonoCount_le 3 n (fun _ => true)).trans (count_le_sq n (fun _ => true))
    have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (div_le_iff₀ (sq_pos_of_pos hp)).2
    norm_num
    exact_mod_cast h
  apply le_antisymm
  · apply liminf_le_of_frequently_le _ hF₀
    rw [frequently_atTop]
    intro N
    let q := max 1 N
    have hq : 0 < q := zero_lt_one.trans_le (le_max_left 1 N)
    refine ⟨1096 * q, ?_, ?_⟩
    · have h := le_max_right 1 N
      dsimp only [q]
      omega
    · let c := fun x : ℕ =>
        let b := (x - 1) / (2 * q)
        b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
        (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
      have h := (minMonoCount_le 3 (1096*q) c).trans (upper q hq)
      have hn : (0 : ℝ) < ((1096*q : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (by decide : 0 < 1096) hq
      apply (div_le_iff₀ (sq_pos_of_pos hn)).2
      push_cast
      have h' : (minMonoCount 3 (1096*q) : ℝ) ≤ 64116 * (q : ℝ)^2 := by exact_mod_cast h
      nlinarith only [h']
  · apply le_of_forall_lt_imp_le_of_dense
    intro x hx
    apply le_liminf_of_le hF₁.isCoboundedUnder_ge
    let d : ℝ := 117/2192 - x
    have hd : 0 < d := sub_pos.2 hx
    obtain ⟨N, hN⟩ := exists_nat_gt ((117 + K) / d)
    filter_upwards [eventually_ge_atTop (max N 1096)] with n hn
    have hn₁ := (le_max_right N 1096).trans hn
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have he : 117 + K ≤ (n : ℝ) * d := (div_le_iff₀ hd).1 (hN.le.trans
      (show (N : ℝ) ≤ n by exact_mod_cast ((le_max_left N 1096).trans hn)))
    have h := mul_le_mul_of_nonneg_right he hn₀.le
    change x ≤ (minMonoCount 3 n : ℝ) / (n : ℝ)^2
    apply (le_div_iff₀ (sq_pos_of_pos hn₀)).2
    dsimp only [d] at h
    nlinarith only [h, all_sizes K hK hfin n hn₁]
end OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1
