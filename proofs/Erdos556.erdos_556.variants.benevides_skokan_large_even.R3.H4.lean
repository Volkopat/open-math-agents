import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R3
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Option.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Preorder.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic

/-!
Erdős Problem 556: colour-permuted host stability, proved independently of
all three extremal absorption theorems. Credit: @fqlx.

Mathematical sources:
* F. S. Benevides and J. Skokan, The 3-colored Ramsey number of even cycles,
  Journal of Combinatorial Theory, Series B 99 (2009), 690–708.
* S. Letzter, An improvement on Łuczak's connected matchings method.

Code provenance (the original notices are retained below):
* @green-notes, accepted PR3417: connected-matching cycle embedding.
* @bmander, PR13771: simultaneous regularity and density lifting; underlying
  Mathlib regularity work by Yaël Dillies and Bhavik Mehta, Apache-2.0.
* @senamakel: original extremal conventions and exact interface.
* @fqlx: finite matching classification, Tutte and saturation arguments,
  completion, quantitative stability, host transfer and this interface.

The proof uses common regularity, connected-matching cycle embedding,
finite stability, and explicit transfer of block sizes and densities.
Every local source module is section-wrapped to preserve its open scopes.
-/

/- Source module: CommonRegularity.lean -/
section PermutedModule0

/-!
Verified extraction of the common-partition and density-pullback lemmas from
PR #13771 by @bmander:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/13771
The proof bodies through the original `end Lift` are retained; only the imports
and outer namespace are changed. This file contains no reduction hypotheses.
The original Mathlib author and Apache-2.0 notices are retained below.
-/

/-
Simultaneous regularity for the large even cycle Ramsey number.

A refinement for one graph gains at least ε⁵/4 of its energy and loses at most ε⁵/25
of the other graph's energy. Iterating the sum gives a common equipartition. Since
the three densities sum to one on disjoint nonempty sets, two regular colours
suffice for a common exceptional set and all three colours. In the EC2 alternative,
passing from unweighted cluster deficits to vertex deficits costs a factor of four.
Portions of the energy argument adapt Mathlib's Regularity/Chunk.lean, Increment.lean and
Lemma.lean. Copyright (c) 2021–2022 Yaël Dillies, Bhavik Mehta. Apache License 2.0.
-/

namespace CommonRegularity

section Energy
open Finpartition Finset Fintype Rel Nat SimpleGraph SzemerediRegularity Function
open scoped SzemerediRegularity.Positivity



variable {α : Type*} [Fintype α] [DecidableEq α] {P : Finpartition (univ : Finset α)}
  {hP : P.IsEquipartition} {G : SimpleGraph α} [DecidableRel G.Adj] {ε : ℝ}
  {U V : Finset α} {hU : U ∈ P.parts} {𝒜 : Finset (Finset α)} {s : Finset α}
private theorem lowerSize (h𝒜 : 𝒜 ⊆ (chunk hP G ε hU).parts) (hs : s ∈ 𝒜) :
    (#𝒜 : ℝ) * #s * ((card α / stepBound #P.parts : ℕ) / ((card α / stepBound #P.parts : ℕ) + 1)) ≤ #(𝒜.sup id) := by
  rw [mul_div_assoc', div_le_iff₀ coe_m_add_one_pos, mul_right_comm]
  gcongr
  · rw [← (ofSubset _ h𝒜 rfl).sum_card_parts, ofSubset_parts, ← cast_mul, cast_le]
    exact card_nsmul_le_sum _ _ _ fun x hx => m_le_card_of_mem_chunk_parts <| h𝒜 hx
  · exact mod_cast card_le_m_add_one_of_mem_chunk_parts (h𝒜 hs)

private theorem sizeRatio [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) :
    ↑1 - ε ^ 5 / ↑50 ≤ ((card α / stepBound #P.parts : ℕ) / ((card α / stepBound #P.parts : ℕ) + 1 : ℝ)) ^ 2 := by
  have : ((card α / stepBound #P.parts : ℕ) : ℝ) / ((card α / stepBound #P.parts : ℕ) + 1) = 1 - 1 / ((card α / stepBound #P.parts : ℕ) + 1) := by
    rw [one_sub_div coe_m_add_one_pos.ne', add_sub_cancel_right]
  rw [this, sub_sq, one_pow, mul_one]
  refine le_trans ?_ (le_add_of_nonneg_right <| sq_nonneg _)
  rw [sub_le_sub_iff_left, ← le_div_iff₀' (show (0 : ℝ) < 2 by simp), div_div,
    one_div_le coe_m_add_one_pos, one_div_div]
  · refine le_trans ?_ (le_add_of_nonneg_right zero_le_one)
    norm_num
    apply hundred_div_ε_pow_five_le_m hPα hPε
  sz_positivity


variable (H : SimpleGraph α) [DecidableRel H.Adj]
private theorem densityAverage [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) :
    (H.edgeDensity (A.biUnion id) (B.biUnion id)) - ε ^ 5 / 50 ≤
    (∑ ab ∈ A.product B, (H.edgeDensity ab.1 ab.2 : ℝ)) / (#A * #B) := by
  have : ↑(H.edgeDensity (A.biUnion id) (B.biUnion id)) - ε ^ 5 / ↑50 ≤
      (↑1 - ε ^ 5 / 50) * H.edgeDensity (A.biUnion id) (B.biUnion id) := by
    rw [sub_mul, one_mul, sub_le_sub_iff_left]
    refine mul_le_of_le_one_right (by sz_positivity) ?_
    exact mod_cast H.edgeDensity_le_one _ _
  refine this.trans ?_
  conv_rhs =>
    simp only [SimpleGraph.edgeDensity_def, sum_div, Rat.cast_div, div_div]
  conv_lhs =>
    rw [SimpleGraph.edgeDensity_def, SimpleGraph.interedges, ← sup_eq_biUnion, ← sup_eq_biUnion,
      Rel.card_interedges_finpartition _ (ofSubset _ hA rfl) (ofSubset _ hB rfl), ofSubset_parts,
      ofSubset_parts]
    simp only [cast_sum, sum_div, mul_sum, Rat.cast_sum, Rat.cast_div,
      mul_div_left_comm ((1 : ℝ) - _)]
  push_cast
  apply sum_le_sum
  simp only [and_imp, Prod.forall, mem_product]
  rintro x y hx hy
  rw [mul_mul_mul_comm, mul_comm (#x : ℝ), mul_comm (#y : ℝ), le_div_iff₀, mul_assoc]
  · refine mul_le_of_le_one_right (cast_nonneg _) ?_
    rw [div_mul_eq_mul_div, ← mul_assoc, mul_assoc]
    refine div_le_one_of_le₀ ?_ (by positivity)
    refine (mul_le_mul_of_nonneg_right (sizeRatio hPα hPε) ?_).trans ?_
    · exact_mod_cast _root_.zero_le
    rw [sq, mul_mul_mul_comm, mul_comm (((card α / stepBound #P.parts : ℕ) : ℝ) / _), mul_comm (((card α / stepBound #P.parts : ℕ) : ℝ) / _)]
    gcongr
    · apply lowerSize hA hx
    · apply lowerSize hB hy
  refine mul_pos (mul_pos ?_ ?_) (mul_pos ?_ ?_) <;> rw [cast_pos, Finset.card_pos]
  exacts [⟨_, hx⟩, nonempty_of_mem_parts _ (hA hx), ⟨_, hy⟩, nonempty_of_mem_parts _ (hB hy)]

private theorem squareAverage [Nonempty α] (hP)
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    (H.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / ↑25 ≤
    ((∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
      (H.edgeDensity ab.1 ab.2 : ℝ)) / ↑16 ^ #P.parts) ^ 2 := by
  obtain hGε | hGε := le_total (H.edgeDensity U V : ℝ) (ε ^ 5 / 50)
  · refine (sub_nonpos_of_le <| (sq_le ?_ ?_).trans <| hGε.trans ?_).trans (sq_nonneg _)
    · exact mod_cast H.edgeDensity_nonneg _ _
    · exact mod_cast H.edgeDensity_le_one _ _
    · exact div_le_div_of_nonneg_left (by sz_positivity) (by simp) (by norm_num)
  rw [← sub_nonneg] at hGε
  have : 0 ≤ ε := by sz_positivity
  calc
    _ = H.edgeDensity U V ^ 2 - 1 * ε ^ 5 / 25 + 0 ^ 10 / 2500 := by ring
    _ ≤ H.edgeDensity U V ^ 2 - H.edgeDensity U V * ε ^ 5 / 25 + ε ^ 10 / 2500 := by
      gcongr; exact mod_cast H.edgeDensity_le_one ..
    _ = (H.edgeDensity U V - ε ^ 5 / 50) ^ 2 := by ring
    _ ≤ _ := by
      gcongr
      have rflU := Subset.refl (chunk hP G ε hU).parts
      have rflV := Subset.refl (chunk hP G ε hV).parts
      refine (le_trans ?_ <| densityAverage H hPα hPε rflU rflV).trans ?_
      · rw [biUnion_parts, biUnion_parts]
      · rw [card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne', ← cast_mul, ← mul_pow, cast_pow]
        norm_cast

theorem cross_chunk [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    (H.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / ↑25 ≤
    (∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
      (H.edgeDensity ab.1 ab.2 : ℝ) ^ 2) / ↑16 ^ #P.parts := by
  apply (squareAverage H (G := G) (hP := hP) hPα hPε hU hV).trans
  have key : (16 : ℝ) ^ #P.parts = #((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts) := by
    rw [card_product, cast_mul, card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne', ←
      cast_mul, ← mul_pow]; norm_cast
  simp_rw [key]
  convert! sum_div_card_sq_le_sum_sq_div_card (α := ℝ)

private theorem distinctPairs_increment :
    P.parts.offDiag.attach.biUnion (fun x : {x // x ∈ P.parts.offDiag} =>
        (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts) ⊆ (increment hP G ε).parts.offDiag := by
  rintro ⟨Ui, Vj⟩
  simp only [increment, mem_offDiag, bind_parts, mem_biUnion, Prod.exists,
    mem_product, mem_attach, true_and, Subtype.exists, and_imp,
    mem_offDiag, forall_exists_index, Ne]
  refine fun U V hUV hUi hVj => ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, ?_⟩
  rintro rfl
  obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hUi
  exact hUV.2.2 (P.disjoint.elim_finset hUV.1 hUV.2.1 i (Finpartition.le _ hUi hi) <|
    Finpartition.le _ hVj hi)

private lemma pairwiseDisjoint_distinctPairs :
    (P.parts.offDiag.attach : Set {x // x ∈ P.parts.offDiag}).PairwiseDisjoint
      (fun x : {x // x ∈ P.parts.offDiag} =>
        (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts) := by
  simp +unfoldPartialApp only [Set.PairwiseDisjoint,
    Function.onFun, Finset.disjoint_left, mem_product]
  rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv₁ huv₂
  rw [mem_offDiag] at hs ht
  obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.1
  obtain ⟨b, hb⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.2
  exact hst <| Subtype.ext <| Prod.ext
    (P.disjoint.elim_finset hs.1 ht.1 a (Finpartition.le _ huv₁.1 ha) <|
      Finpartition.le _ huv₂.1 ha) <|
        P.disjoint.elim_finset hs.2.1 ht.2.1 b (Finpartition.le _ huv₁.2 hb) <|
          Finpartition.le _ huv₂.2 hb

/-- Refining for graph G costs at most ε⁵/25 of the energy of a second graph H. -/
theorem cross_energy [Nonempty α]
    (hPε : 100 ≤ 4 ^ #P.parts * ε ^ 5) (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPG : ¬P.IsUniform G ε) :
    (P.energy H : ℝ) - ε ^ 5 / 25 ≤ (increment hP G ε).energy H := by
  have hk := (nonempty_of_not_uniform hPG).card_pos
  have hk' : (0 : ℝ) < #P.parts := by exact_mod_cast hk
  have hε' := eps_pow_five_pos hPε
  have hn : (#P.parts.offDiag : ℝ) ≤ (#P.parts : ℝ)^2 := by
    exact_mod_cast (show #P.parts.offDiag ≤ #P.parts^2 by rw [offDiag_card, sq]; omega)
  calc
    _ = (∑ x ∈ P.parts.offDiag, (H.edgeDensity x.1 x.2 : ℝ) ^ 2 -
          (#P.parts : ℝ) ^ 2 * (ε ^ 5 / 25)) / #P.parts ^ 2 := by
        rw [coe_energy, sub_div, mul_div_cancel_left₀]; positivity
    _ ≤ (∑ x ∈ P.parts.offDiag.attach, (∑ i ∈ ((chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts),
          H.edgeDensity i.1 i.2 ^ 2 : ℝ) / 16 ^ #P.parts) / #P.parts ^ 2 := by
        gcongr
        calc
          _ ≤ (∑ x ∈ P.parts.offDiag, (H.edgeDensity x.1 x.2 : ℝ)^2) -
                #P.parts.offDiag * (ε^5/25) := by gcongr
          _ = ∑ x ∈ P.parts.offDiag.attach, ((H.edgeDensity x.val.1 x.val.2 : ℝ)^2 -
                ε^5/25) := by
                rw [sum_attach P.parts.offDiag (fun x => (H.edgeDensity x.1 x.2 : ℝ)^2 - ε^5/25),
                  sum_sub_distrib, sum_const, nsmul_eq_mul]
          _ ≤ _ := sum_le_sum fun x _ => cross_chunk H hPα hPε _ _
    _ = (∑ x ∈ P.parts.offDiag.attach, ∑ i ∈ ((chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts),
          H.edgeDensity i.1 i.2 ^ 2 : ℝ) / #(increment hP G ε).parts ^ 2 := by
        rw [card_increment hPα hPG, coe_stepBound, mul_pow, pow_right_comm,
          div_mul_eq_div_div_swap, ← sum_div]; norm_num
    _ ≤ _ := by
        rw [coe_energy]
        gcongr
        rw [← sum_biUnion pairwiseDisjoint_distinctPairs]
        exact sum_le_sum_of_subset_of_nonneg distinctPairs_increment fun i _ _ => sq_nonneg _


/-- One equipartition works simultaneously for two graphs, with a bound independent of the graphs. -/
theorem simultaneous_equipartition (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1) (l : ℕ) :
    ∃ M : ℕ, ∀ {X : Type*} [Fintype X] [DecidableEq X] (G H : SimpleGraph X)
      [DecidableRel G.Adj] [DecidableRel H.Adj], M ≤ Fintype.card X →
      ∃ P : Finpartition (Finset.univ : Finset X), P.IsEquipartition ∧
        l ≤ #P.parts ∧ #P.parts ≤ M ∧ P.IsUniform G η ∧ P.IsUniform H η := by
  let t := initialBound η l
  obtain ⟨r, hr⟩ := exists_nat_gt (10 / η^5)
  let K := stepBound^[r] t
  refine ⟨K * 16^K, ?_⟩
  intro X _ _ G H _ _ hX
  have hK : t ≤ K := by
    exact (monotone_iterate_of_id_le le_stepBound (Nat.zero_le r) t)
  have hKM : K ≤ K * 16^K := Nat.le_mul_of_pos_right _ (by positivity)
  have ht : 0 < t := initialBound_pos _ _
  have : Nonempty X := Fintype.card_pos_iff.mp (ht.trans_le (hK.trans (hKM.trans hX)))
  obtain ⟨start, heq, hnum⟩ := exists_equipartition_card_eq (univ : Finset X) ht.ne'
    (by simpa using hK.trans (hKM.trans hX))
  let goal := fun P : Finpartition (univ : Finset X) => P.IsUniform G η ∧ P.IsUniform H η
  have iter : ∀ i ≤ r, ∃ P : Finpartition (univ : Finset X), P.IsEquipartition ∧
      t ≤ #P.parts ∧ #P.parts ≤ stepBound^[i] t ∧
      (goal P ∨ η^5/5 * i ≤ (P.energy G : ℝ) + P.energy H) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨start, heq, hnum.ge, hnum.le, Or.inr ?_⟩
      simp only [Nat.cast_zero, mul_zero]
      exact add_nonneg (by exact_mod_cast start.energy_nonneg G) (by exact_mod_cast start.energy_nonneg H)
    | succ i ih =>
      intro hi
      obtain ⟨P, hp, hmin, hmax, hor⟩ := ih (by omega)
      by_cases done : goal P
      · exact ⟨P, hp, hmin, hmax.trans (monotone_iterate_of_id_le le_stepBound (Nat.le_succ i) t), Or.inl done⟩
      have he := hor.resolve_left done
      have hsize : #P.parts ≤ K := hmax.trans (monotone_iterate_of_id_le le_stepBound (by omega : i ≤ r) t)
      have hroom : #P.parts * 16 ^ #P.parts ≤ Fintype.card X :=
        (Nat.mul_le_mul hsize (Nat.pow_le_pow_right (by decide) hsize)).trans hX
      have hbig : (100 : ℝ) ≤ 4 ^ #P.parts * η^5 :=
        (hundred_lt_pow_initialBound_mul hη l).le.trans
          (mul_le_mul_of_nonneg_right (pow_right_mono₀ (by norm_num) hmin) (by positivity))
      have hseven : 7 ≤ #P.parts := (seven_le_initialBound η l).trans hmin
      have bounds (J : SimpleGraph X) [DecidableRel J.Adj] (bad : ¬P.IsUniform J η) :
          t ≤ #(increment hp J η).parts ∧ #(increment hp J η).parts ≤ stepBound^[i+1] t := by
        rw [card_increment hroom bad, Function.iterate_succ_apply']
        exact ⟨hmin.trans (le_stepBound _), stepBound_mono hmax⟩
      have hpow := pow_pos hη 5
      by_cases hG : P.IsUniform G η
      · have hH : ¬P.IsUniform H η := fun h => done ⟨hG,h⟩
        obtain ⟨ha,hb⟩ := bounds H hH
        refine ⟨_, increment_isEquipartition hp H η, ha, hb, Or.inr ?_⟩
        have hgain := energy_increment hp hseven hbig hroom hH hη.le hη₁
        have hloss := cross_energy G (hP := hp) hbig hroom hH
        rw [Nat.cast_succ, mul_add, mul_one]
        linarith
      · obtain ⟨ha,hb⟩ := bounds G hG
        refine ⟨_, increment_isEquipartition hp G η, ha, hb, Or.inr ?_⟩
        have hgain := energy_increment hp hseven hbig hroom hG hη.le hη₁
        have hloss := cross_energy H (hP := hp) hbig hroom hG
        rw [Nat.cast_succ, mul_add, mul_one]
        linarith
  obtain ⟨P, hp, ha, hb, hor⟩ := iter r le_rfl
  refine ⟨P, hp, (le_initialBound η l).trans ha, hb.trans hKM, hor.resolve_right ?_⟩
  intro he
  have hg : (P.energy G : ℝ) ≤ 1 := by exact_mod_cast P.energy_le_one G
  have hh : (P.energy H : ℝ) ≤ 1 := by exact_mod_cast P.energy_le_one H
  have hr' := (div_lt_iff₀ (pow_pos hη 5)).mp hr
  linarith

end Energy

section Joint
open Finset SimpleGraph


variable {V : Type*} [DecidableEq V] (c : Fin 3 → SimpleGraph V)
  [∀ i, DecidableRel (c i).Adj]

theorem density_sum (hc : (⊤ : SimpleGraph V).IsEdgeColouring c) {s t : Finset V} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : Disjoint s t) :
    (c 0).edgeDensity s t + (c 1).edgeDensity s t + (c 2).edgeDensity s t = 1 := by
  let E := fun i => (c i).interedges s t
  have hd {i j : Fin 3} (hij : i ≠ j) : Disjoint (E i) (E j) := by
    apply Finset.disjoint_left.mpr
    intro e hi hj
    exact SimpleGraph.disjoint_left.mp (hc.2 _ _ hij) _ _
      (((c i).mem_interedges_iff).mp hi).2.2 (((c j).mem_interedges_iff).mp hj).2.2
  have hu : E 0 ∪ E 1 ∪ E 2 = s ×ˢ t := by
    ext e
    simp only [E, Finset.mem_union, SimpleGraph.mem_interedges_iff, Finset.mem_product]
    constructor
    · rintro ((h | h) | h) <;> exact ⟨h.1, h.2.1⟩
    · rintro ⟨hs', ht'⟩
      have ha : (⊤ : SimpleGraph V).Adj e.1 e.2 := hst.forall_ne_finset hs' ht'
      rw [hc.1, SimpleGraph.iSup_adj] at ha
      obtain ⟨i, hi⟩ := ha
      fin_cases i
      · exact Or.inl (Or.inl ⟨hs', ht', hi⟩)
      · exact Or.inl (Or.inr ⟨hs', ht', hi⟩)
      · exact Or.inr ⟨hs', ht', hi⟩
  have hn := congrArg Finset.card hu
  have hd₂ : Disjoint (E 0 ∪ E 1) (E 2) := disjoint_sup_left.mpr ⟨hd (by decide), hd (by decide)⟩
  rw [Finset.card_union_of_disjoint hd₂,
    Finset.card_union_of_disjoint (hd (i := 0) (j := 1) (by decide)), Finset.card_product] at hn
  simp only [SimpleGraph.edgeDensity_def, ← add_div]
  apply (div_eq_one_iff_eq (mul_ne_zero (by exact_mod_cast hs.card_pos.ne')
    (by exact_mod_cast ht.card_pos.ne'))).mpr
  exact_mod_cast hn

theorem third_uniform (hc : (⊤ : SimpleGraph V).IsEdgeColouring c) {s t : Finset V} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : Disjoint s t) {ε : ℝ}
    (h₀ : (c 0).IsUniform ε s t) (h₁ : (c 1).IsUniform ε s t) :
    (c 2).IsUniform (2 * ε) s t := by
  intro a ha b hb hsa htb
  have hε := h₀.pos
  have hs₀ : (s.card : ℝ) * ε ≤ a.card := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) s.card) hε.le]
  have ht₀ : (t.card : ℝ) * ε ≤ b.card := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) t.card) hε.le]
  have ha₀ : a.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (mul_pos (by exact_mod_cast hs.card_pos) hε).trans_le hs₀)
  have hb₀ : b.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (mul_pos (by exact_mod_cast ht.card_pos) hε).trans_le ht₀)
  have total (x y : Finset V) (hx : x.Nonempty) (hy : y.Nonempty) (hxy : Disjoint x y) :
      ((c 0).edgeDensity x y : ℝ) + (c 1).edgeDensity x y + (c 2).edgeDensity x y = 1 := by
    exact_mod_cast density_sum c hc hx hy hxy
  have ht₁ := total s t hs ht hst
  have ht₂ := total a b ha₀ hb₀ (hst.mono ha hb)
  obtain ⟨hl₀, hu₀⟩ := abs_lt.mp (h₀ ha hb hs₀ ht₀)
  obtain ⟨hl₁, hu₁⟩ := abs_lt.mp (h₁ ha hb hs₀ ht₀)
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Outside one exceptional set of at most 2ε of the ordered pairs of distinct clusters,
all three colours are 2ε-regular and some colour has density at least 1/3. -/
theorem joint_pairs (hc : (⊤ : SimpleGraph V).IsEdgeColouring c) {A : Finset V} (P : Finpartition A) {ε : ℝ}
    (h₀ : P.IsUniform (c 0) ε) (h₁ : P.IsUniform (c 1) ε) :
    ∃ bad ⊆ P.parts.offDiag, (bad.card : ℝ) ≤ (P.parts.offDiag.card : ℝ) * (2 * ε) ∧
      ∀ x ∈ P.parts.offDiag, x ∉ bad →
        (∀ i, (c i).IsUniform (2 * ε) x.1 x.2) ∧
        ∃ i, (1 / 3 : ℚ) ≤ (c i).edgeDensity x.1 x.2 := by
  classical
  let bad := P.nonUniforms (c 0) ε ∪ P.nonUniforms (c 1) ε
  refine ⟨bad, Finset.union_subset (Finset.filter_subset ..) (Finset.filter_subset ..), ?_, ?_⟩
  · have hn : P.parts.offDiag.card = P.parts.card * (P.parts.card - 1) := by
      rw [Finset.offDiag_card, Nat.mul_sub_one]
    have hb : (bad.card : ℝ) ≤ (P.nonUniforms (c 0) ε).card + ((P.nonUniforms (c 1) ε).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (P.nonUniforms (c 0) ε) (P.nonUniforms (c 1) ε)
    rw [Finpartition.IsUniform, ← hn] at h₀ h₁
    linarith
  · intro x hx hgood
    obtain ⟨hx₀, hx₁, hne⟩ := Finset.mem_offDiag.mp hx
    have good (i : Fin 3) (hi : x ∉ P.nonUniforms (c i) ε) : (c i).IsUniform ε x.1 x.2 := by
      by_contra h
      exact hi (Finset.mem_filter.mpr ⟨hx,h⟩)
    have g₀ := good 0 (fun h => hgood (Finset.mem_union_left _ h))
    have g₁ := good 1 (fun h => hgood (Finset.mem_union_right _ h))
    have hs := P.nonempty_of_mem_parts hx₀
    have ht := P.nonempty_of_mem_parts hx₁
    have hd := P.disjoint hx₀ hx₁ hne
    constructor
    · intro i
      fin_cases i
      · exact g₀.mono (by linarith [g₀.pos])
      · exact g₁.mono (by linarith [g₁.pos])
      · exact third_uniform c hc hs ht hd g₀ g₁
    · by_contra! h
      linarith [density_sum c hc hs ht hd, h 0, h 1, h 2]

end Joint

section Lift
open Finset SimpleGraph


variable {V : Type*} [DecidableEq V] {T : Finset V} (P : Finpartition T)

/-- A near-monochromatic unweighted block of clusters pulls back to a near-monochromatic
block of vertices. The factor four covers the difference of one between cluster sizes. -/
theorem lift_density (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset (Finset V)} (hA : A ⊆ P.parts) (hB : B ⊆ P.parts)
    {w : ℕ} (hw : ∀ X ∈ P.parts, w ≤ #X ∧ #X ≤ 2 * w)
    {α : ℝ} (hα : 0 ≤ α)
    (h : ∑ xy ∈ A ×ˢ B, (1 - (G.edgeDensity xy.1 xy.2 : ℝ)) ≤
      α / 4 * A.card * B.card) :
    (1 - α) * ((A.sup id).card : ℝ) * (B.sup id).card ≤
      ∑ x ∈ A.sup id, (((B.sup id).filter (G.Adj x)).card : ℝ) := by
  let X := A.sup id
  let Y := B.sup id
  let Q := P.ofSubset hA rfl
  let R := P.ofSubset hB rfl
  let miss := fun x y : V => ¬ G.Adj x y
  have loss (a b : Finset V) (ha : a ∈ P.parts) (hb : b ∈ P.parts) :
      ((Rel.interedges miss a b).card : ℝ) ≤ (1 - (G.edgeDensity a b : ℝ)) * (4 * (w:ℝ)^2) := by
    have hsum := Rel.card_interedges_add_card_interedges_compl G.Adj a b
    have hsum' : ((G.interedges a b).card : ℝ) + (Rel.interedges miss a b).card =
        (a.card : ℝ) * b.card := by exact_mod_cast hsum
    have hne : (a.card : ℝ) * b.card ≠ 0 := mul_ne_zero
      (by exact_mod_cast (P.nonempty_of_mem_parts ha).card_pos.ne')
      (by exact_mod_cast (P.nonempty_of_mem_parts hb).card_pos.ne')
    have he : (G.edgeDensity a b : ℝ) * (a.card * (b.card : ℝ)) = (G.interedges a b).card := by
      rw [edgeDensity_def]; push_cast; exact div_mul_cancel₀ _ hne
    have hsmall : (a.card : ℝ) * b.card ≤ (2 * (w:ℝ)) * (2 * w) := by
      gcongr
      · exact_mod_cast (hw a ha).2
      · exact_mod_cast (hw b hb).2
    calc
      _ = (1 - (G.edgeDensity a b : ℝ)) * (a.card * (b.card : ℝ)) := by linarith only [he, hsum']
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [hsmall])
        (sub_nonneg.mpr (by exact_mod_cast G.edgeDensity_le_one a b))
  have count : (Rel.interedges miss X Y).card =
      ∑ xy ∈ A ×ˢ B, (Rel.interedges miss xy.1 xy.2).card := by
    exact Rel.card_interedges_finpartition miss Q R
  have lower (C : Finset (Finset V)) (hC : C ⊆ P.parts) :
      C.card * w ≤ (C.sup id).card := by
    rw [← (P.ofSubset hC rfl).sum_card_parts]
    simpa using (Finset.sum_le_sum (s := C) (f := fun _ => w) (g := Finset.card)
      fun a ha => (hw a (hC ha)).1)
  have size : ((A.card : ℝ) * w) * (B.card * (w : ℝ)) ≤ (X.card : ℝ) * Y.card := by
    gcongr
    · exact_mod_cast lower A hA
    · exact_mod_cast lower B hB
  have missing : ((Rel.interedges miss X Y).card : ℝ) ≤ α * X.card * Y.card := by
    rw [count, Nat.cast_sum]
    calc
      _ ≤ ∑ xy ∈ A ×ˢ B, (1 - (G.edgeDensity xy.1 xy.2 : ℝ)) * (4 * (w : ℝ)^2) :=
        sum_le_sum fun xy hxy => loss _ _ (hA (mem_product.mp hxy).1) (hB (mem_product.mp hxy).2)
      _ = _ := (Finset.sum_mul ..).symm
      _ ≤ (α / 4 * A.card * B.card) * (4 * (w : ℝ)^2) := by gcongr
      _ = α * ((A.card * (w : ℝ)) * (B.card * (w : ℝ))) := by ring
      _ ≤ _ := by rw [mul_assoc α]; exact mul_le_mul_of_nonneg_left size hα
  have full : ((Rel.interedges G.Adj X Y).card : ℝ) + (Rel.interedges miss X Y).card =
      (X.card : ℝ) * Y.card := by exact_mod_cast Rel.card_interedges_add_card_interedges_compl G.Adj X Y
  have rows : (Rel.interedges G.Adj X Y).card = ∑ x ∈ X, (Y.filter (G.Adj x)).card := by
    rw [Rel.interedges_eq_biUnion, card_biUnion]
    · simp
    · intro x _ y _ hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro e he hf
      obtain ⟨z,_,rfl⟩ := mem_map.mp he
      obtain ⟨_,_,heq⟩ := mem_map.mp hf
      exact hxy (congrArg Prod.fst heq).symm
  change (1 - α) * (X.card : ℝ) * Y.card ≤ ∑ x ∈ X, ((Y.filter (G.Adj x)).card : ℝ)
  rw [← Nat.cast_sum, ← rows]
  linarith only [full, missing]

end Lift

end CommonRegularity


end PermutedModule0

/- Source module: ReducedMulticoloring.lean -/
section PermutedModule1

/-!
The reduced graph retains every sufficiently dense color on each jointly
regular pair. Keeping all such colors is necessary for the later exclusivity
argument. Credit: @fqlx.
-/

open Finset SimpleGraph

namespace ReducedMulticoloring

variable {V I : Type*} [DecidableEq V]

def graph (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (parts : I → Finset V) (η d : ℝ) (k : Fin 3) : SimpleGraph I where
  Adj u v := u ≠ v ∧ (∀ j, (c j).IsUniform η (parts u) (parts v)) ∧
    d ≤ ((c k).edgeDensity (parts u) (parts v) : ℝ)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, fun j => (h.2.1 j).symm, ?_⟩
    simpa only [SimpleGraph.edgeDensity_comm] using h.2.2⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

noncomputable instance graphDecidable
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (parts : I → Finset V) (η d : ℝ) (k : Fin 3) :
    DecidableRel (graph c parts η d k).Adj := Classical.decRel _

theorem graph_adj (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (parts : I → Finset V) (η d : ℝ) (k : Fin 3) (u v : I) :
    (graph c parts η d k).Adj u v ↔ u ≠ v ∧
      (∀ j, (c j).IsUniform η (parts u) (parts v)) ∧
      d ≤ ((c k).edgeDensity (parts u) (parts v) : ℝ) := Iff.rfl

theorem edge_of_good_pair
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (parts : I → Finset V) (η d : ℝ) (hd : d ≤ 1 / 3)
    {u v : I} (hne : u ≠ v)
    (hregular : ∀ j, (c j).IsUniform η (parts u) (parts v))
    (hdense : ∃ j, (1 / 3 : ℚ) ≤ (c j).edgeDensity (parts u) (parts v)) :
    ∃ j, (graph c parts η d j).Adj u v := by
  obtain ⟨j,hj⟩ := hdense
  refine ⟨j,hne,hregular,hd.trans ?_⟩
  have hj' : ((1 / 3 : ℚ) : ℝ) ≤
      ((c j).edgeDensity (parts u) (parts v) : ℝ) := by exact_mod_cast hj
  norm_num at hj'
  exact hj'

theorem missing_degree_sum_eq [Fintype I] [DecidableEq I]
    (c : Fin 3 → SimpleGraph I) [∀ k, DecidableRel (c k).Adj] :
    (univ.filter (fun e : I × I => e.1 ≠ e.2 ∧ ∀ k, ¬ (c k).Adj e.1 e.2)).card =
      ∑ u : I, (univ.filter (fun v => u ≠ v ∧ ∀ k, ¬ (c k).Adj u v)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]

theorem missing_sum_le_bad [Fintype I] [DecidableEq I]
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (parts : I → Finset V) (η d : ℝ) (hd : d ≤ 1 / 3)
    (bad : Finset (I × I))
    (hgood : ∀ u v, u ≠ v → (u,v) ∉ bad →
      (∀ j, (c j).IsUniform η (parts u) (parts v)) ∧
      ∃ j, (1 / 3 : ℚ) ≤ (c j).edgeDensity (parts u) (parts v)) :
    (∑ u : I, (univ.filter (fun v => u ≠ v ∧
      ∀ k, ¬ (graph c parts η d k).Adj u v)).card) ≤ bad.card := by
  classical
  rw [← missing_degree_sum_eq]
  apply card_le_card
  intro e he
  obtain ⟨_,hne,hno⟩ := mem_filter.mp he
  by_contra hbad
  obtain ⟨hr,hdense⟩ := hgood e.1 e.2 hne hbad
  obtain ⟨k,hk⟩ := edge_of_good_pair c parts η d hd hne hr hdense
  exact hno k hk

/-- All missing reduced pairs belong to the one exceptional set supplied by
simultaneous regularity. This is a count of ordered pairs. -/
theorem missing_pairs_le
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    {A : Finset V} (P : Finpartition A) (η d : ℝ) (hd : d ≤ 1 / 3)
    (bad : Finset (Finset V × Finset V))
    (hgood : ∀ x ∈ P.parts.offDiag, x ∉ bad →
      (∀ j, (c j).IsUniform η x.1 x.2) ∧
      ∃ j, (1 / 3 : ℚ) ≤ (c j).edgeDensity x.1 x.2) :
    let R := graph c (fun U : P.parts => (U : Finset V)) η d
    (univ.filter (fun e : P.parts × P.parts =>
      e.1 ≠ e.2 ∧ ∀ k, ¬ (R k).Adj e.1 e.2)).card ≤ bad.card := by
  classical
  dsimp only
  apply card_le_card_of_injOn (fun e => ((e.1 : Finset V), (e.2 : Finset V)))
  · intro e he
    obtain ⟨_,hne,hno⟩ := mem_filter.mp he
    by_contra hb
    have hp : ((e.1 : Finset V), (e.2 : Finset V)) ∈ P.parts.offDiag :=
      mem_offDiag.mpr ⟨e.1.property,e.2.property,
        fun h => hne (Subtype.ext h)⟩
    obtain ⟨hr,hdense⟩ := hgood _ hp hb
    obtain ⟨k,hk⟩ := edge_of_good_pair c (fun U : P.parts => (U : Finset V))
      η d hd hne hr hdense
    exact hno k hk
  · intro e _ f _ hef
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hef))
      (Subtype.ext (congrArg Prod.snd hef))

theorem jointly_regular_missing_sum
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (hc : (⊤ : SimpleGraph V).IsEdgeColouring c)
    {A : Finset V} (P : Finpartition A) (ε d : ℝ) (hd : d ≤ 1 / 3)
    (h₀ : P.IsUniform (c 0) ε) (h₁ : P.IsUniform (c 1) ε) :
    let R := graph c (fun U : P.parts => (U : Finset V)) (2 * ε) d
    ((∑ U : P.parts,
      (univ.filter (fun W => U ≠ W ∧ ∀ k, ¬ (R k).Adj U W)).card : ℕ) : ℝ) ≤
      (P.parts.offDiag.card : ℝ) * (2 * ε) := by
  classical
  dsimp only
  obtain ⟨bad,_,hbad,hgood⟩ := CommonRegularity.joint_pairs c hc P h₀ h₁
  have hcount := missing_pairs_le c P (2 * ε) d hd bad hgood
  dsimp only at hcount
  rw [missing_degree_sum_eq] at hcount
  exact (Nat.cast_le.mpr hcount).trans hbad

/-- If no other color occurs on a jointly regular reduced pair, the host
pair has density at least 1−2d in the remaining color. -/
theorem exclusive_density
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (hc : (⊤ : SimpleGraph V).IsEdgeColouring c)
    (parts : I → Finset V) (η d : ℝ) (k : Fin 3)
    {u v : I} (hne : u ≠ v) (hu : (parts u).Nonempty) (hv : (parts v).Nonempty)
    (hdis : Disjoint (parts u) (parts v))
    (hregular : ∀ j, (c j).IsUniform η (parts u) (parts v))
    (hother : ∀ j, j ≠ k → ¬ (graph c parts η d j).Adj u v) :
    1 - 2 * d ≤ ((c k).edgeDensity (parts u) (parts v) : ℝ) := by
  have hsmall (j : Fin 3) (hj : j ≠ k) :
      ((c j).edgeDensity (parts u) (parts v) : ℝ) < d := by
    by_contra! h
    exact hother j hj ⟨hne,hregular,h⟩
  have hsum : ((c 0).edgeDensity (parts u) (parts v) : ℝ) +
      (c 1).edgeDensity (parts u) (parts v) +
      (c 2).edgeDensity (parts u) (parts v) = 1 := by
    exact_mod_cast CommonRegularity.density_sum c hc hu hv hdis
  fin_cases k
  · change 1 - 2 * d ≤ ((c 0).edgeDensity (parts u) (parts v) : ℝ)
    have h₁ := hsmall 1 (by decide)
    have h₂ := hsmall 2 (by decide)
    linarith
  · change 1 - 2 * d ≤ ((c 1).edgeDensity (parts u) (parts v) : ℝ)
    have h₀ := hsmall 0 (by decide)
    have h₂ := hsmall 2 (by decide)
    linarith
  · change 1 - 2 * d ≤ ((c 2).edgeDensity (parts u) (parts v) : ℝ)
    have h₀ := hsmall 0 (by decide)
    have h₁ := hsmall 1 (by decide)
    linarith

end ReducedMulticoloring


end PermutedModule1

/- Source module: QuantitativeThreeColourCore.lean -/
section PermutedModule2

/-!
Exclusive multicolour cores for quantitative connected-matching stability.
The labels 0, 1, 2 mean red, blue, green in the core geometry. Output extremal
partitions may use another permutation to match the absorption conventions.
Credit: @fqlx.
-/

open SimpleGraph

namespace MatchingStability

def Exclusive {V : Type*} (c : Fin 3 → SimpleGraph V) (k : Fin 3) (u v : V) : Prop :=
  (c k).Adj u v ∧ ∀ j, j ≠ k → ¬ (c j).Adj u v

def ExclusiveBetween {V : Type*} (c : Fin 3 → SimpleGraph V) (k : Fin 3)
    (A B : Finset V) : Prop := ∀ u ∈ A, ∀ v ∈ B, Exclusive c k u v

theorem Exclusive.symm {V : Type*} {c : Fin 3 → SimpleGraph V} {k : Fin 3} {u v : V}
    (h : Exclusive c k u v) : Exclusive c k v u :=
  ⟨h.1.symm,fun j hj h' => h.2 j hj h'.symm⟩

theorem ExclusiveBetween.symm {V : Type*} {c : Fin 3 → SimpleGraph V} {k : Fin 3}
    {A B : Finset V} (h : ExclusiveBetween c k A B) : ExclusiveBetween c k B A :=
  fun v hv u hu => (h u hu v hv).symm

theorem exclusive_permuted_iff {V : Type*} (c : Fin 3 → SimpleGraph V)
    (σ : Equiv.Perm (Fin 3)) (k : Fin 3) (u v : V) :
    Exclusive (fun i => c (σ i)) k u v ↔ Exclusive c (σ k) u v := by
  constructor
  · rintro ⟨h,hnot⟩
    refine ⟨h,fun j hj => ?_⟩
    have hne : σ.symm j ≠ k := fun he => hj (by simpa [he] using (σ.apply_symm_apply j).symm)
    simpa using hnot (σ.symm j) hne
  · rintro ⟨h,hnot⟩
    exact ⟨h,fun j hj => hnot (σ j) (σ.injective.ne hj)⟩

theorem exclusive_zero_iff {V : Type*} (c : Fin 3 → SimpleGraph V) (u v : V) :
    Exclusive c 0 u v ↔ (c 0).Adj u v ∧ ¬ (c 1).Adj u v ∧ ¬ (c 2).Adj u v := by
  constructor
  · exact fun h => ⟨h.1,h.2 1 (by decide),h.2 2 (by decide)⟩
  · rintro ⟨h,h1,h2⟩
    refine ⟨h,fun j hj => ?_⟩
    fin_cases j <;> simp_all

theorem exclusive_one_iff {V : Type*} (c : Fin 3 → SimpleGraph V) (u v : V) :
    Exclusive c 1 u v ↔ (c 1).Adj u v ∧ ¬ (c 0).Adj u v ∧ ¬ (c 2).Adj u v := by
  constructor
  · exact fun h => ⟨h.1,h.2 0 (by decide),h.2 2 (by decide)⟩
  · rintro ⟨h,h0,h2⟩
    refine ⟨h,fun j hj => ?_⟩
    fin_cases j <;> simp_all

theorem exclusive_two_iff {V : Type*} (c : Fin 3 → SimpleGraph V) (u v : V) :
    Exclusive c 2 u v ↔ (c 2).Adj u v ∧ ¬ (c 0).Adj u v ∧ ¬ (c 1).Adj u v := by
  constructor
  · exact fun h => ⟨h.1,h.2 0 (by decide),h.2 1 (by decide)⟩
  · rintro ⟨h,h0,h1⟩
    refine ⟨h,fun j hj => ?_⟩
    fin_cases j <;> simp_all

structure QuantitativeFourBlockCore {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (m h : ℕ) where
  colors : Equiv.Perm (Fin 3)
  X : Finset V
  Y : Finset V
  Z : Finset V
  W : Finset V
  disjointXY : Disjoint X Y
  disjointZW : Disjoint Z W
  disjointSides : Disjoint (X ∪ Y) (Z ∪ W)
  cardXY : X.card + Y.card = 2 * (m - 4 * h)
  cardZW : Z.card + W.card = 2 * (m - 4 * h)
  lowerX : m - 9 * h + 1 ≤ X.card
  upperX : X.card ≤ m + h - 1
  lowerY : m - 9 * h + 1 ≤ Y.card
  upperY : Y.card ≤ m + h - 1
  lowerZ : 10 * h - 1 ≤ Z.card
  orderedZW : Z.card ≤ W.card
  redXZ : ExclusiveBetween c (colors 0) X Z
  redYW : ExclusiveBetween c (colors 0) Y W
  blueXW : ExclusiveBetween c (colors 1) X W
  blueYZ : ExclusiveBetween c (colors 1) Y Z
  greenXY : ExclusiveBetween c (colors 2) X Y
  greenZW : ExclusiveBetween c (colors 2) Z W

structure QuantitativeCliqueCore {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (m h : ℕ) where
  colors : Equiv.Perm (Fin 3)
  X : Finset V
  Y : Finset V
  W : Finset V
  disjointXY : Disjoint X Y
  disjointXW : Disjoint X W
  disjointYW : Disjoint Y W
  lowerX : m - 9 * h + 1 ≤ X.card
  upperX : X.card ≤ m + h - 1
  lowerY : m - 9 * h + 1 ≤ Y.card
  upperY : Y.card ≤ m + h - 1
  lowerW : 2 * m - 58 * h + 10 ≤ W.card
  redXW : ExclusiveBetween c (colors 0) X W
  blueYW : ExclusiveBetween c (colors 1) Y W
  greenW : ∀ u ∈ W, ∀ v ∈ W, u ≠ v → Exclusive c (colors 2) u v


end MatchingStability

end PermutedModule2

/- Source module: FinitePartitionExtension.lean -/
section PermutedModule3

/-!
Extending disjoint finite cores to a partition and counting the ordered pairs
whose prescribed relation may fail after the extension. Credit: @fqlx.
-/

open Finset
open scoped BigOperators

namespace FinitePartitionExtension

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def outside (W : I → Finset V) : Finset V := univ \ univ.biUnion W

def extend (W : I → Finset V) (j : I) (i : I) : Finset V :=
  if i = j then W i ∪ outside W else W i

theorem mem_extend_iff (W : I → Finset V) (j i : I) (v : V) :
    v ∈ extend W j i ↔ v ∈ W i ∨ i = j ∧ v ∈ outside W := by
  by_cases h : i = j <;> simp [extend,h]

theorem outside_not_mem (W : I → Finset V) (i : I) {v : V}
    (hv : v ∈ outside W) : v ∉ W i := by
  intro hi
  exact (mem_sdiff.mp hv).2 (mem_biUnion.mpr ⟨i,mem_univ _,hi⟩)

theorem outside_disjoint (W : I → Finset V) (i : I) : Disjoint (W i) (outside W) := by
  rw [Finset.disjoint_left]
  exact fun _ hi ho => outside_not_mem W i ho hi

theorem subset_extend (W : I → Finset V) (j i : I) : W i ⊆ extend W j i :=
  fun _ hv => (mem_extend_iff W j i _).mpr (Or.inl hv)

theorem extend_disjoint (W : I → Finset V) (j : I)
    (hdis : ∀ i k, i ≠ k → Disjoint (W i) (W k)) :
    ∀ i k, i ≠ k → Disjoint (extend W j i) (extend W j k) := by
  intro i k hik
  rw [Finset.disjoint_left]
  intro v hvi hvk
  rcases (mem_extend_iff W j i v).mp hvi with hi | ⟨hij,ho⟩ <;>
    rcases (mem_extend_iff W j k v).mp hvk with hk | ⟨hkj,ho'⟩
  · exact Finset.disjoint_left.mp (hdis i k hik) hi hk
  · exact outside_not_mem W i ho' hi
  · exact outside_not_mem W k ho hk
  · exact hik (hij.trans hkj.symm)

theorem extend_cover (W : I → Finset V) (j : I) :
    univ.biUnion (extend W j) = univ := by
  apply eq_univ_of_forall
  intro v
  by_cases h : ∃ i, v ∈ W i
  · obtain ⟨i,hi⟩ := h
    exact mem_biUnion.mpr ⟨i,mem_univ _,subset_extend W j i hi⟩
  · have ho : v ∈ outside W := by
      refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
      intro hv
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
      exact h ⟨i,hi⟩
    exact mem_biUnion.mpr ⟨j,mem_univ _,
      (mem_extend_iff W j j v).mpr (Or.inr ⟨rfl,ho⟩)⟩

theorem extend_card (W : I → Finset V) (j i : I) :
    (extend W j i).card = (W i).card + if i = j then (outside W).card else 0 := by
  by_cases h : i = j
  · simp only [extend,if_pos h]
    exact card_union_of_disjoint (outside_disjoint W i)
  · simp [extend,h]

theorem outside_card (W : I → Finset V)
    (hdis : ∀ i k, i ≠ k → Disjoint (W i) (W k)) :
    (outside W).card = Fintype.card V - ∑ i, (W i).card := by
  have hc : (univ.biUnion W).card = ∑ i, (W i).card :=
    card_biUnion (fun i _ k _ hik => hdis i k hik)
  rw [outside,card_sdiff_of_subset (subset_univ _),card_univ,hc]

theorem selected_extension_difference_subset (W : I → Finset V) (j : I) (S : Finset I) :
    S.biUnion (extend W j) \ S.biUnion W ⊆ outside W := by
  intro v hv
  obtain ⟨hvT,hvW⟩ := mem_sdiff.mp hv
  obtain ⟨i,hi,hvi⟩ := mem_biUnion.mp hvT
  rcases (mem_extend_iff W j i v).mp hvi with hvi | ⟨_,ho⟩
  · exact (hvW (mem_biUnion.mpr ⟨i,hi,hvi⟩)).elim
  · exact ho

/-- The failure set lies among pairs with at least one newly added endpoint. -/
theorem failures_card_le
    (R : V → V → Prop) [DecidableRel R]
    (A B U W : Finset V) (d N : ℕ)
    (hA : (A \ U).card ≤ d) (hB : (B \ W).card ≤ d)
    (hAN : A.card ≤ N) (hBN : B.card ≤ N)
    (hgood : ∀ u ∈ U, ∀ w ∈ W, R u w) :
    ((A.product B).filter (fun p => ¬ R p.1 p.2)).card ≤ 2 * d * N := by
  have hsub : (A.product B).filter (fun p => ¬ R p.1 p.2) ⊆
      (A \ U).product B ∪ A.product (B \ W) := by
    intro p hp
    obtain ⟨hpAB,hpR⟩ := mem_filter.mp hp
    obtain ⟨hpA,hpB⟩ := mem_product.mp hpAB
    by_cases hpU : p.1 ∈ U
    · have hpW : p.2 ∉ W := fun h => hpR (hgood p.1 hpU p.2 h)
      exact mem_union_right _ (mem_product.mpr ⟨hpA,mem_sdiff.mpr ⟨hpB,hpW⟩⟩)
    · exact mem_union_left _ (mem_product.mpr ⟨mem_sdiff.mpr ⟨hpA,hpU⟩,hpB⟩)
  calc
    _ ≤ ((A \ U).product B ∪ A.product (B \ W)).card := card_le_card hsub
    _ ≤ ((A \ U).product B).card + (A.product (B \ W)).card := card_union_le _ _
    _ = (A \ U).card * B.card + A.card * (B \ W).card := by simp only [Finset.product_eq_sprod,card_product]
    _ ≤ d * N + N * d := Nat.add_le_add (Nat.mul_le_mul hA hBN) (Nat.mul_le_mul hAN hB)
    _ = 2 * d * N := by ring

theorem extended_failures_card_le (W : I → Finset V) (j : I) (S T : Finset I)
    (R : V → V → Prop) [DecidableRel R]
    (hgood : ∀ u ∈ S.biUnion W, ∀ v ∈ T.biUnion W, R u v) :
    (((S.biUnion (extend W j)).product (T.biUnion (extend W j))).filter
      (fun p => ¬ R p.1 p.2)).card ≤ 2 * (outside W).card * Fintype.card V := by
  exact failures_card_le R _ _ (S.biUnion W) (T.biUnion W) _ _
    (card_le_card (selected_extension_difference_subset W j S))
    (card_le_card (selected_extension_difference_subset W j T))
    (card_le_univ _) (card_le_univ _) hgood

theorem assignment_of_partition (T : I → Finset V)
    (hdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hcover : univ.biUnion T = univ) :
    ∃ f : V → I, ∀ v i, f v = i ↔ v ∈ T i := by
  classical
  have hv : ∀ v : V, ∃ i, v ∈ T i := by
    intro v
    have hm : v ∈ univ.biUnion T := hcover.symm ▸ mem_univ v
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hm
    exact ⟨i,hi⟩
  choose f hf using hv
  refine ⟨f,fun v i => ⟨?_,?_⟩⟩
  · intro h
    simpa [h] using hf v
  · intro hi
    by_contra hn
    exact Finset.disjoint_left.mp (hdis (f v) i hn) (hf v) hi


end FinitePartitionExtension

end PermutedModule3

/- Source module: FiniteExtremalPatterns.lean -/
section PermutedModule4

/-!
Finite extremal patterns with exclusive reduced-graph pairs. The six-pair
convention agrees with Benevides–Skokan's EC1/EC3 absorption interfaces; EC2
uses a clique split as blocks 0 and 1. Credit: @fqlx.
-/

open SimpleGraph Finset

namespace MatchingStability

def EC1Joins : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)) :=
  [(0,{0},{1}),(0,{2},{3}),(1,{0},{3}),(1,{1},{2}),(2,{0},{2}),(2,{1},{3})]

def EC2Joins : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)) :=
  [(0,{0},{1}),(1,{0,1},{2}),(2,{0,1},{3})]

def BlockPartition {V : Type*} [Fintype V] [DecidableEq V]
    (T : Fin 4 → Finset V) : Prop :=
  (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧ Finset.univ.biUnion T = Finset.univ

noncomputable def badExclusiveCount {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (k : Fin 3) (A B : Finset V) : ℕ := by
  classical
  exact ((A.product B).filter (fun p => ¬ Exclusive c k p.1 p.2)).card

def ExclusiveDensities {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (σ : Equiv.Perm (Fin 3))
    (T : Fin 4 → Finset V) (β : ℝ)
    (J : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) : Prop :=
  ∀ k S U, (k,S,U) ∈ J →
    (badExclusiveCount c (σ k) (S.biUnion T) (U.biUnion T) : ℝ) ≤
      β * (S.biUnion T).card * (U.biUnion T).card

def BalancedBlockSizes {V : Type*} (T : Fin 4 → Finset V) (m : ℕ) (α : ℝ) : Prop :=
  ∀ i, (1 - α) * m ≤ ((T i).card : ℝ)

def EC3BlockSizes {V : Type*} (T : Fin 4 → Finset V) (m : ℕ) (μ : ℝ) : Prop :=
  let a : Fin 4 → ℝ := fun i => (T i).card
  (1 - 4 / 5 * μ) * m ≤ min (a 0) (min (a 1) (a 2)) ∧
    μ * m ≤ a 3 ∧ max (a 1) (max (a 2) (a 3)) + μ * m ≤ a 0 ∧
    a 0 + a 3 ≤ (1 + 3 / 10 * μ) * (2 * m)

def StrongEC3BlockSizes {V : Type*} (T : Fin 4 → Finset V) (m : ℕ) (μ : ℝ) : Prop :=
  let a : Fin 4 → ℝ := fun i => (T i).card
  (1 - 7 / 10 * μ) * m ≤ min (a 0) (min (a 1) (a 2)) ∧
    2 * μ * m ≤ a 3 ∧ max (a 1) (max (a 2) (a 3)) + 2 * μ * m ≤ a 0 ∧
    a 0 + a 3 ≤ (1 + 1 / 5 * μ) * (2 * m)

def FiniteEC1 {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (m : ℕ) (α : ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (T : Fin 4 → Finset V),
    BlockPartition T ∧ BalancedBlockSizes T m α ∧ ExclusiveDensities c σ T α EC1Joins

def FiniteEC2 {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (m : ℕ) (α : ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (T : Fin 4 → Finset V),
    BlockPartition T ∧ BalancedBlockSizes T m α ∧ ExclusiveDensities c σ T α EC2Joins

def FiniteEC3 {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (m : ℕ) (μ δ : ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (T : Fin 4 → Finset V),
    BlockPartition T ∧ EC3BlockSizes T m μ ∧ ExclusiveDensities c σ T δ EC1Joins

def StrongFiniteEC3 {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (m : ℕ) (μ δ : ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (T : Fin 4 → Finset V),
    BlockPartition T ∧ StrongEC3BlockSizes T m μ ∧ ExclusiveDensities c σ T δ EC1Joins

theorem StrongEC3BlockSizes.toEC3 {V : Type*} {T : Fin 4 → Finset V} {m : ℕ} {μ : ℝ}
    (hμ : 0 ≤ μ) (h : StrongEC3BlockSizes T m μ) : EC3BlockSizes T m μ := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rcases h with ⟨h0,h1,h2,h3⟩
  refine ⟨?_,?_,?_,?_⟩ <;> dsimp at * <;> nlinarith

theorem StrongFiniteEC3.toEC3 {V : Type*} [Fintype V] [DecidableEq V]
    {c : Fin 3 → SimpleGraph V} {m : ℕ} {μ δ : ℝ}
    (hμ : 0 ≤ μ) (h : StrongFiniteEC3 c m μ δ) : FiniteEC3 c m μ δ := by
  obtain ⟨σ,T,hT,hs,hd⟩ := h
  exact ⟨σ,T,hT,hs.toEC3 hμ,hd⟩

theorem EC1Joins_nonempty (k : Fin 3) (S T : Finset (Fin 4))
    (h : (k,S,T) ∈ EC1Joins) : S.Nonempty ∧ T.Nonempty := by
  simp only [EC1Joins,List.mem_cons,Prod.mk.injEq,List.not_mem_nil,or_false] at h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> simp

theorem EC2Joins_nonempty (k : Fin 3) (S T : Finset (Fin 4))
    (h : (k,S,T) ∈ EC2Joins) : S.Nonempty ∧ T.Nonempty := by
  simp only [EC2Joins,List.mem_cons,Prod.mk.injEq,List.not_mem_nil,or_false] at h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> simp

theorem extend_is_partition {V : Type*} [Fintype V] [DecidableEq V]
    (W : Fin 4 → Finset V) (j : Fin 4)
    (hdis : ∀ i k, i ≠ k → Disjoint (W i) (W k)) :
    BlockPartition (FinitePartitionExtension.extend W j) :=
  ⟨FinitePartitionExtension.extend_disjoint W j hdis,
    FinitePartitionExtension.extend_cover W j⟩

theorem extended_exclusive_densities {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (σ : Equiv.Perm (Fin 3))
    (W : Fin 4 → Finset V) (j : Fin 4) (β ℓ : ℝ)
    (J : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)))
    (hβ : 0 ≤ β) (hℓ : 0 ≤ ℓ)
    (hlower : ∀ i, ℓ ≤ ((W i).card : ℝ))
    (hne : ∀ k S T, (k,S,T) ∈ J → S.Nonempty ∧ T.Nonempty)
    (hgood : ∀ k S T, (k,S,T) ∈ J →
      ExclusiveBetween c (σ k) (S.biUnion W) (T.biUnion W))
    (hbudget : 2 * (FinitePartitionExtension.outside W).card * (Fintype.card V : ℝ) ≤ β * ℓ ^ 2) :
    ExclusiveDensities c σ (FinitePartitionExtension.extend W j) β J := by
  classical
  intro k S T hJ
  have hc := FinitePartitionExtension.extended_failures_card_le W j S T
    (Exclusive c (σ k)) (hgood k S T hJ)
  have hcount : (badExclusiveCount c (σ k)
      (S.biUnion (FinitePartitionExtension.extend W j))
      (T.biUnion (FinitePartitionExtension.extend W j)) : ℝ) ≤
      2 * (FinitePartitionExtension.outside W).card * (Fintype.card V : ℝ) := by
    unfold badExclusiveCount
    exact_mod_cast hc
  have hsel : ∀ U : Finset (Fin 4), U.Nonempty →
      ℓ ≤ ((U.biUnion (FinitePartitionExtension.extend W j)).card : ℝ) := by
    intro U hU
    obtain ⟨i,hi⟩ := hU
    have hsub : W i ⊆ U.biUnion (FinitePartitionExtension.extend W j) :=
      (FinitePartitionExtension.subset_extend W j i).trans
        (Finset.subset_biUnion_of_mem _ hi)
    exact (hlower i).trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
  have hS := hsel S (hne k S T hJ).1
  have hT := hsel T (hne k S T hJ).2
  calc
    _ ≤ β * ℓ ^ 2 := hcount.trans hbudget
    _ ≤ β * (S.biUnion (FinitePartitionExtension.extend W j)).card *
        (T.biUnion (FinitePartitionExtension.extend W j)).card := by
      have hh := mul_le_mul hS hT hℓ (Nat.cast_nonneg _)
      have hβh := mul_le_mul_of_nonneg_left hh hβ
      nlinarith


end MatchingStability

end PermutedModule4

/- Source module: FourBlockExtremalGeometry.lean -/
section PermutedModule5

/-! Canonical block and colour orders for the two four-core regimes.
Credit: @fqlx. -/

open SimpleGraph Finset
open scoped BigOperators

namespace MatchingStability

theorem four_blocks_disjoint {V : Type*} [DecidableEq V]
    (A B C D : Finset V) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D) (hBC : Disjoint B C) (hBD : Disjoint B D)
    (hCD : Disjoint C D) :
    ∀ i j : Fin 4, i ≠ j → Disjoint (![A,B,C,D] i) (![A,B,C,D] j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [disjoint_comm]

namespace QuantitativeFourBlockCore

variable {V : Type*} [DecidableEq V] {c : Fin 3 → SimpleGraph V} {m h : ℕ}

def ec1Blocks (p : QuantitativeFourBlockCore c m h) : Fin 4 → Finset V :=
  ![p.X,p.Z,p.Y,p.W]

def ec3Blocks (p : QuantitativeFourBlockCore c m h) : Fin 4 → Finset V :=
  ![p.W,p.X,p.Y,p.Z]

def ec3Colors (p : QuantitativeFourBlockCore c m h) : Equiv.Perm (Fin 3) :=
  ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (0 : Fin 3) 2)).trans p.colors

theorem ec1Blocks_disjoint (p : QuantitativeFourBlockCore c m h) :
    ∀ i j, i ≠ j → Disjoint (p.ec1Blocks i) (p.ec1Blocks j) := by
  exact four_blocks_disjoint p.X p.Z p.Y p.W
    (p.disjointSides.mono subset_union_left subset_union_left) p.disjointXY
    (p.disjointSides.mono subset_union_left subset_union_right)
    (p.disjointSides.mono subset_union_right subset_union_left).symm p.disjointZW
    (p.disjointSides.mono subset_union_right subset_union_right)

theorem ec3Blocks_disjoint (p : QuantitativeFourBlockCore c m h) :
    ∀ i j, i ≠ j → Disjoint (p.ec3Blocks i) (p.ec3Blocks j) := by
  exact four_blocks_disjoint p.W p.X p.Y p.Z
    (p.disjointSides.mono subset_union_left subset_union_right).symm
    (p.disjointSides.mono subset_union_right subset_union_right).symm p.disjointZW.symm
    p.disjointXY (p.disjointSides.mono subset_union_left subset_union_left)
    (p.disjointSides.mono subset_union_right subset_union_left)

theorem ec1Blocks_good (p : QuantitativeFourBlockCore c m h)
    (k : Fin 3) (S T : Finset (Fin 4)) (hJ : (k,S,T) ∈ EC1Joins) :
    ExclusiveBetween c (p.colors k) (S.biUnion p.ec1Blocks) (T.biUnion p.ec1Blocks) := by
  simp only [EC1Joins,List.mem_cons,Prod.mk.injEq,List.not_mem_nil,or_false] at hJ
  rcases hJ with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · simpa [ec1Blocks] using p.redXZ
  · simpa [ec1Blocks] using p.redYW
  · simpa [ec1Blocks] using p.blueXW
  · simpa [ec1Blocks] using p.blueYZ.symm
  · simpa [ec1Blocks] using p.greenXY
  · simpa [ec1Blocks] using p.greenZW

theorem ec3Blocks_good (p : QuantitativeFourBlockCore c m h)
    (k : Fin 3) (S T : Finset (Fin 4)) (hJ : (k,S,T) ∈ EC1Joins) :
    ExclusiveBetween c (p.ec3Colors k) (S.biUnion p.ec3Blocks) (T.biUnion p.ec3Blocks) := by
  simp only [EC1Joins,List.mem_cons,Prod.mk.injEq,List.not_mem_nil,or_false] at hJ
  rcases hJ with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · simpa [ec3Blocks,ec3Colors,Equiv.swap_apply_def] using p.blueXW.symm
  · simpa [ec3Blocks,ec3Colors,Equiv.swap_apply_def] using p.blueYZ
  · simpa [ec3Blocks,ec3Colors,Equiv.swap_apply_def] using p.greenZW.symm
  · simpa [ec3Blocks,ec3Colors,Equiv.swap_apply_def] using p.greenXY
  · simpa [ec3Blocks,ec3Colors,Equiv.swap_apply_def] using p.redYW.symm
  · simpa [ec3Blocks,ec3Colors,Equiv.swap_apply_def] using p.redXZ

theorem ec1Blocks_outside_card [Fintype V] (p : QuantitativeFourBlockCore c m h)
    (hV : Fintype.card V = 4 * m) (hm : 4 * h ≤ m) :
    (FinitePartitionExtension.outside p.ec1Blocks).card = 16 * h := by
  rw [FinitePartitionExtension.outside_card _ p.ec1Blocks_disjoint,hV]
  rw [Fin.sum_univ_four]
  change 4 * m - (p.X.card + p.Z.card + p.Y.card + p.W.card) = 16 * h
  have hXY := p.cardXY
  have hZW := p.cardZW
  omega

theorem ec3Blocks_outside_card [Fintype V] (p : QuantitativeFourBlockCore c m h)
    (hV : Fintype.card V = 4 * m) (hm : 4 * h ≤ m) :
    (FinitePartitionExtension.outside p.ec3Blocks).card = 16 * h := by
  rw [FinitePartitionExtension.outside_card _ p.ec3Blocks_disjoint,hV]
  rw [Fin.sum_univ_four]
  change 4 * m - (p.W.card + p.X.card + p.Y.card + p.Z.card) = 16 * h
  have hXY := p.cardXY
  have hZW := p.cardZW
  omega

end QuantitativeFourBlockCore


end MatchingStability

end PermutedModule5

/- Source module: FiniteRegimeArithmetic.lean -/
section PermutedModule6

/-! Explicit quantitative margins for the three extremal regimes.
Credit: @fqlx. -/

namespace MatchingStability

structure RegimeParameters (m h : ℕ) (α μ δ : ℝ) : Prop where
  positiveH : 1 ≤ h
  largeM : 1000 * h ≤ m
  alpha_pos : 0 < α
  alpha_small : α ≤ 1 / 100
  mu_pos : 0 < μ
  mu_small : μ ≤ α / 1000
  delta_pos : 0 < δ
  hAlpha : (h : ℝ) ≤ α * m / 100000
  hMu : (h : ℝ) ≤ μ * m / 10000
  hDelta : (h : ℝ) ≤ δ * μ ^ 2 * m / 100000

namespace RegimeParameters

variable {m h : ℕ} {α μ δ : ℝ}

theorem m_pos (p : RegimeParameters m h α μ δ) : 0 < m := by
  have := p.positiveH
  have := p.largeM
  omega

theorem mu_le_half (p : RegimeParameters m h α μ δ) : μ ≤ 1 / 2 := by
  have := p.mu_small
  have := p.alpha_small
  linarith

theorem tau_gap (p : RegimeParameters m h α μ δ) :
    10 * μ * m ≤ α / 100 * m := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_right p.mu_small hm
  nlinarith

theorem cast_lower (p : RegimeParameters m h α μ δ) (x : ℕ)
    (hx : m - 9 * h + 1 ≤ x) :
    (m : ℝ) - 9 * h + 1 ≤ x := by
  have hm := p.largeM
  have hn : m + 1 ≤ x + 9 * h := by omega
  have hr : (m : ℝ) + 1 ≤ (x : ℝ) + 9 * h := by exact_mod_cast hn
  linarith

theorem cast_upper (p : RegimeParameters m h α μ δ) (x : ℕ)
    (hx : x ≤ m + h - 1) :
    (x : ℝ) ≤ m + h - 1 := by
  have hm := p.m_pos
  have hn : x + 1 ≤ m + h := by omega
  have hr : (x : ℝ) + 1 ≤ (m : ℝ) + h := by exact_mod_cast hn
  linarith

theorem balanced_lower_of_near_m (p : RegimeParameters m h α μ δ) (x : ℝ)
    (hx : (m : ℝ) - 9 * h ≤ x) :
    (1 - α) * m ≤ x ∧ (m : ℝ) / 2 ≤ x := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hαm := mul_nonneg p.alpha_pos.le hm
  have hαupper := mul_le_mul_of_nonneg_right p.alpha_small hm
  have hh := p.hAlpha
  constructor <;> nlinarith

theorem ec1_budget (p : RegimeParameters m h α μ δ) :
    128 * (h : ℝ) * m ≤ α * ((m : ℝ) / 2) ^ 2 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_right p.hAlpha hm
  have hn := mul_nonneg p.alpha_pos.le (sq_nonneg (m : ℝ))
  nlinarith

theorem ec2_budget (p : RegimeParameters m h α μ δ) (e : ℝ)
    (he : e ≤ α / 100 * m + 80 * h) :
    8 * e * m ≤ α * ((m : ℝ) / 2) ^ 2 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_right p.hAlpha hm
  have he' := mul_le_mul_of_nonneg_right he hm
  have hn := mul_nonneg p.alpha_pos.le (sq_nonneg (m : ℝ))
  nlinarith

theorem ec3_budget (p : RegimeParameters m h α μ δ) :
    128 * (h : ℝ) * m ≤ δ * (μ * m) ^ 2 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_right p.hDelta hm
  have hn := mul_nonneg p.delta_pos.le (sq_nonneg (μ * (m : ℝ)))
  nlinarith

theorem strong_ec3_numeric (p : RegimeParameters m h α μ δ)
    (a b c d : ℝ)
    (had : a + d = 2 * m + 8 * h)
    (hbl : (m : ℝ) - 9 * h + 1 ≤ b) (hcl : (m : ℝ) - 9 * h + 1 ≤ c)
    (hbu : b ≤ m + h - 1) (hcu : c ≤ m + h - 1)
    (hdl : α / 100 * m ≤ d) (hdu : d ≤ (1 - α / 100) * m) :
    (1 - 7 / 10 * μ) * m ≤ min a (min b c) ∧
      2 * μ * m ≤ d ∧ max b (max c d) + 2 * μ * m ≤ a ∧
      a + d ≤ (1 + 1 / 5 * μ) * (2 * m) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hμm := mul_nonneg p.mu_pos.le hm
  have hαm := mul_nonneg p.alpha_pos.le hm
  have hgap := p.tau_gap
  have hsmall := p.hMu
  have hA : (1 - 7 / 10 * μ) * m ≤ a := by nlinarith
  have hB : (1 - 7 / 10 * μ) * m ≤ b := by nlinarith
  have hC : (1 - 7 / 10 * μ) * m ≤ c := by nlinarith
  have hb : b ≤ a - 2 * μ * m := by nlinarith
  have hc : c ≤ a - 2 * μ * m := by nlinarith
  have hd : d ≤ a - 2 * μ * m := by nlinarith
  refine ⟨le_min hA (le_min hB hC),?_,?_,?_⟩
  · nlinarith
  · have hmax := max_le hb (max_le hc hd)
    linarith
  · nlinarith

end RegimeParameters


end MatchingStability

end PermutedModule6

/- Source module: EssentialVertex.lean -/
section PermutedModule7

/-!
Finite matching prerequisites for the connected-matching stability argument.

The essential-vertex argument uses the existing proved Tutte theorem.  It is
independent of all Erdős problem declarations and uses no additional axioms.
Credit: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

theorem perfect_matching_of_complete_unmatched_join
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching)
    (U W : Set V) (hd : Disjoint U W)
    (hcover : U ∪ W = M.vertsᶜ) (hcard : U.ncard = W.ncard)
    (hjoin : ∀ u ∈ U, ∀ w ∈ W, G.Adj u w) :
    ∃ P : G.Subgraph, P.IsPerfectMatching := by
  classical
  let f : U ≃ W := Fintype.equivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hcard)
  obtain ⟨N, hNv, hN⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
    (G := G) hd f (fun u => hjoin u u.property (f u) (f u).property)
  refine ⟨M ⊔ N, hM.sup hN ?_, ?_⟩
  · rw [hM.support_eq_verts, hN.support_eq_verts, hNv, hcover]
    exact disjoint_compl_right
  · rw [Subgraph.isSpanning_iff, Subgraph.verts_sup, hNv, hcover]
    exact M.verts.union_compl_self

theorem matching_restriction_of_perfect_matching
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (M : H.Subgraph) (hM : M.IsPerfectMatching) :
    ∃ N : G.Subgraph, N.IsMatching ∧
      N.vertsᶜ.ncard ≤ (Set.range f)ᶜ.ncard := by
  classical
  let N : G.Subgraph := {
    verts := {v | ∃ w, M.Adj (f v) (f w)}
    Adj := fun v w => M.Adj (f v) (f w)
    adj_sub := fun h => f.map_adj_iff.mp (M.adj_sub h)
    edge_vert := fun {v w} h => ⟨w, h⟩
    symm.symm := fun _ _ h => h.symm }
  have hN : N.IsMatching := by
    rintro v ⟨w, hvw⟩
    refine ⟨w, hvw, ?_⟩
    intro z hvz
    exact f.injective (hM.1.eq_of_adj_left hvz hvw)
  choose mate hmate using (Subgraph.isPerfectMatching_iff.mp hM)
  let outside : ↥(N.vertsᶜ) → ↥((Set.range f)ᶜ) := fun v =>
    ⟨mate (f v), by
      rintro ⟨w, hw⟩
      apply v.property
      exact ⟨w, hw ▸ (hmate (f v)).1⟩⟩
  have hinj : Function.Injective outside := by
    intro v w hvw
    apply Subtype.ext
    apply f.injective
    have hm : mate (f v) = mate (f w) := congrArg Subtype.val hvw
    exact hM.1.eq_of_adj_right ((hmate (f v)).1)
      (hm.symm ▸ (hmate (f w)).1)
  refine ⟨N, hN, ?_⟩
  simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective outside hinj

theorem tutte_violator_congr_outside
    {V : Type*} [Fintype V] {G H : SimpleGraph V} (S : Set V)
    (h : ∀ x ∉ S, ∀ y ∉ S, G.Adj x y ↔ H.Adj x y) :
    G.IsTutteViolator S ↔ H.IsTutteViolator S := by
  have heq : ((⊤ : G.Subgraph).deleteVerts S).coe =
      ((⊤ : H.Subgraph).deleteVerts S).coe := by
    ext x y
    change ((⊤ : G.Subgraph).deleteVerts S).Adj x.val y.val ↔
      ((⊤ : H.Subgraph).deleteVerts S).Adj x.val y.val
    constructor
    · intro hxy
      exact Subgraph.deleteVerts_adj.mpr ⟨by trivial,x.property.2,by trivial,y.property.2,
        (h x x.property.2 y y.property.2).mp (Subgraph.deleteVerts_adj.mp hxy).2.2.2.2⟩
    · intro hxy
      exact Subgraph.deleteVerts_adj.mpr ⟨by trivial,x.property.2,by trivial,y.property.2,
        (h x x.property.2 y y.property.2).mpr (Subgraph.deleteVerts_adj.mp hxy).2.2.2.2⟩
  have hc := congrArg (fun K : SimpleGraph ((⊤ : G.Subgraph).deleteVerts S).verts =>
    K.oddComponents.ncard) heq
  unfold SimpleGraph.IsTutteViolator
  exact ⟨fun hs => hs.trans_eq hc,fun hs => hs.trans_eq hc.symm⟩

theorem odd_components_le_one_of_preconnected
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Preconnected) :
    G.oddComponents.ncard ≤ 1 := by
  letI := hG.subsingleton_connectedComponent
  exact Set.ncard_le_one_of_subsingleton _

theorem universal_extension_matching_free
    {V : Type*} [Fintype V] (G : SimpleGraph V) (m q : ℕ)
    (hcard : Fintype.card V = 2 * m + q + 2)
    (hno : ∀ M : G.Subgraph, M.IsMatching → M.verts.ncard ≤ 2 * m) :
    ((Gᶜ ⊕g (⊥ : SimpleGraph (Fin q)))ᶜ).IsMatchingFree := by
  classical
  let H := (Gᶜ ⊕g (⊥ : SimpleGraph (Fin q)))ᶜ
  let f : G ↪g H := {
    toFun := Sum.inl
    inj' := Sum.inl_injective
    map_rel_iff' := by
      intro x y
      by_cases hxy : G.Adj x y
      · simp [H, hxy, hxy.ne]
      · simp [H, hxy] }
  intro P hP
  obtain ⟨M, hM, hcompl⟩ := matching_restriction_of_perfect_matching f P hP
  have hc : M.vertsᶜ.ncard ≤ q := by
    change M.vertsᶜ.ncard ≤ (Set.range (Sum.inl : V → V ⊕ Fin q))ᶜ.ncard at hcompl
    simpa only [Set.compl_range_inl,
      Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card,
      Fintype.card_fin] using hcompl
  have hm := hno M hM
  have hsum := Set.ncard_add_ncard_compl M.verts
  simp only [Nat.card_eq_fintype_card] at hsum
  omega

theorem universal_extension_barrier_meets_original
    {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (hG : G.Connected) (heven : Even (Fintype.card V + Fintype.card W))
    (S : Set (V ⊕ W))
    (hS : ((Gᶜ ⊕g (⊥ : SimpleGraph W))ᶜ).IsTutteViolator S) :
    ∃ v : V, Sum.inl v ∈ S := by
  classical
  by_contra! hnot
  let H := (Gᶜ ⊕g (⊥ : SimpleGraph W))ᶜ
  let K := ((⊤ : H.Subgraph).deleteVerts S).coe
  let old : G →g K := {
    toFun := fun v => ⟨Sum.inl v, by exact ⟨by trivial, hnot v⟩⟩
    map_rel' := by
      intro v w hvw
      exact Subgraph.deleteVerts_adj.mpr
        ⟨by trivial, hnot v, by trivial, hnot w, by simpa [H, hvw.ne] using hvw⟩ }
  obtain ⟨v₀⟩ := hG.nonempty
  have hreach : ∀ x, K.Reachable (old v₀) x := by
    rintro ⟨x, hx⟩
    cases x with
    | inl v =>
      have he : (⟨Sum.inl v,hx⟩ : ((⊤ : H.Subgraph).deleteVerts S).verts) = old v := by
        apply Subtype.ext
        rfl
      rw [he]
      exact (hG v₀ v).map old
    | inr w =>
      apply SimpleGraph.Adj.reachable
      exact Subgraph.deleteVerts_adj.mpr
        ⟨by trivial, hnot v₀, by trivial, hx.2, by simp [H]⟩
  have hK : K.Preconnected := fun x y => (hreach x).symm.trans (hreach y)
  have hle := odd_components_le_one_of_preconnected K hK
  have hlt : S.ncard < K.oddComponents.ncard := hS
  have hs0 : S.ncard = 0 := by omega
  have hsEmpty : S = ∅ := (Set.ncard_eq_zero (s := S) (Set.toFinite S)).mp hs0
  have hcardK : Nat.card ((⊤ : H.Subgraph).deleteVerts S).verts =
      Fintype.card V + Fintype.card W := by
    rw [hsEmpty, Subgraph.deleteVerts_empty]
    simp [Nat.card_eq_fintype_card]
  have hodd : Odd K.oddComponents.ncard := by
    have hc : K.oddComponents.ncard = 1 := by omega
    simp [hc]
  have := (odd_ncard_oddComponents K).mp hodd
  exact (Nat.not_odd_iff_even.mpr heven) (hcardK ▸ this)

theorem exists_essential_vertex
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (m : ℕ) (hsize : 2 * m + 2 ≤ Fintype.card V)
    (hno : ∀ M : G.Subgraph, M.IsMatching → M.verts.ncard ≤ 2 * m) :
    ∃ v : V, ∀ M : G.Subgraph, M.IsMatching →
      2 * m ≤ M.verts.ncard → v ∈ M.verts := by
  classical
  let q := Fintype.card V - (2 * m + 2)
  have hcard : Fintype.card V = 2 * m + q + 2 := by omega
  let H := (Gᶜ ⊕g (⊥ : SimpleGraph (Fin q)))ᶜ
  have hfree : H.IsMatchingFree := universal_extension_matching_free G m q hcard hno
  obtain ⟨S, hS⟩ : ∃ S, H.IsTutteViolator S := by
    by_contra! hn
    obtain ⟨P, hP⟩ := (SimpleGraph.tutte (G := H)).mpr hn
    exact hfree P hP
  have heven : Even (Fintype.card V + Fintype.card (Fin q)) := by
    simp only [Fintype.card_fin]
    exact ⟨m + q + 1, by omega⟩
  obtain ⟨v, hvS⟩ := universal_extension_barrier_meets_original G hG heven S hS
  refine ⟨v, ?_⟩
  intro M hM hlarge
  by_contra hv
  have hMcard : M.verts.ncard = 2 * m := le_antisymm (hno M hM) hlarge
  let J := H ⊔ SimpleGraph.fromRel (fun x _ : V ⊕ Fin q => x = Sum.inl v)
  let f : G →g J := {
    toFun := Sum.inl
    map_rel' := by
      intro x y hxy
      exact Or.inl (by simpa [H, hxy.ne] using hxy) }
  let N := M.map f
  have hN : N.IsMatching := hM.map f Sum.inl_injective
  have hNv : N.verts = Sum.inl '' M.verts := rfl
  let U : Set (V ⊕ Fin q) := Sum.inl '' (M.vertsᶜ \ {v})
  let W : Set (V ⊕ Fin q) := insert (Sum.inl v) (Set.range Sum.inr)
  have hd : Disjoint U W := by
    rw [Set.disjoint_left]
    rintro x ⟨u, hu, rfl⟩ hw
    rcases hw with h | ⟨w, hw⟩
    · exact hu.2 (Sum.inl_injective h)
    · cases hw
  have hcover : U ∪ W = N.vertsᶜ := by
    rw [hNv]
    ext x
    cases x with
    | inl u =>
      by_cases huv : u = v
      · simp [U, W, huv, hv]
      · simp [U, W, huv]
    | inr w => simp [U, W]
  have hcomplcard : M.vertsᶜ.ncard = q + 2 := by
    have hh := Set.ncard_add_ncard_compl M.verts
    simp only [Nat.card_eq_fintype_card] at hh
    omega
  have hUcard : U.ncard = q + 1 := by
    rw [Set.ncard_image_of_injective _ Sum.inl_injective]
    rw [Set.ncard_sdiff_singleton_of_mem hv, hcomplcard]
    omega
  have hWcard : W.ncard = q + 1 := by
    rw [Set.ncard_insert_of_notMem (by simp : Sum.inl v ∉ Set.range
      (Sum.inr : Fin q → V ⊕ Fin q))]
    rw [Set.ncard_range_of_injective Sum.inr_injective]
    simp
  have hjoin : ∀ x ∈ U, ∀ y ∈ W, J.Adj x y := by
    rintro x ⟨u, hu, rfl⟩ y hy
    rcases hy with rfl | ⟨w, rfl⟩
    · right
      exact ⟨by simpa using hu.2, Or.inr rfl⟩
    · left
      simp [H]
  obtain ⟨P, hP⟩ := perfect_matching_of_complete_unmatched_join J N hN U W hd
    hcover (hUcard.trans hWcard.symm) hjoin
  have hJS : J.IsTutteViolator S :=
    (tutte_violator_congr_outside S (G := H) (H := J) (by
      intro x hx y hy
      change H.Adj x y ↔ H.Adj x y ∨ (x ≠ y ∧ (x = Sum.inl v ∨ y = Sum.inl v))
      have hnx : x ≠ Sum.inl v := fun h => hx (h.symm ▸ hvS)
      have hny : y ≠ Sum.inl v := fun h => hy (h.symm ▸ hvS)
      simp [hnx, hny])).mp hS
  exact SimpleGraph.not_isTutteViolator_of_isPerfectMatching hP S hJS


end MatchingStability

end PermutedModule7

/- Source module: MatchingTrimming.lean -/
section PermutedModule8

/-!
Choosing an exact number of edges from a finite matching.
The erase-two-endpoints induction follows the matching-pair extraction method
in the accepted luczak_asymptotic_even.R1.H2 proof, with an arbitrary vertex
type and a closed vertex-set conclusion instead of an ordered list of edges.
Credit: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

theorem matching_closed_subset_card
    {V : Type*} {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching)
    (k : ℕ) (S : Finset V)
    (hSverts : ∀ x ∈ S, x ∈ M.verts)
    (hSclosed : ∀ x ∈ S, ∀ y, M.Adj x y → y ∈ S)
    (hScard : 2 * k ≤ S.card) :
    ∃ T : Finset V, T ⊆ S ∧ T.card = 2 * k ∧
      ∀ x ∈ T, ∀ y, M.Adj x y → y ∈ T := by
  classical
  induction k generalizing S with
  | zero => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨u, huS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    obtain ⟨v, huvAdj, _⟩ := hM (hSverts u huS)
    have hvS : v ∈ S := hSclosed u huS v huvAdj
    have huv : u ≠ v := huvAdj.ne
    let S' := (S.erase u).erase v
    have hS'sub : S' ⊆ S := by
      intro x hx
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have hS'closed : ∀ x ∈ S', ∀ y, M.Adj x y → y ∈ S' := by
      intro x hx y hxy
      have hxv : x ≠ v := Finset.ne_of_mem_erase hx
      have hxu : x ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
        hSclosed x (hS'sub hx) y hxy⟩⟩
      · rintro rfl
        exact hxu (hM.eq_of_adj_right hxy huvAdj)
      · rintro rfl
        exact hxv (hM.eq_of_adj_right hxy huvAdj.symm)
    have hS'card : 2 * k ≤ S'.card := by
      have hc1 := Finset.card_erase_of_mem huS
      have hc2 := Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨huv.symm, hvS⟩ : v ∈ S.erase u)
      change 2 * k ≤ ((S.erase u).erase v).card
      omega
    obtain ⟨T, hTsub, hTcard, hTclosed⟩ := ih S'
      (fun x hx => hSverts x (hS'sub hx)) hS'closed hS'card
    have huT : u ∉ T := by
      intro h
      exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (hTsub h)) rfl
    have hvT : v ∉ T := by
      intro h
      exact Finset.ne_of_mem_erase (hTsub h) rfl
    refine ⟨insert u (insert v T), ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact huS
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hvS
      · exact hS'sub (hTsub hx)
    · simp [Finset.card_insert_of_notMem, huT, hvT, huv, hTcard]
      omega
    · intro x hx y hxy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · have hy : y = v := hM.eq_of_adj_left hxy huvAdj
        simp [hy]
      rcases Finset.mem_insert.mp hx with rfl | hx
      · have hy : y = u := hM.eq_of_adj_left hxy huvAdj.symm
        simp [hy]
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hTclosed x hx y hxy))

theorem exists_submatching_card
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) (k : ℕ) (hk : 2 * k ≤ M.verts.ncard) :
    ∃ N : G.Subgraph, N ≤ M ∧ N.IsMatching ∧ N.verts.ncard = 2 * k := by
  classical
  obtain ⟨T, hTsub, hTcard, hTclosed⟩ := matching_closed_subset_card M hM k
    M.verts.toFinset (by simp) (by
      intro x hx y hxy
      simpa using hxy.snd_mem)
    (by simpa only [Set.ncard_eq_toFinset_card'] using hk)
  let N := M.induce (T : Set V)
  have hsub : N ≤ M := by
    constructor
    · intro x hx
      exact Set.mem_toFinset.mp (hTsub hx)
    · intro x y h
      exact h.2.2
  have hN : N.IsMatching := by
    intro x hx
    obtain ⟨y, hxy, huniq⟩ := hM (hsub.1 hx)
    refine ⟨y, ⟨hx, hTclosed x hx y hxy, hxy⟩, ?_⟩
    intro z hz
    exact huniq z hz.2.2
  refine ⟨N, hsub, hN, ?_⟩
  simpa [N] using hTcard


end MatchingStability

end PermutedModule8

/- Source module: FiniteMatchingCover.lean -/
section PermutedModule9

/-!
Finite bipartite vertex covers and conversion between edge families and
SimpleGraph matchings. The theorem `finite_konig_cover` is copied verbatim
apart from its name from the accepted proof
`proofs/Erdos1088.erdos_1088.lean`, theorem `E1088.konig_cover`.
The matching adapters are new. Credit for the new adapters: @fqlx.
-/

open SimpleGraph Finset

namespace MatchingStability

theorem finite_konig_cover {α β : Type*} [DecidableEq α] [DecidableEq β] (L : Finset α)
    (N : α → Finset β) (m : ℕ)
    (hno : ∀ M : Finset (α × β), (∀ p ∈ M, p.1 ∈ L ∧ p.2 ∈ N p.1) →
      (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 ∨ p.2 = q.2 → p = q) → M.card < m) :
    ∃ A ⊆ L, ∃ B : Finset β, (∀ a ∈ L, a ∉ A → N a ⊆ B) ∧ A.card + B.card < m := by
  classical
  have hm : 0 < m := hno ∅ (by simp) (by simp)
  by_cases hβ : Nonempty β
  swap
  · exact ⟨∅, empty_subset _, ∅, fun a _ _ b _ => (hβ ⟨b⟩).elim, by simpa using hm⟩
  obtain ⟨b0⟩ := hβ
  obtain ⟨S, hS, hmax⟩ := exists_max_image L.powerset
    (fun S => (S.card : ℤ) - (S.biUnion N).card) ⟨∅, empty_mem_powerset _⟩
  rw [mem_powerset] at hS
  set d : ℤ := (S.card : ℤ) - (S.biUnion N).card with hd
  have hd0 : 0 ≤ d := by
    have := hmax ∅ (empty_mem_powerset _); simpa using this
  set d' := d.toNat with hd'
  have hdd : (d' : ℤ) = d := Int.toNat_of_nonneg hd0
  let t : {a // a ∈ L} → Finset (β ⊕ Fin d') := fun a => (N a.1).disjSum Finset.univ
  have hHall : ∀ s : Finset {a // a ∈ L}, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
    · simp
    set s' := s.map (Function.Embedding.subtype _) with hs'
    have hs'L : s' ⊆ L := by
      intro a ha; obtain ⟨x, -, rfl⟩ := mem_map.1 ha; exact x.2
    have hsub : (s'.biUnion N).disjSum (Finset.univ : Finset (Fin d')) ⊆ s.biUnion t := by
      intro z hz
      rcases z with b | i
      · rw [inl_mem_disjSum, mem_biUnion] at hz
        obtain ⟨a, ha, hb⟩ := hz
        obtain ⟨x, hx, rfl⟩ := mem_map.1 ha
        exact mem_biUnion.2 ⟨x, hx, inl_mem_disjSum.2 hb⟩
      · exact mem_biUnion.2 ⟨a0, ha0, inr_mem_disjSum.2 (mem_univ _)⟩
    have h1 := card_le_card hsub
    rw [card_disjSum, card_univ, Fintype.card_fin] at h1
    have h2 := hmax s' (mem_powerset.2 hs'L)
    have h3 : s'.card = s.card := card_map _
    have : (s.card : ℤ) ≤ (s'.biUnion N).card + d' := by rw [hdd]; omega
    omega
  obtain ⟨f, hfinj, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective t).1 hHall
  set Ll := (Finset.univ : Finset {a // a ∈ L}).filter fun a => (f a).isLeft with hLl
  set Lr := (Finset.univ : Finset {a // a ∈ L}).filter fun a => ¬ (f a).isLeft with hLr
  let g : {a // a ∈ L} → β := fun a => Sum.elim id (fun _ => b0) (f a)
  have hgL : ∀ a ∈ Ll, f a = Sum.inl (g a) := by
    intro a ha
    have := (mem_filter.1 ha).2
    simp only [g]
    rcases h : f a with b | i
    · rfl
    · rw [h] at this; simp at this
  set M := Ll.image fun a => (a.1, g a) with hM
  have hMprop : ∀ p ∈ M, p.1 ∈ L ∧ p.2 ∈ N p.1 := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    refine ⟨a.2, ?_⟩
    have := hft a
    rw [hgL a ha] at this
    exact inl_mem_disjSum.1 this
  have hMinj : ∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 ∨ p.2 = q.2 → p = q := by
    intro p hp q hq h
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    obtain ⟨a', ha', rfl⟩ := mem_image.1 hq
    rcases h with h | h
    · have : a = a' := Subtype.ext h
      rw [this]
    · have : f a = f a' := by rw [hgL a ha, hgL a' ha']; simp only at h; rw [h]
      rw [hfinj this]
  have hMcard : M.card = Ll.card :=
    card_image_of_injective _ (fun a a' h => Subtype.ext (Prod.ext_iff.1 h).1)
  have hLrcard : Lr.card ≤ d' := by
    have hmaps : ∀ a ∈ Lr, f a ∈ (Finset.univ : Finset (Fin d')).map Function.Embedding.inr := by
      intro a ha
      have := (mem_filter.1 ha).2
      rcases h : f a with b | i
      · rw [h] at this; simp at this
      · exact mem_map.2 ⟨i, mem_univ _, rfl⟩
    have := card_le_card_of_injOn f hmaps (fun x _ y _ h => hfinj h)
    simpa using this
  have hsplit : Ll.card + Lr.card = L.card := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_coe]
  have hMlt := hno M hMprop hMinj
  refine ⟨L \ S, sdiff_subset, S.biUnion N, ?_, ?_⟩
  · intro a ha haA
    have haS : a ∈ S := by
      by_contra h; exact haA (mem_sdiff.2 ⟨ha, h⟩)
    exact subset_biUnion_of_mem N haS
  · rw [card_sdiff_of_subset hS]
    have hSL := card_le_card hS
    have : ((L.card - S.card + (S.biUnion N).card : ℕ) : ℤ) = L.card - d := by
      push_cast [Nat.cast_sub hSL]; rw [hd]; ring
    have h4 : (L.card : ℤ) - d < m := by rw [← hdd]; omega
    omega

theorem matching_of_injective_endpoints
    {V I : Type*} [Fintype V] [Fintype I] (G : SimpleGraph V)
    (left right : I → V) (hleft : Function.Injective left) (hright : Function.Injective right)
    (hdisj : ∀ i j, left i ≠ right j) (hedges : ∀ i, G.Adj (left i) (right i)) :
    ∃ M : G.Subgraph, M.IsMatching ∧
      M.verts = Set.range left ∪ Set.range right ∧ M.verts.ncard = 2 * Fintype.card I := by
  classical
  let eL := Equiv.ofInjective left hleft
  let eR := Equiv.ofInjective right hright
  let e : Set.range left ≃ Set.range right := eL.symm.trans eR
  have hd : Disjoint (Set.range left) (Set.range right) := by
    rw [Set.disjoint_left]
    rintro x ⟨i, rfl⟩ ⟨j, h⟩
    exact hdisj i j h.symm
  have hadj : ∀ x : Set.range left, G.Adj x (e x) := by
    intro x
    have hx : left (eL.symm x) = x := Equiv.apply_ofInjective_symm hleft x
    change G.Adj x (right (eL.symm x))
    rw [← hx]
    exact hedges _
  obtain ⟨M, hMv, hM⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hd e hadj
  refine ⟨M, hM, hMv, ?_⟩
  rw [hMv, Set.ncard_union_eq hd, Set.ncard_range_of_injective hleft,
    Set.ncard_range_of_injective hright, Nat.card_eq_fintype_card]
  omega

theorem bipartite_vertex_cover
    {V : Type*} [Fintype V] (G : SimpleGraph V) (A B : Finset V)
    (hdisj : Disjoint A B) (s : ℕ)
    (hbound : ∀ M : G.Subgraph, M.IsMatching → M.verts.ncard < 2 * s) :
    ∃ X ⊆ A, ∃ Y ⊆ B, X.card + Y.card < s ∧
      ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a ∈ X ∨ b ∈ Y := by
  classical
  let neighbors : V → Finset V := fun a => B.filter (G.Adj a)
  have hno : ∀ P : Finset (V × V),
      (∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ neighbors p.1) →
      (∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 ∨ p.2 = q.2 → p = q) → P.card < s := by
    intro P hP huniq
    let left : P → V := fun p => p.val.1
    let right : P → V := fun p => p.val.2
    have hleft : Function.Injective left := by
      intro p q h
      exact Subtype.ext (huniq p p.property q q.property (Or.inl h))
    have hright : Function.Injective right := by
      intro p q h
      exact Subtype.ext (huniq p p.property q q.property (Or.inr h))
    have hd : ∀ p q, left p ≠ right q := by
      intro p q h
      have hqB : right q ∈ B := (Finset.mem_filter.mp (hP q q.property).2).1
      have hpB : left p ∈ B := h.symm ▸ hqB
      exact Finset.disjoint_left.mp hdisj (hP p p.property).1
        hpB
    have he : ∀ p, G.Adj (left p) (right p) := fun p =>
      (Finset.mem_filter.mp (hP p p.property).2).2
    obtain ⟨M, hM, _, hc⟩ := matching_of_injective_endpoints G left right hleft hright hd he
    have hlt := hbound M hM
    simp only [Fintype.card_coe] at hc
    omega
  obtain ⟨X, hXA, Y₀, hcover, hcard⟩ := finite_konig_cover A neighbors s hno
  refine ⟨X, hXA, Y₀ ∩ B, Finset.inter_subset_right, ?_, ?_⟩
  · have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := Y₀) (s₂ := B))
    omega
  · intro a ha b hb hab
    by_cases hx : a ∈ X
    · exact Or.inl hx
    · exact Or.inr (Finset.mem_inter.mpr
        ⟨hcover a ha hx (Finset.mem_filter.mpr ⟨hb, hab⟩), hb⟩)


end MatchingStability

end PermutedModule9

/- Source module: ConnectedMatchingSupport.lean -/
section PermutedModule10

/-!
Common connected-matching interface and finite saturation existence.
Credit: @fqlx. The matching-size convention counts edges: a size-s matching
covers at least 2s vertices in one connected component.
-/

open SimpleGraph Set

namespace MatchingStability

def HasCM {V : Type*} (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∃ M : G.Subgraph, M.IsMatching ∧ 2*s ≤ M.verts.ncard ∧
    ∀ u∈M.verts, ∀ v∈M.verts, G.Reachable u v

theorem HasCM.map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {s : ℕ} (h : HasCM G s) (f : G →g H) (hf : Function.Injective f) : HasCM H s := by
  obtain ⟨M,hM,hsize,hcon⟩ := h
  refine ⟨M.map f,hM.map f hf,?_,?_⟩
  · simpa only [Subgraph.map_verts,Set.ncard_image_of_injective M.verts hf] using hsize
  · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
    exact (hcon u hu v hv).map f

theorem HasCM.mono {V : Type*} {G H : SimpleGraph V} {s : ℕ}
    (h : HasCM G s) (hle : G≤ H) : HasCM H s :=
  h.map (Hom.ofLE hle) Function.injective_id

theorem HasCM.of_preconnected {V : Type*} {G : SimpleGraph V} {s : ℕ}
    (hG : G.Preconnected) (M : G.Subgraph) (hM : M.IsMatching)
    (hsize : 2*s≤ M.verts.ncard) : HasCM G s :=
  ⟨M,hM,hsize,fun u _ v _ => hG u v⟩

theorem not_hasCM_iff_of_preconnected {V : Type*} {G : SimpleGraph V} (s : ℕ)
    (hG : G.Preconnected) :
    ¬ HasCM G s ↔ ∀ M : G.Subgraph, M.IsMatching → M.verts.ncard < 2*s := by
  constructor
  · intro h M hM
    by_contra hsize
    exact h (HasCM.of_preconnected hG M hM (by omega))
  · rintro h ⟨M,hM,hsize,_⟩
    exact (Nat.not_lt_of_ge hsize) (h M hM)

theorem component_matching_bound {V : Type*} {G : SimpleGraph V} (s : ℕ)
    (h : ¬ HasCM G s) (C : G.ConnectedComponent)
    (M : C.toSimpleGraph.Subgraph) (hM : M.IsMatching) : M.verts.ncard < 2*s := by
  by_contra hsize
  have hC : HasCM C.toSimpleGraph s :=
    HasCM.of_preconnected C.connected_toSimpleGraph.preconnected M hM (by omega)
  exact h (hC.map C.toSimpleGraph_hom Subtype.val_injective)

/-- Every finite multicolouring with no connected s-matching extends to one
maximal with that property. Edges may carry more than one colour. -/
theorem exists_maximal_multicolouring {V : Type*} [Finite V]
    (c : Fin 3 → SimpleGraph V) (s : ℕ) (hno : ∀ k, ¬ HasCM (c k) s) :
    ∃ C : Fin 3 → SimpleGraph V,
      c≤ C ∧ (∀ k, ¬ HasCM (C k) s) ∧
      ∀ D : Fin 3 → SimpleGraph V, C≤ D → (∀ k, ¬ HasCM (D k) s) → D=C := by
  obtain ⟨C,hcC,hC⟩ := Finite.exists_le_maximal
    (p:=fun C : Fin 3 → SimpleGraph V => ∀ k, ¬ HasCM (C k) s) hno
  exact ⟨C,hcC,hC.1,fun D hCD hD => le_antisymm (hC.2 hD hCD) hCD⟩

end MatchingStability


end PermutedModule10

/- Source module: BipartiteConnectedMatching.lean -/
section PermutedModule11

/-!
Connected matching constructions used in the exact two-color bipartite
classification. Credit: @fqlx.
-/

open SimpleGraph

namespace MatchingStability

theorem HasCM.of_complete_join
    {V : Type*} [Fintype V] (G : SimpleGraph V) (A B : Finset V) (s : ℕ)
    (hd : Disjoint A B) (hA : s ≤ A.card) (hB : s ≤ B.card)
    (hjoin : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) : HasCM G s := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : Fin s ↪ V, Set.range f ⊆ A :=
    Function.Embedding.exists_of_card_le_finset (by simpa using hA)
  obtain ⟨g, hg⟩ : ∃ g : Fin s ↪ V, Set.range g ⊆ B :=
    Function.Embedding.exists_of_card_le_finset (by simpa using hB)
  have hfA : ∀ i, f i ∈ A := fun i => hf ⟨i, rfl⟩
  have hgB : ∀ i, g i ∈ B := fun i => hg ⟨i, rfl⟩
  have hdisj : ∀ i j, f i ≠ g j := by
    intro i j h
    exact Finset.disjoint_left.mp hd (hfA i) (h.symm ▸ hgB j)
  obtain ⟨M, hM, hMv, hc⟩ := matching_of_injective_endpoints G f g
    f.injective g.injective hdisj (fun i => hjoin (f i) (hfA i) (g i) (hgB i))
  refine ⟨M, hM, by simpa using hc.ge, ?_⟩
  intro u hu v hv
  rw [hMv] at hu hv
  rcases hu with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases hv with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (hjoin (f i) (hfA i) (g i) (hgB i)).reachable.trans
      (hjoin (f j) (hfA j) (g i) (hgB i)).symm.reachable
  · exact (hjoin (f i) (hfA i) (g j) (hgB j)).reachable
  · exact (hjoin (f j) (hfA j) (g i) (hgB i)).symm.reachable
  · exact (hjoin (f i) (hfA i) (g i) (hgB i)).symm.reachable.trans
      (hjoin (f i) (hfA i) (g j) (hgB j)).reachable

theorem matching_bound_of_edges_in_one_component
    {V : Type*} {G : SimpleGraph V} (s : ℕ) (hno : ¬ HasCM G s)
    (C : G.ConnectedComponent) (hC : ∀ u v, G.Adj u v → u ∈ C.supp) :
    ∀ M : G.Subgraph, M.IsMatching → M.verts.ncard < 2 * s := by
  intro M hM
  by_contra! hbig
  apply hno
  refine ⟨M, hM, hbig, ?_⟩
  intro u hu v hv
  obtain ⟨u', huu', _⟩ := hM hu
  obtain ⟨v', hvv', _⟩ := hM hv
  exact C.reachable_of_mem_supp (hC u u' huu'.adj_sub) (hC v v' hvv'.adj_sub)

theorem HasCM.of_complete_join_and_extra_edge
    {V : Type*} [Fintype V] (G : SimpleGraph V) (A B : Finset V) (s : ℕ)
    (hd : Disjoint A B) (hA : s ≤ A.card) (hB : s + 1 ≤ B.card)
    (hjoin : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (x y : V) (hxA : x ∉ A) (hxB : x ∉ B) (hyB : y ∈ B)
    (hxy : G.Adj x y) : HasCM G (s + 1) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : Fin s ↪ V, Set.range f ⊆ A :=
    Function.Embedding.exists_of_card_le_finset (by simpa using hA)
  have hBerase : s ≤ (B.erase y).card := by
    rw [Finset.card_erase_of_mem hyB]
    omega
  obtain ⟨g, hg⟩ : ∃ g : Fin s ↪ V, Set.range g ⊆ B.erase y :=
    Function.Embedding.exists_of_card_le_finset (by simpa using hBerase)
  have hfA : ∀ i, f i ∈ A := fun i => hf ⟨i, rfl⟩
  have hgB : ∀ i, g i ∈ B := fun i => Finset.mem_of_mem_erase (hg ⟨i, rfl⟩)
  have hgNe : ∀ i, g i ≠ y := fun i => Finset.ne_of_mem_erase (hg ⟨i, rfl⟩)
  let left : Option (Fin s) → V
    | none => x
    | some i => f i
  let right : Option (Fin s) → V
    | none => y
    | some i => g i
  have hleft : Function.Injective left := by
    intro i j h
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        have hh : x = f j := h
        exact (hxA (hh.symm ▸ hfA j)).elim
    | some i =>
      cases j with
      | none =>
        have hh : f i = x := h
        exact (hxA (hh ▸ hfA i)).elim
      | some j => exact congrArg some (f.injective h)
  have hright : Function.Injective right := by
    intro i j h
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact (hgNe j (show y = g j from h).symm).elim
    | some i =>
      cases j with
      | none => exact (hgNe i h).elim
      | some j => exact congrArg some (g.injective h)
  have hrightB : ∀ i, right i ∈ B := by
    intro i
    cases i with
    | none => exact hyB
    | some i => exact hgB i
  have hdisj : ∀ i j, left i ≠ right j := by
    intro i j h
    have hmem : left i ∈ B := h.symm ▸ hrightB j
    cases i with
    | none => exact hxB hmem
    | some i => exact Finset.disjoint_left.mp hd (hfA i) hmem
  have hedges : ∀ i, G.Adj (left i) (right i) := by
    intro i
    cases i with
    | none => exact hxy
    | some i => exact hjoin (f i) (hfA i) (g i) (hgB i)
  obtain ⟨M, hM, hMv, hc⟩ := matching_of_injective_endpoints G left right
    hleft hright hdisj hedges
  have hleftReach : ∀ i, G.Reachable (left i) y := by
    intro i
    cases i with
    | none => exact hxy.reachable
    | some i => exact (hjoin (f i) (hfA i) y hyB).reachable
  have hrightReach : ∀ i, G.Reachable (right i) y := by
    intro i
    cases i with
    | none => exact SimpleGraph.Reachable.rfl
    | some i =>
      exact (hjoin (f i) (hfA i) (g i) (hgB i)).symm.reachable.trans
        (hjoin (f i) (hfA i) y hyB).reachable
  have hreach : ∀ u ∈ M.verts, G.Reachable u y := by
    intro u hu
    rw [hMv] at hu
    rcases hu with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hleftReach i
    · exact hrightReach i
  refine ⟨M, hM, ?_, fun u hu v hv => (hreach u hu).trans (hreach v hv).symm⟩
  simpa using hc.ge


end MatchingStability

end PermutedModule11

/- Source module: ConnectedMatchingBridges.lean -/
section PermutedModule12

/-!
Joining disjoint matching families through an edge between their connected
regions. Credit: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

theorem HasCM.of_two_matchings
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching)
    (hd : Disjoint M.verts N.verts) (s t : ℕ)
    (hsizeM : 2 * s ≤ M.verts.ncard) (hsizeN : 2 * t ≤ N.verts.ncard)
    (x y : V) (hMr : ∀ u ∈ M.verts, G.Reachable u x)
    (hNr : ∀ v ∈ N.verts, G.Reachable v y) (hxy : G.Reachable x y) :
    HasCM G (s + t) := by
  have hsup : (M ⊔ N).IsMatching := hM.sup hN (by
    simpa only [hM.support_eq_verts, hN.support_eq_verts] using hd)
  have hcard : (M ⊔ N).verts.ncard = M.verts.ncard + N.verts.ncard := by
    rw [Subgraph.verts_sup, Set.ncard_union_eq hd]
  have hr : ∀ u ∈ (M ⊔ N).verts, G.Reachable u x := by
    intro u hu
    rcases hu with hu | hu
    · exact hMr u hu
    · exact (hNr u hu).trans hxy.symm
  exact ⟨M ⊔ N, hsup, by omega, fun u hu v hv => (hr u hu).trans (hr v hv).symm⟩

theorem matching_in_complete_join
    {V : Type*} [Fintype V] (G : SimpleGraph V) (A B : Finset V) (s : ℕ)
    (hd : Disjoint A B) (hA : s ≤ A.card) (hB : s ≤ B.card)
    (hjoin : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    ∃ M : G.Subgraph, M.IsMatching ∧ 2 * s ≤ M.verts.ncard ∧
      M.verts ⊆ (A : Set V) ∪ (B : Set V) ∧
      ∀ u ∈ M.verts, ∀ x ∈ (A : Set V) ∪ (B : Set V), G.Reachable u x := by
  classical
  let H := G.between (A : Set V) (B : Set V)
  obtain ⟨M₀, hM₀, hsize, _⟩ := HasCM.of_complete_join H A B s hd hA hB
    (fun a ha b hb => ⟨hjoin a ha b hb, Or.inl ⟨ha, hb⟩⟩)
  let M := M₀.map (Hom.ofLE (G.between_le (s := (A : Set V)) (t := (B : Set V))))
  have hM : M.IsMatching := hM₀.map_ofLE G.between_le
  have hMv : M.verts = M₀.verts := by simp [M, Subgraph.map_verts]
  refine ⟨M, hM, by simpa only [hMv] using hsize, ?_, ?_⟩
  · intro u hu
    rw [hMv] at hu
    obtain ⟨v, huv, _⟩ := hM₀ hu
    rcases huv.adj_sub.2 with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  · intro u hu x hx
    rw [hMv] at hu
    obtain ⟨v, huv, _⟩ := hM₀ hu
    rcases huv.adj_sub.2 with ⟨huA, hvB⟩ | ⟨huB, hvA⟩ <;>
      rcases hx with hxA | hxB
    · exact huv.adj_sub.1.reachable.trans (hjoin x hxA v hvB).symm.reachable
    · exact (hjoin u huA x hxB).reachable
    · exact (hjoin x hxA u huB).symm.reachable
    · exact huv.adj_sub.1.reachable.trans (hjoin v hvA x hxB).reachable

theorem HasCM.of_bridged_complete_joins
    {V : Type*} [Fintype V] (G : SimpleGraph V) (A B C D : Finset V) (s t : ℕ)
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hregions : Disjoint ((A : Set V) ∪ (B : Set V)) ((C : Set V) ∪ (D : Set V)))
    (hA : s ≤ A.card) (hB : s ≤ B.card) (hC : t ≤ C.card) (hD : t ≤ D.card)
    (hjoinAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hjoinCD : ∀ c ∈ C, ∀ d ∈ D, G.Adj c d)
    (x y : V) (hx : x ∈ (A : Set V) ∪ (B : Set V))
    (hy : y ∈ (C : Set V) ∪ (D : Set V)) (hxy : G.Adj x y) :
    HasCM G (s + t) := by
  obtain ⟨M, hM, hsizeM, hsubM, hrM⟩ := matching_in_complete_join G A B s hAB hA hB hjoinAB
  obtain ⟨N, hN, hsizeN, hsubN, hrN⟩ := matching_in_complete_join G C D t hCD hC hD hjoinCD
  exact HasCM.of_two_matchings G M N hM hN (hregions.mono hsubM hsubN) s t
    hsizeM hsizeN x y (fun u hu => hrM u hu x hx) (fun v hv => hrN v hv y hy) hxy.reachable


end MatchingStability

end PermutedModule12

/- Source module: StripCliqueCleanup.lean -/
section PermutedModule13

/-!
Quantitative cleaning of a red/blue strip into a clique of the third colour.
This is the finite matching argument in Section 4 of
`finite_matching_stability_blueprint.md`, based on Letzter's connected-matching
method. The constants count deleted vertices, not matching edges.
Credit: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

/-- An internal matching can be extended through a complete join, with every
matching edge in the same connected component. -/
theorem HasCM.of_internal_matching_and_join
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (X W : Finset V) (s : ℕ)
    (hdis : Disjoint X W) (hX : X.Nonempty) (hXs : X.card ≤ s)
    (hcapacity : 2 * s ≤ W.card + X.card)
    (hjoin : ∀ x ∈ X, ∀ w ∈ W, G.Adj x w)
    (M : G.Subgraph) (hM : M.IsMatching)
    (hMW : M.verts ⊆ (W : Set V))
    (hsize : 2 * (s - X.card) ≤ M.verts.ncard) :
    HasCM G s := by
  classical
  obtain ⟨N, hNM, hN, hNsize⟩ := exists_submatching_card M hM (s - X.card) hsize
  have hNW : N.verts ⊆ (W : Set V) := hNM.1.trans hMW
  have hNfin : N.verts.toFinset ⊆ W := by
    intro x hx
    exact hNW (Set.mem_toFinset.mp hx)
  have hNcard : N.verts.toFinset.card = 2 * (s - X.card) := by
    simpa only [← Set.ncard_eq_toFinset_card'] using hNsize
  let B := W \ N.verts.toFinset
  have hBcard : X.card ≤ B.card := by
    have hc : B.card = W.card - N.verts.toFinset.card :=
      Finset.card_sdiff_of_subset hNfin
    omega
  have hXB : Disjoint X B := hdis.mono_right Finset.sdiff_subset
  obtain ⟨J, hJ, hJsize, hJsub, hJreach⟩ :=
    matching_in_complete_join G X B X.card hXB le_rfl hBcard
      (fun x hx w hw => hjoin x hx w ((Finset.mem_sdiff.mp hw).1))
  have hNJ : Disjoint N.verts J.verts := by
    rw [Set.disjoint_left]
    intro u huN huJ
    rcases hJsub huJ with huX | huB
    · exact Finset.disjoint_left.mp hdis huX (hNW huN)
    · exact (Finset.mem_sdiff.mp huB).2 (Set.mem_toFinset.mpr huN)
  obtain ⟨x, hx⟩ := hX
  have hCM := HasCM.of_two_matchings G N J hN hJ hNJ (s - X.card) X.card
    (le_of_eq hNsize.symm) hJsize x x
    (fun u hu => (hjoin x hx u (hNW hu)).symm.reachable)
    (fun u hu => hJreach u hu x (Or.inl hx)) SimpleGraph.Reachable.rfl
  simpa only [Nat.sub_add_cancel hXs] using hCM

/-- Endpoints of a maximal matching cover every edge. If no matching has
`ell` edges, this uses at most `2 * (ell - 1)` vertices. -/
theorem exists_small_cover_of_internal_matching_bound
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (W : Finset V) (ell : ℕ) (hell : 1 ≤ ell)
    (hbound : ∀ M : G.Subgraph, M.IsMatching →
      M.verts ⊆ (W : Set V) → M.verts.ncard < 2 * ell) :
    ∃ D : Finset V, D ⊆ W ∧ D.card ≤ 2 * (ell - 1) ∧
      ∀ u ∈ W, ∀ v ∈ W, G.Adj u v → u ∈ D ∨ v ∈ D := by
  classical
  have hbot : (⊥ : G.Subgraph).IsMatching ∧
      (⊥ : G.Subgraph).verts ⊆ (W : Set V) := by
    constructor
    · intro v hv
      exact hv.elim
    · exact Set.empty_subset _
  obtain ⟨M, _, hmax⟩ := Finite.exists_le_maximal
    (p := fun M : G.Subgraph => M.IsMatching ∧ M.verts ⊆ (W : Set V)) hbot
  have hM := hmax.1.1
  have hMW := hmax.1.2
  refine ⟨M.verts.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    exact hMW (Set.mem_toFinset.mp hx)
  · have hlt := hbound M hM hMW
    rw [Set.ncard_eq_toFinset_card'] at hlt
    obtain ⟨k, hk⟩ := hM.even_card
    omega
  · intro u hu v hv huv
    by_contra hn
    push Not at hn
    have huM : u ∉ M.verts := by simpa using hn.1
    have hvM : v ∉ M.verts := by simpa using hn.2
    let E := G.subgraphOfAdj huv
    have hE : E.IsMatching := Subgraph.IsMatching.subgraphOfAdj huv
    have hEM : Disjoint M.verts E.verts := by
      rw [Set.disjoint_left]
      intro z hzM hzE
      have hz : z = u ∨ z = v := by simpa [E, subgraphOfAdj_verts] using hzE
      rcases hz with rfl | rfl
      · exact huM hzM
      · exact hvM hzM
    have hsup : (M ⊔ E).IsMatching := hM.sup hE (by
      simpa only [hM.support_eq_verts, hE.support_eq_verts] using hEM)
    have hsupW : (M ⊔ E).verts ⊆ (W : Set V) := by
      intro z hz
      rcases hz with hzM | hzE
      · exact hMW hzM
      · have hz : z = u ∨ z = v := by simpa [E, subgraphOfAdj_verts] using hzE
        rcases hz with rfl | rfl
        · exact hu
        · exact hv
    have hle : M ⊔ E ≤ M := hmax.2 ⟨hsup, hsupW⟩ le_sup_left
    apply huM
    exact hle.1 (Or.inr (by simp [E, subgraphOfAdj_verts]))

/-- Removing the endpoints of two small internal matchings leaves a clique
in the third colour. The two endpoint sets are chosen independently. -/
theorem strip_clique_cleanup
    {V : Type*} [Fintype V] (R B G : SimpleGraph V)
    (X Y W : Finset V) (s : ℕ)
    (hXW : Disjoint X W) (hYW : Disjoint Y W)
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXs : X.card < s) (hYs : Y.card < s)
    (hcapX : 2 * s ≤ W.card + X.card)
    (hcapY : 2 * s ≤ W.card + Y.card)
    (hred : ∀ x ∈ X, ∀ w ∈ W, R.Adj x w)
    (hblue : ∀ y ∈ Y, ∀ w ∈ W, B.Adj y w)
    (hcover : ∀ u ∈ W, ∀ v ∈ W, u ≠ v →
      R.Adj u v ∨ B.Adj u v ∨ G.Adj u v)
    (hnoR : ¬ HasCM R s) (hnoB : ¬ HasCM B s) :
    ∃ W' : Finset V, W' ⊆ W ∧
      W.card ≤ W'.card + 2 * (s - X.card - 1) + 2 * (s - Y.card - 1) ∧
      G.IsClique (W' : Set V) := by
  classical
  have hRbound : ∀ M : R.Subgraph, M.IsMatching →
      M.verts ⊆ (W : Set V) → M.verts.ncard < 2 * (s - X.card) := by
    intro M hM hMW
    by_contra hn
    exact hnoR (HasCM.of_internal_matching_and_join R X W s hXW hX hXs.le
      hcapX hred M hM hMW (by omega))
  have hBbound : ∀ M : B.Subgraph, M.IsMatching →
      M.verts ⊆ (W : Set V) → M.verts.ncard < 2 * (s - Y.card) := by
    intro M hM hMW
    by_contra hn
    exact hnoB (HasCM.of_internal_matching_and_join B Y W s hYW hY hYs.le
      hcapY hblue M hM hMW (by omega))
  obtain ⟨D_R, hDRW, hDRcard, hDRcover⟩ :=
    exists_small_cover_of_internal_matching_bound R W (s - X.card) (by omega) hRbound
  obtain ⟨D_B, hDBW, hDBcard, hDBcover⟩ :=
    exists_small_cover_of_internal_matching_bound B W (s - Y.card) (by omega) hBbound
  let W' := W \ (D_R ∪ D_B)
  refine ⟨W', Finset.sdiff_subset, ?_, ?_⟩
  · have hDW : D_R ∪ D_B ⊆ W := Finset.union_subset hDRW hDBW
    have hc : W'.card = W.card - (D_R ∪ D_B).card :=
      Finset.card_sdiff_of_subset hDW
    have hu := Finset.card_union_le D_R D_B
    have hl := Finset.card_le_card hDW
    omega
  · intro u hu v hv huv
    have huW : u ∈ W := (Finset.mem_sdiff.mp hu).1
    have hvW : v ∈ W := (Finset.mem_sdiff.mp hv).1
    have huD : u ∉ D_R ∪ D_B := (Finset.mem_sdiff.mp hu).2
    have hvD : v ∉ D_R ∪ D_B := (Finset.mem_sdiff.mp hv).2
    rcases hcover u huW v hvW huv with hr | hb | hg
    · rcases hDRcover u huW v hvW hr with hur | hvr
      · exact (huD (Finset.mem_union_left _ hur)).elim
      · exact (hvD (Finset.mem_union_left _ hvr)).elim
    · rcases hDBcover u huW v hvW hb with hub | hvb
      · exact (huD (Finset.mem_union_right _ hub)).elim
      · exact (hvD (Finset.mem_union_right _ hvb)).elim
    · exact hg


end MatchingStability

end PermutedModule13

/- Source module: StripCliqueQuantitative.lean -/
section PermutedModule14

/-!
The numerical strip-cleaning bound used in the finite stability theorem.
Credit: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

/-- At the stability scale `s = m + h`, strip cleaning loses at most
`40h - 8` vertices and leaves a clique on at least `2m - 58h + 10` vertices. -/
theorem strip_clique_cleanup_quantitative
    {V : Type*} [Fintype V] (R B G : SimpleGraph V)
    (X Y W : Finset V) (m h : ℕ) (hh : 1 ≤ h) (hm : 1000 * h ≤ m)
    (hXW : Disjoint X W) (hYW : Disjoint Y W)
    (hXlower : m - 9 * h + 1 ≤ X.card)
    (hYlower : m - 9 * h + 1 ≤ Y.card)
    (hXupper : X.card ≤ m + h - 1)
    (hYupper : Y.card ≤ m + h - 1)
    (hWlower : 2 * (m - 9 * h + 1) ≤ W.card)
    (hred : ∀ x ∈ X, ∀ w ∈ W, R.Adj x w)
    (hblue : ∀ y ∈ Y, ∀ w ∈ W, B.Adj y w)
    (hcover : ∀ u ∈ W, ∀ v ∈ W, u ≠ v →
      R.Adj u v ∨ B.Adj u v ∨ G.Adj u v)
    (hnoR : ¬ HasCM R (m + h)) (hnoB : ¬ HasCM B (m + h)) :
    ∃ W' : Finset V, W' ⊆ W ∧
      2 * m - 58 * h + 10 ≤ W'.card ∧ G.IsClique (W' : Set V) := by
  obtain ⟨W', hW'W, hloss, hclique⟩ := strip_clique_cleanup R B G X Y W (m + h)
    hXW hYW (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega))
    (by omega) (by omega) (by omega) (by omega)
    hred hblue hcover hnoR hnoB
  refine ⟨W', hW'W, ?_, hclique⟩
  omega


end MatchingStability

end PermutedModule14

/- Source module: StripCliqueExclusive.lean -/
section PermutedModule15

/-!
Exclusive-colour versions of strip cleaning, needed when the reduced graph is
multicoloured. Applying the cleaning proof to `G \ (R ⊔ B)` records absence
of both other colours, not just the presence of the third one.
Credit: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

theorem three_colour_cover_sdiff
    {V : Type*} (R B G : SimpleGraph V) (u v : V)
    (h : R.Adj u v ∨ B.Adj u v ∨ G.Adj u v) :
    R.Adj u v ∨ B.Adj u v ∨ (G \ (R ⊔ B)).Adj u v := by
  by_cases hr : R.Adj u v
  · exact Or.inl hr
  by_cases hb : B.Adj u v
  · exact Or.inr (Or.inl hb)
  refine Or.inr (Or.inr ⟨(h.resolve_left hr).resolve_left hb, ?_⟩)
  exact fun h => h.elim hr hb

theorem strip_clique_cleanup_exclusive
    {V : Type*} [Fintype V] (R B G : SimpleGraph V)
    (X Y W : Finset V) (s : ℕ)
    (hXW : Disjoint X W) (hYW : Disjoint Y W)
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXs : X.card < s) (hYs : Y.card < s)
    (hcapX : 2 * s ≤ W.card + X.card)
    (hcapY : 2 * s ≤ W.card + Y.card)
    (hred : ∀ x ∈ X, ∀ w ∈ W, R.Adj x w)
    (hblue : ∀ y ∈ Y, ∀ w ∈ W, B.Adj y w)
    (hcover : ∀ u ∈ W, ∀ v ∈ W, u ≠ v →
      R.Adj u v ∨ B.Adj u v ∨ G.Adj u v)
    (hnoR : ¬ HasCM R s) (hnoB : ¬ HasCM B s) :
    ∃ W' : Finset V, W' ⊆ W ∧
      W.card ≤ W'.card + 2 * (s - X.card - 1) + 2 * (s - Y.card - 1) ∧
      (G \ (R ⊔ B)).IsClique (W' : Set V) :=
  strip_clique_cleanup R B (G \ (R ⊔ B)) X Y W s hXW hYW hX hY hXs hYs
    hcapX hcapY hred hblue
    (fun u hu v hv hne => three_colour_cover_sdiff R B G u v (hcover u hu v hv hne))
    hnoR hnoB

theorem strip_clique_cleanup_quantitative_exclusive
    {V : Type*} [Fintype V] (R B G : SimpleGraph V)
    (X Y W : Finset V) (m h : ℕ) (hh : 1 ≤ h) (hm : 1000 * h ≤ m)
    (hXW : Disjoint X W) (hYW : Disjoint Y W)
    (hXlower : m - 9 * h + 1 ≤ X.card)
    (hYlower : m - 9 * h + 1 ≤ Y.card)
    (hXupper : X.card ≤ m + h - 1)
    (hYupper : Y.card ≤ m + h - 1)
    (hWlower : 2 * (m - 9 * h + 1) ≤ W.card)
    (hred : ∀ x ∈ X, ∀ w ∈ W, R.Adj x w)
    (hblue : ∀ y ∈ Y, ∀ w ∈ W, B.Adj y w)
    (hcover : ∀ u ∈ W, ∀ v ∈ W, u ≠ v →
      R.Adj u v ∨ B.Adj u v ∨ G.Adj u v)
    (hnoR : ¬ HasCM R (m + h)) (hnoB : ¬ HasCM B (m + h)) :
    ∃ W' : Finset V, W' ⊆ W ∧
      2 * m - 58 * h + 10 ≤ W'.card ∧ (G \ (R ⊔ B)).IsClique (W' : Set V) :=
  strip_clique_cleanup_quantitative R B (G \ (R ⊔ B)) X Y W m h hh hm hXW hYW
    hXlower hYlower hXupper hYupper hWlower hred hblue
    (fun u hu v hv hne => three_colour_cover_sdiff R B G u v (hcover u hu v hv hne))
    hnoR hnoB


end MatchingStability

end PermutedModule15

/- Source module: FourCoreExtremal.lean -/
section PermutedModule16

/-!
The balanced and intermediate-size regimes of an exclusive four-class core,
and the exclusive clique obtained in the small-class regime.
Credit: @fqlx.
-/

open SimpleGraph Finset

namespace MatchingStability
namespace QuantitativeFourBlockCore

variable {V : Type*} [Fintype V] [DecidableEq V]
  {c : Fin 3 → SimpleGraph V} {m h : ℕ} {α μ δ : ℝ}

theorem W_lower_real (p : QuantitativeFourBlockCore c m h) (hm : 4 * h ≤ m) :
    (m : ℝ) - 4 * h ≤ p.W.card := by
  have hzw := p.cardZW
  have ho := p.orderedZW
  have hn : m ≤ p.W.card + 4 * h := by omega
  have hr : (m : ℝ) ≤ (p.W.card : ℝ) + 4 * h := by exact_mod_cast hn
  linarith

theorem toEC1 (p : QuantitativeFourBlockCore c m h)
    (a : RegimeParameters m h α μ δ) (hV : Fintype.card V = 4 * m)
    (hZ : (1 - α / 100) * m ≤ (p.Z.card : ℝ)) : FiniteEC1 c m α := by
  have hm4 : 4 * h ≤ m := by have hh := a.largeM; omega
  have hx := a.balanced_lower_of_near_m (p.X.card : ℝ) (by
    have hh := a.cast_lower p.X.card p.lowerX
    linarith)
  have hy := a.balanced_lower_of_near_m (p.Y.card : ℝ) (by
    have hh := a.cast_lower p.Y.card p.lowerY
    linarith)
  have hw := a.balanced_lower_of_near_m (p.W.card : ℝ) (by
    have hh := p.W_lower_real hm4
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    linarith)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hαm := mul_nonneg a.alpha_pos.le hm0
  have hαupper := mul_le_mul_of_nonneg_right a.alpha_small hm0
  have hz : (1 - α) * m ≤ (p.Z.card : ℝ) ∧ (m : ℝ) / 2 ≤ p.Z.card := by
    constructor <;> nlinarith
  have hsizes : ∀ i, (1 - α) * m ≤ ((p.ec1Blocks i).card : ℝ) := by
    intro i
    fin_cases i
    · exact hx.1
    · exact hz.1
    · exact hy.1
    · exact hw.1
  have hcores : ∀ i, (m : ℝ) / 2 ≤ ((p.ec1Blocks i).card : ℝ) := by
    intro i
    fin_cases i
    · exact hx.2
    · exact hz.2
    · exact hy.2
    · exact hw.2
  let T := FinitePartitionExtension.extend p.ec1Blocks 3
  refine ⟨p.colors,T,extend_is_partition _ _ p.ec1Blocks_disjoint,?_,?_⟩
  · intro i
    exact (hsizes i).trans (Nat.cast_le.mpr (card_le_card
      (FinitePartitionExtension.subset_extend p.ec1Blocks 3 i)))
  · apply extended_exclusive_densities c p.colors p.ec1Blocks 3 α ((m : ℝ) / 2)
      EC1Joins a.alpha_pos.le (by positivity) hcores EC1Joins_nonempty p.ec1Blocks_good
    rw [p.ec1Blocks_outside_card hV hm4,hV]
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
    nlinarith [a.ec1_budget]

theorem toStrongEC3 (p : QuantitativeFourBlockCore c m h)
    (a : RegimeParameters m h α μ δ) (hV : Fintype.card V = 4 * m)
    (hZlower : α / 100 * m ≤ (p.Z.card : ℝ))
    (hZupper : (p.Z.card : ℝ) ≤ (1 - α / 100) * m) :
    StrongFiniteEC3 c m μ δ := by
  have hm4 : 4 * h ≤ m := by have hh := a.largeM; omega
  have hO := p.ec3Blocks_outside_card hV hm4
  let T := FinitePartitionExtension.extend p.ec3Blocks 0
  have hT0 : (T 0).card = p.W.card + 16 * h := by
    change (FinitePartitionExtension.extend p.ec3Blocks 0 0).card = _
    rw [FinitePartitionExtension.extend_card,hO]
    simp [ec3Blocks]
  have hT1 : (T 1).card = p.X.card := by simp [T,FinitePartitionExtension.extend,ec3Blocks]
  have hT2 : (T 2).card = p.Y.card := by simp [T,FinitePartitionExtension.extend,ec3Blocks]
  have hT3 : (T 3).card = p.Z.card := by simp [T,FinitePartitionExtension.extend,ec3Blocks]
  have hADnat : (T 0).card + (T 3).card = 2 * m + 8 * h := by
    have hh := p.cardZW
    omega
  have hAD : ((T 0).card : ℝ) + (T 3).card = 2 * m + 8 * h := by exact_mod_cast hADnat
  have hXl := a.cast_lower p.X.card p.lowerX
  have hYl := a.cast_lower p.Y.card p.lowerY
  have hXu := a.cast_upper p.X.card p.upperX
  have hYu := a.cast_upper p.Y.card p.upperY
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hμm := mul_nonneg a.mu_pos.le hm0
  have hhalf := mul_le_mul_of_nonneg_right a.mu_le_half hm0
  have hsmall := a.hMu
  have hWl := p.W_lower_real hm4
  have hgap := a.tau_gap
  have hcores : ∀ i, μ * m ≤ ((p.ec3Blocks i).card : ℝ) := by
    intro i
    fin_cases i
    · change μ * m ≤ (p.W.card : ℝ)
      nlinarith
    · change μ * m ≤ (p.X.card : ℝ)
      nlinarith
    · change μ * m ≤ (p.Y.card : ℝ)
      nlinarith
    · change μ * m ≤ (p.Z.card : ℝ)
      nlinarith
  refine ⟨p.ec3Colors,T,extend_is_partition _ _ p.ec3Blocks_disjoint,?_,?_⟩
  · exact a.strong_ec3_numeric _ _ _ _ hAD
      (by simpa [hT1] using hXl) (by simpa [hT2] using hYl)
      (by simpa [hT1] using hXu) (by simpa [hT2] using hYu)
      (by simpa [hT3] using hZlower) (by simpa [hT3] using hZupper)
  · apply extended_exclusive_densities c p.ec3Colors p.ec3Blocks 0 δ (μ * m)
      EC1Joins a.delta_pos.le hμm hcores EC1Joins_nonempty p.ec3Blocks_good
    rw [hO,hV]
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
    nlinarith [a.ec3_budget]

theorem smallZ_exclusive_clique (p : QuantitativeFourBlockCore c m h)
    (a : RegimeParameters m h α μ δ)
    (hcover : ∀ u v : V, u ≠ v → ∃ k, (c k).Adj u v)
    (hno : ∀ k, ¬ HasCM (c k) (m + h))
    (hZ : (p.Z.card : ℝ) ≤ α / 100 * m) :
    ∃ W' : Finset V, W' ⊆ p.W ∧
      (2 - α / 100) * m - 58 * h ≤ (W'.card : ℝ) ∧
      ∀ u ∈ W', ∀ v ∈ W', u ≠ v → Exclusive c (p.colors 2) u v := by
  have hlarge := a.largeM
  have hposH := a.positiveH
  have hm4 : 4 * h ≤ m := by omega
  have hxy := p.lowerX
  have hyy := p.lowerY
  have hxup := p.upperX
  have hyup := p.upperY
  have hXl := a.cast_lower p.X.card p.lowerX
  have hYl := a.cast_lower p.Y.card p.lowerY
  have hsumNat : p.Z.card + p.W.card + 8 * h = 2 * m := by
    have hh := p.cardZW
    omega
  have hsum : (p.Z.card : ℝ) + p.W.card + 8 * h = 2 * m := by exact_mod_cast hsumNat
  have hlargeR : 1000 * (h : ℝ) ≤ m := by exact_mod_cast hlarge
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hαupper := mul_le_mul_of_nonneg_right a.alpha_small hm0
  have hcapX : 2 * (m + h) ≤ p.W.card + p.X.card := by
    have hr : 2 * ((m : ℝ) + h) ≤ (p.W.card : ℝ) + p.X.card := by nlinarith
    exact_mod_cast hr
  have hcapY : 2 * (m + h) ≤ p.W.card + p.Y.card := by
    have hr : 2 * ((m : ℝ) + h) ≤ (p.W.card : ℝ) + p.Y.card := by nlinarith
    exact_mod_cast hr
  have hpermCover : ∀ u ∈ p.W, ∀ v ∈ p.W, u ≠ v →
      (c (p.colors 0)).Adj u v ∨ (c (p.colors 1)).Adj u v ∨ (c (p.colors 2)).Adj u v := by
    intro u _ v _ huv
    obtain ⟨k,hk⟩ := hcover u v huv
    obtain ⟨i,hi⟩ : ∃ i, (c (p.colors i)).Adj u v :=
      ⟨p.colors.symm k,by simpa using hk⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  obtain ⟨W',hW'W,hloss,hclique⟩ := strip_clique_cleanup_exclusive
    (c (p.colors 0)) (c (p.colors 1)) (c (p.colors 2)) p.Y p.X p.W (m + h)
    (p.disjointSides.mono subset_union_right subset_union_right)
    (p.disjointSides.mono subset_union_left subset_union_right)
    (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega))
    (by omega) (by omega) hcapY hcapX
    (fun y hy w hw => (p.redYW y hy w hw).1)
    (fun x hx w hw => (p.blueXW x hx w hw).1)
    hpermCover (hno (p.colors 0)) (hno (p.colors 1))
  have hlose : p.W.card ≤ W'.card + 40 * h := by omega
  have hloseR : (p.W.card : ℝ) ≤ (W'.card : ℝ) + 40 * h := by exact_mod_cast hlose
  refine ⟨W',hW'W,by nlinarith,?_⟩
  intro u hu v hv huv
  have hc := hclique hu hv huv
  apply (exclusive_permuted_iff c p.colors 2 u v).mp
  apply (exclusive_two_iff (fun i => c (p.colors i)) u v).mpr
  exact ⟨hc.1,fun hr => hc.2 (Or.inl hr),fun hb => hc.2 (Or.inr hb)⟩

end QuantitativeFourBlockCore


end MatchingStability

end PermutedModule16

/- Source module: CliqueExtremalEC2.lean -/
section PermutedModule17

/-!
The clique-core branch of quantitative stability gives the EC2 pattern.
Split the exclusive green clique into two almost equal blocks, retain X and
Y as the red and blue partner blocks, and assign all remaining vertices to
the X block. The density loss is paid by the explicit regime budget.
New proof: @fqlx.
-/

open SimpleGraph Finset
open scoped BigOperators

namespace MatchingStability

theorem finite_ec2_of_weak_clique_core
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) {m h : ℕ} {α μ δ : ℝ}
    (p : RegimeParameters m h α μ δ) (hV : Fintype.card V=4*m)
    (σ : Equiv.Perm (Fin 3)) (X Y W : Finset V)
    (hXY : Disjoint X Y) (hXW : Disjoint X W) (hYW : Disjoint Y W)
    (hX : m-9*h+1 ≤ X.card) (hY : m-9*h+1 ≤ Y.card)
    (hW : (2-α/100)*m-58*h ≤ (W.card : ℝ))
    (hred : ExclusiveBetween c (σ 0) X W)
    (hblue : ExclusiveBetween c (σ 1) Y W)
    (hgreen : ∀ u ∈ W, ∀ v ∈ W, u ≠ v → Exclusive c (σ 2) u v) :
    FiniteEC2 c m α := by
  classical
  obtain ⟨W₀,hW₀,hW₀card⟩ := exists_subset_card_eq (Nat.div_le_self W.card 2)
  let W₁ := W\W₀
  have hW₁ : W₁ ⊆ W := sdiff_subset
  have hsplit : W₀.card+W₁.card=W.card := by
    simpa only [W₁,Nat.add_comm] using card_sdiff_add_card_eq_card hW₀
  have hhalf : W.card ≤ 2*W₀.card+1 := by omega
  have horder : W₀.card ≤ W₁.card := by omega
  have hWunion : W₀∪W₁=W := union_sdiff_of_subset hW₀
  have hWdis : Disjoint W₀ W₁ := disjoint_sdiff_self_right
  let U : Fin 4 → Finset V := ![W₀,W₁,X,Y]
  let τ : Equiv.Perm (Fin 3) :=
    ((Equiv.swap (0 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 1)).trans σ
  have hUdis : ∀ i j, i ≠ j → Disjoint (U i) (U j) := by
    exact four_blocks_disjoint W₀ W₁ X Y hWdis
      (hXW.mono_right hW₀).symm (hYW.mono_right hW₀).symm
      (hXW.mono_right hW₁).symm (hYW.mono_right hW₁).symm hXY
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hh : (1 : ℝ) ≤ h := by exact_mod_cast p.positiveH
  have hαm := mul_le_mul_of_nonneg_right p.alpha_small hm
  have hsmall := p.hAlpha
  have hXreal := p.cast_lower X.card hX
  have hYreal := p.cast_lower Y.card hY
  have hhalfReal : (W.card : ℝ) ≤ 2*(W₀.card : ℝ)+1 := by exact_mod_cast hhalf
  have hbalanced₀ : (1-α)*m ≤ (W₀.card : ℝ) := by nlinarith
  have hhalf₀ : (m : ℝ)/2 ≤ W₀.card := by nlinarith
  have hbalancedX := p.balanced_lower_of_near_m (X.card : ℝ) (by linarith)
  have hbalancedY := p.balanced_lower_of_near_m (Y.card : ℝ) (by linarith)
  have hUlower : ∀ i, (1-α)*m ≤ ((U i).card : ℝ) ∧ (m : ℝ)/2 ≤ (U i).card := by
    intro i
    fin_cases i
    · exact ⟨hbalanced₀,hhalf₀⟩
    · exact ⟨hbalanced₀.trans (Nat.cast_le.mpr horder),
        hhalf₀.trans (Nat.cast_le.mpr horder)⟩
    · exact hbalancedX
    · exact hbalancedY
  have hcount : (FinitePartitionExtension.outside U).card+W.card+X.card+Y.card=4*m := by
    have hu : (univ.biUnion U).card=∑ i, (U i).card :=
      card_biUnion (fun i _ j _ hij => hUdis i j hij)
    have he := card_sdiff_add_card_eq_card (subset_univ (univ.biUnion U))
    rw [card_univ,hV,hu] at he
    change (FinitePartitionExtension.outside U).card+∑ i, (U i).card=4*m at he
    rw [Fin.sum_univ_four] at he
    change (FinitePartitionExtension.outside U).card+
      (W₀.card+W₁.card+X.card+Y.card)=4*m at he
    omega
  have hcountReal : ((FinitePartitionExtension.outside U).card : ℝ)+W.card+X.card+Y.card=4*m := by
    exact_mod_cast hcount
  have houtside : ((FinitePartitionExtension.outside U).card : ℝ) ≤ α/100*m+80*h := by
    nlinarith
  have hgood : ∀ k S T, (k,S,T) ∈ EC2Joins →
      ExclusiveBetween c (τ k) (S.biUnion U) (T.biUnion U) := by
    intro k S T hJ
    simp only [EC2Joins,List.mem_cons,Prod.mk.injEq,List.not_mem_nil,or_false] at hJ
    rcases hJ with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · have hg : ExclusiveBetween c (σ 2) W₀ W₁ := by
        intro u hu v hv
        exact hgreen u (hW₀ hu) v (hW₁ hv) (hWdis.forall_ne_finset hu hv)
      simpa [U,τ,Equiv.swap_apply_def] using hg
    · simpa [U,τ,Equiv.swap_apply_def,hWunion] using hred.symm
    · simpa [U,τ,Equiv.swap_apply_def,hWunion] using hblue.symm
  refine ⟨τ,FinitePartitionExtension.extend U 2,extend_is_partition U 2 hUdis,?_,?_⟩
  · intro i
    exact (hUlower i).1.trans (Nat.cast_le.mpr
      (card_le_card (FinitePartitionExtension.subset_extend U 2 i)))
  · apply extended_exclusive_densities c τ U 2 α ((m : ℝ)/2) EC2Joins
      p.alpha_pos.le (by positivity) (fun i => (hUlower i).2) EC2Joins_nonempty hgood
    have hb := p.ec2_budget ((FinitePartitionExtension.outside U).card : ℝ) houtside
    rw [hV,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith

theorem QuantitativeCliqueCore.toEC2
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : Fin 3 → SimpleGraph V} {m h : ℕ} {α μ δ : ℝ}
    (q : QuantitativeCliqueCore c m h) (a : RegimeParameters m h α μ δ)
    (hV : Fintype.card V=4*m) : FiniteEC2 c m α := by
  apply finite_ec2_of_weak_clique_core c a hV q.colors q.X q.Y q.W
    q.disjointXY q.disjointXW q.disjointYW q.lowerX q.lowerY
    _ q.redXW q.blueYW q.greenW
  have hW := q.lowerW
  have hm := a.largeM
  have hWnat : 2*m+10 ≤ q.W.card+58*h := by omega
  have hWreal : 2*(m : ℝ)+10 ≤ q.W.card+58*h := by exact_mod_cast hWnat
  have hαm := mul_nonneg a.alpha_pos.le (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  nlinarith

end MatchingStability


end PermutedModule17

/- Source module: BipartiteComponentRectangle.lean -/
section PermutedModule18

/-!
The exact two-by-two component pattern in a complete bipartite graph covered
by two colors, when both colors have multiple nontrivial components.  This
pure label lemma isolates the finite classification step from graph APIs.
Credit: @fqlx.
-/

namespace MatchingStability

theorem bipartite_component_rectangle
    {A B R C : Type*} (rA : A → R) (rB : B → R) (bA : A → C) (bB : B → C)
    (hcover : ∀ a b, rA a = rB b ∨ bA a = bB b)
    (a₀ a₁ : A) (b₀ b₁ : B)
    (hblue₀ : bA a₀ = bB b₀) (hblue₁ : bA a₁ = bB b₁)
    (hbne : bA a₀ ≠ bA a₁)
    (hrvary : ∃ a a', rA a ≠ rA a') :
    rA a₀ ≠ rA a₁ ∧
      (∀ a, (rA a = rA a₀ ∧ bA a = bA a₀) ∨
        (rA a = rA a₁ ∧ bA a = bA a₁)) ∧
      (∀ b, (rB b = rA a₁ ∧ bB b = bA a₀) ∨
        (rB b = rA a₀ ∧ bB b = bA a₁)) := by
  classical
  have hr₀₁ : rA a₀ = rB b₁ := (hcover a₀ b₁).resolve_right
    (fun h => hbne (h.trans hblue₁.symm))
  have hr₁₀ : rA a₁ = rB b₀ := (hcover a₁ b₀).resolve_right
    (fun h => hbne (hblue₀.trans h.symm))
  have hleft : ∀ a, if bA a = bA a₀ then rA a = rA a₀ else rA a = rA a₁ := by
    intro a
    split_ifs with h
    · exact ((hcover a b₁).resolve_right
        (fun h' => hbne (h.symm.trans (h'.trans hblue₁.symm)))).trans hr₀₁.symm
    · exact ((hcover a b₀).resolve_right
        (fun h' => h (h'.trans hblue₀.symm))).trans hr₁₀.symm
  have hright : ∀ b, if bB b = bA a₀ then rB b = rA a₁ else rB b = rA a₀ := by
    intro b
    split_ifs with h
    · exact ((hcover a₁ b).resolve_right
        (fun h' => hbne (h.symm.trans h'.symm))).symm
    · exact ((hcover a₀ b).resolve_right (fun h' => h h'.symm)).symm
  have hrne : rA a₀ ≠ rA a₁ := by
    intro heq
    obtain ⟨a, a', hne⟩ := hrvary
    have ha : rA a = rA a₀ := by
      simpa [heq] using hleft a
    have ha' : rA a' = rA a₀ := by
      simpa [heq] using hleft a'
    exact hne (ha.trans ha'.symm)
  refine ⟨hrne, ?_, ?_⟩
  · intro a
    by_cases h : bA a = bA a₀
    · exact Or.inl ⟨by simpa [h] using hleft a, h⟩
    · have hr : rA a = rA a₁ := by simpa [h] using hleft a
      have hb : bA a = bB b₁ := (hcover a b₁).resolve_left
        (fun h' => hrne (hr₀₁.trans (h'.symm.trans hr)))
      exact Or.inr ⟨hr, hb.trans hblue₁.symm⟩
  · intro b
    by_cases h : bB b = bA a₀
    · exact Or.inl ⟨by simpa [h] using hright b, h⟩
    · have hr : rB b = rA a₀ := by simpa [h] using hright b
      have hb : bA a₁ = bB b := (hcover a₁ b).resolve_left
        (fun h' => hrne (hr.symm.trans h'.symm))
      exact Or.inr ⟨hr, hb.symm⟩


end MatchingStability

end PermutedModule18

/- Source module: BipartiteExactClassification.lean -/
section PermutedModule19

/-!
The finite two-color bipartite classification underlying Letzter's Lemma 5.2.
This file keeps the graph-theoretic matching assertions explicit. Credit: @fqlx.
-/

open SimpleGraph

namespace MatchingStability

theorem bipartite_strip_of_ordinary_matching_bound
    {V : Type*} [Fintype V] [DecidableEq V] (R B : SimpleGraph V) (A D : Finset V) (m : ℕ)
    (hd : Disjoint A D) (hA : A.card = 2 * m) (hD : D.card = 2 * m + 1)
    (hcover : ∀ a ∈ A, ∀ d ∈ D, R.Adj a d ∨ B.Adj a d)
    (hR : ∀ M : R.Subgraph, M.IsMatching → M.verts.ncard < 2 * (m + 1))
    (hB : ¬ HasCM B (m + 1)) :
    ∃ X Y : Finset V, Disjoint X Y ∧ X ∪ Y = A ∧
      X.card = m ∧ Y.card = m ∧
      (∀ x ∈ X, ∀ d ∈ D, R.Adj x d ∧ ¬ B.Adj x d) ∧
      (∀ y ∈ Y, ∀ d ∈ D, B.Adj y d ∧ ¬ R.Adj y d) := by
  classical
  obtain ⟨X, hXA, E, hED, hXE, hRedCover⟩ := bipartite_vertex_cover R A D hd (m + 1) hR
  have hXle : X.card ≤ m := by omega
  have hEle : E.card ≤ m := by omega
  have hDminus : m + 1 ≤ (D \ E).card := by
    rw [Finset.card_sdiff_of_subset hED]
    omega
  have hBlueMinus : ∀ a ∈ A \ X, ∀ d ∈ D \ E, B.Adj a d := by
    intro a ha d hd'
    have ha' := Finset.mem_sdiff.mp ha
    have hd'' := Finset.mem_sdiff.mp hd'
    apply (hcover a ha'.1 d hd''.1).resolve_left
    intro h
    rcases hRedCover a ha'.1 d hd''.1 h with hx | he
    · exact ha'.2 hx
    · exact hd''.2 he
  have hAminus : (A \ X).card ≤ m := by
    by_contra! hbig
    exact hB (HasCM.of_complete_join B (A \ X) (D \ E) (m + 1)
      (hd.mono Finset.sdiff_subset Finset.sdiff_subset) (by omega) hDminus hBlueMinus)
  have hcardX : X.card = m := by
    have hh := Finset.card_sdiff_of_subset hXA
    have hx := Finset.card_le_card hXA
    omega
  have hEempty : E = ∅ := Finset.card_eq_zero.mp (by omega)
  let Y := A \ X
  have hYcard : Y.card = m := by
    dsimp [Y]
    rw [Finset.card_sdiff_of_subset hXA]
    omega
  have hBlue : ∀ y ∈ Y, ∀ d ∈ D, B.Adj y d ∧ ¬ R.Adj y d := by
    intro y hy d hd'
    have hy' := Finset.mem_sdiff.mp hy
    have hnot : ¬ R.Adj y d := by
      intro h
      rcases hRedCover y hy'.1 d hd' h with hx | he
      · exact hy'.2 hx
      · simpa [hEempty] using he
    exact ⟨(hcover y hy'.1 d hd').resolve_left hnot, hnot⟩
  have hRed : ∀ x ∈ X, ∀ d ∈ D, R.Adj x d ∧ ¬ B.Adj x d := by
    intro x hx d hd'
    have hxA := hXA hx
    have hnot : ¬ B.Adj x d := by
      intro h
      apply hB
      exact HasCM.of_complete_join_and_extra_edge B Y D m
        (hd.mono Finset.sdiff_subset Finset.Subset.rfl) hYcard.ge (by omega)
        (fun y hy d hd' => (hBlue y hy d hd').1) x d
        (by simpa [Y, hx] using hx) (fun hxD => Finset.disjoint_left.mp hd hxA hxD) hd' h
    exact ⟨(hcover x hxA d hd').resolve_right hnot, hnot⟩
  refine ⟨X, Y, ?_, ?_, hcardX, hYcard, hRed, hBlue⟩
  · exact disjoint_sdiff_self_right
  · exact Finset.union_sdiff_of_subset hXA

theorem bipartite_components_dichotomy
    {V : Type*} (G : SimpleGraph V) (A D : Finset V) (v₀ : V)
    (hbip : G.IsBipartiteWith (A : Set V) (D : Set V)) :
    (∃ C : G.ConnectedComponent, ∀ u v, G.Adj u v → u ∈ C.supp) ∨
    (∃ a₀ ∈ A, ∃ d₀ ∈ D, ∃ a₁ ∈ A, ∃ d₁ ∈ D,
      G.Adj a₀ d₀ ∧ G.Adj a₁ d₁ ∧
      G.connectedComponentMk a₀ ≠ G.connectedComponentMk a₁) := by
  classical
  by_cases hex : ∃ a ∈ A, ∃ d ∈ D, G.Adj a d
  · obtain ⟨a, ha, d, hd, had⟩ := hex
    by_cases hall : ∀ x ∈ A, ∀ y ∈ D, G.Adj x y →
        G.connectedComponentMk x = G.connectedComponentMk a
    · refine Or.inl ⟨G.connectedComponentMk a, ?_⟩
      intro u v huv
      rcases hbip.mem_of_adj huv with h | h
      · exact hall u h.1 v h.2 huv
      · exact (ConnectedComponent.sound huv.reachable).trans (hall v h.2 u h.1 huv.symm)
    · push_neg at hall
      obtain ⟨a', ha', d', hd', had', hne⟩ := hall
      exact Or.inr ⟨a, ha, d, hd, a', ha', d', hd', had, had', hne.symm⟩
  · refine Or.inl ⟨G.connectedComponentMk v₀, ?_⟩
    intro u v huv
    exfalso
    rcases hbip.mem_of_adj huv with h | h
    · exact hex ⟨u, h.1, v, h.2, huv⟩
    · exact hex ⟨v, h.2, u, h.1, huv.symm⟩

theorem edge_of_component_ne
    {V : Type*} {R B : SimpleGraph V} {u v : V}
    (hcover : R.Adj u v ∨ B.Adj u v)
    (hne : B.connectedComponentMk u ≠ B.connectedComponentMk v) :
    R.Adj u v ∧ ¬ B.Adj u v := by
  have hnot : ¬ B.Adj u v := fun h => hne (ConnectedComponent.sound h.reachable)
  exact ⟨hcover.resolve_right hnot, hnot⟩

theorem bipartite_rectangle_of_component_witnesses
    {V : Type*} [Fintype V] [DecidableEq V] (R B : SimpleGraph V) (A D : Finset V) (m : ℕ)
    (hd : Disjoint A D) (hA : A.card = 2 * m) (hD : D.card = 2 * m + 1)
    (hcover : ∀ a ∈ A, ∀ d ∈ D, R.Adj a d ∨ B.Adj a d)
    (hR : ¬ HasCM R (m + 1)) (hB : ¬ HasCM B (m + 1))
    (a₀ a₁ d₀ d₁ : V) (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A)
    (hd₀ : d₀ ∈ D) (hd₁ : d₁ ∈ D)
    (hb₀ : B.Adj a₀ d₀) (hb₁ : B.Adj a₁ d₁)
    (hbne : B.connectedComponentMk a₀ ≠ B.connectedComponentMk a₁)
    (hrvary : ∃ a ∈ A, ∃ a' ∈ A, R.connectedComponentMk a ≠ R.connectedComponentMk a') :
    ∃ X Y Z W : Finset V, Disjoint X Y ∧ X ∪ Y = A ∧
      Disjoint Z W ∧ Z ∪ W = D ∧ X.card = m ∧ Y.card = m ∧
      (∀ x ∈ X, ∀ z ∈ Z, R.Adj x z ∧ ¬ B.Adj x z) ∧
      (∀ y ∈ Y, ∀ w ∈ W, R.Adj y w ∧ ¬ B.Adj y w) ∧
      (∀ x ∈ X, ∀ w ∈ W, B.Adj x w ∧ ¬ R.Adj x w) ∧
      (∀ y ∈ Y, ∀ z ∈ Z, B.Adj y z ∧ ¬ R.Adj y z) := by
  classical
  have hc : ∀ a : A, ∀ d : D,
      R.connectedComponentMk a = R.connectedComponentMk d ∨
      B.connectedComponentMk a = B.connectedComponentMk d := by
    intro a d
    rcases hcover a a.property d d.property with h | h
    · exact Or.inl (ConnectedComponent.sound h.reachable)
    · exact Or.inr (ConnectedComponent.sound h.reachable)
  obtain ⟨hrne, hLeft, hRight⟩ := bipartite_component_rectangle
    (fun a : A => R.connectedComponentMk a) (fun d : D => R.connectedComponentMk d)
    (fun a : A => B.connectedComponentMk a) (fun d : D => B.connectedComponentMk d)
    hc ⟨a₀, ha₀⟩ ⟨a₁, ha₁⟩ ⟨d₀, hd₀⟩ ⟨d₁, hd₁⟩
    (ConnectedComponent.sound hb₀.reachable) (ConnectedComponent.sound hb₁.reachable) hbne
    (by obtain ⟨a, ha, a', ha', h⟩ := hrvary; exact ⟨⟨a, ha⟩, ⟨a', ha'⟩, h⟩)
  let X := A.filter (fun x => B.connectedComponentMk x = B.connectedComponentMk a₀)
  let Y := A \ X
  let W := D.filter (fun x => B.connectedComponentMk x = B.connectedComponentMk a₀)
  let Z := D \ W
  have hXA : X ⊆ A := Finset.filter_subset _ _
  have hYA : Y ⊆ A := Finset.sdiff_subset
  have hWD : W ⊆ D := Finset.filter_subset _ _
  have hZD : Z ⊆ D := Finset.sdiff_subset
  have hXlabels : ∀ x ∈ X, R.connectedComponentMk x = R.connectedComponentMk a₀ ∧
      B.connectedComponentMk x = B.connectedComponentMk a₀ := by
    intro x hx
    rcases hLeft ⟨x, hXA hx⟩ with h | h
    · exact h
    · exact (hbne ((Finset.mem_filter.mp hx).2.symm.trans h.2)).elim
  have hYlabels : ∀ y ∈ Y, R.connectedComponentMk y = R.connectedComponentMk a₁ ∧
      B.connectedComponentMk y = B.connectedComponentMk a₁ := by
    intro y hy
    rcases hLeft ⟨y, hYA hy⟩ with h | h
    · exact ((Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨hYA hy, h.2⟩)).elim
    · exact h
  have hWlabels : ∀ w ∈ W, R.connectedComponentMk w = R.connectedComponentMk a₁ ∧
      B.connectedComponentMk w = B.connectedComponentMk a₀ := by
    intro w hw
    rcases hRight ⟨w, hWD hw⟩ with h | h
    · exact h
    · exact (hbne ((Finset.mem_filter.mp hw).2.symm.trans h.2)).elim
  have hZlabels : ∀ z ∈ Z, R.connectedComponentMk z = R.connectedComponentMk a₀ ∧
      B.connectedComponentMk z = B.connectedComponentMk a₁ := by
    intro z hz
    rcases hRight ⟨z, hZD hz⟩ with h | h
    · exact ((Finset.mem_sdiff.mp hz).2 (Finset.mem_filter.mpr ⟨hZD hz, h.2⟩)).elim
    · exact h
  have hRXZ : ∀ x ∈ X, ∀ z ∈ Z, R.Adj x z ∧ ¬ B.Adj x z := by
    intro x hx z hz
    apply edge_of_component_ne (hcover x (hXA hx) z (hZD hz))
    rw [(hXlabels x hx).2, (hZlabels z hz).2]
    exact hbne
  have hRYW : ∀ y ∈ Y, ∀ w ∈ W, R.Adj y w ∧ ¬ B.Adj y w := by
    intro y hy w hw
    apply edge_of_component_ne (hcover y (hYA hy) w (hWD hw))
    rw [(hYlabels y hy).2, (hWlabels w hw).2]
    exact hbne.symm
  have hBXW : ∀ x ∈ X, ∀ w ∈ W, B.Adj x w ∧ ¬ R.Adj x w := by
    intro x hx w hw
    apply edge_of_component_ne (hcover x (hXA hx) w (hWD hw)).symm
    rw [(hXlabels x hx).1, (hWlabels w hw).1]
    exact hrne
  have hBYZ : ∀ y ∈ Y, ∀ z ∈ Z, B.Adj y z ∧ ¬ R.Adj y z := by
    intro y hy z hz
    apply edge_of_component_ne (hcover y (hYA hy) z (hZD hz)).symm
    rw [(hYlabels y hy).1, (hZlabels z hz).1]
    exact hrne.symm
  have hXYcard : X.card + Y.card = 2 * m := by
    have hh := Finset.card_sdiff_of_subset hXA
    have hx := Finset.card_le_card hXA
    change X.card + (A \ X).card = 2 * m
    omega
  have hZWcard : Z.card + W.card = 2 * m + 1 := by
    have hh := Finset.card_sdiff_of_subset hWD
    have hw := Finset.card_le_card hWD
    change (D \ W).card + W.card = 2 * m + 1
    omega
  have hcards : X.card = m ∧ Y.card = m := by
    by_cases hw : m + 1 ≤ W.card
    · have hx : X.card ≤ m := by
        by_contra! hbig
        exact hB (HasCM.of_complete_join B X W (m + 1) (hd.mono hXA hWD)
          (by omega) hw (fun x hx w hw => (hBXW x hx w hw).1))
      have hy : Y.card ≤ m := by
        by_contra! hbig
        exact hR (HasCM.of_complete_join R Y W (m + 1) (hd.mono hYA hWD)
          (by omega) hw (fun y hy w hw => (hRYW y hy w hw).1))
      omega
    · have hz : m + 1 ≤ Z.card := by omega
      have hx : X.card ≤ m := by
        by_contra! hbig
        exact hR (HasCM.of_complete_join R X Z (m + 1) (hd.mono hXA hZD)
          (by omega) hz (fun x hx z hz => (hRXZ x hx z hz).1))
      have hy : Y.card ≤ m := by
        by_contra! hbig
        exact hB (HasCM.of_complete_join B Y Z (m + 1) (hd.mono hYA hZD)
          (by omega) hz (fun y hy z hz => (hBYZ y hy z hz).1))
      omega
  exact ⟨X, Y, Z, W, disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hXA,
    disjoint_sdiff_self_left, Finset.sdiff_union_of_subset hWD,
    hcards.1, hcards.2, hRXZ, hRYW, hBXW, hBYZ⟩

theorem bipartite_two_color_exact
    {V : Type*} [Fintype V] [DecidableEq V] (R B : SimpleGraph V) (A D : Finset V) (m : ℕ)
    (hd : Disjoint A D) (hA : A.card = 2 * m) (hD : D.card = 2 * m + 1)
    (hRbip : R.IsBipartiteWith (A : Set V) (D : Set V))
    (hBbip : B.IsBipartiteWith (A : Set V) (D : Set V))
    (hcover : ∀ a ∈ A, ∀ d ∈ D, R.Adj a d ∨ B.Adj a d)
    (hR : ¬ HasCM R (m + 1)) (hB : ¬ HasCM B (m + 1)) :
    ∃ X Y Z W : Finset V, Disjoint X Y ∧ X ∪ Y = A ∧
      Disjoint Z W ∧ Z ∪ W = D ∧ X.card = m ∧ Y.card = m ∧ Z.card ≤ m ∧
      (∀ x ∈ X, ∀ z ∈ Z, R.Adj x z ∧ ¬ B.Adj x z) ∧
      (∀ y ∈ Y, ∀ w ∈ W, R.Adj y w ∧ ¬ B.Adj y w) ∧
      (∀ x ∈ X, ∀ w ∈ W, B.Adj x w ∧ ¬ R.Adj x w) ∧
      (∀ y ∈ Y, ∀ z ∈ Z, B.Adj y z ∧ ¬ R.Adj y z) := by
  classical
  obtain ⟨v₀, _⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
  have hrect : ∃ X Y Z W : Finset V, Disjoint X Y ∧ X ∪ Y = A ∧
      Disjoint Z W ∧ Z ∪ W = D ∧ X.card = m ∧ Y.card = m ∧
      (∀ x ∈ X, ∀ z ∈ Z, R.Adj x z ∧ ¬ B.Adj x z) ∧
      (∀ y ∈ Y, ∀ w ∈ W, R.Adj y w ∧ ¬ B.Adj y w) ∧
      (∀ x ∈ X, ∀ w ∈ W, B.Adj x w ∧ ¬ R.Adj x w) ∧
      (∀ y ∈ Y, ∀ z ∈ Z, B.Adj y z ∧ ¬ R.Adj y z) := by
    rcases bipartite_components_dichotomy R A D v₀ hRbip with hOneR | hTwoR
    · obtain ⟨C, hC⟩ := hOneR
      obtain ⟨X, Y, hXY, hUnion, hXcard, hYcard, hRed, hBlue⟩ :=
        bipartite_strip_of_ordinary_matching_bound R B A D m hd hA hD hcover
          (matching_bound_of_edges_in_one_component (m + 1) hR C hC) hB
      refine ⟨Y, X, ∅, D, hXY.symm, by simpa [Finset.union_comm] using hUnion,
        by simp, by simp, hYcard, hXcard, ?_, hRed, hBlue, ?_⟩ <;> simp
    · rcases bipartite_components_dichotomy B A D v₀ hBbip with hOneB | hTwoB
      · obtain ⟨C, hC⟩ := hOneB
        obtain ⟨X, Y, hXY, hUnion, hXcard, hYcard, hBlue, hRed⟩ :=
          bipartite_strip_of_ordinary_matching_bound B R A D m hd hA hD
            (fun a ha d hd => (hcover a ha d hd).symm)
            (matching_bound_of_edges_in_one_component (m + 1) hB C hC) hR
        refine ⟨X, Y, ∅, D, hXY, hUnion, by simp, by simp,
          hXcard, hYcard, ?_, hRed, hBlue, ?_⟩ <;> simp
      · obtain ⟨r₀, hr₀, _, _, r₁, hr₁, _, _, _, _, hrne⟩ := hTwoR
        obtain ⟨a₀, ha₀, d₀, hd₀, a₁, ha₁, d₁, hd₁, hb₀, hb₁, hbne⟩ := hTwoB
        exact bipartite_rectangle_of_component_witnesses R B A D m hd hA hD hcover hR hB
          a₀ a₁ d₀ d₁ ha₀ ha₁ hd₀ hd₁ hb₀ hb₁ hbne ⟨r₀, hr₀, r₁, hr₁, hrne⟩
  obtain ⟨X, Y, Z, W, hXY, hXYunion, hZW, hZWunion, hXcard, hYcard,
    hRXZ, hRYW, hBXW, hBYZ⟩ := hrect
  by_cases hZ : Z.card ≤ m
  · exact ⟨X, Y, Z, W, hXY, hXYunion, hZW, hZWunion, hXcard, hYcard,
      hZ, hRXZ, hRYW, hBXW, hBYZ⟩
  · have hW : W.card ≤ m := by
      have hh := Finset.card_union_of_disjoint hZW
      rw [hZWunion, hD] at hh
      omega
    exact ⟨Y, X, W, Z, hXY.symm, by simpa [Finset.union_comm] using hXYunion,
      hZW.symm, by simpa [Finset.union_comm] using hZWunion, hYcard, hXcard,
      hW, hRYW, hRXZ, hBYZ, hBXW⟩


end MatchingStability

end PermutedModule19

/- Source module: ConnectedMatchingCore.lean -/
section PermutedModule20

/-!
The four-block conclusion used in the finite connected-matching induction.
Its vertices need not exhaust the ambient type, so it can be transported
from an induced subgraph and then augmented by an outside vertex.
Credit: @fqlx.
-/

open SimpleGraph

namespace MatchingStability

structure FourBlockCore {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (m : ℕ) where
  colors : Equiv.Perm (Fin 3)
  X : Finset V
  Y : Finset V
  Z : Finset V
  W : Finset V
  disjointXY : Disjoint X Y
  disjointZW : Disjoint Z W
  disjointSides : Disjoint (X ∪ Y) (Z ∪ W)
  cardX : X.card = m
  cardY : Y.card = m
  cardZ : Z.card ≤ m
  cardZW : Z.card + W.card = 2 * m + 1
  redXZ : ∀ x ∈ X, ∀ z ∈ Z, (c (colors 0)).Adj x z
  redYW : ∀ y ∈ Y, ∀ w ∈ W, (c (colors 0)).Adj y w
  blueXW : ∀ x ∈ X, ∀ w ∈ W, (c (colors 1)).Adj x w
  blueYZ : ∀ y ∈ Y, ∀ z ∈ Z, (c (colors 1)).Adj y z
  greenZW : ∀ z ∈ Z, ∀ w ∈ W, (c (colors 2)).Adj z w
  greenXY : Z.Nonempty → ∀ x ∈ X, ∀ y ∈ Y, (c (colors 2)).Adj x y
  greenW : m + 2 ≤ W.card → (c (colors 2)).IsClique (W : Set V)

theorem FourBlockCore.card_union
    {V : Type*} [DecidableEq V] {c : Fin 3 → SimpleGraph V} {m : ℕ}
    (p : FourBlockCore c m) : ((p.X ∪ p.Y) ∪ (p.Z ∪ p.W)).card = 4 * m + 1 := by
  rw [Finset.card_union_of_disjoint p.disjointSides,
    Finset.card_union_of_disjoint p.disjointXY, Finset.card_union_of_disjoint p.disjointZW,
    p.cardX, p.cardY, p.cardZW]
  omega

theorem FourBlockCore.exists_outside
    {V : Type*} [Fintype V] [DecidableEq V] {c : Fin 3 → SimpleGraph V} {m : ℕ}
    (p : FourBlockCore c m) (hsize : 4 * m + 1 < Fintype.card V) :
    ∃ v : V, v ∉ (p.X ∪ p.Y) ∪ (p.Z ∪ p.W) := by
  by_contra! h
  have heq : (p.X ∪ p.Y) ∪ (p.Z ∪ p.W) = Finset.univ := Finset.eq_univ_iff_forall.mpr h
  have hh := p.card_union
  rw [heq, Finset.card_univ] at hh
  omega

def FourBlockCore.map
    {V U : Type*} [DecidableEq V] [DecidableEq U]
    {c : Fin 3 → SimpleGraph V} {d : Fin 3 → SimpleGraph U} {m : ℕ}
    (p : FourBlockCore c m) (f : V ↪ U)
    (hmap : ∀ k u v, (c k).Adj u v → (d k).Adj (f u) (f v)) : FourBlockCore d m where
  colors := p.colors
  X := p.X.map f
  Y := p.Y.map f
  Z := p.Z.map f
  W := p.W.map f
  disjointXY := (Finset.disjoint_map f).mpr p.disjointXY
  disjointZW := (Finset.disjoint_map f).mpr p.disjointZW
  disjointSides := by
    rw [← Finset.map_union, ← Finset.map_union]
    exact (Finset.disjoint_map f).mpr p.disjointSides
  cardX := by simpa using p.cardX
  cardY := by simpa using p.cardY
  cardZ := by simpa using p.cardZ
  cardZW := by simpa using p.cardZW
  redXZ := by
    intro x hx z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hz
    exact hmap _ _ _ (p.redXZ a ha b hb)
  redYW := by
    intro y hy w hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hw
    exact hmap _ _ _ (p.redYW a ha b hb)
  blueXW := by
    intro x hx w hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hw
    exact hmap _ _ _ (p.blueXW a ha b hb)
  blueYZ := by
    intro y hy z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hz
    exact hmap _ _ _ (p.blueYZ a ha b hb)
  greenZW := by
    intro z hz w hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hw
    exact hmap _ _ _ (p.greenZW a ha b hb)
  greenXY := by
    intro hZ x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hmap _ _ _ (p.greenXY (Finset.map_nonempty.mp hZ) a ha b hb)
  greenW := by
    intro hW x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hmap _ _ _ (p.greenW (by simpa using hW) ha hb (fun h => hxy (congrArg f h)))

def FourBlockCore.zero
    {V : Type*} [DecidableEq V] (c : Fin 3 → SimpleGraph V) (v : V) : FourBlockCore c 0 where
  colors := Equiv.refl _
  X := ∅
  Y := ∅
  Z := ∅
  W := {v}
  disjointXY := by simp
  disjointZW := by simp
  disjointSides := by simp
  cardX := by simp
  cardY := by simp
  cardZ := by simp
  cardZW := by simp
  redXZ := by simp
  redYW := by simp
  blueXW := by simp
  blueYZ := by simp
  greenZW := by simp
  greenXY := by simp
  greenW := by simp


end MatchingStability

end PermutedModule20

/- Source module: SaturatedStar.lean -/
section PermutedModule21

/-!
The star structure of a maximal graph without a perfect matching, derived
directly from Mathlib's proved Tutte theorem.  This is the saturation step used
after adjoining universal vertices in connected-matching stability arguments.
Credit: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

theorem odd_components_ncard_eq_of_reachable_eq
    {V : Type*} {G H : SimpleGraph V} (h : G.Reachable = H.Reachable) :
    G.oddComponents.ncard = H.oddComponents.ncard := by
  change
    ({c : Quot G.Reachable | Odd ({v : V | Quot.mk G.Reachable v = c} : Set V).ncard} :
      Set (Quot G.Reachable)).ncard =
    ({c : Quot H.Reachable | Odd ({v : V | Quot.mk H.Reachable v = c} : Set V).ncard} :
      Set (Quot H.Reachable)).ncard
  rw [h]

theorem reachable_eq_of_adj_reachable
    {V : Type*} {G H : SimpleGraph V} (hle : G ≤ H)
    (hadj : ∀ x y, H.Adj x y → G.Reachable x y) :
    G.Reachable = H.Reachable := by
  ext x y
  constructor
  · exact fun h => h.mono hle
  · rintro ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.rfl
    | @cons u v w huv p ih => exact (hadj u v huv).trans ih

theorem tutte_violator_deleted_not_preconnected
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : Even (Fintype.card V)) (S : Set V) (hS : G.IsTutteViolator S) :
    ¬((⊤ : G.Subgraph).deleteVerts S).coe.Preconnected := by
  classical
  intro hK
  let K := ((⊤ : G.Subgraph).deleteVerts S).coe
  have hle := odd_components_le_one_of_preconnected K hK
  have hlt : S.ncard < K.oddComponents.ncard := hS
  have hs0 : S.ncard = 0 := by omega
  have hsEmpty : S = ∅ := (Set.ncard_eq_zero (s := S) (Set.toFinite S)).mp hs0
  have hcardK : Nat.card ((⊤ : G.Subgraph).deleteVerts S).verts = Fintype.card V := by
    rw [hsEmpty, Subgraph.deleteVerts_empty]
    simp [Nat.card_eq_fintype_card]
  have hodd : Odd K.oddComponents.ncard := by
    have hc : K.oddComponents.ncard = 1 := by omega
    simp [hc]
  have := (odd_ncard_oddComponents K).mp hodd
  exact (Nat.not_odd_iff_even.mpr heven) (hcardK ▸ this)

theorem universal_vertices_subset_tutte_violator
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : Even (Fintype.card V)) (S : Set V) (hS : G.IsTutteViolator S) :
    G.universalVerts ⊆ S := by
  intro v hv
  by_contra hvS
  let K := ((⊤ : G.Subgraph).deleteVerts S).coe
  let u : ((⊤ : G.Subgraph).deleteVerts S).verts := ⟨v, by exact ⟨by trivial, hvS⟩⟩
  have hu : K.IsUniversal u := by
    intro w huw
    exact Subgraph.deleteVerts_adj.mpr ⟨by trivial, hvS, by trivial, w.property.2,
      hv (fun h => huw (Subtype.ext h))⟩
  apply tutte_violator_deleted_not_preconnected G heven S hS
  intro x y
  exact (SimpleGraph.Reachable.of_isUniversal x hu).symm.trans
    (SimpleGraph.Reachable.of_isUniversal y hu)

theorem maximal_perfect_matching_free_star
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hfree : G.IsMatchingFree)
    (hmax : ∀ H : SimpleGraph V, G < H → ∃ M : H.Subgraph, M.IsPerfectMatching) :
    ∃ S : Set V, G.IsTutteViolator S ∧ S ⊆ G.universalVerts ∧
      ∀ C : ((⊤ : G.Subgraph).deleteVerts S).coe.ConnectedComponent,
        ((⊤ : G.Subgraph).deleteVerts S).coe.IsClique C.supp := by
  classical
  obtain ⟨S, hS⟩ : ∃ S, G.IsTutteViolator S := by
    by_contra! hn
    obtain ⟨M, hM⟩ := (SimpleGraph.tutte (G := G)).mpr hn
    exact hfree M hM
  let K := ((⊤ : G.Subgraph).deleteVerts S).coe
  let J : SimpleGraph V := {
    Adj := fun x y => x ≠ y ∧ (x ∈ S ∨ y ∈ S ∨
      ∃ hx : x ∉ S, ∃ hy : y ∉ S,
        K.Reachable ⟨x, ⟨by trivial, hx⟩⟩ ⟨y, ⟨by trivial, hy⟩⟩)
    symm.symm := by
      intro x y h
      refine ⟨h.1.symm, ?_⟩
      rcases h.2 with hx | hy | ⟨hx, hy, hr⟩
      · exact Or.inr (Or.inl hx)
      · exact Or.inl hy
      · exact Or.inr (Or.inr ⟨hy, hx, hr.symm⟩)
    loopless.irrefl := fun _ h => h.1 rfl }
  have hle : G ≤ J := by
    intro x y hxy
    refine ⟨hxy.ne, ?_⟩
    by_cases hx : x ∈ S
    · exact Or.inl hx
    by_cases hy : y ∈ S
    · exact Or.inr (Or.inl hy)
    exact Or.inr (Or.inr ⟨hx, hy,
      (show K.Adj ⟨x, ⟨by trivial, hx⟩⟩ ⟨y, ⟨by trivial, hy⟩⟩ from
        Subgraph.deleteVerts_adj.mpr ⟨by trivial, hx, by trivial, hy, hxy⟩).reachable⟩)
  have hreach : K.Reachable = ((⊤ : J.Subgraph).deleteVerts S).coe.Reachable := by
    apply reachable_eq_of_adj_reachable (G := K)
      (H := ((⊤ : J.Subgraph).deleteVerts S).coe)
      (Subgraph.deleteVerts_mono' (G := G) (G' := J) S hle)
    intro x y hxy
    have hJ : J.Adj x y := Subgraph.coe_adj_sub _ _ _ hxy
    rcases hJ.2 with hx | hy | ⟨hx, hy, hr⟩
    · exact (x.property.2 hx).elim
    · exact (y.property.2 hy).elim
    · exact hr
  have hJS : J.IsTutteViolator S := by
    have hc := odd_components_ncard_eq_of_reachable_eq hreach
    change S.ncard < K.oddComponents.ncard at hS
    change S.ncard < ((⊤ : J.Subgraph).deleteVerts S).coe.oddComponents.ncard
    exact hS.trans_eq hc
  have hge : J ≤ G := by
    by_contra hn
    obtain ⟨M, hM⟩ := hmax J (lt_of_le_not_ge hle hn)
    exact SimpleGraph.not_isTutteViolator_of_isPerfectMatching hM S hJS
  refine ⟨S, hS, ?_, ?_⟩
  · intro x hx y hxy
    exact hge ⟨hxy, Or.inl hx⟩
  · intro C x hx y hy hxy
    exact Subgraph.deleteVerts_adj.mpr ⟨by trivial, x.property.2, by trivial,
      y.property.2, hge ⟨fun h => hxy (Subtype.ext h),
        Or.inr (Or.inr ⟨x.property.2, y.property.2, C.reachable_of_mem_supp hx hy⟩)⟩⟩


end MatchingStability

end PermutedModule21

/- Source module: UniversalMatchingStar.lean -/
section PermutedModule22

/-!
Universal-vertex extensions convert the absence of a fixed-size ordinary
matching into the absence of a perfect matching.  Pulling back the saturated
perfect-matching-free star structure then gives the corresponding ordinary
matching theorem.  All finite graph facts used here are proved in Mathlib or
the imported scratch modules.  Credit: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

theorem universal_extension_adj_original
    {V W : Type*} (G : SimpleGraph V) (x y : V) :
    ((Gᶜ ⊕g (⊥ : SimpleGraph W))ᶜ).Adj (Sum.inl x) (Sum.inl y) ↔ G.Adj x y := by
  by_cases hxy : G.Adj x y
  · simp [hxy, hxy.ne]
  · simp [hxy]

theorem universal_extension_perfect_matching_iff
    {V : Type*} [Fintype V] (G : SimpleGraph V) (k q : ℕ)
    (hcard : Fintype.card V = 2 * k + q) :
    (∃ P : ((Gᶜ ⊕g (⊥ : SimpleGraph (Fin q)))ᶜ).Subgraph, P.IsPerfectMatching) ↔
    ∃ M : G.Subgraph, M.IsMatching ∧ 2 * k ≤ M.verts.ncard := by
  classical
  let H := (Gᶜ ⊕g (⊥ : SimpleGraph (Fin q)))ᶜ
  let f : G ↪g H := {
    toFun := Sum.inl
    inj' := Sum.inl_injective
    map_rel_iff' := universal_extension_adj_original G _ _ }
  constructor
  · rintro ⟨P, hP⟩
    obtain ⟨M, hM, hcompl⟩ := matching_restriction_of_perfect_matching f P hP
    change M.vertsᶜ.ncard ≤ (Set.range (Sum.inl : V → V ⊕ Fin q))ᶜ.ncard at hcompl
    have hc : M.vertsᶜ.ncard ≤ q := by
      simpa only [Set.compl_range_inl, Set.ncard_range_of_injective Sum.inr_injective,
        Nat.card_eq_fintype_card, Fintype.card_fin] using hcompl
    have hsum := Set.ncard_add_ncard_compl M.verts
    simp only [Nat.card_eq_fintype_card] at hsum
    exact ⟨M, hM, by omega⟩
  · rintro ⟨M, hM, hbig⟩
    obtain ⟨M₀, _, hM₀, hM₀card⟩ := exists_submatching_card M hM k hbig
    let N := M₀.map f.toHom
    have hN : N.IsMatching := hM₀.map f.toHom f.injective
    have hNv : N.verts = Sum.inl '' M₀.verts := rfl
    let U : Set (V ⊕ Fin q) := Sum.inl '' M₀.vertsᶜ
    let W : Set (V ⊕ Fin q) := Set.range Sum.inr
    have hd : Disjoint U W := by
      rw [Set.disjoint_left]
      rintro x ⟨u, _, rfl⟩ ⟨w, hw⟩
      cases hw
    have hcover : U ∪ W = N.vertsᶜ := by
      rw [hNv]
      ext x
      cases x <;> simp [U, W]
    have hUcard : U.ncard = q := by
      rw [Set.ncard_image_of_injective _ Sum.inl_injective]
      have hsum := Set.ncard_add_ncard_compl M₀.verts
      simp only [Nat.card_eq_fintype_card] at hsum
      omega
    have hWcard : W.ncard = q := by
      rw [Set.ncard_range_of_injective Sum.inr_injective]
      simp
    apply perfect_matching_of_complete_unmatched_join H N hN U W hd hcover
      (hUcard.trans hWcard.symm)
    rintro x ⟨u, _, rfl⟩ y ⟨w, rfl⟩
    simp [H]

theorem star_structure_comap_embedding
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (S : Set W) (hS : S ⊆ H.universalVerts)
    (hclique : ∀ C : ((⊤ : H.Subgraph).deleteVerts S).coe.ConnectedComponent,
      ((⊤ : H.Subgraph).deleteVerts S).coe.IsClique C.supp) :
    f ⁻¹' S ⊆ G.universalVerts ∧
      ∀ C : ((⊤ : G.Subgraph).deleteVerts (f ⁻¹' S)).coe.ConnectedComponent,
        ((⊤ : G.Subgraph).deleteVerts (f ⁻¹' S)).coe.IsClique C.supp := by
  let A := f ⁻¹' S
  let K := ((⊤ : G.Subgraph).deleteVerts A).coe
  let L := ((⊤ : H.Subgraph).deleteVerts S).coe
  let e : K ↪g L := {
    toFun := fun x => ⟨f x, by exact ⟨by trivial, x.property.2⟩⟩
    inj' := by
      intro x y h
      exact Subtype.ext (f.injective (congrArg Subtype.val h))
    map_rel_iff' := by
      intro x y
      constructor
      · intro h
        exact Subgraph.deleteVerts_adj.mpr ⟨by trivial, x.property.2, by trivial,
          y.property.2, f.map_adj_iff.mp (Subgraph.coe_adj_sub _ _ _ h)⟩
      · intro h
        exact Subgraph.deleteVerts_adj.mpr ⟨by trivial, x.property.2, by trivial,
          y.property.2, f.map_adj_iff.mpr (Subgraph.coe_adj_sub _ _ _ h)⟩ }
  constructor
  · intro x hx y hxy
    exact f.map_adj_iff.mp (hS hx (f.injective.ne hxy))
  · intro C x hx y hy hxy
    have hr := (C.reachable_of_mem_supp hx hy).map e.toHom
    let D := L.connectedComponentMk (e x)
    have hxD : e x ∈ D.supp := rfl
    have hyD : e y ∈ D.supp := ConnectedComponent.sound hr.symm
    exact e.map_adj_iff.mp (hclique D hxD hyD (e.injective.ne hxy))

theorem maximal_matching_free_star
    {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hsize : 2 * k ≤ Fintype.card V)
    (hfree : ∀ M : G.Subgraph, M.IsMatching → M.verts.ncard < 2 * k)
    (hmax : ∀ F : SimpleGraph V, G < F →
      ∃ M : F.Subgraph, M.IsMatching ∧ 2 * k ≤ M.verts.ncard) :
    ∃ A : Set V, A ⊆ G.universalVerts ∧
      ∀ C : ((⊤ : G.Subgraph).deleteVerts A).coe.ConnectedComponent,
        ((⊤ : G.Subgraph).deleteVerts A).coe.IsClique C.supp := by
  classical
  let q := Fintype.card V - 2 * k
  have hcard : Fintype.card V = 2 * k + q := by omega
  let H := (Gᶜ ⊕g (⊥ : SimpleGraph (Fin q)))ᶜ
  have hHfree : H.IsMatchingFree := by
    intro P hP
    obtain ⟨M, hM, hbig⟩ := (universal_extension_perfect_matching_iff G k q hcard).mp ⟨P, hP⟩
    exact (hfree M hM).not_ge hbig
  obtain ⟨J, hHJ, hJfree, hJmax⟩ := SimpleGraph.exists_maximal_isMatchingFree hHfree
  let F := J.comap (Sum.inl : V → V ⊕ Fin q)
  have hGF : G ≤ F := by
    intro x y hxy
    exact hHJ ((universal_extension_adj_original G x y).mpr hxy)
  have hFJ : ((Fᶜ ⊕g (⊥ : SimpleGraph (Fin q)))ᶜ) ≤ J := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact (universal_extension_adj_original F x y).mp hxy
      | inr y => exact hHJ (by simp [H])
    | inr x =>
      cases y with
      | inl y => exact hHJ (by simp [H])
      | inr y => exact hHJ (by simpa [H] using hxy.ne)
  have hFfree : ∀ M : F.Subgraph, M.IsMatching → M.verts.ncard < 2 * k := by
    intro M hM
    by_contra! hbig
    obtain ⟨P, hP⟩ := (universal_extension_perfect_matching_iff F k q hcard).mpr ⟨M, hM, hbig⟩
    exact hJfree.mono hFJ P hP
  have hFG : F ≤ G := by
    by_contra hn
    obtain ⟨M, hM, hbig⟩ := hmax F (lt_of_le_not_ge hGF hn)
    exact (hFfree M hM).not_ge hbig
  let f : G ↪g J := {
    toFun := Sum.inl
    inj' := Sum.inl_injective
    map_rel_iff' := by
      intro x y
      exact ⟨fun h => hFG h, fun h => hGF h⟩ }
  obtain ⟨S, _, hS, hclique⟩ := maximal_perfect_matching_free_star J hJfree hJmax
  exact ⟨f ⁻¹' S, star_structure_comap_embedding f S hS hclique⟩


end MatchingStability

end PermutedModule22

/- Source module: ConnectedMatchingDeletion.lean -/
section PermutedModule23

/-!
Deleting one essential vertex from the unique component containing a large
connected matching. This is the induction step's matching-theoretic input.
Credit: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

theorem matching_card_even
    {V : Type*} [Fintype V] {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching) :
    Even M.verts.ncard := by
  classical
  simpa only [← Set.ncard_eq_toFinset_card'] using hM.even_card

theorem matching_card_le_of_lt_two_succ
    {V : Type*} [Fintype V] {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching)
    (m : ℕ) (hcard : M.verts.ncard < 2 * (m + 1)) : M.verts.ncard ≤ 2 * m := by
  obtain ⟨k, hk⟩ := matching_card_even M hM
  omega

theorem exists_essential_vertex_of_no_larger_CM
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (m : ℕ) (hsize : 2 * m + 2 ≤ Fintype.card V) (hno : ¬ HasCM G (m + 1)) :
    ∃ v : V, ∀ M : G.Subgraph, M.IsMatching →
      2 * m ≤ M.verts.ncard → v ∈ M.verts := by
  apply exists_essential_vertex G hG m hsize
  intro M hM
  exact matching_card_le_of_lt_two_succ M hM m
    ((not_hasCM_iff_of_preconnected (m + 1) hG.preconnected).mp hno M hM)

theorem matching_induce_with_verts
    {V : Type*} (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (S : Set V) (hMS : M.verts ⊆ S) :
    ∃ N : (G.induce S).Subgraph, N.IsMatching ∧
      N.verts = Subtype.val ⁻¹' M.verts ∧ N.verts.ncard = M.verts.ncard := by
  let N : (G.induce S).Subgraph := {
    verts := Subtype.val ⁻¹' M.verts
    Adj := fun u v => M.Adj u.val v.val
    adj_sub := fun h => M.adj_sub h
    edge_vert := fun h => M.edge_vert h
    symm.symm := fun _ _ h => h.symm }
  refine ⟨N, ?_, rfl, ?_⟩
  · intro v hv
    obtain ⟨w, hvw, huniq⟩ := hM hv
    refine ⟨⟨w, hMS hvw.snd_mem⟩, hvw, ?_⟩
    intro z hz
    exact Subtype.ext (huniq z hz)
  · apply Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
    intro v hv
    exact ⟨⟨v, hMS hv⟩, rfl⟩

theorem HasCM.exists_component
    {V : Type*} {G : SimpleGraph V} {s : ℕ} (hs : 1 ≤ s) (h : HasCM G s) :
    ∃ C : G.ConnectedComponent, HasCM C.toSimpleGraph s := by
  obtain ⟨M, hM, hsize, hcon⟩ := h
  obtain ⟨v, hv⟩ := Set.nonempty_of_ncard_ne_zero (by omega : M.verts.ncard ≠ 0)
  let C := G.connectedComponentMk v
  have hMC : M.verts ⊆ C.supp := by
    intro u hu
    exact ConnectedComponent.sound (hcon u hu v hv)
  obtain ⟨N, hN, _, hcard⟩ := matching_induce_with_verts G M hM C.supp hMC
  refine ⟨C, HasCM.of_preconnected C.connected_toSimpleGraph.preconnected N hN ?_⟩
  simpa only [hcard] using hsize

theorem component_unique_of_large_CM_components
    {V : Type*} [Fintype V] (G : SimpleGraph V) (m : ℕ)
    (hsize : Fintype.card V ≤ 4 * m + 3)
    (hlarge : ∀ C : G.ConnectedComponent, HasCM C.toSimpleGraph m →
      2 * m + 2 ≤ C.supp.ncard)
    (C D : G.ConnectedComponent) (hC : HasCM C.toSimpleGraph m)
    (hD : HasCM D.toSimpleGraph m) : C = D := by
  by_contra hne
  have hd : Disjoint C.supp D.supp := pairwise_disjoint_supp_connectedComponent G hne
  have hc := hlarge C hC
  have hd' := hlarge D hD
  have hsum := Set.ncard_union_eq hd
  have hbound := Set.ncard_le_card (C.supp ∪ D.supp)
  simp only [Nat.card_eq_fintype_card] at hbound
  omega

theorem exists_vertex_killing_CM
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v₀ : V) (m : ℕ) (hm : 1 ≤ m)
    (hsize : Fintype.card V ≤ 4 * m + 3) (hno : ¬ HasCM G (m + 1))
    (hlarge : ∀ C : G.ConnectedComponent, HasCM C.toSimpleGraph m →
      2 * m + 2 ≤ C.supp.ncard) :
    ∃ v : V, ¬ HasCM (G.induce ({v}ᶜ : Set V)) m := by
  classical
  by_cases hCM : HasCM G m
  swap
  · refine ⟨v₀, fun h => hCM (h.map (Embedding.induce _).toHom Subtype.val_injective)⟩
  obtain ⟨C, hC⟩ := hCM.exists_component hm
  have hCsize : 2 * m + 2 ≤ Fintype.card C := by
    rw [← Nat.card_eq_fintype_card]
    change 2 * m + 2 ≤ Nat.card C.supp
    simpa only [Nat.card_coe_set_eq] using hlarge C hC
  have hCno : ¬ HasCM C.toSimpleGraph (m + 1) := fun h =>
    hno (h.map C.toSimpleGraph_hom Subtype.val_injective)
  obtain ⟨v, hv⟩ := exists_essential_vertex_of_no_larger_CM C.toSimpleGraph
    C.connected_toSimpleGraph m hCsize hCno
  refine ⟨v, ?_⟩
  rintro ⟨M, hM, hMsize, hMcon⟩
  let f : (G.induce ({(v : V)}ᶜ : Set V)) →g G := (Embedding.induce _).toHom
  let N := M.map f
  have hN : N.IsMatching := hM.map f Subtype.val_injective
  have hNv : N.verts = Subtype.val '' M.verts := rfl
  have hNsize : 2 * m ≤ N.verts.ncard := by
    rw [hNv, Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hMsize
  have hNcon : ∀ u ∈ N.verts, ∀ w ∈ N.verts, G.Reachable u w := by
    simp only [hNv, Set.mem_image]
    rintro u ⟨u', hu', rfl⟩ w ⟨w', hw', rfl⟩
    exact (hMcon u' hu' w' hw').map f
  have hvNot : (v : V) ∉ N.verts := by
    rw [hNv]
    rintro ⟨w, _, hw⟩
    exact w.property hw
  obtain ⟨u, hu⟩ := Set.nonempty_of_ncard_ne_zero (by omega : N.verts.ncard ≠ 0)
  let D := G.connectedComponentMk u
  have hND : N.verts ⊆ D.supp := by
    intro w hw
    exact ConnectedComponent.sound (hNcon w hw u hu)
  obtain ⟨N_D, hN_D, _, hN_Dcard⟩ := matching_induce_with_verts G N hN D.supp hND
  have hD : HasCM D.toSimpleGraph m :=
    HasCM.of_preconnected D.connected_toSimpleGraph.preconnected N_D hN_D
      (by simpa only [hN_Dcard] using hNsize)
  have hDC : D = C := component_unique_of_large_CM_components G m hsize hlarge D C hD hC
  have hNC : N.verts ⊆ C.supp := hDC ▸ hND
  obtain ⟨N_C, hN_C, hN_Cverts, hN_Ccard⟩ := matching_induce_with_verts G N hN C.supp hNC
  have hvC := hv N_C hN_C (by simpa only [hN_Ccard] using hNsize)
  rw [hN_Cverts] at hvC
  exact hvNot hvC


end MatchingStability

end PermutedModule23

/- Source module: ConnectedMatchingBalancedCut.lean -/
section PermutedModule24

/-!
Balanced cuts missing one color, and the four-block conclusion obtained from
the exact two-color bipartite classification. Credit: @fqlx.
-/

open SimpleGraph

namespace MatchingStability

def BalancedMissingCut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ A D : Finset V, Disjoint A D ∧ A ∪ D = Finset.univ ∧
    A.card = 2 * m ∧ D.card = 2 * m + 1 ∧
    ∀ a ∈ A, ∀ d ∈ D, ¬ G.Adj a d

theorem component_large_of_no_balanced_cut
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (m : ℕ)
    (hsize : Fintype.card V = 4 * m + 1) (hnoCut : ¬ BalancedMissingCut G m)
    (C : G.ConnectedComponent) (hC : HasCM C.toSimpleGraph m) :
    2 * m + 2 ≤ C.supp.ncard := by
  classical
  by_contra! hsmall
  have hlower : 2 * m ≤ C.supp.ncard := by
    obtain ⟨M, _, hMsize, _⟩ := hC
    have hbound := Set.ncard_le_card M.verts
    change M.verts.ncard ≤ Nat.card C.supp at hbound
    simp only [Nat.card_coe_set_eq] at hbound
    omega
  let T := C.supp.toFinset
  have hTcard : T.card = C.supp.ncard := (Set.ncard_eq_toFinset_card' _).symm
  have hNotJoin : ∀ u ∈ T, ∀ v ∈ Finset.univ \ T, ¬ G.Adj u v := by
    intro u hu v hv huv
    have hvC := C.mem_supp_of_adj_mem_supp (by simpa [T] using hu) huv
    exact (Finset.mem_sdiff.mp hv).2 (by simpa [T] using hvC)
  have hCases : T.card = 2 * m ∨ T.card = 2 * m + 1 := by omega
  apply hnoCut
  rcases hCases with hT | hT
  · refine ⟨T, Finset.univ \ T, disjoint_sdiff_self_right,
      Finset.union_sdiff_of_subset (Finset.subset_univ _), hT, ?_, hNotJoin⟩
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hsize, hT]
    omega
  · refine ⟨Finset.univ \ T, T, disjoint_sdiff_self_left,
      Finset.sdiff_union_of_subset (Finset.subset_univ _), ?_, hT, ?_⟩
    · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hsize, hT]
      omega
    · intro u hu v hv huv
      exact hNotJoin v hv u hu huv.symm

theorem three_color_cover_permuted
    {V : Type*} (c : Fin 3 → SimpleGraph V) (σ : Equiv.Perm (Fin 3))
    (hcover : ∀ u v, u ≠ v → ∃ k, (c k).Adj u v) {u v : V} (hne : u ≠ v) :
    (c (σ 0)).Adj u v ∨ (c (σ 1)).Adj u v ∨ (c (σ 2)).Adj u v := by
  obtain ⟨k, hk⟩ := hcover u v hne
  obtain ⟨j, hj⟩ : ∃ j, (c (σ j)).Adj u v := ⟨σ.symm k, by simpa using hk⟩
  fin_cases j
  · exact Or.inl hj
  · exact Or.inr (Or.inl hj)
  · exact Or.inr (Or.inr hj)

theorem four_block_core_of_balanced_cut
    {V : Type*} [Fintype V] [DecidableEq V] (c : Fin 3 → SimpleGraph V) (m : ℕ)
    (hcover : ∀ u v, u ≠ v → ∃ k, (c k).Adj u v)
    (hno : ∀ k, ¬ HasCM (c k) (m + 1))
    (i : Fin 3) (hcut : BalancedMissingCut (c i) m) :
    Nonempty (FourBlockCore c m) := by
  classical
  obtain ⟨A, D, hAD, _, hAcard, hDcard, hMissing⟩ := hcut
  let σ := Equiv.swap i (2 : Fin 3)
  let R := c (σ 0)
  let B := c (σ 1)
  let H := c (σ 2)
  have hGreen : σ 2 = i := by simp [σ]
  have hCoverRB : ∀ a ∈ A, ∀ d ∈ D, R.Adj a d ∨ B.Adj a d := by
    intro a ha d hd
    have hne : a ≠ d := fun h => Finset.disjoint_left.mp hAD ha (h.symm ▸ hd)
    rcases three_color_cover_permuted c σ hcover hne with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hMissing a ha d hd (by simpa only [hGreen] using h)).elim
  let R' := R.between (A : Set V) (D : Set V)
  let B' := B.between (A : Set V) (D : Set V)
  have hADset : Disjoint (A : Set V) (D : Set V) := by
    simpa using hAD
  have hRbip : R'.IsBipartiteWith (A : Set V) (D : Set V) := R.between_isBipartiteWith hADset
  have hBbip : B'.IsBipartiteWith (A : Set V) (D : Set V) := B.between_isBipartiteWith hADset
  have hR'no : ¬ HasCM R' (m + 1) := fun h => hno (σ 0) (h.mono R.between_le)
  have hB'no : ¬ HasCM B' (m + 1) := fun h => hno (σ 1) (h.mono B.between_le)
  have hCross : ∀ a ∈ A, ∀ d ∈ D, R'.Adj a d ∨ B'.Adj a d := by
    intro a ha d hd
    rcases hCoverRB a ha d hd with h | h
    · exact Or.inl ⟨h, Or.inl ⟨ha, hd⟩⟩
    · exact Or.inr ⟨h, Or.inl ⟨ha, hd⟩⟩
  obtain ⟨X, Y, Z, W, hXY, hXYunion, hZW, hZWunion, hXcard, hYcard, hZcard,
    hRXZ', hRYW', hBXW', hBYZ'⟩ := bipartite_two_color_exact R' B' A D m hAD hAcard hDcard
      hRbip hBbip hCross hR'no hB'no
  have hSides : Disjoint (X ∪ Y) (Z ∪ W) := by rw [hXYunion, hZWunion]; exact hAD
  have hXZ : Disjoint X Z := hSides.mono Finset.subset_union_left Finset.subset_union_left
  have hXW : Disjoint X W := hSides.mono Finset.subset_union_left Finset.subset_union_right
  have hYZ : Disjoint Y Z := hSides.mono Finset.subset_union_right Finset.subset_union_left
  have hYW : Disjoint Y W := hSides.mono Finset.subset_union_right Finset.subset_union_right
  have hRXZ : ∀ x ∈ X, ∀ z ∈ Z, R.Adj x z := fun x hx z hz => (hRXZ' x hx z hz).1.1
  have hRYW : ∀ y ∈ Y, ∀ w ∈ W, R.Adj y w := fun y hy w hw => (hRYW' y hy w hw).1.1
  have hBXW : ∀ x ∈ X, ∀ w ∈ W, B.Adj x w := fun x hx w hw => (hBXW' x hx w hw).1.1
  have hBYZ : ∀ y ∈ Y, ∀ z ∈ Z, B.Adj y z := fun y hy z hz => (hBYZ' y hy z hz).1.1
  have hZWcard : Z.card + W.card = 2 * m + 1 := by
    rw [← Finset.card_union_of_disjoint hZW, hZWunion, hDcard]
  have hWlarge : m + 1 ≤ W.card := by omega
  have hRedRegions : Disjoint ((X : Set V) ∪ (Z : Set V)) ((Y : Set V) ∪ (W : Set V)) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    rcases hu with hu | hu <;> rcases hu' with hu' | hu'
    · exact Finset.disjoint_left.mp hXY hu hu'
    · exact Finset.disjoint_left.mp hXW hu hu'
    · exact Finset.disjoint_left.mp hYZ hu' hu
    · exact Finset.disjoint_left.mp hZW hu hu'
  have hBlueRegions : Disjoint ((X : Set V) ∪ (W : Set V)) ((Y : Set V) ∪ (Z : Set V)) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    rcases hu with hu | hu <;> rcases hu' with hu' | hu'
    · exact Finset.disjoint_left.mp hXY hu hu'
    · exact Finset.disjoint_left.mp hXZ hu hu'
    · exact Finset.disjoint_left.mp hYW hu' hu
    · exact Finset.disjoint_left.mp hZW hu' hu
  have hNoRed : Z.Nonempty → ∀ u ∈ (X : Set V) ∪ (Z : Set V),
      ∀ v ∈ (Y : Set V) ∪ (W : Set V), ¬ R.Adj u v := by
    intro hZ u hu v hv huv
    have hz : 1 ≤ Z.card := Finset.card_pos.mpr hZ
    have hcm := HasCM.of_bridged_complete_joins R X Z Y W 1 m hXZ hYW hRedRegions
      (by omega) hz hYcard.ge (by omega) hRXZ hRYW u v hu hv huv
    exact hno (σ 0) (by simpa only [Nat.add_comm 1 m] using hcm)
  have hNoBlue : Z.Nonempty → ∀ u ∈ (X : Set V) ∪ (W : Set V),
      ∀ v ∈ (Y : Set V) ∪ (Z : Set V), ¬ B.Adj u v := by
    intro hZ u hu v hv huv
    have hz : 1 ≤ Z.card := Finset.card_pos.mpr hZ
    exact hno (σ 1) (HasCM.of_bridged_complete_joins B X W Y Z m 1 hXW hYZ hBlueRegions
      hXcard.ge (by omega) (by omega) hz hBXW hBYZ u v hu hv huv)
  have hHZW : ∀ z ∈ Z, ∀ w ∈ W, H.Adj z w := by
    intro z hz w hw
    have hne : z ≠ w := fun h => Finset.disjoint_left.mp hZW hz (h.symm ▸ hw)
    rcases three_color_cover_permuted c σ hcover hne with h | h | h
    · exact (hNoRed ⟨z, hz⟩ z (Or.inr hz) w (Or.inr hw) h).elim
    · exact (hNoBlue ⟨z, hz⟩ w (Or.inr hw) z (Or.inr hz) h.symm).elim
    · exact h
  have hHXY : Z.Nonempty → ∀ x ∈ X, ∀ y ∈ Y, H.Adj x y := by
    intro hZ x hx y hy
    have hne : x ≠ y := fun h => Finset.disjoint_left.mp hXY hx (h.symm ▸ hy)
    rcases three_color_cover_permuted c σ hcover hne with h | h | h
    · exact (hNoRed hZ x (Or.inl hx) y (Or.inl hy) h).elim
    · exact (hNoBlue hZ x (Or.inl hx) y (Or.inl hy) h).elim
    · exact h
  have hHW : m + 2 ≤ W.card → H.IsClique (W : Set V) := by
    intro hW u hu v hv huv
    have hWminus : m + 1 ≤ (W.erase u).card := by
      rw [Finset.card_erase_of_mem hu]
      omega
    have hvErase : v ∈ W.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
    have hnotR : ¬ R.Adj u v := by
      intro h
      exact hno (σ 0) (HasCM.of_complete_join_and_extra_edge R Y (W.erase u) m
        (hYW.mono_right (Finset.erase_subset u W)) hYcard.ge hWminus
        (fun y hy w hw => hRYW y hy w (Finset.mem_of_mem_erase hw)) u v
        (fun huY => Finset.disjoint_left.mp hYW huY hu) (Finset.notMem_erase _ _)
        hvErase h)
    have hnotB : ¬ B.Adj u v := by
      intro h
      exact hno (σ 1) (HasCM.of_complete_join_and_extra_edge B X (W.erase u) m
        (hXW.mono_right (Finset.erase_subset u W)) hXcard.ge hWminus
        (fun x hx w hw => hBXW x hx w (Finset.mem_of_mem_erase hw)) u v
        (fun huX => Finset.disjoint_left.mp hXW huX hu) (Finset.notMem_erase _ _)
        hvErase h)
    rcases three_color_cover_permuted c σ hcover huv with h | h | h
    · exact (hnotR h).elim
    · exact (hnotB h).elim
    · exact h
  exact ⟨{
    colors := σ, X := X, Y := Y, Z := Z, W := W,
    disjointXY := hXY, disjointZW := hZW, disjointSides := hSides,
    cardX := hXcard, cardY := hYcard, cardZ := hZcard, cardZW := hZWcard,
    redXZ := hRXZ, redYW := hRYW, blueXW := hBXW, blueYZ := hBYZ,
    greenZW := hHZW, greenXY := hHXY, greenW := hHW }⟩


end MatchingStability

end PermutedModule24

/- Source module: FourBlockAugmentation.lean -/
section PermutedModule25

/-!
Augment the four-block core by one outside vertex. The only new construction
is a matching in a complete join to a clique, with one prescribed outside
edge. Credit: @fqlx.
-/

open SimpleGraph Finset

namespace MatchingStability

theorem HasCM.of_join_clique_and_extra_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (m : ℕ)
    (hdis : Disjoint A B) (hA : A.card ≤ m) (hcard : A.card+B.card=2*m+1)
    (hjoin : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hclique : G.IsClique (B : Set V))
    (v w : V) (hvA : v ∉ A) (hvB : v ∉ B) (hw : w ∈ B) (hvw : G.Adj v w) :
    HasCM G (m+1) := by
  classical
  have hBerase : A.card ≤ (B.erase w).card := by
    have hc := card_erase_add_one hw
    omega
  obtain ⟨U,hUB,hUcard⟩ := exists_subset_card_eq hBerase
  have hUB' : U ⊆ B := hUB.trans (erase_subset w B)
  have hAU : Disjoint (A : Set V) (U : Set V) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxU
    exact Finset.disjoint_left.mp hdis hxA (hUB' hxU)
  let f : (A : Set V) ≃ (U : Set V) := Fintype.equivOfCardEq (by simpa using hUcard.symm)
  obtain ⟨M₁,hM₁v,hM₁⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hAU f
    (fun x => hjoin x x.property (f x) (hUB' (f x).property))
  let R := B.erase w \ U
  have hRsub : R ⊆ B := sdiff_subset.trans (erase_subset w B)
  have hRcard : R.card=2*(m-A.card) := by
    have h1:=card_erase_add_one hw
    have h2:=card_sdiff_add_card_eq_card hUB
    change R.card+U.card=(B.erase w).card at h2
    omega
  have hReven : Even (R : Set V).ncard := by
    rw [show (R : Set V).ncard=R.card by simp,hRcard]
    exact even_two_mul _
  have hRclique : G.IsClique (R : Set V) :=
    fun x hx y hy hxy => hclique (hRsub hx) (hRsub hy) hxy
  obtain ⟨M₂,hM₂v,hM₂⟩ := (hRclique.even_iff_exists_isMatching (Set.toFinite _)).mp hReven
  have hMdisV : Disjoint M₁.verts M₂.verts := by
    rw [hM₁v,hM₂v]
    apply Set.disjoint_left.mpr
    intro x hx hxR
    rcases hx with hxA | hxU
    · exact Finset.disjoint_left.mp hdis hxA (hRsub hxR)
    · exact (mem_sdiff.mp hxR).2 hxU
  have hMdis : Disjoint M₁.support M₂.support := by
    rw [hM₁.support_eq_verts,hM₂.support_eq_verts]
    exact hMdisV
  let M := M₁ ⊔ M₂
  have hM : M.IsMatching := hM₁.sup hM₂ hMdis
  have hMv : M.verts = (A : Set V) ∪ (B.erase w : Set V) := by
    rw [show M.verts=M₁.verts∪M₂.verts from rfl,hM₁v,hM₂v]
    ext x
    simp only [Set.mem_union,mem_coe,R,mem_sdiff]
    constructor
    · rintro (h | h)
      · exact h.imp_right (fun hx=> hUB hx)
      · exact Or.inr h.1
    · rintro (ha | hb)
      · exact Or.inl (Or.inl ha)
      · by_cases hxU : x∈U
        · exact Or.inl (Or.inr hxU)
        · exact Or.inr ⟨hb,hxU⟩
  have hMcard : M.verts.ncard=2*m := by
    rw [hMv,← coe_union]
    simp only [Set.ncard_coe_finset]
    rw [card_union_of_disjoint (hdis.mono_right (erase_subset w B))]
    have h:=card_erase_add_one hw
    omega
  have hvM : v ∉ M.verts := by
    rw [hMv]
    rintro (h | h)
    · exact hvA h
    · exact hvB (mem_of_mem_erase h)
  have hwM : w ∉ M.verts := by
    rw [hMv]
    rintro (h | h)
    · exact Finset.disjoint_left.mp hdis h hw
    · exact notMem_erase w B h
  let E := G.subgraphOfAdj hvw
  have hE : E.IsMatching := Subgraph.IsMatching.subgraphOfAdj hvw
  have hMEv : Disjoint M.verts E.verts := by
    rw [show E.verts=({v,w} : Set V) from rfl]
    apply Set.disjoint_left.mpr
    intro x hx hxE
    rcases hxE with h | h
    · exact hvM (h ▸ hx)
    · exact hwM (h ▸ hx)
  have hME : Disjoint M.support E.support := by
    rw [hM.support_eq_verts,hE.support_eq_verts]
    exact hMEv
  have hEcard : E.verts.ncard=2 := by
    change ({v,w} : Set V).ncard=2
    simp [hvw.ne]
  have hreach : ∀ x ∈ (M⊔E).verts, G.Reachable x w := by
    intro x hx
    change x∈M.verts ∨ x∈E.verts at hx
    rcases hx with hx | hx
    · rw [hMv] at hx
      rcases hx with hxA | hxB
      · exact (hjoin x hxA w hw).reachable
      · exact (hclique (mem_of_mem_erase hxB) hw (ne_of_mem_erase hxB)).reachable
    · change x=v ∨ x=w at hx
      rcases hx with rfl | rfl
      · exact hvw.reachable
      · exact Reachable.rfl
  refine ⟨M⊔E,hM.sup hE hME,?_,fun x hx y hy=>(hreach x hx).trans (hreach y hy).symm⟩
  rw [Subgraph.verts_sup,Set.ncard_union_eq hMEv,hMcard,hEcard]
  omega

/-- One outside vertex augments the odd four-block core to a connected
matching with one additional edge, in some color. -/
theorem FourBlockCore.augment
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) (m : ℕ) (p : FourBlockCore c m)
    (hcover : ∀ u v : V, u ≠ v → ∃ k, (c k).Adj u v)
    (v : V) (hv : v ∉ (p.X∪p.Y)∪(p.Z∪p.W)) :
    ∃ k, HasCM (c k) (m+1) := by
  classical
  have hW : m+1 ≤ p.W.card := by have h1:=p.cardZ; have h2:=p.cardZW; omega
  obtain ⟨w,hw⟩ := card_pos.mp (by omega : 0 < p.W.card)
  have hvX : v ∉ p.X := fun h=> hv (mem_union_left _ (mem_union_left _ h))
  have hvY : v ∉ p.Y := fun h=> hv (mem_union_left _ (mem_union_right _ h))
  have hvZ : v ∉ p.Z := fun h=> hv (mem_union_right _ (mem_union_left _ h))
  have hvW : v ∉ p.W := fun h=> hv (mem_union_right _ (mem_union_right _ h))
  have hvw : v ≠ w := fun h=> hvW (h.symm ▸ hw)
  obtain ⟨k,hk⟩ := hcover v w hvw
  obtain ⟨i,rfl⟩ := p.colors.surjective k
  fin_cases i
  · refine ⟨p.colors 0,?_⟩
    exact HasCM.of_complete_join_and_extra_edge (c (p.colors 0)) p.Y p.W m
      (p.disjointSides.mono subset_union_right subset_union_right) p.cardY.ge hW
      p.redYW v w hvY hvW hw hk
  · refine ⟨p.colors 1,?_⟩
    exact HasCM.of_complete_join_and_extra_edge (c (p.colors 1)) p.X p.W m
      (p.disjointSides.mono subset_union_left subset_union_right) p.cardX.ge hW
      p.blueXW v w hvX hvW hw hk
  · refine ⟨p.colors 2,?_⟩
    by_cases hWlarge : m+2 ≤ p.W.card
    · exact HasCM.of_join_clique_and_extra_edge (c (p.colors 2)) p.Z p.W m
        p.disjointZW p.cardZ p.cardZW p.greenZW (p.greenW hWlarge) v w hvZ hvW hw hk
    · have hZ : m ≤ p.Z.card := by have h:=p.cardZW; omega
      exact HasCM.of_complete_join_and_extra_edge (c (p.colors 2)) p.Z p.W m
        p.disjointZW hZ hW p.greenZW v w hvZ hvW hw hk


end MatchingStability

end PermutedModule25

/- Source module: FiniteConnectedMatchingClassification.lean -/
section PermutedModule26

/-!
The complete finite induction behind Letzter's Lemma 5.1, including its
connected-matching Ramsey consequence. The argument works for multicolored
complete graphs. Credit: @fqlx.
-/

open SimpleGraph

namespace MatchingStability

universe u

theorem finite_connected_matching_classification (m : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (c : Fin 3 → SimpleGraph V),
      Fintype.card V = 4 * m + 1 →
      (∀ a b, a ≠ b → ∃ k, (c k).Adj a b) →
      (∀ k, ¬ HasCM (c k) (m + 1)) → Nonempty (FourBlockCore c m) := by
  induction m with
  | zero =>
    intro V _ _ c hsize _ _
    have hpos : 0 < Fintype.card V := by omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨FourBlockCore.zero c v⟩
  | succ n ih =>
    intro V _ _ c hsize hcover hno
    classical
    by_cases hcut : ∃ i, BalancedMissingCut (c i) (n + 1)
    · obtain ⟨i, hi⟩ := hcut
      exact four_block_core_of_balanced_cut c (n + 1) hcover hno i hi
    · have hNoCut : ∀ i, ¬ BalancedMissingCut (c i) (n + 1) := fun i hi => hcut ⟨i, hi⟩
      have hlarge : ∀ i, ∀ C : (c i).ConnectedComponent, HasCM C.toSimpleGraph (n + 1) →
          2 * (n + 1) + 2 ≤ C.supp.ncard := by
        intro i C hC
        exact component_large_of_no_balanced_cut (c i) (n + 1) hsize (hNoCut i) C hC
      have hpos : 0 < Fintype.card V := by omega
      obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hpos
      have hdelete : ∀ i, ∃ v : V, ¬ HasCM ((c i).induce ({v}ᶜ : Set V)) (n + 1) := by
        intro i
        exact exists_vertex_killing_CM (c i) v₀ (n + 1) (by omega) (by omega) (hno i) (hlarge i)
      choose v hv using hdelete
      let D : Finset V := Finset.univ.image v
      have hDcard : D.card ≤ 3 := by
        exact (Finset.card_image_le).trans (by simp)
      let S : Set V := (D : Set V)ᶜ
      have hScard : 4 * n + 2 ≤ Fintype.card S := by
        have hsum := Set.ncard_add_ncard_compl (D : Set V)
        have hs : S.ncard = Fintype.card S := by
          rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
        simp only [Set.ncard_coe_finset, Nat.card_eq_fintype_card] at hsum
        change D.card + S.ncard = Fintype.card V at hsum
        omega
      let G : Fin 3 → SimpleGraph S := fun i => (c i).induce S
      have hGcover : ∀ a b : S, a ≠ b → ∃ k, (G k).Adj a b := by
        intro a b hab
        exact hcover a b (Subtype.val_injective.ne hab)
      have hGno : ∀ i, ¬ HasCM (G i) (n + 1) := by
        intro i h
        have hS : S ⊆ ({v i}ᶜ : Set V) := by
          intro x hx hxi
          have hmem : v i ∈ D := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
          exact hx (hxi.symm ▸ hmem)
        exact hv i (h.map ((c i).induceHomOfLE hS).toHom ((c i).induceHomOfLE hS).injective)
      obtain ⟨T, _, hTcard⟩ := Finset.exists_subset_card_eq
        (show 4 * n + 1 ≤ (Finset.univ : Finset S).card by simpa using (by omega : 4 * n + 1 ≤ Fintype.card S))
      let H : Fin 3 → SimpleGraph T := fun i => (G i).induce (T : Set S)
      have hHsize : Fintype.card T = 4 * n + 1 := by simpa using hTcard
      have hHcover : ∀ a b : T, a ≠ b → ∃ k, (H k).Adj a b := by
        intro a b hab
        exact hGcover a b (Subtype.val_injective.ne hab)
      have hHno : ∀ k, ¬ HasCM (H k) (n + 1) := fun k h =>
        hGno k (h.map (Embedding.induce _).toHom Subtype.val_injective)
      obtain ⟨p⟩ := ih H hHsize hHcover hHno
      let pS : FourBlockCore G n := p.map (Function.Embedding.subtype _) (fun _ _ _ h => h)
      obtain ⟨x, hx⟩ := pS.exists_outside (by omega)
      obtain ⟨k, hk⟩ := FourBlockCore.augment G n pS hGcover x hx
      exact (hGno k hk).elim

theorem complete_three_color_hasCM
    {V : Type u} [Fintype V] [DecidableEq V] (c : Fin 3 → SimpleGraph V) (m : ℕ)
    (hsize : Fintype.card V = 4 * m + 1)
    (hcover : ∀ u v, u ≠ v → ∃ k, (c k).Adj u v) :
    ∃ k, HasCM (c k) m := by
  classical
  by_contra! hno
  have hnoLarger : ∀ k, ¬ HasCM (c k) (m + 1) := by
    rintro k ⟨M, hM, hcard, hcon⟩
    exact hno k ⟨M, hM, by omega, hcon⟩
  obtain ⟨p⟩ := finite_connected_matching_classification m c hsize hcover hnoLarger
  have hYW : Disjoint p.Y p.W :=
    p.disjointSides.mono Finset.subset_union_right Finset.subset_union_right
  have hW : m ≤ p.W.card := by have hz := p.cardZ; have hzw := p.cardZW; omega
  exact hno (p.colors 0) (HasCM.of_complete_join (c (p.colors 0)) p.Y p.W m
    hYW p.cardY.ge hW p.redYW)

theorem complete_three_color_hasCM_of_card_le
    {V : Type u} [Fintype V] [DecidableEq V] (c : Fin 3 → SimpleGraph V) (m : ℕ)
    (hsize : 4 * m + 1 ≤ Fintype.card V)
    (hcover : ∀ u v, u ≠ v → ∃ k, (c k).Adj u v) :
    ∃ k, HasCM (c k) m := by
  classical
  obtain ⟨T, _, hTcard⟩ := Finset.exists_subset_card_eq
    (show 4 * m + 1 ≤ (Finset.univ : Finset V).card by simpa using hsize)
  let d : Fin 3 → SimpleGraph T := fun i => (c i).induce (T : Set V)
  have hTsize : Fintype.card T = 4 * m + 1 := by simpa using hTcard
  have hTcover : ∀ a b : T, a ≠ b → ∃ k, (d k).Adj a b := by
    intro a b hab
    exact hcover a b (Subtype.val_injective.ne hab)
  obtain ⟨k, hk⟩ := complete_three_color_hasCM d m hTsize hTcover
  exact ⟨k, hk.map (Embedding.induce _).toHom Subtype.val_injective⟩


end MatchingStability

end PermutedModule26

/- Source module: LargeMissingCut.lean -/
section PermutedModule27

/-!
Repeated essential-vertex deletion gives a large cut missing one color.
This quantitative step uses the complete finite connected-matching theorem,
with no regularity or asymptotic assumption. Credit: @fqlx.
-/

open SimpleGraph

namespace MatchingStability

universe u

/-- Two disjoint large vertex sets with no graph edge between them. -/
def LargeMissingCut {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ A B : Finset V, Disjoint A B ∧ 2 * r ≤ A.card ∧ 2 * r ≤ B.card ∧
    ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

theorem exists_vertex_killing_CM_of_unique_component
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v₀ : V) (m : ℕ) (hm : 1 ≤ m)
    (hno : ¬ HasCM G (m + 1))
    (hlarge : ∀ C : G.ConnectedComponent, HasCM C.toSimpleGraph m →
      2 * m + 2 ≤ C.supp.ncard)
    (hunique : ∀ C D : G.ConnectedComponent, HasCM C.toSimpleGraph m →
      HasCM D.toSimpleGraph m → C = D) :
    ∃ v : V, ¬ HasCM (G.induce ({v}ᶜ : Set V)) m := by
  classical
  by_cases hCM : HasCM G m
  swap
  · refine ⟨v₀, fun h => hCM (h.map (Embedding.induce _).toHom Subtype.val_injective)⟩
  obtain ⟨C, hC⟩ := hCM.exists_component hm
  have hCsize : 2 * m + 2 ≤ Fintype.card C := by
    rw [← Nat.card_eq_fintype_card]
    change 2 * m + 2 ≤ Nat.card C.supp
    simpa only [Nat.card_coe_set_eq] using hlarge C hC
  have hCno : ¬ HasCM C.toSimpleGraph (m + 1) := fun h =>
    hno (h.map C.toSimpleGraph_hom Subtype.val_injective)
  obtain ⟨v, hv⟩ := exists_essential_vertex_of_no_larger_CM C.toSimpleGraph
    C.connected_toSimpleGraph m hCsize hCno
  refine ⟨v, ?_⟩
  rintro ⟨M, hM, hMsize, hMcon⟩
  let f : (G.induce ({(v : V)}ᶜ : Set V)) →g G := (Embedding.induce _).toHom
  let N := M.map f
  have hN : N.IsMatching := hM.map f Subtype.val_injective
  have hNv : N.verts = Subtype.val '' M.verts := rfl
  have hNsize : 2 * m ≤ N.verts.ncard := by
    rw [hNv, Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hMsize
  have hNcon : ∀ u ∈ N.verts, ∀ w ∈ N.verts, G.Reachable u w := by
    simp only [hNv, Set.mem_image]
    rintro u ⟨u', hu', rfl⟩ w ⟨w', hw', rfl⟩
    exact (hMcon u' hu' w' hw').map f
  have hvNot : (v : V) ∉ N.verts := by
    rw [hNv]
    rintro ⟨w, _, hw⟩
    exact w.property hw
  obtain ⟨u, hu⟩ := Set.nonempty_of_ncard_ne_zero (by omega : N.verts.ncard ≠ 0)
  let D := G.connectedComponentMk u
  have hND : N.verts ⊆ D.supp := by
    intro w hw
    exact ConnectedComponent.sound (hNcon w hw u hu)
  obtain ⟨N_D, hN_D, _, hN_Dcard⟩ := matching_induce_with_verts G N hN D.supp hND
  have hD : HasCM D.toSimpleGraph m :=
    HasCM.of_preconnected D.connected_toSimpleGraph.preconnected N_D hN_D
      (by simpa only [hN_Dcard] using hNsize)
  have hDC : D = C := hunique D C hD hC
  have hNC : N.verts ⊆ C.supp := hDC ▸ hND
  obtain ⟨N_C, hN_C, hN_Cverts, hN_Ccard⟩ := matching_induce_with_verts G N hN C.supp hNC
  have hvC := hv N_C hN_C (by simpa only [hN_Ccard] using hNsize)
  rw [hN_Cverts] at hvC
  exact hvNot hvC


theorem LargeMissingCut.map
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ}
    (h : LargeMissingCut G r) (f : G ↪g H) : LargeMissingCut H r := by
  classical
  obtain ⟨A, B, hAB, hA, hB, hno⟩ := h
  refine ⟨A.map f.toEmbedding, B.map f.toEmbedding, ?_, by simpa using hA,
    by simpa using hB, ?_⟩
  · simpa using hAB
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    exact hno a' ha' b' hb' (f.map_rel_iff.mp hab)

theorem component_size_of_CM
    {V : Type*} [Fintype V] (G : SimpleGraph V) (t : ℕ)
    (C : G.ConnectedComponent) (hC : HasCM C.toSimpleGraph t) :
    2 * t ≤ C.supp.ncard := by
  obtain ⟨M, _, hMsize, _⟩ := hC
  have hbound := Set.ncard_le_card M.verts
  change M.verts.ncard ≤ Nat.card C.supp at hbound
  simp only [Nat.card_coe_set_eq] at hbound
  omega

theorem component_unique_of_no_large_missing_cut
    {V : Type*} [Fintype V] (G : SimpleGraph V) (r t : ℕ) (hrt : r ≤ t)
    (hnoCut : ¬ LargeMissingCut G r)
    (C D : G.ConnectedComponent) (hC : HasCM C.toSimpleGraph t)
    (hD : HasCM D.toSimpleGraph t) : C = D := by
  classical
  by_contra hne
  have hdisj : Disjoint C.supp D.supp := pairwise_disjoint_supp_connectedComponent G hne
  have hCsize := component_size_of_CM G t C hC
  have hDsize := component_size_of_CM G t D hD
  apply hnoCut
  refine ⟨C.supp.toFinset, D.supp.toFinset, ?_, ?_, ?_, ?_⟩
  · simpa using hdisj
  · simpa only [← Set.ncard_eq_toFinset_card'] using (by omega : 2 * r ≤ C.supp.ncard)
  · simpa only [← Set.ncard_eq_toFinset_card'] using (by omega : 2 * r ≤ D.supp.ncard)
  · intro a ha b hb hab
    have hbC := C.mem_supp_of_adj_mem_supp (by simpa using ha) hab
    exact Set.disjoint_left.mp hdisj hbC (by simpa using hb)

theorem component_large_of_no_large_missing_cut
    {V : Type*} [Fintype V] (G : SimpleGraph V) (r t : ℕ) (hrt : r ≤ t)
    (hsize : 2 * r + 2 * (t + 1) ≤ Fintype.card V + 1)
    (hnoCut : ¬ LargeMissingCut G r)
    (C : G.ConnectedComponent) (hC : HasCM C.toSimpleGraph t) :
    2 * t + 2 ≤ C.supp.ncard := by
  classical
  by_contra! hsmall
  have hlower := component_size_of_CM G t C hC
  let A := C.supp.toFinset
  have hAcard : A.card = C.supp.ncard := (Set.ncard_eq_toFinset_card' _).symm
  apply hnoCut
  refine ⟨A, Finset.univ \ A, disjoint_sdiff_self_right, by omega, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  · intro a ha b hb hab
    have hbC := C.mem_supp_of_adj_mem_supp (by simpa [A] using ha) hab
    exact (Finset.mem_sdiff.mp hb).2 (by simpa [A] using hbC)


end MatchingStability

end PermutedModule27

/- Source module: RepeatedCMDeletion.lean -/
section PermutedModule28

/-!
Independent essential-vertex deletions in the three colors produce a large
two-color cut. The exact loss is three times the matching-threshold gap.
Credit: @fqlx.
-/

open SimpleGraph

namespace MatchingStability

universe u

theorem delete_to_lower_CM_threshold (r : ℕ) (hr : 1 ≤ r) (s : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      r ≤ s → 2 * r + 2 * s ≤ Fintype.card V + 1 →
      ¬ HasCM G s → ¬ LargeMissingCut G r →
      ∃ D : Finset V, D.card ≤ s - r ∧
        ¬ HasCM (G.induce ((D : Set V)ᶜ)) r := by
  induction s with
  | zero =>
    intro V _ _ G hrs
    omega
  | succ t ih =>
    intro V _ _ G hrs hsize hno hnoCut
    classical
    by_cases hrt : r ≤ t
    · have hpos : 0 < Fintype.card V := by omega
      obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hpos
      have hlarge : ∀ C : G.ConnectedComponent, HasCM C.toSimpleGraph t →
          2 * t + 2 ≤ C.supp.ncard :=
        component_large_of_no_large_missing_cut G r t hrt hsize hnoCut
      have hunique : ∀ C D : G.ConnectedComponent, HasCM C.toSimpleGraph t →
          HasCM D.toSimpleGraph t → C = D :=
        component_unique_of_no_large_missing_cut G r t hrt hnoCut
      obtain ⟨v, hv⟩ := exists_vertex_killing_CM_of_unique_component G v₀ t
        (by omega) hno hlarge hunique
      let S : Set V := ({v} : Set V)ᶜ
      let H := G.induce S
      have hScard : Fintype.card S + 1 = Fintype.card V := by
        have hsum := Set.ncard_add_ncard_compl ({v} : Set V)
        have hs : S.ncard = Fintype.card S := by
          rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
        simp only [Set.ncard_singleton, Nat.card_eq_fintype_card] at hsum
        change 1 + S.ncard = Fintype.card V at hsum
        omega
      have hHsize : 2 * r + 2 * t ≤ Fintype.card S + 1 := by omega
      have hHnoCut : ¬ LargeMissingCut H r := fun h =>
        hnoCut (h.map (Embedding.induce S))
      obtain ⟨D', hD'card, hD'no⟩ := ih H hrt hHsize hv hHnoCut
      let D : Finset V := insert v (D'.map (Function.Embedding.subtype S))
      have hvNot : v ∉ D'.map (Function.Embedding.subtype S) := by
        rintro h
        obtain ⟨x, _, hx⟩ := Finset.mem_map.mp h
        exact x.property hx
      have hDcard : D.card ≤ t + 1 - r := by
        have hc : D.card = D'.card + 1 := by
          simp only [D, Finset.card_insert_of_notMem hvNot, Finset.card_map]
        omega
      refine ⟨D, hDcard, ?_⟩
      intro hCM
      have hNotV : ∀ x : ↥((D : Set V)ᶜ), (x : V) ≠ v := by
        intro x hx
        exact x.property (by simp [D, hx])
      let g : ↥((D : Set V)ᶜ) → S := fun x => ⟨x, hNotV x⟩
      have hg : ∀ x : ↥((D : Set V)ᶜ), g x ∉ D' := by
        intro x hx
        apply x.property
        apply Finset.mem_insert_of_mem
        exact Finset.mem_map.mpr ⟨g x, hx, rfl⟩
      let f : (G.induce ((D : Set V)ᶜ)) →g (H.induce ((D' : Set S)ᶜ)) := {
        toFun := fun x => ⟨g x, hg x⟩
        map_rel' := fun h => h }
      have hf : Function.Injective f := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : ↥((D' : Set S)ᶜ) => z.val.val) hxy
      exact hD'no (hCM.map f hf)
    · have heq : r = t + 1 := by omega
      refine ⟨∅, by simp, ?_⟩
      intro h
      exact hno (heq ▸ h.map (Embedding.induce _).toHom Subtype.val_injective)

theorem large_missing_cut_of_complete_three_color
    {V : Type u} [Fintype V] [DecidableEq V] (c : Fin 3 → SimpleGraph V)
    (r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s)
    (hsize : 3 * s + r + 1 ≤ Fintype.card V)
    (hcover : ∀ u v, u ≠ v → ∃ k, (c k).Adj u v)
    (hno : ∀ k, ¬ HasCM (c k) s) :
    ∃ k, LargeMissingCut (c k) r := by
  classical
  by_contra! hnoCut
  have hsize' : 2 * r + 2 * s ≤ Fintype.card V + 1 := by omega
  have hdel : ∀ k, ∃ D : Finset V, D.card ≤ s - r ∧
      ¬ HasCM ((c k).induce ((D : Set V)ᶜ)) r := by
    intro k
    exact delete_to_lower_CM_threshold r hr s (c k) hrs hsize' (hno k) (hnoCut k)
  choose D hDcard hDno using hdel
  let E := (D 0 ∪ D 1) ∪ D 2
  have hEcard : E.card ≤ 3 * (s - r) := by
    have h01 := Finset.card_union_le (D 0) (D 1)
    have h012 := Finset.card_union_le (D 0 ∪ D 1) (D 2)
    have h0 := hDcard 0
    have h1 := hDcard 1
    have h2 := hDcard 2
    change (D 0 ∪ D 1 ∪ D 2).card ≤ 3 * (s - r)
    omega
  have hDE : ∀ k, D k ⊆ E := by
    intro k
    fin_cases k
    · exact Finset.subset_union_left.trans Finset.subset_union_left
    · exact Finset.subset_union_right.trans Finset.subset_union_left
    · exact Finset.subset_union_right
  let T : Set V := (E : Set V)ᶜ
  let d : Fin 3 → SimpleGraph T := fun k => (c k).induce T
  have hTcard : 4 * r + 1 ≤ Fintype.card T := by
    have hsum := Set.ncard_add_ncard_compl (E : Set V)
    have ht : T.ncard = Fintype.card T := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    simp only [Set.ncard_coe_finset, Nat.card_eq_fintype_card] at hsum
    change E.card + T.ncard = Fintype.card V at hsum
    omega
  have hdcover : ∀ u v : T, u ≠ v → ∃ k, (d k).Adj u v := by
    intro u v huv
    exact hcover u v (Subtype.val_injective.ne huv)
  obtain ⟨k, hk⟩ := complete_three_color_hasCM_of_card_le d r hTcard hdcover
  have hTD : T ⊆ ((D k : Set V)ᶜ) := by
    intro x hx hxD
    exact hx (hDE k hxD)
  exact hDno k (hk.map ((c k).induceHomOfLE hTD).toHom
    ((c k).induceHomOfLE hTD).injective)

theorem quantitative_large_missing_cut
    {V : Type u} [Fintype V] [DecidableEq V] (c : Fin 3 → SimpleGraph V)
    (m h : ℕ) (hh : 1 ≤ h) (hm : 1000 * h ≤ m)
    (hsize : Fintype.card V = 4 * m)
    (hcover : ∀ u v, u ≠ v → ∃ k, (c k).Adj u v)
    (hno : ∀ k, ¬ HasCM (c k) (m + h)) :
    ∃ k, LargeMissingCut (c k) (m - 4 * h) := by
  apply large_missing_cut_of_complete_three_color c (m - 4 * h) (m + h)
    (by omega) (by omega) (by omega) hcover hno


end MatchingStability

end PermutedModule28

/- Source module: QuantitativeBipartiteCore.lean -/
section PermutedModule29

/-!
Output structures and normalization of the quantitative two-colour bipartite
classification. New proofs: @fqlx, following the quantitative complete-graph
stability argument recorded in finite_matching_stability_blueprint.md.
-/

open SimpleGraph Finset

namespace MatchingStability

def ExclusiveJoin {V : Type*} (R B : SimpleGraph V) (X Y : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, R.Adj x y ∧ ¬ B.Adj x y

theorem ExclusiveJoin.symm {V : Type*} {R B : SimpleGraph V} {X Y : Finset V}
    (h : ExclusiveJoin R B X Y) : ExclusiveJoin R B Y X := by
  intro y hy x hx
  exact ⟨(h x hx y hy).1.symm,fun hxy => (h x hx y hy).2 hxy.symm⟩

structure TwoColourRectangle {V : Type*} [DecidableEq V]
    (R B : SimpleGraph V) (r : ℕ) where
  X : Finset V
  Y : Finset V
  Z : Finset V
  W : Finset V
  disjointXY : Disjoint X Y
  disjointZW : Disjoint Z W
  disjointSides : Disjoint (X∪Y) (Z∪W)
  cardXY : X.card+Y.card=2*r
  cardZW : Z.card+W.card=2*r
  nonemptyX : X.Nonempty
  nonemptyY : Y.Nonempty
  nonemptyZ : Z.Nonempty
  nonemptyW : W.Nonempty
  redXZ : ExclusiveJoin R B X Z
  redYW : ExclusiveJoin R B Y W
  blueXW : ExclusiveJoin B R X W
  blueYZ : ExclusiveJoin B R Y Z

def TwoColourRectangle.transpose
    {V : Type*} [DecidableEq V] {R B : SimpleGraph V} {r : ℕ}
    (p : TwoColourRectangle R B r) : TwoColourRectangle R B r where
  X := p.Z
  Y := p.W
  Z := p.X
  W := p.Y
  disjointXY := p.disjointZW
  disjointZW := p.disjointXY
  disjointSides := p.disjointSides.symm
  cardXY := p.cardZW
  cardZW := p.cardXY
  nonemptyX := p.nonemptyZ
  nonemptyY := p.nonemptyW
  nonemptyZ := p.nonemptyX
  nonemptyW := p.nonemptyY
  redXZ := p.redXZ.symm
  redYW := p.redYW.symm
  blueXW := p.blueYZ.symm
  blueYZ := p.blueXW.symm

def TwoColourRectangle.switch
    {V : Type*} [DecidableEq V] {R B : SimpleGraph V} {r : ℕ}
    (p : TwoColourRectangle R B r) : TwoColourRectangle R B r where
  X := p.Y
  Y := p.X
  Z := p.W
  W := p.Z
  disjointXY := p.disjointXY.symm
  disjointZW := p.disjointZW.symm
  disjointSides := by simpa only [union_comm] using p.disjointSides
  cardXY := by rw [add_comm]; exact p.cardXY
  cardZW := by rw [add_comm]; exact p.cardZW
  nonemptyX := p.nonemptyY
  nonemptyY := p.nonemptyX
  nonemptyZ := p.nonemptyW
  nonemptyW := p.nonemptyZ
  redXZ := p.redYW
  redYW := p.redXZ
  blueXW := p.blueYZ
  blueYZ := p.blueXW

structure QuantitativeRectangle {V : Type*} [DecidableEq V]
    (R B : SimpleGraph V) (r s : ℕ) extends TwoColourRectangle R B r where
  lowerX : 2*r+1-s ≤ X.card
  upperX : X.card ≤ s-1
  lowerY : 2*r+1-s ≤ Y.card
  upperY : Y.card ≤ s-1
  orderedZW : Z.card ≤ W.card

structure QuantitativeStrip {V : Type*} [DecidableEq V]
    (R B : SimpleGraph V) (r s : ℕ) where
  X : Finset V
  Y : Finset V
  W : Finset V
  disjointXY : Disjoint X Y
  disjointXW : Disjoint X W
  disjointYW : Disjoint Y W
  lowerX : 2*r+1-s ≤ X.card
  upperX : X.card ≤ s-1
  lowerY : 2*r+1-s ≤ Y.card
  upperY : Y.card ≤ s-1
  lowerW : 2*(2*r+1-s) ≤ W.card
  redXW : ExclusiveJoin R B X W
  blueYW : ExclusiveJoin B R Y W

def QuantitativeStrip.swapColours
    {V : Type*} [DecidableEq V] {R B : SimpleGraph V} {r s : ℕ}
    (p : QuantitativeStrip B R r s) : QuantitativeStrip R B r s where
  X := p.Y
  Y := p.X
  W := p.W
  disjointXY := p.disjointXY.symm
  disjointXW := p.disjointYW
  disjointYW := p.disjointXW
  lowerX := p.lowerY
  upperX := p.upperY
  lowerY := p.lowerX
  upperY := p.upperX
  lowerW := p.lowerW
  redXW := p.blueYW
  blueYW := p.redXW

theorem TwoColourRectangle.quantitative
    {V : Type*} [Fintype V] [DecidableEq V] {R B : SimpleGraph V} {r s : ℕ}
    (hs : 1 ≤ s) (p : TwoColourRectangle R B r)
    (hR : ¬ HasCM R s) (hB : ¬ HasCM B s) :
    Nonempty (QuantitativeRectangle R B r s) := by
  have hxz : Disjoint p.X p.Z := p.disjointSides.mono subset_union_left subset_union_left
  have hxw : Disjoint p.X p.W := p.disjointSides.mono subset_union_left subset_union_right
  have hyz : Disjoint p.Y p.Z := p.disjointSides.mono subset_union_right subset_union_left
  have hyw : Disjoint p.Y p.W := p.disjointSides.mono subset_union_right subset_union_right
  have hsmall : ∃ q : TwoColourRectangle R B r, q.X.card ≤ s-1 ∧ q.Y.card ≤ s-1 := by
    by_cases hx : p.X.card ≤ s-1
    · by_cases hy : p.Y.card ≤ s-1
      · exact ⟨p,hx,hy⟩
      · have hybig : s ≤ p.Y.card := by omega
        have hz : p.Z.card ≤ s-1 := by
          by_contra! hn
          exact hB (HasCM.of_complete_join B p.Y p.Z s hyz hybig (by omega)
            (fun y hy z hz => (p.blueYZ y hy z hz).1))
        have hw : p.W.card ≤ s-1 := by
          by_contra! hn
          exact hR (HasCM.of_complete_join R p.Y p.W s hyw hybig (by omega)
            (fun y hy w hw => (p.redYW y hy w hw).1))
        exact ⟨p.transpose,hz,hw⟩
    · have hxbig : s ≤ p.X.card := by omega
      have hz : p.Z.card ≤ s-1 := by
        by_contra! hn
        exact hR (HasCM.of_complete_join R p.X p.Z s hxz hxbig (by omega)
          (fun x hx z hz => (p.redXZ x hx z hz).1))
      have hw : p.W.card ≤ s-1 := by
        by_contra! hn
        exact hB (HasCM.of_complete_join B p.X p.W s hxw hxbig (by omega)
          (fun x hx w hw => (p.blueXW x hx w hw).1))
      exact ⟨p.transpose,hz,hw⟩
  obtain ⟨q,hx,hy⟩ := hsmall
  have hsum := q.cardXY
  have hlx : 2*r+1-s ≤ q.X.card := by omega
  have hly : 2*r+1-s ≤ q.Y.card := by omega
  by_cases horder : q.Z.card ≤ q.W.card
  · exact ⟨{
      toTwoColourRectangle := q
      lowerX := hlx
      upperX := hx
      lowerY := hly
      upperY := hy
      orderedZW := horder }⟩
  · exact ⟨{
      toTwoColourRectangle := q.switch
      lowerX := hly
      upperX := hy
      lowerY := hlx
      upperY := hx
      orderedZW := le_of_not_ge horder }⟩

end MatchingStability


end PermutedModule29

/- Source module: BipartiteMatchingAppend.lean -/
section PermutedModule30

/-!
Append an arbitrary bipartite matching to a complete join while preserving
connectedness. This supplies the second König-cover step in quantitative
two-colour bipartite stability. New proof: @fqlx.
-/

open SimpleGraph Finset

namespace MatchingStability

theorem HasCM.of_bipartite_family_and_complete_join
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X Y D : Finset V) (P : Finset (V×V))
    (hXY : Disjoint X Y) (hXD : Disjoint X D) (hYD : Disjoint Y D)
    (hY : Y.Nonempty)
    (hP : ∀ e ∈ P, e.1 ∈ X ∧ e.2 ∈ D ∧ G.Adj e.1 e.2)
    (huniq : ∀ p ∈ P, ∀ q ∈ P, p.1=q.1 ∨ p.2=q.2 → p=q)
    (hjoin : ∀ y ∈ Y, ∀ d ∈ D, G.Adj y d)
    (hsize : Y.card+P.card ≤ D.card) :
    HasCM G (Y.card+P.card) := by
  classical
  let T := P.image Prod.snd
  have hTD : T ⊆ D := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
    exact (hP p hp).2.1
  have hTcard : T.card = P.card := by
    apply card_image_of_injOn
    intro p hp q hq he
    exact huniq p hp q hq (Or.inr he)
  have hDminus : Y.card ≤ (D\T).card := by
    rw [card_sdiff_of_subset hTD,hTcard]
    omega
  obtain ⟨M,hM,hMsize,hMsub,hMr⟩ := matching_in_complete_join G Y (D\T) Y.card
    (hYD.mono_right sdiff_subset) le_rfl hDminus
    (fun y hy d hd => hjoin y hy d (mem_sdiff.mp hd).1)
  let left : P → V := fun p => p.val.1
  let right : P → V := fun p => p.val.2
  have hleft : Function.Injective left := by
    intro p q h
    exact Subtype.ext (huniq p p.property q q.property (Or.inl h))
  have hright : Function.Injective right := by
    intro p q h
    exact Subtype.ext (huniq p p.property q q.property (Or.inr h))
  have hends : ∀ p q, left p ≠ right q := by
    intro p q he
    apply Finset.disjoint_left.mp hXD (hP p p.property).1
    change left p ∈ D
    rw [he]
    exact (hP q q.property).2.1
  obtain ⟨N,hN,hNv,hNcard⟩ := matching_of_injective_endpoints G left right
    hleft hright hends (fun p => (hP p p.property).2.2)
  have hNsub : N.verts ⊆ (X : Set V) ∪ (T : Set V) := by
    intro v hv
    rw [hNv] at hv
    rcases hv with ⟨p,rfl⟩ | ⟨p,rfl⟩
    · exact Or.inl (hP p p.property).1
    · exact Or.inr (mem_image.mpr ⟨p,p.property,rfl⟩)
  have hregions : Disjoint ((Y : Set V) ∪ ((D\T : Finset V) : Set V))
      ((X : Set V) ∪ (T : Set V)) := by
    rw [Set.disjoint_left]
    intro v hv hw
    rcases hv with hy | hd
    · rcases hw with hx | ht
      · exact Finset.disjoint_left.mp hXY hx hy
      · exact Finset.disjoint_left.mp hYD hy (hTD ht)
    · have hd' := mem_sdiff.mp hd
      rcases hw with hx | ht
      · exact Finset.disjoint_left.mp hXD hx hd'.1
      · exact hd'.2 ht
  obtain ⟨y,hy⟩ := hY
  have hNr : ∀ v ∈ N.verts, G.Reachable v y := by
    intro v hv
    rw [hNv] at hv
    rcases hv with ⟨p,rfl⟩ | ⟨p,rfl⟩
    · exact (hP p p.property).2.2.reachable.trans
        (hjoin y hy (right p) (hP p p.property).2.1).symm.reachable
    · exact (hjoin y hy (right p) (hP p p.property).2.1).symm.reachable
  exact HasCM.of_two_matchings G M N hM hN (hregions.mono hMsub hNsub)
    Y.card P.card hMsize (by simpa only [Fintype.card_coe] using hNcard.ge)
    y y (fun v hv => hMr v hv y (Or.inl hy)) hNr Reachable.rfl

/-- A large complete join forces a small vertex cover for all extra blue
edges from a disjoint left class. The threshold is exactly `s-|Y|`. -/
theorem cover_extra_edges_beside_complete_join
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X Y D : Finset V) (s : ℕ)
    (hXY : Disjoint X Y) (hXD : Disjoint X D) (hYD : Disjoint Y D)
    (hY : Y.Nonempty) (hYsmall : Y.card < s) (hD : s ≤ D.card)
    (hjoin : ∀ y ∈ Y, ∀ d ∈ D, G.Adj y d) (hno : ¬ HasCM G s) :
    ∃ A ⊆ X, ∃ B ⊆ D, A.card+B.card < s-Y.card ∧
      ∀ x ∈ X, ∀ d ∈ D, G.Adj x d → x ∈ A ∨ d ∈ B := by
  classical
  let neighbors : V → Finset V := fun x => D.filter (G.Adj x)
  have hbound : ∀ P : Finset (V×V),
      (∀ p ∈ P, p.1 ∈ X ∧ p.2 ∈ neighbors p.1) →
      (∀ p ∈ P, ∀ q ∈ P, p.1=q.1 ∨ p.2=q.2 → p=q) → P.card < s-Y.card := by
    intro P hP huniq
    by_contra! hlarge
    obtain ⟨Q,hQP,hQcard⟩ := exists_subset_card_eq hlarge
    have hQ : ∀ p ∈ Q, p.1 ∈ X ∧ p.2 ∈ D ∧ G.Adj p.1 p.2 := by
      intro p hp
      have hh := hP p (hQP hp)
      exact ⟨hh.1,(mem_filter.mp hh.2).1,(mem_filter.mp hh.2).2⟩
    have hsum : Y.card+Q.card=s := by omega
    have hcm := HasCM.of_bipartite_family_and_complete_join G X Y D Q
      hXY hXD hYD hY hQ
      (fun p hp q hq h => huniq p (hQP hp) q (hQP hq) h)
      hjoin (by omega)
    rw [hsum] at hcm
    exact hno hcm
  obtain ⟨A,hAX,B₀,hcover,hcard⟩ := finite_konig_cover X neighbors (s-Y.card) hbound
  refine ⟨A,hAX,B₀∩D,inter_subset_right,?_,?_⟩
  · have hh := card_le_card (inter_subset_left (s₁ := B₀) (s₂ := D))
    omega
  · intro x hx d hd hxd
    by_cases ha : x ∈ A
    · exact Or.inl ha
    · exact Or.inr (mem_inter.mpr
        ⟨hcover x hx ha (mem_filter.mpr ⟨hd,hxd⟩),hd⟩)

end MatchingStability


end PermutedModule30

/- Source module: QuantitativeBipartiteStrip.lean -/
section PermutedModule31

/-!
The two König-cover argument for a quantitative bipartite strip. The coupled
cover bounds preserve the large right class: its size is at least twice the
lower bound on either left class. New proofs: @fqlx.
-/

open SimpleGraph Finset

namespace MatchingStability

theorem quantitative_strip_of_oriented_cover
    {V : Type*} [Fintype V] [DecidableEq V] (R B : SimpleGraph V)
    (A D X E : Finset V) (r s : ℕ)
    (hr : 1 ≤ r) (hrs : r < s) (hcap : 3*s ≤ 4*r+2)
    (hd : Disjoint A D) (hA : A.card=2*r) (hD : D.card=2*r)
    (hXA : X ⊆ A) (hED : E ⊆ D)
    (hcover : ∀ a ∈ A, ∀ d ∈ D, R.Adj a d ∨ B.Adj a d)
    (hRedCover : ∀ a ∈ A, ∀ d ∈ D, R.Adj a d → a ∈ X ∨ d ∈ E)
    (hfirstSize : X.card+E.card < s) (hlarge : 2*r+1-s ≤ X.card)
    (hB : ¬ HasCM B s) : Nonempty (QuantitativeStrip R B r s) := by
  classical
  let Y := A\X
  let D₀ := D\E
  have hXle := card_le_card hXA
  have hEle := card_le_card hED
  have hYcard : Y.card=A.card-X.card := card_sdiff_of_subset hXA
  have hD₀card : D₀.card=D.card-E.card := card_sdiff_of_subset hED
  have hYlow : 2*r+1-s ≤ Y.card := by omega
  have hYhigh : Y.card < s := by omega
  have hYpos : Y.Nonempty := card_pos.mp (by omega)
  have hD₀large : s ≤ D₀.card := by omega
  have hXY : Disjoint X Y := disjoint_sdiff_self_right
  have hXD₀ : Disjoint X D₀ := hd.mono hXA sdiff_subset
  have hYD₀ : Disjoint Y D₀ := hd.mono sdiff_subset sdiff_subset
  have hBlue : ExclusiveJoin B R Y D₀ := by
    intro y hy d hd'
    have hy' := mem_sdiff.mp hy
    have hd'' := mem_sdiff.mp hd'
    have hnot : ¬ R.Adj y d := by
      intro h
      rcases hRedCover y hy'.1 d hd''.1 h with hx | he
      · exact hy'.2 hx
      · exact hd''.2 he
    exact ⟨(hcover y hy'.1 d hd''.1).resolve_left hnot,hnot⟩
  obtain ⟨P,hPX,Q,hQD₀,hsecondSize,hBlueCover⟩ :=
    cover_extra_edges_beside_complete_join B X Y D₀ s hXY hXD₀ hYD₀
      hYpos hYhigh hD₀large (fun y hy d hd => (hBlue y hy d hd).1) hB
  let X' := X\P
  let W := D₀\Q
  have hPle := card_le_card hPX
  have hQle := card_le_card hQD₀
  have hX'card : X'.card=X.card-P.card := card_sdiff_of_subset hPX
  have hWcard : W.card=D₀.card-Q.card := card_sdiff_of_subset hQD₀
  have hX'low : 2*r+1-s ≤ X'.card := by omega
  have hWhigh : 2*(2*r+1-s) ≤ W.card := by omega
  have hRed : ExclusiveJoin R B X' W := by
    intro x hx w hw
    have hx' := mem_sdiff.mp hx
    have hw' := mem_sdiff.mp hw
    have hnot : ¬ B.Adj x w := by
      intro h
      rcases hBlueCover x hx'.1 w hw'.1 h with hp | hq
      · exact hx'.2 hp
      · exact hw'.2 hq
    exact ⟨(hcover x (hXA hx'.1) w (mem_sdiff.mp hw'.1).1).resolve_right hnot,hnot⟩
  exact ⟨{
    X := X'
    Y := Y
    W := W
    disjointXY := hXY.mono_left sdiff_subset
    disjointXW := hXD₀.mono sdiff_subset sdiff_subset
    disjointYW := hYD₀.mono_right sdiff_subset
    lowerX := hX'low
    upperX := by omega
    lowerY := hYlow
    upperY := by omega
    lowerW := hWhigh
    redXW := hRed
    blueYW := fun y hy w hw => hBlue y hy w (mem_sdiff.mp hw).1 }⟩

/-- If all red matchings are small, two applications of König's theorem
produce the quantitative red/blue strip. -/
theorem quantitative_strip_of_ordinary_matching_bound
    {V : Type*} [Fintype V] [DecidableEq V] (R B : SimpleGraph V)
    (A D : Finset V) (r s : ℕ)
    (hr : 1 ≤ r) (hrs : r < s) (hcap : 3*s ≤ 4*r+2)
    (hd : Disjoint A D) (hA : A.card=2*r) (hD : D.card=2*r)
    (hcover : ∀ a ∈ A, ∀ d ∈ D, R.Adj a d ∨ B.Adj a d)
    (hR : ∀ M : R.Subgraph, M.IsMatching → M.verts.ncard < 2*s)
    (hB : ¬ HasCM B s) : Nonempty (QuantitativeStrip R B r s) := by
  classical
  obtain ⟨X,hXA,E,hED,hsize,hRedCover⟩ := bipartite_vertex_cover R A D hd s hR
  by_cases hlarge : 2*r+1-s ≤ X.card
  · exact quantitative_strip_of_oriented_cover R B A D X E r s hr hrs hcap hd hA hD
      hXA hED hcover hRedCover hsize hlarge hB
  · have hElarge : 2*r+1-s ≤ E.card := by
      by_contra hn
      have hXle := card_le_card hXA
      have hEle := card_le_card hED
      have hAXcard := card_sdiff_of_subset hXA
      have hDEcard := card_sdiff_of_subset hED
      apply hB
      apply HasCM.of_complete_join B (A\X) (D\E) s
        (hd.mono sdiff_subset sdiff_subset) (by omega) (by omega)
      intro a ha d hd'
      have ha' := mem_sdiff.mp ha
      have hd'' := mem_sdiff.mp hd'
      apply (hcover a ha'.1 d hd''.1).resolve_left
      intro h
      rcases hRedCover a ha'.1 d hd''.1 h with hx | he
      · exact ha'.2 hx
      · exact hd''.2 he
    apply quantitative_strip_of_oriented_cover R B D A E X r s hr hrs hcap
      hd.symm hD hA hED hXA
    · intro d hd' a ha
      exact (hcover a ha d hd').imp Adj.symm Adj.symm
    · intro d hd' a ha h
      exact (hRedCover a ha d hd' h.symm).symm
    · omega
    · exact hElarge
    · exact hB

end MatchingStability


end PermutedModule31

/- Source module: QuantitativeBipartiteClassification.lean -/
section PermutedModule32

/-!
Quantitative two-colour bipartite classification: an exact nonempty rectangle
or a large exclusive red/blue strip. The label split reuses the proved
BipartiteExactClassification argument; the quantitative normalization and
double-cover branch are new. Credit: @fqlx.
-/

open SimpleGraph Finset

namespace MatchingStability

theorem two_colour_rectangle_of_component_witnesses
    {V : Type*} [Fintype V] [DecidableEq V] (R B : SimpleGraph V)
    (A D : Finset V) (r : ℕ)
    (hd : Disjoint A D) (hA : A.card=2*r) (hD : D.card=2*r)
    (hcover : ∀ a ∈ A, ∀ d ∈ D, R.Adj a d ∨ B.Adj a d)
    (a₀ a₁ d₀ d₁ : V) (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A)
    (hd₀ : d₀ ∈ D) (hd₁ : d₁ ∈ D)
    (hb₀ : B.Adj a₀ d₀) (hb₁ : B.Adj a₁ d₁)
    (hbne : B.connectedComponentMk a₀ ≠ B.connectedComponentMk a₁)
    (hrvary : ∃ a ∈ A, ∃ a' ∈ A,
      R.connectedComponentMk a ≠ R.connectedComponentMk a') :
    Nonempty (TwoColourRectangle R B r) := by
  classical
  have hc : ∀ a : A, ∀ d : D,
      R.connectedComponentMk a = R.connectedComponentMk d ∨
      B.connectedComponentMk a = B.connectedComponentMk d := by
    intro a d
    rcases hcover a a.property d d.property with h | h
    · exact Or.inl (ConnectedComponent.sound h.reachable)
    · exact Or.inr (ConnectedComponent.sound h.reachable)
  obtain ⟨hrne, hLeft, hRight⟩ := bipartite_component_rectangle
    (fun a : A => R.connectedComponentMk a) (fun d : D => R.connectedComponentMk d)
    (fun a : A => B.connectedComponentMk a) (fun d : D => B.connectedComponentMk d)
    hc ⟨a₀, ha₀⟩ ⟨a₁, ha₁⟩ ⟨d₀, hd₀⟩ ⟨d₁, hd₁⟩
    (ConnectedComponent.sound hb₀.reachable) (ConnectedComponent.sound hb₁.reachable) hbne
    (by obtain ⟨a, ha, a', ha', h⟩ := hrvary; exact ⟨⟨a, ha⟩, ⟨a', ha'⟩, h⟩)
  let X := A.filter (fun x => B.connectedComponentMk x = B.connectedComponentMk a₀)
  let Y := A \ X
  let W := D.filter (fun x => B.connectedComponentMk x = B.connectedComponentMk a₀)
  let Z := D \ W
  have hXA : X ⊆ A := Finset.filter_subset _ _
  have hYA : Y ⊆ A := Finset.sdiff_subset
  have hWD : W ⊆ D := Finset.filter_subset _ _
  have hZD : Z ⊆ D := Finset.sdiff_subset
  have hXlabels : ∀ x ∈ X, R.connectedComponentMk x = R.connectedComponentMk a₀ ∧
      B.connectedComponentMk x = B.connectedComponentMk a₀ := by
    intro x hx
    rcases hLeft ⟨x, hXA hx⟩ with h | h
    · exact h
    · exact (hbne ((Finset.mem_filter.mp hx).2.symm.trans h.2)).elim
  have hYlabels : ∀ y ∈ Y, R.connectedComponentMk y = R.connectedComponentMk a₁ ∧
      B.connectedComponentMk y = B.connectedComponentMk a₁ := by
    intro y hy
    rcases hLeft ⟨y, hYA hy⟩ with h | h
    · exact ((Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨hYA hy, h.2⟩)).elim
    · exact h
  have hWlabels : ∀ w ∈ W, R.connectedComponentMk w = R.connectedComponentMk a₁ ∧
      B.connectedComponentMk w = B.connectedComponentMk a₀ := by
    intro w hw
    rcases hRight ⟨w, hWD hw⟩ with h | h
    · exact h
    · exact (hbne ((Finset.mem_filter.mp hw).2.symm.trans h.2)).elim
  have hZlabels : ∀ z ∈ Z, R.connectedComponentMk z = R.connectedComponentMk a₀ ∧
      B.connectedComponentMk z = B.connectedComponentMk a₁ := by
    intro z hz
    rcases hRight ⟨z, hZD hz⟩ with h | h
    · exact ((Finset.mem_sdiff.mp hz).2 (Finset.mem_filter.mpr ⟨hZD hz, h.2⟩)).elim
    · exact h
  have hRXZ : ∀ x ∈ X, ∀ z ∈ Z, R.Adj x z ∧ ¬ B.Adj x z := by
    intro x hx z hz
    apply edge_of_component_ne (hcover x (hXA hx) z (hZD hz))
    rw [(hXlabels x hx).2, (hZlabels z hz).2]
    exact hbne
  have hRYW : ∀ y ∈ Y, ∀ w ∈ W, R.Adj y w ∧ ¬ B.Adj y w := by
    intro y hy w hw
    apply edge_of_component_ne (hcover y (hYA hy) w (hWD hw))
    rw [(hYlabels y hy).2, (hWlabels w hw).2]
    exact hbne.symm
  have hBXW : ∀ x ∈ X, ∀ w ∈ W, B.Adj x w ∧ ¬ R.Adj x w := by
    intro x hx w hw
    apply edge_of_component_ne (hcover x (hXA hx) w (hWD hw)).symm
    rw [(hXlabels x hx).1, (hWlabels w hw).1]
    exact hrne
  have hBYZ : ∀ y ∈ Y, ∀ z ∈ Z, B.Adj y z ∧ ¬ R.Adj y z := by
    intro y hy z hz
    apply edge_of_component_ne (hcover y (hYA hy) z (hZD hz)).symm
    rw [(hYlabels y hy).1, (hZlabels z hz).1]
    exact hrne.symm
  exact ⟨{
    X := X
    Y := Y
    Z := Z
    W := W
    disjointXY := disjoint_sdiff_self_right
    disjointZW := disjoint_sdiff_self_left
    disjointSides := by
      change Disjoint (X∪(A\X)) ((D\W)∪W)
      rw [union_sdiff_of_subset hXA,sdiff_union_of_subset hWD]
      exact hd
    cardXY := by
      have hh := card_sdiff_of_subset hXA
      have hx := card_le_card hXA
      change X.card+(A\X).card=2*r
      omega
    cardZW := by
      have hh := card_sdiff_of_subset hWD
      have hw := card_le_card hWD
      change (D\W).card+W.card=2*r
      omega
    nonemptyX := ⟨a₀,mem_filter.mpr ⟨ha₀,rfl⟩⟩
    nonemptyY := ⟨a₁,mem_sdiff.mpr ⟨ha₁,fun hx => hbne (mem_filter.mp hx).2.symm⟩⟩
    nonemptyZ := ⟨d₁,mem_sdiff.mpr ⟨hd₁,fun hw => hbne
      ((mem_filter.mp hw).2.symm.trans (ConnectedComponent.sound hb₁.reachable).symm)⟩⟩
    nonemptyW := ⟨d₀,mem_filter.mpr ⟨hd₀,(ConnectedComponent.sound hb₀.reachable).symm⟩⟩
    redXZ := hRXZ
    redYW := hRYW
    blueXW := hBXW
    blueYZ := hBYZ }⟩

/-- Two-colour stability on a complete balanced bipartite graph.  The
matching threshold is slightly larger than half a side; all conclusions
retain exclusive colours, even when the input is a multicolouring. -/
theorem quantitative_bipartite_classification
    {V : Type*} [Fintype V] [DecidableEq V] (R B : SimpleGraph V)
    (A D : Finset V) (r s : ℕ)
    (hr : 1 ≤ r) (hrs : r < s) (hcap : 3*s ≤ 4*r+2)
    (hd : Disjoint A D) (hA : A.card=2*r) (hD : D.card=2*r)
    (hRbip : R.IsBipartiteWith (A : Set V) (D : Set V))
    (hBbip : B.IsBipartiteWith (A : Set V) (D : Set V))
    (hcover : ∀ a ∈ A, ∀ d ∈ D, R.Adj a d ∨ B.Adj a d)
    (hR : ¬ HasCM R s) (hB : ¬ HasCM B s) :
    Nonempty (QuantitativeRectangle R B r s) ∨
      Nonempty (QuantitativeStrip R B r s) := by
  classical
  obtain ⟨v₀,_⟩ := card_pos.mp (by omega : 0 < D.card)
  rcases bipartite_components_dichotomy R A D v₀ hRbip with hOneR | hTwoR
  · obtain ⟨C,hC⟩ := hOneR
    exact Or.inr (quantitative_strip_of_ordinary_matching_bound R B A D r s hr hrs hcap
      hd hA hD hcover (matching_bound_of_edges_in_one_component s hR C hC) hB)
  · rcases bipartite_components_dichotomy B A D v₀ hBbip with hOneB | hTwoB
    · obtain ⟨C,hC⟩ := hOneB
      obtain ⟨p⟩ := quantitative_strip_of_ordinary_matching_bound B R A D r s hr hrs hcap
        hd hA hD (fun a ha d hd => (hcover a ha d hd).symm)
        (matching_bound_of_edges_in_one_component s hB C hC) hR
      exact Or.inr ⟨p.swapColours⟩
    · obtain ⟨a₀,ha₀,d₀,hd₀,a₁,ha₁,d₁,hd₁,hb₀,hb₁,hbne⟩ := hTwoB
      obtain ⟨a,ha,d,hd',a',ha',d',hd'',_,_,hrne⟩ := hTwoR
      obtain ⟨p⟩ := two_colour_rectangle_of_component_witnesses R B A D r hd hA hD hcover
        a₀ a₁ d₀ d₁ ha₀ ha₁ hd₀ hd₁ hb₀ hb₁ hbne ⟨a,ha,a',ha',hrne⟩
      exact Or.inl (p.quantitative (by omega) hR hB)

end MatchingStability


end PermutedModule32

/- Source module: RectangleThirdColour.lean -/
section PermutedModule33

/-!
Forcing the third colour on the two remaining joins of a two-colour rectangle.
Every forbidden extra edge would connect two disjoint complete-join matchings.
Credit: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

theorem rectangle_third_colour
    {V : Type*} [Fintype V] [DecidableEq V] (R B G : SimpleGraph V)
    (X Y Z W : Finset V) (s : ℕ)
    (hXY : Disjoint X Y) (hZW : Disjoint Z W)
    (hSides : Disjoint (X ∪ Y) (Z ∪ W))
    (hRXZ : ∀ x ∈ X, ∀ z ∈ Z, R.Adj x z)
    (hRYW : ∀ y ∈ Y, ∀ w ∈ W, R.Adj y w)
    (hBXW : ∀ x ∈ X, ∀ w ∈ W, B.Adj x w)
    (hBYZ : ∀ y ∈ Y, ∀ z ∈ Z, B.Adj y z)
    (hRsize : s ≤ min X.card Z.card + min Y.card W.card)
    (hBsize : s ≤ min X.card W.card + min Y.card Z.card)
    (hcover : ∀ u v : V, u ≠ v → R.Adj u v ∨ B.Adj u v ∨ G.Adj u v)
    (hnoR : ¬ HasCM R s) (hnoB : ¬ HasCM B s) :
    (∀ x ∈ X, ∀ y ∈ Y, G.Adj x y ∧ ¬ R.Adj x y ∧ ¬ B.Adj x y) ∧
    (∀ z ∈ Z, ∀ w ∈ W, G.Adj z w ∧ ¬ R.Adj z w ∧ ¬ B.Adj z w) := by
  have hXZ : Disjoint X Z := hSides.mono Finset.subset_union_left Finset.subset_union_left
  have hXW : Disjoint X W := hSides.mono Finset.subset_union_left Finset.subset_union_right
  have hYZ : Disjoint Y Z := hSides.mono Finset.subset_union_right Finset.subset_union_left
  have hYW : Disjoint Y W := hSides.mono Finset.subset_union_right Finset.subset_union_right
  have hRedRegions : Disjoint ((X : Set V) ∪ (Z : Set V)) ((Y : Set V) ∪ (W : Set V)) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    rcases hu with hu | hu <;> rcases hu' with hu' | hu'
    · exact Finset.disjoint_left.mp hXY hu hu'
    · exact Finset.disjoint_left.mp hXW hu hu'
    · exact Finset.disjoint_left.mp hYZ hu' hu
    · exact Finset.disjoint_left.mp hZW hu hu'
  have hBlueRegions : Disjoint ((X : Set V) ∪ (W : Set V)) ((Y : Set V) ∪ (Z : Set V)) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    rcases hu with hu | hu <;> rcases hu' with hu' | hu'
    · exact Finset.disjoint_left.mp hXY hu hu'
    · exact Finset.disjoint_left.mp hXZ hu hu'
    · exact Finset.disjoint_left.mp hYW hu' hu
    · exact Finset.disjoint_left.mp hZW hu' hu
  have hNoRed : ∀ u ∈ (X : Set V) ∪ (Z : Set V),
      ∀ v ∈ (Y : Set V) ∪ (W : Set V), ¬ R.Adj u v := by
    intro u hu v hv huv
    obtain ⟨M,hM,hcard,hcon⟩ := HasCM.of_bridged_complete_joins R X Z Y W
      (min X.card Z.card) (min Y.card W.card) hXZ hYW hRedRegions
      (min_le_left _ _) (min_le_right _ _) (min_le_left _ _) (min_le_right _ _)
      hRXZ hRYW u v hu hv huv
    exact hnoR ⟨M,hM,by omega,hcon⟩
  have hNoBlue : ∀ u ∈ (X : Set V) ∪ (W : Set V),
      ∀ v ∈ (Y : Set V) ∪ (Z : Set V), ¬ B.Adj u v := by
    intro u hu v hv huv
    obtain ⟨M,hM,hcard,hcon⟩ := HasCM.of_bridged_complete_joins B X W Y Z
      (min X.card W.card) (min Y.card Z.card) hXW hYZ hBlueRegions
      (min_le_left _ _) (min_le_right _ _) (min_le_left _ _) (min_le_right _ _)
      hBXW hBYZ u v hu hv huv
    exact hnoB ⟨M,hM,by omega,hcon⟩
  constructor
  · intro x hx y hy
    have hr := hNoRed x (Or.inl hx) y (Or.inl hy)
    have hb := hNoBlue x (Or.inl hx) y (Or.inl hy)
    have hne : x ≠ y := fun he => Finset.disjoint_left.mp hXY hx (he.symm ▸ hy)
    exact ⟨((hcover x y hne).resolve_left hr).resolve_left hb,hr,hb⟩
  · intro z hz w hw
    have hr := hNoRed z (Or.inr hz) w (Or.inr hw)
    have hb : ¬ B.Adj z w := fun h => hNoBlue w (Or.inr hw) z (Or.inr hz) h.symm
    have hne : z ≠ w := fun he => Finset.disjoint_left.mp hZW hz (he.symm ▸ hw)
    exact ⟨((hcover z w hne).resolve_left hr).resolve_left hb,hr,hb⟩

theorem rectangle_third_colour_quantitative
    {V : Type*} [Fintype V] [DecidableEq V] (R B G : SimpleGraph V)
    (X Y Z W : Finset V) (m h : ℕ) (hh : 1 ≤ h) (hm : 1000 * h ≤ m)
    (hXY : Disjoint X Y) (hZW : Disjoint Z W)
    (hSides : Disjoint (X ∪ Y) (Z ∪ W))
    (hXlower : m - 9 * h + 1 ≤ X.card)
    (hYlower : m - 9 * h + 1 ≤ Y.card)
    (hZWcard : Z.card + W.card = 2 * (m - 4 * h))
    (hZWorder : Z.card ≤ W.card) (hZlower : 10 * h - 1 ≤ Z.card)
    (hRXZ : ∀ x ∈ X, ∀ z ∈ Z, R.Adj x z)
    (hRYW : ∀ y ∈ Y, ∀ w ∈ W, R.Adj y w)
    (hBXW : ∀ x ∈ X, ∀ w ∈ W, B.Adj x w)
    (hBYZ : ∀ y ∈ Y, ∀ z ∈ Z, B.Adj y z)
    (hcover : ∀ u v : V, u ≠ v → R.Adj u v ∨ B.Adj u v ∨ G.Adj u v)
    (hnoR : ¬ HasCM R (m + h)) (hnoB : ¬ HasCM B (m + h)) :
    (∀ x ∈ X, ∀ y ∈ Y, G.Adj x y ∧ ¬ R.Adj x y ∧ ¬ B.Adj x y) ∧
    (∀ z ∈ Z, ∀ w ∈ W, G.Adj z w ∧ ¬ R.Adj z w ∧ ¬ B.Adj z w) := by
  apply rectangle_third_colour R B G X Y Z W (m + h) hXY hZW hSides
    hRXZ hRYW hBXW hBYZ ?_ ?_ hcover hnoR hnoB <;> omega


end MatchingStability

end PermutedModule33

/- Source module: QuantitativeCompleteClassification.lean -/
section PermutedModule34

/-!
Quantitative finite stability for complete three-multicoloured graphs.
The proof combines independent essential-vertex deletions, the two-colour
bipartite classification, and explicit matching-based cleaning. It preserves
exclusive colours, as required when passing back from a completed reduced
multicolouring. Credit: @fqlx.
-/

open SimpleGraph

namespace MatchingStability

theorem exclusive_join_of_between_missing
    {V : Type*} (R B G : SimpleGraph V) (A D X Y : Finset V)
    (hmissing : ∀ a ∈ A, ∀ d ∈ D, ¬ G.Adj a d)
    (hjoin : ExclusiveJoin (R.between (A : Set V) (D : Set V))
      (B.between (A : Set V) (D : Set V)) X Y) :
    ∀ x ∈ X, ∀ y ∈ Y, R.Adj x y ∧ ¬ B.Adj x y ∧ ¬ G.Adj x y := by
  intro x hx y hy
  obtain ⟨⟨hR, hside⟩, hB⟩ := hjoin x hx y hy
  refine ⟨hR, fun h => hB ⟨h, hside⟩, ?_⟩
  rcases hside with ⟨hxA, hyD⟩ | ⟨hxD, hyA⟩
  · exact hmissing x hxA y hyD
  · exact fun h => hmissing y hyA x hxD h.symm

theorem quantitative_clique_core_of_strip
    {V : Type*} [Fintype V] [DecidableEq V] (c : Fin 3 → SimpleGraph V)
    (σ : Equiv.Perm (Fin 3)) (X Y W : Finset V) (m h : ℕ)
    (hh : 1 ≤ h) (hm : 1000 * h ≤ m)
    (hXY : Disjoint X Y) (hXW : Disjoint X W) (hYW : Disjoint Y W)
    (hXlower : m - 9 * h + 1 ≤ X.card)
    (hYlower : m - 9 * h + 1 ≤ Y.card)
    (hXupper : X.card ≤ m + h - 1)
    (hYupper : Y.card ≤ m + h - 1)
    (hWlower : 2 * (m - 9 * h + 1) ≤ W.card)
    (hred : ExclusiveBetween c (σ 0) X W)
    (hblue : ExclusiveBetween c (σ 1) Y W)
    (hcover : ∀ u v, u ≠ v → ∃ k, (c k).Adj u v)
    (hno : ∀ k, ¬ HasCM (c k) (m + h)) :
    Nonempty (QuantitativeCliqueCore c m h) := by
  obtain ⟨W', hW', hW'card, hclique⟩ := strip_clique_cleanup_quantitative_exclusive
    (c (σ 0)) (c (σ 1)) (c (σ 2)) X Y W m h hh hm hXW hYW
    hXlower hYlower hXupper hYupper hWlower
    (fun x hx w hw => (hred x hx w hw).1)
    (fun y hy w hw => (hblue y hy w hw).1)
    (fun u _ v _ hne => three_color_cover_permuted c σ hcover hne)
    (hno (σ 0)) (hno (σ 1))
  exact ⟨{
    colors := σ
    X := X
    Y := Y
    W := W'
    disjointXY := hXY
    disjointXW := hXW.mono_right hW'
    disjointYW := hYW.mono_right hW'
    lowerX := hXlower
    upperX := hXupper
    lowerY := hYlower
    upperY := hYupper
    lowerW := hW'card
    redXW := fun x hx w hw => hred x hx w (hW' hw)
    blueYW := fun y hy w hw => hblue y hy w (hW' hw)
    greenW := by
      intro u hu v hv hne
      have hadj := hclique hu hv hne
      apply (exclusive_permuted_iff c σ 2 u v).mp
      apply (exclusive_two_iff (fun k => c (σ k)) u v).mpr
      exact ⟨hadj.1, fun h => hadj.2 (Or.inl h), fun h => hadj.2 (Or.inr h)⟩ }⟩

theorem quantitative_complete_three_color_classification
    {V : Type*} [Fintype V] [DecidableEq V] (c : Fin 3 → SimpleGraph V)
    (m h : ℕ) (hh : 1 ≤ h) (hm : 1000 * h ≤ m)
    (hsize : Fintype.card V = 4 * m)
    (hcover : ∀ u v, u ≠ v → ∃ k, (c k).Adj u v)
    (hno : ∀ k, ¬ HasCM (c k) (m + h)) :
    Nonempty (QuantitativeFourBlockCore c m h) ∨
      Nonempty (QuantitativeCliqueCore c m h) := by
  classical
  obtain ⟨i, U, T, hUT, hUcard, hTcard, hMissing⟩ :=
    quantitative_large_missing_cut c m h hh hm hsize hcover hno
  obtain ⟨A, hAU, hAcard⟩ := Finset.exists_subset_card_eq hUcard
  obtain ⟨D, hDT, hDcard⟩ := Finset.exists_subset_card_eq hTcard
  have hAD : Disjoint A D := hUT.mono hAU hDT
  let σ := Equiv.swap i (2 : Fin 3)
  let R := c (σ 0)
  let B := c (σ 1)
  let G := c (σ 2)
  let R' := R.between (A : Set V) (D : Set V)
  let B' := B.between (A : Set V) (D : Set V)
  have hGreen : σ 2 = i := by simp [σ]
  have hGmissing : ∀ a ∈ A, ∀ d ∈ D, ¬ G.Adj a d := by
    intro a ha d hd
    simpa only [G, hGreen] using hMissing a (hAU ha) d (hDT hd)
  have hCover3 : ∀ u v, u ≠ v → R.Adj u v ∨ B.Adj u v ∨ G.Adj u v :=
    fun _ _ hne => three_color_cover_permuted c σ hcover hne
  have hCoverRB : ∀ a ∈ A, ∀ d ∈ D, R'.Adj a d ∨ B'.Adj a d := by
    intro a ha d hd
    have hne : a ≠ d := fun he => Finset.disjoint_left.mp hAD ha (he.symm ▸ hd)
    rcases hCover3 a d hne with hr | hb | hg
    · exact Or.inl ⟨hr, Or.inl ⟨ha, hd⟩⟩
    · exact Or.inr ⟨hb, Or.inl ⟨ha, hd⟩⟩
    · exact (hGmissing a ha d hd hg).elim
  have hADset : Disjoint (A : Set V) (D : Set V) := by simpa using hAD
  have hR'no : ¬ HasCM R' (m + h) := fun h => hno (σ 0) (h.mono R.between_le)
  have hB'no : ¬ HasCM B' (m + h) := fun h => hno (σ 1) (h.mono B.between_le)
  have hLower : 2 * (m - 4 * h) + 1 - (m + h) = m - 9 * h + 1 := by omega
  have hRedTransfer : ∀ X Y, ExclusiveJoin R' B' X Y →
      ExclusiveBetween c (σ 0) X Y := by
    intro X Y hj x hx y hy
    apply (exclusive_permuted_iff c σ 0 x y).mp
    apply (exclusive_zero_iff (fun k => c (σ k)) x y).mpr
    exact exclusive_join_of_between_missing R B G A D X Y hGmissing hj x hx y hy
  have hBlueTransfer : ∀ X Y, ExclusiveJoin B' R' X Y →
      ExclusiveBetween c (σ 1) X Y := by
    intro X Y hj x hx y hy
    apply (exclusive_permuted_iff c σ 1 x y).mp
    apply (exclusive_one_iff (fun k => c (σ k)) x y).mpr
    exact exclusive_join_of_between_missing B R G A D X Y hGmissing hj x hx y hy
  rcases quantitative_bipartite_classification R' B' A D (m - 4 * h) (m + h)
      (by omega) (by omega) (by omega) hAD hAcard hDcard
      (R.between_isBipartiteWith hADset) (B.between_isBipartiteWith hADset)
      hCoverRB hR'no hB'no with hrect | hstrip
  · obtain ⟨p⟩ := hrect
    have hXlower : m - 9 * h + 1 ≤ p.X.card := by simpa only [hLower] using p.lowerX
    have hYlower : m - 9 * h + 1 ≤ p.Y.card := by simpa only [hLower] using p.lowerY
    have hRXZ := hRedTransfer p.X p.Z p.redXZ
    have hRYW := hRedTransfer p.Y p.W p.redYW
    have hBXW := hBlueTransfer p.X p.W p.blueXW
    have hBYZ := hBlueTransfer p.Y p.Z p.blueYZ
    by_cases hZlarge : 10 * h - 1 ≤ p.Z.card
    · obtain ⟨hGreenXY, hGreenZW⟩ := rectangle_third_colour_quantitative R B G
        p.X p.Y p.Z p.W m h hh hm p.disjointXY p.disjointZW p.disjointSides
        hXlower hYlower p.cardZW p.orderedZW hZlarge
        (fun x hx z hz => (hRXZ x hx z hz).1)
        (fun y hy w hw => (hRYW y hy w hw).1)
        (fun x hx w hw => (hBXW x hx w hw).1)
        (fun y hy z hz => (hBYZ y hy z hz).1)
        hCover3 (hno (σ 0)) (hno (σ 1))
      exact Or.inl ⟨{
        colors := σ
        X := p.X
        Y := p.Y
        Z := p.Z
        W := p.W
        disjointXY := p.disjointXY
        disjointZW := p.disjointZW
        disjointSides := p.disjointSides
        cardXY := p.cardXY
        cardZW := p.cardZW
        lowerX := hXlower
        upperX := p.upperX
        lowerY := hYlower
        upperY := p.upperY
        lowerZ := hZlarge
        orderedZW := p.orderedZW
        redXZ := hRXZ
        redYW := hRYW
        blueXW := hBXW
        blueYZ := hBYZ
        greenXY := by
          intro x hx y hy
          apply (exclusive_permuted_iff c σ 2 x y).mp
          exact (exclusive_two_iff (fun k => c (σ k)) x y).mpr (hGreenXY x hx y hy)
        greenZW := by
          intro z hz w hw
          apply (exclusive_permuted_iff c σ 2 z w).mp
          exact (exclusive_two_iff (fun k => c (σ k)) z w).mpr (hGreenZW z hz w hw) }⟩
    · have hWlower : 2 * (m - 9 * h + 1) ≤ p.W.card := by
        have hsum := p.cardZW
        omega
      exact Or.inr (quantitative_clique_core_of_strip c σ p.Y p.X p.W m h hh hm
        p.disjointXY.symm
        (p.disjointSides.mono Finset.subset_union_right Finset.subset_union_right)
        (p.disjointSides.mono Finset.subset_union_left Finset.subset_union_right)
        hYlower hXlower p.upperY p.upperX hWlower hRYW hBXW hcover hno)
  · obtain ⟨p⟩ := hstrip
    have hXlower : m - 9 * h + 1 ≤ p.X.card := by simpa only [hLower] using p.lowerX
    have hYlower : m - 9 * h + 1 ≤ p.Y.card := by simpa only [hLower] using p.lowerY
    have hWlower : 2 * (m - 9 * h + 1) ≤ p.W.card := by simpa only [hLower] using p.lowerW
    exact Or.inr (quantitative_clique_core_of_strip c σ p.X p.Y p.W m h hh hm
      p.disjointXY p.disjointXW p.disjointYW hXlower hYlower p.upperX p.upperY
      hWlower (hRedTransfer p.X p.W p.redXW) (hBlueTransfer p.Y p.W p.blueYW) hcover hno)


end MatchingStability

end PermutedModule34

/- Source module: FiniteExtremalStability.lean -/
section PermutedModule35

/-!
Quantitative finite three-colour stability with explicit exclusive-density
bounds and colour permutations. This completes the finite-regime conversion;
regularity and the cycle embedding are separate host-graph steps.
Credit: @fqlx.
-/

open SimpleGraph Finset

namespace MatchingStability

theorem QuantitativeFourBlockCore.toEC2_of_smallZ
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : Fin 3 → SimpleGraph V} {m h : ℕ} {α μ δ : ℝ}
    (p : QuantitativeFourBlockCore c m h) (a : RegimeParameters m h α μ δ)
    (hV : Fintype.card V = 4 * m)
    (hcover : ∀ u v : V, u ≠ v → ∃ k, (c k).Adj u v)
    (hno : ∀ k, ¬ HasCM (c k) (m + h))
    (hZ : (p.Z.card : ℝ) ≤ α / 100 * m) : FiniteEC2 c m α := by
  obtain ⟨W',hW'W,hsize,hclique⟩ := p.smallZ_exclusive_clique a hcover hno hZ
  exact finite_ec2_of_weak_clique_core c a hV p.colors p.Y p.X W'
    p.disjointXY.symm
    ((p.disjointSides.mono subset_union_right subset_union_right).mono_right hW'W)
    ((p.disjointSides.mono subset_union_left subset_union_right).mono_right hW'W)
    p.lowerY p.lowerX hsize
    (fun y hy w hw => p.redYW y hy w (hW'W hw))
    (fun x hx w hw => p.blueXW x hx w (hW'W hw)) hclique

theorem quantitative_finite_stability_of_noCM
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) {m h : ℕ} {α μ δ : ℝ}
    (a : RegimeParameters m h α μ δ) (hV : Fintype.card V = 4 * m)
    (hcover : ∀ u v : V, u ≠ v → ∃ k, (c k).Adj u v)
    (hno : ∀ k, ¬ HasCM (c k) (m + h)) :
    FiniteEC1 c m α ∨ FiniteEC2 c m α ∨ StrongFiniteEC3 c m μ δ := by
  classical
  rcases quantitative_complete_three_color_classification c m h a.positiveH a.largeM hV
      hcover hno with hp | hq
  · obtain ⟨p⟩ := hp
    by_cases hZlarge : (1 - α / 100) * m ≤ (p.Z.card : ℝ)
    · exact Or.inl (p.toEC1 a hV hZlarge)
    · by_cases hZsmall : (p.Z.card : ℝ) ≤ α / 100 * m
      · exact Or.inr (Or.inl (p.toEC2_of_smallZ a hV hcover hno hZsmall))
      · exact Or.inr (Or.inr (p.toStrongEC3 a hV (le_of_not_ge hZsmall)
          (le_of_not_ge hZlarge)))
  · obtain ⟨q⟩ := hq
    exact Or.inr (Or.inl (q.toEC2 a hV))

/-- Every complete three-multicolouring has the specified large connected
matching or one of the three exclusive extremal partitions. -/
theorem quantitative_finite_stability
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) {m h : ℕ} {α μ δ : ℝ}
    (a : RegimeParameters m h α μ δ) (hV : Fintype.card V = 4 * m)
    (hcover : ∀ u v : V, u ≠ v → ∃ k, (c k).Adj u v) :
    (∃ k, HasCM (c k) (m + h)) ∨
      FiniteEC1 c m α ∨ FiniteEC2 c m α ∨ StrongFiniteEC3 c m μ δ := by
  classical
  by_cases hCM : ∃ k, HasCM (c k) (m + h)
  · exact Or.inl hCM
  · exact Or.inr (quantitative_finite_stability_of_noCM c a hV hcover
      (fun k hk => hCM ⟨k,hk⟩))


end MatchingStability

end PermutedModule35

/- Source module: StabilityNumerics.lean -/
section PermutedModule36

/-!
Numerical bookkeeping for the regularity/connected-matching argument.
The margin in the matching threshold pays for cluster rounding and for the
small core deletion. Credit: @fqlx.
-/

namespace StabilityNumerics

theorem matching_threshold_embeds
    (N t : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ ≤ 1 / 100)
    (ht : 16 ≤ θ * t) (hN : 4 * (t : ℝ) ≤ θ * N) :
    let s := t / 4 + Nat.ceil (θ * t)
    let w := N / t
    1 ≤ s ∧ (N : ℝ) / 2 ≤ (1 - θ / 4) * (2 * (s : ℝ) * (w : ℝ)) := by
  dsimp only
  have htpos : 0 < t := by
    by_contra h
    have : t = 0 := by omega
    norm_num [this] at ht
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have hsceil : θ * t ≤ (Nat.ceil (θ * t) : ℝ) := Nat.le_ceil _
  have hspos : 1 ≤ t / 4 + Nat.ceil (θ * t) := by
    have : (1 : ℝ) ≤ Nat.ceil (θ * t) := by linarith
    have : 1 ≤ Nat.ceil (θ * t) := by exact_mod_cast this
    omega
  refine ⟨hspos,?_⟩
  have hdiv4 : (t : ℝ) ≤ 4 * ((t / 4 : ℕ) : ℝ) + 3 := by
    have he := Nat.div_add_mod t 4
    have hm := Nat.mod_lt t (by omega : 0 < 4)
    exact_mod_cast (show t ≤ 4 * (t / 4) + 3 by omega)
  have hs : (1 / 2 + θ) * (t : ℝ) ≤
      2 * ((t / 4 + Nat.ceil (θ * t) : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hw : (1 - θ / 4) * (N : ℝ) ≤
      ((N / t : ℕ) : ℝ) * t := by
    have he := Nat.div_add_mod N t
    rw [Nat.mul_comm] at he
    have hm := Nat.mod_lt N htpos
    have hround : (N : ℝ) ≤ ((N / t : ℕ) : ℝ) * t + t := by
      exact_mod_cast (show N ≤ (N / t) * t + t by omega)
    nlinarith
  have hδ : 0 ≤ 1 - θ / 4 := by linarith
  have hcoef : (1 / 2 : ℝ) ≤ (1 - θ / 4) ^ 2 * (1 / 2 + θ) := by
    have hsquare := mul_le_mul_of_nonneg_right hθsmall hθ.le
    nlinarith [sq_nonneg θ, mul_nonneg hθ.le (sq_nonneg θ)]
  have hA := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (N / t) : (0 : ℝ) ≤ _)
  have hB := mul_le_mul_of_nonneg_left hw (show (0 : ℝ) ≤ 1 / 2 + θ by linarith)
  have hAB : (1 / 2 + θ) * ((1 - θ / 4) * (N : ℝ)) ≤
      2 * ((t / 4 + Nat.ceil (θ * t) : ℕ) : ℝ) * ((N / t : ℕ) : ℝ) := by
    nlinarith [hA,hB]
  have hC := mul_le_mul_of_nonneg_left hAB hδ
  have hD := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg N : (0 : ℝ) ≤ _)
  nlinarith [hC,hD]

theorem rounded_core_parameters
    (t m : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ ≤ 1 / 100)
    (ht : 16 ≤ θ * t) (hmle : 4 * m ≤ t)
    (hloss : (t : ℝ) ≤ 4 * m + θ * t) :
    let s := t / 4 + Nat.ceil (θ * t)
    let h := s - m
    s = m + h ∧ 1 ≤ h ∧ (t : ℝ) / 5 ≤ m ∧ (h : ℝ) ≤ 10 * θ * m := by
  dsimp only
  have hmdiv : m ≤ t / 4 := by omega
  have hsceil : θ * t ≤ (Nat.ceil (θ * t) : ℝ) := Nat.le_ceil _
  have hsceil' : (Nat.ceil (θ * t) : ℝ) < θ * t + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hhpos : 1 ≤ Nat.ceil (θ * t) := by
    exact_mod_cast (show (1 : ℝ) ≤ Nat.ceil (θ * t) by linarith)
  have hsge : m ≤ t / 4 + Nat.ceil (θ * t) := by omega
  have he : t / 4 + Nat.ceil (θ * t) =
      m + (t / 4 + Nat.ceil (θ * t) - m) := by omega
  have heR : ((t / 4 : ℕ) : ℝ) + Nat.ceil (θ * t) =
      (m : ℝ) + ((t / 4 + Nat.ceil (θ * t) - m : ℕ) : ℝ) := by
    exact_mod_cast he
  have hdiv : 4 * ((t / 4 : ℕ) : ℝ) ≤ t := by
    exact_mod_cast Nat.mul_div_le t 4
  have hmR : (t : ℝ) / 5 ≤ m := by
    have hmul := mul_le_mul_of_nonneg_right hθsmall (Nat.cast_nonneg t : (0 : ℝ) ≤ _)
    nlinarith
  have hhR : ((t / 4 + Nat.ceil (θ * t) - m : ℕ) : ℝ) ≤ 2 * θ * t := by
    nlinarith
  refine ⟨he,by omega,hmR,?_⟩
  have hbound := mul_le_mul_of_nonneg_left hmR hθ.le
  nlinarith

end StabilityNumerics


end PermutedModule36

/- Source module: TransferParameters.lean -/
section PermutedModule37

/-!
One compatible choice of constants for the finite stability, regularity,
host-density and block-size transfers. Credit: @fqlx.
-/

namespace MatchingStability

structure TransferParameters (α μ δ θ d : ℝ) : Prop where
  alpha_pos : 0 < α
  alpha_small : α ≤ 1
  mu_pos : 0 < μ
  mu_small : μ ≤ α / 100000
  delta_pos : 0 < δ
  theta_pos : 0 < θ
  theta_small : θ ≤ 1 / 10000
  theta_mu : 1000000 * θ ≤ μ
  theta_alpha : 100000000 * θ ≤ α
  theta_delta : 100000000 * θ ≤ δ * μ ^ 2
  density_alpha : 1000 * θ ≤ α * μ ^ 2
  density_delta : 1000 * θ ≤ δ * μ ^ 2
  d_pos : 0 < d
  d_alpha : d ≤ α / 100
  d_delta : d ≤ δ / 100

theorem exists_transfer_parameters (α μ δ : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hμ : 0 < μ)
    (hμsmall : μ ≤ α / 100000) (hδ : 0 < δ) :
    ∃ θ d : ℝ, TransferParameters α μ δ θ d := by
  let θ := min (1 / 1000000 : ℝ)
    (min (μ / 1000000) (min (α * μ ^ 2 / 100000000) (δ * μ ^ 2 / 100000000)))
  let d := min α δ / 100
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have ht₀ : θ ≤ 1 / 1000000 := min_le_left _ _
  have htμ : θ ≤ μ / 1000000 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htα : θ ≤ α * μ ^ 2 / 100000000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htδ : θ ≤ δ * μ ^ 2 / 100000000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hμ₁ : μ ≤ 1 := by linarith
  have hμsq : μ ^ 2 ≤ 1 := by nlinarith
  have hαprod := mul_le_mul_of_nonneg_left hμsq hα.le
  have hd : 0 < d := div_pos (lt_min hα hδ) (by norm_num)
  have hdα : d ≤ α / 100 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hdδ : d ≤ δ / 100 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  refine ⟨θ,d,hα,hα₁,hμ,hμsmall,hδ,hθ,?_,?_,?_,?_,?_,?_,hd,hdα,hdδ⟩ <;> nlinarith

namespace TransferParameters

variable {α μ δ θ d : ℝ} (p : TransferParameters α μ δ θ d)

include p

theorem mu_le_one : μ ≤ 1 := by
  have := p.mu_small
  have := p.alpha_small
  linarith

theorem d_le_third : d ≤ 1 / 3 := by
  have := p.d_alpha
  have := p.alpha_small
  linarith

theorem regime {m h : ℕ} (hh : 1 ≤ h) (hm : 1000 * h ≤ m)
    (hsmall : (h : ℝ) ≤ 10 * θ * m) :
    RegimeParameters m h (α / 100) μ (δ / 100) := by
  have hα := p.alpha_pos
  have hδ := p.delta_pos
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have htα := mul_le_mul_of_nonneg_right p.theta_alpha hm0
  have htμ := mul_le_mul_of_nonneg_right p.theta_mu hm0
  have htδ := mul_le_mul_of_nonneg_right p.theta_delta hm0
  have hθm := mul_nonneg p.theta_pos.le hm0
  refine ⟨hh,hm,by positivity,?_,p.mu_pos,?_,by positivity,?_,?_,?_⟩
  · have := p.alpha_small
    linarith
  · have := p.mu_small
    linarith
  · nlinarith
  · nlinarith
  · nlinarith

theorem balanced_minimum {K : Type*} (T : Fin 4 → Finset K) (m : ℕ)
    (hs : BalancedBlockSizes T m (α / 100)) :
    ∀ i, μ * m ≤ ((T i).card : ℝ) := by
  intro i
  have hsum : μ ≤ 1 - α / 100 := by
    have := p.mu_small
    have := p.alpha_small
    linarith
  exact (mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg m)).trans (hs i)

theorem strong_ec3_minimum {K : Type*} (T : Fin 4 → Finset K) (m : ℕ)
    (hs : StrongEC3BlockSizes T m μ) :
    ∀ i, μ * m ≤ ((T i).card : ℝ) := by
  have hsum : μ ≤ 1 - 7 / 10 * μ := by
    have := p.mu_small
    have := p.alpha_small
    linarith
  have hsmall := (mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg m)).trans hs.1
  have hD : μ * m ≤ ((T 3).card : ℝ) := by
    have hh := hs.2.1
    have hn := mul_nonneg p.mu_pos.le (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
    linarith
  intro i
  fin_cases i
  · exact hsmall.trans (min_le_left _ _)
  · exact hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  · exact hD

end TransferParameters

end MatchingStability


end PermutedModule37

/- Source module: HostReducedData.lean -/
section PermutedModule38

/-!
The checked finite information passed from regularity and completion to the
host transfer and absorption steps. Credit: @fqlx.
-/

open Finset SimpleGraph

namespace MatchingStability

def HostDensities {V : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (σ : Equiv.Perm (Fin 3)) (U : Fin 4 → Finset V) (β : ℝ)
    (J : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) : Prop :=
  ∀ k S T, (k,S,T) ∈ J →
    (1 - β) * ((S.biUnion U).card : ℝ) * (T.biUnion U).card ≤
      ∑ x ∈ S.biUnion U, (((T.biUnion U).filter ((c (σ k)).Adj x)).card : ℝ)

def HostEC1 (M : ℕ) (c : Fin 3 → SimpleGraph (Fin (4 * M)))
    [∀ k, DecidableRel (c k).Adj] (α : ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (U : Fin 4 → Finset (Fin (4 * M))),
    BlockPartition U ∧ BalancedBlockSizes U M α ∧ HostDensities c σ U α EC1Joins

def HostEC2 (M : ℕ) (c : Fin 3 → SimpleGraph (Fin (4 * M)))
    [∀ k, DecidableRel (c k).Adj] (α : ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (U : Fin 4 → Finset (Fin (4 * M))),
    BlockPartition U ∧ BalancedBlockSizes U M α ∧ HostDensities c σ U α EC2Joins

def HostEC3 (M : ℕ) (c : Fin 3 → SimpleGraph (Fin (4 * M)))
    [∀ k, DecidableRel (c k).Adj] (μ δ : ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (U : Fin 4 → Finset (Fin (4 * M))),
    BlockPartition U ∧ EC3BlockSizes U M μ ∧ HostDensities c σ U δ EC1Joins

structure HostReducedData (M : ℕ) (c : Fin 3 → SimpleGraph (Fin (4 * M)))
    [∀ k, DecidableRel (c k).Adj] (α μ δ θ d : ℝ) where
  t : ℕ
  t_pos : 1 ≤ t
  w : ℕ
  w_pos : 1 ≤ w
  epsilon : ℝ
  parts : Fin t → Finset (Fin (4 * M))
  parts_disjoint : Pairwise (fun i j => Disjoint (parts i) (parts j))
  parts_cover : univ.biUnion parts = univ
  parts_size : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ w + 1
  parts_nonempty : ∀ i, (parts i).Nonempty
  weight_bound : w * t ≤ 4 * M
  host_rounding : 4 * (t : ℝ) ≤ θ * (4 * M)
  irregular : Finset (Fin t × Fin t)
  irregular_card : (irregular.card : ℝ) ≤ θ * (t : ℝ) ^ 2
  regular : ∀ u v, u ≠ v → (u,v) ∉ irregular →
    ∀ k, (c k).IsUniform (2 * epsilon) (parts u) (parts v)
  m : ℕ
  m_lower : (t : ℝ) / 5 ≤ m
  core_embedding : Fin (4 * m) ↪ Fin t
  core_colors : Fin 3 → SimpleGraph (Fin (4 * m))
  core_loss : ((t - 4 * m : ℕ) : ℝ) ≤ θ * t
  preserves : ∀ k a b,
    (ReducedMulticoloring.graph c parts (2 * epsilon) d k).Adj
      (core_embedding a) (core_embedding b) → (core_colors k).Adj a b
  alternatives : FiniteEC1 core_colors m (α / 100) ∨
    FiniteEC2 core_colors m (α / 100) ∨ StrongFiniteEC3 core_colors m μ (δ / 100)

end MatchingStability

end PermutedModule38

/- Source module: MatchingInduceSupport.lean -/
section PermutedModule39

open SimpleGraph Set

namespace MatchingStability

/-- Restrict a matching to a vertex set containing all its vertices, without
changing the number of covered vertices. -/
theorem matching_induce_of_verts_subset
    {V : Type*} (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (S : Set V) (hMS : M.verts ⊆ S) :
    ∃ N : (G.induce S).Subgraph, N.IsMatching ∧ N.verts.ncard=M.verts.ncard := by
  let N : (G.induce S).Subgraph := {
    verts := Subtype.val ⁻¹' M.verts
    Adj := fun u v => M.Adj u.val v.val
    adj_sub := fun h => M.adj_sub h
    edge_vert := fun h => M.edge_vert h
    symm.symm := fun _ _ h => h.symm }
  refine ⟨N,?_,?_⟩
  · intro v hv
    obtain ⟨w,hvw,huniq⟩ := hM hv
    refine ⟨⟨w,hMS (M.edge_vert hvw.symm)⟩,hvw,?_⟩
    intro z hz
    apply Subtype.ext
    exact huniq z hz
  · apply Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
    intro v hv
    exact ⟨⟨v,hMS hv⟩,rfl⟩

theorem not_hasCM_iff_component_bounds
    {V : Type*} [Finite V] (G : SimpleGraph V) (s : ℕ) (hs : 1 ≤ s) :
    ¬ HasCM G s ↔ ∀ C : G.ConnectedComponent,
      ∀ M : C.toSimpleGraph.Subgraph, M.IsMatching → M.verts.ncard < 2*s := by
  constructor
  · exact fun h C M hM => component_matching_bound s h C M hM
  · intro h
    rintro ⟨M,hM,hsize,hcon⟩
    have hpos : 0< M.verts.ncard := by omega
    obtain ⟨v,hv⟩ := Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hpos)
    let C := G.connectedComponentMk v
    have hMC : M.verts ⊆ C.supp := by
      intro u hu
      exact ConnectedComponent.sound (hcon u hu v hv)
    obtain ⟨N,hN,hcard⟩ := matching_induce_of_verts_subset G M hM C.supp hMC
    have hbound := h C N hN
    rw [hcard] at hbound
    omega

end MatchingStability


end PermutedModule39

/- Source module: ConnectedMatchingModify.lean -/
section PermutedModule40

open SimpleGraph Set

namespace MatchingStability

theorem reachable_mem_of_closed
    {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hclosed : ∀ u v, u ∈ S → G.Adj u v → v ∈ S)
    {u v : V} (h : G.Reachable u v) (hu : u ∈ S) : v ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | @cons u w v huw p ih => exact ih (hclosed u w hu huw)

theorem reachable_outside_modification
    {V : Type*} (G H : SimpleGraph V) (S : Set V)
    (hclosed : ∀ u v, u ∈ S → G.Adj u v → v ∈ S)
    (hchange : ∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ S ∧ v ∈ S))
    {u v : V} (h : H.Reachable u v) (hu : u ∉ S) : G.Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.rfl
  | @cons u w v huw p ih =>
    have hG : G.Adj u w := (hchange u w huw).resolve_right (fun hw => hu hw.1)
    have hw : w ∉ S := fun hw => hu (hclosed w u hw hG.symm)
    exact hG.reachable.trans (ih hw)

/-- Adding arbitrary edges inside a closed set of fewer than `2s` vertices
cannot create a connected `s`-matching. -/
theorem no_hasCM_of_small_closed_modification
    {V : Type*} [Finite V] (G H : SimpleGraph V) (s : ℕ) (S : Set V)
    (hno : ¬ HasCM G s) (hsmall : S.ncard < 2*s)
    (hclosed : ∀ u v, u ∈ S → G.Adj u v → v ∈ S)
    (hchange : ∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ S ∧ v ∈ S)) :
    ¬ HasCM H s := by
  classical
  rintro ⟨M,hM,hsize,hcon⟩
  by_cases hin : ∃ u ∈ M.verts, u ∈ S
  · obtain ⟨u,hu,huS⟩ := hin
    have hclosedH : ∀ x y, x ∈ S → H.Adj x y → y ∈ S := by
      intro x y hx hxy
      rcases hchange x y hxy with h | h
      · exact hclosed x y hx h
      · exact h.2
    have hMS : M.verts ⊆ S := fun v hv =>
      reachable_mem_of_closed H S hclosedH (hcon u hu v hv) huS
    have hb := Set.ncard_le_ncard hMS
    omega
  · have hout : ∀ u ∈ M.verts, u ∉ S := by simpa only [not_exists, not_and] using hin
    let N : G.Subgraph := {
      verts := M.verts
      Adj := M.Adj
      adj_sub := fun {u v} huv => (hchange u v (M.adj_sub huv)).resolve_right
        (fun h => hout u (M.edge_vert huv) h.1)
      edge_vert := M.edge_vert
      symm.symm := fun _ _ h => h.symm }
    apply hno
    refine ⟨N,hM,hsize,?_⟩
    exact fun u hu v hv =>
      reachable_outside_modification G H S hclosed hchange (hcon u hu v hv) (hout u hu)

def fillInside {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∨ (u ≠ v ∧ u ∈ S ∧ v ∈ S)
  symm.symm := by
    intro u v h
    rcases h with h | ⟨hne,hu,hv⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne.symm,hv,hu⟩
  loopless.irrefl := by
    intro v h
    rcases h with h | h
    · exact G.irrefl h
    · exact h.1 rfl

theorem le_fillInside {V : Type*} (G : SimpleGraph V) (S : Set V) :
    G ≤ fillInside G S := fun _ _ h => Or.inl h

/-- In a maximal graph without a connected `s`-matching, two different
components cannot both have fewer than `s` vertices. -/
theorem small_components_unique
    {V : Type*} [Finite V] (G : SimpleGraph V) (s : ℕ)
    (hno : ¬ HasCM G s)
    (hmax : ∀ H : SimpleGraph V, G ≤ H → ¬ HasCM H s → H = G)
    (C D : G.ConnectedComponent)
    (hC : C.supp.ncard < s) (hD : D.supp.ncard < s) : C = D := by
  classical
  by_contra hCD
  let S := C.supp ∪ D.supp
  have hs : S.ncard < 2*s := by
    have hh := Set.ncard_union_le C.supp D.supp
    change (C.supp ∪ D.supp).ncard < 2*s
    omega
  have hclosed : ∀ u v, u ∈ S → G.Adj u v → v ∈ S := by
    intro u v hu huv
    rcases hu with hu | hu
    · exact Or.inl ((C.mem_supp_congr_adj huv).mp hu)
    · exact Or.inr ((D.mem_supp_congr_adj huv).mp hu)
  have hHno : ¬ HasCM (fillInside G S) s :=
    no_hasCM_of_small_closed_modification G (fillInside G S) s S hno hs hclosed
      (fun _ _ h => h.elim Or.inl (fun h => Or.inr h.2))
  have hH := hmax (fillInside G S) (le_fillInside G S) hHno
  obtain ⟨u,hu⟩ := C.nonempty_supp
  obtain ⟨v,hv⟩ := D.nonempty_supp
  have hne : u ≠ v := by
    intro he
    subst v
    exact hCD (hu.symm.trans hv)
  have hadj : (fillInside G S).Adj u v := Or.inr ⟨hne,Or.inl hu,Or.inr hv⟩
  rw [hH] at hadj
  exact hCD (hu.symm.trans ((ConnectedComponent.sound hadj.reachable).trans hv))

end MatchingStability


end PermutedModule40

/- Source module: ConnectedMatchingSaturated.lean -/
section PermutedModule41

/-!
Componentwise saturation for a graph maximal without a connected matching.
The ordinary matching star theorem is proved in UniversalMatchingStar from
Mathlib's Tutte theorem. New connecting proofs: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

/-- A modification inside a closed vertex set preserves the connected
matching bound if its induced graph preserves the ordinary matching bound. -/
theorem no_hasCM_of_closed_modification
    {V : Type*} [Finite V] (G H : SimpleGraph V) (s : ℕ) (S : Set V)
    (hno : ¬ HasCM G s)
    (hclosed : ∀ u v, u ∈ S → G.Adj u v → v ∈ S)
    (hchange : ∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ S ∧ v ∈ S))
    (hinside : ∀ M : (H.induce S).Subgraph,
      M.IsMatching → M.verts.ncard < 2*s) :
    ¬ HasCM H s := by
  classical
  rintro ⟨M,hM,hsize,hcon⟩
  by_cases hin : ∃ u ∈ M.verts, u ∈ S
  · obtain ⟨u,hu,huS⟩ := hin
    have hclosedH : ∀ x y, x ∈ S → H.Adj x y → y ∈ S := by
      intro x y hx hxy
      rcases hchange x y hxy with h | h
      · exact hclosed x y hx h
      · exact h.2
    have hMS : M.verts ⊆ S := fun v hv =>
      reachable_mem_of_closed H S hclosedH (hcon u hu v hv) huS
    obtain ⟨N,hN,hcard⟩ := matching_induce_of_verts_subset H M hM S hMS
    have hbound := hinside N hN
    rw [hcard] at hbound
    omega
  · have hout : ∀ u ∈ M.verts, u ∉ S := by
      simpa only [not_exists, not_and] using hin
    let N : G.Subgraph := {
      verts := M.verts
      Adj := M.Adj
      adj_sub := fun {u v} huv => (hchange u v (M.adj_sub huv)).resolve_right
        (fun h => hout u (M.edge_vert huv) h.1)
      edge_vert := M.edge_vert
      symm.symm := fun _ _ h => h.symm }
    apply hno
    refine ⟨N,hM,hsize,?_⟩
    exact fun u hu v hv =>
      reachable_outside_modification G H S hclosed hchange
        (hcon u hu v hv) (hout u hu)

/-- The graph induced by a component of a maximal connected-matching-free
graph is maximal with the corresponding ordinary matching bound. -/
theorem component_maximal_matching_free
    {V : Type*} [Finite V] (G : SimpleGraph V) (s : ℕ)
    (hno : ¬ HasCM G s)
    (hmax : ∀ H : SimpleGraph V, G ≤ H → ¬ HasCM H s → H = G)
    (C : G.ConnectedComponent) (F : SimpleGraph C)
    (hle : C.toSimpleGraph ≤ F)
    (hfree : ∀ M : F.Subgraph, M.IsMatching → M.verts.ncard < 2*s) :
    F = C.toSimpleGraph := by
  classical
  let H := G ⊔ F.spanningCoe
  have hGH : G ≤ H := le_sup_left
  have hind : H.induce C.supp = F := by
    ext x y
    change (G.Adj x.val y.val ∨ F.spanningCoe.Adj x.val y.val) ↔ F.Adj x y
    constructor
    · rintro (h | h)
      · exact hle h
      · exact (SimpleGraph.map_adj_apply (f := Function.Embedding.subtype C.supp)).mp h
    · intro h
      exact Or.inr ((SimpleGraph.map_adj_apply (f := Function.Embedding.subtype C.supp)).mpr h)
  have hHno : ¬ HasCM H s := by
    apply no_hasCM_of_closed_modification G H s C.supp hno
    · exact fun u v hu huv => (C.mem_supp_congr_adj huv).mp hu
    · intro u v huv
      rcases huv with h | h
      · exact Or.inl h
      · exact Or.inr ⟨Subgraph.mem_of_adj_spanningCoe F h,
          Subgraph.mem_of_adj_spanningCoe F h.symm⟩
    · rw [hind]
      exact hfree
  have hHG := hmax H hGH hHno
  rw [hHG] at hind
  exact hind.symm

theorem component_matching_saturated
    {V : Type*} [Finite V] (G : SimpleGraph V) (s : ℕ)
    (hno : ¬ HasCM G s)
    (hmax : ∀ H : SimpleGraph V, G ≤ H → ¬ HasCM H s → H = G)
    (C : G.ConnectedComponent) (F : SimpleGraph C) (hlt : C.toSimpleGraph < F) :
    ∃ M : F.Subgraph, M.IsMatching ∧ 2*s ≤ M.verts.ncard := by
  by_contra! hn
  exact hlt.ne (component_maximal_matching_free G s hno hmax C F hlt.le hn).symm

/-- Every component has universal head vertices and clique tail components,
including components too small to contain the forbidden matching. -/
theorem component_matching_star
    {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ)
    (hno : ¬ HasCM G s)
    (hmax : ∀ H : SimpleGraph V, G ≤ H → ¬ HasCM H s → H = G)
    (C : G.ConnectedComponent) :
    ∃ A : Set C, A ⊆ C.toSimpleGraph.universalVerts ∧
      ∀ D : ((⊤ : C.toSimpleGraph.Subgraph).deleteVerts A).coe.ConnectedComponent,
        ((⊤ : C.toSimpleGraph.Subgraph).deleteVerts A).coe.IsClique D.supp := by
  classical
  by_cases hsize : 2*s ≤ Fintype.card C
  · exact maximal_matching_free_star C.toSimpleGraph s hsize
      (component_matching_bound s hno C)
      (component_matching_saturated G s hno hmax C)
  · have htop : C.toSimpleGraph = ⊤ := by
      symm
      apply component_maximal_matching_free G s hno hmax C ⊤ le_top
      intro M _
      have hcard := Set.ncard_le_card M.verts
      simp only [Nat.card_eq_fintype_card] at hcard
      omega
    refine ⟨Set.univ,?_,?_⟩
    · intro x _ y hxy
      simpa only [htop,SimpleGraph.top_adj] using hxy
    · intro D x _ y _ _
      exact (x.property.2 (Set.mem_univ _)).elim

end MatchingStability


end PermutedModule41

/- Source module: MatchingStarLabels.lean -/
section PermutedModule42

/-!
Finite labels for a graph with universal head vertices and clique tails.
Tail labels are representatives from the original vertex type; their number
is unrestricted. New proof: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

noncomputable def starLeafLabel {V : Type*} (G : SimpleGraph V) (A : Set V)
    (v : V) : Option V := by
  classical
  exact if hv : v ∈ A then none else
    some ((((⊤ : G.Subgraph).deleteVerts A).coe.connectedComponentMk
      ⟨v,⟨by trivial,hv⟩⟩).out.val)

theorem star_leaf_form
    {V : Type*} (G : SimpleGraph V) (A : Set V)
    (hA : A ⊆ G.universalVerts)
    (hclique : ∀ C : ((⊤ : G.Subgraph).deleteVerts A).coe.ConnectedComponent,
      ((⊤ : G.Subgraph).deleteVerts A).coe.IsClique C.supp) :
    ∀ u v, G.Adj u v ↔ u ≠ v ∧
      (u ∈ A ∨ v ∈ A ∨ starLeafLabel G A u = starLeafLabel G A v) := by
  classical
  let K := ((⊤ : G.Subgraph).deleteVerts A).coe
  intro u v
  constructor
  · intro huv
    refine ⟨huv.ne,?_⟩
    by_cases hu : u ∈ A
    · exact Or.inl hu
    by_cases hv : v ∈ A
    · exact Or.inr (Or.inl hv)
    right
    right
    let x : ((⊤ : G.Subgraph).deleteVerts A).verts := ⟨u,⟨by trivial,hu⟩⟩
    let y : ((⊤ : G.Subgraph).deleteVerts A).verts := ⟨v,⟨by trivial,hv⟩⟩
    have hxy : K.Adj x y :=
      Subgraph.deleteVerts_adj.mpr ⟨by trivial,hu,by trivial,hv,huv⟩
    have hc := ConnectedComponent.sound hxy.reachable
    simpa only [starLeafLabel,dif_neg hu,dif_neg hv] using
      congrArg (fun C : K.ConnectedComponent => some C.out.val) hc
  · rintro ⟨hne,hhead | hhead | hleaf⟩
    · exact hA hhead hne
    · exact (hA hhead hne.symm).symm
    · by_cases hu : u ∈ A
      · exact hA hu hne
      by_cases hv : v ∈ A
      · exact (hA hv hne.symm).symm
      let x : ((⊤ : G.Subgraph).deleteVerts A).verts := ⟨u,⟨by trivial,hu⟩⟩
      let y : ((⊤ : G.Subgraph).deleteVerts A).verts := ⟨v,⟨by trivial,hv⟩⟩
      have hval : (K.connectedComponentMk x).out.val =
          (K.connectedComponentMk y).out.val := by
        apply Option.some.inj
        simpa only [starLeafLabel,dif_neg hu,dif_neg hv] using hleaf
      have hout : (K.connectedComponentMk x).out = (K.connectedComponentMk y).out :=
        Subtype.ext hval
      have hc : K.connectedComponentMk x = K.connectedComponentMk y := by
        calc
          K.connectedComponentMk x = K.connectedComponentMk (K.connectedComponentMk x).out :=
            (K.connectedComponentMk x).out_eq.symm
          _ = K.connectedComponentMk (K.connectedComponentMk y).out := congrArg _ hout
          _ = K.connectedComponentMk y := (K.connectedComponentMk y).out_eq
      have hxy : K.Adj x y := hclique (K.connectedComponentMk x) rfl hc.symm
        (fun he => hne (congrArg Subtype.val he))
      exact Subgraph.coe_adj_sub _ _ _ hxy

end MatchingStability


end PermutedModule42

/- Source module: ConnectedMatchingStarLabels.lean -/
section PermutedModule43

/-!
Finite vertex labels for saturated connected-matching-free graphs.  Component
labels are the actual connected components, while every tail label is an
optional original vertex. New proof: @fqlx.
-/

open SimpleGraph Set

namespace MatchingStability

theorem component_star_representation
    {V : Type*} (G : SimpleGraph V)
    (hstar : ∀ C : G.ConnectedComponent,
      ∃ A : Set C, A ⊆ C.toSimpleGraph.universalVerts ∧
        ∀ D : ((⊤ : C.toSimpleGraph.Subgraph).deleteVerts A).coe.ConnectedComponent,
          ((⊤ : C.toSimpleGraph.Subgraph).deleteVerts A).coe.IsClique D.supp) :
    ∃ head : V → Prop, ∃ leaf : V → Option V,
      ∀ u v, G.Adj u v ↔ u ≠ v ∧ G.connectedComponentMk u = G.connectedComponentMk v ∧
        (head u ∨ head v ∨ leaf u = leaf v) := by
  classical
  choose A hA hclique using hstar
  let head : V → Prop := fun u =>
    (⟨u,rfl⟩ : G.connectedComponentMk u) ∈ A (G.connectedComponentMk u)
  let leaf : V → Option V := fun u =>
    (starLeafLabel (G.connectedComponentMk u).toSimpleGraph
      (A (G.connectedComponentMk u)) ⟨u,rfl⟩).map Subtype.val
  have head_component (C : G.ConnectedComponent) (u : V) (hu : u ∈ C.supp) :
      head u ↔ (⟨u,hu⟩ : C) ∈ A C := by
    change G.connectedComponentMk u = C at hu
    subst C
    rfl
  have leaf_component (C : G.ConnectedComponent) (u : V) (hu : u ∈ C.supp) :
      leaf u = (starLeafLabel C.toSimpleGraph (A C) ⟨u,hu⟩).map Subtype.val := by
    change G.connectedComponentMk u = C at hu
    subst C
    rfl
  have component_form (C : G.ConnectedComponent) (u v : V)
      (hu : u ∈ C.supp) (hv : v ∈ C.supp) :
      G.Adj u v ↔ u ≠ v ∧ (head u ∨ head v ∨ leaf u = leaf v) := by
    have hleaf : leaf u = leaf v ↔
        starLeafLabel C.toSimpleGraph (A C) ⟨u,hu⟩ =
          starLeafLabel C.toSimpleGraph (A C) ⟨v,hv⟩ := by
      rw [leaf_component C u hu,leaf_component C v hv]
      exact (Option.map_injective Subtype.val_injective).eq_iff
    have h := star_leaf_form C.toSimpleGraph (A C) (hA C) (hclique C)
      ⟨u,hu⟩ ⟨v,hv⟩
    simpa only [head_component C u hu,head_component C v hv,hleaf,
      ne_eq,Subtype.mk.injEq,C.toSimpleGraph_adj hu hv] using h
  refine ⟨head,leaf,?_⟩
  intro u v
  constructor
  · intro huv
    have hc := ConnectedComponent.sound huv.reachable
    exact ⟨huv.ne,hc,
      ((component_form (G.connectedComponentMk u) u v rfl hc.symm).mp huv).2⟩
  · rintro ⟨hne,hc,hhead⟩
    exact (component_form (G.connectedComponentMk u) u v rfl hc.symm).mpr ⟨hne,hhead⟩

/-- A finite saturated graph without a connected s-matching has the exact
head-and-tail adjacency form needed by the completion argument. -/
theorem maximal_no_connected_matching_representation
    {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ)
    (hno : ¬ HasCM G s)
    (hmax : ∀ H : SimpleGraph V, G ≤ H → ¬ HasCM H s → H = G) :
    ∃ head : V → Prop, ∃ leaf : V → Option V,
      ∀ u v, G.Adj u v ↔ u ≠ v ∧ G.connectedComponentMk u = G.connectedComponentMk v ∧
        (head u ∨ head v ∨ leaf u = leaf v) :=
  component_star_representation G (component_matching_star G s hno hmax)

end MatchingStability


end PermutedModule43

/- Source module: ConnectedMatchingComponents.lean -/
section PermutedModule44

open SimpleGraph Set Finset
open scoped BigOperators

namespace MatchingStability

/-- A saturated graph with no connected `s`-matching on at most `b*s`
vertices has at most `b+1` components. At most one can be smaller than `s`. -/
theorem component_count_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (s b : ℕ) (hs : 1 ≤ s)
    (hsize : Fintype.card V ≤ b*s) (hno : ¬ HasCM G s)
    (hmax : ∀ H : SimpleGraph V, G ≤ H → ¬ HasCM H s → H = G) :
    Nat.card G.ConnectedComponent ≤ b+1 := by
  classical
  letI := Fintype.ofFinite G.ConnectedComponent
  let L : Finset G.ConnectedComponent := univ.filter (fun C => s ≤ C.supp.ncard)
  let T : Finset G.ConnectedComponent := univ.filter (fun C => C.supp.ncard < s)
  have hT : T.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro C hC D hD
    exact small_components_unique G s hno hmax C D
      (mem_filter.mp hC).2 (mem_filter.mp hD).2
  have hd : (L : Set G.ConnectedComponent).PairwiseDisjoint
      (fun C => C.supp.toFinset) := by
    intro C _ D _ hCD
    exact Set.disjoint_toFinset.mpr (G.pairwise_disjoint_supp_connectedComponent hCD)
  have hsum : (∑ C ∈ L, C.supp.ncard) ≤ Fintype.card V := by
    simp_rw [Set.ncard_eq_toFinset_card']
    rw [← Finset.card_biUnion hd]
    exact card_le_univ _
  have hmul : L.card*s ≤ Fintype.card V := by
    calc
      L.card*s = ∑ _C ∈ L, s := by simp
      _ ≤ ∑ C ∈ L, C.supp.ncard := sum_le_sum (fun C hC => (mem_filter.mp hC).2)
      _ ≤ Fintype.card V := hsum
  have hL : L.card ≤ b := by nlinarith
  have hcover : L ∪ T = Finset.univ := by
    apply Finset.ext
    intro C
    simp only [L,T,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact le_or_gt s C.supp.ncard
  have hbound : Fintype.card G.ConnectedComponent ≤ L.card+T.card := by
    rw [← card_univ,← hcover]
    exact card_union_le ..
  rw [Nat.card_eq_fintype_card]
  omega

/-- Maximality of a multicolouring gives maximality in every single colour. -/
theorem maximal_colour_of_multicolouring
    {V : Type*} (c : Fin 3 → SimpleGraph V) (s : ℕ)
    (hno : ∀ k, ¬ HasCM (c k) s)
    (hmax : ∀ D : Fin 3 → SimpleGraph V, c ≤ D →
      (∀ k, ¬ HasCM (D k) s) → D=c)
    (k : Fin 3) (H : SimpleGraph V) (hle : c k ≤ H) (hH : ¬ HasCM H s) : H=c k := by
  classical
  let D := Function.update c k H
  have hleD : c ≤ D := by
    intro j
    by_cases hj : j=k
    · subst j; simpa [D] using hle
    · simp [D,Function.update_of_ne hj]
  have hD : ∀ j, ¬ HasCM (D j) s := by
    intro j
    by_cases hj : j=k
    · subst j; simpa [D] using hH
    · simpa [D,Function.update_of_ne hj] using hno j
  have hh := congrFun (hmax D hleD hD) k
  simpa [D] using hh

end MatchingStability


end PermutedModule44

/- Source module: ConnectedMatchingCompletionLabels.lean -/
section PermutedModule45

/-!
The bounded-label multicolouring produced by saturation, ready for the
quantitative completion argument. New proof: @fqlx.
-/

open SimpleGraph

namespace MatchingStability

/-- Saturating a connected-matching-free multicolouring on at most `b*s`
vertices gives at most `b+1` component labels in each colour. Tail labels can
always be chosen in the common finite type `Option V`. -/
theorem exists_saturated_star_multicolouring
    {V : Type*} [Fintype V] (c : Fin 3 → SimpleGraph V) (s b : ℕ)
    (hs : 1 ≤ s) (hsize : Fintype.card V ≤ b*s)
    (hno : ∀ k, ¬ HasCM (c k) s) :
    ∃ C : Fin 3 → SimpleGraph V,
      c ≤ C ∧ (∀ k, ¬ HasCM (C k) s) ∧
      ∃ comp : Fin 3 → V → Fin (b+1),
      ∃ head : Fin 3 → V → Prop,
      ∃ leaf : Fin 3 → V → Option V,
        ∀ k u v, (C k).Adj u v ↔ u ≠ v ∧ comp k u = comp k v ∧
          (head k u ∨ head k v ∨ leaf k u = leaf k v) := by
  classical
  obtain ⟨C,hcC,hC,hmax⟩ := exists_maximal_multicolouring c s hno
  have hmaxC (k : Fin 3) :
      ∀ H : SimpleGraph V, C k ≤ H → ¬ HasCM H s → H = C k :=
    maximal_colour_of_multicolouring C s hC hmax k
  have hemb (k : Fin 3) : Nonempty ((C k).ConnectedComponent ↪ Fin (b+1)) := by
    letI := Fintype.ofFinite (C k).ConnectedComponent
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
      component_count_le (C k) s b hs hsize (hC k) (hmaxC k)
  let emb (k : Fin 3) : (C k).ConnectedComponent ↪ Fin (b+1) :=
    Classical.choice (hemb k)
  choose head leaf hform using
    fun k => maximal_no_connected_matching_representation (C k) s (hC k) (hmaxC k)
  refine ⟨C,hcC,hC,(fun k v => emb k ((C k).connectedComponentMk v)),head,leaf,?_⟩
  intro k u v
  simpa only [(emb k).injective.eq_iff] using hform k u v

/-- The `b=4` interface used for three-colour even-cycle stability. -/
theorem exists_five_component_multicolouring
    {V : Type*} [Fintype V] (c : Fin 3 → SimpleGraph V) (s : ℕ)
    (hs : 1 ≤ s) (hsize : Fintype.card V ≤ 4*s)
    (hno : ∀ k, ¬ HasCM (c k) s) :
    ∃ C : Fin 3 → SimpleGraph V,
      c ≤ C ∧ (∀ k, ¬ HasCM (C k) s) ∧
      ∃ comp : Fin 3 → V → Fin 5,
      ∃ head : Fin 3 → V → Prop,
      ∃ leaf : Fin 3 → V → Option V,
        ∀ k u v, (C k).Adj u v ↔ u ≠ v ∧ comp k u = comp k v ∧
          (head k u ∨ head k v ∨ leaf k u = leaf k v) :=
  exists_saturated_star_multicolouring c s 4 hs hsize hno

end MatchingStability


end PermutedModule45

/- Source module: LetzterQuarterCut.lean -/
section PermutedModule46

/-!
A finite quarter-cut lemma used in Letzter's completion argument for
monochromatic connected matchings. The averaging is proved by finite sums
and two Boolean-coordinate involutions; no probabilistic axiom is needed.
Credit: @fqlx; mathematical argument from Letzter, Claim 4.1.
-/

namespace LetzterCuts

open Finset
open scoped BigOperators

def flipAt {A : Type*} [DecidableEq A] (a : A) : Equiv.Perm (A → Bool) where
  toFun f x := if x=a then !(f x) else f x
  invFun f x := if x=a then !(f x) else f x
  left_inv f := by
    funext x
    by_cases h : x=a <;> simp [h]
  right_inv f := by
    funext x
    by_cases h : x=a <;> simp [h]

def hit {A : Type*} (a b : A) (f : A → Bool) : ℕ :=
  if f a = true ∧ f b = false then 1 else 0

theorem four_hits {A : Type*} [DecidableEq A]
    (a b : A) (hab : a ≠ b) (f : A → Bool) :
    hit a b f + hit a b (flipAt a f) + hit a b (flipAt b f) +
      hit a b (flipAt a (flipAt b f)) = 1 := by
  cases hfa : f a <;> cases hfb : f b <;>
    simp [hit,flipAt,hab,Ne.symm hab,hfa,hfb]

theorem four_mul_sum_hit {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A) (hab : a ≠ b) :
    4 * (∑ f : A → Bool, hit a b f) = Fintype.card (A → Bool) := by
  have ha := Equiv.sum_comp (flipAt a) (hit a b)
  have hb := Equiv.sum_comp (flipAt b) (hit a b)
  have hab' := Equiv.sum_comp ((flipAt b).trans (flipAt a)) (hit a b)
  change (∑ f : A → Bool, hit a b (flipAt a (flipAt b f))) = _ at hab'
  calc
    4 * (∑ f : A → Bool, hit a b f) =
        ∑ f : A → Bool, (hit a b f + hit a b (flipAt a f) +
          hit a b (flipAt b f) + hit a b (flipAt a (flipAt b f))) := by
      rw [sum_add_distrib,sum_add_distrib,sum_add_distrib,ha,hb,hab']
      omega
    _ = ∑ _f : A → Bool, 1 := by
      apply sum_congr rfl
      intro f _
      exact four_hits a b hab f
    _ = Fintype.card (A → Bool) := by simp

/-- From any indexed collection of unequal ordered pairs, retain at least a
quarter so that no left label equals any right label in the retained family. -/
theorem exists_quarter_cut
    {I A : Type*} [DecidableEq I] [Fintype A] [DecidableEq A]
    (S : Finset I) (a b : I → A) (hne : ∀ i ∈ S, a i ≠ b i) :
    ∃ T ⊆ S, S.card ≤ 4*T.card ∧ ∀ i ∈ T, ∀ j ∈ T, a i ≠ b j := by
  classical
  let cut (f : A → Bool) := S.filter (fun i => f (a i)=true ∧ f (b i)=false)
  have hcut (f : A → Bool) : (cut f).card = ∑ i ∈ S, hit (a i) (b i) f := by
    simp only [cut,card_eq_sum_ones,sum_filter,hit]
  have total : 4 * (∑ f : A → Bool, (cut f).card) =
      S.card * Fintype.card (A → Bool) := by
    calc
      4 * (∑ f : A → Bool, (cut f).card) =
          ∑ i ∈ S, 4 * (∑ f : A → Bool, hit (a i) (b i) f) := by
        simp_rw [hcut]
        rw [sum_comm,mul_sum]
      _ = ∑ _i ∈ S, Fintype.card (A → Bool) := by
        apply sum_congr rfl
        intro i hi
        exact four_mul_sum_hit (a i) (b i) (hne i hi)
      _ = S.card * Fintype.card (A → Bool) := by simp
  obtain ⟨f,_,hmax⟩ := exists_max_image (univ : Finset (A → Bool))
    (fun f => (cut f).card) univ_nonempty
  have hsum : (∑ g : A → Bool, (cut g).card) ≤
      Fintype.card (A → Bool) * (cut f).card := by
    calc
      _ ≤ ∑ _g : A → Bool, (cut f).card := sum_le_sum (fun g hg => hmax g hg)
      _ = _ := by simp
  have hpos : 0 < Fintype.card (A → Bool) := Fintype.card_pos
  have hlarge : S.card ≤ 4*(cut f).card := by nlinarith
  refine ⟨cut f,filter_subset ..,hlarge,?_⟩
  intro i hi j hj heq
  have hi' := (mem_filter.mp hi).2.1
  have hj' := (mem_filter.mp hj).2.2
  rw [heq] at hi'
  simp_all

end LetzterCuts


end PermutedModule46

/- Source module: LetzterStarCuts.lean -/
section PermutedModule47

/-!
The bounded-type part of Letzter's completion argument, separated from
the saturated-star structural theorem. Credit: @fqlx.
-/

namespace LetzterCuts

open Finset SimpleGraph

theorem one_colour_cut
    {I V B A : Type*} [DecidableEq I] [Fintype A] [DecidableEq A]
    (S : Finset I) (left right : I → V) (G : SimpleGraph V)
    (comp : V → B) (head : V → Prop) (leaf : V → A)
    (form : ∀ u v, G.Adj u v ↔ u ≠ v ∧ comp u = comp v ∧
      (head u ∨ head v ∨ leaf u = leaf v))
    (lc rc : B) (hleft : ∀ i ∈ S, comp (left i) = lc)
    (hright : ∀ i ∈ S, comp (right i) = rc)
    (hne : ∀ i ∈ S, ∀ j ∈ S, left i ≠ right j)
    (hnon : ∀ i ∈ S, ¬ G.Adj (left i) (right i)) :
    ∃ T ⊆ S, S.card ≤ 4*T.card ∧
      ∀ i ∈ T, ∀ j ∈ T, ¬ G.Adj (left i) (right j) := by
  classical
  by_cases hc : lc = rc
  · have comps (i) (hi : i∈S) (j) (hj : j∈S) : comp (left i)=comp (right j) :=
      (hleft i hi).trans (hc.trans (hright j hj).symm)
    have noleft (i) (hi : i∈S) : ¬ head (left i) := fun h =>
      hnon i hi ((form ..).mpr ⟨hne i hi i hi,comps i hi i hi,Or.inl h⟩)
    have noright (i) (hi : i∈S) : ¬ head (right i) := fun h =>
      hnon i hi ((form ..).mpr ⟨hne i hi i hi,comps i hi i hi,Or.inr (Or.inl h)⟩)
    have diff (i) (hi : i∈S) : leaf (left i) ≠ leaf (right i) := fun h =>
      hnon i hi ((form ..).mpr ⟨hne i hi i hi,comps i hi i hi,Or.inr (Or.inr h)⟩)
    obtain ⟨T,hT,hsize,hcut⟩ := exists_quarter_cut S (leaf ∘ left) (leaf ∘ right) diff
    refine ⟨T,hT,hsize,?_⟩
    intro i hi j hj hadj
    rcases ((form ..).mp hadj).2.2 with h | h | h
    · exact noleft i (hT hi) h
    · exact noright j (hT hj) h
    · exact hcut i hi j hj h
  · refine ⟨S,subset_rfl,by omega,?_⟩
    intro i hi j hj hadj
    exact hc ((hleft i hi).symm.trans (((form ..).mp hadj).2.1.trans (hright j hj)))

/-- If each colour component is a complete blow-up of a star, and there are
at most `card B` components of each colour, a bounded missing degree bounds
every disjoint family of nonedges. Component labels alone suffice for the
type count; a nonedge inside one component already forces both ends into tails. -/
theorem nonedge_family_bound
    {I V B A : Type*} [DecidableEq I] [Fintype V] [DecidableEq V]
    [Fintype B] [DecidableEq B] [Fintype A] [DecidableEq A]
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (comp : Fin 3 → V → B) (head : Fin 3 → V → Prop) (leaf : Fin 3 → V → A)
    (form : ∀ k u v, (c k).Adj u v ↔ u ≠ v ∧ comp k u = comp k v ∧
      (head k u ∨ head k v ∨ leaf k u = leaf k v))
    (d : ℕ) (hdegree : ∀ u : V,
      (univ.filter (fun v => u ≠ v ∧ ∀ k, ¬ (c k).Adj u v)).card ≤ d)
    (S : Finset I) (left right : I → V)
    (hrinj : Set.InjOn right S)
    (hne : ∀ i ∈ S, ∀ j ∈ S, left i ≠ right j)
    (hnon : ∀ k i, i∈S → ¬ (c k).Adj (left i) (right i)) :
    S.card ≤ 64 * (Fintype.card B)^6 * d := by
  classical
  by_contra hbad
  have hbig : 64 * (Fintype.card B)^6 * d < S.card := by omega
  let P := (Fin 3 → B) × (Fin 3 → B)
  let τ : I → P := fun i => (fun k => comp k (left i), fun k => comp k (right i))
  have hP : Fintype.card P = (Fintype.card B)^6 := by
    simp only [P,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
    ring
  obtain ⟨p,_,hlarge⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s:=S) (t:=univ) (f:=τ) (n:=64*d) (fun _ _ => mem_univ _) (by
      calc
        (univ : Finset P).card * (64*d) = 64 * (Fintype.card B)^6 * d := by
          rw [card_univ,hP]
          ring
        _ < S.card := hbig)
  let S₀ := S.filter (fun i => τ i = p)
  change 64*d < S₀.card at hlarge
  have hS₀ : S₀ ⊆ S := filter_subset ..
  have cut (k : Fin 3) (T : Finset I) (hT : T⊆S₀) :
      ∃ U ⊆ T, T.card ≤ 4*U.card ∧
        ∀ i∈U, ∀ j∈U, ¬ (c k).Adj (left i) (right j) := by
    apply one_colour_cut T left right (c k) (comp k) (head k) (leaf k)
      (form k) (p.1 k) (p.2 k)
    · intro i hi
      exact congrArg (fun q : P => q.1 k) ((mem_filter.mp (hT hi)).2)
    · intro i hi
      exact congrArg (fun q : P => q.2 k) ((mem_filter.mp (hT hi)).2)
    · intro i hi j hj
      exact hne i (hS₀ (hT hi)) j (hS₀ (hT hj))
    · intro i hi
      exact hnon k i (hS₀ (hT hi))
  obtain ⟨S₁,hS₁,hsize₁,hn₀⟩ := cut 0 S₀ subset_rfl
  obtain ⟨S₂,hS₂,hsize₂,hn₁⟩ := cut 1 S₁ hS₁
  obtain ⟨S₃,hS₃,hsize₃,hn₂⟩ := cut 2 S₂ (hS₂.trans hS₁)
  have hS₃S : S₃ ⊆ S := hS₃.trans (hS₂.trans (hS₁.trans hS₀))
  have hdlt : d < S₃.card := by omega
  obtain ⟨i,hi⟩ := card_pos.mp (show 0< S₃.card by omega)
  have hcross : S₃.image right ⊆ univ.filter
      (fun v => left i ≠ v ∧ ∀ k, ¬ (c k).Adj (left i) v) := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hv
    refine mem_filter.mpr ⟨mem_univ _,hne i (hS₃S hi) j (hS₃S hj),?_⟩
    intro k
    fin_cases k
    · exact hn₀ i (hS₂ (hS₃ hi)) j (hS₂ (hS₃ hj))
    · exact hn₁ i (hS₃ hi) j (hS₃ hj)
    · exact hn₂ i hi j hj
  have hcard : (S₃.image right).card = S₃.card :=
    card_image_of_injOn (hrinj.mono hS₃S)
  have hbound := (card_le_card hcross).trans (hdegree (left i))
  rw [hcard] at hbound
  omega

end LetzterCuts


end PermutedModule47

/- Source module: LetzterCompletion.lean -/
section PermutedModule48

open Finset SimpleGraph
open scoped BigOperators

namespace LetzterCuts

/-- The star representation and bounded missing degree allow completion by
deleting only a bounded number of vertices. The remaining graph is genuinely
complete; no missing edge is assigned an arbitrary colour. -/
theorem delete_vertices_to_complete
    {V B A : Type*} [Fintype V] [DecidableEq V]
    [Fintype B] [DecidableEq B] [Fintype A] [DecidableEq A]
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (comp : Fin 3 → V → B) (head : Fin 3 → V → Prop) (leaf : Fin 3 → V → A)
    (form : ∀ k u v, (c k).Adj u v ↔ u ≠ v ∧ comp k u=comp k v ∧
      (head k u ∨ head k v ∨ leaf k u=leaf k v))
    (d : ℕ) (hdegree : ∀ u : V,
      (univ.filter (fun v => u ≠ v ∧ ∀ k, ¬ (c k).Adj u v)).card ≤ d) :
    ∃ Z : Finset V, Z.card ≤ 128*(Fintype.card B)^6*d ∧
      ∀ u v : V, u ∉ Z → v ∉ Z → u ≠ v → ∃ k, (c k).Adj u v := by
  classical
  let ends : V×V → Finset V := fun e => {e.1,e.2}
  let good : Finset (V×V) → Prop := fun E =>
    (∀ e ∈ E, e.1 ≠ e.2 ∧ ∀ k, ¬ (c k).Adj e.1 e.2) ∧
    (E : Set (V×V)).PairwiseDisjoint ends
  have hempty : good ∅ := by simp [good]
  obtain ⟨E,_,hmax⟩ := Finite.exists_le_maximal (p:=good) hempty
  have hgood : good E := hmax.1
  let Z := E.biUnion ends
  have hends {e : V×V} (he : e∈E) : ends e ⊆ Z :=
    fun _ h => mem_biUnion.mpr ⟨e,he,h⟩
  have hright : Set.InjOn Prod.snd (E : Set (V×V)) := by
    intro e he f hf hef
    by_contra hne
    have hd := hgood.2 he hf hne
    have he2 : e.2 ∈ ends e := by simp [ends]
    have hf2 : e.2 ∈ ends f := by simp [ends,hef]
    exact Finset.disjoint_left.mp hd he2 hf2
  have hcross : ∀ e∈E, ∀ f∈E, e.1 ≠ f.2 := by
    intro e he f hf hef
    by_cases heq : e=f
    · subst f
      exact (hgood.1 e he).1 hef
    · have he1 : e.1 ∈ ends e := by simp [ends]
      have hf2 : e.1 ∈ ends f := by simp [ends,hef]
      exact Finset.disjoint_left.mp (hgood.2 he hf heq) he1 hf2
  have hbound : E.card ≤ 64*(Fintype.card B)^6*d :=
    nonedge_family_bound c comp head leaf form d hdegree E Prod.fst Prod.snd
      hright hcross (fun k e he => (hgood.1 e he).2 k)
  have hZ : Z.card ≤ 2*E.card := by
    calc
      Z.card ≤ ∑ e∈E, (ends e).card := card_biUnion_le
      _ ≤ ∑ _e∈E, 2 := sum_le_sum (fun e _ => by
        have h := card_insert_le e.1 ({e.2} : Finset V)
        simpa [ends] using h)
      _ = 2*E.card := by simp [Nat.mul_comm]
  refine ⟨Z,?_,?_⟩
  · calc
      Z.card ≤ 2*E.card := hZ
      _ ≤ 2*(64*(Fintype.card B)^6*d) := Nat.mul_le_mul_left 2 hbound
      _ = 128*(Fintype.card B)^6*d := by ring
  intro u v hu hv huv
  by_contra hnon
  push_neg at hnon
  have hnew : (u,v) ∉ E := by
    intro he
    exact hu (hends he (by simp [ends]))
  have hnewdis (e : V×V) (he : e∈E) : Disjoint (ends (u,v)) (ends e) := by
    apply Finset.disjoint_left.mpr
    intro w hw hwE
    have hwZ := hends he hwE
    have hw' : w=u ∨ w=v := by simpa [ends] using hw
    rcases hw' with rfl | rfl
    · exact hu hwZ
    · exact hv hwZ
  have hgood' : good (insert (u,v) E) := by
    constructor
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · exact ⟨huv,hnon⟩
      · exact hgood.1 e he
    · intro e he f hf hef
      rcases mem_insert.mp he with rfl | he
      · rcases mem_insert.mp hf with rfl | hf
        · exact (hef rfl).elim
        · exact hnewdis f hf
      · rcases mem_insert.mp hf with rfl | hf
        · exact (hnewdis e he).symm
        · exact hgood.2 he hf hef
  have hle : insert (u,v) E ⊆ E := hmax.2 hgood' (subset_insert ..)
  exact hnew (hle (mem_insert_self ..))

end LetzterCuts


end PermutedModule48

/- Source module: ConnectedMatchingCompletion.lean -/
section PermutedModule49

open Finset SimpleGraph

namespace MatchingStability

/-- Quantitative completion for three-colour connected matchings. Saturate
each colour without creating the forbidden matching, then delete the endpoints
of a maximal family of remaining nonedges. -/
theorem complete_extension_after_deletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (s d : ℕ) (hs : 1 ≤ s) (hsize : Fintype.card V ≤ 4*s)
    (hno : ∀ k, ¬ HasCM (c k) s)
    (hdegree : ∀ u : V,
      (univ.filter (fun v => u ≠ v ∧ ∀ k, ¬ (c k).Adj u v)).card ≤ d) :
    ∃ (C : Fin 3 → SimpleGraph V) (Z : Finset V),
      c ≤ C ∧ (∀ k, ¬ HasCM (C k) s) ∧ Z.card ≤ 2000000*d ∧
      ∀ u v : V, u ∉ Z → v ∉ Z → u ≠ v → ∃ k, (C k).Adj u v := by
  classical
  obtain ⟨C,hcC,hC,comp,head,leaf,hform⟩ :=
    exists_five_component_multicolouring c s hs hsize hno
  have hdegreeC (u : V) :
      (univ.filter (fun v => u ≠ v ∧ ∀ k, ¬ (C k).Adj u v)).card ≤ d := by
    apply le_trans ?_ (hdegree u)
    apply card_le_card
    intro v hv
    obtain ⟨_,hne,hn⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨mem_univ _,hne,fun k hk => hn k (hcC k hk)⟩
  obtain ⟨Z,hZ,hcomplete⟩ := LetzterCuts.delete_vertices_to_complete
    C comp head leaf hform d hdegreeC
  have hZ' : Z.card ≤ 2000000*d := by
    simpa using hZ
  exact ⟨C,Z,hcC,hC,hZ',hcomplete⟩

end MatchingStability


end PermutedModule49

/- Source module: MissingDegreeCleaning.lean -/
section PermutedModule50

/-!
From a bound on the total number of ordered missing pairs to a complete
reduced core, preserving every original color and every connected-matching
exclusion. Credit: @fqlx.
-/

open Finset SimpleGraph

namespace MatchingStability

theorem exists_low_missing_degree_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (d : ℕ)
    (hsum : ∑ u : V,
      (univ.filter (fun v => u ≠ v ∧ ∀ k, ¬ (c k).Adj u v)).card ≤ d * d) :
    ∃ S : Finset V, Fintype.card V ≤ S.card + d ∧
      ∀ u ∈ S,
        (S.filter (fun v => u ≠ v ∧ ∀ k, ¬ (c k).Adj u v)).card ≤ d := by
  classical
  let deg (u : V) :=
    (univ.filter (fun v => u ≠ v ∧ ∀ k, ¬ (c k).Adj u v)).card
  let bad := univ.filter (fun u => d < deg u)
  have hlow : bad.card * (d + 1) ≤ ∑ u : V, deg u := by
    calc
      _ = ∑ _u ∈ bad, (d + 1) := by simp
      _ ≤ ∑ u ∈ bad, deg u := by
        exact sum_le_sum fun u hu => (mem_filter.mp hu).2
      _ ≤ ∑ u : V, deg u := sum_le_sum_of_subset (filter_subset _ _)
  have hbad : bad.card ≤ d := by
    by_contra! h
    have hle : (d + 1) * (d + 1) ≤ d * d :=
      (Nat.mul_le_mul_right (d + 1) h).trans (hlow.trans hsum)
    nlinarith only [hle]
  let S := univ \ bad
  refine ⟨S,?_,?_⟩
  · have h := card_sdiff_add_card_eq_card (subset_univ bad)
    simp only [card_univ] at h
    change Fintype.card V ≤ (univ \ bad).card + d
    omega
  · intro u hu
    have hgood : deg u ≤ d := by
      have hn := (mem_sdiff.mp hu).2
      by_contra! h
      exact hn (mem_filter.mpr ⟨mem_univ _,h⟩)
    apply le_trans ?_ hgood
    exact card_le_card (filter_subset_filter _ (subset_univ _))

/-- A nearly complete multicoloring has a complete multicolored core. The
embedding records the original vertices and the extension keeps all original
edges. Its loss is linear in the square-root missing-pair bound. -/
theorem exists_complete_core
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (s d : ℕ) (hs : 1 ≤ s) (hsize : Fintype.card V ≤ 4 * s)
    (hno : ∀ k, ¬ HasCM (c k) s)
    (hsum : ∑ u : V,
      (univ.filter (fun v => u ≠ v ∧ ∀ k, ¬ (c k).Adj u v)).card ≤ d * d) :
    ∃ (q : ℕ) (f : Fin q ↪ V) (C : Fin 3 → SimpleGraph (Fin q)),
      Fintype.card V ≤ q + 2000001 * d ∧ q ≤ Fintype.card V ∧
      (∀ k u v, (c k).Adj (f u) (f v) → (C k).Adj u v) ∧
      (∀ k, ¬ HasCM (C k) s) ∧
      ∀ u v, u ≠ v → ∃ k, (C k).Adj u v := by
  classical
  obtain ⟨S,hScard,hSdegree⟩ := exists_low_missing_degree_subset c d hsum
  let cS : Fin 3 → SimpleGraph S := fun k => (c k).induce (S : Set V)
  have hSsize : Fintype.card S ≤ 4 * s := by
    have h := card_le_univ S
    simpa only [Fintype.card_coe] using h.trans hsize
  have hSno (k : Fin 3) : ¬ HasCM (cS k) s := by
    intro h
    exact hno k (h.map ⟨Subtype.val,fun he => he⟩ Subtype.val_injective)
  have hSdeg (u : S) :
      (univ.filter (fun v : S => u ≠ v ∧ ∀ k, ¬ (cS k).Adj u v)).card ≤ d := by
    apply le_trans ?_ (hSdegree u u.property)
    apply card_le_card_of_injOn (fun v : S => (v : V))
    · intro v hv
      obtain ⟨_,hne,hv⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨v.property,fun h => hne (Subtype.ext h),hv⟩
    · intro u _ v _ h
      exact Subtype.ext h
  obtain ⟨D,Z,hcD,hD,hZ,hcomplete⟩ := complete_extension_after_deletion
    cS s d hs hSsize hSno hSdeg
  let T : Finset S := univ \ Z
  let e : Fin T.card ≃ T := (Fintype.equivFinOfCardEq (by simp)).symm
  let f : Fin T.card ↪ V :=
    ⟨fun u => ((e u : T) : S).val,
      fun u v h => e.injective (Subtype.ext (Subtype.ext h))⟩
  let C : Fin 3 → SimpleGraph (Fin T.card) :=
    fun k => (D k).comap (fun u => (e u : S))
  have hTcard : T.card + Z.card = S.card := by
    simpa only [card_univ,Fintype.card_coe] using
      card_sdiff_add_card_eq_card (subset_univ Z)
  have hmapinj : Function.Injective (fun u : Fin T.card => (e u : S)) :=
    fun u v h => e.injective (Subtype.ext h)
  refine ⟨T.card,f,C,by omega,?_,?_,?_,?_⟩
  · simpa using Fintype.card_le_of_injective f f.injective
  · intro k u v huv
    exact hcD k huv
  · intro k h
    exact hD k (h.map ⟨fun u => (e u : S),fun he => he⟩ hmapinj)
  · intro u v huv
    apply hcomplete (e u : S) (e v : S)
    · exact (mem_sdiff.mp (e u).property).2
    · exact (mem_sdiff.mp (e v).property).2
    · exact fun h => huv (hmapinj h)

end MatchingStability


end PermutedModule50

/- Source module: ReducedCoreClassification.lean -/
section PermutedModule51

/-!
Quantitative stability for a nearly complete reduced multicoloring, including
the completion and the rounding to a multiple of four. Credit: @fqlx.
-/

open SimpleGraph Finset

namespace MatchingStability

theorem nearly_complete_core_classification
    (t d : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ ≤ 1 / 10000)
    (ht : 16 ≤ θ * t) (hloss : (2000001 * d + 3 : ℝ) ≤ θ * t)
    (c : Fin 3 → SimpleGraph (Fin t)) [∀ k, DecidableRel (c k).Adj]
    (hno : ∀ k, ¬ HasCM (c k) (t / 4 + Nat.ceil (θ * t)))
    (hsum : ∑ u : Fin t,
      (univ.filter (fun v => u ≠ v ∧ ∀ k, ¬ (c k).Adj u v)).card ≤ d * d) :
    ∃ (m h : ℕ) (f : Fin (4 * m) ↪ Fin t)
      (C : Fin 3 → SimpleGraph (Fin (4 * m))),
      1 ≤ h ∧ 1000 * h ≤ m ∧ (t : ℝ) / 5 ≤ m ∧
      (t : ℝ) ≤ 4 * m + θ * t ∧ (h : ℝ) ≤ 10 * θ * m ∧
      (∀ k u v, (c k).Adj (f u) (f v) → (C k).Adj u v) ∧
      (∀ k, ¬ HasCM (C k) (m + h)) ∧
      (∀ u v, u ≠ v → ∃ k, (C k).Adj u v) ∧
      (Nonempty (QuantitativeFourBlockCore C m h) ∨
        Nonempty (QuantitativeCliqueCore C m h)) := by
  classical
  let s := t / 4 + Nat.ceil (θ * t)
  have hsceil : θ * t ≤ (Nat.ceil (θ * t) : ℝ) := Nat.le_ceil _
  have hsceilpos : 1 ≤ Nat.ceil (θ * t) := by
    exact_mod_cast (show (1 : ℝ) ≤ Nat.ceil (θ * t) by linarith)
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hsize : Fintype.card (Fin t) ≤ 4 * s := by
    simp only [Fintype.card_fin]
    dsimp [s]
    omega
  obtain ⟨q,f,D,hq,hqt,hcD,hD,hcomplete⟩ :=
    exists_complete_core c s d hs hsize hno hsum
  simp only [Fintype.card_fin] at hq hqt
  let m := q / 4
  let h := s - m
  have hmq : 4 * m ≤ q := Nat.mul_div_le q 4
  have hmt : 4 * m ≤ t := hmq.trans hqt
  have hqround : q ≤ 4 * m + 3 := by dsimp [m]; omega
  have htloss : (t : ℝ) ≤ 4 * m + θ * t := by
    have hnat : t ≤ 4 * m + 2000001 * d + 3 := by omega
    have hreal : (t : ℝ) ≤ 4 * m + 2000001 * d + 3 := by exact_mod_cast hnat
    linarith
  obtain ⟨he,hh,hmlower,hhupper⟩ := StabilityNumerics.rounded_core_parameters
    t m θ hθ (by linarith) ht hmt htloss
  change s = m + h at he
  change 1 ≤ h at hh
  change (h : ℝ) ≤ 10 * θ * m at hhupper
  have hm : 1000 * h ≤ m := by
    have hprod := mul_le_mul_of_nonneg_right hθsmall (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
    have hre : 1000 * (h : ℝ) ≤ m := by nlinarith
    exact_mod_cast hre
  let g : Fin (4 * m) ↪ Fin q := ⟨Fin.castLE hmq, Fin.castLE_injective hmq⟩
  let C : Fin 3 → SimpleGraph (Fin (4 * m)) := fun k => (D k).comap g
  have hCno (k : Fin 3) : ¬ HasCM (C k) (m + h) := by
    intro hCM
    have hCM' : HasCM (D k) (m + h) := hCM.map ⟨g,fun he => he⟩ g.injective
    rw [← he] at hCM'
    exact hD k hCM'
  have hCcover : ∀ u v : Fin (4 * m), u ≠ v → ∃ k, (C k).Adj u v := by
    intro u v huv
    exact hcomplete (g u) (g v) (fun h => huv (g.injective h))
  have hclass := quantitative_complete_three_color_classification C m h hh hm
    (Fintype.card_fin _) hCcover hCno
  refine ⟨m,h,g.trans f,C,hh,hm,hmlower,htloss,hhupper,?_,hCno,hCcover,hclass⟩
  intro k u v huv
  exact hcD k (g u) (g v) huv

end MatchingStability


end PermutedModule51

/- Source module: ReducedDegreeRounding.lean -/
section PermutedModule52

/-!
Rounding the maximum-missing-degree parameter used by reduced completion.
The concrete constant 2000001 includes completion loss and the final trimming
to a multiple of four. Credit: @fqlx.
-/

namespace MatchingStability

theorem reduced_degree_rounding_loss
    (θ : ℝ) (t : ℕ) (hθ : 0 < θ)
    (hlarge : 8 * (2000001 + 3 : ℝ) ≤ θ * t) :
    (2000001 * (Nat.ceil (θ * t / (8 * 2000001)) : ℝ) + 3) ≤ θ * t := by
  have hx : 0 ≤ θ * t / (8 * 2000001) :=
    div_nonneg (mul_nonneg hθ.le (Nat.cast_nonneg t)) (by norm_num)
  have hceil := Nat.ceil_lt_add_one hx
  norm_num at hceil hlarge ⊢
  nlinarith

theorem reduced_degree_rounding_lower (θ : ℝ) (t : ℕ) :
    θ * t / (8 * 2000001) ≤ (Nat.ceil (θ * t / (8 * 2000001)) : ℝ) :=
  Nat.le_ceil _

theorem reduced_exception_count_le_square
    (θ ε : ℝ) (t b : ℕ) (hθ : 0 ≤ θ)
    (hε : 2 * ε ≤ (θ / (8 * 2000001)) ^ 2)
    (hb : (b : ℝ) ≤ 2 * ε * (t : ℝ) ^ 2) :
    b ≤ Nat.ceil (θ * t / (8 * 2000001)) *
      Nat.ceil (θ * t / (8 * 2000001)) := by
  let D := Nat.ceil (θ * t / (8 * 2000001))
  have hx : 0 ≤ θ * t / (8 * 2000001) := by positivity
  have hD : θ * t / (8 * 2000001) ≤ (D : ℝ) := Nat.le_ceil _
  have hsq : (θ * t / (8 * 2000001)) ^ 2 ≤ (D : ℝ) ^ 2 :=
    (sq_le_sq₀ hx (Nat.cast_nonneg D)).mpr hD
  have hmul := mul_le_mul_of_nonneg_right hε (sq_nonneg (t : ℝ))
  have heq : (θ / (8 * 2000001)) ^ 2 * (t : ℝ) ^ 2 =
      (θ * t / (8 * 2000001)) ^ 2 := by ring
  have hreal : (b : ℝ) ≤ (D : ℝ) * D := by
    calc
      (b : ℝ) ≤ 2 * ε * (t : ℝ) ^ 2 := hb
      _ ≤ (θ / (8 * 2000001)) ^ 2 * (t : ℝ) ^ 2 := hmul
      _ = (θ * t / (8 * 2000001)) ^ 2 := heq
      _ ≤ (D : ℝ) ^ 2 := hsq
      _ = (D : ℝ) * D := by ring
  have hNat : b ≤ D * D := by exact_mod_cast hreal
  simpa [D] using hNat

theorem reduced_degree_rounding
    (θ ε : ℝ) (t b : ℕ) (hθ : 0 < θ)
    (hlarge : 8 * (2000001 + 3 : ℝ) ≤ θ * t)
    (hε : 2 * ε ≤ (θ / (8 * 2000001)) ^ 2)
    (hb : (b : ℝ) ≤ 2 * ε * (t : ℝ) ^ 2) :
    let D := Nat.ceil (θ * t / (8 * 2000001))
    (2000001 * D + 3 : ℝ) ≤ θ * t ∧
      θ * t / (8 * 2000001) ≤ (D : ℝ) ∧ b ≤ D * D := by
  exact ⟨reduced_degree_rounding_loss θ t hθ hlarge,
    reduced_degree_rounding_lower θ t,
    reduced_exception_count_le_square θ ε t b hθ.le hε hb⟩


end MatchingStability

end PermutedModule52

/- Source module: IndexedCommonRegularity.lean -/
section PermutedModule53

/-!
An indexed interface to @bmander's simultaneous regularity theorem from
open-math-agents PR #13771, whose proof is audited in CommonRegularity.lean.
The underlying regularity machinery is due to Yaël Dillies and Bhavik Mehta
(Apache-2.0, original notices retained in CommonRegularity.lean).
The enumeration and exceptional-pair transport below are new: @fqlx.
-/

open Finset SimpleGraph

namespace CommonRegularity

theorem indexed_simultaneous_equipartition
    (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (l : ℕ) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      ∀ (c : Fin 3 → SimpleGraph (Fin N)) [∀ k, DecidableRel (c k).Adj],
      (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c →
      ∃ t : ℕ, 1 ≤ t ∧ l ≤ t ∧ t ≤ M ∧
      ∃ parts : Fin t → Finset (Fin N),
        Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
        univ.biUnion parts = univ ∧
        (∀ i, N/t ≤ (parts i).card ∧ (parts i).card ≤ N/t+1) ∧
        (∀ i, (parts i).Nonempty) ∧
        ∃ bad ⊆ (univ : Finset (Fin t)).offDiag,
          (bad.card : ℝ) ≤ 2*ε*(t : ℝ)^2 ∧
          ∀ u v, u ≠ v → (u,v) ∉ bad →
            (∀ k, (c k).IsUniform (2*ε) (parts u) (parts v)) ∧
            ∃ k, (1/3 : ℚ) ≤ (c k).edgeDensity (parts u) (parts v) := by
  classical
  obtain ⟨M₀,hM₀⟩ := simultaneous_equipartition ε hε hε₁ (max l 1)
  refine ⟨max M₀ 1,?_⟩
  intro N hN c _ hc
  obtain ⟨P,hP,hl,hM,h₀,h₁⟩ := hM₀ (c 0) (c 1) (by
    simp only [Fintype.card_fin]
    omega)
  let t := P.parts.card
  let e : Fin t ≃ P.parts := P.parts.equivFin.symm
  let parts : Fin t → Finset (Fin N) := fun i => (e i).val
  have hparts (i) : parts i ∈ P.parts := (e i).property
  have hinj : Function.Injective parts := by
    intro i j h
    exact e.injective (Subtype.ext h)
  have hdisj : Pairwise (fun i j => Disjoint (parts i) (parts j)) := by
    intro i j hij
    exact P.disjoint (hparts i) (hparts j) (fun h => hij (hinj h))
  have hcover : univ.biUnion parts = univ := by
    apply eq_univ_iff_forall.mpr
    intro v
    obtain ⟨U,hU,hv⟩ := P.exists_mem (mem_univ v)
    obtain ⟨i,hi⟩ := e.surjective ⟨U,hU⟩
    apply mem_biUnion.mpr
    refine ⟨i,mem_univ _,?_⟩
    have he : parts i = U := congrArg Subtype.val hi
    simpa only [he] using hv
  have hsize (i) : N/t ≤ (parts i).card ∧ (parts i).card ≤ N/t+1 := by
    constructor
    · simpa only [card_univ,Fintype.card_fin] using hP.average_le_card_part (hparts i)
    · simpa only [card_univ,Fintype.card_fin] using hP.card_part_le_average_add_one (hparts i)
  obtain ⟨bad,hbadsub,hbadsize,hgood⟩ := joint_pairs c hc P h₀ h₁
  let badIdx := (univ : Finset (Fin t)).offDiag.filter
    (fun e => (parts e.1,parts e.2) ∈ bad)
  have hcard : badIdx.card ≤ bad.card := by
    apply card_le_card_of_injOn (fun e : Fin t × Fin t => (parts e.1,parts e.2))
    · exact fun e he => (mem_filter.mp he).2
    · intro a _ b _ hab
      exact Prod.ext (hinj (congrArg Prod.fst hab)) (hinj (congrArg Prod.snd hab))
  have hoff : (P.parts.offDiag.card : ℝ) ≤ (t : ℝ)^2 := by
    have hn : P.parts.offDiag.card ≤ t*t := by
      rw [offDiag_card]
      exact Nat.sub_le _ _
    rw [sq]
    exact_mod_cast hn
  refine ⟨t,(le_max_right l 1).trans hl,(le_max_left l 1).trans hl,
    hM.trans (le_max_left M₀ 1),parts,hdisj,hcover,hsize,
    (fun i => P.nonempty_of_mem_parts (hparts i)),badIdx,filter_subset _ _,?_,?_⟩
  · calc
      (badIdx.card : ℝ) ≤ bad.card := Nat.cast_le.mpr hcard
      _ ≤ P.parts.offDiag.card*(2*ε) := hbadsize
      _ ≤ (t : ℝ)^2*(2*ε) := mul_le_mul_of_nonneg_right hoff (by positivity)
      _ = 2*ε*(t : ℝ)^2 := by ring
  · intro u v huv hbad
    have hp : (parts u,parts v) ∈ P.parts.offDiag :=
      mem_offDiag.mpr ⟨hparts u,hparts v,fun h => huv (hinj h)⟩
    apply hgood _ hp
    intro hh
    exact hbad (mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_univ _,mem_univ _,huv⟩,hh⟩)

end CommonRegularity


end PermutedModule53

/- Source module: ConnectedMatchingEmbedding.lean -/
section PermutedModule54

/-!
Connected-matching cycle embedding, extracted from the accepted proof by
@green-notes, PR #3417 (commit e9d2a42f3ec1204b160d967776d1811234930b92):
`proofs/Erdos556.erdos_556.variants.luczak_asymptotic_even.R1.H2.lean`
in GuillaumeBAUD-coder/open-math-agents, checkout
b50c56608400a430d1f82972b03849f2def3d6e3.
The proof bodies are retained; imports and namespaces are adjusted and the
original H2 proposition is expanded in full. No reduction hypothesis is used.
-/

open SimpleGraph Finset

namespace ConnectedMatchingEmbeddingProof

/-! ### Uniformity and typical-degree helpers -/

private lemma card_bad_lt {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η) {U V V' : Finset (Fin N)}
    (huni : G.IsUniform η U V) (hd : d ≤ (G.edgeDensity U V : ℝ))
    (hU : 0 < U.card) (hV : 0 < V.card) (hV' : V' ⊆ V)
    (hV'card : (V.card : ℝ) * η ≤ (V'.card : ℝ)) :
    ((U.filter (fun u => ((G.neighborFinset u ∩ V').card : ℝ) ≤ (d - η) * (V'.card : ℝ))).card : ℝ) <
      (U.card : ℝ) * η := by
  set B := U.filter (fun u => ((G.neighborFinset u ∩ V').card : ℝ) ≤ (d - η) * (V'.card : ℝ))
  by_contra! hle
  have hB_pos : 0 < B.card := by
    have h1 : (0 : ℝ) < (U.card : ℝ) * η := by positivity
    exact_mod_cast h1.trans_le hle
  have hV'_pos : 0 < V'.card := by
    have h1 : (0 : ℝ) < (V.card : ℝ) * η := by positivity
    exact_mod_cast h1.trans_le hV'card
  have hdiff := huni (Finset.filter_subset _ _) hV' hle hV'card
  have hgt : d - η < (G.edgeDensity B V' : ℝ) := by
    rw [abs_sub_lt_iff] at hdiff
    linarith
  have hsub : G.interedges B V' ⊆
      B.biUnion (fun u => (G.neighborFinset u ∩ V').image (fun v => (u, v))) := by
    intro ⟨u, v⟩ huv
    rw [SimpleGraph.mk_mem_interedges_iff] at huv
    exact Finset.mem_biUnion.mpr ⟨u, huv.1,
      Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr huv.2.2, huv.2.1⟩, rfl⟩⟩
  have hcard_ie : (G.interedges B V').card ≤ ∑ u ∈ B, (G.neighborFinset u ∩ V').card := by
    calc (G.interedges B V').card
        ≤ (B.biUnion (fun u => (G.neighborFinset u ∩ V').image (fun v => (u, v)))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ u ∈ B, ((G.neighborFinset u ∩ V').image (fun v => (u, v))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ u ∈ B, (G.neighborFinset u ∩ V').card :=
          Finset.sum_le_sum fun _ _ => Finset.card_image_le
  have hcard_real : ((G.interedges B V').card : ℝ) ≤ (B.card : ℝ) * ((d - η) * (V'.card : ℝ)) := by
    calc ((G.interedges B V').card : ℝ)
        ≤ ((∑ u ∈ B, (G.neighborFinset u ∩ V').card : ℕ) : ℝ) := Nat.cast_le.mpr hcard_ie
      _ = ∑ u ∈ B, ((G.neighborFinset u ∩ V').card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _u ∈ B, (d - η) * (V'.card : ℝ) := by
          refine Finset.sum_le_sum fun u hu => ?_
          exact (Finset.mem_filter.mp hu).2
      _ = (B.card : ℝ) * ((d - η) * (V'.card : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
  have hden_pos : (0 : ℝ) < (B.card : ℝ) * (V'.card : ℝ) := by positivity
  have hle_den : (G.edgeDensity B V' : ℝ) ≤ d - η := by
    rw [SimpleGraph.edgeDensity_def]
    push_cast
    rw [div_le_iff₀ hden_pos]
    linarith
  linarith

private lemma exists_good_two {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η) {U P avoid V₁ T₁ V₂ T₂ : Finset (Fin N)}
    (hPU : P ⊆ U) (hU : 0 < U.card)
    (huni₁ : G.IsUniform η U V₁) (hd₁ : d ≤ (G.edgeDensity U V₁ : ℝ))
    (hV₁ : 0 < V₁.card) (hT₁ : T₁ ⊆ V₁) (hT₁c : (V₁.card : ℝ) * η ≤ (T₁.card : ℝ))
    (huni₂ : G.IsUniform η U V₂) (hd₂ : d ≤ (G.edgeDensity U V₂ : ℝ))
    (hV₂ : 0 < V₂.card) (hT₂ : T₂ ⊆ V₂) (hT₂c : (V₂.card : ℝ) * η ≤ (T₂.card : ℝ))
    (hP : (avoid.card : ℝ) + 2 * (U.card : ℝ) * η ≤ (P.card : ℝ)) :
    ∃ u ∈ P, u ∉ avoid ∧
      (d - η) * (T₁.card : ℝ) < ((G.neighborFinset u ∩ T₁).card : ℝ) ∧
      (d - η) * (T₂.card : ℝ) < ((G.neighborFinset u ∩ T₂).card : ℝ) := by
  set B₁ := U.filter (fun u => ((G.neighborFinset u ∩ T₁).card : ℝ) ≤ (d - η) * (T₁.card : ℝ))
  set B₂ := U.filter (fun u => ((G.neighborFinset u ∩ T₂).card : ℝ) ≤ (d - η) * (T₂.card : ℝ))
  have hB₁ : (B₁.card : ℝ) < (U.card : ℝ) * η := card_bad_lt G hη huni₁ hd₁ hU hV₁ hT₁ hT₁c
  have hB₂ : (B₂.card : ℝ) < (U.card : ℝ) * η := card_bad_lt G hη huni₂ hd₂ hU hV₂ hT₂ hT₂c
  set rem := P \ (avoid ∪ B₁ ∪ B₂)
  have hrem_pos : 0 < rem.card := by
    have h1 : P.card ≤ rem.card + (avoid ∪ B₁ ∪ B₂).card := by
      calc P.card ≤ (rem ∪ (avoid ∪ B₁ ∪ B₂)).card := Finset.card_le_card (fun x hx => by
            by_cases h : x ∈ avoid ∪ B₁ ∪ B₂
            · exact Finset.mem_union_right _ h
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩))
        _ ≤ rem.card + (avoid ∪ B₁ ∪ B₂).card := Finset.card_union_le _ _
    have h2 : (avoid ∪ B₁ ∪ B₂).card ≤ avoid.card + B₁.card + B₂.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have h12 : P.card ≤ rem.card + avoid.card + B₁.card + B₂.card := by omega
    have h3 : ((P.card : ℝ)) ≤ (rem.card : ℝ) + (avoid.card : ℝ) + (B₁.card : ℝ) + (B₂.card : ℝ) := by
      exact_mod_cast h12
    have h4 : (0 : ℝ) < (rem.card : ℝ) := by linarith
    exact_mod_cast h4
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hrem_pos
  rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_union] at hu
  have huU : u ∈ U := hPU hu.1
  have hnotB₁ : u ∉ B₁ := fun h => hu.2 (Or.inl (Or.inr h))
  have hnotB₂ : u ∉ B₂ := fun h => hu.2 (Or.inr h)
  refine ⟨u, hu.1, fun h => hu.2 (Or.inl (Or.inl h)), ?_, ?_⟩
  · by_contra! hle
    exact hnotB₁ (Finset.mem_filter.mpr ⟨huU, hle⟩)
  · by_contra! hle
    exact hnotB₂ (Finset.mem_filter.mpr ⟨huU, hle⟩)

private lemma no_empty_pair_of_uniform {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hd_gt : η < d) {U V A' B' : Finset (Fin N)}
    (huni : G.IsUniform η U V) (hd : d ≤ (G.edgeDensity U V : ℝ))
    (hA' : A' ⊆ U) (hB' : B' ⊆ V) {cA cB : ℕ}
    (hcA : (U.card : ℝ) * η ≤ (cA : ℝ)) (hcB : (V.card : ℝ) * η ≤ (cB : ℝ)) :
    ∀ X ⊆ A', ∀ Y ⊆ B', cA ≤ X.card → cB ≤ Y.card → ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y := by
  intro X hX Y hY hXc hYc
  have hX' : (U.card : ℝ) * η ≤ (X.card : ℝ) := hcA.trans (Nat.cast_le.mpr hXc)
  have hY' : (V.card : ℝ) * η ≤ (Y.card : ℝ) := hcB.trans (Nat.cast_le.mpr hYc)
  have hdiff := huni (hX.trans hA') (hY.trans hB') hX' hY'
  have hpos : (0 : ℝ) < (G.edgeDensity X Y : ℝ) := by
    rw [abs_sub_lt_iff] at hdiff
    linarith
  have hne : (G.interedges X Y).Nonempty := by
    rw [SimpleGraph.edgeDensity_def] at hpos
    push_cast at hpos
    by_contra! hem
    simp [hem] at hpos
  obtain ⟨⟨x, y⟩, hxy⟩ := hne
  rw [SimpleGraph.mk_mem_interedges_iff] at hxy
  exact ⟨x, hxy.1, y, hxy.2.1, hxy.2.2⟩

/-! ### Splitting a cluster into disjoint Res, Cap, Body -/

private lemma split_cluster {N : ℕ} (S : Finset (Fin N)) (q : ℕ) (hq : 2 * q ≤ S.card) :
    ∃ Res Cap Body : Finset (Fin N),
      Res ⊆ S ∧ Cap ⊆ S ∧ Body ⊆ S ∧
      Disjoint Res Cap ∧ Disjoint Res Body ∧ Disjoint Cap Body ∧
      Res.card = q ∧ Cap.card = q ∧ Body.card = S.card - 2 * q := by
  classical
  set L := S.toList
  have hnodup : L.Nodup := S.nodup_toList
  have hlen : L.length = S.card := S.length_toList
  set L1 := L.take q
  set L2 := (L.drop q).take q
  set L3 := L.drop (2 * q)
  have hcat : L1 ++ L2 ++ L3 = L := by
    have h1 : L2 ++ L3 = L.drop q := by
      simp only [L2, L3]
      rw [show 2 * q = q + q by omega, ← List.drop_drop]
      exact List.take_append_drop q (L.drop q)
    rw [List.append_assoc, h1]
    exact List.take_append_drop q L
  have hnodup_cat : (L1 ++ L2 ++ L3).Nodup := hcat.symm ▸ hnodup
  have hn12 : (L1 ++ L2).Nodup := (List.nodup_append.mp hnodup_cat).1
  have hn1 : L1.Nodup := (List.nodup_append.mp hn12).1
  have hn2 : L2.Nodup := (List.nodup_append.mp hn12).2.1
  have hn3 : L3.Nodup := (List.nodup_append.mp hnodup_cat).2.1
  refine ⟨L1.toFinset, L2.toFinset, L3.toFinset, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_toFinset] at hx
    exact S.mem_toList.mp (by show x ∈ L; rw [← hcat]; exact List.mem_append_left _ (List.mem_append_left _ hx))
  · intro x hx
    rw [List.mem_toFinset] at hx
    exact S.mem_toList.mp (by show x ∈ L; rw [← hcat]; exact List.mem_append_left _ (List.mem_append_right _ hx))
  · intro x hx
    rw [List.mem_toFinset] at hx
    exact S.mem_toList.mp (by show x ∈ L; rw [← hcat]; exact List.mem_append_right _ hx)
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [List.mem_toFinset] at hx1 hx2
    exact (List.nodup_append.mp hn12).2.2 x hx1 x hx2 rfl
  · rw [Finset.disjoint_left]
    intro x hx1 hx3
    rw [List.mem_toFinset] at hx1 hx3
    exact (List.nodup_append.mp hnodup_cat).2.2 x (List.mem_append_left _ hx1) x hx3 rfl
  · rw [Finset.disjoint_left]
    intro x hx2 hx3
    rw [List.mem_toFinset] at hx2 hx3
    exact (List.nodup_append.mp hnodup_cat).2.2 x (List.mem_append_right _ hx2) x hx3 rfl
  · rw [List.toFinset_card_of_nodup hn1, List.length_take, hlen]
    omega
  · rw [List.toFinset_card_of_nodup hn2, List.length_take, List.length_drop, hlen]
    omega
  · rw [List.toFinset_card_of_nodup hn3, List.length_drop, hlen]

/-! ### DFS long alternating path lemma -/

private noncomputable def bipartAdj {N : ℕ} (G : SimpleGraph (Fin N))
    (A' B' : Finset (Fin N)) (x y : Fin N) : Prop :=
  ((x ∈ A' ∧ y ∈ B') ∨ (x ∈ B' ∧ y ∈ A')) ∧ G.Adj x y

private lemma bipartAdj_symm {N : ℕ} {G : SimpleGraph (Fin N)} {A' B' : Finset (Fin N)}
    {x y : Fin N} (h : bipartAdj G A' B' x y) : bipartAdj G A' B' y x :=
  ⟨by rcases h.1 with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> [exact Or.inr ⟨hy, hx⟩; exact Or.inl ⟨hy, hx⟩],
    h.2.symm⟩

open Classical in
private noncomputable def dfsStep {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A' B' : Finset (Fin N)) (cA cB : ℕ)
    (P : List (Fin N)) (D W : Finset (Fin N)) :
    List (Fin N) × Finset (Fin N) × Finset (Fin N) :=
  if _ : cA ≤ (D ∩ A').card ∨ cB ≤ (D ∩ B').card then (P, D, W)
  else match P with
  | [] => ([], D, W)
  | v :: rest =>
    if hex : ∃ w ∈ W, bipartAdj G A' B' v w then
      dfsStep G A' B' cA cB (hex.choose :: v :: rest) D (W.erase hex.choose)
    else
      dfsStep G A' B' cA cB rest (insert v D) W
termination_by 2 * W.card + P.length
decreasing_by
  · have hc : (W.erase hex.choose).card < W.card := Finset.card_erase_lt_of_mem hex.choose_spec.1
    simp only [List.length_cons]
    omega
  · simp only [List.length_cons]
    omega

open Classical in
private lemma dfsStep_spec {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A' B' : Finset (Fin N)) (hdisj : Disjoint A' B') (cA cB : ℕ)
    (a₀ : Fin N) (ha₀ : a₀ ∈ A') (hdeg₀ : cB ≤ (G.neighborFinset a₀ ∩ B').card) :
    ∀ n : ℕ, ∀ (P : List (Fin N)) (D W : Finset (Fin N)),
      2 * W.card + P.length = n →
      P ≠ [] →
      P.getLast? = some a₀ →
      P.Nodup →
      P.IsChain (bipartAdj G A' B') →
      P.toFinset ⊆ A' ∪ B' →
      D ⊆ A' ∪ B' →
      W ⊆ A' ∪ B' →
      A' ∪ B' ⊆ P.toFinset ∪ D ∪ W →
      Disjoint D W →
      Disjoint D P.toFinset →
      Disjoint W P.toFinset →
      (∀ d ∈ D, ∀ w ∈ W, ¬ bipartAdj G A' B' d w) →
      (D ∩ A').card ≤ cA →
      (D ∩ B').card ≤ cB →
      let res := dfsStep G A' B' cA cB P D W
      res.1 ≠ [] ∧
      res.1.getLast? = some a₀ ∧
      res.1.Nodup ∧
      res.1.IsChain (bipartAdj G A' B') ∧
      res.1.toFinset ⊆ A' ∪ B' ∧
      res.2.1 ⊆ A' ∪ B' ∧
      res.2.2 ⊆ A' ∪ B' ∧
      A' ∪ B' ⊆ res.1.toFinset ∪ res.2.1 ∪ res.2.2 ∧
      (∀ d ∈ res.2.1, ∀ w ∈ res.2.2, ¬ bipartAdj G A' B' d w) ∧
      (res.2.1 ∩ A').card ≤ cA ∧
      (res.2.1 ∩ B').card ≤ cB ∧
      (cA ≤ (res.2.1 ∩ A').card ∨ cB ≤ (res.2.1 ∩ B').card) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P D W hn hPne hPlast hPnodup hPchain hPsub hDsub hWsub hcov
      hDW hDP hWP hnoEdge hDA hDB
    unfold dfsStep
    by_cases hstop : cA ≤ (D ∩ A').card ∨ cB ≤ (D ∩ B').card
    · simp only [dif_pos hstop]
      exact ⟨hPne, hPlast, hPnodup, hPchain, hPsub, hDsub, hWsub, hcov, hnoEdge, hDA, hDB, hstop⟩
    · simp only [dif_neg hstop]
      rcases P with _ | ⟨v, rest⟩
      · exact (hPne rfl).elim
      · by_cases hex : ∃ w ∈ W, bipartAdj G A' B' v w
        · simp only [dif_pos hex]
          set w := hex.choose
          have hwW : w ∈ W := hex.choose_spec.1
          have hvw : bipartAdj G A' B' v w := hex.choose_spec.2
          have hwsub : w ∈ A' ∪ B' := hWsub hwW
          have hwnP : w ∉ (v :: rest).toFinset := Finset.disjoint_left.mp hWP hwW
          have hwnD : w ∉ D := Finset.disjoint_right.mp hDW hwW
          have hlt : 2 * (W.erase w).card + (w :: v :: rest).length < n := by
            have hc := Finset.card_erase_lt_of_mem hwW
            simp only [List.length_cons] at hn ⊢
            omega
          refine ih _ hlt (w :: v :: rest) D (W.erase w) rfl (by simp) ?_ ?_ ?_ ?_ hDsub ?_ ?_ ?_ ?_ ?_ ?_ hDA hDB
          · simpa using hPlast
          · exact List.nodup_cons.mpr ⟨by simpa [List.mem_toFinset] using hwnP, hPnodup⟩
          · exact List.IsChain.cons_cons (bipartAdj_symm hvw) hPchain
          · intro x hx
            rw [List.toFinset_cons, Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · exact hwsub
            · exact hPsub hx
          · exact (Finset.erase_subset w W).trans hWsub
          · intro x hx
            rcases Finset.mem_union.mp (hcov hx) with hPD | hW
            · rcases Finset.mem_union.mp hPD with hP | hD
              · rw [List.toFinset_cons, Finset.mem_union, Finset.mem_union, Finset.mem_insert]
                exact Or.inl (Or.inl (Or.inr hP))
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ hD)
            · by_cases hxw : x = w
              · subst hxw
                rw [List.toFinset_cons, Finset.mem_union, Finset.mem_union, Finset.mem_insert]
                exact Or.inl (Or.inl (Or.inl rfl))
              · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxw, hW⟩)
          · exact Finset.disjoint_of_subset_right (Finset.erase_subset w W) hDW
          · rw [List.toFinset_cons, Finset.disjoint_insert_right]
            exact ⟨hwnD, hDP⟩
          · rw [List.toFinset_cons, Finset.disjoint_insert_right]
            exact ⟨Finset.notMem_erase w W, Finset.disjoint_of_subset_left (Finset.erase_subset w W) hWP⟩
          · intro d hd x hx
            exact hnoEdge d hd x (Finset.mem_of_mem_erase hx)
        · simp only [dif_neg hex]
          have hvP : v ∈ (v :: rest).toFinset := by simp
          have hvsub : v ∈ A' ∪ B' := hPsub hvP
          have hvnD : v ∉ D := Finset.disjoint_right.mp hDP hvP
          have hvnW : v ∉ W := Finset.disjoint_right.mp hWP hvP
          have hvnR : v ∉ rest.toFinset := by
            intro h
            have : v ∈ rest := List.mem_toFinset.mp h
            exact (List.nodup_cons.mp hPnodup).1 this
          have hrest_ne : rest ≠ [] := by
            intro hnil
            subst hnil
            simp only [List.getLast?_singleton, Option.some.injEq] at hPlast
            subst hPlast
            have hsubB : G.neighborFinset v ∩ B' ⊆ D ∩ B' := by
              intro b hb
              rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hb
              have hbAB : b ∈ A' ∪ B' := Finset.mem_union_right _ hb.2
              rcases Finset.mem_union.mp (hcov hbAB) with hPD | hW
              · rcases Finset.mem_union.mp hPD with hP | hD
                · rw [List.mem_toFinset, List.mem_singleton] at hP
                  subst hP
                  exact (Finset.disjoint_left.mp hdisj ha₀ hb.2).elim
                · exact Finset.mem_inter.mpr ⟨hD, hb.2⟩
              · exact (hex ⟨b, hW, Or.inl ⟨ha₀, hb.2⟩, hb.1⟩).elim
            have hle : cB ≤ (D ∩ B').card := hdeg₀.trans (Finset.card_le_card hsubB)
            exact hstop (Or.inr hle)
          have hlt : 2 * W.card + rest.length < n := by
            simp only [List.length_cons] at hn
            omega
          have hDA' : ((insert v D) ∩ A').card ≤ cA := by
            by_cases hvA : v ∈ A'
            · have : insert v D ∩ A' = insert v (D ∩ A') := by
                ext x; simp only [Finset.mem_inter, Finset.mem_insert]
                exact ⟨fun ⟨h1, h2⟩ => h1.elim Or.inl (fun hd => Or.inr ⟨hd, h2⟩),
                       fun h => h.elim (fun he => ⟨Or.inl he, he ▸ hvA⟩) (fun ⟨hd, ha⟩ => ⟨Or.inr hd, ha⟩)⟩
              rw [this, Finset.card_insert_of_notMem (fun h => hvnD (Finset.mem_inter.mp h).1)]
              have : (D ∩ A').card < cA := not_le.mp (fun h => hstop (Or.inl h))
              omega
            · have : insert v D ∩ A' = D ∩ A' := by
                ext x; simp only [Finset.mem_inter, Finset.mem_insert]
                exact ⟨fun ⟨h1, h2⟩ => ⟨h1.elim (fun he => (hvA (he ▸ h2)).elim) id, h2⟩,
                       fun ⟨hd, ha⟩ => ⟨Or.inr hd, ha⟩⟩
              rw [this]
              exact (not_le.mp (fun h => hstop (Or.inl h))).le
          have hDB' : ((insert v D) ∩ B').card ≤ cB := by
            by_cases hvB : v ∈ B'
            · have : insert v D ∩ B' = insert v (D ∩ B') := by
                ext x; simp only [Finset.mem_inter, Finset.mem_insert]
                exact ⟨fun ⟨h1, h2⟩ => h1.elim Or.inl (fun hd => Or.inr ⟨hd, h2⟩),
                       fun h => h.elim (fun he => ⟨Or.inl he, he ▸ hvB⟩) (fun ⟨hd, hb⟩ => ⟨Or.inr hd, hb⟩)⟩
              rw [this, Finset.card_insert_of_notMem (fun h => hvnD (Finset.mem_inter.mp h).1)]
              have : (D ∩ B').card < cB := not_le.mp (fun h => hstop (Or.inr h))
              omega
            · have : insert v D ∩ B' = D ∩ B' := by
                ext x; simp only [Finset.mem_inter, Finset.mem_insert]
                exact ⟨fun ⟨h1, h2⟩ => ⟨h1.elim (fun he => (hvB (he ▸ h2)).elim) id, h2⟩,
                       fun ⟨hd, hb⟩ => ⟨Or.inr hd, hb⟩⟩
              rw [this]
              exact (not_le.mp (fun h => hstop (Or.inr h))).le
          refine ih _ hlt rest (insert v D) W rfl hrest_ne ?_ (List.nodup_cons.mp hPnodup).2
            hPchain.tail ?_ ?_ hWsub ?_ ?_ ?_ ?_ ?_ hDA' hDB'
          · rcases rest with _ | ⟨r, rs⟩
            · exact (hrest_ne rfl).elim
            · simpa using hPlast
          · exact fun x hx => hPsub (by simp [List.mem_toFinset] at hx ⊢; right; exact hx)
          · rw [Finset.insert_subset_iff]
            exact ⟨hvsub, hDsub⟩
          · intro x hx
            rcases Finset.mem_union.mp (hcov hx) with hPD | hW
            · rcases Finset.mem_union.mp hPD with hP | hD
              · simp only [List.toFinset_cons, Finset.mem_insert] at hP
                rcases hP with rfl | hxR
                · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
                · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxR)
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_insert_of_mem hD))
            · exact Finset.mem_union_right _ hW
          · exact Finset.disjoint_insert_left.mpr ⟨hvnW, hDW⟩
          · rw [Finset.disjoint_insert_left]
            exact ⟨hvnR, Finset.disjoint_of_subset_right
              (by intro x hx; simp [List.mem_toFinset] at hx ⊢; right; exact hx) hDP⟩
          · exact Finset.disjoint_of_subset_right
              (by intro x hx; simp [List.mem_toFinset] at hx ⊢; right; exact hx) hWP
          · intro d hd w hw hadj
            rcases Finset.mem_insert.mp hd with rfl | hd
            · exact hex ⟨w, hw, hadj⟩
            · exact hnoEdge d hd w hw hadj

private lemma alternating_chain_props {N : ℕ} (G : SimpleGraph (Fin N)) :
    ∀ (Q : List (Fin N)) (A' B' : Finset (Fin N)),
      Disjoint A' B' → Q ≠ [] →
      (∀ h : Q ≠ [], Q.head h ∈ A') →
      Q.IsChain (bipartAdj G A' B') → Q.Nodup →
      (Q.toFinset ∩ A').card ≤ (Q.length + 1) / 2 ∧
      (Q.toFinset ∩ B').card ≤ Q.length / 2 ∧
      (∀ i (hi : i < Q.length), (Even i → Q[i] ∈ A') ∧ (Odd i → Q[i] ∈ B')) := by
  intro Q
  induction Q with
  | nil => intro _ _ _ hne; exact (hne rfl).elim
  | cons a t ih =>
    intro A' B' hdisj _ hhead hchain hnodup
    have haA : a ∈ A' := hhead (by simp)
    have haB : a ∉ B' := Finset.disjoint_left.mp hdisj haA
    rcases t with _ | ⟨b, ts⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [haA]
      · simp [haB]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨fun _ => haA, fun hodd => by simp at hodd⟩
    · have hab : bipartAdj G A' B' a b := List.IsChain.rel_head hchain
      have hbB : b ∈ B' := by
        rcases hab.1 with ⟨_, hb⟩ | ⟨ha, _⟩
        · exact hb
        · exact (haB ha).elim
      have hchain_t : (b :: ts).IsChain (bipartAdj G B' A') := by
        refine hchain.tail.imp fun {x y} hxy => ?_
        rcases hxy.1 with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact ⟨Or.inr ⟨hx, hy⟩, hxy.2⟩
        · exact ⟨Or.inl ⟨hx, hy⟩, hxy.2⟩
      have hrec := ih B' A' hdisj.symm (by simp) (fun _ => hbB) hchain_t (List.nodup_cons.mp hnodup).2
      have hanT : a ∉ (b :: ts).toFinset := by
        simpa [List.mem_toFinset] using (List.nodup_cons.mp hnodup).1
      have hsubA : (a :: b :: ts).toFinset ∩ A' = insert a ((b :: ts).toFinset ∩ A') := by
        ext x; simp [haA]
      have hsubB : (a :: b :: ts).toFinset ∩ B' = (b :: ts).toFinset ∩ B' := by
        ext x; simp [haB]
      refine ⟨?_, ?_, ?_⟩
      · rw [hsubA, Finset.card_insert_of_notMem (fun h => hanT (Finset.mem_inter.mp h).1)]
        have := hrec.2.1
        simp only [List.length_cons] at this ⊢
        omega
      · rw [hsubB]
        have := hrec.1
        simp only [List.length_cons] at this ⊢
        omega
      · intro i hi
        rcases i with _ | i
        · exact ⟨fun _ => haA, fun hodd => by simp at hodd⟩
        · have hi' : i < (b :: ts).length := by simpa using hi
          have hstep := hrec.2.2 i hi'
          refine ⟨fun heven => ?_, fun hodd => ?_⟩
          · rcases Nat.even_or_odd i with h | h
            · exact absurd h (Nat.even_add_one.mp heven)
            · exact hstep.2 h
          · rcases Nat.even_or_odd i with h | h
            · exact hstep.1 h
            · exact absurd h (Nat.odd_add_one.mp hodd)

private lemma dfs_long_path {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A' B' : Finset (Fin N)) (hdisj : Disjoint A' B') {cA cB : ℕ}
    (hcA : 0 < cA) (hcB : 0 < cB)
    (hnoempty : ∀ X ⊆ A', ∀ Y ⊆ B', cA ≤ X.card → cB ≤ Y.card → ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y)
    (a₀ : Fin N) (ha₀ : a₀ ∈ A') (hdeg₀ : cB ≤ (G.neighborFinset a₀ ∩ B').card) :
    ∃ Q : List (Fin N),
      Q ≠ [] ∧ Q.head? = some a₀ ∧ Q.Nodup ∧ Q.IsChain (bipartAdj G A' B') ∧
      Q.toFinset ⊆ A' ∪ B' ∧
      2 * (min A'.card B'.card - 2 * max cA cB) + 1 ≤ Q.length ∧
      (∀ i (hi : i < Q.length), (Even i → Q[i] ∈ A') ∧ (Odd i → Q[i] ∈ B')) := by
  have ha₀_sub : a₀ ∈ A' ∪ B' := Finset.mem_union_left _ ha₀
  set W₀ := (A' ∪ B').erase a₀
  have hspec := dfsStep_spec G A' B' hdisj cA cB a₀ ha₀ hdeg₀
    (2 * W₀.card + [a₀].length) [a₀] ∅ W₀ rfl (by simp) (by simp) (by simp) (by simp)
    (by simp [ha₀_sub]) (by simp) (Finset.erase_subset _ _)
    (fun x hx => by
      by_cases h : x = a₀
      · subst h; simp
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h, hx⟩))
    (by simp) (by simp) (by simp [W₀]) (by simp) (by simp) (by simp)
  set res := dfsStep G A' B' cA cB [a₀] ∅ W₀
  set P := res.1
  set D := res.2.1
  set W := res.2.2
  obtain ⟨hPne, hPlast, hPnodup, hPchain, hPsub, hDsub, hWsub, hcov, hnoEdge, hDA, hDB, hstop⟩ := hspec
  set Q := P.reverse
  have hQne : Q ≠ [] := by simpa [Q] using hPne
  have hQhead : Q.head? = some a₀ := by
    rw [List.head?_reverse]
    exact hPlast
  have hQnodup : Q.Nodup := List.nodup_reverse.mpr hPnodup
  have hQchain : Q.IsChain (bipartAdj G A' B') := by
    rw [List.isChain_reverse]
    exact hPchain.imp (fun {_ _} h => bipartAdj_symm h)
  have hQsub : Q.toFinset ⊆ A' ∪ B' := by
    intro x hx
    exact hPsub (by simpa [Q] using hx)
  have hprops := alternating_chain_props G Q A' B' hdisj hQne (fun h => by
    have := List.head?_eq_some_head h
    rw [hQhead] at this
    exact (Option.some.inj this).symm ▸ ha₀) hQchain hQnodup
  have hQpos : 0 < Q.length := List.length_pos_of_ne_nil hQne
  have hlen : 2 * (min A'.card B'.card - 2 * max cA cB) + 1 ≤ Q.length := by
    rcases hstop with hDA_ge | hDB_ge
    · have hWB : (W ∩ B').card < cB := by
        by_contra! hWB_ge
        obtain ⟨x, hx, y, hy, hadj⟩ := hnoempty (D ∩ A') Finset.inter_subset_right
          (W ∩ B') Finset.inter_subset_right hDA_ge hWB_ge
        exact hnoEdge x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1
          ⟨Or.inl ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hy).2⟩, hadj⟩
      have hB_cov : B' ⊆ (Q.toFinset ∩ B') ∪ (D ∩ B') ∪ (W ∩ B') := by
        intro b hb
        have hbAB : b ∈ A' ∪ B' := Finset.mem_union_right _ hb
        rcases Finset.mem_union.mp (hcov hbAB) with hPD | hW
        · rcases Finset.mem_union.mp hPD with hP | hD
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_inter.mpr ⟨by simpa [Q] using hP, hb⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hD, hb⟩))
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hW, hb⟩)
      have hB_card : B'.card ≤ (Q.toFinset ∩ B').card + (D ∩ B').card + (W ∩ B').card :=
        (Finset.card_le_card hB_cov).trans
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
      have hQB := hprops.2.1
      have hDB' : (D ∩ B').card ≤ cB := hDB
      have hmin := min_le_right A'.card B'.card
      have hmax := le_max_right cA cB
      omega
    · have hWA : (W ∩ A').card < cA := by
        by_contra! hWA_ge
        obtain ⟨x, hx, y, hy, hadj⟩ := hnoempty (W ∩ A') Finset.inter_subset_right
          (D ∩ B') Finset.inter_subset_right hWA_ge hDB_ge
        exact hnoEdge y (Finset.mem_inter.mp hy).1 x (Finset.mem_inter.mp hx).1
          ⟨Or.inr ⟨(Finset.mem_inter.mp hy).2, (Finset.mem_inter.mp hx).2⟩, hadj.symm⟩
      have hA_cov : A' ⊆ (Q.toFinset ∩ A') ∪ (D ∩ A') ∪ (W ∩ A') := by
        intro a ha
        have haAB : a ∈ A' ∪ B' := Finset.mem_union_left _ ha
        rcases Finset.mem_union.mp (hcov haAB) with hPD | hW
        · rcases Finset.mem_union.mp hPD with hP | hD
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_inter.mpr ⟨by simpa [Q] using hP, ha⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hD, ha⟩))
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hW, ha⟩)
      have hA_card : A'.card ≤ (Q.toFinset ∩ A').card + (D ∩ A').card + (W ∩ A').card :=
        (Finset.card_le_card hA_cov).trans
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
      have hQA := hprops.1
      have hDA' : (D ∩ A').card ≤ cA := hDA
      have hmin := min_le_left A'.card B'.card
      have hmax := le_max_left cA cB
      omega
  exact ⟨Q, hQne, hQhead, hQnodup, hQchain, hQsub, hlen, hprops.2.2⟩

/-! ### Extracting disjoint matching edges and building closed walk in R -/

private lemma extract_matching_pairs {t : ℕ} {R : SimpleGraph (Fin t)} (M : R.Subgraph)
    (hM : M.IsMatching) :
    ∀ (k : ℕ) (S : Finset (Fin t)),
      (∀ x ∈ S, x ∈ M.verts) →
      (∀ x ∈ S, ∀ y, M.Adj x y → y ∈ S) →
      2 * k ≤ S.card →
      ∃ edges : List (Fin t × Fin t),
        edges.length = k ∧
        (∀ p ∈ edges, M.Adj p.1 p.2) ∧
        (∀ p ∈ edges, p.1 ∈ S ∧ p.2 ∈ S) ∧
        (edges.flatMap (fun p => [p.1, p.2])).Nodup := by
  intro k
  induction k with
  | zero =>
    intro S _ _ _
    exact ⟨[], rfl, by simp, by simp, by simp⟩
  | succ k ih =>
    intro S hSverts hSclosed hScard
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨u, huS⟩ := hSne
    obtain ⟨v, hvAdj, hvUniq⟩ := hM (hSverts u huS)
    have hvS : v ∈ S := hSclosed u huS v hvAdj
    have huv : u ≠ v := R.ne_of_adj (M.adj_sub hvAdj)
    set S' := (S.erase u).erase v
    have hS'verts : ∀ x ∈ S', x ∈ M.verts := fun x hx =>
      hSverts x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
    have hS'closed : ∀ x ∈ S', ∀ y, M.Adj x y → y ∈ S' := by
      intro x hx y hxy
      have hxS := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
      have hxv : x ≠ v := Finset.ne_of_mem_erase hx
      have hxu : x ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
      have hyS := hSclosed x hxS y hxy
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hyS⟩⟩
      · intro hyv; subst hyv
        exact hxu (hM.eq_of_adj_right hxy hvAdj)
      · intro hyu; subst hyu
        exact hxv (hvUniq x hxy.symm)
    have hS'card : 2 * k ≤ S'.card := by
      have h1 : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem huS
      have hv_er : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvS⟩
      have h2 : S'.card = (S.erase u).card - 1 := Finset.card_erase_of_mem hv_er
      omega
    obtain ⟨edges, hlen, hadj, hmemS', hnodup⟩ := ih S' hS'verts hS'closed hS'card
    have hnotU : u ∉ edges.flatMap (fun p => [p.1, p.2]) := by
      rw [List.mem_flatMap]
      rintro ⟨q, hq, hzq⟩
      have hqS' := hmemS' q hq
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hzq
      rcases hzq with rfl | rfl
      · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hqS'.1) rfl
      · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hqS'.2) rfl
    have hnotV : v ∉ edges.flatMap (fun p => [p.1, p.2]) := by
      rw [List.mem_flatMap]
      rintro ⟨q, hq, hzq⟩
      have hqS' := hmemS' q hq
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hzq
      rcases hzq with rfl | rfl
      · exact Finset.ne_of_mem_erase hqS'.1 rfl
      · exact Finset.ne_of_mem_erase hqS'.2 rfl
    refine ⟨(u, v) :: edges, by simp [hlen], ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hvAdj
      · exact hadj p hp
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨huS, hvS⟩
      · exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hmemS' p hp).1),
               Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hmemS' p hp).2)⟩
    · simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
      refine ⟨?_, hnotV, hnodup⟩
      simp only [List.mem_cons]
      rintro (rfl | h)
      · exact huv rfl
      · exact hnotU h

private lemma walk_boundary_edge {t : ℕ} {R : SimpleGraph (Fin t)}
    {V : Finset (Fin t)} {a b : Fin t} (ha : a ∈ V) (hb : b ∉ V)
    (hwalk : R.Reachable a b) :
    ∃ x y : Fin t, R.Adj x y ∧ x ∈ V ∧ y ∉ V := by
  obtain ⟨w⟩ := hwalk
  induction w with
  | nil => exact (hb ha).elim
  | @cons u v c huv _ ih =>
    by_cases hv : v ∈ V
    · exact ih hv hb
    · exact ⟨u, v, huv, ha, hv⟩

private def spliceAt {α : Type*} [DecidableEq α] (x : α)
    (ins W : List (α × α × Bool)) : List (α × α × Bool) :=
  match W with
  | [] => ins
  | e :: rest => if e.1 = x then ins ++ e :: rest else e :: spliceAt x ins rest

private lemma isChain_append {α : Type*} {r : α → α → Prop} {l₁ l₂ : List α}
    (h₁ : l₁.IsChain r) (h₂ : l₂.IsChain r)
    (hbd : ∀ a ∈ l₁.getLast?, ∀ b ∈ l₂.head?, r a b) :
    (l₁ ++ l₂).IsChain r := by
  induction l₁ with
  | nil => simpa using h₂
  | cons x xs ih =>
    rcases xs with _ | ⟨y, ys⟩
    · simp only [List.nil_append, List.singleton_append]
      rcases l₂ with _ | ⟨b, bs⟩
      · exact h₁
      · exact List.IsChain.cons_cons (hbd x (by simp) b (by simp)) h₂
    · simp only [List.cons_append]
      exact List.IsChain.cons_cons (List.IsChain.rel_head h₁)
        (ih h₁.tail (fun a ha b hb => hbd a (by simpa using ha) b hb))

private lemma spliceAt_props {α : Type*} [DecidableEq α] (x : α)
    (ins W : List (α × α × Bool))
    (hWne : W ≠ []) (hex : ∃ e ∈ W, e.1 = x)
    (hWchain : W.IsChain (fun a b => a.2.1 = b.1))
    (hins_ne : ins ≠ [])
    (hins_head : (ins.head hins_ne).1 = x)
    (hins_last : (ins.getLast hins_ne).2.1 = x)
    (hins_chain : ins.IsChain (fun a b => a.2.1 = b.1)) :
    let W' := spliceAt x ins W
    W' ≠ [] ∧
    (∀ h' : W' ≠ [], (W'.head h').1 = (W.head hWne).1) ∧
    (∀ h' : W' ≠ [], W'.getLast h' = W.getLast hWne) ∧
    W'.length = W.length + ins.length ∧
    W'.IsChain (fun a b => a.2.1 = b.1) ∧
    (∀ e, e ∈ W' ↔ e ∈ ins ∨ e ∈ W) ∧
    List.Perm (W'.filter (·.2.2)) (ins.filter (·.2.2) ++ W.filter (·.2.2)) := by
  induction W with
  | nil => exact (hWne rfl).elim
  | cons e rest ih =>
    unfold spliceAt
    by_cases he : e.1 = x
    · rw [if_pos he]
      have hne' : ins ++ e :: rest ≠ [] := List.append_ne_nil_of_right_ne_nil _ (by simp)
      refine ⟨hne', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h'
        rw [List.head_append_of_ne_nil hins_ne]
        simpa [he] using hins_head
      · intro h'
        exact List.getLast_append_of_ne_nil _ (by simp)
      · simp; omega
      · refine isChain_append hins_chain hWchain ?_
        intro a ha b hb
        have ha' : a = ins.getLast hins_ne := (by
          rw [List.getLast?_eq_some_getLast hins_ne] at ha
          simpa using ha : ins.getLast hins_ne = a).symm
        have hb' : b = e := (by simpa using hb : e = b).symm
        subst ha'; subst hb'
        simpa [he] using hins_last
      · intro z; simp
      · rw [List.filter_append]
    · rw [if_neg he]
      have hex_rest : ∃ e' ∈ rest, e'.1 = x := by
        rcases hex with ⟨e', he', hx'⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact (he hx').elim
        · exact ⟨e', he', hx'⟩
      have hrest_ne : rest ≠ [] := by
        rintro rfl; obtain ⟨e', he', _⟩ := hex_rest; exact (List.not_mem_nil he').elim
      obtain ⟨hne_r, hhead_r, hlast_r, hlen_r, hchain_r, hmem_r, hperm_r⟩ :=
        ih hrest_ne hex_rest hWchain.tail
      refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; simp
      · intro h'
        rw [List.getLast_cons hne_r, hlast_r hne_r, List.getLast_cons hrest_ne]
      · simp [hlen_r]; omega
      · refine List.IsChain.cons_of_ne_nil hne_r hchain_r ?_
        rw [hhead_r hne_r]
        rcases rest with _ | ⟨r, rs⟩
        · exact (hrest_ne rfl).elim
        · simp only [List.head_cons]
          exact List.isChain_iff_getElem.mp hWchain 0 (by simp)
      · intro z
        simp only [List.mem_cons, hmem_r]
        tauto
      · by_cases hp : e.2.2 = true
        · simp only [List.filter_cons, hp, ↓reduceIte]
          exact (hperm_r.cons e).trans (List.perm_middle.symm)
        · have hp' : e.2.2 = false := Bool.eq_false_iff.mpr hp
          simp only [List.filter_cons, hp', Bool.false_eq_true, ↓reduceIte]
          exact hperm_r

private lemma nodup_flatMap_pair_unique {α : Type*} :
    ∀ (L : List (α × α)) (p q : α × α),
      (L.flatMap (fun r => [r.1, r.2])).Nodup →
      p ∈ L → q ∈ L → (q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2) → q = p := by
  intro L
  induction L with
  | nil => intro p q _ hp; exact (List.not_mem_nil hp).elim
  | cons a t ih =>
    intro p q hnodup hp hq heq
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hp with hpa | hp'
    · rcases List.mem_cons.mp hq with hqa | hq'
      · exact hqa.trans hpa.symm
      · exfalso
        have h1 : q.1 ∈ t.flatMap (fun r => [r.1, r.2]) := List.mem_flatMap.mpr ⟨q, hq', by simp⟩
        have h2 : q.2 ∈ t.flatMap (fun r => [r.1, r.2]) := List.mem_flatMap.mpr ⟨q, hq', by simp⟩
        rw [hpa] at heq
        rcases heq with h | h | h | h
        · exact hnodup.1 (List.mem_cons.mpr (Or.inr (h ▸ h1)))
        · exact hnodup.2.1 (h ▸ h1)
        · exact hnodup.1 (List.mem_cons.mpr (Or.inr (h ▸ h2)))
        · exact hnodup.2.1 (h ▸ h2)
    · rcases List.mem_cons.mp hq with hqa | hq'
      · exfalso
        have h1 : p.1 ∈ t.flatMap (fun r => [r.1, r.2]) := List.mem_flatMap.mpr ⟨p, hp', by simp⟩
        have h2 : p.2 ∈ t.flatMap (fun r => [r.1, r.2]) := List.mem_flatMap.mpr ⟨p, hp', by simp⟩
        rw [hqa] at heq
        rcases heq with h | h | h | h
        · exact hnodup.1 (List.mem_cons.mpr (Or.inr (h.symm ▸ h1)))
        · exact hnodup.1 (List.mem_cons.mpr (Or.inr (h.symm ▸ h2)))
        · exact hnodup.2.1 (h.symm ▸ h1)
        · exact hnodup.2.1 (h.symm ▸ h2)
      · exact ih p q hnodup.2.2 hp' hq' heq

private lemma filter_length_insert_two {α : Type*} [DecidableEq α]
    (L : List (α × α)) (hL : L.Nodup) (V : Finset α) (y y' : α)
    (p : α × α) (hpL : p ∈ L) (hp_eq : (p.1 = y ∧ p.2 = y') ∨ (p.1 = y' ∧ p.2 = y))
    (huniq : ∀ q ∈ L, (q.1 = y ∨ q.1 = y') → q = p)
    (hyV : y ∉ V) (hy'V : y' ∉ V) :
    (L.filter (fun q => decide (q.1 ∈ insert y (insert y' V)))).length =
      (L.filter (fun q => decide (q.1 ∈ V))).length + 1 := by
  induction L with
  | nil => exact (List.not_mem_nil hpL).elim
  | cons a t ih =>
    have hat : a ∉ t := (List.nodup_cons.mp hL).1
    have ht : t.Nodup := (List.nodup_cons.mp hL).2
    rcases List.mem_cons.mp hpL with hpa | hp
    · have hp_old : decide (p.1 ∈ V) = false := by
        rw [decide_eq_false_iff_not]
        rcases hp_eq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1 ▸ hyV
        · exact h1 ▸ hy'V
      have hp_new : decide (p.1 ∈ insert y (insert y' V)) = true := by
        rw [decide_eq_true_eq]
        rcases hp_eq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1 ▸ Finset.mem_insert_self _ _
        · exact h1 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hcongr : t.filter (fun q => decide (q.1 ∈ insert y (insert y' V))) =
          t.filter (fun q => decide (q.1 ∈ V)) := by
        refine List.filter_congr fun q hqt => ?_
        have hqn : q ≠ p := fun h => hat (hpa ▸ h ▸ hqt)
        have hqnot : ¬ (q.1 = y ∨ q.1 = y') := fun h => hqn (huniq q (List.mem_cons_of_mem _ hqt) h)
        have hiff : q.1 ∈ insert y (insert y' V) ↔ q.1 ∈ V := by simp only [Finset.mem_insert]; tauto
        simp only [hiff]
      rw [← hpa]
      simp only [List.filter_cons, hp_old, hp_new, Bool.false_eq_true, ↓reduceIte, hcongr, List.length_cons]
    · have ha_neq : a ≠ p := fun h => hat (h ▸ hp)
      have ha_not : ¬ (a.1 = y ∨ a.1 = y') := fun h => ha_neq (huniq a List.mem_cons_self h)
      have hiff : a.1 ∈ insert y (insert y' V) ↔ a.1 ∈ V := by simp only [Finset.mem_insert]; tauto
      have hsame : decide (a.1 ∈ insert y (insert y' V)) = decide (a.1 ∈ V) := by simp only [hiff]
      have ih' := ih ht hp (fun q hqt h => huniq q (List.mem_cons_of_mem _ hqt) h)
      simp only [List.filter_cons, hsame]
      cases h : decide (a.1 ∈ V)
      · simp only [Bool.false_eq_true, ↓reduceIte, ih']
      · simp only [↓reduceIte, List.length_cons, ih']

private lemma build_closed_walk {t : ℕ} {R : SimpleGraph (Fin t)}
    (chosen : List (Fin t × Fin t)) (hchosen_ne : chosen ≠ [])
    (hchosen_adj : ∀ p ∈ chosen, R.Adj p.1 p.2)
    (hchosen_nodup : (chosen.flatMap (fun p => [p.1, p.2])).Nodup)
    (hchosen_reach : ∀ p ∈ chosen, ∀ q ∈ chosen, R.Reachable p.1 q.1) :
    ∃ W : List (Fin t × Fin t × Bool),
      W ≠ [] ∧
      (∀ e ∈ W, R.Adj e.1 e.2.1) ∧
      W.IsChain (fun a b => a.2.1 = b.1) ∧
      (∀ h : W ≠ [], (W.getLast h).2.1 = (W.head h).1) ∧
      (∀ h : W ≠ [], (W.getLast h).2.2 = false) ∧
      Even W.length ∧ 2 ≤ W.length ∧ W.length ≤ 2 * t ∧
      chosen.length ≤ W.length / 2 ∧
      (chosen.length = 1 → W.length = 2) ∧
      W.countP (·.2.2) = chosen.length ∧
      ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup := by
  classical
  rcases chosen with _ | ⟨⟨u₁, v₁⟩, rest_ch⟩
  · exact (hchosen_ne rfl).elim
  have h1_mem : (u₁, v₁) ∈ (u₁, v₁) :: rest_ch := List.mem_cons_self
  have h1_adj : R.Adj u₁ v₁ := hchosen_adj _ h1_mem
  have huv1 : u₁ ≠ v₁ := R.ne_of_adj h1_adj
  set W₀ : List (Fin t × Fin t × Bool) := [(u₁, v₁, true), (v₁, u₁, false)]
  set V₀ : Finset (Fin t) := {u₁, v₁}
  have hV₀_card : V₀.card = 2 := Finset.card_pair huv1
  have ht2 : 2 ≤ t := by
    have h1 : V₀.card ≤ t := by simpa using Finset.card_le_univ V₀
    omega
  by_cases hrest : rest_ch = []
  · subst hrest
    refine ⟨W₀, by simp [W₀], ?_, List.IsChain.cons_cons rfl (List.IsChain.singleton _),
      by simp [W₀], by simp [W₀], ⟨1, rfl⟩, by simp [W₀], by simp [W₀]; omega,
      by simp [W₀], fun _ => by simp [W₀], by simp [W₀], by simp [W₀, huv1]⟩
    intro e he
    simp only [W₀, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact h1_adj
    · exact h1_adj.symm
  set ch := (u₁, v₁) :: rest_ch
  have hch_nodup : ch.Nodup := by
    have : ∀ (L : List (Fin t × Fin t)), (L.flatMap (fun p => [p.1, p.2])).Nodup → L.Nodup := by
      intro L h
      induction L with
      | nil => simp
      | cons a ts ih =>
        simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at h
        refine List.nodup_cons.mpr ⟨fun ha => ?_, ih h.2.2⟩
        exact h.1 (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩))
    exact this ch hchosen_nodup
  have hstep : ∀ n : ℕ, ∀ (W : List (Fin t × Fin t × Bool)) (V : Finset (Fin t)),
      t - V.card = n →
      W ≠ [] →
      (∀ e ∈ W, R.Adj e.1 e.2.1) →
      W.IsChain (fun a b => a.2.1 = b.1) →
      (∀ h : W ≠ [], (W.getLast h).2.1 = (W.head h).1) →
      (∀ h : W ≠ [], (W.getLast h).2.2 = false) →
      u₁ ∈ V →
      (∀ e ∈ W, e.1 ∈ V ∧ e.2.1 ∈ V) →
      (∀ v ∈ V, ∃ e ∈ W, e.1 = v) →
      W.length = 2 * (V.card - 1) → 2 ≤ V.card →
      (∀ p ∈ ch, (p.1 ∈ V ∧ p.2 ∈ V) ∨ (p.1 ∉ V ∧ p.2 ∉ V)) →
      W.countP (·.2.2) = (ch.filter (fun p => decide (p.1 ∈ V))).length →
      ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup →
      ∃ W' : List (Fin t × Fin t × Bool),
        W' ≠ [] ∧
        (∀ e ∈ W', R.Adj e.1 e.2.1) ∧
        W'.IsChain (fun a b => a.2.1 = b.1) ∧
        (∀ h : W' ≠ [], (W'.getLast h).2.1 = (W'.head h).1) ∧
        (∀ h : W' ≠ [], (W'.getLast h).2.2 = false) ∧
        Even W'.length ∧ 2 ≤ W'.length ∧ W'.length ≤ 2 * t ∧
        ch.length ≤ W'.length / 2 ∧
        (ch.length = 1 → W'.length = 2) ∧
        W'.countP (·.2.2) = ch.length ∧
        ((W'.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro W V hn hWne hWadj hWchain hWwrap hWlastf hu1V hWV hVW hWlen hV2 hchInv hWcnt hWnodup
      by_cases hall : ∀ p ∈ ch, p.1 ∈ V ∧ p.2 ∈ V
      · have hfilt : ch.filter (fun p => decide (p.1 ∈ V)) = ch :=
          List.filter_eq_self.mpr fun p hp => decide_eq_true (hall p hp).1
        have hch_sub : ∀ z ∈ ch.flatMap (fun p => [p.1, p.2]), z ∈ V := by
          intro z hz
          rw [List.mem_flatMap] at hz
          obtain ⟨p, hp, hzp⟩ := hz
          rcases List.mem_cons.mp hzp with rfl | hzp
          · exact (hall p hp).1
          · rw [List.mem_singleton] at hzp; subst hzp; exact (hall p hp).2
        have h2ch : 2 * ch.length ≤ V.card := by
          have h1 : (ch.flatMap (fun p => [p.1, p.2])).toFinset ⊆ V := fun z hz =>
            hch_sub z (List.mem_toFinset.mp hz)
          have h2 := Finset.card_le_card h1
          rw [List.toFinset_card_of_nodup hchosen_nodup] at h2
          have h3 : (ch.flatMap (fun p => [p.1, p.2])).length = 2 * ch.length := by
            clear h1 h2 hch_sub hfilt hall
            induction ch with
            | nil => simp
            | cons a ts ihc => simp [ihc]; omega
          omega
        have hVt : V.card ≤ t := by simpa using Finset.card_le_univ V
        refine ⟨W, hWne, hWadj, hWchain, hWwrap, hWlastf, ?_, by omega, by omega, by omega,
          fun hch1 => by exfalso; simp [ch] at hch1; exact hrest hch1, ?_, hWnodup⟩
        · exact ⟨V.card - 1, by omega⟩
        · rw [hWcnt, hfilt]
      · push_neg at hall
        obtain ⟨p, hp_ch, hp_not⟩ := hall
        have hp_out : p.1 ∉ V ∧ p.2 ∉ V := by
          rcases hchInv p hp_ch with h | h
          · exact (hp_not h.1 h.2).elim
          · exact h
        obtain ⟨x, y, hxyAdj, hxV, hyV⟩ :=
          walk_boundary_edge hu1V hp_out.1 (hchosen_reach (u₁, v₁) h1_mem p hp_ch)
        obtain ⟨ex, hexW, hex1⟩ := hVW x hxV
        by_cases hy_ch : ∃ q ∈ ch, q.1 = y ∨ q.2 = y
        · obtain ⟨q, hq_ch, hqy⟩ := hy_ch
          set y' := if q.1 = y then q.2 else q.1
          have hy'_eq : (q.1 = y ∧ q.2 = y') ∨ (q.1 = y' ∧ q.2 = y) := by
            by_cases h : q.1 = y
            · exact Or.inl ⟨h, by simp [y', h]⟩
            · exact Or.inr ⟨by simp [y', h], hqy.resolve_left h⟩
          have hq_adj : R.Adj y y' := by
            rcases hy'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [← h1, ← h2]; exact hchosen_adj q hq_ch
            · rw [← h1, ← h2]; exact (hchosen_adj q hq_ch).symm
          have hyy' : y ≠ y' := R.ne_of_adj hq_adj
          have hy'V : y' ∉ V := by
            rcases hchInv q hq_ch with h | h
            · exfalso
              rcases hqy with h1 | h1
              · exact hyV (h1 ▸ h.1)
              · exact hyV (h1 ▸ h.2)
            · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩
              · exact h2 ▸ h.2
              · exact h1 ▸ h.1
          set ins : List (Fin t × Fin t × Bool) :=
            [(x, y, false), (y, y', true), (y', y, false), (y, x, false)]
          have hins_ne : ins ≠ [] := by simp [ins]
          have hins_chain : ins.IsChain (fun a b => a.2.1 = b.1) := by
            simp only [ins]
            exact List.IsChain.cons_cons rfl (List.IsChain.cons_cons rfl
              (List.IsChain.cons_cons rfl (List.IsChain.singleton _)))
          obtain ⟨hne', hhead', hlast', hlen', hchain', hmem', hperm'⟩ :=
            spliceAt_props x ins W hWne ⟨ex, hexW, hex1⟩ hWchain hins_ne rfl rfl hins_chain
          set W' := spliceAt x ins W
          set V' := insert y (insert y' V)
          have hV'card : V'.card = V.card + 2 := by
            have hy_ins : y ∉ insert y' V := by
              simp [hyy', hyV]
            rw [Finset.card_insert_of_notMem hy_ins, Finset.card_insert_of_notMem hy'V]
          have hVt : V.card ≤ t := by simpa using Finset.card_le_univ V
          have hV't : V'.card ≤ t := by simpa using Finset.card_le_univ V'
          have hlt : t - V'.card < n := by omega
          refine ih _ hlt W' V' rfl hne' ?_ hchain' ?_ ?_ ?_ ?_ ?_ ?_ (by omega) ?_ ?_ ?_
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he_ins
              rcases he_ins with rfl | rfl | rfl | rfl
              · exact hxyAdj
              · exact hq_adj
              · exact hq_adj.symm
              · exact hxyAdj.symm
            · exact hWadj e he_W
          · intro h'
            rw [hlast' h', hhead' h', hWwrap hWne]
          · intro h'
            rw [hlast' h', hWlastf hWne]
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu1V)
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he_ins
              rcases he_ins with rfl | rfl | rfl | rfl
              · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxV),
                       Finset.mem_insert_self _ _⟩
              · exact ⟨Finset.mem_insert_self _ _,
                       Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
              · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
                       Finset.mem_insert_self _ _⟩
              · exact ⟨Finset.mem_insert_self _ _,
                       Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxV)⟩
            · have := hWV e he_W
              exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.1),
                     Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.2)⟩
          · intro v hv
            simp only [V', Finset.mem_insert] at hv
            rcases hv with hvy | hvy' | hv
            · exact ⟨(y, y', true), (hmem' _).mpr (Or.inl (by simp [ins])), hvy.symm⟩
            · exact ⟨(y', y, false), (hmem' _).mpr (Or.inl (by simp [ins])), hvy'.symm⟩
            · obtain ⟨e, heW, he1⟩ := hVW v hv
              exact ⟨e, (hmem' _).mpr (Or.inr heW), he1⟩
          · rw [hlen', hV'card, hWlen]; simp [ins]; omega
          · intro r hr
            rcases hchInv r hr with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
            · exact Or.inl ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr1),
                            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr2)⟩
            · by_cases hr_eq : r = q
              · subst hr_eq
                rcases hy'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact Or.inl ⟨h1 ▸ Finset.mem_insert_self _ _,
                                h2 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
                · exact Or.inl ⟨h1 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
                                h2 ▸ Finset.mem_insert_self _ _⟩
              · refine Or.inr ⟨?_, ?_⟩
                · simp only [V', Finset.mem_insert, not_or]
                  refine ⟨fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_),
                          fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_), hr1⟩
                  · rcases hy'_eq with ⟨h1, _⟩ | ⟨_, h2⟩ <;> [exact Or.inl (h.trans h1.symm); exact Or.inr (Or.inl (h.trans h2.symm))]
                  · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩ <;> [exact Or.inr (Or.inl (h.trans h2.symm)); exact Or.inl (h.trans h1.symm)]
                · simp only [V', Finset.mem_insert, not_or]
                  refine ⟨fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_),
                          fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_), hr2⟩
                  · rcases hy'_eq with ⟨h1, _⟩ | ⟨_, h2⟩ <;> [exact Or.inr (Or.inr (Or.inl (h.trans h1.symm))); exact Or.inr (Or.inr (Or.inr (h.trans h2.symm)))]
                  · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩ <;> [exact Or.inr (Or.inr (Or.inr (h.trans h2.symm))); exact Or.inr (Or.inr (Or.inl (h.trans h1.symm)))]
          · rw [List.countP_eq_length_filter] at hWcnt ⊢
            have hperm_len := hperm'.length_eq
            have hins_filt : ins.filter (·.2.2) = [(y, y', true)] := by simp [ins]
            rw [hins_filt, List.length_append] at hperm_len
            simp only [List.length_singleton] at hperm_len
            have huniq_q : ∀ r ∈ ch, (r.1 = y ∨ r.1 = y') → r = q := by
              intro r hr h
              refine nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_
              rcases h with h | h
              · rcases hy'_eq with ⟨h1, _⟩ | ⟨_, h2⟩
                · exact Or.inl (h.trans h1.symm)
                · exact Or.inr (Or.inl (h.trans h2.symm))
              · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩
                · exact Or.inr (Or.inl (h.trans h2.symm))
                · exact Or.inl (h.trans h1.symm)
            rw [hperm_len, hWcnt, filter_length_insert_two ch hch_nodup V y y' q hq_ch hy'_eq huniq_q hyV hy'V]
            omega
          · have hperm_flat : List.Perm ((W'.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1]))
                (y :: y' :: (W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])) := by
              have h1 := hperm'.flatMap (fun e _ => List.Perm.refl [e.1, e.2.1])
              simpa [ins] using h1
            rw [hperm_flat.nodup_iff, List.nodup_cons, List.nodup_cons]
            refine ⟨?_, ?_, hWnodup⟩
            · intro h
              rcases List.mem_cons.mp h with hy0 | h
              · exact hyy' hy0
              · rw [List.mem_flatMap] at h
                rcases h with ⟨e, he, hye⟩
                have heW : e ∈ W := (List.mem_filter.mp he).1
                rcases List.mem_cons.mp hye with hye | hye
                · exact hyV (hye ▸ (hWV e heW).1)
                · rw [List.mem_singleton] at hye
                  exact hyV (hye ▸ (hWV e heW).2)
            · rw [List.mem_flatMap]
              rintro ⟨e, he, hy'e⟩
              have heW : e ∈ W := (List.mem_filter.mp he).1
              rcases List.mem_cons.mp hy'e with hy'e | hy'e
              · exact hy'V (hy'e ▸ (hWV e heW).1)
              · rw [List.mem_singleton] at hy'e
                exact hy'V (hy'e ▸ (hWV e heW).2)
        · push_neg at hy_ch
          set ins : List (Fin t × Fin t × Bool) := [(x, y, false), (y, x, false)]
          have hins_ne : ins ≠ [] := by simp [ins]
          have hins_chain : ins.IsChain (fun a b => a.2.1 = b.1) := by
            simp only [ins]
            exact List.IsChain.cons_cons rfl (List.IsChain.singleton _)
          obtain ⟨hne', hhead', hlast', hlen', hchain', hmem', hperm'⟩ :=
            spliceAt_props x ins W hWne ⟨ex, hexW, hex1⟩ hWchain hins_ne rfl rfl hins_chain
          set W' := spliceAt x ins W
          set V' := insert y V
          have hV'card : V'.card = V.card + 1 := Finset.card_insert_of_notMem hyV
          have hV't : V'.card ≤ t := by simpa using Finset.card_le_univ V'
          have hlt : t - V'.card < n := by omega
          refine ih _ hlt W' V' rfl hne' ?_ hchain' ?_ ?_ ?_ ?_ ?_ ?_ (by omega) ?_ ?_ ?_
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he_ins
              rcases he_ins with rfl | rfl
              · exact hxyAdj
              · exact hxyAdj.symm
            · exact hWadj e he_W
          · intro h'; rw [hlast' h', hhead' h', hWwrap hWne]
          · intro h'; rw [hlast' h', hWlastf hWne]
          · exact Finset.mem_insert_of_mem hu1V
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he_ins
              rcases he_ins with rfl | rfl
              · exact ⟨Finset.mem_insert_of_mem hxV, Finset.mem_insert_self _ _⟩
              · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hxV⟩
            · have := hWV e he_W
              exact ⟨Finset.mem_insert_of_mem this.1, Finset.mem_insert_of_mem this.2⟩
          · intro v hv
            rcases Finset.mem_insert.mp hv with hvy | hv
            · exact ⟨(y, x, false), (hmem' _).mpr (Or.inl (by simp [ins])), hvy.symm⟩
            · obtain ⟨e, heW, he1⟩ := hVW v hv
              exact ⟨e, (hmem' _).mpr (Or.inr heW), he1⟩
          · rw [hlen', hV'card, hWlen]; simp [ins]; omega
          · intro r hr
            rcases hchInv r hr with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
            · exact Or.inl ⟨Finset.mem_insert_of_mem hr1, Finset.mem_insert_of_mem hr2⟩
            · exact Or.inr ⟨fun h => by
                  rcases Finset.mem_insert.mp h with h | h
                  · exact (hy_ch r hr).1 h
                  · exact hr1 h,
                fun h => by
                  rcases Finset.mem_insert.mp h with h | h
                  · exact (hy_ch r hr).2 h
                  · exact hr2 h⟩
          · rw [List.countP_eq_length_filter] at hWcnt ⊢
            have hperm_len := hperm'.length_eq
            have hins_filt : ins.filter (·.2.2) = [] := by simp [ins]
            rw [hins_filt, List.nil_append] at hperm_len
            have hcongr : ch.filter (fun r => decide (r.1 ∈ V')) = ch.filter (fun r => decide (r.1 ∈ V)) := by
              refine List.filter_congr fun r hr => ?_
              have hry : r.1 ≠ y := fun h => (hy_ch r hr).1 h
              simp [V', hry]
            rw [hperm_len, hWcnt, hcongr]
          · have hperm_flat : List.Perm ((W'.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1]))
                ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])) := by
              have h1 := hperm'.flatMap (fun e _ => List.Perm.refl [e.1, e.2.1])
              simpa [ins] using h1
            exact hperm_flat.nodup_iff.mpr hWnodup
  have hchInv₀ : ∀ p ∈ ch, (p.1 ∈ V₀ ∧ p.2 ∈ V₀) ∨ (p.1 ∉ V₀ ∧ p.2 ∉ V₀) := by
    intro p hp
    by_cases hp1 : p = (u₁, v₁)
    · subst hp1; exact Or.inl ⟨by simp [V₀], by simp [V₀]⟩
    · refine Or.inr ⟨?_, ?_⟩
      · simp only [V₀, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (Or.inl h)),
               fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (Or.inr (Or.inl h)))⟩
      · simp only [V₀, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (Or.inr (Or.inr (Or.inl h)))),
               fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (Or.inr (Or.inr (Or.inr h))))⟩
  have hWcnt₀ : W₀.countP (·.2.2) = (ch.filter (fun p => decide (p.1 ∈ V₀))).length := by
    have hfilt : ch.filter (fun p => decide (p.1 ∈ V₀)) = [(u₁, v₁)] := by
      simp only [ch, List.filter_cons, decide_eq_true (by simp [V₀] : u₁ ∈ V₀),
        ↓reduceIte, List.cons.injEq, true_and]
      rw [List.filter_eq_nil_iff]
      intro p hp
      have hne1 : p ≠ (u₁, v₁) := by
        intro h; subst h
        simp only [ch, List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hchosen_nodup
        exact hchosen_nodup.1 (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(u₁, v₁), hp, List.mem_cons_self⟩))
      have hp_out : p.1 ∉ V₀ := by
        rcases hchInv₀ p (List.mem_cons_of_mem _ hp) with h | h
        · exfalso
          exact hne1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem (List.mem_cons_of_mem _ hp)
            (Or.inl (by
              rcases Finset.mem_insert.mp h.1 with h1 | h1
              · exact h1
              · rw [Finset.mem_singleton] at h1
                exfalso; exact hne1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem
                  (List.mem_cons_of_mem _ hp) (Or.inr (Or.inl h1))))))
        · exact h.1
      simp [hp_out]
    simp [W₀, hfilt]
  refine hstep (t - V₀.card) W₀ V₀ rfl (by simp [W₀]) ?_ ?_ (by simp [W₀]) (by simp [W₀])
    (by simp [V₀]) ?_ ?_ (by simp [W₀, hV₀_card]) (by omega) hchInv₀ hWcnt₀ ?_
  · intro e he
    simp only [W₀, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact h1_adj
    · exact h1_adj.symm
  · exact List.IsChain.cons_cons rfl (List.IsChain.singleton _)
  · intro e he
    simp only [W₀, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [V₀]
  · intro v hv
    simp only [V₀, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hvu | hvv
    · rw [hvu]; exact ⟨(u₁, v₁, true), by simp [W₀], rfl⟩
    · rw [hvv]; exact ⟨(v₁, u₁, false), by simp [W₀], rfl⟩
  · simp [W₀, huv1]

/-! ### Length assignment and cycle assembly -/

private def assignList {α : Type*} (B : ℕ) (W : List (α × α × Bool)) (D : ℕ) : List ℕ :=
  match W with
  | [] => []
  | e :: rest =>
    if e.2.2 then min B D :: assignList B rest (D - min B D)
    else 0 :: assignList B rest D

private lemma assignList_length {α : Type*} (B : ℕ) :
    ∀ (W : List (α × α × Bool)) (D : ℕ), (assignList B W D).length = W.length := by
  intro W
  induction W with
  | nil => intro D; simp [assignList]
  | cons e rest ih =>
    intro D
    unfold assignList
    by_cases hf : e.2.2 = true <;> simp [hf, ih]

private lemma assignList_props {α : Type*} (B : ℕ) :
    ∀ (W : List (α × α × Bool)) (D : ℕ),
      D ≤ W.countP (·.2.2) * B →
      (assignList B W D).length = W.length ∧
      (assignList B W D).sum = D ∧
      (∀ i (hi : i < W.length), (assignList B W D)[i]'(assignList_length B W D ▸ hi) ≤ B) ∧
      (∀ i (hi : i < W.length), W[i].2.2 = false →
        (assignList B W D)[i]'(assignList_length B W D ▸ hi) = 0) := by
  intro W
  induction W with
  | nil =>
    intro D hD
    simp [assignList] at hD ⊢
    omega
  | cons e rest ih =>
    intro D hD
    by_cases hf : e.2.2 = true
    · have hD' : D - min B D ≤ rest.countP (·.2.2) * B := by
        have hcnt : (e :: rest).countP (·.2.2) = rest.countP (·.2.2) + 1 := by
          simp [List.countP_cons, hf]
        rw [hcnt, Nat.add_one_mul] at hD
        by_cases hBD : B ≤ D
        · rw [min_eq_left hBD]; omega
        · rw [min_eq_right (Nat.le_of_not_le hBD)]; simp
      obtain ⟨hlen, hsum, hleB, hzero⟩ := ih (D - min B D) hD'
      refine ⟨assignList_length B (e :: rest) D, ?_, ?_, ?_⟩
      · simp only [assignList, if_pos hf, List.sum_cons, hsum]; omega
      · intro i hi
        rcases i with _ | i
        · simp only [assignList, if_pos hf, List.getElem_cons_zero]; exact min_le_left B D
        · simp only [assignList, if_pos hf, List.getElem_cons_succ]
          exact hleB i (by simpa using hi)
      · intro i hi hif
        rcases i with _ | i
        · simp [hf] at hif
        · simp only [assignList, if_pos hf, List.getElem_cons_succ]
          exact hzero i (by simpa using hi) (by simpa using hif)
    · have hf' : e.2.2 = false := Bool.eq_false_iff.mpr hf
      have hcnt : (e :: rest).countP (·.2.2) = rest.countP (·.2.2) := by
        simp [List.countP_cons, hf']
      rw [hcnt] at hD
      obtain ⟨hlen, hsum, hleB, hzero⟩ := ih D hD
      refine ⟨assignList_length B (e :: rest) D, ?_, ?_, ?_⟩
      · simp only [assignList, if_neg hf, List.sum_cons, zero_add, hsum]
      · intro i hi
        rcases i with _ | i
        · simp only [assignList, if_neg hf, List.getElem_cons_zero]; omega
        · simp only [assignList, if_neg hf, List.getElem_cons_succ]
          exact hleB i (by simpa using hi)
      · intro i hi hif
        rcases i with _ | i
        · simp only [assignList, if_neg hf, List.getElem_cons_zero]
        · simp only [assignList, if_neg hf, List.getElem_cons_succ]
          exact hzero i (by simpa using hi) (by simpa using hif)

private lemma sum_range_eq_list_sum : ∀ (l : List ℕ) (f : ℕ → ℕ),
    (∀ i (hi : i < l.length), f i = l[i]) →
    ∑ i ∈ Finset.range l.length, f i = l.sum := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    intro f hf
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, add_comm]
    congr 1
    · exact hf 0 (Nat.zero_lt_succ _)
    · exact ih (fun i => f (i + 1)) (fun i hi => by
        rw [hf (i + 1) (Nat.succ_lt_succ hi), List.getElem_cons_succ])

private lemma cycleGraph_of_cycleList {N n : ℕ} (G : SimpleGraph (Fin N)) (hn4 : 4 ≤ n)
    (cyc : List (Fin N)) (hlen : cyc.length = n) (hnodup : cyc.Nodup)
    (hstep : ∀ i (hi : i + 1 < cyc.length), G.Adj cyc[i] cyc[i + 1])
    (hwrap : ∀ h : 0 < cyc.length, G.Adj cyc[cyc.length - 1] cyc[0]) :
    (cycleGraph n).IsContained G := by
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  let f : Fin n → Fin N := fun i => cyc[i.val]'(hlen ▸ i.isLt)
  have hinj : Function.Injective f := by
    intro i j hij
    exact Fin.ext (congrArg (@Fin.val cyc.length)
      (List.nodup_iff_injective_getElem.mp hnodup (a₁ := ⟨i.val, hlen ▸ i.isLt⟩) (a₂ := ⟨j.val, hlen ▸ j.isLt⟩) hij))
  let hhom : (cycleGraph n) →g G := ⟨f, by
    intro a b hab
    have hcases : (a - b).val = 1 ∨ (b - a).val = 1 := SimpleGraph.cycleGraph_adj'.mp hab
    have step_adj : ∀ x y : Fin n, (y - x).val = 1 → G.Adj (f x) (f y) := by
      intro x y hxy
      have hy_val : y.val = (x.val + 1) % n := by
        rw [Fin.coe_sub] at hxy
        by_cases hle : x.val ≤ y.val
        · have h1 : y.val - x.val = 1 := by
            rw [show (n - x.val + y.val) % n = (n + (y.val - x.val)) % n by congr 1; omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hxy
            exact hxy
          have : x.val + 1 < n := by omega
          rw [Nat.mod_eq_of_lt this]; omega
        · have h1 : n - x.val + y.val = 1 := by
            rw [Nat.mod_eq_of_lt (by omega)] at hxy; exact hxy
          have hx_last : x.val = n - 1 := by omega
          have hy0 : y.val = 0 := by omega
          rw [hx_last, show n - 1 + 1 = n by omega, Nat.mod_self, hy0]
      rcases eq_or_ne (x.val + 1) n with hlast | hlt
      · have hy0 : y.val = 0 := by rw [hy_val, hlast, Nat.mod_self]
        have hxlast : x.val = cyc.length - 1 := by omega
        simpa [f, hxlast, hy0] using hwrap (hlen ▸ hn0)
      · have hlt' : x.val + 1 < cyc.length := by omega
        have hy' : y.val = x.val + 1 := by rw [hy_val, Nat.mod_eq_of_lt (by omega)]
        simpa [f, hy'] using hstep x.val hlt'
    rcases hcases with h | h
    · exact (step_adj b a h).symm
    · exact step_adj a b h⟩
  exact ⟨⟨hhom, fun i j h => hinj h⟩⟩

private lemma assemble_cycle {N n L : ℕ} (G : SimpleGraph (Fin N)) (hn4 : 4 ≤ n) (hL : 0 < L)
    (z : ℕ → Fin N) (segs : ℕ → List (Fin N))
    (hne : ∀ i < L, segs i ≠ [])
    (hhead : ∀ i < L, ∀ h : segs i ≠ [], (segs i).head h = z i)
    (hnodup : ∀ i < L, (segs i).Nodup)
    (hchain : ∀ i < L, (segs i).IsChain G.Adj)
    (hnext : ∀ i < L, ∀ h : segs i ≠ [], G.Adj ((segs i).getLast h) (z ((i + 1) % L)))
    (hdisj : ∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ → Disjoint (segs i₁).toFinset (segs i₂).toFinset)
    (hsum : ∑ i ∈ Finset.range L, (segs i).length = n) :
    (cycleGraph n).IsContained G := by
  have hbuild : ∀ k : ℕ, 1 ≤ k → k ≤ L →
      let pref := (List.range k).flatMap segs
      pref ≠ [] ∧
      (∀ h : pref ≠ [], pref.head h = z 0) ∧
      (∀ h : pref ≠ [], ∀ hk : segs (k - 1) ≠ [], pref.getLast h = (segs (k - 1)).getLast hk) ∧
      pref.Nodup ∧
      pref.IsChain G.Adj ∧
      pref.toFinset = (Finset.range k).biUnion (fun i => (segs i).toFinset) ∧
      pref.length = ∑ i ∈ Finset.range k, (segs i).length := by
    intro k hk1 hkL
    induction k with
    | zero => omega
    | succ k ih =>
      rcases eq_or_lt_of_le hk1 with hkeq1 | hkgt1
      · have hk0 : k = 0 := by omega
        subst hk0
        have h0ne : segs 0 ≠ [] := hne 0 hL
        refine ⟨by simpa using h0ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro _; simpa using hhead 0 hL h0ne
        · intro _ _; simp
        · simpa using hnodup 0 hL
        · simpa using hchain 0 hL
        · simp
        · simp
      · have hk1' : 1 ≤ k := by omega
        obtain ⟨hpne, hphead, hplast, hpnodup, hpchain, hpfin, hplen⟩ := ih hk1' (by omega)
        have hkne : segs k ≠ [] := hne k hkL
        have hk1ne : segs (k - 1) ≠ [] := hne (k - 1) (by omega)
        have heq_cat : (List.range (k + 1)).flatMap segs = (List.range k).flatMap segs ++ segs k := by
          rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        rw [heq_cat]
        set pref := (List.range k).flatMap segs
        have hne' : pref ++ segs k ≠ [] := List.append_ne_nil_of_right_ne_nil _ hkne
        have hdisj_k : Disjoint pref.toFinset (segs k).toFinset := by
          rw [hpfin, Finset.disjoint_biUnion_left]
          intro i hi
          exact hdisj i (by rw [Finset.mem_range] at hi; omega) k hkL (by rw [Finset.mem_range] at hi; omega)
        refine ⟨hne', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro h'
          rw [List.head_append_of_ne_nil hpne, hphead hpne]
        · intro h' _
          simpa using List.getLast_append_of_ne_nil h' hkne
        · rw [List.nodup_append]
          refine ⟨hpnodup, hnodup k hkL, fun a ha b hb heq => ?_⟩
          subst heq
          exact Finset.disjoint_left.mp hdisj_k (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb)
        · refine isChain_append hpchain (hchain k hkL) ?_
          intro a ha b hb
          have ha' : a = pref.getLast hpne := (by
            rw [List.getLast?_eq_some_getLast hpne] at ha; simpa using ha : pref.getLast hpne = a).symm
          have hb' : b = (segs k).head hkne := (by
            rw [List.head?_eq_some_head hkne] at hb; simpa using hb : (segs k).head hkne = b).symm
          subst ha'; subst hb'
          rw [hplast hpne hk1ne, hhead k hkL hkne]
          have hmod : (k - 1 + 1) % L = k := by
            rw [show k - 1 + 1 = k by omega, Nat.mod_eq_of_lt hkL]
          simpa [hmod] using hnext (k - 1) (by omega) hk1ne
        · rw [List.toFinset_append, hpfin, Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
        · rw [List.length_append, hplen, Finset.sum_range_succ]
  obtain ⟨hcyne, hcyhead, hcylast, hcynodup, hcychain, _, hcylen⟩ := hbuild L hL le_rfl
  set cyc := (List.range L).flatMap segs
  have hL1ne : segs (L - 1) ≠ [] := hne (L - 1) (by omega)
  refine cycleGraph_of_cycleList G hn4 cyc (hcylen.trans hsum) hcynodup ?_ ?_
  · intro i hi
    exact List.isChain_iff_getElem.mp hcychain i hi
  · intro h0
    have hne' : cyc ≠ [] := List.ne_nil_of_length_pos h0
    have hlast_eq : cyc[cyc.length - 1] = cyc.getLast hne' := (List.getLast_eq_getElem hne').symm
    have hhead_eq : cyc[0] = cyc.head hne' := (List.head_eq_getElem hne').symm
    rw [hlast_eq, hhead_eq, hcylast hne' hL1ne, hcyhead hne']
    have hmod : (L - 1 + 1) % L = 0 := by rw [show L - 1 + 1 = L by omega, Nat.mod_self]
    simpa [hmod] using hnext (L - 1) (by omega) hL1ne

/-! ### Bridge segment for a blown-up matching step -/

private lemma true_indices_disjoint {α : Type*} [DecidableEq α] :
    ∀ (W : List (α × α × Bool)),
      ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup →
      ∀ (i₁ i₂ : ℕ) (hi₁ : i₁ < W.length) (hi₂ : i₂ < W.length),
        i₁ < i₂ → W[i₁].2.2 = true → W[i₂].2.2 = true →
        Disjoint ({W[i₁].1, W[i₁].2.1} : Finset α) ({W[i₂].1, W[i₂].2.1} : Finset α) := by
  intro W
  induction W with
  | nil => intro _ i₁ _ hi₁; simp at hi₁
  | cons e rest ih =>
    intro hnodup i₁ i₂ hi₁ hi₂ hlt h1 h2
    have hnodup_rest : ((rest.filter (·.2.2)).flatMap (fun x => [x.1, x.2.1])).Nodup := by
      by_cases he : e.2.2 = true
      · simp only [List.filter_cons, he, ↓reduceIte, List.flatMap_cons, List.cons_append,
          List.nil_append, List.nodup_cons] at hnodup
        exact hnodup.2.2
      · have he' : e.2.2 = false := Bool.eq_false_iff.mpr he
        simp only [List.filter_cons, he', Bool.false_eq_true, ↓reduceIte] at hnodup
        exact hnodup
    rcases i₁ with _ | j₁ <;> rcases i₂ with _ | j₂
    · omega
    · simp only [List.getElem_cons_zero] at h1
      simp only [List.filter_cons, h1, ↓reduceIte, List.flatMap_cons, List.cons_append,
        List.nil_append, List.nodup_cons] at hnodup
      have hj₂ : j₂ < rest.length := by simpa using hi₂
      have hmem : rest[j₂]'hj₂ ∈ rest.filter (·.2.2) :=
        List.mem_filter.mpr ⟨List.getElem_mem hj₂, by simpa using h2⟩
      have hm1 : (rest[j₂]'hj₂).1 ∈ (rest.filter (·.2.2)).flatMap (fun x => [x.1, x.2.1]) :=
        List.mem_flatMap.mpr ⟨rest[j₂]'hj₂, hmem, by simp⟩
      have hm2 : (rest[j₂]'hj₂).2.1 ∈ (rest.filter (·.2.2)).flatMap (fun x => [x.1, x.2.1]) :=
        List.mem_flatMap.mpr ⟨rest[j₂]'hj₂, hmem, by simp⟩
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, Finset.mem_insert,
        Finset.mem_singleton] at hz1 hz2
      rcases hz1 with rfl | rfl <;> rcases hz2 with heq | heq
      · exact hnodup.1 (List.mem_cons_of_mem _ (heq ▸ hm1))
      · exact hnodup.1 (List.mem_cons_of_mem _ (heq ▸ hm2))
      · exact hnodup.2.1 (heq ▸ hm1)
      · exact hnodup.2.1 (heq ▸ hm2)
    · omega
    · exact ih hnodup_rest j₁ j₂ (by simpa using hi₁) (by simpa using hi₂) (by omega)
        (by simpa using h1) (by simpa using h2)

private lemma bridge_segment {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η) (hd_gt : η < d)
    {U V ResU CapU BodyU BodyV : Finset (Fin N)}
    (hResU : ResU ⊆ U) (hCapU : CapU ⊆ U) (hBodyU : BodyU ⊆ U) (hBodyV : BodyV ⊆ V)
    (hdisjUV : Disjoint U V)
    (hRC : Disjoint ResU CapU) (hRB : Disjoint ResU BodyU) (hCB : Disjoint CapU BodyU)
    (huni : G.IsUniform η U V) (hd : d ≤ (G.edgeDensity U V : ℝ))
    (hUpos : 0 < U.card) (hVpos : 0 < V.card)
    (c : ℕ) (hcU : (U.card : ℝ) * η ≤ (c : ℝ)) (hcV : (V.card : ℝ) * η ≤ (c : ℝ))
    (hcBodyU : (c : ℝ) ≤ (d - η) * (BodyU.card : ℝ))
    (hCapCard : (U.card : ℝ) * η ≤ (CapU.card : ℝ))
    (hBodyUcard : (U.card : ℝ) * η ≤ (BodyU.card : ℝ))
    (hBodyVcard : (V.card : ℝ) * η ≤ (BodyV.card : ℝ))
    {zu zv : Fin N} (hzu : zu ∈ ResU)
    (hzu_deg : (d - η) * (BodyV.card : ℝ) < ((G.neighborFinset zu ∩ BodyV).card : ℝ))
    (hzv_deg : (d - η) * (CapU.card : ℝ) < ((G.neighborFinset zv ∩ CapU).card : ℝ))
    (hSend_big : (U.card : ℝ) * η ≤ (d - η) * (CapU.card : ℝ))
    (hPool_big : 3 * ((max U.card V.card : ℝ) * η + 1) ≤ (d - η) * (BodyV.card : ℝ))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ_len : ℓ ≤ min (BodyV.card - c) BodyU.card - 2 * c) :
    ∃ seg : List (Fin N),
      seg ≠ [] ∧
      seg.length = 2 * ℓ + 1 ∧
      (∀ h : seg ≠ [], seg.head h = zu) ∧
      (∀ h : seg ≠ [], G.Adj (seg.getLast h) zv) ∧
      seg.Nodup ∧
      seg.IsChain G.Adj ∧
      seg.toFinset ⊆ insert zu (BodyU ∪ BodyV ∪ CapU) := by
  set S_end := G.neighborFinset zv ∩ CapU
  have hSend_sub : S_end ⊆ U := Finset.inter_subset_right.trans hCapU
  have hSend_card : (U.card : ℝ) * η ≤ (S_end.card : ℝ) := hSend_big.trans hzv_deg.le
  have huniVU : G.IsUniform η V U := huni.symm
  have hdVU : d ≤ (G.edgeDensity V U : ℝ) := by rwa [SimpleGraph.edgeDensity_comm]
  set B_bad := V.filter (fun y => ((G.neighborFinset y ∩ S_end).card : ℝ) ≤ (d - η) * (S_end.card : ℝ))
  have hB_bad : (B_bad.card : ℝ) < (V.card : ℝ) * η :=
    card_bad_lt G hη huniVU hdVU hVpos hUpos hSend_sub hSend_card
  set Body'V := BodyV \ B_bad
  have hBody'V_sub : Body'V ⊆ V := Finset.sdiff_subset.trans hBodyV
  have hBody'V_card : BodyV.card - c ≤ Body'V.card := by
    have hB_le : B_bad.card ≤ c := by
      have h1 : (B_bad.card : ℝ) < (c : ℝ) := hB_bad.trans_le hcV
      exact_mod_cast h1.le
    have h2 : BodyV.card ≤ Body'V.card + B_bad.card := by
      calc BodyV.card ≤ (Body'V ∪ B_bad).card := Finset.card_le_card (fun x hx => by
            by_cases h : x ∈ B_bad
            · exact Finset.mem_union_right _ h
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩))
        _ ≤ Body'V.card + B_bad.card := Finset.card_union_le _ _
    omega
  set P := G.neighborFinset zu ∩ Body'V
  have hP_sub : P ⊆ V := Finset.inter_subset_right.trans hBody'V_sub
  have hP_card : ((∅ : Finset (Fin N)).card : ℝ) + 2 * (V.card : ℝ) * η ≤ (P.card : ℝ) := by
    have h1 : (G.neighborFinset zu ∩ BodyV).card ≤ P.card + B_bad.card := by
      calc (G.neighborFinset zu ∩ BodyV).card
          ≤ (P ∪ B_bad).card := Finset.card_le_card (fun x hx => by
              rw [Finset.mem_inter] at hx
              by_cases h : x ∈ B_bad
              · exact Finset.mem_union_right _ h
              · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx.1, Finset.mem_sdiff.mpr ⟨hx.2, h⟩⟩))
        _ ≤ P.card + B_bad.card := Finset.card_union_le _ _
    have h1r : ((G.neighborFinset zu ∩ BodyV).card : ℝ) ≤ (P.card : ℝ) + (B_bad.card : ℝ) := by
      exact_mod_cast h1
    have hmaxV : (V.card : ℝ) ≤ (max U.card V.card : ℝ) := by exact_mod_cast le_max_right U.card V.card
    simp only [Finset.card_empty, Nat.cast_zero, zero_add]
    nlinarith
  obtain ⟨y₁, hy₁P, _, hy₁_BodyU, _⟩ := exists_good_two G hη hP_sub hVpos huniVU hdVU
    hUpos hBodyU hBodyUcard huniVU hdVU hUpos hBodyU hBodyUcard hP_card
  have hy₁_Body'V : y₁ ∈ Body'V := (Finset.mem_inter.mp hy₁P).2
  have hzy₁ : G.Adj zu y₁ := (G.mem_neighborFinset zu y₁).mp (Finset.mem_inter.mp hy₁P).1
  have hy₁_deg : c ≤ (G.neighborFinset y₁ ∩ BodyU).card := by
    exact_mod_cast (hcBodyU.trans_lt hy₁_BodyU).le
  have hc_pos : 0 < c := by
    have h1 : (0 : ℝ) < (U.card : ℝ) * η := by positivity
    exact_mod_cast h1.trans_le hcU
  have hdisj_BU : Disjoint Body'V BodyU :=
    hdisjUV.symm.mono hBody'V_sub hBodyU
  have hnoempty : ∀ X ⊆ Body'V, ∀ Y ⊆ BodyU, c ≤ X.card → c ≤ Y.card →
      ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y :=
    no_empty_pair_of_uniform G hd_gt huniVU hdVU hBody'V_sub hBodyU hcV hcU
  obtain ⟨Q, hQne, hQhead, hQnodup, hQchain, hQsub, hQlen, hQalt⟩ :=
    dfs_long_path G Body'V BodyU hdisj_BU hc_pos hc_pos hnoempty y₁ hy₁_Body'V hy₁_deg
  have htake_le : 2 * ℓ - 1 ≤ Q.length := by
    have h1 : min (BodyV.card - c) BodyU.card ≤ min Body'V.card BodyU.card := by omega
    omega
  set Q' := Q.take (2 * ℓ - 1)
  have hQ'len : Q'.length = 2 * ℓ - 1 := List.length_take_of_le htake_le
  have hQ'ne : Q' ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hQ'head : Q'.head hQ'ne = y₁ := by
    rw [List.head_eq_getElem hQ'ne]
    simp only [Q', List.getElem_take]
    rw [← List.head_eq_getElem hQne, ← Option.some.injEq]
    rw [List.head?_eq_some_head hQne] at hQhead
    exact hQhead
  have hQ'nodup : Q'.Nodup := hQnodup.take
  have hQ'chain : Q'.IsChain G.Adj := by
    have h1 : Q'.IsChain (bipartAdj G Body'V BodyU) := hQchain.take (2 * ℓ - 1)
    exact h1.imp (fun {_ _} h => h.2)
  have hQ'sub : Q'.toFinset ⊆ BodyU ∪ BodyV := by
    intro x hx
    have hxQ : x ∈ Q := List.mem_of_mem_take (List.mem_toFinset.mp hx)
    rcases Finset.mem_union.mp (hQsub (List.mem_toFinset.mpr hxQ)) with hV | hU
    · exact Finset.mem_union_right _ (Finset.sdiff_subset hV)
    · exact Finset.mem_union_left _ hU
  set y_last := Q'.getLast hQ'ne
  have hy_last_eq : y_last = Q[2 * ℓ - 2]'(by omega) := by
    change Q'.getLast hQ'ne = Q[2 * ℓ - 2]'(by omega)
    rw [List.getLast_eq_getElem hQ'ne]
    simp only [Q', hQ'len]
    exact List.getElem_take
  have hy_last_Body'V : y_last ∈ Body'V := by
    rw [hy_last_eq]
    exact (hQalt (2 * ℓ - 2) (by omega)).1 ⟨ℓ - 1, by omega⟩
  have hy_last_bad : y_last ∉ B_bad := (Finset.mem_sdiff.mp hy_last_Body'V).2
  have hy_last_V : y_last ∈ V := hBody'V_sub hy_last_Body'V
  have hy_last_deg : (d - η) * (S_end.card : ℝ) < ((G.neighborFinset y_last ∩ S_end).card : ℝ) := by
    by_contra! hle
    exact hy_last_bad (Finset.mem_filter.mpr ⟨hy_last_V, hle⟩)
  have hy_last_pos : 0 < (G.neighborFinset y_last ∩ S_end).card := by
    have hSpos : (0 : ℝ) < (S_end.card : ℝ) := by
      have : (0 : ℝ) < (U.card : ℝ) * η := by positivity
      exact this.trans_le hSend_card
    have h1 : (0 : ℝ) < (d - η) * (S_end.card : ℝ) := mul_pos (sub_pos.mpr hd_gt) hSpos
    exact_mod_cast h1.trans hy_last_deg
  obtain ⟨x_last, hx_last⟩ := Finset.card_pos.mp hy_last_pos
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hx_last
  have hx_last_CapU : x_last ∈ CapU := (Finset.mem_inter.mp hx_last.2).2
  have hx_last_zv : G.Adj x_last zv :=
    ((G.mem_neighborFinset zv x_last).mp (Finset.mem_inter.mp hx_last.2).1).symm
  set seg := zu :: (Q' ++ [x_last])
  have hseg_ne : seg ≠ [] := by simp [seg]
  have hzu_not_BUV : zu ∉ BodyU ∪ BodyV := by
    intro h
    rcases Finset.mem_union.mp h with hU | hV
    · exact Finset.disjoint_left.mp hRB hzu hU
    · exact Finset.disjoint_left.mp hdisjUV (hResU hzu) (hBodyV hV)
  have hx_not_BUV : x_last ∉ BodyU ∪ BodyV := by
    intro h
    rcases Finset.mem_union.mp h with hU | hV
    · exact Finset.disjoint_left.mp hCB hx_last_CapU hU
    · exact Finset.disjoint_left.mp hdisjUV (hCapU hx_last_CapU) (hBodyV hV)
  have hzu_ne_x : zu ≠ x_last := fun h =>
    Finset.disjoint_left.mp hRC hzu (h ▸ hx_last_CapU)
  refine ⟨seg, hseg_ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [seg, hQ'len]; omega
  · intro _; simp [seg]
  · intro _
    have h1 : seg.getLast hseg_ne = (Q' ++ [x_last]).getLast (by simp) :=
      List.getLast_cons (by simp)
    rw [h1, List.getLast_append_singleton]
    exact hx_last_zv
  · rw [show seg = zu :: (Q' ++ [x_last]) from rfl, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨fun h => hzu_not_BUV (hQ'sub (List.mem_toFinset.mpr h)), hzu_ne_x⟩
    · rw [List.nodup_append]
      refine ⟨hQ'nodup, List.nodup_singleton _, fun a ha b hb heq => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb; subst heq
      exact hx_not_BUV (hQ'sub (List.mem_toFinset.mpr ha))
  · refine List.IsChain.cons_of_ne_nil (by simp) ?_ ?_
    · refine isChain_append hQ'chain (List.isChain_singleton _) ?_
      intro a ha b hb
      have ha' : a = y_last := (by
        rw [List.getLast?_eq_some_getLast hQ'ne] at ha; simpa using ha : y_last = a).symm
      have hb' : b = x_last := (by simpa using hb : x_last = b).symm
      subst ha'; subst hb'
      exact hx_last.1
    · rw [List.head_append_of_ne_nil hQ'ne, hQ'head]
      exact hzy₁
  · intro x hx
    simp only [seg, List.toFinset_cons, List.toFinset_append, List.toFinset_nil,
      Finset.mem_insert, Finset.mem_union, Finset.notMem_empty, or_false] at hx
    rcases hx with rfl | hxQ | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by
        have := hQ'sub hxQ
        rcases Finset.mem_union.mp this with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hx_last_CapU)

/-! ### Selecting tour transition vertices along closed walk W -/

set_option maxHeartbeats 800000 in
private lemma embed_tour_vertices {N t : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η)
    (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t))
    (hparts_pos : ∀ i : Fin t, 0 < (parts i).card)
    (hR : ∀ u v : Fin t, R.Adj u v → G.IsUniform η (parts u) (parts v) ∧ d ≤ (G.edgeDensity (parts u) (parts v) : ℝ))
    (Res Cap Body : Fin t → Finset (Fin N))
    (hRes_sub : ∀ i, Res i ⊆ parts i) (hCap_sub : ∀ i, Cap i ⊆ parts i) (hBody_sub : ∀ i, Body i ⊆ parts i)
    (hRes_sz : ∀ i j, (parts j).card * η ≤ (Res i).card)
    (hCap_sz : ∀ i j, (parts j).card * η ≤ (Cap i).card)
    (hBody_sz : ∀ i j, (parts j).card * η ≤ (Body i).card)
    (L : ℕ) (w w' : ℕ → Fin t)
    (hw_adj : ∀ i < L, R.Adj (w i) (w' i))
    (hw'_eq : ∀ i, i + 1 < L → w' i = w (i + 1))
    (hw_wrap : w' (L - 1) = w 0)
    (len : ℕ → ℕ)
    (hlen_L : len (L - 1) = 0)
    (hL_ge : 2 ≤ L)
    (hL2_len0 : L = 2 → 0 < len 0)
    (hPool_Res : ∀ i, (L : ℝ) + 2 * ((parts i).card : ℝ) * η ≤ (Res i).card)
    (hPool_Send : ∀ i j, (parts j).card * η ≤ (d - η) * (Res i).card ∧
      (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * (Res i).card)
    (hPool_Send2 : ∀ i j, (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * ((d - η) * (Res i).card)) :
    ∃ z : ℕ → Fin N,
      (∀ i < L, z i ∈ Res (w i)) ∧
      (∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ → z i₁ ≠ z i₂) ∧
      (∀ i (hi : i + 1 < L),
        if 0 < len i then (d - η) * ((Body (w' i)).card : ℝ) < ((G.neighborFinset (z i) ∩ Body (w' i)).card : ℝ)
        else if i + 1 < L - 1 then (d - η) * ((Res (w' i)).card : ℝ) < ((G.neighborFinset (z i) ∩ Res (w' i)).card : ℝ)
        else (d - η) * ((G.neighborFinset (z 0) ∩ Res (w (L - 1))).card : ℝ) <
          ((G.neighborFinset (z i) ∩ (G.neighborFinset (z 0) ∩ Res (w (L - 1)))).card : ℝ)) ∧
      (∀ i (hi : 0 < i) (hiL : i < L),
        if 0 < len (i - 1) then (d - η) * ((Cap (w (i - 1))).card : ℝ) < ((G.neighborFinset (z i) ∩ Cap (w (i - 1))).card : ℝ)
        else G.Adj (z (i - 1)) (z i)) ∧
      G.Adj (z (L - 1)) (z 0) := by
  classical
  let S_end : Fin N → Finset (Fin N) := fun z0 => G.neighborFinset z0 ∩ Res (w (L - 1))
  let TargetNext : Fin N → (i : ℕ) → i + 1 < L → Finset (Fin N) := fun z0 i _ =>
    if 0 < len i then Body (w' i)
    else if i + 1 < L - 1 then Res (w' i)
    else S_end z0
  have hT_sub : ∀ z0 i (hi : i + 1 < L), TargetNext z0 i hi ⊆ parts (w' i) := by
    intro z0 i hi
    simp only [TargetNext]
    split_ifs with h1 h2
    · exact hBody_sub _
    · exact hRes_sub _
    · have heq : w (L - 1) = w' i := by
        have hL1 : i + 1 = L - 1 := by omega
        rw [← hL1, ← hw'_eq i hi]
      rw [← heq]
      exact Finset.inter_subset_right.trans (hRes_sub _)
  have hbind : ∀ k : ℕ, 1 ≤ k → k ≤ L →
      ∃ z : ℕ → Fin N,
        (∀ i < k, z i ∈ Res (w i)) ∧
        (∀ i₁ < k, ∀ i₂ < k, i₁ ≠ i₂ → z i₁ ≠ z i₂) ∧
        (d - η) * ((Res (w (L - 1))).card : ℝ) < ((G.neighborFinset (z 0) ∩ Res (w (L - 1))).card : ℝ) ∧
        (∀ i (hi : i < k) (hi1 : i + 1 < L),
          (d - η) * ((TargetNext (z 0) i hi1).card : ℝ) <
            ((G.neighborFinset (z i) ∩ TargetNext (z 0) i hi1).card : ℝ)) ∧
        (∀ i (hi : 0 < i) (hik : i < k),
          if 0 < len (i - 1) then
            (d - η) * ((Cap (w (i - 1))).card : ℝ) < ((G.neighborFinset (z i) ∩ Cap (w (i - 1))).card : ℝ)
          else G.Adj (z (i - 1)) (z i)) ∧
        (k = L → G.Adj (z (L - 1)) (z 0)) := by
    intro k hk1 hkL
    induction k with
    | zero => omega
    | succ k ih =>
      rcases eq_or_lt_of_le hk1 with hkeq1 | hkgt1
      · have hk0 : k = 0 := by omega
        subst hk0
        have h0L : 0 + 1 < L := by omega
        let T1 := if 0 < len 0 then Body (w' 0) else Res (w' 0)
        have hT1_sub : T1 ⊆ parts (w' 0) := by
          dsimp [T1]; split_ifs <;> [exact hBody_sub _; exact hRes_sub _]
        have hT1_sz : (parts (w' 0)).card * η ≤ (T1.card : ℝ) := by
          dsimp [T1]; split_ifs <;> [exact hBody_sz _ _; exact hRes_sz _ _]
        have hR01 := hR (w 0) (w' 0) (hw_adj 0 (by omega))
        have hRL0 : R.Adj (w 0) (w (L - 1)) := by
          have := hw_adj (L - 1) (by omega)
          rw [hw_wrap] at this
          exact this.symm
        have hR0L := hR (w 0) (w (L - 1)) hRL0
        have hP0 : ((∅ : Finset (Fin N)).card : ℝ) + 2 * ((parts (w 0)).card : ℝ) * η ≤ (Res (w 0)).card := by
          simp only [Finset.card_empty, Nat.cast_zero, zero_add]
          exact le_trans (by linarith) (hPool_Res (w 0))
        obtain ⟨z0, hz0_Res, _, hz0_T1, hz0_SL⟩ := exists_good_two G hη (hRes_sub (w 0))
          (hparts_pos _) hR01.1 hR01.2 (hparts_pos _) hT1_sub hT1_sz
          hR0L.1 hR0L.2 (hparts_pos _) (hRes_sub _) (hRes_sz _ _) hP0
        refine ⟨fun _ => z0, ?_, ?_, hz0_SL, ?_, ?_, ?_⟩
        · intro i hi; rw [show i = 0 by omega]; exact hz0_Res
        · intro i₁ hi₁ i₂ hi₂ hne; omega
        · intro i hi hi1
          have hi0 : i = 0 := by omega
          subst hi0
          have hT_eq : TargetNext z0 0 hi1 = T1 := by
            dsimp [TargetNext, T1]
            by_cases h0 : 0 < len 0
            · simp [h0]
            · have hLne2 : L ≠ 2 := fun h2 => h0 (hL2_len0 h2)
              have h1L : 0 + 1 < L - 1 := by omega
              simp [h0, h1L]
          simpa [hT_eq] using hz0_T1
        · intro i hi hik; omega
        · intro hL1; omega
      · obtain ⟨z, hz_Res, hz_inj, hz0_SL, hz_next, hz_prev, _⟩ := ih (by omega) (by omega)
        set avoid := (Finset.range k).image z
        have havoid_card : avoid.card ≤ L :=
          (Finset.card_image_le.trans (Finset.card_range k).le).trans (by omega)
        have hSend_sz : (parts (w (L - 1))).card * η ≤ ((S_end (z 0)).card : ℝ) :=
          (hPool_Send (w (L - 1)) (w (L - 1))).1.trans hz0_SL.le
        have hT_sz : ∀ i (hi : i + 1 < L), (parts (w' i)).card * η ≤ ((TargetNext (z 0) i hi).card : ℝ) := by
          intro i hi
          dsimp [TargetNext]
          split_ifs with h1 h2
          · exact hBody_sz _ _
          · exact hRes_sz _ _
          · have heq : w (L - 1) = w' i := by
              have hL1 : i + 1 = L - 1 := by omega
              rw [← hL1, ← hw'_eq i hi]
            rw [← heq]
            exact hSend_sz
        have hk_w : w' (k - 1) = w k := by
          simpa [show k - 1 + 1 = k by omega] using hw'_eq (k - 1) (by omega)
        have hR_prev : R.Adj (w k) (w (k - 1)) := by
          have := hw_adj (k - 1) (by omega)
          rw [hk_w] at this
          exact this.symm
        have hR_prev_p := hR (w k) (w (k - 1)) hR_prev
        have hSend_sub_wk : S_end (z 0) ⊆ parts (w (L - 1)) := Finset.inter_subset_right.trans (hRes_sub _)
        have hpick : ∃ zk : Fin N,
            zk ∈ Res (w k) ∧ zk ∉ avoid ∧
            (if 0 < len (k - 1) then
              (d - η) * ((Cap (w (k - 1))).card : ℝ) < ((G.neighborFinset zk ∩ Cap (w (k - 1))).card : ℝ)
            else G.Adj (z (k - 1)) zk) ∧
            (∀ hk1L : k + 1 < L,
              (d - η) * ((TargetNext (z 0) k hk1L).card : ℝ) <
                ((G.neighborFinset zk ∩ TargetNext (z 0) k hk1L).card : ℝ)) ∧
            (k = L - 1 → G.Adj zk (z 0)) := by
          by_cases hlen_prev : 0 < len (k - 1)
          · by_cases hk1L : k + 1 < L
            · have hR_next := hR (w k) (w' k) (hw_adj k hkL)
              have hP : (avoid.card : ℝ) + 2 * ((parts (w k)).card : ℝ) * η ≤ (Res (w k)).card := by
                have hav : (avoid.card : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr havoid_card
                linarith only [hav, hPool_Res (w k)]
              obtain ⟨zk, hzkP, hzk_av, hzk_cap, hzk_next⟩ := exists_good_two G hη (hRes_sub (w k))
                (hparts_pos _) hR_prev_p.1 hR_prev_p.2 (hparts_pos _) (hCap_sub _) (hCap_sz _ _)
                hR_next.1 hR_next.2 (hparts_pos _) (hT_sub (z 0) k hk1L) (hT_sz k hk1L) hP
              refine ⟨zk, hzkP, hzk_av, by simp [hlen_prev, hzk_cap], fun _ => hzk_next, fun h => by omega⟩
            · have hk_eq : k = L - 1 := by omega
              have hP_sub : S_end (z 0) ⊆ parts (w k) := by rw [hk_eq]; exact hSend_sub_wk
              have hP : (avoid.card : ℝ) + 2 * ((parts (w k)).card : ℝ) * η ≤ ((S_end (z 0)).card : ℝ) := by
                have hav : (avoid.card : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr havoid_card
                have hps := (hPool_Send (w (L - 1)) (w k)).2
                rw [hk_eq] at hps ⊢
                linarith only [hav, hps, hz0_SL]
              obtain ⟨zk, hzkP, hzk_av, hzk_cap, _⟩ := exists_good_two G hη hP_sub
                (hparts_pos _) hR_prev_p.1 hR_prev_p.2 (hparts_pos _) (hCap_sub _) (hCap_sz _ _)
                hR_prev_p.1 hR_prev_p.2 (hparts_pos _) (hCap_sub _) (hCap_sz _ _) hP
              have hzk_Res : zk ∈ Res (w k) := by rw [hk_eq]; exact (Finset.mem_inter.mp hzkP).2
              have hzk_z0 : G.Adj zk (z 0) :=
                ((G.mem_neighborFinset (z 0) zk).mp (Finset.mem_inter.mp hzkP).1).symm
              exact ⟨zk, hzk_Res, hzk_av, by simp [hlen_prev, hzk_cap], fun h => (hk1L h).elim, fun _ => hzk_z0⟩
          · have hk_prev_lt : k - 1 + 1 < L := by omega
            have hz_prev_deg := hz_next (k - 1) (by omega) hk_prev_lt
            by_cases hk1L : k + 1 < L
            · have hk_lt_L1 : k - 1 + 1 < L - 1 := by omega
              have hT_eq : TargetNext (z 0) (k - 1) hk_prev_lt = Res (w k) := by
                simp only [TargetNext, hlen_prev, ↓reduceIte, hk_lt_L1, hk_w]
              rw [hT_eq] at hz_prev_deg
              set P := G.neighborFinset (z (k - 1)) ∩ Res (w k)
              have hP_sub : P ⊆ parts (w k) := Finset.inter_subset_right.trans (hRes_sub _)
              have hP : (avoid.card : ℝ) + 2 * ((parts (w k)).card : ℝ) * η ≤ (P.card : ℝ) := by
                have hav : (avoid.card : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr havoid_card
                have hps := (hPool_Send (w k) (w k)).2
                linarith only [hav, hps, hz_prev_deg]
              have hR_next := hR (w k) (w' k) (hw_adj k hkL)
              obtain ⟨zk, hzkP, hzk_av, hzk_next, _⟩ := exists_good_two G hη hP_sub
                (hparts_pos _) hR_next.1 hR_next.2 (hparts_pos _) (hT_sub (z 0) k hk1L) (hT_sz k hk1L)
                hR_next.1 hR_next.2 (hparts_pos _) (hT_sub (z 0) k hk1L) (hT_sz k hk1L) hP
              have hzk_Res : zk ∈ Res (w k) := (Finset.mem_inter.mp hzkP).2
              have hzk_adj : G.Adj (z (k - 1)) zk := (G.mem_neighborFinset (z (k - 1)) zk).mp (Finset.mem_inter.mp hzkP).1
              exact ⟨zk, hzk_Res, hzk_av, by simp [hlen_prev, hzk_adj], fun _ => hzk_next, fun h => by omega⟩
            · have hk_eq : k = L - 1 := by omega
              have hk_lt_L1 : ¬ (k - 1 + 1 < L - 1) := by omega
              have hT_eq : TargetNext (z 0) (k - 1) hk_prev_lt = S_end (z 0) := by
                simp only [TargetNext, hlen_prev, ↓reduceIte, hk_lt_L1]
              rw [hT_eq] at hz_prev_deg
              set P := G.neighborFinset (z (k - 1)) ∩ S_end (z 0)
              have hP_pos : avoid.card < P.card := by
                have h1 : (avoid.card : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr havoid_card
                have h2 : (L : ℝ) < (d - η) * ((d - η) * ((Res (w (L - 1))).card : ℝ)) := by
                  have hnn := hPool_Send2 (w (L - 1)) (w k)
                  have hp : (0 : ℝ) < 2 * ((parts (w k)).card : ℝ) * η := by
                    have := hparts_pos (w k)
                    positivity
                  linarith only [hnn, hp]
                have h3 : (d - η) * ((d - η) * ((Res (w (L - 1))).card : ℝ)) <
                    (d - η) * ((S_end (z 0)).card : ℝ) := by
                  have hdn : 0 < d - η := by
                    have hps1 := (hPool_Send (w (L - 1)) (w (L - 1))).1
                    have hpos1 : (0 : ℝ) < (parts (w (L - 1))).card * η := by
                      have := hparts_pos (w (L - 1)); positivity
                    have hpos2 : (0 : ℝ) ≤ (Res (w (L - 1))).card := Nat.cast_nonneg _
                    nlinarith only [hps1, hpos1, hpos2]
                  exact mul_lt_mul_of_pos_left hz0_SL hdn
                exact_mod_cast (h1.trans_lt (h2.trans h3)).trans hz_prev_deg
              have hrem : (P \ avoid).Nonempty := Finset.card_pos.mp (by
                have : P.card ≤ (P \ avoid).card + avoid.card := by
                  calc P.card ≤ ((P \ avoid) ∪ avoid).card := Finset.card_le_card (fun x hx => by
                        by_cases h : x ∈ avoid
                        · exact Finset.mem_union_right _ h
                        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩))
                    _ ≤ (P \ avoid).card + avoid.card := Finset.card_union_le _ _
                omega)
              obtain ⟨zk, hzk⟩ := hrem
              rw [Finset.mem_sdiff] at hzk
              have hzk_mem := Finset.mem_inter.mp hzk.1
              have hzk_Send := Finset.mem_inter.mp hzk_mem.2
              have hzk_Res : zk ∈ Res (w k) := by rw [hk_eq]; exact hzk_Send.2
              have hzk_adj : G.Adj (z (k - 1)) zk := (G.mem_neighborFinset (z (k - 1)) zk).mp hzk_mem.1
              have hzk_z0 : G.Adj zk (z 0) := ((G.mem_neighborFinset (z 0) zk).mp hzk_Send.1).symm
              exact ⟨zk, hzk_Res, hzk.2, by simp [hlen_prev, hzk_adj], fun h => (hk1L h).elim, fun _ => hzk_z0⟩
        obtain ⟨zk, hzk_Res, hzk_av, hzk_prev, hzk_next, hzk_wrap⟩ := hpick
        let z' : ℕ → Fin N := fun i => if i = k then zk else z i
        have hz'0 : z' 0 = z 0 := if_neg (by omega : (0 : ℕ) ≠ k)
        refine ⟨z', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i hi
          by_cases hik : i = k
          · subst hik; dsimp only [z']; rw [if_pos rfl]; exact hzk_Res
          · dsimp only [z']; rw [if_neg hik]; exact hz_Res i (by omega)
        · intro i₁ hi₁ i₂ hi₂ hne
          by_cases h1 : i₁ = k <;> by_cases h2 : i₂ = k
          · exact (hne (h1.trans h2.symm)).elim
          · subst h1; dsimp only [z']; rw [if_pos rfl, if_neg h2]
            intro heq
            exact hzk_av (Finset.mem_image.mpr ⟨i₂, Finset.mem_range.mpr (by omega), heq.symm⟩)
          · subst h2; dsimp only [z']; rw [if_neg h1, if_pos rfl]
            intro heq
            exact hzk_av (Finset.mem_image.mpr ⟨i₁, Finset.mem_range.mpr (by omega), heq⟩)
          · dsimp only [z']; rw [if_neg h1, if_neg h2]
            exact hz_inj i₁ (by omega) i₂ (by omega) hne
        · rw [hz'0]; exact hz0_SL
        · intro i hi hi1
          rw [hz'0]
          by_cases hik : i = k
          · subst hik
            have hzk1 : z' i = zk := by dsimp [z']; exact if_pos rfl
            rw [hzk1]; exact hzk_next hi1
          · have hzi : z' i = z i := by dsimp [z']; exact if_neg hik
            rw [hzi]; exact hz_next i (by omega) hi1
        · intro i hi hik
          by_cases hkeq : i = k
          · subst hkeq
            have hzk1 : z' i = zk := by dsimp [z']; exact if_pos rfl
            have hzm1 : z' (i - 1) = z (i - 1) := by dsimp [z']; exact if_neg (by omega : i - 1 ≠ i)
            rw [hzk1, hzm1]; exact hzk_prev
          · have him1 : i - 1 ≠ k := by omega
            have hzi : z' i = z i := by dsimp [z']; exact if_neg hkeq
            have hzm : z' (i - 1) = z (i - 1) := by dsimp [z']; exact if_neg him1
            rw [hzi, hzm]; exact hz_prev i hi (by omega)
        · intro hkL1
          have hk_eq : k = L - 1 := by omega
          subst hk_eq
          rw [hz'0]
          simp only [z', if_pos rfl]; exact hzk_wrap rfl
  obtain ⟨z, hz_Res, hz_inj, hz0_SL, hz_next, hz_prev, hz_wrap⟩ := hbind L (by omega) le_rfl
  refine ⟨z, hz_Res, hz_inj, ?_, hz_prev, hz_wrap rfl⟩
  intro i hi
  have h := hz_next i (by omega) hi
  dsimp [TargetNext, S_end] at h
  split_ifs at h ⊢ <;> exact h

end ConnectedMatchingEmbeddingProof

set_option maxHeartbeats 800000 in
theorem connected_matching_cycle_embedding :
  ∀ (d δ : ℝ), 0 < d → 0 < δ → δ < 1 →
    ∃ η > (0 : ℝ), ∀ (t : ℕ), ∃ m₀ : ℕ,
      ∀ (N n m k : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
        (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t)) (M : R.Subgraph),
        Even n → 4 ≤ n → 1 ≤ k → m₀ ≤ m → (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) →
        Pairwise (fun i j => Disjoint (parts i) (parts j)) →
        (∀ i : Fin t, m ≤ (parts i).card ∧ (parts i).card ≤ m + 1) →
        (∀ u v : Fin t, R.Adj u v →
          G.IsUniform η (parts u) (parts v) ∧ (d : ℝ) ≤ (G.edgeDensity (parts u) (parts v) : ℝ)) →
        M.IsMatching → 2 * k ≤ M.verts.ncard →
        (∀ u ∈ M.verts, ∀ v ∈ M.verts, R.Reachable u v) →
        (cycleGraph n).IsContained G := by
  intro d δ hd hδ0 hδ1
  let d' : ℝ := min d 1
  have hd' : 0 < d' := lt_min hd zero_lt_one
  have hd'1 : d' ≤ 1 := min_le_right d 1
  have hd'd : d' ≤ d := min_le_left d 1
  let η : ℝ := min (d' / 4) (min (δ / 16) (d' ^ 2 * δ / 256))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hη_d' : η ≤ d' / 4 := min_le_left _ _
  have hη_δ : η ≤ δ / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hη_sq : η ≤ d' ^ 2 * δ / 256 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, fun t => ?_⟩
  let m₀ : ℕ := Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) + 32
  refine ⟨m₀, fun N n m k G _ parts R M heven hn4 hk1 hm hm₀ hdisj hparts hR hM hMcard hMreach => ?_⟩
  classical
  have hm32 : 32 ≤ m := le_trans (by omega : 32 ≤ m₀) hm
  have hm_pos : 0 < m := by omega
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hparts_pos : ∀ i : Fin t, 0 < (parts i).card := fun i =>
    lt_of_lt_of_le hm_pos (hparts i).1
  have hS_card : 2 * k ≤ M.verts.toFinset.card := by
    rwa [← Set.ncard_eq_toFinset_card']
  obtain ⟨edges, hedges_len, hedges_adj, _, hedges_nodup⟩ :=
    ConnectedMatchingEmbeddingProof.extract_matching_pairs M hM k M.verts.toFinset
      (fun x hx => Set.mem_toFinset.mp hx)
      (fun x hx y hxy => Set.mem_toFinset.mpr (M.edge_vert hxy.symm))
      hS_card
  have hR_has_edge : ∃ u v : Fin t, R.Adj u v := by
    have hne : edges ≠ [] := by intro h; simp [h] at hedges_len; omega
    obtain ⟨⟨u, v⟩, rest, h⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨u, v, M.adj_sub (hedges_adj (u, v) (by simp [h]))⟩
  have hd1 : d ≤ 1 := by
    obtain ⟨u, v, huv⟩ := hR_has_edge
    have h1 := (hR u v huv).2
    have h2 : (G.edgeDensity (parts u) (parts v) : ℝ) ≤ 1 := by
      exact_mod_cast SimpleGraph.edgeDensity_le_one G (parts u) (parts v)
    linarith
  have hd_gt : η < d := by linarith
  have hd_sub_ge : 3 / 4 * d' ≤ d - η := by linarith
  have hη_d1 : η ≤ d' / 256 := by
    have h1 : d' ^ 2 * δ / 256 ≤ d' * 1 / 256 := by nlinarith
    linarith
  have hη_δd : η ≤ d' * δ / 256 := by
    have h1 : d' ^ 2 * δ / 256 ≤ d' * δ / 256 := by nlinarith
    linarith
  have h1mδ : 0 < 1 - δ := sub_pos.mpr hδ1
  have hm_t_den : (t : ℝ) / (1 - δ) ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            Nat.le_ceil _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, Nat.cast_add, Nat.cast_ofNat]; linarith
    have h2 : (0 : ℝ) ≤ 256 * (t : ℝ) / (d' ^ 2 * δ) := by positivity
    have h3 : (0 : ℝ) ≤ 32 / δ := by positivity
    have h4 : (0 : ℝ) ≤ 32 / (d' * δ) := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hm_t_sq : 256 * (t : ℝ) / (d' ^ 2 * δ) ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            Nat.le_ceil _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, Nat.cast_add, Nat.cast_ofNat]; linarith
    have h2 : (0 : ℝ) ≤ (t : ℝ) / (1 - δ) := by positivity
    have h3 : (0 : ℝ) ≤ 32 / δ := by positivity
    have h4 : (0 : ℝ) ≤ 32 / (d' * δ) := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hm_δ : 32 / δ ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            Nat.le_ceil _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, Nat.cast_add, Nat.cast_ofNat]; linarith
    have h2 : (0 : ℝ) ≤ 256 * (t : ℝ) / (d' ^ 2 * δ) := by positivity
    have h3 : (0 : ℝ) ≤ (t : ℝ) / (1 - δ) := by positivity
    have h4 : (0 : ℝ) ≤ 32 / (d' * δ) := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hm_dδ : 32 / (d' * δ) ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            Nat.le_ceil _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, Nat.cast_add, Nat.cast_ofNat]; linarith
    have h2 : (0 : ℝ) ≤ 256 * (t : ℝ) / (d' ^ 2 * δ) := by positivity
    have h3 : (0 : ℝ) ≤ (t : ℝ) / (1 - δ) := by positivity
    have h4 : (0 : ℝ) ≤ 32 / δ := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hchoose_r : ∃ r : ℕ, 1 ≤ r ∧ r ≤ k ∧ (n : ℝ) ≤ (1 - δ) * (2 * (r : ℝ) * (m : ℝ)) ∧
      (2 ≤ r → (1 - δ) * (2 * ((r - 1 : ℕ) : ℝ) * (m : ℝ)) < (n : ℝ)) := by
    let S : Finset ℕ := (Finset.Icc (1 : ℕ) k).filter (fun j => (n : ℝ) ≤ (1 - δ) * (2 * (j : ℝ) * (m : ℝ)))
    have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, le_rfl⟩, hm₀⟩
    have hSne : S.Nonempty := ⟨k, hkS⟩
    let r := S.min' hSne
    have hrS : r ∈ S := Finset.min'_mem S hSne
    have hr_mem := Finset.mem_filter.mp hrS
    have hr_icc := Finset.mem_Icc.mp hr_mem.1
    refine ⟨r, hr_icc.1, hr_icc.2, hr_mem.2, fun hr2 => ?_⟩
    by_contra! hle
    have hr1_mem : r - 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hle⟩
    have := Finset.min'_le S (r - 1) hr1_mem
    omega
  obtain ⟨r, hr1, hrk, hnr, hnr_min⟩ := hchoose_r
  set chosen := edges.take r
  have hchosen_len : chosen.length = r := by rw [List.length_take, hedges_len]; exact min_eq_left hrk
  have hchosen_ne : chosen ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hchosen_adj : ∀ p ∈ chosen, R.Adj p.1 p.2 := fun p hp =>
    M.adj_sub (hedges_adj p (List.mem_of_mem_take hp))
  have hchosen_nodup : (chosen.flatMap (fun p => [p.1, p.2])).Nodup := by
    have h1 : chosen.flatMap (fun p => [p.1, p.2]) <+: edges.flatMap (fun p => [p.1, p.2]) :=
      (List.take_prefix r edges).flatMap (fun p => [p.1, p.2])
    exact hedges_nodup.sublist h1.sublist
  have hchosen_reach : ∀ p ∈ chosen, ∀ q ∈ chosen, R.Reachable p.1 q.1 := fun p hp q hq =>
    hMreach p.1 (M.edge_vert (hedges_adj p (List.mem_of_mem_take hp)))
      q.1 (M.edge_vert (hedges_adj q (List.mem_of_mem_take hq)))
  obtain ⟨W, hWne, hWadj, hWchain, hWwrap, hWlastf, hWeven, hW2, hW2t, hr_le_W2, hW1_eq, hWcnt, hWnodup⟩ :=
    ConnectedMatchingEmbeddingProof.build_closed_walk chosen hchosen_ne hchosen_adj hchosen_nodup hchosen_reach
  rw [hchosen_len] at hr_le_W2 hW1_eq hWcnt
  set L := W.length
  have hL_le_n : L ≤ n := by
    rcases eq_or_lt_of_le hr1 with rfl | hr2
    · have : L = 2 := hW1_eq rfl
      omega
    · have hgt := hnr_min hr2
      have h2m : 2 * (1 - δ) * (m : ℝ) < (n : ℝ) := by
        have h1 : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
        nlinarith
      have ht_le : (t : ℝ) ≤ (1 - δ) * (m : ℝ) := by linarith [(div_le_iff₀ h1mδ).mp hm_t_den]
      have hLt : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
      have hLn_real : (L : ℝ) < (n : ℝ) := by linarith
      exact_mod_cast hLn_real.le
  obtain ⟨n_half, hn_half⟩ := heven
  obtain ⟨L_half, hL_half⟩ := hWeven
  set D := n_half - L_half
  have hn_eq : n = L + 2 * D := by omega
  set B := Nat.floor ((1 - δ) * (m : ℝ))
  have hD_le : D ≤ r * B := by
    have hB_gt : (1 - δ) * (m : ℝ) < (B : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1 : (D : ℝ) + (r : ℝ) ≤ (n_half : ℝ) := by
      have : L_half ≥ r := by omega
      exact_mod_cast (by omega : D + r ≤ n_half)
    have h2 : (n_half : ℝ) ≤ (1 - δ) * (r : ℝ) * (m : ℝ) := by
      have h2n : (n : ℝ) = 2 * (n_half : ℝ) := by exact_mod_cast (by omega : n = 2 * n_half)
      linarith
    have h3 : (1 - δ) * (r : ℝ) * (m : ℝ) < (r : ℝ) * ((B : ℝ) + 1) := by
      have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
      nlinarith
    have h4 : (D : ℝ) < (r : ℝ) * (B : ℝ) := by linarith
    have h4n : D < r * B := by exact_mod_cast h4
    exact h4n.le
  set lens := ConnectedMatchingEmbeddingProof.assignList B W D
  obtain ⟨hlens_len, hlens_sum, hlens_leB, hlens_zero⟩ := ConnectedMatchingEmbeddingProof.assignList_props B W D (hWcnt ▸ hD_le)
  have hlens_L : lens.length = L := hlens_len
  let len : ℕ → ℕ := fun i => if h : i < L then lens[i]'(hlens_len ▸ h) else 0
  have hlen_L : len (L - 1) = 0 := by
    simp only [len, dif_pos (by omega : L - 1 < L)]
    refine hlens_zero (L - 1) (by omega) ?_
    have h1 := hWlastf hWne
    rwa [List.getLast_eq_getElem hWne] at h1
  have hL2_len0 : L = 2 → 0 < len 0 := by
    intro hL2
    have hlen1_0 : len 1 = 0 := by simpa [hL2] using hlen_L
    have hL_half1 : L_half = 1 := by omega
    have hD_pos : 0 < D := by omega
    have hsum0 : len 0 + len 1 = D := by
      have hsum_rng := ConnectedMatchingEmbeddingProof.sum_range_eq_list_sum lens len (fun i hi => by
        have hiL : i < L := hlens_L ▸ hi
        simp [len, hiL])
      rw [hlens_L, hL2, hlens_sum] at hsum_rng
      simpa [Finset.sum_range_succ] using hsum_rng
    omega
  set q := Nat.ceil (δ / 8 * (m : ℝ))
  have hq_ge : δ / 8 * (m : ℝ) ≤ (q : ℝ) := Nat.le_ceil _
  have hq_lt : (q : ℝ) < δ / 8 * (m : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2q_le : 2 * q ≤ m := by
    have h1 : (2 * q : ℝ) < δ / 4 * (m : ℝ) + 2 := by linarith only [hq_lt]
    have h2 : δ / 4 * (m : ℝ) + 2 ≤ 1 / 4 * (m : ℝ) + 2 := by nlinarith only [hδ1, hm_real_pos]
    have h3 : (1 / 4 * (m : ℝ) + 2 : ℝ) ≤ (m : ℝ) := by
      have : (32 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm32
      linarith only [this]
    exact_mod_cast (h1.trans_le (h2.trans h3)).le
  have hsplit_all : ∀ i : Fin t, ∃ Res Cap Body : Finset (Fin N),
      Res ⊆ parts i ∧ Cap ⊆ parts i ∧ Body ⊆ parts i ∧
      Disjoint Res Cap ∧ Disjoint Res Body ∧ Disjoint Cap Body ∧
      Res.card = q ∧ Cap.card = q ∧ Body.card = (parts i).card - 2 * q :=
    fun i => ConnectedMatchingEmbeddingProof.split_cluster (parts i) q (h2q_le.trans (hparts i).1)
  choose Res Cap Body hRes_sub hCap_sub hBody_sub hRC hRB hCB hRes_card hCap_card hBody_card using hsplit_all
  set c := Nat.ceil ((m + 1 : ℝ) * η)
  have hc_ge : (m + 1 : ℝ) * η ≤ (c : ℝ) := Nat.le_ceil _
  have hc_lt : (c : ℝ) < (m + 1 : ℝ) * η + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm1_2m : (m + 1 : ℝ) ≤ 2 * (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
    linarith only [this]
  have hparts_le : ∀ i : Fin t, ((parts i).card : ℝ) ≤ (m : ℝ) + 1 := fun i => by
    exact_mod_cast (hparts i).2
  have hc_parts : ∀ i : Fin t, ((parts i).card : ℝ) * η ≤ (c : ℝ) := fun i =>
    (mul_le_mul_of_nonneg_right (hparts_le i) hη.le).trans hc_ge
  have h_m1η_q : (m + 1 : ℝ) * η ≤ (q : ℝ) := by
    have h1 : (m + 1 : ℝ) * η ≤ 2 * (m : ℝ) * (δ / 16) := mul_le_mul hm1_2m hη_δ hη.le (by positivity)
    linarith only [h1, hq_ge]
  have hRes_sz : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ ((Res i).card : ℝ) := fun i j => by
    rw [hRes_card i]
    exact (mul_le_mul_of_nonneg_right (hparts_le j) hη.le).trans h_m1η_q
  have hCap_sz : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ ((Cap i).card : ℝ) := fun i j => by
    rw [hCap_card i]
    exact (mul_le_mul_of_nonneg_right (hparts_le j) hη.le).trans h_m1η_q
  have hBody_ge : ∀ i : Fin t, (m : ℝ) / 2 ≤ ((Body i).card : ℝ) := fun i => by
    have hb1 : m - 2 * q ≤ (Body i).card := by rw [hBody_card i]; exact Nat.sub_le_sub_right (hparts i).1 _
    have hb2 : (m : ℝ) - 2 * (q : ℝ) ≤ ((Body i).card : ℝ) := by
      have : ((m - 2 * q : ℕ) : ℝ) = (m : ℝ) - 2 * (q : ℝ) := by
        rw [Nat.cast_sub h2q_le]; push_cast; rfl
      rw [← this]; exact_mod_cast hb1
    have h2q : 2 * (q : ℝ) ≤ δ / 4 * (m : ℝ) + 2 := by linarith only [hq_lt]
    have h32 : (32 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm32
    nlinarith only [hb2, h2q, h32, hδ1, hδ0]
  have hBody_sz : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ ((Body i).card : ℝ) := fun i j => by
    have h1 : ((parts j).card : ℝ) * η ≤ 2 * (m : ℝ) * (δ / 16) :=
      mul_le_mul ((hparts_le j).trans hm1_2m) hη_δ hη.le (by positivity)
    have h2 : 2 * (m : ℝ) * (δ / 16) ≤ (m : ℝ) / 2 := by nlinarith only [hδ1, hm_real_pos]
    exact h1.trans (h2.trans (hBody_ge i))
  have hBody_pool : ∀ i j₁ j₂ : Fin t,
      3 * ((max (parts j₁).card (parts j₂).card : ℝ) * η + 1) ≤ (d - η) * ((Body i).card : ℝ) := by
    intro i j₁ j₂
    have hmax : (max (parts j₁).card (parts j₂).card : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast max_le (hparts j₁).2 (hparts j₂).2
    have h1 : 3 * ((max (parts j₁).card (parts j₂).card : ℝ) * η + 1) ≤ 3 * (2 * (m : ℝ) * (d' / 256) + 1) := by
      have : (max (parts j₁).card (parts j₂).card : ℝ) * η ≤ 2 * (m : ℝ) * (d' / 256) :=
        mul_le_mul (hmax.trans hm1_2m) hη_d1 hη.le (by positivity)
      linarith only [this]
    have h2 : (32 : ℝ) ≤ d' * (m : ℝ) := by
      have hdm := (div_le_iff₀ (by positivity : 0 < d' * δ)).mp hm_dδ
      have hle : d' * δ * (m : ℝ) ≤ d' * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hd'.le hδ1.le) hm_real_pos.le
      linarith only [hdm, hle, show (m : ℝ) * (d' * δ) = d' * δ * (m : ℝ) by ring]
    have h3 : 3 * (2 * (m : ℝ) * (d' / 256) + 1) ≤ 3 / 8 * (d' * (m : ℝ)) := by
      have heq : 3 * (2 * (m : ℝ) * (d' / 256) + 1) = 3 / 128 * (d' * (m : ℝ)) + 3 := by ring
      rw [heq]
      linarith only [h2]
    have h4 : 3 / 8 * (d' * (m : ℝ)) ≤ (d - η) * ((Body i).card : ℝ) := by
      have hb := hBody_ge i
      nlinarith only [hb, hd_sub_ge, hd', hm_real_pos]
    exact h1.trans (h3.trans h4)
  have hc_Body : ∀ i : Fin t, (c : ℝ) ≤ (d - η) * ((Body i).card : ℝ) := fun i => by
    have h1 : (c : ℝ) ≤ 3 * ((max (parts i).card (parts i).card : ℝ) * η + 1) := by
      have hm_le : (m : ℝ) ≤ (parts i).card := by exact_mod_cast (hparts i).1
      have h2m : (m + 1 : ℝ) * η ≤ 2 * ((parts i).card : ℝ) * η := by
        nlinarith only [hm1_2m, hm_le, hη]
      simp only [max_self]
      linarith only [hc_lt, h2m]
    exact h1.trans (hBody_pool i i i)
  have hd'2 : d' ^ 2 ≤ 1 := by rw [sq]; exact mul_le_one₀ hd'1 hd'.le hd'1
  have hSend_big : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ (d - η) * ((Cap i).card : ℝ) := by
    intro i j
    rw [hCap_card i]
    have h1 : ((parts j).card : ℝ) * η ≤ 2 * (m : ℝ) * (d' * δ / 256) :=
      mul_le_mul ((hparts_le j).trans hm1_2m) hη_δd hη.le (by positivity)
    have h2 : 2 * (m : ℝ) * (d' * δ / 256) ≤ (3 / 4 * d') * (δ / 8 * (m : ℝ)) := by
      have hdm0 : 0 ≤ d' * δ * (m : ℝ) := by positivity
      linarith only [hdm0, show 2 * (m : ℝ) * (d' * δ / 256) = (1 / 128) * (d' * δ * (m : ℝ)) by ring,
        show (3 / 4 * d') * (δ / 8 * (m : ℝ)) = (3 / 32) * (d' * δ * (m : ℝ)) by ring]
    have h3 : (3 / 4 * d') * (δ / 8 * (m : ℝ)) ≤ (d - η) * (q : ℝ) :=
      mul_le_mul hd_sub_ge hq_ge (by positivity) (by linarith only [hd_sub_ge, hd'])
    exact h1.trans (h2.trans h3)
  have hPool_Res : ∀ i : Fin t, (L : ℝ) + 2 * ((parts i).card : ℝ) * η ≤ ((Res i).card : ℝ) := by
    intro i
    rw [hRes_card i]
    have hL2t : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
    have ht_bnd : 2 * (t : ℝ) ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have h1 := (div_le_iff₀ (by positivity : 0 < d' ^ 2 * δ)).mp hm_t_sq
      linarith only [h1, show (m : ℝ) * (d' ^ 2 * δ) = d' ^ 2 * δ * (m : ℝ) by ring]
    have h2η' : 2 * ((parts i).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 64 := by
      have hle := (hparts_le i).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have h3' : d' ^ 2 * δ * (m : ℝ) / 128 + d' ^ 2 * δ * (m : ℝ) / 64 ≤ δ / 8 * (m : ℝ) := by
      have hδm0 : 0 ≤ δ * (m : ℝ) := by positivity
      have hsq : d' ^ 2 * (δ * (m : ℝ)) ≤ 1 * (δ * (m : ℝ)) := mul_le_mul_of_nonneg_right hd'2 hδm0
      linarith only [hsq, hδm0, show d' ^ 2 * δ * (m : ℝ) = d' ^ 2 * (δ * (m : ℝ)) by ring]
    linarith only [hL2t, ht_bnd, h2η', h3', hq_ge]
  have hPool_Send : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ (d - η) * ((Res i).card : ℝ) ∧
      (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * ((Res i).card : ℝ) := by
    intro i j
    rw [hRes_card i]
    have hL2t : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
    have ht_bnd : 2 * (t : ℝ) ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have h1 := (div_le_iff₀ (by positivity : 0 < d' ^ 2 * δ)).mp hm_t_sq
      linarith only [h1, show (m : ℝ) * (d' ^ 2 * δ) = d' ^ 2 * δ * (m : ℝ) by ring]
    have h2η : 2 * ((parts j).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 64 := by
      have hle := (hparts_le j).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have h1η : ((parts j).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have hle := (hparts_le j).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have hRHS : (3 / 4 * d') * (δ / 8 * (m : ℝ)) ≤ (d - η) * (q : ℝ) :=
      mul_le_mul hd_sub_ge hq_ge (by positivity) (by linarith only [hd_sub_ge, hd'])
    have hdm_bnd : d' ^ 2 * δ * (m : ℝ) ≤ d' * δ * (m : ℝ) := by
      have hδm0 : 0 ≤ δ * (m : ℝ) := by positivity
      have hsq : d' ^ 2 ≤ d' := by rw [sq]; exact mul_le_of_le_one_left hd'.le hd'1
      have h1 := mul_le_mul_of_nonneg_right hsq hδm0
      linarith only [h1, show d' ^ 2 * (δ * (m : ℝ)) = d' ^ 2 * δ * (m : ℝ) by ring,
        show d' * (δ * (m : ℝ)) = d' * δ * (m : ℝ) by ring]
    have hdm0 : 0 ≤ d' * δ * (m : ℝ) := by positivity
    have hA : d' ^ 2 * δ * (m : ℝ) / 128 + d' ^ 2 * δ * (m : ℝ) / 64 ≤
        (3 / 4 * d') * (δ / 8 * (m : ℝ)) := by
      linarith only [hdm_bnd, hdm0, show (3 / 4 * d') * (δ / 8 * (m : ℝ)) = 3 / 32 * (d' * δ * (m : ℝ)) by ring]
    have hB : d' ^ 2 * δ * (m : ℝ) / 128 ≤ (3 / 4 * d') * (δ / 8 * (m : ℝ)) := by
      linarith only [hdm_bnd, hdm0, show (3 / 4 * d') * (δ / 8 * (m : ℝ)) = 3 / 32 * (d' * δ * (m : ℝ)) by ring]
    exact ⟨h1η.trans (hB.trans hRHS), by linarith only [hL2t, ht_bnd, h2η, hA, hRHS]⟩
  have hPool_Send2 : ∀ i j : Fin t,
      (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * ((d - η) * ((Res i).card : ℝ)) := by
    intro i j
    rw [hRes_card i]
    have hL2t : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
    have ht_bnd : 2 * (t : ℝ) ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have h1 := (div_le_iff₀ (by positivity : 0 < d' ^ 2 * δ)).mp hm_t_sq
      linarith only [h1, show (m : ℝ) * (d' ^ 2 * δ) = d' ^ 2 * δ * (m : ℝ) by ring]
    have h2η : 2 * ((parts j).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 64 := by
      have hle := (hparts_le j).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have hRHS : (3 / 4 * d') * ((3 / 4 * d') * (δ / 8 * (m : ℝ))) ≤ (d - η) * ((d - η) * (q : ℝ)) := by
      have hq' : (3 / 4 * d') * (δ / 8 * (m : ℝ)) ≤ (d - η) * (q : ℝ) :=
        mul_le_mul hd_sub_ge hq_ge (by positivity) (by linarith only [hd_sub_ge, hd'])
      exact mul_le_mul hd_sub_ge hq' (by positivity) (by linarith only [hd_sub_ge, hd'])
    have hA : d' ^ 2 * δ * (m : ℝ) / 128 + d' ^ 2 * δ * (m : ℝ) / 64 ≤
        (3 / 4 * d') * ((3 / 4 * d') * (δ / 8 * (m : ℝ))) := by
      have hpos : 0 ≤ d' ^ 2 * δ * (m : ℝ) := by positivity
      linarith only [hpos, show (3 / 4 * d') * ((3 / 4 * d') * (δ / 8 * (m : ℝ))) = 9 / 128 * (d' ^ 2 * δ * (m : ℝ)) by ring]
    linarith only [hL2t, ht_bnd, h2η, hA, hRHS]
  let w : ℕ → Fin t := fun i => if h : i < L then W[i].1 else (W.head hWne).1
  let w' : ℕ → Fin t := fun i => if h : i < L then W[i].2.1 else (W.head hWne).1
  have hw_adj : ∀ i (hi : i < L), R.Adj (w i) (w' i) := fun i hi => by
    simp only [w, w', dif_pos hi]
    exact hWadj W[i] (List.getElem_mem hi)
  have hw'_eq : ∀ i (hi : i + 1 < L), w' i = w (i + 1) := fun i hi => by
    simp only [w', w, dif_pos (by omega : i < L), dif_pos hi]
    exact List.isChain_iff_getElem.mp hWchain i hi
  have hw_wrap : w' (L - 1) = w 0 := by
    simp only [w', w, dif_pos (by omega : L - 1 < L), dif_pos (by omega : 0 < L)]
    have h1 := hWwrap hWne
    rwa [List.getLast_eq_getElem hWne, List.head_eq_getElem hWne] at h1
  obtain ⟨z, hz_Res, hz_inj, hz_next, hz_prev, hz_wrap⟩ :=
    ConnectedMatchingEmbeddingProof.embed_tour_vertices G hη parts R hparts_pos hR Res Cap Body
      hRes_sub hCap_sub hBody_sub hRes_sz hCap_sz hBody_sz
      L w w' hw_adj hw'_eq hw_wrap len hlen_L hW2 hL2_len0 hPool_Res hPool_Send hPool_Send2
  have hℓ_bound : ∀ i (hi : i < L), len i ≤ min ((Body (w' i)).card - c) (Body (w i)).card - 2 * c := by
    intro i hi
    have hleB : len i ≤ B := by
      simp only [len, dif_pos hi]
      exact hlens_leB i hi
    have hB_real : (B : ℝ) ≤ (1 - δ) * (m : ℝ) := Nat.floor_le (by positivity)
    have hc_ub : (c : ℝ) < 2 * (m : ℝ) * (δ / 16) + 1 := by
      have : (m + 1 : ℝ) * η ≤ 2 * (m : ℝ) * (δ / 16) := mul_le_mul hm1_2m hη_δ hη.le (by positivity)
      linarith only [this, hc_lt]
    have hq_ub : (q : ℝ) < δ / 8 * (m : ℝ) + 1 := hq_lt
    have hBU : (m : ℝ) - 2 * (q : ℝ) ≤ ((Body (w i)).card : ℝ) := by
      have hb1 : m - 2 * q ≤ (Body (w i)).card := by
        rw [hBody_card (w i)]; exact Nat.sub_le_sub_right (hparts (w i)).1 _
      have hb2 : ((m - 2 * q : ℕ) : ℝ) = (m : ℝ) - 2 * (q : ℝ) := by
        rw [Nat.cast_sub h2q_le]; push_cast; rfl
      rw [← hb2]; exact_mod_cast hb1
    have hBV : (m : ℝ) - 2 * (q : ℝ) ≤ ((Body (w' i)).card : ℝ) := by
      have hb1 : m - 2 * q ≤ (Body (w' i)).card := by
        rw [hBody_card (w' i)]; exact Nat.sub_le_sub_right (hparts (w' i)).1 _
      have hb2 : ((m - 2 * q : ℕ) : ℝ) = (m : ℝ) - 2 * (q : ℝ) := by
        rw [Nat.cast_sub h2q_le]; push_cast; rfl
      rw [← hb2]; exact_mod_cast hb1
    have h32 : (32 : ℝ) ≤ δ * (m : ℝ) := by
      have := (div_le_iff₀ hδ0).mp hm_δ
      linarith only [this]
    have h1 : (len i : ℝ) ≤ (1 - δ) * (m : ℝ) := (Nat.cast_le.mpr hleB).trans hB_real
    have h2 : (1 - δ) * (m : ℝ) ≤ ((Body (w' i)).card : ℝ) - 3 * (c : ℝ) := by
      nlinarith only [hBV, hc_ub, hq_ub, h32, hδ0, hδ1, hm_real_pos]
    have h3 : (1 - δ) * (m : ℝ) ≤ ((Body (w i)).card : ℝ) - 3 * (c : ℝ) := by
      nlinarith only [hBU, hc_ub, hq_ub, h32, hδ0, hδ1, hm_real_pos]
    have hn1 : len i ≤ (Body (w' i)).card - 3 * c := by
      have : (len i : ℝ) + 3 * (c : ℝ) ≤ ((Body (w' i)).card : ℝ) := by linarith only [h1, h2]
      have : len i + 3 * c ≤ (Body (w' i)).card := by exact_mod_cast this
      omega
    have hn2 : len i ≤ (Body (w i)).card - 3 * c := by
      have : (len i : ℝ) + 3 * (c : ℝ) ≤ ((Body (w i)).card : ℝ) := by linarith only [h1, h3]
      have : len i + 3 * c ≤ (Body (w i)).card := by exact_mod_cast this
      omega
    omega
  have hseg_exists : ∀ i : ℕ, i < L →
      ∃ seg : List (Fin N),
        seg ≠ [] ∧
        seg.length = 2 * len i + 1 ∧
        (∀ h : seg ≠ [], seg.head h = z i) ∧
        (∀ h : seg ≠ [], G.Adj (seg.getLast h) (z ((i + 1) % L))) ∧
        seg.Nodup ∧
        seg.IsChain G.Adj ∧
        (0 < len i → seg.toFinset ⊆ insert (z i) (Body (w i) ∪ Body (w' i) ∪ Cap (w i))) ∧
        (len i = 0 → seg = [z i]) := by
    intro i hi
    by_cases hli : 0 < len i
    · have hi1 : i + 1 < L := by
        by_contra! hge
        have : i = L - 1 := by omega
        subst this
        omega
      have hmod : (i + 1) % L = i + 1 := Nat.mod_eq_of_lt hi1
      have hzu_deg := hz_next i hi1
      simp only [hli, ↓reduceIte] at hzu_deg
      have hzv_deg := hz_prev (i + 1) (by omega) hi1
      simp only [show i + 1 - 1 = i by omega, hli, ↓reduceIte] at hzv_deg
      have hR_uv := hR (w i) (w' i) (hw_adj i hi)
      obtain ⟨seg, hne, hlen_s, hhead_s, hlast_s, hnodup_s, hchain_s, hsub_s⟩ :=
        ConnectedMatchingEmbeddingProof.bridge_segment G hη hd_gt (hRes_sub (w i)) (hCap_sub (w i)) (hBody_sub (w i)) (hBody_sub (w' i))
          (hdisj (R.ne_of_adj (hw_adj i hi))) (hRC (w i)) (hRB (w i)) (hCB (w i))
          hR_uv.1 hR_uv.2 (hparts_pos (w i)) (hparts_pos (w' i)) c
          (hc_parts (w i)) (hc_parts (w' i))
          (hc_Body (w i)) (hCap_sz (w i) (w i)) (hBody_sz (w i) (w i)) (hBody_sz (w' i) (w' i))
          (hz_Res i hi) hzu_deg hzv_deg (hSend_big (w i) (w i)) (hBody_pool (w' i) (w i) (w' i))
          (len i) hli (hℓ_bound i hi)
      refine ⟨seg, hne, hlen_s, hhead_s, ?_, hnodup_s, hchain_s, fun _ => hsub_s, fun h => by omega⟩
      rw [hmod]
      exact hlast_s
    · have hli0 : len i = 0 := by omega
      refine ⟨[z i], by simp, by simp [hli0], fun _ => rfl, ?_, List.nodup_singleton _, List.isChain_singleton _, fun h => by omega, fun _ => rfl⟩
      intro _
      simp only [List.getLast_singleton]
      by_cases hi1 : i + 1 < L
      · have hmod : (i + 1) % L = i + 1 := Nat.mod_eq_of_lt hi1
        rw [hmod]
        have hp := hz_prev (i + 1) (by omega) hi1
        simpa [show i + 1 - 1 = i by omega, hli0] using hp
      · have hieq : i = L - 1 := by omega
        subst hieq
        have hmod : (L - 1 + 1) % L = 0 := by rw [show L - 1 + 1 = L by omega, Nat.mod_self]
        rw [hmod]
        exact hz_wrap
  let segs : ℕ → List (Fin N) := fun i =>
    if h : i < L then (hseg_exists i h).choose else []
  have hsegs_spec : ∀ i (hi : i < L),
      segs i ≠ [] ∧
      (segs i).length = 2 * len i + 1 ∧
      (∀ h : segs i ≠ [], (segs i).head h = z i) ∧
      (∀ h : segs i ≠ [], G.Adj ((segs i).getLast h) (z ((i + 1) % L))) ∧
      (segs i).Nodup ∧
      (segs i).IsChain G.Adj ∧
      (0 < len i → (segs i).toFinset ⊆ insert (z i) (Body (w i) ∪ Body (w' i) ∪ Cap (w i))) ∧
      (len i = 0 → segs i = [z i]) := by
    intro i hi
    simp only [segs, dif_pos hi]
    exact (hseg_exists i hi).choose_spec
  have hlen_true : ∀ i (hi : i < L), 0 < len i → W[i].2.2 = true := by
    intro i hi hpos
    by_contra hfalse
    have hf : W[i].2.2 = false := Bool.eq_false_iff.mpr hfalse
    have hz := hlens_zero i hi hf
    simp only [len, dif_pos hi] at hpos
    rw [hz] at hpos
    omega
  have hW_disj_true : ∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ → 0 < len i₁ → 0 < len i₂ →
      Disjoint ({w i₁, w' i₁} : Finset (Fin t)) ({w i₂, w' i₂} : Finset (Fin t)) := by
    intro i₁ hi₁ i₂ hi₂ hne hpos₁ hpos₂
    have ht1 := hlen_true i₁ hi₁ hpos₁
    have ht2 := hlen_true i₂ hi₂ hpos₂
    simp only [w, w', dif_pos hi₁, dif_pos hi₂]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ConnectedMatchingEmbeddingProof.true_indices_disjoint W hWnodup i₁ i₂ hi₁ hi₂ hlt ht1 ht2
    · exact (ConnectedMatchingEmbeddingProof.true_indices_disjoint W hWnodup i₂ i₁ hi₂ hi₁ hlt ht2 ht1).symm
  have hz_not_BBC : ∀ i₁ < L, ∀ i₂ < L,
      z i₁ ∉ Body (w i₂) ∪ Body (w' i₂) ∪ Cap (w i₂) := by
    intro i₁ hi₁ i₂ hi₂ hmem
    have hz1 : z i₁ ∈ Res (w i₁) := hz_Res i₁ hi₁
    have hzR := hRes_sub (w i₁) hz1
    simp only [Finset.mem_union] at hmem
    rcases hmem with (hB1 | hB2) | hC
    · by_cases heq : w i₁ = w i₂
      · rw [heq] at hz1
        exact Finset.disjoint_left.mp (hRB (w i₂)) hz1 hB1
      · exact Finset.disjoint_left.mp (hdisj heq) hzR (hBody_sub _ hB1)
    · by_cases heq : w i₁ = w' i₂
      · rw [heq] at hz1
        exact Finset.disjoint_left.mp (hRB (w' i₂)) hz1 hB2
      · exact Finset.disjoint_left.mp (hdisj heq) hzR (hBody_sub _ hB2)
    · by_cases heq : w i₁ = w i₂
      · rw [heq] at hz1
        exact Finset.disjoint_left.mp (hRC (w i₂)) hz1 hC
      · exact Finset.disjoint_left.mp (hdisj heq) hzR (hCap_sub _ hC)
  have hdisj_segs : ∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ →
      Disjoint (segs i₁).toFinset (segs i₂).toFinset := by
    intro i₁ hi₁ i₂ hi₂ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    by_cases h1 : 0 < len i₁ <;> by_cases h2 : 0 < len i₂
    · have hs1 := (hsegs_spec i₁ hi₁).2.2.2.2.2.2.1 h1 hx₁
      have hs2 := (hsegs_spec i₂ hi₂).2.2.2.2.2.2.1 h2 hx₂
      rcases Finset.mem_insert.mp hs1 with rfl | hx1' <;>
        rcases Finset.mem_insert.mp hs2 with hzx | hx2'
      · exact hz_inj i₁ hi₁ i₂ hi₂ hne hzx
      · exact hz_not_BBC i₁ hi₁ i₂ hi₂ hx2'
      · exact hz_not_BBC i₂ hi₂ i₁ hi₁ (hzx ▸ hx1')
      · have hd := hW_disj_true i₁ hi₁ i₂ hi₂ hne h1 h2
        have hx_in₁ : ∃ u ∈ ({w i₁, w' i₁} : Finset (Fin t)), x ∈ parts u := by
          simp only [Finset.mem_union] at hx1'
          rcases hx1' with (h | h) | h
          · exact ⟨w i₁, by simp, hBody_sub _ h⟩
          · exact ⟨w' i₁, by simp, hBody_sub _ h⟩
          · exact ⟨w i₁, by simp, hCap_sub _ h⟩
        have hx_in₂ : ∃ v ∈ ({w i₂, w' i₂} : Finset (Fin t)), x ∈ parts v := by
          simp only [Finset.mem_union] at hx2'
          rcases hx2' with (h | h) | h
          · exact ⟨w i₂, by simp, hBody_sub _ h⟩
          · exact ⟨w' i₂, by simp, hBody_sub _ h⟩
          · exact ⟨w i₂, by simp, hCap_sub _ h⟩
        obtain ⟨u, hu, hxu⟩ := hx_in₁
        obtain ⟨v, hv, hxv⟩ := hx_in₂
        have huv : u ≠ v := fun h => Finset.disjoint_left.mp hd hu (h ▸ hv)
        exact Finset.disjoint_left.mp (hdisj huv) hxu hxv
    · have hl2 : len i₂ = 0 := by omega
      have hs1 := (hsegs_spec i₁ hi₁).2.2.2.2.2.2.1 h1 hx₁
      have hs2 := (hsegs_spec i₂ hi₂).2.2.2.2.2.2.2 hl2
      rw [hs2] at hx₂
      simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
        Finset.notMem_empty, or_false] at hx₂
      subst hx₂
      rcases Finset.mem_insert.mp hs1 with hzx | hx1'
      · exact hz_inj i₂ hi₂ i₁ hi₁ hne.symm hzx
      · exact hz_not_BBC i₂ hi₂ i₁ hi₁ hx1'
    · have hl1 : len i₁ = 0 := by omega
      have hs1 := (hsegs_spec i₁ hi₁).2.2.2.2.2.2.2 hl1
      have hs2 := (hsegs_spec i₂ hi₂).2.2.2.2.2.2.1 h2 hx₂
      rw [hs1] at hx₁
      simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
        Finset.notMem_empty, or_false] at hx₁
      subst hx₁
      rcases Finset.mem_insert.mp hs2 with hzx | hx2'
      · exact hz_inj i₁ hi₁ i₂ hi₂ hne hzx
      · exact hz_not_BBC i₁ hi₁ i₂ hi₂ hx2'
    · have hl1 : len i₁ = 0 := by omega
      have hl2 : len i₂ = 0 := by omega
      rw [List.mem_toFinset, (hsegs_spec i₁ hi₁).2.2.2.2.2.2.2 hl1, List.mem_singleton] at hx₁
      rw [List.mem_toFinset, (hsegs_spec i₂ hi₂).2.2.2.2.2.2.2 hl2, List.mem_singleton] at hx₂
      exact hz_inj i₁ hi₁ i₂ hi₂ hne (hx₁.symm.trans hx₂)
  have hsum_segs : ∑ i ∈ Finset.range L, (segs i).length = n := by
    have h1 : ∑ i ∈ Finset.range L, (segs i).length = ∑ i ∈ Finset.range L, (2 * len i + 1) :=
      Finset.sum_congr rfl fun i hi => (hsegs_spec i (Finset.mem_range.mp hi)).2.1
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
      ← Finset.mul_sum]
    have h2 : ∑ i ∈ Finset.range L, len i = D := by
      have h3 : ∑ i ∈ Finset.range L, len i = lens.sum := by
        rw [← hlens_L]
        exact ConnectedMatchingEmbeddingProof.sum_range_eq_list_sum lens len (fun i hi => by
          have hiL : i < L := hlens_L ▸ hi
          simp [len, hiL])
      exact h3.trans hlens_sum
    omega
  exact ConnectedMatchingEmbeddingProof.assemble_cycle G hn4 (by omega) z segs
    (fun i hi => (hsegs_spec i hi).1)
    (fun i hi => (hsegs_spec i hi).2.2.1)
    (fun i hi => (hsegs_spec i hi).2.2.2.2.1)
    (fun i hi => (hsegs_spec i hi).2.2.2.2.2.1)
    (fun i hi => (hsegs_spec i hi).2.2.2.1)
    hdisj_segs
    hsum_segs



end PermutedModule54

/- Source module: ReducedHostExistence.lean -/
section PermutedModule55

/-!
Regularity, cycle embedding, and quantitative completion produce the exact
finite data needed by the host extremal transfer. Credit: @fqlx.
The common regularity and embedding source attributions are retained in the
imported modules and in the final flattened submission.
-/

open Finset SimpleGraph

namespace MatchingStability

theorem eventual_reduced_host_dichotomy
    (α μ δ θ d : ℝ) (p : TransferParameters α μ δ θ d) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ c : Fin 3 → SimpleGraph (Fin (4 * M)),
      ∀ [∀ k, DecidableRel (c k).Adj],
      (⊤ : SimpleGraph (Fin (4 * M))).IsEdgeColouring c →
      (∃ k, cycleGraph (2 * M) ⊑ c k) ∨
        Nonempty (HostReducedData M c α μ δ θ d) := by
  classical
  have hθ := p.theta_pos
  have hθsmall := p.theta_small
  obtain ⟨η,hη,hembed⟩ := connected_matching_cycle_embedding d (θ / 4) p.d_pos
    (by positivity) (by linarith)
  choose m₀ hm₀ using hembed
  let ε : ℝ := min (η / 2)
    (min ((θ / (8 * 2000001)) ^ 2 / 2) (min (θ / 2) 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεη : 2 * ε ≤ η := by
    have hh : ε ≤ η / 2 := min_le_left _ _
    linarith
  have hεsquare : 2 * ε ≤ (θ / (8 * 2000001)) ^ 2 := by
    have hh : ε ≤ (θ / (8 * 2000001)) ^ 2 / 2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hεθ : 2 * ε ≤ θ := by
    have hh : ε ≤ θ / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hεone : ε ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let l := Nat.ceil (8 * (2000001 + 3 : ℝ) / θ)
  obtain ⟨B,hB⟩ := CommonRegularity.indexed_simultaneous_equipartition ε hε hεone l
  let w₀ := max 1 ((range (B + 1)).sup m₀)
  let M₀ := max 2 (max B (max (B * w₀) (Nat.ceil ((B : ℝ) / θ))))
  refine ⟨M₀,?_⟩
  intro M hM c _ hc
  have hMtwo : 2 ≤ M := (le_max_left _ _).trans hM
  have hMB : B ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hMprod : B * w₀ ≤ M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hMceil : Nat.ceil ((B : ℝ) / θ) ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  obtain ⟨t,htpos,hlt,htB,parts,hdis,hcover,hparts,hpartsne,bad,_,hbad,hgood⟩ :=
    hB (4 * M) (by omega) c hc
  let w := 4 * M / t
  have htpositive : 0 < t := by omega
  have hlarge : 8 * (2000001 + 3 : ℝ) ≤ θ * t := by
    have hl : 8 * (2000001 + 3 : ℝ) / θ ≤ (l : ℝ) := Nat.le_ceil _
    have hlt' : (l : ℝ) ≤ t := by exact_mod_cast hlt
    have hh := (div_le_iff₀ hθ).mp (hl.trans hlt')
    nlinarith
  have htmargin : 16 ≤ θ * t := by linarith
  have hround : 4 * (t : ℝ) ≤ θ * (4 * M) := by
    have hmc : (B : ℝ) / θ ≤ M :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hMceil)
    have hh := (div_le_iff₀ hθ).mp hmc
    have htB' : (t : ℝ) ≤ B := by exact_mod_cast htB
    nlinarith
  have hw₀ : 1 ≤ w₀ := le_max_left _ _
  have hm₀t : m₀ t ≤ w₀ :=
    (le_sup (f := m₀) (mem_range.mpr (by omega))).trans (le_max_right _ _)
  have hwlarge : w₀ ≤ w := by
    apply (Nat.le_div_iff_mul_le htpositive).mpr
    have hprod : w₀ * t ≤ B * w₀ := by nlinarith
    exact hprod.trans (by omega)
  have hwpos : 1 ≤ w := hw₀.trans hwlarge
  have hwt : w * t ≤ 4 * M := Nat.div_mul_le_self _ _
  let R := ReducedMulticoloring.graph c parts (2 * ε) d
  have hmissing : ∑ u : Fin t,
      (univ.filter (fun v => u ≠ v ∧ ∀ k, ¬ (R k).Adj u v)).card ≤ bad.card :=
    ReducedMulticoloring.missing_sum_le_bad c parts (2 * ε) d p.d_le_third bad hgood
  let D := Nat.ceil (θ * t / (8 * 2000001))
  obtain ⟨hloss,_,hsquare⟩ := reduced_degree_rounding θ ε t bad.card hθ hlarge hεsquare hbad
  change (2000001 * D + 3 : ℝ) ≤ θ * t at hloss
  change bad.card ≤ D * D at hsquare
  let s := t / 4 + Nat.ceil (θ * t)
  have hnum := StabilityNumerics.matching_threshold_embeds (4 * M) t θ hθ
    (by linarith) htmargin (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hround)
  have hs : 1 ≤ s := hnum.1
  have hlength : ((2 * M : ℕ) : ℝ) ≤ (1 - θ / 4) * (2 * (s : ℝ) * (w : ℝ)) := by
    have hh := hnum.2
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hh ⊢
    convert hh using 1 <;> ring
  by_cases hcycle : ∃ k, cycleGraph (2 * M) ⊑ c k
  · exact Or.inl hcycle
  have hno (k : Fin 3) : ¬ HasCM (R k) s := by
    rintro ⟨F,hF,hFcard,hFreach⟩
    apply hcycle
    refine ⟨k,hm₀ t (4 * M) (2 * M) w s (c k) parts (R k) F
      ⟨M,by omega⟩ (by omega) hs (hm₀t.trans hwlarge) hlength hdis hparts ?_ hF hFcard hFreach⟩
    intro u v huv
    exact ⟨(huv.2.1 k).mono hεη,huv.2.2⟩
  obtain ⟨m,h,f,C,hh,hm,hmlower,htloss,hhupper,hpres,hCno,hCcover,_⟩ :=
    nearly_complete_core_classification t D θ hθ hθsmall htmargin hloss R hno
      (hmissing.trans hsquare)
  have hmt : 4 * m ≤ t := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f f.injective
  have hcoreloss : ((t - 4 * m : ℕ) : ℝ) ≤ θ * t := by
    rw [Nat.cast_sub hmt]
    push_cast
    linarith
  have hirreg : (bad.card : ℝ) ≤ θ * (t : ℝ) ^ 2 :=
    hbad.trans (mul_le_mul_of_nonneg_right hεθ (sq_nonneg _))
  have halt := quantitative_finite_stability_of_noCM C (p.regime hh hm hhupper)
    (Fintype.card_fin _) hCcover hCno
  exact Or.inr ⟨{
    t := t
    t_pos := htpos
    w := w
    w_pos := hwpos
    epsilon := ε
    parts := parts
    parts_disjoint := hdis
    parts_cover := hcover
    parts_size := hparts
    parts_nonempty := hpartsne
    weight_bound := hwt
    host_rounding := hround
    irregular := bad
    irregular_card := hirreg
    regular := fun u v huv hbad => (hgood u v huv hbad).1
    m := m
    m_lower := hmlower
    core_embedding := f
    core_colors := C
    core_loss := hcoreloss
    preserves := hpres
    alternatives := halt }⟩

end MatchingStability


end PermutedModule55

/- Source module: RegularityDensityTransfer.lean -/
section PermutedModule56

/-!
Unweighted density-deficit accounting and its host-graph consequence.
The final lift uses @bmander's `lift_density` from PR #13771, audited in
CommonRegularity.lean with the original Mathlib author notices.
The exceptional-pair accounting is new: @fqlx.
-/

open Finset SimpleGraph
open scoped BigOperators

namespace CommonRegularity

theorem sum_deficit_of_exceptional_set
    {I : Type*} [DecidableEq I] (S bad : Finset I) (f : I → ℝ) (d : ℝ)
    (hbad : bad ⊆ S) (hd : 0 ≤ d)
    (hf : ∀ i ∈ S, 0 ≤ f i)
    (hgood : ∀ i ∈ S, i ∉ bad → 1-2*d ≤ f i) :
    ∑ i ∈ S, (1-f i) ≤ 2*d*S.card+bad.card := by
  have hgoodSum : ∑ i ∈ S\bad, (1-f i) ≤ 2*d*((S\bad).card : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ S\bad, (2*d) := sum_le_sum (by
        intro i hi
        have h := hgood i (mem_sdiff.mp hi).1 (mem_sdiff.mp hi).2
        linarith)
      _ = _ := by simp [mul_comm]
  have hbadSum : ∑ i ∈ bad, (1-f i) ≤ (bad.card : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ bad, (1 : ℝ) := sum_le_sum (by
        intro i hi
        have h := hf i (hbad hi)
        linarith)
      _ = _ := by simp
  rw [← sum_sdiff hbad]
  calc
    _ ≤ 2*d*((S\bad).card : ℝ)+bad.card := add_le_add hgoodSum hbadSum
    _ ≤ 2*d*S.card+bad.card := by
      gcongr
      exact sdiff_subset

/-- The error is at most `2d` on every good pair and at most one on every
exceptional pair. Both pairs and errors are counted with their orientation. -/
theorem sum_deficit_of_bad_pairs
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (A : Finset I) (B : Finset J) (bad : Finset (I×J))
    (f : I → J → ℝ) (d : ℝ) (hbad : bad ⊆ A×ˢB) (hd : 0 ≤ d)
    (hf : ∀ i ∈ A, ∀ j ∈ B, 0 ≤ f i j)
    (hgood : ∀ i ∈ A, ∀ j ∈ B, (i,j) ∉ bad → 1-2*d ≤ f i j) :
    ∑ ij ∈ A×ˢB, (1-f ij.1 ij.2) ≤ 2*d*A.card*B.card+bad.card := by
  have h := sum_deficit_of_exceptional_set (A×ˢB) bad (fun ij => f ij.1 ij.2) d
    hbad hd
    (fun ij hij => hf ij.1 (mem_product.mp hij).1 ij.2 (mem_product.mp hij).2)
    (fun ij hij => hgood ij.1 (mem_product.mp hij).1 ij.2 (mem_product.mp hij).2)
  simpa only [card_product,Nat.cast_mul,mul_assoc] using h

theorem lift_density_of_bad_pairs
    {V : Type*} [DecidableEq V] {T : Finset V} (P : Finpartition T)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (bad : Finset (Finset V×Finset V))
    (hA : A ⊆ P.parts) (hB : B ⊆ P.parts)
    (w : ℕ) (hw : ∀ X ∈ P.parts, w ≤ X.card ∧ X.card ≤ 2*w)
    (d α : ℝ) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hbad : bad ⊆ A×ˢB)
    (hgood : ∀ X ∈ A, ∀ Y ∈ B, (X,Y) ∉ bad →
      1-2*d ≤ (G.edgeDensity X Y : ℝ))
    (hbudget : 2*d*A.card*B.card+bad.card ≤ α/4*A.card*B.card) :
    (1-α)*((A.sup id).card : ℝ)*(B.sup id).card ≤
      ∑ x ∈ A.sup id, (((B.sup id).filter (G.Adj x)).card : ℝ) := by
  apply lift_density P G hA hB hw hα
  apply le_trans (sum_deficit_of_bad_pairs A B bad
    (fun X Y => (G.edgeDensity X Y : ℝ)) d hbad hd ?_ hgood) hbudget
  intro X _ Y _
  exact_mod_cast G.edgeDensity_nonneg X Y

/-- A bad-pair proportion `β` and a good-pair density loss `2d` give host
density loss at most `8d+4β`, accounting for unequal cluster sizes. -/
theorem lift_density_of_bad_pair_fraction
    {V : Type*} [DecidableEq V] {T : Finset V} (P : Finpartition T)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (bad : Finset (Finset V×Finset V))
    (hA : A ⊆ P.parts) (hB : B ⊆ P.parts)
    (w : ℕ) (hw : ∀ X ∈ P.parts, w ≤ X.card ∧ X.card ≤ 2*w)
    (d β : ℝ) (hd : 0 ≤ d) (hβ : 0 ≤ β)
    (hbad : bad ⊆ A×ˢB)
    (hbadSize : (bad.card : ℝ) ≤ β*A.card*B.card)
    (hgood : ∀ X ∈ A, ∀ Y ∈ B, (X,Y) ∉ bad →
      1-2*d ≤ (G.edgeDensity X Y : ℝ)) :
    (1-(8*d+4*β))*((A.sup id).card : ℝ)*(B.sup id).card ≤
      ∑ x ∈ A.sup id, (((B.sup id).filter (G.Adj x)).card : ℝ) := by
  apply lift_density_of_bad_pairs P G A B bad hA hB w hw d (8*d+4*β) hd
    (by positivity) hbad hgood
  calc
    _ ≤ 2*d*A.card*B.card+β*A.card*B.card := add_le_add le_rfl hbadSize
    _ = (8*d+4*β)/4*A.card*B.card := by ring

end CommonRegularity


end PermutedModule56

/- Source module: IndexedDensityTransfer.lean -/
section PermutedModule57

/-!
Indexed host-density transfer, compatible with IndexedCommonRegularity and
the reduced multicolouring. This transports the checked unweighted deficit
bound to unions of arbitrary indexed cluster classes. New proof: @fqlx.
The underlying factor-four lift is credited in RegularityDensityTransfer.
-/

open Finset SimpleGraph
open scoped BigOperators

namespace CommonRegularity

theorem lift_density_indexed_of_bad_pairs
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (parts : I → Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hne : ∀ i, (parts i).Nonempty)
    (w : ℕ) (hw : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ 2*w)
    (A B : Finset I) (bad : Finset (I×I))
    (d α : ℝ) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hbad : bad ⊆ A×ˢB)
    (hgood : ∀ i ∈ A, ∀ j ∈ B, (i,j) ∉ bad →
      1-2*d ≤ (G.edgeDensity (parts i) (parts j) : ℝ))
    (hbudget : 2*d*A.card*B.card+bad.card ≤ α/4*A.card*B.card) :
    (1-α)*((A.biUnion parts).card : ℝ)*(B.biUnion parts).card ≤
      ∑ x ∈ A.biUnion parts, (((B.biUnion parts).filter (G.Adj x)).card : ℝ) := by
  classical
  have hinj : Function.Injective parts := by
    intro i j he
    by_contra hij
    obtain ⟨v,hv⟩ := hne i
    apply Finset.disjoint_left.mp (hdisj hij) hv
    rw [←he]
    exact hv
  let P : Finpartition (univ.biUnion parts) := {
    parts := univ.image parts
    supIndep := by
      apply Finset.supIndep_iff_pairwiseDisjoint.mpr
      intro X hX Y hY hXY
      obtain ⟨i,_,rfl⟩ := mem_image.mp hX
      obtain ⟨j,_,rfl⟩ := mem_image.mp hY
      exact hdisj (fun h => hXY (congrArg parts h))
    sup_parts := by simp only [sup_image,Function.id_comp,sup_eq_biUnion]
    bot_notMem := by
      intro h
      obtain ⟨i,_,hi⟩ := mem_image.mp h
      exact (hne i).ne_empty hi }
  have hA : A.image parts ⊆ P.parts :=
    image_subset_image (subset_univ A)
  have hB : B.image parts ⊆ P.parts :=
    image_subset_image (subset_univ B)
  have hcardA : (A.image parts).card=A.card := card_image_of_injective A hinj
  have hcardB : (B.image parts).card=B.card := card_image_of_injective B hinj
  let badParts := bad.image (fun ij => (parts ij.1,parts ij.2))
  have hbadParts : badParts ⊆ (A.image parts)×ˢ(B.image parts) := by
    intro XY hXY
    obtain ⟨ij,hij,rfl⟩ := mem_image.mp hXY
    have hh := mem_product.mp (hbad hij)
    exact mem_product.mpr ⟨mem_image.mpr ⟨ij.1,hh.1,rfl⟩,
      mem_image.mpr ⟨ij.2,hh.2,rfl⟩⟩
  have hbadCard : badParts.card ≤ bad.card := card_image_le
  have hresult := lift_density_of_bad_pairs P G (A.image parts) (B.image parts) badParts
    hA hB w (by
      intro X hX
      obtain ⟨i,_,rfl⟩ := mem_image.mp hX
      exact hw i) d α hd hα hbadParts (by
      intro X hX Y hY hnot
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hX
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hY
      apply hgood i hi j hj
      exact fun hij => hnot (mem_image.mpr ⟨(i,j),hij,rfl⟩)) (by
      rw [hcardA,hcardB]
      exact (add_le_add le_rfl (Nat.cast_le.mpr hbadCard)).trans hbudget)
  simpa only [sup_image,Function.id_comp,sup_eq_biUnion] using hresult

theorem lift_density_indexed_of_bad_pair_fraction
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (parts : I → Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hne : ∀ i, (parts i).Nonempty)
    (w : ℕ) (hw : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ 2*w)
    (A B : Finset I) (bad : Finset (I×I))
    (d β : ℝ) (hd : 0 ≤ d) (hβ : 0 ≤ β)
    (hbad : bad ⊆ A×ˢB)
    (hbadSize : (bad.card : ℝ) ≤ β*A.card*B.card)
    (hgood : ∀ i ∈ A, ∀ j ∈ B, (i,j) ∉ bad →
      1-2*d ≤ (G.edgeDensity (parts i) (parts j) : ℝ)) :
    (1-(8*d+4*β))*((A.biUnion parts).card : ℝ)*(B.biUnion parts).card ≤
      ∑ x ∈ A.biUnion parts, (((B.biUnion parts).filter (G.Adj x)).card : ℝ) := by
  apply lift_density_indexed_of_bad_pairs G parts hdisj hne w hw A B bad d (8*d+4*β)
    hd (by positivity) hbad hgood
  calc
    _ ≤ 2*d*A.card*B.card+β*A.card*B.card := add_le_add le_rfl hbadSize
    _ = (8*d+4*β)/4*A.card*B.card := by ring

end CommonRegularity


end PermutedModule57

/- Source module: ExclusiveDensityTransfer.lean -/
section PermutedModule58

/-!
Transport exclusive reduced colors through a vertex embedding and account
for discarded clusters and irregular pairs before lifting to host density.
Credit: @fqlx.
-/

open Finset SimpleGraph

namespace MatchingStability

def TransportedExclusive {J I : Type*} (f : J ↪ I)
    (C : Fin 3 → SimpleGraph J) (k : Fin 3) (u v : I) : Prop :=
  ∃ a b, f a = u ∧ f b = v ∧ Exclusive C k a b

noncomputable instance transportedExclusiveDecidable {J I : Type*} (f : J ↪ I)
    (C : Fin 3 → SimpleGraph J) (k : Fin 3) :
    DecidableRel (TransportedExclusive f C k) := Classical.decRel _

theorem transported_failures_card
    {J I : Type*} [DecidableEq J] [DecidableEq I]
    (f : J ↪ I) (C : Fin 3 → SimpleGraph J) (k : Fin 3) (A B : Finset J) :
    (((A.image f).product (B.image f)).filter
      (fun p => ¬ TransportedExclusive f C k p.1 p.2)).card =
      badExclusiveCount C k A B := by
  classical
  let F : J × J → I × I := fun p => (f p.1,f p.2)
  have hF : Function.Injective F := by
    intro a b hab
    exact Prod.ext (f.injective (congrArg Prod.fst hab))
      (f.injective (congrArg Prod.snd hab))
  have he : ((A.image f).product (B.image f)).filter
      (fun p => ¬ TransportedExclusive f C k p.1 p.2) =
      ((A.product B).filter (fun p => ¬ Exclusive C k p.1 p.2)).image F := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpAB,hpno⟩ := mem_filter.mp hp
      obtain ⟨hpA,hpB⟩ := mem_product.mp hpAB
      obtain ⟨a,ha,hfa⟩ := mem_image.mp hpA
      obtain ⟨b,hb,hfb⟩ := mem_image.mp hpB
      refine mem_image.mpr ⟨(a,b),mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,?_⟩,?_⟩
      · exact fun h => hpno ⟨a,b,hfa,hfb,h⟩
      · exact Prod.ext hfa hfb
    · intro himage
      obtain ⟨q,hq,rfl⟩ := mem_image.mp himage
      obtain ⟨hpAB,hpno⟩ := mem_filter.mp hq
      obtain ⟨hpA,hpB⟩ := mem_product.mp hpAB
      refine mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_image_of_mem f hpA,mem_image_of_mem f hpB⟩,?_⟩
      rintro ⟨a,b,ha,hb,hab⟩
      have ha' : a = q.1 := f.injective ha
      have hb' : b = q.2 := f.injective hb
      exact hpno (ha' ▸ hb' ▸ hab)
  rw [he,card_image_of_injective _ hF]
  rfl

theorem failures_extension_card_le
    {I : Type*} [DecidableEq I]
    (R : I → I → Prop) [DecidableRel R]
    (A B U W : Finset I) (e n : ℕ)
    (hA : (A \ U).card ≤ e) (hB : (B \ W).card ≤ e)
    (hAN : A.card ≤ n) (hBN : B.card ≤ n) :
    ((A.product B).filter (fun p => ¬ R p.1 p.2)).card ≤
      ((U.product W).filter (fun p => ¬ R p.1 p.2)).card + 2 * e * n := by
  have hsub : (A.product B).filter (fun p => ¬ R p.1 p.2) ⊆
      ((U.product W).filter (fun p => ¬ R p.1 p.2)) ∪
      ((A \ U).product B ∪ A.product (B \ W)) := by
    intro p hp
    obtain ⟨hpAB,hpR⟩ := mem_filter.mp hp
    obtain ⟨hpA,hpB⟩ := mem_product.mp hpAB
    by_cases hpU : p.1 ∈ U
    · by_cases hpW : p.2 ∈ W
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨hpU,hpW⟩,hpR⟩)
      · exact mem_union_right _ (mem_union_right _
          (mem_product.mpr ⟨hpA,mem_sdiff.mpr ⟨hpB,hpW⟩⟩))
    · exact mem_union_right _ (mem_union_left _
        (mem_product.mpr ⟨mem_sdiff.mpr ⟨hpA,hpU⟩,hpB⟩))
  have hnew : ((A \ U).product B ∪ A.product (B \ W)).card ≤ 2 * e * n := by
    calc
      _ ≤ ((A \ U).product B).card + (A.product (B \ W)).card := card_union_le _ _
      _ = (A \ U).card * B.card + A.card * (B \ W).card := by simp
      _ ≤ e * n + n * e := Nat.add_le_add (Nat.mul_le_mul hA hBN) (Nat.mul_le_mul hAN hB)
      _ = 2 * e * n := by ring
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left hnew _))

theorem transported_exclusive_host_density
    {V J I : Type*} [DecidableEq V]
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (hc : (⊤ : SimpleGraph V).IsEdgeColouring c)
    (parts : I → Finset V) (η d : ℝ)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hne : ∀ i, (parts i).Nonempty)
    (f : J ↪ I) (C : Fin 3 → SimpleGraph J)
    (hpres : ∀ k a b,
      (ReducedMulticoloring.graph c parts η d k).Adj (f a) (f b) → (C k).Adj a b)
    (k : Fin 3) {u v : I}
    (hex : TransportedExclusive f C k u v)
    (hreg : ∀ j, (c j).IsUniform η (parts u) (parts v)) :
    1 - 2 * d ≤ ((c k).edgeDensity (parts u) (parts v) : ℝ) := by
  obtain ⟨a,b,rfl,rfl,hex⟩ := hex
  have hab : a ≠ b := (C k).ne_of_adj hex.1
  have hfab : f a ≠ f b := fun h => hab (f.injective h)
  apply ReducedMulticoloring.exclusive_density c hc parts η d k hfab (hne _) (hne _)
    (hdis hfab) hreg
  intro j hj hjadj
  exact hex.2 j hj (hpres j a b hjadj)

theorem extended_host_density
    {V J I : Type*} [DecidableEq V] [DecidableEq J] [Fintype I] [DecidableEq I]
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (hc : (⊤ : SimpleGraph V).IsEdgeColouring c)
    (parts : I → Finset V) (η d : ℝ) (hd : 0 ≤ d)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hne : ∀ i, (parts i).Nonempty)
    (w : ℕ) (hw : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ 2 * w)
    (irregular : Finset (I × I))
    (hreg : ∀ u v, u ≠ v → (u,v) ∉ irregular →
      ∀ j, (c j).IsUniform η (parts u) (parts v))
    (f : J ↪ I) (C : Fin 3 → SimpleGraph J)
    (hpres : ∀ k a b,
      (ReducedMulticoloring.graph c parts η d k).Adj (f a) (f b) → (C k).Adj a b)
    (k : Fin 3) (A₀ B₀ : Finset J) (A B : Finset I) (e : ℕ)
    (hA : (A \ A₀.image f).card ≤ e) (hB : (B \ B₀.image f).card ≤ e)
    (α : ℝ) (hα : 0 ≤ α)
    (hbudget : 2 * d * A.card * B.card +
      (badExclusiveCount C k A₀ B₀ : ℝ) + 2 * e * Fintype.card I + irregular.card ≤
        α / 4 * A.card * B.card) :
    (1 - α) * ((A.biUnion parts).card : ℝ) * (B.biUnion parts).card ≤
      ∑ x ∈ A.biUnion parts, (((B.biUnion parts).filter ((c k).Adj x)).card : ℝ) := by
  classical
  let fail := (A.product B).filter (fun p => ¬ TransportedExclusive f C k p.1 p.2)
  let bad := (A.product B).filter (fun p => p ∈ irregular ∨ p ∈ fail)
  have hbadsub : bad ⊆ A.product B := filter_subset _ _
  have hfail : fail.card ≤ badExclusiveCount C k A₀ B₀ + 2 * e * Fintype.card I := by
    have hh := failures_extension_card_le (TransportedExclusive f C k)
      A B (A₀.image f) (B₀.image f) e (Fintype.card I) hA hB (card_le_univ _) (card_le_univ _)
    simpa only [transported_failures_card] using hh
  have hbad : bad.card ≤ irregular.card + fail.card := by
    apply le_trans ?_ (card_union_le irregular fail)
    apply card_le_card
    intro p hp
    exact mem_union.mpr (mem_filter.mp hp).2
  apply CommonRegularity.lift_density_indexed_of_bad_pairs (c k) parts hdis hne w hw
    A B bad d α hd hα hbadsub
  · intro u hu v hv hnot
    have hab : (u,v) ∈ A.product B := mem_product.mpr ⟨hu,hv⟩
    have hnreg : (u,v) ∉ irregular :=
      fun h => hnot (mem_filter.mpr ⟨hab,Or.inl h⟩)
    have hex : TransportedExclusive f C k u v := by
      by_contra h
      have hf : (u,v) ∈ fail := mem_filter.mpr ⟨hab,h⟩
      exact hnot (mem_filter.mpr ⟨hab,Or.inr hf⟩)
    have hneq : u ≠ v := by
      obtain ⟨a,b,ha,hb,hex⟩ := hex
      intro huv
      have hab' := f.injective (ha.trans (huv.trans hb.symm))
      exact (C k).ne_of_adj hex.1 hab'
    exact transported_exclusive_host_density c hc parts η d hdis hne f C hpres k hex
      (hreg u v hneq hnreg)
  · have hfR : (fail.card : ℝ) ≤ badExclusiveCount C k A₀ B₀ + 2 * e * Fintype.card I := by
      exact_mod_cast hfail
    have hbR : (bad.card : ℝ) ≤ irregular.card + (fail.card : ℝ) := by exact_mod_cast hbad
    linarith

end MatchingStability


end PermutedModule58

/- Source module: HostBlockLifting.lean -/
section PermutedModule59

/-!
Lifting a four-block reduced partition through an injection into an equitable
host partition. Every discarded cluster is assigned to block 0. The formulas
are shared directly with the density-transfer argument. Credit: @fqlx.
-/

open Finset
open scoped BigOperators

namespace MatchingStability

theorem selected_image_union
    {K I : Type*} [DecidableEq K] [DecidableEq I]
    (T : Fin 4 → Finset K) (f : K → I) (A : Finset (Fin 4)) :
    A.biUnion (fun j => (T j).image f) = (A.biUnion T).image f := by
  exact Finset.biUnion_image.symm

theorem image_blocks_disjoint
    {K I : Type*} [Fintype K] [DecidableEq K] [DecidableEq I]
    (T : Fin 4 → Finset K) (hT : BlockPartition T) (f : K ↪ I) :
    ∀ i j, i ≠ j → Disjoint ((T i).image f) ((T j).image f) := by
  intro i j hij
  exact (Finset.disjoint_image f.injective).mpr (hT.1 i j hij)

theorem outside_image_blocks_card
    {K I : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (T : Fin 4 → Finset K) (hT : BlockPartition T) (f : K ↪ I) :
    (FinitePartitionExtension.outside (fun j => (T j).image f)).card =
      Fintype.card I - Fintype.card K := by
  rw [FinitePartitionExtension.outside,
    card_sdiff_of_subset (subset_univ _),card_univ,
    selected_image_union,hT.2,card_image_of_injective _ f.injective,card_univ]

theorem lifted_cluster_block_card
    {K I : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (T : Fin 4 → Finset K) (hT : BlockPartition T) (f : K ↪ I) (j : Fin 4) :
    (FinitePartitionExtension.extend (fun i => (T i).image f) 0 j).card =
      (T j).card + if j = 0 then Fintype.card I - Fintype.card K else 0 := by
  rw [FinitePartitionExtension.extend_card,
    card_image_of_injective _ f.injective,outside_image_blocks_card T hT f]

theorem union_parts_card
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (parts : I → Finset V)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j))) (A : Finset I) :
    (A.biUnion parts).card = ∑ i ∈ A, (parts i).card := by
  exact card_biUnion (fun i _ j _ hij => hdis hij)

theorem union_parts_card_bounds
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (parts : I → Finset V)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (w : ℕ) (hsize : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ w + 1)
    (A : Finset I) :
    w * A.card ≤ (A.biUnion parts).card ∧
      (A.biUnion parts).card ≤ (w + 1) * A.card := by
  rw [union_parts_card parts hdis]
  constructor
  · calc
      _ = ∑ i ∈ A, w := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ A, (parts i).card := sum_le_sum (fun i _ => (hsize i).1)
  · calc
      _ ≤ ∑ i ∈ A, (w + 1) := sum_le_sum (fun i _ => (hsize i).2)
      _ = _ := by simp [Nat.mul_comm]

theorem lifted_blocks_partition
    {K I V : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V]
    (T : Fin 4 → Finset K) (hT : BlockPartition T) (f : K ↪ I)
    (parts : I → Finset V)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hcover : univ.biUnion parts = univ) :
    BlockPartition (fun j =>
      (FinitePartitionExtension.extend (fun i => (T i).image f) 0 j).biUnion parts) := by
  let S := FinitePartitionExtension.extend (fun i => (T i).image f) 0
  have hS : BlockPartition S := extend_is_partition _ 0 (image_blocks_disjoint T hT f)
  constructor
  · intro j k hjk
    apply Finset.disjoint_left.mpr
    intro v hvj hvk
    obtain ⟨a, haj, hva⟩ := mem_biUnion.mp hvj
    obtain ⟨b, hbk, hvb⟩ := mem_biUnion.mp hvk
    have hab : a ≠ b := fun he =>
      Finset.disjoint_left.mp (hS.1 j k hjk) haj (he.symm ▸ hbk)
    exact Finset.disjoint_left.mp (hdis hab) hva hvb
  · apply eq_univ_of_forall
    intro v
    have hv : v ∈ univ.biUnion parts := hcover.symm ▸ mem_univ v
    obtain ⟨a, _, hva⟩ := mem_biUnion.mp hv
    have ha : a ∈ univ.biUnion S := hS.2.symm ▸ mem_univ a
    obtain ⟨j, _, haj⟩ := mem_biUnion.mp ha
    exact mem_biUnion.mpr ⟨j,mem_univ _,mem_biUnion.mpr ⟨a,haj,hva⟩⟩

theorem lifted_block_card_bounds
    {K I V : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    [DecidableEq V]
    (T : Fin 4 → Finset K) (hT : BlockPartition T) (f : K ↪ I)
    (parts : I → Finset V)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (w : ℕ) (hsize : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ w + 1)
    (j : Fin 4) :
    let U := (FinitePartitionExtension.extend (fun i => (T i).image f) 0 j).biUnion parts
    w * (T j).card ≤ U.card ∧ U.card ≤
      (w + 1) * ((T j).card + if j = 0 then Fintype.card I - Fintype.card K else 0) := by
  dsimp only
  obtain ⟨hl,hu⟩ := union_parts_card_bounds parts hdis w hsize
    (FinitePartitionExtension.extend (fun i => (T i).image f) 0 j)
  rw [lifted_cluster_block_card T hT f j] at hl hu
  exact ⟨(Nat.mul_le_mul_left w (Nat.le_add_right _ _)).trans hl,hu⟩

theorem lifted_block_uniform_error
    {K I V : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    [DecidableEq V]
    (T : Fin 4 → Finset K) (hT : BlockPartition T) (f : K ↪ I)
    (parts : I → Finset V)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (w : ℕ) (hsize : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ w + 1)
    (j : Fin 4) :
    let U := (FinitePartitionExtension.extend (fun i => (T i).image f) 0 j).biUnion parts
    w * (T j).card ≤ U.card ∧ U.card ≤
      w * (T j).card + (w * (Fintype.card I - Fintype.card K) + Fintype.card I) := by
  dsimp only
  obtain ⟨hl,hu⟩ := lifted_block_card_bounds T hT f parts hdis w hsize j
  have hTK : (T j).card ≤ Fintype.card K := card_le_univ _
  have hKI : Fintype.card K ≤ Fintype.card I := Fintype.card_le_of_injective f f.injective
  have hsum : Fintype.card K + (Fintype.card I - Fintype.card K) = Fintype.card I := by omega
  refine ⟨hl,hu.trans ?_⟩
  split_ifs <;> nlinarith

theorem host_card_error
    {K I V : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V]
    (f : K ↪ I) (parts : I → Finset V)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hcover : univ.biUnion parts = univ)
    (w : ℕ) (hsize : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ w + 1) :
    w * Fintype.card K ≤ Fintype.card V ∧ Fintype.card V ≤
      w * Fintype.card K + (w * (Fintype.card I - Fintype.card K) + Fintype.card I) := by
  obtain ⟨hl,hu⟩ := union_parts_card_bounds parts hdis w hsize univ
  rw [hcover,card_univ,card_univ] at hl hu
  have hKI : Fintype.card K ≤ Fintype.card I := Fintype.card_le_of_injective f f.injective
  have hsum : Fintype.card K + (Fintype.card I - Fintype.card K) = Fintype.card I := by omega
  refine ⟨(Nat.mul_le_mul_left w hKI).trans hl,?_⟩
  nlinarith


end MatchingStability

end PermutedModule59

/- Source module: LiftedExclusiveDensity.lean -/
section PermutedModule60

/-!
The density budget for lifting an exclusive extremal partition from a
completed reduced multicolouring to the host graph. Discarded clusters are
assigned to block 0, exactly as in HostBlockLifting. Credit: @fqlx.
-/

open Finset SimpleGraph

namespace MatchingStability

/-- A uniform real budget for reduced-pair failures, discarded clusters and
irregular pairs. The constant 1000 leaves a substantial margin. -/
theorem lifted_exclusive_density_budget
    (A B A₀ B₀ t e bad α β d μ θ : ℝ)
    (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀) (hAold : A₀ ≤ A) (hBold : B₀ ≤ B)
    (ht : 0 ≤ t) (hα : 0 ≤ α) (hμ : 0 ≤ μ)
    (hA : μ * t / 5 ≤ A) (hB : μ * t / 5 ≤ B)
    (he : e ≤ θ * t) (hbad : bad ≤ θ * t ^ 2)
    (hβ : β ≤ α / 100) (hd : d ≤ α / 100)
    (hθ : 1000 * θ ≤ α * μ ^ 2) :
    2 * d * A * B + β * A₀ * B₀ + 2 * e * t + bad ≤ α / 4 * A * B := by
  have hAN : 0 ≤ A := hA₀.trans hAold
  have hBN : 0 ≤ B := hB₀.trans hBold
  have hAB : 0 ≤ A * B := mul_nonneg hAN hBN
  have hAB₀ : 0 ≤ A₀ * B₀ := mul_nonneg hA₀ hB₀
  have hprod : A₀ * B₀ ≤ A * B := mul_le_mul hAold hBold hB₀ hAN
  have hd' := mul_le_mul_of_nonneg_right hd hAB
  have hβ' := mul_le_mul_of_nonneg_right hβ hAB₀
  have hprod' := mul_le_mul_of_nonneg_left hprod (show 0 ≤ α / 100 by positivity)
  have hbase : 0 ≤ μ * t / 5 := by positivity
  have hmin := mul_le_mul hA hB hbase hAN
  have hmin' := mul_le_mul_of_nonneg_left hmin hα
  have hθ' := mul_le_mul_of_nonneg_right hθ (sq_nonneg t)
  have he' := mul_le_mul_of_nonneg_right he ht
  have hnonneg := mul_nonneg hα hAB
  nlinarith

theorem selected_image_subset_extended
    {K I : Type*} [DecidableEq K] [Fintype I] [DecidableEq I]
    (T : Fin 4 → Finset K) (f : K ↪ I) (S : Finset (Fin 4)) :
    (S.biUnion T).image f ⊆
      S.biUnion (FinitePartitionExtension.extend (fun j => (T j).image f) 0) := by
  intro v hv
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
  obtain ⟨j,hj,haj⟩ := mem_biUnion.mp ha
  exact mem_biUnion.mpr ⟨j,hj,
    FinitePartitionExtension.subset_extend _ 0 j (mem_image_of_mem f haj)⟩

/-- All prescribed joins inherit host density `1-α` from a sufficiently
accurate exclusive reduced partition. The result uses exactly the lifted
block sets from the partition and size-transfer theorems. -/
theorem lifted_exclusive_densities
    {V K I : Type*} [DecidableEq V] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I]
    (c : Fin 3 → SimpleGraph V) [∀ k, DecidableRel (c k).Adj]
    (hc : (⊤ : SimpleGraph V).IsEdgeColouring c)
    (parts : I → Finset V) (η d : ℝ) (hd : 0 ≤ d)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hne : ∀ i, (parts i).Nonempty)
    (w : ℕ) (hw : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ 2 * w)
    (irregular : Finset (I × I))
    (hreg : ∀ u v, u ≠ v → (u,v) ∉ irregular →
      ∀ j, (c j).IsUniform η (parts u) (parts v))
    (f : K ↪ I) (C : Fin 3 → SimpleGraph K)
    (hpres : ∀ k a b,
      (ReducedMulticoloring.graph c parts η d k).Adj (f a) (f b) → (C k).Adj a b)
    (σ : Equiv.Perm (Fin 3)) (T : Fin 4 → Finset K) (hT : BlockPartition T)
    (L : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)))
    (hnonempty : ∀ k S U, (k,S,U) ∈ L → S.Nonempty ∧ U.Nonempty)
    (m : ℕ) (α β μ θ : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ)
    (hsource : ExclusiveDensities C σ T β L)
    (hlower : ∀ j, μ * m ≤ ((T j).card : ℝ))
    (htm : (Fintype.card I : ℝ) / 5 ≤ m)
    (hloss : ((Fintype.card I - Fintype.card K : ℕ) : ℝ) ≤ θ * Fintype.card I)
    (hirregular : (irregular.card : ℝ) ≤ θ * (Fintype.card I : ℝ) ^ 2)
    (hβsmall : β ≤ α / 100) (hdsmall : d ≤ α / 100)
    (hθsmall : 1000 * θ ≤ α * μ ^ 2) :
    let U : Fin 4 → Finset V := fun j =>
      (FinitePartitionExtension.extend (fun i => (T i).image f) 0 j).biUnion parts
    ∀ k S Q, (k,S,Q) ∈ L →
      (1 - α) * ((S.biUnion U).card : ℝ) * (Q.biUnion U).card ≤
        ∑ x ∈ S.biUnion U, (((Q.biUnion U).filter ((c (σ k)).Adj x)).card : ℝ) := by
  classical
  dsimp only
  intro k S Q hL
  let A₀ := S.biUnion T
  let B₀ := Q.biUnion T
  let blocks := FinitePartitionExtension.extend (fun i => (T i).image f) 0
  let A := S.biUnion blocks
  let B := Q.biUnion blocks
  let e := Fintype.card I - Fintype.card K
  have hAimage : A₀.image f ⊆ A := selected_image_subset_extended T f S
  have hBimage : B₀.image f ⊆ B := selected_image_subset_extended T f Q
  have hAoldNat : A₀.card ≤ A.card := by
    simpa only [card_image_of_injective _ f.injective] using card_le_card hAimage
  have hBoldNat : B₀.card ≤ B.card := by
    simpa only [card_image_of_injective _ f.injective] using card_le_card hBimage
  have hAdiff : (A \ A₀.image f).card ≤ e := by
    have hh := card_le_card
      (FinitePartitionExtension.selected_extension_difference_subset (fun i => (T i).image f) 0 S)
    rw [outside_image_blocks_card T hT f,selected_image_union T f S] at hh
    exact hh
  have hBdiff : (B \ B₀.image f).card ≤ e := by
    have hh := card_le_card
      (FinitePartitionExtension.selected_extension_difference_subset (fun i => (T i).image f) 0 Q)
    rw [outside_image_blocks_card T hT f,selected_image_union T f Q] at hh
    exact hh
  have hselectedLower : ∀ Z : Finset (Fin 4), Z.Nonempty →
      μ * m ≤ ((Z.biUnion T).card : ℝ) := by
    intro Z hZ
    obtain ⟨j,hj⟩ := hZ
    exact (hlower j).trans (Nat.cast_le.mpr
      (card_le_card (subset_biUnion_of_mem T hj)))
  have hA₀lower : μ * m ≤ (A₀.card : ℝ) := hselectedLower S (hnonempty k S Q hL).1
  have hB₀lower : μ * m ≤ (B₀.card : ℝ) := hselectedLower Q (hnonempty k S Q hL).2
  have hAold : (A₀.card : ℝ) ≤ A.card := by exact_mod_cast hAoldNat
  have hBold : (B₀.card : ℝ) ≤ B.card := by exact_mod_cast hBoldNat
  have hmul := mul_le_mul_of_nonneg_left htm hμ
  have hAlower : μ * Fintype.card I / 5 ≤ (A.card : ℝ) := by nlinarith
  have hBlower : μ * Fintype.card I / 5 ≤ (B.card : ℝ) := by nlinarith
  have hnum := lifted_exclusive_density_budget
    A.card B.card A₀.card B₀.card (Fintype.card I) e irregular.card α β d μ θ
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hAold hBold (Nat.cast_nonneg _) hα hμ
    hAlower hBlower hloss hirregular hβsmall hdsmall hθsmall
  have hbudget : 2 * d * A.card * B.card +
      (badExclusiveCount C (σ k) A₀ B₀ : ℝ) + 2 * e * Fintype.card I + irregular.card ≤
      α / 4 * A.card * B.card := by
    have hs := hsource k S Q hL
    change (badExclusiveCount C (σ k) A₀ B₀ : ℝ) ≤ β * A₀.card * B₀.card at hs
    linarith
  have hhost := extended_host_density c hc parts η d hd hdis hne w hw irregular hreg
    f C hpres (σ k) A₀ B₀ A B e hAdiff hBdiff α hα hbudget
  simpa only [A,B,blocks,Finset.biUnion_biUnion] using hhost


end MatchingStability

end PermutedModule60

/- Source module: HostBlockSizeTransfer.lean -/
section PermutedModule61

/-!
Explicit additive-error budgets transferring reduced block sizes to the host.
The stronger EC3 margins absorb both discarded clusters and the one-vertex
rounding in equitable classes. Credit: @fqlx.
-/

open Finset

namespace MatchingStability

theorem balanced_block_sizes_of_uniform_error
    {K V : Type*} (T : Fin 4 → Finset K) (U : Fin 4 → Finset V)
    (m M w E : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (hstage : BalancedBlockSizes T m (α / 2))
    (hlower : ∀ i, w * (T i).card ≤ (U i).card)
    (hscale : M ≤ w * m + E) (hbudget : 2 * (E : ℝ) ≤ α * M) :
    BalancedBlockSizes U M α := by
  intro i
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have he : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left (hstage i) hw
  have hlow : (w : ℝ) * (T i).card ≤ (U i).card := by exact_mod_cast hlower i
  have hq : (M : ℝ) ≤ (w : ℝ) * m + E := by exact_mod_cast hscale
  have hc : 0 ≤ 1 - α / 2 := by linarith
  have hshift := mul_le_mul_of_nonneg_left hq hc
  have hαE := mul_nonneg hα he
  nlinarith

theorem strong_ec3_block_sizes_of_uniform_error
    {K V : Type*} (T : Fin 4 → Finset K) (U : Fin 4 → Finset V)
    (m M w E : ℕ) (μ : ℝ) (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hstage : StrongEC3BlockSizes T m μ)
    (hbounds : ∀ i, w * (T i).card ≤ (U i).card ∧
      (U i).card ≤ w * (T i).card + E)
    (hscaleLower : w * m ≤ M) (hscaleUpper : M ≤ w * m + E)
    (hbudget : 10 * (E : ℝ) ≤ μ * M) :
    EC3BlockSizes U M μ := by
  let a : Fin 4 → ℝ := fun i => (T i).card
  let b : Fin 4 → ℝ := fun i => (U i).card
  let q : ℝ := (w : ℝ) * m
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have he : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hqlo : q ≤ M := by dsimp [q]; exact_mod_cast hscaleLower
  have hqhi : (M : ℝ) ≤ q + E := by dsimp [q]; exact_mod_cast hscaleUpper
  have hB (i : Fin 4) : (w : ℝ) * a i ≤ b i ∧ b i ≤ (w : ℝ) * a i + E := by
    dsimp [a,b]
    constructor
    · exact_mod_cast (hbounds i).1
    · exact_mod_cast (hbounds i).2
  have hsmall : (1 - 7 / 10 * μ) * m ≤ min (a 0) (min (a 1) (a 2)) := hstage.1
  have hD : 2 * μ * m ≤ a 3 := hstage.2.1
  have hgap : max (a 1) (max (a 2) (a 3)) + 2 * μ * m ≤ a 0 := hstage.2.2.1
  have hsum : a 0 + a 3 ≤ (1 + 1 / 5 * μ) * (2 * m) := hstage.2.2.2
  have hsmallBudget : (1 - 4 / 5 * μ) * M ≤ (1 - 7 / 10 * μ) * q := by
    have hc : 0 ≤ 1 - 7 / 10 * μ := by linarith
    have hshift := mul_le_mul_of_nonneg_left hqhi hc
    have hμE := mul_nonneg hμ he
    nlinarith
  have hgapBudget : (E : ℝ) + μ * M ≤ 2 * μ * q := by
    have hshift := mul_le_mul_of_nonneg_left hqhi (by positivity : 0 ≤ 2 * μ)
    have hμE := mul_le_mul_of_nonneg_right hμ₁ he
    nlinarith
  have hsumBudget : (1 + 1 / 5 * μ) * (2 * q) + 2 * E ≤
      (1 + 3 / 10 * μ) * (2 * M) := by
    have hc : 0 ≤ 2 * (1 + 1 / 5 * μ) := by positivity
    have hshift := mul_le_mul_of_nonneg_left hqlo hc
    nlinarith
  have hsmallTransfer (i : Fin 4) (hi : (1 - 7 / 10 * μ) * m ≤ a i) :
      (1 - 4 / 5 * μ) * M ≤ b i := by
    apply hsmallBudget.trans
    calc
      (1 - 7 / 10 * μ) * q = (w : ℝ) * ((1 - 7 / 10 * μ) * m) := by dsimp [q]; ring
      _ ≤ (w : ℝ) * a i := mul_le_mul_of_nonneg_left hi hw
      _ ≤ b i := (hB i).1
  have hgapTransfer (i : Fin 4) (hi : a i + 2 * μ * m ≤ a 0) :
      b i + μ * M ≤ b 0 := by
    have hscaled := mul_le_mul_of_nonneg_left hi hw
    have hiB := (hB i).2
    have hzeroB := (hB 0).1
    dsimp [q] at hgapBudget
    nlinarith
  change (1 - 4 / 5 * μ) * M ≤ min (b 0) (min (b 1) (b 2)) ∧
    μ * M ≤ b 3 ∧ max (b 1) (max (b 2) (b 3)) + μ * M ≤ b 0 ∧
    b 0 + b 3 ≤ (1 + 3 / 10 * μ) * (2 * M)
  refine ⟨?_,?_,?_,?_⟩
  · exact le_min (hsmallTransfer 0 (hsmall.trans (min_le_left _ _)))
      (le_min (hsmallTransfer 1 (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))))
        (hsmallTransfer 2 (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))))
  · have hscaled := mul_le_mul_of_nonneg_left hD hw
    have hthree := (hB 3).1
    dsimp [q] at hgapBudget
    nlinarith
  · have ha1 : a 1 ≤ max (a 1) (max (a 2) (a 3)) := le_max_left _ _
    have ha2 : a 2 ≤ max (a 1) (max (a 2) (a 3)) :=
      (le_max_left (a 2) (a 3)).trans (le_max_right _ _)
    have ha3 : a 3 ≤ max (a 1) (max (a 2) (a 3)) :=
      (le_max_right (a 2) (a 3)).trans (le_max_right _ _)
    have h1 := hgapTransfer 1 (by linarith)
    have h2 := hgapTransfer 2 (by linarith)
    have h3 := hgapTransfer 3 (by linarith)
    have hbmax : max (b 1) (max (b 2) (b 3)) ≤ b 0 - μ * M := by
      exact max_le (by linarith) (max_le (by linarith) (by linarith))
    linarith
  · have hscaled := mul_le_mul_of_nonneg_left hsum hw
    have hzero := (hB 0).2
    have hthree := (hB 3).2
    dsimp [q] at hsumBudget
    nlinarith

theorem lifted_host_quarter_error
    {K I V : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V]
    (f : K ↪ I) (parts : I → Finset V)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hcover : univ.biUnion parts = univ)
    (w : ℕ) (hsize : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ w + 1)
    (m M : ℕ) (hK : Fintype.card K = 4 * m) (hV : Fintype.card V = 4 * M) :
    w * m ≤ M ∧ M ≤ w * m +
      (w * (Fintype.card I - Fintype.card K) + Fintype.card I) := by
  obtain ⟨hl,hu⟩ := host_card_error f parts hdis hcover w hsize
  rw [hK,hV] at hl hu
  rw [hK]
  constructor <;> nlinarith

theorem balanced_lifted_block_sizes
    {K I V : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V]
    (T : Fin 4 → Finset K) (hT : BlockPartition T) (f : K ↪ I)
    (parts : I → Finset V)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hcover : univ.biUnion parts = univ)
    (w : ℕ) (hsize : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ w + 1)
    (m M : ℕ) (hK : Fintype.card K = 4 * m) (hV : Fintype.card V = 4 * M)
    (α : ℝ) (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (hstage : BalancedBlockSizes T m (α / 2))
    (hbudget : 2 * ((w * (Fintype.card I - Fintype.card K) + Fintype.card I : ℕ) : ℝ) ≤
      α * (M : ℝ)) :
    BalancedBlockSizes (fun j =>
      (FinitePartitionExtension.extend (fun i => (T i).image f) 0 j).biUnion parts) M α := by
  apply balanced_block_sizes_of_uniform_error T _ m M w
    (w * (Fintype.card I - Fintype.card K) + Fintype.card I) α hα hα₁ hstage
    (fun i => (lifted_block_card_bounds T hT f parts hdis w hsize i).1)
    (lifted_host_quarter_error f parts hdis hcover w hsize m M hK hV).2
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudget

theorem strong_ec3_lifted_block_sizes
    {K I V : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V]
    (T : Fin 4 → Finset K) (hT : BlockPartition T) (f : K ↪ I)
    (parts : I → Finset V)
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hcover : univ.biUnion parts = univ)
    (w : ℕ) (hsize : ∀ i, w ≤ (parts i).card ∧ (parts i).card ≤ w + 1)
    (m M : ℕ) (hK : Fintype.card K = 4 * m) (hV : Fintype.card V = 4 * M)
    (μ : ℝ) (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hstage : StrongEC3BlockSizes T m μ)
    (hbudget : 10 * ((w * (Fintype.card I - Fintype.card K) + Fintype.card I : ℕ) : ℝ) ≤
      μ * (M : ℝ)) :
    EC3BlockSizes (fun j =>
      (FinitePartitionExtension.extend (fun i => (T i).image f) 0 j).biUnion parts) M μ := by
  obtain ⟨hl,hu⟩ := lifted_host_quarter_error f parts hdis hcover w hsize m M hK hV
  apply strong_ec3_block_sizes_of_uniform_error T _ m M w
    (w * (Fintype.card I - Fintype.card K) + Fintype.card I) μ hμ hμ₁ hstage
    (fun i => lifted_block_uniform_error T hT f parts hdis w hsize i) hl hu
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudget


end MatchingStability

end PermutedModule61

/- Source module: HostBlockErrorBudgets.lean -/
section PermutedModule62

/-!
Small arithmetic interfaces for the host lifting error `w * loss + t`.
They separate fractional cluster loss from equitable-part rounding.
Credit: @fqlx.
-/

namespace MatchingStability

theorem cluster_error_budget
    (N t w loss : ℕ) (C θ : ℝ) (hθ : 0 ≤ θ)
    (hwt : w * t ≤ N)
    (hloss : C * loss ≤ θ * t) (hround : C * t ≤ θ * N) :
    C * ((w * loss + t : ℕ) : ℝ) ≤ 2 * θ * N := by
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hscale := mul_le_mul_of_nonneg_left hloss hw
  have hwt' : (w : ℝ) * t ≤ N := by exact_mod_cast hwt
  have hhost := mul_le_mul_of_nonneg_left hwt' hθ
  simp only [Nat.cast_add,Nat.cast_mul]
  nlinarith

theorem balanced_cluster_error_budget
    (N M t w loss : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (hN : N = 4 * M) (hwt : w * t ≤ N)
    (hloss : 16 * (loss : ℝ) ≤ α * t)
    (hround : 16 * (t : ℝ) ≤ α * N) :
    2 * ((w * loss + t : ℕ) : ℝ) ≤ α * M := by
  have h := cluster_error_budget N t w loss 16 α hα hwt hloss hround
  have hN' : (N : ℝ) = 4 * M := by exact_mod_cast hN
  nlinarith

theorem ec3_cluster_error_budget
    (N M t w loss : ℕ) (μ : ℝ) (hμ : 0 ≤ μ)
    (hN : N = 4 * M) (hwt : w * t ≤ N)
    (hloss : 80 * (loss : ℝ) ≤ μ * t)
    (hround : 80 * (t : ℝ) ≤ μ * N) :
    10 * ((w * loss + t : ℕ) : ℝ) ≤ μ * M := by
  have h := cluster_error_budget N t w loss 80 μ hμ hwt hloss hround
  have hN' : (N : ℝ) = 4 * M := by exact_mod_cast hN
  nlinarith

theorem cluster_error_le_five
    (N M t w loss : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hN : N = 4 * M) (hwt : w * t ≤ N)
    (hloss : (loss : ℝ) ≤ θ * t)
    (hround : 4 * (t : ℝ) ≤ θ * N) :
    ((w * loss + t : ℕ) : ℝ) ≤ 5 * θ * M := by
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hscale := mul_le_mul_of_nonneg_left hloss hw
  have hwt' : (w : ℝ) * t ≤ N := by exact_mod_cast hwt
  have hhost := mul_le_mul_of_nonneg_left hwt' hθ
  have hN' : (N : ℝ) = 4 * M := by exact_mod_cast hN
  simp only [Nat.cast_add,Nat.cast_mul]
  nlinarith


end MatchingStability

end PermutedModule62

/- Source module: HostExtremalTransfer.lean -/
section PermutedModule63

/-!
Final transfer from the finite reduced alternatives to the three host
extremal configurations. Size and density estimates use the same lifted
block partition, with omitted clusters assigned to block 0. Credit: @fqlx.
-/

open Finset SimpleGraph

namespace MatchingStability
namespace HostReducedData

variable {M : ℕ} {c : Fin 3 → SimpleGraph (Fin (4 * M))}
  [∀ k, DecidableRel (c k).Adj] {α μ δ θ d : ℝ}

theorem transfer_error_budgets (D : HostReducedData M c α μ δ θ d)
    (p : TransferParameters α μ δ θ d) :
    2 * ((D.w * (D.t - 4 * D.m) + D.t : ℕ) : ℝ) ≤ α * M ∧
      10 * ((D.w * (D.t - 4 * D.m) + D.t : ℕ) : ℝ) ≤ μ * M := by
  have hE := cluster_error_le_five (4 * M) M D.t D.w (D.t - 4 * D.m)
    θ p.theta_pos.le rfl D.weight_bound D.core_loss
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using D.host_rounding)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hα := mul_le_mul_of_nonneg_right p.theta_alpha hM
  have hμ := mul_le_mul_of_nonneg_right p.theta_mu hM
  have hθM := mul_nonneg p.theta_pos.le hM
  constructor <;> nlinarith

theorem transfer_balanced (D : HostReducedData M c α μ δ θ d)
    (p : TransferParameters α μ δ θ d)
    (hc : (⊤ : SimpleGraph (Fin (4 * M))).IsEdgeColouring c)
    (σ : Equiv.Perm (Fin 3)) (T : Fin 4 → Finset (Fin (4 * D.m)))
    (hT : BlockPartition T)
    (J : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)))
    (hnonempty : ∀ k S Q, (k,S,Q) ∈ J → S.Nonempty ∧ Q.Nonempty)
    (hs : BalancedBlockSizes T D.m (α / 100))
    (hdensity : ExclusiveDensities D.core_colors σ T (α / 100) J) :
    ∃ U : Fin 4 → Finset (Fin (4 * M)), BlockPartition U ∧
      BalancedBlockSizes U M α ∧ HostDensities c σ U α J := by
  let U : Fin 4 → Finset (Fin (4 * M)) := fun j =>
    (FinitePartitionExtension.extend (fun i => (T i).image D.core_embedding) 0 j).biUnion D.parts
  have hU : BlockPartition U := lifted_blocks_partition T hT D.core_embedding D.parts
    D.parts_disjoint D.parts_cover
  have hstage : BalancedBlockSizes T D.m (α / 2) := by
    intro i
    have hh := hs i
    have hm : (0 : ℝ) ≤ D.m := Nat.cast_nonneg _
    have hαm := mul_nonneg p.alpha_pos.le hm
    nlinarith
  have hbudget : 2 * ((D.w * (Fintype.card (Fin D.t) - Fintype.card (Fin (4 * D.m))) +
      Fintype.card (Fin D.t) : ℕ) : ℝ) ≤ α * M := by
    simpa only [Fintype.card_fin] using (D.transfer_error_budgets p).1
  have hsizes : BalancedBlockSizes U M α := balanced_lifted_block_sizes T hT
    D.core_embedding D.parts D.parts_disjoint D.parts_cover D.w D.parts_size D.m M
    (by simp) (by simp) α p.alpha_pos.le p.alpha_small hstage hbudget
  have hsize2 : ∀ i, D.w ≤ (D.parts i).card ∧ (D.parts i).card ≤ 2 * D.w := by
    intro i
    have hh := D.parts_size i
    have hw := D.w_pos
    exact ⟨hh.1,by omega⟩
  have hden : HostDensities c σ U α J := by
    exact lifted_exclusive_densities c hc D.parts (2 * D.epsilon) d p.d_pos.le
      D.parts_disjoint D.parts_nonempty D.w hsize2 D.irregular D.regular
      D.core_embedding D.core_colors D.preserves σ T hT J hnonempty D.m
      α (α / 100) μ θ p.alpha_pos.le p.mu_pos.le hdensity
      (p.balanced_minimum T D.m hs)
      (by simpa only [Fintype.card_fin] using D.m_lower)
      (by simpa only [Fintype.card_fin] using D.core_loss)
      (by simpa only [Fintype.card_fin] using D.irregular_card)
      le_rfl p.d_alpha p.density_alpha
  exact ⟨U,hU,hsizes,hden⟩

theorem transfer_ec3 (D : HostReducedData M c α μ δ θ d)
    (p : TransferParameters α μ δ θ d)
    (hc : (⊤ : SimpleGraph (Fin (4 * M))).IsEdgeColouring c)
    (σ : Equiv.Perm (Fin 3)) (T : Fin 4 → Finset (Fin (4 * D.m)))
    (hT : BlockPartition T) (hs : StrongEC3BlockSizes T D.m μ)
    (hdensity : ExclusiveDensities D.core_colors σ T (δ / 100) EC1Joins) :
    ∃ U : Fin 4 → Finset (Fin (4 * M)), BlockPartition U ∧
      EC3BlockSizes U M μ ∧ HostDensities c σ U δ EC1Joins := by
  let U : Fin 4 → Finset (Fin (4 * M)) := fun j =>
    (FinitePartitionExtension.extend (fun i => (T i).image D.core_embedding) 0 j).biUnion D.parts
  have hU : BlockPartition U := lifted_blocks_partition T hT D.core_embedding D.parts
    D.parts_disjoint D.parts_cover
  have hbudget : 10 * ((D.w * (Fintype.card (Fin D.t) - Fintype.card (Fin (4 * D.m))) +
      Fintype.card (Fin D.t) : ℕ) : ℝ) ≤ μ * M := by
    simpa only [Fintype.card_fin] using (D.transfer_error_budgets p).2
  have hsizes : EC3BlockSizes U M μ := strong_ec3_lifted_block_sizes T hT
    D.core_embedding D.parts D.parts_disjoint D.parts_cover D.w D.parts_size D.m M
    (by simp) (by simp) μ p.mu_pos.le p.mu_le_one hs hbudget
  have hsize2 : ∀ i, D.w ≤ (D.parts i).card ∧ (D.parts i).card ≤ 2 * D.w := by
    intro i
    have hh := D.parts_size i
    have hw := D.w_pos
    exact ⟨hh.1,by omega⟩
  have hden : HostDensities c σ U δ EC1Joins := by
    exact lifted_exclusive_densities c hc D.parts (2 * D.epsilon) d p.d_pos.le
      D.parts_disjoint D.parts_nonempty D.w hsize2 D.irregular D.regular
      D.core_embedding D.core_colors D.preserves σ T hT EC1Joins EC1Joins_nonempty D.m
      δ (δ / 100) μ θ p.delta_pos.le p.mu_pos.le hdensity
      (p.strong_ec3_minimum T D.m hs)
      (by simpa only [Fintype.card_fin] using D.m_lower)
      (by simpa only [Fintype.card_fin] using D.core_loss)
      (by simpa only [Fintype.card_fin] using D.irregular_card)
      le_rfl p.d_delta p.density_delta
  exact ⟨U,hU,hsizes,hden⟩

theorem to_host_extremal (D : HostReducedData M c α μ δ θ d)
    (p : TransferParameters α μ δ θ d)
    (hc : (⊤ : SimpleGraph (Fin (4 * M))).IsEdgeColouring c) :
    HostEC1 M c α ∨ HostEC2 M c α ∨ HostEC3 M c μ δ := by
  rcases D.alternatives with h1 | h2 | h3
  · obtain ⟨σ,T,hT,hs,hd⟩ := h1
    obtain ⟨U,hU,hsize,hdensity⟩ := D.transfer_balanced p hc σ T hT EC1Joins
      EC1Joins_nonempty hs hd
    exact Or.inl ⟨σ,U,hU,hsize,hdensity⟩
  · obtain ⟨σ,T,hT,hs,hd⟩ := h2
    obtain ⟨U,hU,hsize,hdensity⟩ := D.transfer_balanced p hc σ T hT EC2Joins
      EC2Joins_nonempty hs hd
    exact Or.inr (Or.inl ⟨σ,U,hU,hsize,hdensity⟩)
  · obtain ⟨σ,T,hT,hs,hd⟩ := h3
    obtain ⟨U,hU,hsize,hdensity⟩ := D.transfer_ec3 p hc σ T hT hs hd
    exact Or.inr (Or.inr ⟨σ,U,hU,hsize,hdensity⟩)


end HostReducedData
end MatchingStability

end PermutedModule63

/- Source module: EC1Pattern.lean -/
section PermutedModule64

namespace EC1Pattern

/-- Red, blue, green are 0,1,2; the four blocks are X,Y,Z,W. -/
def pairColour (a b : Fin 4) : Fin 3 :=
  if a.val / 2 = b.val / 2 then 0 else if a.val % 2 = b.val % 2 then 1 else 2

def partner (c : Fin 3) (a : Fin 4) : Fin 4 :=
  ![![1,0,3,2], ![2,3,0,1], ![3,2,1,0]] c a

theorem pairColour_symm (a b : Fin 4) : pairColour a b = pairColour b a := by
  fin_cases a <;> fin_cases b <;> decide

theorem partner_ne (c : Fin 3) (a : Fin 4) : partner c a ≠ a := by
  fin_cases c <;> fin_cases a <;> decide

theorem partner_colour (c : Fin 3) (a : Fin 4) : pairColour a (partner c a) = c := by
  fin_cases c <;> fin_cases a <;> decide

theorem partner_involution (c : Fin 3) (a : Fin 4) : partner c (partner c a) = a := by
  fin_cases c <;> fin_cases a <;> decide

theorem different_components {a b : Fin 4} {c : Fin 3}
    (hab : a ≠ b) (hc : c ≠ pairColour a b) :
    a ≠ partner c b ∧ partner c a ≠ b ∧ partner c a ≠ partner c b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all [pairColour, partner]

abbrev WrongPair :=
  {p : Fin 4 × Fin 4 × Fin 3 // p.1 < p.2.1 ∧ p.2.2 ≠ pairColour p.1 p.2.1}

theorem card_wrongPair : Fintype.card WrongPair = 12 := by decide

end EC1Pattern

end PermutedModule64

/- Source module: EC1Parameters.lean -/
section PermutedModule65

open Finset

namespace EC1Parameters

noncomputable def alpha0 : ℝ := 1 / 1000000000000
def cleaningThreshold (m : ℕ) : ℕ := m / 100000
def errorBudget (m : ℕ) : ℕ := 12 * cleaningThreshold m + 24

theorem alpha0_pos : 0 < alpha0 := by norm_num [alpha0]

theorem fixed_constants (m : ℕ) (hm : 1000000000 ≤ m) :
    1 ≤ cleaningThreshold m ∧
    1000 * errorBudget m ≤ m ∧
    m ≤ 200000 * cleaningThreshold m ∧
    m / 2 + 2 * cleaningThreshold m + 2 + errorBudget m ≤ m ∧
    100 * (errorBudget m + 6) + 1000 ≤ m := by
  dsimp only [cleaningThreshold, errorBudget]
  omega

theorem alpha_mul_le_threshold (m : ℕ) (hm : 1000000000 ≤ m)
    (α : ℝ) (hα : α ≤ alpha0) :
    α * (m : ℝ) ≤ cleaningThreshold m := by
  have hmd : (m : ℝ) ≤ 200000 * (cleaningThreshold m : ℝ) := by
    exact_mod_cast (fixed_constants m hm).2.2.1
  calc
    α * (m : ℝ) ≤ alpha0 * m := mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg m)
    _ ≤ alpha0 * (200000 * (cleaningThreshold m : ℝ)) :=
      mul_le_mul_of_nonneg_left hmd alpha0_pos.le
    _ ≤ cleaningThreshold m := by
      dsimp only [alpha0]
      nlinarith [Nat.cast_nonneg (α := ℝ) (cleaningThreshold m)]

theorem block_upper {m : ℕ} {α : ℝ} (a : Fin 4 → ℕ)
    (hsum : ∑ i, a i = 4 * m)
    (hlower : ∀ i, (1 - α) * (m : ℝ) ≤ a i) :
    ∀ i, (a i : ℝ) ≤ (1 + 3 * α) * m := by
  have hsum' : a 0 + a 1 + a 2 + a 3 = 4 * m := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hsumR : (a 0 : ℝ) + a 1 + a 2 + a 3 = 4 * (m : ℝ) := by exact_mod_cast hsum'
  have h0 := hlower 0
  have h1 := hlower 1
  have h2 := hlower 2
  have h3 := hlower 3
  intro i
  fin_cases i
  · change (a 0 : ℝ) ≤ (1 + 3 * α) * m
    nlinarith
  · change (a 1 : ℝ) ≤ (1 + 3 * α) * m
    nlinarith
  · change (a 2 : ℝ) ≤ (1 + 3 * α) * m
    nlinarith
  · change (a 3 : ℝ) ≤ (1 + 3 * α) * m
    nlinarith

theorem block_upper_nat {m : ℕ} (hm : 1000000000 ≤ m)
    {α : ℝ} (hα : α ≤ alpha0) (a : Fin 4 → ℕ)
    (hsum : ∑ i, a i = 4 * m)
    (hlower : ∀ i, (1 - α) * (m : ℝ) ≤ a i) :
    ∀ i, a i ≤ m + 3 * cleaningThreshold m := by
  intro i
  have hu := block_upper a hsum hlower i
  have ht := alpha_mul_le_threshold m hm α hα
  have h : (a i : ℝ) ≤ m + 3 * (cleaningThreshold m : ℝ) := by nlinarith
  exact_mod_cast h

theorem density_budget {m w z : ℕ} (hm : 1000000000 ≤ m)
    (hw : w ≤ 2 * m) (hz : z ≤ 2 * m)
    {α : ℝ} (hα : α ≤ alpha0) :
    α * (w : ℝ) * z ≤ (cleaningThreshold m : ℝ) * cleaningThreshold m := by
  have hwR : (w : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hw
  have hzR : (z : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hz
  have hmd : (m : ℝ) ≤ 200000 * (cleaningThreshold m : ℝ) := by
    exact_mod_cast (fixed_constants m hm).2.2.1
  have hsquare : (m : ℝ) * m ≤
      (200000 * (cleaningThreshold m : ℝ)) * (200000 * cleaningThreshold m) :=
    mul_le_mul hmd hmd (Nat.cast_nonneg m) (by positivity)
  calc
    α * (w : ℝ) * z ≤ alpha0 * w * z :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg w)) (Nat.cast_nonneg z)
    _ ≤ alpha0 * (2 * (m : ℝ)) * (2 * m) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hwR alpha0_pos.le) hzR
        (Nat.cast_nonneg z) (mul_nonneg alpha0_pos.le (by positivity))
    _ ≤ (cleaningThreshold m : ℝ) * cleaningThreshold m := by
      dsimp only [alpha0]
      nlinarith only [hsquare, mul_self_nonneg (cleaningThreshold m : ℝ)]

theorem cleaned_core_size {m w k : ℕ} (hm : 1000000000 ≤ m)
    {α : ℝ} (hα : α ≤ alpha0)
    (hlower : (1 - α) * (m : ℝ) ≤ w)
    (hloss : w ≤ k + 3 * cleaningThreshold m + 24) :
    m ≤ k + errorBudget m := by
  have ht := alpha_mul_le_threshold m hm α hα
  have hL : (w : ℝ) ≤ k + 3 * (cleaningThreshold m : ℝ) + 24 := by exact_mod_cast hloss
  have h : (m : ℝ) ≤ k + 12 * (cleaningThreshold m : ℝ) + 24 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (cleaningThreshold m)]
  dsimp only [errorBudget]
  exact_mod_cast h


end EC1Parameters

end PermutedModule65

/- Source module: EC1OriginalInterface.lean -/
section PermutedModule66

open Finset SimpleGraph Filter
open scoped BigOperators

namespace EC1OriginalInterface

/-- The original accepted R1.H1 interface, repeated here only to permit a
narrow-import check of the conversion. The final theorem uses the actual R1.H1. -/
def OriginalEC1 : Prop :=
  ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ᶠ n : ℕ in atTop, Even n →
      ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)), (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∀ f : Fin (2 * n) → Fin 4,
          (∀ j, (1 - α) * n / 2 ≤ (Nat.card {v // f v = j} : ℝ)) →
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - α) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ)) →
          ∃ i, cycleGraph n ⊑ c i

/-- Count a bipartite relation using its degrees. This is the cardinality
adapter already used in the checked EC2 interface proof. -/
theorem relation_count {V : Type*} [Fintype V] [DecidableEq V]
    (X Y : Finset V) (r : V → V → Prop) [DecidableRel r] :
    Nat.card {e : V × V // e.1 ∈ X ∧ e.2 ∈ Y ∧ r e.1 e.2} =
      ∑ x ∈ X, (Y.filter (r x)).card := by
  classical
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun x y : V => x ∈ X ∧ y ∈ Y ∧ r x y)), Fintype.card_sigma]
  calc
    _ = ∑ x : V, if x ∈ X then (Y.filter (r x)).card else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ X
      · simp only [if_pos hx, Fintype.card_subtype]
        congr 1
        ext y
        simp [hx]
      · simp [hx]
    _ = _ := by simp

theorem relation_count_symm {V : Type*} [Fintype V] [DecidableEq V]
    (X Y : Finset V) (r : V → V → Prop) [DecidableRel r]
    (hr : ∀ x y, r x y → r y x) :
    (∑ x ∈ X, (Y.filter (r x)).card) = ∑ y ∈ Y, (X.filter (r y)).card := by
  rw [← relation_count X Y r, ← relation_count Y X r]
  apply Nat.card_congr
  exact {
    toFun := fun e => ⟨(e.val.2,e.val.1),e.property.2.1,e.property.1,
      hr _ _ e.property.2.2⟩
    invFun := fun e => ⟨(e.val.2,e.val.1),e.property.2.1,e.property.1,
      hr _ _ e.property.2.2⟩
    left_inv := fun e => by cases e; rfl
    right_inv := fun e => by cases e; rfl }

/-- Convert the finite EC1 theorem to the exact original quantifiers and
colour convention. The finite theorem is supplied by the actual absorption proof. -/
theorem original_of_finite
    (hfinite : ∀ {V : Type} [Fintype V] [DecidableEq V]
      (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
      (W : Fin 4 → Finset V) (m : ℕ), 1000000000 ≤ m →
      Fintype.card V = 4*m →
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) →
      (∑ i, (W i).card) = 4*m →
      ∀ α : ℝ, α ≤ EC1Parameters.alpha0 →
      (∀ i, (1-α)*(m : ℝ) ≤ (W i).card) →
      (∀ i j, i ≠ j →
        (1-α)*((W i).card : ℝ)*(W j).card ≤
          ∑ x ∈ W i, (((W j).filter ((c (EC1Pattern.pairColour i j)).Adj x)).card : ℝ)) →
      (∀ x y : V, x ≠ y → ∃ k, (c k).Adj x y) →
      (∀ (i j : Fin 3) (x y : V), (c i).Adj x y → (c j).Adj x y → i=j) →
      ∃ i, cycleGraph (2*m) ⊑ c i) : OriginalEC1 := by
  classical
  refine ⟨EC1Parameters.alpha0,EC1Parameters.alpha0_pos,?_⟩
  intro α _ hα
  filter_upwards [Filter.eventually_ge_atTop (2*1000000000)] with n hn
  intro heven
  obtain ⟨m,rfl⟩ := heven
  have hlen : m+m=2*m := by omega
  rw [hlen,show 2*(2*m)=4*m by omega]
  intro c hcolour f hsize hdensity
  letI : ∀ i, DecidableRel (c i).Adj := fun i => Classical.decRel _
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let c' := fun i => c (σ i)
  let W (j : Fin 4) : Finset (Fin (4*m)) := univ.filter (fun v => f v=j)
  let B (S : Finset (Fin 4)) : Finset (Fin (4*m)) := univ.filter (fun v => f v∈S)
  have b_single (j : Fin 4) : B {j}=W j := by ext v; simp [B,W]
  have count (S : Finset (Fin 4)) :
      Nat.card {v : Fin (4*m) // f v∈S} = (B S).card := by
    simp [B,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have pair_count (k : Fin 3) (S T : Finset (Fin 4)) :
      Nat.card {e : Fin (4*m) × Fin (4*m) //
        f e.1∈S ∧ f e.2∈T ∧ (c k).Adj e.1 e.2} =
        ∑ x ∈ B S, ((B T).filter ((c k).Adj x)).card := by
    simpa only [B,mem_filter,mem_univ,true_and] using
      relation_count (B S) (B T) ((c k).Adj)
  have dense (k : Fin 3) (S T : Finset (Fin 4))
      (hmem : (k,S,T) ∈
        ([(0,{0},{1}),(0,{2},{3}),(1,{0},{3}),(1,{1},{2}),(2,{0},{2}),(2,{1},{3})] :
          List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)))) :
      (1-α)*((B S).card : ℝ)*(B T).card ≤
        ∑ x ∈ B S, (((B T).filter ((c k).Adj x)).card : ℝ) := by
    have h := hdensity k S T hmem
    rw [count S,count T,pair_count k S T] at h
    push_cast at h
    exact h
  have hmem (i j : Fin 4) (hij : i < j) :
      (σ (EC1Pattern.pairColour i j),{i},{j}) ∈
        ([(0,{0},{1}),(0,{2},{3}),(1,{0},{3}),(1,{1},{2}),(2,{0},{2}),(2,{1},{3})] :
          List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) := by
    revert i j
    decide
  have hdense_up (i j : Fin 4) (hij : i < j) :
      (1-α)*((W i).card : ℝ)*(W j).card ≤
        ∑ x ∈ W i, (((W j).filter ((c' (EC1Pattern.pairColour i j)).Adj x)).card : ℝ) := by
    simpa only [b_single] using dense _ _ _ (hmem i j hij)
  have hdense (i j : Fin 4) (hij : i≠ j) :
      (1-α)*((W i).card : ℝ)*(W j).card ≤
        ∑ x ∈ W i, (((W j).filter ((c' (EC1Pattern.pairColour i j)).Adj x)).card : ℝ) := by
    by_cases hlt : i < j
    · exact hdense_up i j hlt
    have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hij.symm
    calc
      _ = (1-α)*((W j).card : ℝ)*(W i).card := by ring
      _ ≤ ∑ x ∈ W j, (((W i).filter ((c' (EC1Pattern.pairColour i j)).Adj x)).card : ℝ) := by
        simpa only [EC1Pattern.pairColour_symm j i] using hdense_up j i hgt
      _ = _ := by
        exact_mod_cast relation_count_symm (W j) (W i)
          ((c' (EC1Pattern.pairColour i j)).Adj) (fun _ _ h => h.symm)
  have hdis (i j : Fin 4) (hij : i≠ j) : Disjoint (W i) (W j) := by
    apply Finset.disjoint_left.mpr
    intro v hi hj
    exact hij ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)
  have hsum : (∑ i, (W i).card)=4*m := by
    simpa [W] using sum_card_fiberwise_eq_card_filter
      (univ : Finset (Fin (4*m))) (univ : Finset (Fin 4)) f
  have hlower (i : Fin 4) : (1-α)*(m : ℝ) ≤ (W i).card := by
    have h := hsize i
    have hc : Nat.card {v : Fin (4*m) // f v=i} = (W i).card := by
      simp [W,Nat.card_eq_fintype_card,Fintype.card_subtype]
    have heq : (1-α)*((2*m : ℕ) : ℝ)/2=(1-α)*(m : ℝ) := by push_cast; ring
    rwa [hc,heq] at h
  have hcover (x y : Fin (4*m)) (hxy : x≠ y) : ∃ k, (c' k).Adj x y := by
    have h : (⊤ : SimpleGraph (Fin (4*m))).Adj x y := hxy
    rw [hcolour.1,SimpleGraph.iSup_adj] at h
    obtain ⟨k,hk⟩ := h
    exact ⟨σ.symm k,by simpa [c'] using hk⟩
  have hunique (i j : Fin 3) (x y : Fin (4*m))
      (hi : (c' i).Adj x y) (hj : (c' j).Adj x y) : i=j := by
    apply σ.injective
    by_contra hne
    exact SimpleGraph.disjoint_left.mp (hcolour.2 (σ i) (σ j) hne) x y hi hj
  obtain ⟨i,hi⟩ := hfinite c' W m (by omega) (by simp) hdis hsum α hα hlower hdense hcover hunique
  exact ⟨σ i,hi⟩

end EC1OriginalInterface


end PermutedModule66

/- Source module: PermutedHostStability.lean -/
section PermutedModule67

/-!
The stability alternative with its necessary permutation of the three colours.
This interface uses no absorption theorem. It is proved directly from common
regularity, connected-matching stability and host transfer. Credit: @fqlx.
-/

open SimpleGraph Filter Finset

namespace MatchingStability

def PermutedHostStability : Prop :=
  ∃ α₀ μ₀ : ℝ, 0 < α₀ ∧ 0 < μ₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ μ₁ : ℝ, 0 < μ₁ → μ₁ ≤ μ₀ → ∃ μ : ℝ, 0 < μ ∧ μ < μ₁ ∧
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, Even n →
    ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)),
      (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
      (∃ i, cycleGraph n ⊑ c i) ∨
      ∃ (σ : Equiv.Perm (Fin 3)) (f : Fin (2 * n) → Fin 4),
        let a : Fin 4 → ℝ := fun j => Nat.card {v // f v = j}
        let J : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)) :=
          [(0,{0},{1}),(0,{2},{3}),(1,{0},{3}),(1,{1},{2}),(2,{0},{2}),(2,{1},{3})]
        let D := fun (β : ℝ) (L : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) =>
          ∀ k S T, (k,S,T) ∈ L →
            (1 - β) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) //
                f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c (σ k)).Adj e.1 e.2} : ℝ)
        ((∀ j, (1 - α) * n / 2 ≤ a j) ∧ D α J) ∨
        ((∀ j, (1 - α) * n / 2 ≤ a j) ∧ D α [(0,{0},{1}),(1,{0,1},{2}),(2,{0,1},{3})]) ∨
        (((1 - 4 / 5 * μ) * n / 2 ≤ min (a 0) (min (a 1) (a 2)) ∧
          μ * n / 2 ≤ a 3 ∧ max (a 1) (max (a 2) (a 3)) + μ * n / 2 ≤ a 0 ∧
          a 0 + a 3 ≤ (1 + 3 / 10 * μ) * n) ∧ D δ J)

theorem labeled_density_of_block_partition
    (N : ℕ) (c : Fin 3 → SimpleGraph (Fin N)) [∀ k, DecidableRel (c k).Adj]
    (σ : Equiv.Perm (Fin 3)) (U : Fin 4 → Finset (Fin N))
    (hU : BlockPartition U) (β : ℝ)
    (J : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)))
    (hdense : HostDensities c σ U β J) :
    ∃ f : Fin N → Fin 4,
      (∀ j, Nat.card {v // f v = j} = (U j).card) ∧
      (∀ k S T, (k,S,T) ∈ J →
        (1 - β) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
          (Nat.card {e : Fin N × Fin N //
            f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c (σ k)).Adj e.1 e.2} : ℝ)) := by
  classical
  obtain ⟨f,hf⟩ := FinitePartitionExtension.assignment_of_partition U hU.1 hU.2
  have hsel (S : Finset (Fin 4)) :
      (univ.filter (fun v : Fin N => f v ∈ S)) = S.biUnion U := by
    ext v
    simp only [mem_filter,mem_univ,true_and,mem_biUnion]
    constructor
    · intro h
      exact ⟨f v,h,(hf v (f v)).mp rfl⟩
    · rintro ⟨i,hi,hvi⟩
      exact (hf v i).mpr hvi ▸ hi
  have hcount (S : Finset (Fin 4)) :
      Nat.card {v : Fin N // f v ∈ S} = (S.biUnion U).card := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,hsel]
  refine ⟨f,?_,?_⟩
  · intro j
    simpa only [mem_singleton,Finset.singleton_biUnion] using hcount {j}
  · intro k S T hJ
    have hpair : Nat.card {e : Fin N × Fin N //
        f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c (σ k)).Adj e.1 e.2} =
        ∑ x ∈ S.biUnion U, ((T.biUnion U).filter ((c (σ k)).Adj x)).card := by
      have h := EC1OriginalInterface.relation_count
        (univ.filter (fun v : Fin N => f v ∈ S))
        (univ.filter (fun v : Fin N => f v ∈ T)) ((c (σ k)).Adj)
      simp only [mem_filter,mem_univ,true_and] at h
      rw [hsel S,hsel T] at h
      exact h
    rw [hcount S,hcount T,hpair]
    push_cast
    exact hdense k S T hJ

theorem permuted_host_stability : PermutedHostStability := by
  classical
  refine ⟨1,1,by norm_num,by norm_num,?_⟩
  intro α hα hαone μ₁ hμ₁ _
  let μ : ℝ := min (μ₁ / 2) (α / 200000)
  have hμ : 0 < μ := lt_min (by positivity) (by positivity)
  have hμlt : μ < μ₁ := by
    have h : μ ≤ μ₁ / 2 := min_le_left _ _
    linarith
  have hμsmall : μ ≤ α / 100000 := by
    have h : μ ≤ α / 200000 := min_le_right _ _
    linarith
  refine ⟨μ,hμ,hμlt,?_⟩
  intro δ hδ
  obtain ⟨θ,d,p⟩ := exists_transfer_parameters α μ δ hα hαone hμ hμsmall hδ
  obtain ⟨M₀,hM₀⟩ := eventual_reduced_host_dichotomy α μ δ θ d p
  filter_upwards [eventually_ge_atTop (2 * M₀)] with n hn
  intro heven
  obtain ⟨M,rfl⟩ := heven
  rw [show M + M = 2 * M by omega,show 2 * (2 * M) = 4 * M by omega]
  intro c hc
  letI : ∀ k, DecidableRel (c k).Adj := fun _ => Classical.decRel _
  have half_double (x : ℝ) : x * (2 * (M : ℝ)) / 2 = x * M := by ring
  rcases hM₀ M (by omega) c hc with hcycle | hdata
  · exact Or.inl hcycle
  · right
    obtain ⟨D⟩ := hdata
    rcases D.to_host_extremal p hc with h1 | h2 | h3
    · obtain ⟨σ,U,hU,hs,hd⟩ := h1
      obtain ⟨f,hf,hden⟩ := labeled_density_of_block_partition (4 * M) c σ U hU α EC1Joins hd
      refine ⟨σ,f,Or.inl ⟨?_,hden⟩⟩
      intro j
      simpa only [Nat.cast_mul,Nat.cast_ofNat,half_double,hf] using hs j
    · obtain ⟨σ,U,hU,hs,hd⟩ := h2
      obtain ⟨f,hf,hden⟩ := labeled_density_of_block_partition (4 * M) c σ U hU α EC2Joins hd
      refine ⟨σ,f,Or.inr (Or.inl ⟨?_,hden⟩)⟩
      intro j
      simpa only [Nat.cast_mul,Nat.cast_ofNat,half_double,hf] using hs j
    · obtain ⟨σ,U,hU,hs,hd⟩ := h3
      obtain ⟨f,hf,hden⟩ := labeled_density_of_block_partition (4 * M) c σ U hU δ EC1Joins hd
      refine ⟨σ,f,Or.inr (Or.inr ⟨?_,hden⟩)⟩
      simpa only [EC3BlockSizes,Nat.cast_mul,Nat.cast_ofNat,half_double,hf] using hs


end MatchingStability

end PermutedModule67

theorem OMA.solution :
    OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R3.H4 := by
  change MatchingStability.PermutedHostStability
  exact MatchingStability.permuted_host_stability
