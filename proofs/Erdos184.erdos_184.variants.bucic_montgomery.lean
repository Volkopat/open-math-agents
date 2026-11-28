import FormalConjectures.ErdosProblems.«184»
import Mathlib

/-!
# Erdős Problem 184, Bucić–Montgomery variant: O(n log* n) cycles and edges

Every graph on n vertices decomposes into at most C * n edge-disjoint cycles
and edges (the Erdős–Gallai conjecture), hence into O(n log* n) of them.

## Attribution and licence

The proof of the linear bound is a machine-shortened copy of OpenAI's Lean
development OAI.Combinatorics.CycleDecomposition (34 modules, main theorem
OAI.ErdosGallai.erdos_gallai), taken from
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CycleDecomposition
Copyright OpenAI. Licensed under the Apache License, Version 2.0; you may not
use this file except in compliance with the License. You may obtain a copy of
the License at http://www.apache.org/licenses/LICENSE-2.0 . Unless required by
applicable law or agreed to in writing, software distributed under the License
is distributed on an AS IS BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. SPDX-License-Identifier: Apache-2.0

Changes made to the OpenAI code (the mathematics is unchanged; the edits make it
compile with the Lean and Mathlib pinned here, obey the checker's rules and fit
its 512 KiB file limit):
* the modules are concatenated in import order; imports and comments removed;
* for the older Mathlib: ite_eq_left/right and dite_eq_left/right become
  if_pos/if_neg/dif_pos/dif_neg, Finset.prod_le_prod₀ and Finset.one_le_prod₀
  become Finset.prod_le_prod and Finset.one_le_prod, map_le_iff_le_comap gets
  explicit arguments, and one congr/ext step is rewritten;
* attribute lines are replaced by local instance / instance declarations;
* BatchLovasz, BatchPathDeletion, BatchEndpoints and most of BatchRouting repeat
  Lovasz, PathDeletion, EndpointPartition and Routing in another namespace; they
  and other verbatim repeated declarations are dropped in favour of the first
  copy, as are declarations the main theorem does not use;
* by script: local identifiers are renamed to short names (so names below do
  not match upstream), frequently used Mathlib lemmas get short aliases (the
  lines of the form lemma xx:type_of% @Name:=@Name), some namespace prefixes
  are dropped, lines are joined and whitespace removed, fun is written λ and
  some operators in ASCII.

The Mathlib fixes and the instance replacements follow the adaptation in the
merged proof of Erdos184.erdos_184.variants.conlon_fox_sudakov in this
repository (by amp2600); its two lemmas transporting a decomposition to
G.Subgraph (supportedPiece, transportPartition there) are reused at the end.

New here: two lemmas giving 1 ≤ Real.iteratedLog x for 1 < x, and OMA.solution
(f n = C * n, which is at most C * (n * log* n) for n ≥ 2).
-/

noncomputable section
lemma bK:type_of% @mul_comm:=@mul_comm
lemma pG:type_of% @Finset.not_nonempty_iff_eq_empty:=@Finset.not_nonempty_iff_eq_empty
lemma nZ:type_of% @pow_le_pow_left₀:=@pow_le_pow_left₀
lemma aJ:type_of% @mul_le_mul_of_nonneg_left:=@mul_le_mul_of_nonneg_left
lemma bZ:type_of% @mul_nonneg:=@mul_nonneg
lemma aN:type_of% @Nat.cast_nonneg:=@Nat.cast_nonneg
lemma gV:type_of% @measurable_of_finite:=@measurable_of_finite
lemma fo:type_of% @Set.mem_ofPred_eq:=@Set.mem_ofPred_eq
lemma aL:type_of% @Finset.disjoint_left:=@Finset.disjoint_left
lemma aD:type_of% @Finset.mem_filter:=@Finset.mem_filter
lemma aQ:type_of% @Finset.mem_univ:=@Finset.mem_univ
lemma b5:type_of% @true_and:=@true_and
lemma dB:type_of% @Set.mem_singleton_iff:=@Set.mem_singleton_iff
lemma j5:type_of% @Finset.card_biUnion:=@Finset.card_biUnion
lemma cZ:type_of% @Finset.sum_congr:=@Finset.sum_congr
lemma dD:type_of% @Finset.mem_inter:=@Finset.mem_inter
lemma f7:type_of% @mul_pos:=@mul_pos
lemma aK:type_of% @Finset.sum_le_sum:=@Finset.sum_le_sum
lemma b8:type_of% @Set.mem_union:=@Set.mem_union
lemma iF:type_of% @Finset.inter_subset_left:=@Finset.inter_subset_left
lemma dF:type_of% @le_of_not_gt:=@le_of_not_gt
lemma av:type_of% @Set.mem_iUnion:=@Set.mem_iUnion
lemma aZ:type_of% @Subtype.ext:=@Subtype.ext
lemma j6:type_of% @Finset.mem_range:=@Finset.mem_range
lemma eV:type_of% @Nat.cast_sum:=@Nat.cast_sum
lemma f8:type_of% @Finset.sum_add_distrib:=@Finset.sum_add_distrib
lemma eW:type_of% @Finset.filter_subset:=@Finset.filter_subset
lemma d5:type_of% @Finset.sum_const:=@Finset.sum_const
lemma j7:type_of% @nsmul_eq_mul:=@nsmul_eq_mul
lemma k8:type_of% @Nat.cast_mul:=@Nat.cast_mul
lemma j8:type_of% @Nat.cast_ofNat:=@Nat.cast_ofNat
lemma iG:type_of% @lt_of_not_ge:=@lt_of_not_ge
lemma dR:type_of% @Finset.mul_sum:=@Finset.mul_sum
lemma jr:type_of% @Finset.sum_le_sum_of_subset_of_nonneg:=@Finset.sum_le_sum_of_subset_of_nonneg
lemma iH:type_of% @sq_nonneg:=@sq_nonneg
lemma aY:type_of% @mul_le_mul_of_nonneg_right:=@mul_le_mul_of_nonneg_right
lemma aU:type_of% @Finset.card_le_card:=@Finset.card_le_card
lemma gQ:type_of% @Finset.mem_union:=@Finset.mem_union
lemma aS:type_of% @Finset.mem_sdiff:=@Finset.mem_sdiff
lemma j9:type_of% @Finset.card_union_of_disjoint:=@Finset.card_union_of_disjoint
lemma kc:type_of% @Sym2.mk_eq_mk_iff:=@Sym2.mk_eq_mk_iff
lemma aF:type_of% @congrArg:=@congrArg
lemma bk:type_of% @Finset.mem_image:=@Finset.mem_image
lemma ee:type_of% @Finset.mem_union_right:=@Finset.mem_union_right
lemma jt:type_of% @Finset.mem_product:=@Finset.mem_product
lemma k9:type_of% @Finset.mem_symmDiff:=@Finset.mem_symmDiff
lemma bx:type_of% @Sym2.eq_swap:=@Sym2.eq_swap
lemma cQ:type_of% @Finset.mem_union_left:=@Finset.mem_union_left
lemma nL:type_of% @Finset.card_image_of_injOn:=@Finset.card_image_of_injOn
lemma dG:type_of% @Finset.card_union_le:=@Finset.card_union_le
lemma ju:type_of% @Finset.card_image_le:=@Finset.card_image_le
lemma lg:type_of% @Finset.sdiff_subset:=@Finset.sdiff_subset
lemma e3:type_of% @le_div_iff₀:=@le_div_iff₀
lemma bR:type_of% @Finset.mem_biUnion:=@Finset.mem_biUnion
lemma c5:type_of% @Finset.card_biUnion_le:=@Finset.card_biUnion_le
lemma fF:type_of% @div_nonneg:=@div_nonneg
lemma kd:type_of% @div_le_one:=@div_le_one
lemma e4:type_of% @Finset.card_le_univ:=@Finset.card_le_univ
lemma cT:type_of% @Finset.card_pos:=@Finset.card_pos
lemma dS:type_of% @add_le_add:=@add_le_add
lemma cU:type_of% @Finset.mem_compl:=@Finset.mem_compl
lemma ke:type_of% @Finset.inter_subset_right:=@Finset.inter_subset_right
lemma f9:type_of% @min_eq_left:=@min_eq_left
lemma nO:type_of% @Finset.card_compl:=@Finset.card_compl
lemma iI:type_of% @Finset.card_singleton:=@Finset.card_singleton
lemma gR:type_of% @Nat.cast_one:=@Nat.cast_one
lemma gd:type_of% @Finset.mem_singleton:=@Finset.mem_singleton
lemma e5:type_of% @div_le_div_of_nonneg_right:=@div_le_div_of_nonneg_right
lemma gS:type_of% @Finset.subset_univ:=@Finset.subset_univ
lemma lu:type_of% @Finset.mem_powersetCard:=@Finset.mem_powersetCard
lemma nP:type_of% @Finset.card_powersetCard:=@Finset.card_powersetCard
lemma c7:type_of% @Finset.card_univ:=@Finset.card_univ
lemma nQ:type_of% @SimpleGraph.mem_interedges_iff:=@SimpleGraph.mem_interedges_iff
lemma nS:type_of% @div_le_div_iff₀:=@div_le_div_iff₀
lemma dH:type_of% @le_rfl:=@le_rfl
lemma d6:type_of% @Real.rpow_pos_of_pos:=@Real.rpow_pos_of_pos
lemma c8:type_of% @Real.rpow_add:=@Real.rpow_add
lemma nT:type_of% @tendsto_rpow_atTop:=@tendsto_rpow_atTop
lemma lz:type_of% @Real.rpow_mul:=@Real.rpow_mul
lemma o8:type_of% @isLittleO_log_rpow_atTop:=@isLittleO_log_rpow_atTop
lemma kg:type_of% @Real.norm_eq_abs:=@Real.norm_eq_abs
lemma gk:type_of% @abs_of_nonneg:=@abs_of_nonneg
lemma nU:type_of% @Real.log_nonneg:=@Real.log_nonneg
lemma fG:type_of% @Real.rpow_nonneg:=@Real.rpow_nonneg
lemma gT:type_of% @Real.rpow_sub:=@Real.rpow_sub
lemma nV:type_of% @Nat.ceil_lt_add_one:=@Nat.ceil_lt_add_one
lemma jv:type_of% @Real.one_le_rpow:=@Real.one_le_rpow
lemma iJ:type_of% @mul_le_mul:=@mul_le_mul
lemma lA:type_of% @Real.rpow_mul_natCast:=@Real.rpow_mul_natCast
lemma gq:type_of% @div_eq_mul_inv:=@div_eq_mul_inv
lemma lB:type_of% @ENNReal.ofReal_add:=@ENNReal.ofReal_add
lemma iK:type_of% @Finset.mem_erase:=@Finset.mem_erase
lemma dU:type_of% @Fintype.card_fin:=@Fintype.card_fin
lemma aI:type_of% @Set.disjoint_left:=@Set.disjoint_left
lemma bJ:type_of% @Sym2.ind:=@Sym2.ind
lemma o9:type_of% @Finset.induction_on:=@Finset.induction_on
lemma nW:type_of% @Finset.card_insert_of_notMem:=@Finset.card_insert_of_notMem
lemma bU:type_of% @Finset.mem_insert:=@Finset.mem_insert
lemma po:type_of% @Finset.filter_insert:=@Finset.filter_insert
lemma ej:type_of% @if_pos:=@if_pos
lemma oE:type_of% @Finset.card_product:=@Finset.card_product
lemma dY:type_of% @le_trans:=@le_trans
lemma b6:type_of% @le_max_left:=@le_max_left
lemma bC:type_of% @le_max_right:=@le_max_right
lemma dK:type_of% @div_le_iff₀:=@div_le_iff₀
lemma l5:type_of% @Nat.add_le_add_right:=@Nat.add_le_add_right
lemma l6:type_of% @Finset.card_sdiff_of_subset:=@Finset.card_sdiff_of_subset
lemma kO:type_of% @Real.log_pos:=@Real.log_pos
lemma cV:type_of% @Finset.card_eq_sum_ones:=@Finset.card_eq_sum_ones
lemma ck:type_of% @Finset.sum_filter:=@Finset.sum_filter
lemma gD:type_of% @Finset.sum_comm:=@Finset.sum_comm
lemma bw:type_of% @List.mem_toFinset:=@List.mem_toFinset
lemma l7:type_of% @Finset.eq_empty_iff_forall_notMem:=@Finset.eq_empty_iff_forall_notMem
lemma oF:type_of% @SimpleGraph.Walk.edges_append:=@SimpleGraph.Walk.edges_append
lemma gG:type_of% @Finset.card_le_card_of_injOn:=@Finset.card_le_card_of_injOn
lemma cq:type_of% @Nat.cast_le:=@Nat.cast_le
lemma oG:type_of% @List.toFinset_card_le:=@List.toFinset_card_le
lemma i8:type_of% @Sym2.inductionOn:=@Sym2.inductionOn
lemma g3:type_of% @Nat.cast_zero:=@Nat.cast_zero
lemma fq:type_of% @add_zero:=@add_zero
lemma gH:type_of% @eq_comm:=@eq_comm
lemma dL:type_of% @Real.logb_le_logb_of_le:=@Real.logb_le_logb_of_le
lemma g4:type_of% @Real.logb_pos:=@Real.logb_pos
lemma jH:type_of% @Real.logb_rpow_eq_mul_logb_of_pos:=@Real.logb_rpow_eq_mul_logb_of_pos
lemma g5:type_of% @Real.rpow_le_rpow_of_exponent_le:=@Real.rpow_le_rpow_of_exponent_le
lemma dZ:type_of% @lt_of_lt_of_le:=@lt_of_lt_of_le
lemma gI:type_of% @Finset.card_image_of_injective:=@Finset.card_image_of_injective
lemma dM:type_of% @Subtype.val_injective:=@Subtype.val_injective
lemma eG:type_of% @Fintype.card_coe:=@Fintype.card_coe
lemma l8:type_of% @SimpleGraph.Walk.length_map:=@SimpleGraph.Walk.length_map
lemma oH:type_of% @SimpleGraph.Walk.support_map:=@SimpleGraph.Walk.support_map
lemma bV:type_of% @List.mem_map:=@List.mem_map
lemma g6:type_of% @SimpleGraph.Walk.edgeSet_map:=@SimpleGraph.Walk.edgeSet_map
lemma l9:type_of% @Set.disjoint_image_iff:=@Set.disjoint_image_iff
lemma fI:type_of% @Sym2.map.injective:=@Sym2.map.injective
lemma mg:type_of% @Fintype.card_subtype:=@Fintype.card_subtype
lemma jI:type_of% @Sym2.eq_iff:=@Sym2.eq_iff
lemma ct:type_of% @List.disjoint_left:=@List.disjoint_left
lemma g7:type_of% @List.mem_of_mem_tail:=@List.mem_of_mem_tail
lemma i9:type_of% @List.nodup_cons:=@List.nodup_cons
lemma eI:type_of% @Set.mem_insert_iff:=@Set.mem_insert_iff
lemma mj:type_of% @Set.iUnion_union_distrib:=@Set.iUnion_union_distrib
lemma cD:type_of% @SimpleGraph.edgeSet_mono:=@SimpleGraph.edgeSet_mono
lemma kP:type_of% @Set.disjoint_iUnion_left:=@Set.disjoint_iUnion_left
lemma oI:type_of% @Set.disjoint_iUnion_right:=@Set.disjoint_iUnion_right
lemma rT:type_of% @SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil:=@SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
lemma g8:type_of% @SimpleGraph.edgeSet_deleteEdges:=@SimpleGraph.edgeSet_deleteEdges
lemma mo:type_of% @Set.sdiff_union_of_subset:=@Set.sdiff_union_of_subset
lemma jc:type_of% @Set.mem_toFinset:=@Set.mem_toFinset
lemma kQ:type_of% @Finset.mem_coe:=@Finset.mem_coe
lemma kR:type_of% @Set.mem_sdiff:=@Set.mem_sdiff
lemma jd:type_of% @Set.sdiff_subset:=@Set.sdiff_subset
lemma mw:type_of% @Set.disjoint_union_left:=@Set.disjoint_union_left
lemma mz:type_of% @Set.disjoint_union_right:=@Set.disjoint_union_right
lemma jJ:type_of% @smul_eq_mul:=@smul_eq_mul
lemma fy:type_of% @Fintype.card_sigma:=@Fintype.card_sigma
lemma gJ:type_of% @Set.iUnion_subset:=@Set.iUnion_subset
lemma mB:type_of% @Set.subset_union_left:=@Set.subset_union_left
lemma je:type_of% @Set.subset_iUnion:=@Set.subset_iUnion
lemma mC:type_of% @List.tail_cons:=@List.tail_cons
lemma kS:type_of% @List.append_assoc:=@List.append_assoc
lemma dd:type_of% @List.mem_cons:=@List.mem_cons
lemma mD:type_of% @Set.mem_empty_iff_false:=@Set.mem_empty_iff_false
lemma cu:type_of% @SimpleGraph.mem_edgeFinset:=@SimpleGraph.mem_edgeFinset
lemma eJ:type_of% @List.toFinset_card_of_nodup:=@List.toFinset_card_of_nodup
lemma jf:type_of% @Nat.not_even_iff_odd:=@Nat.not_even_iff_odd
lemma mJ:type_of% @SimpleGraph.deleteEdges_adj:=@SimpleGraph.deleteEdges_adj
lemma jg:type_of% @Finset.card_erase_add_one:=@Finset.card_erase_add_one
lemma oJ:type_of% @Finset.card_lt_card:=@Finset.card_lt_card
lemma oK:type_of% @Finset.ssubset_iff_subset_ne:=@Finset.ssubset_iff_subset_ne
lemma mK:type_of% @Set.disjoint_singleton:=@Set.disjoint_singleton
lemma mL:type_of% @Fintype.sum_option:=@Fintype.sum_option
lemma oL:type_of% @Finset.card_erase_of_mem:=@Finset.card_erase_of_mem
lemma oM:type_of% @Option.some_ne_none:=@Option.some_ne_none
lemma mO:type_of% @Option.some_injective:=@Option.some_injective
lemma jh:type_of% @Nat.strong_induction_on:=@Nat.strong_induction_on
lemma mW:type_of% @Set.Subset.antisymm:=@Set.Subset.antisymm
lemma rU:type_of% @SimpleGraph.Walk.mem_support_iff_exists_mem_edges:=@SimpleGraph.Walk.mem_support_iff_exists_mem_edges
lemma fJ:type_of% @List.nodup_append:=@List.nodup_append
lemma oN:type_of% @SimpleGraph.Walk.edgeSet_append:=@SimpleGraph.Walk.edgeSet_append
lemma oO:type_of% @SimpleGraph.Walk.length_dropLast:=@SimpleGraph.Walk.length_dropLast
lemma oP:type_of% @SimpleGraph.Walk.length_tail:=@SimpleGraph.Walk.length_tail
lemma jK:type_of% @Finset.card_le_one:=@Finset.card_le_one
lemma jL:type_of% @Set.image_mono:=@Set.image_mono
lemma m4:type_of% @Finset.disjoint_coe:=@Finset.disjoint_coe
lemma m5:type_of% @Set.singleton_subset_iff:=@Set.singleton_subset_iff
lemma fO:type_of% @Fintype.card_sum:=@Fintype.card_sum
lemma oQ:type_of% @Function.injective_id:=@Function.injective_id
lemma fP:type_of% @Nat.cast_add:=@Nat.cast_add
lemma g9:type_of% @Fintype.card_congr:=@Fintype.card_congr
lemma m6:type_of% @Equiv.swap_apply_of_ne_of_ne:=@Equiv.swap_apply_of_ne_of_ne
lemma h9:type_of% @one_div_le_one_div_of_le:=@one_div_le_one_div_of_le
lemma oR:type_of% @SimpleGraph.card_neighborFinset_eq_degree:=@SimpleGraph.card_neighborFinset_eq_degree
lemma oT:type_of% @SimpleGraph.mem_neighborFinset:=@SimpleGraph.mem_neighborFinset
lemma oU:type_of% @Nat.cast_choose_two:=@Nat.cast_choose_two
lemma jm:type_of% @Finset.erase_subset:=@Finset.erase_subset
lemma ic:type_of% @SimpleGraph.mem_edgeSet:=@SimpleGraph.mem_edgeSet
lemma iu:type_of% @List.pairwise_cons:=@List.pairwise_cons
lemma kT:type_of% @List.length_cons:=@List.length_cons
lemma m7:type_of% @List.pairwise_map:=@List.pairwise_map
lemma oV:type_of% @List.pairwise_iff_getElem:=@List.pairwise_iff_getElem
lemma fQ:type_of% @List.mem_append:=@List.mem_append
lemma jM:type_of% @List.mem_singleton:=@List.mem_singleton
lemma m8:type_of% @Real.sqrt_le_sqrt:=@Real.sqrt_le_sqrt
lemma oW:type_of% @SimpleGraph.edgeSet_subset_edgeSet:=@SimpleGraph.edgeSet_subset_edgeSet
lemma oX:type_of% @Finset.coe_sort_coe:=@Finset.coe_sort_coe
lemma m9:type_of% @Finset.disjoint_insert_left:=@Finset.disjoint_insert_left
lemma ng:type_of% @List.length_append:=@List.length_append
lemma oY:type_of% @List.mem_append_right:=@List.mem_append_right
lemma ni:type_of% @Finset.card_sdiff_add_card_eq_card:=@Finset.card_sdiff_add_card_eq_card
lemma gK:type_of% @List.map_append:=@List.map_append
lemma nj:type_of% @List.sum_append:=@List.sum_append
lemma kU:type_of% @List.sum_le_sum:=@List.sum_le_sum
lemma nq:type_of% @SimpleGraph.disjoint_left:=@SimpleGraph.disjoint_left
lemma nv:type_of% @SimpleGraph.sup_adj:=@SimpleGraph.sup_adj
lemma jN:type_of% @List.flatMap_cons:=@List.flatMap_cons
lemma fB:type_of% @List.map_cons:=@List.map_cons
lemma nw:type_of% @Finset.sum_range_succ:=@Finset.sum_range_succ
lemma iw:type_of% @List.sum_cons:=@List.sum_cons
lemma jn:type_of% @List.map_map:=@List.map_map
lemma kV:type_of% @List.mem_flatMap:=@List.mem_flatMap
lemma jo:type_of% @Nat.add_zero:=@Nat.add_zero
lemma nB:type_of% @List.mem_iff_get:=@List.mem_iff_get
lemma nC:type_of% @Finset.mem_insert_of_mem:=@Finset.mem_insert_of_mem
lemma oZ:type_of% @Finset.card_inter_add_card_sdiff:=@Finset.card_inter_add_card_sdiff
lemma nD:type_of% @Set.mem_iUnion₂:=@Set.mem_iUnion₂
lemma d3:type_of% @Nat.zero_add:=@Nat.zero_add
lemma nE:type_of% @List.flatMap_singleton':=@List.flatMap_singleton'
lemma iy:type_of% @List.flatMap_singleton:=@List.flatMap_singleton
lemma o0:type_of% @List.map_eq_flatMap:=@List.map_eq_flatMap
lemma o3:type_of% @List.sum_map_mul_left:=@List.sum_map_mul_left
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX gu
section
namespace af.aV
open MeasureTheory ProbabilityTheory Finset Real
section qe
variable {Ω:Type bX} {I:Type bY} [MeasurableSpace Ω] {μ:Measure Ω} [IsProbabilityMeasure μ]
lemma uA {Ω:Type cy} [aP:MeasurableSpace Ω] {X:Ω->ℝ} (hX:∀ω,X ω=0\/X ω=1) (ω:Ω):X ω∈Set.Icc (0:ℝ) 1:=by rcases hX ω with h | h<;>simp [h]
lemma DL {X:Ω->ℝ} (hm:Measurable X)
  (hX:∀ω,X ω=0\/X ω=1) (p t:ℝ) (hp:∫ ω,X ω ∂μ=p):mgf X μ t=1+p*(exp t-1):=by
 have W4:Integrable X μ:=Integrable.of_mem_Icc 0 1 hm.aemeasurable
  (ae_of_all _ (uA hX))
 have heq:(λ ω=>exp (t*X ω))=λ ω=>(1:ℝ)+(exp t-1)*X ω:=by funext ω;rcases hX ω with h | h<;>simp [h]
 rw [mgf,heq,integral_add (integrable_const _) (W4.const_mul _),integral_const_mul,hp,integral_const];simp [bK]
lemma uh {X:I->Ω->ℝ} (s:Finset I)
  (hm:∀i,Measurable (X i)) (hi:iIndepFun X μ)
  (hX:∀i ω,X i ω=0\/X i ω=1)
  (p t:ℝ) (hp:∀i,∫ ω,X i ω ∂μ=p):mgf (∑i∈s,X i) μ t<=exp ((s.card:ℝ)*p*(exp t-1)):=by
 by_cases hs:s.Nonempty;swap
 ·have he:=pG.mp hs;simp [he]
 rw [hi.mgf_sum hm];have heq:(∏i∈s,mgf (X i) μ t)=(1+p*(exp t-1))^s.card:=by simp_rw [DL (hm _) (hX _) p t (hp _)];simp
 rw [heq];have hn:0<=1+p*(exp t-1):=by obtain ⟨i,_⟩:=hs;rw [<-DL (hm i) (hX i) p t (hp i)];exact mgf_nonneg
 calc
  (1+p*(exp t-1))^s.card<=exp (p*(exp t-1))^s.card:=nZ hn (by linarith [add_one_le_exp (p*(exp t-1))]) _
  _=_:=by rw [<-exp_nat_mul];congr 1;ring
lemma EJ:exp (-(1/2:ℝ))<=5/8:=by
 have he:exp (1/2:ℝ)*exp (1/2:ℝ)=exp 1:=by rw [<-exp_add];norm_num
 have EK:(8/5:ℝ)<=exp (1/2:ℝ):=by nlinarith [exp_one_gt_d9,exp_pos (1/2:ℝ)]
 rw [exp_neg];exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *;exact EK)
lemma JL:exp (1/2:ℝ)<=5/3:=by
 have he:exp (1/2:ℝ)*exp (1/2:ℝ)=exp 1:=by rw [<-exp_add];norm_num
 nlinarith [exp_one_lt_d9,exp_pos (1/2:ℝ)]
lemma pH {X:I->Ω->ℝ} (s:Finset I)
  (hm:∀i,Measurable (X i)) (hi:iIndepFun X μ)
  (hX:∀i ω,X i ω=0\/X i ω=1)
  (p:ℝ) (Rv:0<=p) (hp:∀i,∫ ω,X i ω ∂μ=p):μ.real {ω | (∑i∈s,X i ω)<=p*s.card/2}<=exp (-p*s.card/8):=by
 have O7:Integrable (λ ω=>exp (-(1/2:ℝ)*(∑i∈s,X i) ω)) μ:=hi.integrable_exp_mul_sum hm (λ i _=>integrable_exp_mul_of_mem_Icc
   (hm i).aemeasurable (ae_of_all _ (uA (hX i))))
 have hb:=measure_le_le_exp_mul_mgf (X:=∑i∈s,X i) (p*s.card/2)
  (by norm_num: -(1/2:ℝ)<=0) O7
 simp only [Finset.sum_apply] at hb;apply hb.trans;calc
  _<=exp (-(-(1/2:ℝ))*(p*s.card/2))*exp ((s.card:ℝ)*p*(exp (-(1/2:ℝ))-1)):=by exact aJ (uh s hm hi hX p _ hp) (exp_pos _).le
  _=exp (p*s.card/4+(s.card:ℝ)*p*(exp (-(1/2:ℝ))-1)):=by rw [<-exp_add];congr 1;ring
  _<=_:=by
   apply exp_le_exp.mpr;nlinarith [aJ EJ
    (bZ (aN s.card) Rv)]
lemma zG {X:I->Ω->ℝ} (s:Finset I)
  (hm:∀i,Measurable (X i)) (hi:iIndepFun X μ)
  (hX:∀i ω,X i ω=0\/X i ω=1)
  (p:ℝ) (Rv:0<=p) (hp:∀i,∫ ω,X i ω ∂μ=p):μ.real {ω | 2*p*s.card<=∑i∈s,X i ω}<=exp (-p*s.card/3):=by
 have O7:Integrable (λ ω=>exp ((1/2:ℝ)*(∑i∈s,X i) ω)) μ:=hi.integrable_exp_mul_sum hm (λ i _=>integrable_exp_mul_of_mem_Icc
   (hm i).aemeasurable (ae_of_all _ (uA (hX i))))
 have hb:=measure_ge_le_exp_mul_mgf (X:=∑i∈s,X i) (2*p*s.card)
  (by norm_num:(0:ℝ)<=1/2) O7
 simp only [Finset.sum_apply] at hb;apply hb.trans;calc
  _<=exp (-(1/2:ℝ)*(2*p*s.card))*exp ((s.card:ℝ)*p*(exp (1/2:ℝ)-1)):=by exact aJ (uh s hm hi hX p _ hp) (exp_pos _).le
  _=exp (-p*s.card+(s.card:ℝ)*p*(exp (1/2:ℝ)-1)):=by rw [<-exp_add];congr 1;ring
  _<=_:=by
   apply exp_le_exp.mpr;nlinarith [aJ JL
    (bZ (aN s.card) Rv)]
end qe
section JM
variable {V:Type cz} [Fintype V] [DecidableEq V]
noncomputable def dn (V:Type cP) [Fintype V] (p:unitInterval):Measure (V->Bool):=Measure.pi (λ _:V=>bernoulliMeasure true false p)
instance K5 (p:unitInterval):IsProbabilityMeasure (dn V p):=by unfold dn;infer_instance
def aW (ω:V->Bool):Finset V:=univ.filter (λ v=>ω v=true)
def jS (v:V) (ω:V->Bool):ℝ:=if ω v then 1 else 0
lemma rV {V:Type cL} [aP:Fintype V] [aO:DecidableEq V] (v:V):Measurable (jS v):=gV _
lemma uI {V:Type c9} [aP:Fintype V] [aO:DecidableEq V] (v:V) (ω:V->Bool):jS v ω=0\/jS v ω=1:=by simp only [jS];split<;>simp
lemma vl {V:Type dW} [aP:Fintype V] [aO:DecidableEq V] (p:unitInterval):iIndepFun (jS (V:=V)) (dn V p):=by
 exact iIndepFun_pi (X:=λ _:V=>λ b:Bool=>if b then (1:ℝ) else 0)
  (λ _=>(gV _).aemeasurable)
lemma pI {V:Type eo} [aP:Fintype V] [aO:DecidableEq V] (p:unitInterval) (v:V):∫ ω,jS v ω ∂dn V p=(p:ℝ):=by
 have hl:=(measurePreserving_eval (λ _:V=>bernoulliMeasure true false p) v).hasLaw;have hi:=hl.integral_comp (f:=λ b:Bool=>if b then (1:ℝ) else 0)
  (gV _).aestronglyMeasurable
 simpa [dn,jS,integral_bernoulliMeasure] using hi
lemma wT (S:Finset V) (ω:V->Bool):(∑v∈S,jS v ω)=((S∩aW ω).card:ℝ):=by simp only [jS,sum_boole];congr 2;ext v;simp [aW]
lemma Bj (p:unitInterval) (S:Finset V):(dn V p).real {ω | ((S∩aW ω).card:ℝ)<=(p:ℝ)*S.card/2}<=exp (-(p:ℝ)*S.card/8):=by
 simpa only [wT] using pH S
  rV (vl p) uI
  (p:ℝ) p.property.1 (pI p)
lemma Bk (p:unitInterval) (S:Finset V):(dn V p).real {ω | 2*(p:ℝ)*S.card<=((S∩aW ω).card:ℝ)}<=exp (-(p:ℝ)*S.card/3):=by
 simpa only [wT] using zG S
  rV (vl p) uI
  (p:ℝ) p.property.1 (pI p)
lemma At (p:unitInterval) (S:Finset V):(dn V p).real {ω | Disjoint S (aW ω)}=(1-(p:ℝ))^S.card:=by
 have heq:{ω | Disjoint S (aW ω)}=Set.univ.pi (λ v:V=>if v∈S then {false} else Set.univ):=by
  ext ω;simp only [fo,Set.mem_pi,Set.mem_univ,forall_true_left];simp only [aL,aW,aD,aQ,b5];constructor
  ·intro h v
   by_cases hv:v∈S
   ·simp only [hv,↓reduceIte,dB];cases hi:ω v<;>simp_all
   ·simp [hv]
  ·intro h v hv ht;have:=h v;simp_all
 rw [heq,Measure.real,dn,Measure.pi_pi,ENNReal.toReal_prod];have Li (v:V):((bernoulliMeasure true false p) (if v∈S then {false} else Set.univ)).toReal=if v∈S then 1-(p:ℝ) else 1:=by
  by_cases hv:v∈S
  ·simp only [hv,↓reduceIte];change (bernoulliMeasure true false p).real {false}=_;exact bernoulliMeasure_real_apply_of_notMem_of_mem p (by simp) (by simp) (by simp)
  ·simp [hv]
 simp_rw [Li];simp
lemma Ge (p:unitInterval) (S:Finset V):(dn V p).real {ω | Disjoint S (aW ω)}<=exp (-(p:ℝ)*S.card):=by
 rw [At];calc
  (1-(p:ℝ))^S.card<=exp (-(p:ℝ))^S.card:=by apply nZ (sub_nonneg.mpr p.property.2);linarith [add_one_le_exp (-(p:ℝ))]
  _=_:=by rw [<-exp_nat_mul];congr 1;ring
lemma ow (p:unitInterval) (S:Finset V):(dn V p) {ω | S⊆aW ω}=ENNReal.ofReal (p:ℝ)^S.card:=by
 have heq:{ω | S⊆aW ω}=Set.univ.pi (λ v:V=>if v∈S then {true} else Set.univ):=by
  ext ω;simp only [fo,Set.mem_pi,Set.mem_univ,forall_true_left];simp only [subset_iff,aW,aD,aQ,b5];constructor
  ·intro h v;by_cases hv:v∈S<;>simp_all
  ·intro h v hv;simpa [hv] using h v
 rw [heq,dn,Measure.pi_pi];have Li (v:V):bernoulliMeasure true false p (if v∈S then {true} else Set.univ)=if v∈S then ENNReal.ofReal (p:ℝ) else 1:=by
  by_cases hv:v∈S
  ·simp only [hv,↓reduceIte];rw [bernoulliMeasure_apply_of_mem_of_notMem p (by simp) (by simp) (by simp)];exact ENNReal.ofReal_coe_nnreal.symm
  ·simp [hv]
 simp_rw [Li];simp
lemma u9 (p:unitInterval) (S:Finset V):(dn V p).real {ω | S⊆aW ω}=(p:ℝ)^S.card:=by rw [Measure.real,ow,ENNReal.toReal_pow,ENNReal.toReal_ofReal p.property.1]
lemma yZ {I:Type d7} (p:unitInterval) (S:I->Finset V)
  (hS:Pairwise λ i j=>Disjoint (S i) (S j)):iIndepSet (λ i=>{ω | S i⊆aW ω}) (dn V p):=by
 classical
 rw [iIndepSet_iff_meas_biInter (λ _=>MeasurableSet.of_discrete)];intro t;have heq:(⋂ i∈t,{ω | S i⊆aW ω})={ω | t.biUnion S⊆aW ω}:=by ext ω;simp only [Set.mem_iInter,fo,biUnion_subset]
 rw [heq,ow,j5]
 ·simp_rw [ow];exact (prod_pow_eq_pow_sum t (λ i=>(S i).card) _).symm
 ·intro i _ j _ hij;exact hS hij
noncomputable def jO (S:Finset V):(V->Bool)->ℝ:={ω | S⊆aW ω}.indicator (λ _=>1)
lemma BT (S:Finset V) (ω:V->Bool):jO S ω=0\/jO S ω=1:=by
 classical
 by_cases h:S⊆aW ω<;>simp [jO,h]
lemma Au (p:unitInterval) (S:Finset V):∫ ω,jO S ω ∂dn V p=(p:ℝ)^S.card:=by rw [jO,integral_indicator_const _ MeasurableSet.of_discrete,u9];simp
lemma zH {I:Type d8} (p:unitInterval) (S:I->Finset V)
  (hS:Pairwise λ i j=>Disjoint (S i) (S j)) (d:ℕ)
  (hd:∀i,(S i).card=d) (t:Finset I):(dn V p).real {ω | (∑i∈t,jO (S i) ω)<=(p:ℝ)^d*t.card/2}<=exp (-(p:ℝ)^d*t.card/8):=by
 apply pH t (λ _=>gV _)
  (yZ p S hS).iIndepFun_indicator
  (λ i=>BT (S i)) ((p:ℝ)^d) (pow_nonneg p.property.1 _)
 intro i;change (∫ ω,jO (S i) ω ∂dn V p)=_;rw [Au,hd]
lemma Gf (A:Finset V) (w:V->ℝ) (ω:V->Bool):(∑v∈A∩aW ω,w v)=∑v∈A,w v*jS v ω:=by
 rw [<-Finset.sum_ite_mem];apply cZ rfl;intro v _;simp only [aW,aD,aQ,b5,jS]
 split<;>simp_all
lemma Bl (p:unitInterval) (A:Finset V) (w:V->ℝ):∫ ω,(∑v∈A∩aW ω,w v) ∂dn V p=(p:ℝ)*∑v∈A,w v:=by simp_rw [Gf];rw [integral_finsetSum A (λ _ _=>Integrable.of_finite)];simp_rw [integral_const_mul,pI];rw [<-sum_mul,bK]
lemma yj {Ω:Type d9} [MeasurableSpace Ω]
  {μ:Measure Ω} [IsProbabilityMeasure μ] {X:Ω->ℝ}
  (hi:Integrable X μ) (hn:∀ω,0<=X ω) {B:ℝ} (hB:0<B)
  (he:∫ ω,X ω ∂μ<=B):μ.real {ω | 4*B<X ω}<=1/4:=by
 have hb:=mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hn) hi (4*B);have hm:μ.real {ω | 4*B<X ω}<=μ.real {ω | 4*B<=X ω}:=measureReal_mono (λ ω (h:4*B<X ω)=>h.le);nlinarith [aJ hm (by positivity:0<=4*B)]
lemma vU (p:unitInterval) (hp:0<(p:ℝ))
  (A:Finset V) (w:V->ℝ) (hw:∀v∈A,0<=w v)
  {B:ℝ} (hB:0<B) (hs:∑v∈A,w v<=B):(dn V p).real {ω | 4*(p:ℝ)*B<∑v∈A∩aW ω,w v}<=1/4:=by
 have ht:=yj (μ:=dn V p)
  (X:=λ ω=>∑v∈A∩aW ω,w v) Integrable.of_finite
  (λ ω=>sum_nonneg (λ v hv=>hw v (dD.mp hv).1))
  (f7 hp hB) (by rw [Bl];exact aJ hs hp.le)
 simpa only [mul_assoc] using ht
lemma uJ {I:Type eO} (A:Finset V) (hA:A.Nonempty)
  (good:Finset I) (K:I->Finset V) (W5:∀i∈good,K i⊆A)
  (w:V->ℝ) (hw:∀v∈A,0<=w v) {B d:ℝ}
  (hB:0<B) (hs:∑v∈A,w v<=B)
  (hd:∀i∈good,d<=(K i).card)
  (q:unitInterval) (hq:0<(q:ℝ))
  (vV:(good.card:ℝ)*exp (-(q:ℝ)*d)<1/2):∃S:Finset V,S⊆A/\(S.card:ℝ)<=4*(q:ℝ)*A.card/\(∑v∈S,w v)<=4*(q:ℝ)*B/\∀i∈good,¬Disjoint (K i) S:=by
 classical
 let μ:=dn V q;let JN:Set (V->Bool):={ω | 4*(q:ℝ)*A.card<((A∩aW ω).card:ℝ)};let Lj:Set (V->Bool):={ω | 4*(q:ℝ)*B<∑v∈A∩aW ω,w v};let JO:Set (V->Bool):=⋃ i∈good,{ω | Disjoint (K i) (aW ω)};have h₁:μ.real JN<=1/4:=by
  have ht:=vU q hq A (λ _=>(1:ℝ)) (by simp)
   (show (0:ℝ)<A.card by exact_mod_cast hA.card_pos) (by simp)
  simpa [μ,JN] using ht
 have h₂:μ.real Lj<=1/4:=vU q hq A w hw hB hs;have h₃:μ.real JO<1/2:=by
  calc
   μ.real JO<=∑i∈good,μ.real {ω | Disjoint (K i) (aW ω)}:=measureReal_biUnion_finset_le good _
   _<=∑i∈good,exp (-(q:ℝ)*d):=by
    apply aK;intro i hi;exact (Ge q (K i)).trans (exp_le_exp.mpr
     (mul_le_mul_of_nonpos_left (hd i hi) (neg_nonpos.mpr hq.le)))
   _=(good.card:ℝ)*exp (-(q:ℝ)*d):=by simp
   _<_:=vV
 have hf:μ.real (JN∪Lj∪JO)<1:=by have ha:=measureReal_union_le (μ:=μ) (JN∪Lj) JO;have hb:=measureReal_union_le (μ:=μ) JN Lj;linarith
 have hne:JN∪Lj∪JO≠Set.univ:=by
  intro h;rw [h] at hf;have hu:μ.real Set.univ=1:=by simp [μ,Measure.real]
  linarith
 obtain ⟨ω,hω⟩:=(Set.ne_univ_iff_exists_notMem _).mp hne;have hn:=hω;simp only [b8,not_or] at hn;refine ⟨A∩aW ω,iF,dF hn.1.1,dF hn.1.2,?_⟩;intro i hi PL;apply hn.2;simp only [JO,av,fo];refine ⟨i,hi,?_⟩;apply aL.mpr;intro v hv W6;exact aL.mp PL hv (dD.mpr ⟨W5 i hi hv,W6⟩)
end JM
section MD
variable {Ω:Type fX} {I:Type gu} [MeasurableSpace Ω] {μ:Measure Ω} [IsProbabilityMeasure μ]
lemma wM (s:Finset I) (E:I->Set Ω)
  (h:∑i∈s,μ.real (E i)<1):∃ω,∀i∈s,ω∉E i:=by
 by_contra hn
 push Not at hn
 have cover:(⋃ i∈s,E i)=Set.univ:=by ext ω;simp only [av,Set.mem_univ,iff_true];obtain ⟨i,hi,he⟩:=hn ω;exact ⟨i,hi,he⟩
 have hu:=measureReal_biUnion_finset_le (μ:=μ) s E;rw [cover] at hu;have:μ.real Set.univ=1:=by simp [Measure.real]
 rw [this] at hu;linarith
end MD
end af.aV
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9
section
namespace af.aV
open Finset MeasureTheory ProbabilityTheory Real
open scoped symmDiff
variable {V:Type bX} [Fintype V] [DecidableEq V]
noncomputable def qE (e:V×V):ℕ:=(equivFin V e.1).val+(equivFin V e.2).val
lemma ME {V:Type bY} [aP:Fintype V] [aO:DecidableEq V] (e:V×V):qE e<2*card V:=by have h₁:=(equivFin V e.1).isLt;have h₂:=(equivFin V e.2).isLt;dsimp [qE];omega
lemma wN (A B:Finset V) (wU:Disjoint A B)
  {e f:V×V} (FZ:e.1∈A) (F3:e.2∈B)
  (Ty:f.1∈A) (Tz:f.2∈B) (hc:qE e=qE f) (xH:e≠f):Disjoint ({e.1,e.2}:Finset V) {f.1,f.2}:=by
 have h₁:e.1≠f.1:=by intro h;have ht:e.2=f.2:=(equivFin V).injective (Fin.ext (by dsimp [qE] at hc;rw [h] at hc;omega));exact xH (Prod.ext h ht)
 have h₂:e.2≠f.2:=by intro h;have ht:e.1=f.1:=(equivFin V).injective (Fin.ext (by dsimp [qE] at hc;rw [h] at hc;omega));exact xH (Prod.ext ht h)
 have h₃:e.1≠f.2:=λ h=>aL.mp wU FZ (h▸Tz)
 have VU:e.2≠f.1:=λ h=>aL.mp wU Ty (h▸F3)
 simp [aL,h₁,h₂,h₃,VU]
lemma Av (E:Finset (V×V)) (ω:V->Bool):(∑e∈E,jO ({e.1,e.2}:Finset V) ω)=((E.filter (λ e=>e.1∈aW ω/\e.2∈aW ω)).card:ℝ):=by
 classical
 simp only [jO,Set.indicator_apply,fo,insert_subset_iff,singleton_subset_iff];exact sum_boole _ _
lemma xI (p:unitInterval) (A B:Finset V) (wU:Disjoint A B)
  (E:Finset (V×V)) (hE:∀e∈E,e.1∈A/\e.2∈B)
  (c:ℕ) (hc:∀e∈E,qE e=c):
  (dn V p).real {ω |
   ((E.filter (λ e=>e.1∈aW ω/\e.2∈aW ω)).card:ℝ)<=(p:ℝ)^2*E.card/2}<=exp (-(p:ℝ)^2*E.card/8):=by
 classical
 let S:E->Finset V:=λ e=>{e.val.1,e.val.2}
 have hS:Pairwise λ e f:E=>Disjoint (S e) (S f):=by
  intro e f xH;exact wN A B wU (hE e e.property).1 (hE e e.property).2
   (hE f f.property).1 (hE f f.property).2 ((hc e e.property).trans (hc f f.property).symm)
   (λ h=>xH (aZ h))
 have hd:∀e:E,(S e).card=2:=by intro e;apply card_pair;intro h;exact aL.mp wU (hE e e.property).1 (h▸(hE e e.property).2)
 have ht:=zH p S hS 2 hd univ;have heq (ω:V->Bool):(∑e:E,jO (S e) ω)=(∑e∈E,jO ({e.1,e.2}:Finset V) ω):=by exact sum_attach E (λ e=>jO ({e.1,e.2}:Finset V) ω)
 simp_rw [heq,Av] at ht;simpa using ht
lemma uj (E:Finset (V×V)):(∑i∈range (2*card V),(E.filter (λ e=>qE e=i)).card)=E.card:=by rw [sum_card_fiberwise_eq_card_filter];congr 1;apply filter_true_of_mem;intro e _;exact j6.mpr (ME e)
lemma vc (p:unitInterval)
  (hr:0<Fintype.card V) (A B:Finset V) (wU:Disjoint A B)
  (E:Finset (V×V)) (hE:∀e∈E,e.1∈A/\e.2∈B):
  (dn V p).real {ω |
   ((E.filter (λ e=>e.1∈aW ω/\e.2∈aW ω)).card:ℝ)<(p:ℝ)^2*E.card/4}<=
   2*(Fintype.card V:ℝ)*exp (-(p:ℝ)^2*E.card/(32*Fintype.card V)):=by
 classical
 let r:ℝ:=Fintype.card V;have Rw:0< r:=by change 0<(Fintype.card V:ℝ);exact_mod_cast hr
 let qT:=Finset.range (2*Fintype.card V);let C (i:ℕ):=E.filter (λ e=>qE e=i);let m (i:ℕ):ℝ:=(C i).card;let L:=qT.filter (λ i=>(E.card:ℝ)/(4*r)<=m i);let gW (i:ℕ) (ω:V->Bool):ℝ:=((C i |>.filter (λ e=>e.1∈aW ω/\e.2∈aW ω)).card:ℝ);have hsum:∑i∈qT,m i=(E.card:ℝ):=by dsimp [qT,m,C];exact_mod_cast uj E
 have QH (ω:V->Bool):∑i∈qT,gW i ω=((E.filter (λ e=>e.1∈aW ω/\e.2∈aW ω)).card:ℝ):=by
  have ht:=uj
   (E.filter (λ e=>e.1∈aW ω/\e.2∈aW ω))
  simpa only [gW,C,qT,Finset.filter_filter,and_comm,eV] using
   (show (∑i∈Finset.range (2*Fintype.card V),(((E.filter (λ e=>e.1∈aW ω/\e.2∈aW ω)).filter
     (λ e=>qE e=i)).card:ℝ))=_ by exact_mod_cast ht)
 have qU:(E.card:ℝ)/2<=∑i∈L,m i:=by
  have hb:∑i∈qT,m i<=∑i∈qT,((if i∈L then m i else 0)+(E.card:ℝ)/(4*r)):=by
   apply aK;intro i hi;by_cases Ry:i∈L
   ·simp only [Ry,↓reduceIte]
    have:0<=(E.card:ℝ)/(4*r):=by positivity
    linarith
   ·have W7:m i<(E.card:ℝ)/(4*r):=by
     simpa only [L,aD,hi,b5,not_le] using Ry
    simp only [Ry,↓reduceIte,zero_add];exact W7.le
  rw [hsum,f8,Finset.sum_ite_mem] at hb;have hsub:qT∩L=L:=Finset.inter_eq_right.mpr (eW _ _);rw [hsub] at hb;have hconst:∑_i∈qT,(E.card:ℝ)/(4*r)=(E.card:ℝ)/2:=by
   simp only [d5,j7,qT,Finset.card_range,k8,j8];dsimp [r] at *;field_simp
   ;ring
  rw [hconst] at hb;linarith
 let M4 (i:ℕ):Set (V->Bool):={ω | gW i ω<=(p:ℝ)^2*m i/2};have e7:{ω |
   ((E.filter (λ e=>e.1∈aW ω/\e.2∈aW ω)).card:ℝ)<(p:ℝ)^2*E.card/4}⊆⋃ i∈L,M4 i:=by
  intro ω ND;by_contra hnot;have VV:∀i∈L,(p:ℝ)^2*m i/2<=gW i ω:=by
   intro i hi;have hn:ω∉M4 i:=λ h=>hnot (av.mpr ⟨i,av.mpr ⟨hi,h⟩⟩)
   exact (iG hn).le
  have F4:(p:ℝ)^2/2*(∑i∈L,m i)<=∑i∈L,gW i ω:=by
   rw [dR];apply aK;intro i hi;calc
    _=(p:ℝ)^2*m i/2:=by ring
    _<=gW i ω:=VV i hi
  have CS:(∑i∈L,gW i ω)<=∑i∈qT,gW i ω:=jr (eW _ _)
    (λ i _ _=>aN _)
  rw [QH] at CS;have ZU:=aJ qU (by positivity:0<=(p:ℝ)^2/2);change ((E.filter (λ e=>e.1∈aW ω/\e.2∈aW ω)).card:ℝ)<(p:ℝ)^2*E.card/4 at ND;nlinarith
 have td (i:ℕ) (hi:i∈L):(dn V p).real (M4 i)<=exp (-(p:ℝ)^2*E.card/(32*r)):=by
  have ht:=xI p A B wU (C i)
   (λ e he=>hE e (aD.mp he).1) i
   (λ e he=>(aD.mp he).2)
  have hm:(E.card:ℝ)/(4*r)<=m i:=(aD.mp hi).2;have he: -(p:ℝ)^2*m i/8<= -(p:ℝ)^2*E.card/(32*r):=by
   have ht:=mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr (iH (p:ℝ)));calc
    _<=(-(p:ℝ)^2*((E.card:ℝ)/(4*r)))/8:=by linarith
    _=_:=by ring
  exact ht.trans (exp_le_exp.mpr he)
 calc
  _<=(dn V p).real (⋃ i∈L,M4 i):=measureReal_mono e7 (measure_ne_top _ _)
  _<=∑i∈L,(dn V p).real (M4 i):=measureReal_biUnion_finset_le L M4
  _<=∑i∈L,exp (-(p:ℝ)^2*E.card/(32*r)):=aK td
  _=(L.card:ℝ)*exp (-(p:ℝ)^2*E.card/(32*r)):=by simp
  _<=2*r*exp (-(p:ℝ)^2*E.card/(32*r)):=by
   apply aY _ (exp_pos _).le;have ht:=aU (eW (λ i=>(E.card:ℝ)/(4*r)<=m i) qT);have W8:L.card<=2*Fintype.card V:=by simpa only [qT,Finset.card_range] using ht
   change (L.card:ℝ)<=2*(Fintype.card V:ℝ);exact_mod_cast W8
def aX (P:SimpleGraph V) [DecidableRel P.Adj] (v:V) (A:Finset V):=A.filter (P.Adj v)
lemma lS {V:Type cy} [aP:Fintype V] [aO:DecidableEq V] (P:SimpleGraph V) [DecidableRel P.Adj]
  (A B:Finset V):(P.interedges A B).card=∑v∈A,(aX P v B).card:=by
 simp only [interedges,Rel.interedges,aX,card_filter];rw [sum_product]
lemma yk {V:Type cz} [aP:Fintype V] [aO:DecidableEq V] (P:SimpleGraph V) [DecidableRel P.Adj]
  (v:V) (A W:Finset V) (zI:A⊆W):(aX P v W).card=(aX P v A).card+(aX P v (W\A)).card:=by
 have hu:aX P v W=aX P v A∪aX P v (W\A):=by
  ext x;simp only [aX,gQ,aD,aS];constructor
  ·intro ⟨hx,ha⟩
   by_cases Lk:x∈A
   ·exact Or.inl ⟨Lk,ha⟩
   ·exact Or.inr ⟨⟨hx,Lk⟩,ha⟩
  ·rintro (⟨hx,ha⟩ | ⟨⟨hx,_⟩,ha⟩)
   ·exact ⟨zI hx,ha⟩
   ·exact ⟨hx,ha⟩
 rw [hu,j9];apply aL.mpr;intro x hx hy;exact (aS.mp (aD.mp hy).1).2 (aD.mp hx).1
lemma y3 {V:Type cP} [aP:Fintype V] [aO:DecidableEq V] (P:SimpleGraph V) [DecidableRel P.Adj]
  (A B:Finset V) (wU:Disjoint A B):Set.InjOn (λ e:V×V=>s(e.1,e.2)) (P.interedges A B:Set (V×V)):=by
 intro e he f hf xH;rcases kc.mp xH with h | h
 ·exact h
 ·exact False.elim<|aL.mp wU (P.mem_interedges_iff.mp he).1
   ((aF Prod.fst h).symm▸(P.mem_interedges_iff.mp hf).2.1)
lemma BU (P:SimpleGraph V) [DecidableRel P.Adj]
  (W A T:Finset V) (aat:A⊆W) (aau:T⊆W):(P.interedges T (W\T)).card<=(P.interedges A (W\A)).card+card V*(A ∆ T).card:=by
 classical
 let f:=λ e:V×V=>s(e.1,e.2)
 let E:=(P.interedges A (W\A)).image f;let D:=(((A ∆ T) ×ˢ (univ:Finset V)).image f);have hinj:=y3 P T (W\T) (aL.mpr (by intro x hx hy;exact (aS.mp hy).2 hx));have hsub:(P.interedges T (W\T)).image f⊆E∪D:=by
  intro e he;obtain ⟨⟨x,y⟩,hxy,rfl⟩:=bk.mp he;rcases P.mem_interedges_iff.mp hxy with ⟨Ll,VY,hxy⟩;obtain ⟨W9,Xa⟩:=aS.mp VY;by_cases Lk:x∈A
  ·by_cases Ot:y∈A
   ·apply ee
    apply bk.mpr;refine ⟨(y,x),jt.mpr ⟨?_,aQ _⟩,?_⟩
    ·exact k9.mpr (Or.inl ⟨Ot,Xa⟩)
    ·exact bx
   ·apply cQ
    exact bk.mpr ⟨(x,y),P.mem_interedges_iff.mpr
     ⟨Lk,aS.mpr ⟨W9,Ot⟩,hxy⟩,rfl⟩
  ·apply ee
   exact bk.mpr ⟨(x,y),jt.mpr
    ⟨k9.mpr (Or.inr ⟨Ll,Lk⟩),aQ _⟩,rfl⟩
 calc
  _=((P.interedges T (W\T)).image f).card:=(nL hinj).symm
  _<=(E∪D).card:=aU hsub
  _<=E.card+D.card:=dG _ _
  _<=(P.interedges A (W\A)).card+(((A ∆ T) ×ˢ (univ:Finset V))).card:=Nat.add_le_add (ju) ju
  _=_:=by simp [bK]
lemma CX {V:Type cL} [aP:Fintype V] [aO:DecidableEq V] (A T:Finset V):A.card<=T.card+(A ∆ T).card:=by
 have hs:A⊆T∪(A ∆ T):=by
  intro x hx;by_cases Ll:x∈T
  ·exact cQ _ Ll
  ·exact ee _ (k9.mpr (Or.inl ⟨hx,Ll⟩))
 exact (aU hs).trans (dG _ _)
lemma yl {V:Type c9} [aP:Fintype V] [aO:DecidableEq V] (W A T:Finset V):(W\A).card<=(W\T).card+(A ∆ T).card:=by
 have hs:W\A⊆(W\T)∪(A ∆ T):=by
  intro x hx;obtain ⟨Xb,Lk⟩:=aS.mp hx;by_cases Ll:x∈T
  ·exact ee _ (k9.mpr (Or.inr ⟨Ll,Lk⟩))
  ·exact cQ _ (aS.mpr ⟨Xb,Ll⟩)
 exact (aU hs).trans (dG _ _)
lemma q6 (P:SimpleGraph V) [DecidableRel P.Adj]
  (A B Q:Finset V) (Xc:Q⊆A) (c:ℝ)
  (hc:∀v∈Q,c<=(aX P v B).card):c*Q.card<=((P.interedges A B).card:ℝ):=by
 rw [lS,eV];calc
  _=∑v∈Q,c:=by simp [bK]
  _<=∑v∈Q,((aX P v B).card:ℝ):=aK hc
  _<=∑v∈A,((aX P v B).card:ℝ):=jr Xc (λ _ _ _=>aN _)
lemma th (P:SimpleGraph V) [DecidableRel P.Adj]
  (W A:Finset V) (zI:A⊆W) (aaI:0<(A.card:ℝ))
  {p h τ:ℝ} (hp:0<p) (hh:0<h) (hτ:τ<p*h/4)
  (hdeg:∀v,p*h/2<=((aX P v W).card:ℝ))
  (td:((P.interedges A (W\A)).card:ℝ)<τ*A.card):p*h/4<(A.card:ℝ)/\((A\A.filter (λ v=>p*h/4<=((aX P v A).card:ℝ))).card:ℝ)<=4*τ*A.card/(p*h):=by
 have hpart (v:V):((aX P v W).card:ℝ)=((aX P v A).card:ℝ)+((aX P v (W\A)).card:ℝ):=by exact_mod_cast yk P v A W zI
 constructor
 ·by_contra hn
  have ha':(A.card:ℝ)<=p*h/4:=dF hn;have hlo:p*h/4*A.card<=((P.interedges A (W\A)).card:ℝ):=by
   apply q6 P A (W\A) A (Subset.refl _) (p*h/4);intro v _;have hc:((aX P v A).card:ℝ)<=A.card:=by exact_mod_cast aU (eW (P.Adj v) A)
   have hd:=hdeg v;have he:=hpart v;linarith
  nlinarith
 ·let Q:=A\A.filter (λ v=>p*h/4<=((aX P v A).card:ℝ))
  have hl:p*h/4*Q.card<=((P.interedges A (W\A)).card:ℝ):=by
   apply q6 P A (W\A) Q lg (p*h/4);intro v hv;obtain ⟨M5,Rz⟩:=aS.mp hv;have hn:((aX P v A).card:ℝ)<p*h/4:=by simpa only [aD,M5,b5,not_le] using Rz
   have hd:=hdeg v;have he:=hpart v;linarith
  change (Q.card:ℝ)<=_;apply (e3 (f7 hp hh)).mpr;nlinarith
def jq (P:SimpleGraph V) [DecidableRel P.Adj] (S:Finset V):Finset V:=S.biUnion (λ v=>aX P v univ)
lemma y4 (P:SimpleGraph V) [DecidableRel P.Adj]
  (S W A:Finset V):(((jq P S∩W)\A).card:ℝ)<=∑v∈S,((aX P v (W\A)).card:ℝ):=by
 have heq:(jq P S∩W)\A=S.biUnion (λ v=>aX P v (W\A)):=by ext x;simp only [jq,aX,aS,dD,bR,aD,aQ,b5];aesop
 rw [heq];exact_mod_cast c5
lemma y5 (P:SimpleGraph V) [DecidableRel P.Adj]
  (good S A:Finset V) (VZ:∀v∈good,¬Disjoint (aX P v A) S):good⊆jq P S:=by
 intro v hv;obtain ⟨x,Xd,Xe⟩:=not_disjoint_iff.mp (VZ v hv);apply bR.mpr;refine ⟨x,Xe,?_⟩;exact aD.mpr ⟨aQ _,P.adj_symm (aD.mp Xd).2⟩
lemma w4 (P:SimpleGraph V) [DecidableRel P.Adj]
  (W A:Finset V) (zI:A⊆W) (ha:0<(A.card:ℝ))
  {p h τ M:ℝ} (hp:0<p) (hh:0<h) (Lm:0<τ)
  (hτ:τ<p*h/4) (hM:0<M) (Ou:M<=h)
  (vV:(card V:ℝ)*exp (-p*M/4)<1/2)
  (hdeg:∀v,p*h/2<=((aX P v W).card:ℝ))
  (td:((P.interedges A (W\A)).card:ℝ)<τ*A.card):p*h/4<(A.card:ℝ)/\∃S:Finset V,S⊆A/\(S.card:ℝ)<=4*A.card*M/h/\((A ∆ (jq P S∩W)).card:ℝ)<=(4*τ/(p*h)+4*τ*M/h)*A.card:=by
 classical
 obtain ⟨qU,RA⟩:=th P W A zI ha hp hh hτ hdeg td;refine ⟨qU,?_⟩;let good:=A.filter (λ v=>p*h/4<=((aX P v A).card:ℝ));let w:V->ℝ:=λ v=>((aX P v (W\A)).card:ℝ)
 let q:unitInterval:=⟨M/h,fF hM.le hh.le,(kd hh).mpr Ou⟩;have hq:0<(q:ℝ):=div_pos hM hh;have hm:(good.card:ℝ)*exp (-(q:ℝ)*(p*h/4))<1/2:=by
  have heq: -(q:ℝ)*(p*h/4)= -p*M/4:=by dsimp [q];field_simp [hh.ne']
  rw [heq];have hg:(good.card:ℝ)<=card V:=by exact_mod_cast e4 good
  exact (aY hg (exp_pos _).le).trans_lt vV
 have hsum:∑v∈A,w v<=τ*A.card:=by dsimp [w];rw [<-eV,<-lS];exact td.le
 obtain ⟨S,UU,hSc,Xf,Xg⟩:=uJ A
  (cT.mp (by exact_mod_cast ha)) good (λ v=>aX P v A)
  (λ v _=>eW _ _) w (λ _ _=>aN _)
  (f7 Lm ha) hsum
  (λ v hv=>(aD.mp hv).2) q hq hm
 refine ⟨S,UU,?_,?_⟩
 ·convert hSc using 1;dsimp [q];ring
 ·let T:=jq P S∩W
  have xx:good⊆jq P S:=y5 P good S A Xg;have hsub:A ∆ T⊆(A\good)∪(T\A):=by
   intro v hv;rcases k9.mp hv with ⟨M5,Ov⟩ | ⟨Ov,M5⟩
   ·apply cQ;apply aS.mpr;refine ⟨M5,?_⟩;intro Rz;exact Ov (dD.mpr ⟨xx Rz,zI M5⟩)
   ·exact ee _ (aS.mpr ⟨Ov,M5⟩)
  have PM:((A ∆ T).card:ℝ)<=((A\good).card:ℝ)+((T\A).card:ℝ):=by exact_mod_cast (aU hsub).trans (dG _ _)
  have TA:((T\A).card:ℝ)<=4*(q:ℝ)*(τ*A.card):=(y4 P S W A).trans Xf;change ((A ∆ T).card:ℝ)<=_;change ((A\good).card:ℝ)<=_ at RA;calc
   _<=4*τ*A.card/(p*h)+4*(q:ℝ)*(τ*A.card):=dS RA TA |>.trans' PM
   _=_:=by dsimp [q];ring
def cW (P:SimpleGraph V) [DecidableRel P.Adj] (h:ℝ):Prop:=∀U:Finset V,h*min (U.card:ℝ) (Uᶜ.card:ℝ)<=((P.interedges U Uᶜ).card:ℝ)
def b9 (P:SimpleGraph V) [DecidableRel P.Adj] (W:Finset V) (h:ℝ):Prop:=∀A:Finset V,A⊆W->h*min (A.card:ℝ) ((W\A).card:ℝ)<=((P.interedges A (W\A)).card:ℝ)
lemma xJ (P:SimpleGraph V) [DecidableRel P.Adj]
  (W:Finset V) {p h τ M:ℝ} (hp:0<p) (hh:0<h) (Lm:0<τ)
  (hτ:τ<p*h/4) (hM:0<M) (Ou:M<=h)
  (vV:(card V:ℝ)*exp (-p*M/4)<1/2)
  (hε:4*τ/(p*h)+4*τ*M/h<=1/2)
  (zJ:τ+card V*(4*τ/(p*h)+4*τ*M/h)<=p^2*h/8)
  (hexp:cW P h)
  (hdeg:∀v,p*h/2<=((aX P v W).card:ℝ))
  (zK:∀S:Finset V,(S.card:ℝ)<=4*card V*M/h->let U:=jq P S
   p*h/8<=min (U.card:ℝ) (Uᶜ.card:ℝ)->(p^2/4)*((P.interedges U Uᶜ).card:ℝ)<=((P.interedges (U∩W) (W\(U∩W))).card:ℝ)):
  b9 P W τ:=by
 classical
 have iE (A:Finset V) (zI:A⊆W)
   (u6:(A.card:ℝ)<=(W\A).card):τ*A.card<=((P.interedges A (W\A)).card:ℝ):=by
  by_contra hn;have td:=iG hn;have ha:0<(A.card:ℝ):=by by_contra hn;have hz:(A.card:ℝ)=0:=(dF hn).antisymm (aN _);rw [hz,mul_zero] at td;exact (aN _).not_gt td
  obtain ⟨qU,S,UU,hSc,PM⟩:=w4 P W A zI ha
   hp hh Lm hτ hM Ou vV hdeg td
  let U:=jq P S;let T:=U∩W;let δ:ℝ:=(A ∆ T).card;have aav:δ<=(A.card:ℝ)/2:=by have ht:=aY hε ha.le;dsimp [δ,T,U];linarith
  have JP:(A.card:ℝ)/2<=min (U.card:ℝ) (Uᶜ.card:ℝ):=by
   apply le_min
   ·have ht:(A.card:ℝ)<=(T.card:ℝ)+δ:=by
     dsimp [δ];exact_mod_cast CX A T
    have aaJ:(T.card:ℝ)<=U.card:=by exact_mod_cast aU (iF:T⊆U)
    linarith
   ·have ht:((W\A).card:ℝ)<=((W\T).card:ℝ)+δ:=by
     dsimp [δ];exact_mod_cast yl W A T
    have hs:W\T⊆Uᶜ:=by intro v hv;obtain ⟨Xh,Ov⟩:=aS.mp hv;apply cU.mpr;intro RB;exact Ov (dD.mpr ⟨RB,Xh⟩)
    have hh':((W\T).card:ℝ)<=Uᶜ.card:=by exact_mod_cast aU hs
    linarith
  have QI:(S.card:ℝ)<=4*card V*M/h:=by
   apply hSc.trans;have hac:(A.card:ℝ)<=card V:=by exact_mod_cast e4 A
   gcongr
  have hw:=zK S QI (by dsimp [U] at JP;linarith);have he:=hexp U;have hlo:p^2*h*A.card/8<=((P.interedges T (W\T)).card:ℝ):=by have hm:=aJ JP hh.le;have ht:=aJ (hm.trans he) (by positivity:0<=p^2/4);change p^2/4*((P.interedges U Uᶜ).card:ℝ)<=_ at hw;nlinarith
  have Ln:((P.interedges T (W\T)).card:ℝ)<=((P.interedges A (W\A)).card:ℝ)+card V*δ:=by dsimp [δ];exact_mod_cast BU P W A T zI ke
  have hd:=aJ PM (by positivity:0<=(card V:ℝ));have RD:=aY zJ ha.le;change (card V:ℝ)*δ<=_ at hd;nlinarith
 intro A zI;by_cases hs:(A.card:ℝ)<=(W\A).card
 ·rw [f9 hs];exact iE A zI hs
 ·have hs':((W\A).card:ℝ)<=A.card:=(iG hs).le;rw [min_eq_right hs'];have heq:W\(W\A)=A:=Finset.sdiff_sdiff_eq_self zI;have ht:=iE (W\A) lg (by simpa only [heq] using hs');rw [heq] at ht;let:Std.Symm P.Adj:=P.symm;have NH:(P.interedges (W\A) A).card=(P.interedges A (W\A)).card:=Rel.card_interedges_comm (W\A) A;rwa [NH] at ht
lemma Bm (P:SimpleGraph V) [DecidableRel P.Adj]
  {h:ℝ} (hexp:cW P h) (hr:2<=card V) (v:V):h<=((aX P v univ).card:ℝ):=by
 have ht:=hexp {v};have hc:(1:ℝ)<=((({v}:Finset V)ᶜ).card:ℝ):=by
  have:1<=(({v}:Finset V)ᶜ).card:=by rw [nO,iI];omega
  exact_mod_cast this
 simp only [iI,gR,f9 hc,mul_one] at ht;rw [lS,sum_singleton] at ht;have heq:aX P v ({v}:Finset V)ᶜ=aX P v univ:=by ext x;simp only [aX,aD,cU,gd,aQ,b5];exact ⟨λ h=>h.2,λ h=>⟨λ he=>P.irrefl (he▸h),h⟩⟩
 rwa [heq] at ht
lemma xK (P:SimpleGraph V) [DecidableRel P.Adj]
  (p:unitInterval) {h:ℝ} (hdeg:∀v,h<=((aX P v univ).card:ℝ))
  (v:V):(dn V p).real {ω | ((aX P v (aW ω)).card:ℝ)<(p:ℝ)*h/2}<=exp (-(p:ℝ)*h/8):=by
 have heq (ω:V->Bool):aX P v (aW ω)=aX P v univ∩aW ω:=by ext x;simp [aX,and_comm]
 simp_rw [heq];have hs:{ω | (((aX P v univ)∩aW ω).card:ℝ)<(p:ℝ)*h/2}⊆{ω | (((aX P v univ)∩aW ω).card:ℝ)<=(p:ℝ)*(aX P v univ).card/2}:=by
  intro ω hω;change (((aX P v univ)∩aW ω).card:ℝ)<(p:ℝ)*h/2 at hω;exact hω.le.trans (e5
   (aJ (hdeg v) p.property.1) (by norm_num))
 have he: -(p:ℝ)*(aX P v univ).card/8<= -(p:ℝ)*h/8:=by have ht:=aJ (hdeg v) p.property.1;linarith
 exact (measureReal_mono hs (measure_ne_top _ _)).trans
  ((Bj p _).trans (exp_le_exp.mpr he))
lemma BV (s:ℕ) (hr:0<card V):(((univ:Finset V).powerset).filter (λ S=>S.card<=s)).card<=(s+1)*card V^s:=by
 classical
 have heq:(((univ:Finset V).powerset).filter (λ S=>S.card<=s))=(range (s+1)).biUnion (λ t=>(univ:Finset V).powersetCard t):=by ext S;simp only [aD,mem_powerset,gS,b5,bR,j6,lu];exact ⟨λ h=>⟨S.card,by omega,rfl⟩,λ ⟨t,ht,he⟩=>by omega⟩
 rw [heq];calc
  _<=∑t∈range (s+1),((univ:Finset V).powersetCard t).card:=c5
  _<=∑t∈range (s+1),card V^s:=by apply aK;intro t ht;rw [nP,c7];exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hr (by simpa using ht))
  _=_:=by simp [bK]
def DM (P:SimpleGraph V) [DecidableRel P.Adj] (s:ℕ):Finset (Finset V):=((((univ:Finset V).powerset).filter (λ S=>S.card<=s))).image (jq P)
lemma BW (P:SimpleGraph V) [DecidableRel P.Adj]
  (s:ℕ) (hr:0<card V):(DM P s).card<=(s+1)*card V^s:=ju.trans (BV s hr)
lemma vW (P:SimpleGraph V) [DecidableRel P.Adj]
  (p:unitInterval) {h:ℝ} (hh:0<=h) (hexp:cW P h)
  (hr:0<card V) (U:Finset V)
  (hU:(p:ℝ)*h/8<=min (U.card:ℝ) (Uᶜ.card:ℝ)):
  (dn V p).real {ω |
   ((P.interedges (U∩aW ω) (aW ω\(U∩aW ω))).card:ℝ)<(p:ℝ)^2/4*(P.interedges U Uᶜ).card}<=
   2*(card V:ℝ)*exp (-(p:ℝ)^3*h^2/(256*card V)):=by
 have wU:Disjoint U Uᶜ:=aL.mpr (λ _ hx hy=>(cU.mp hy) hx);have heq (ω:V->Bool):P.interedges (U∩aW ω) (aW ω\(U∩aW ω))=(P.interedges U Uᶜ).filter (λ e=>e.1∈aW ω/\e.2∈aW ω):=by ext ⟨x,y⟩;simp only [nQ,dD,aS,aD,cU];aesop
 have ht:=vc p hr U Uᶜ wU (P.interedges U Uᶜ)
  (λ e he=>⟨(P.mem_interedges_iff.mp he).1,(P.mem_interedges_iff.mp he).2.1⟩)
 have hl:(p:ℝ)*h^2/8<=((P.interedges U Uᶜ).card:ℝ):=by have ht:=aJ hU hh;have hu:=hexp U;nlinarith
 have he: -(p:ℝ)^2*(P.interedges U Uᶜ).card/(32*card V)<=
   -(p:ℝ)^3*h^2/(256*card V):=by
  have Rw:0<(card V:ℝ):=by exact_mod_cast hr
  apply (nS (by positivity) (by positivity)).mpr;have hs:=aJ hl (by positivity:0<=(p:ℝ)^2);nlinarith
 simp_rw [heq];have hc:(p:ℝ)^2/4*(P.interedges U Uᶜ).card=(p:ℝ)^2*(P.interedges U Uᶜ).card/4:=by ring
 rw [hc];exact ht.trans (aJ (exp_le_exp.mpr he) (by positivity))
def rE (P:SimpleGraph V) [DecidableRel P.Adj] (p h τ:ℝ) (ω:V->Bool):Prop:=((aW ω).card:ℝ)<=2*p*card V/\(∀v,p*h/2<=((aX P v (aW ω)).card:ℝ))/\b9 P (aW ω) τ
lemma wO (P:SimpleGraph V) [DecidableRel P.Adj]
  (p:unitInterval) {h τ M:ℝ} (hp:0<(p:ℝ)) (hh:0<h) (Lm:0<τ)
  (hτ:τ<(p:ℝ)*h/4) (hM:0<M) (Ou:M<=h)
  (hr:2<=card V)
  (vV:(card V:ℝ)*exp (-(p:ℝ)*M/4)<1/2)
  (hε:4*τ/((p:ℝ)*h)+4*τ*M/h<=1/2)
  (zJ:τ+card V*(4*τ/((p:ℝ)*h)+4*τ*M/h)<=(p:ℝ)^2*h/8)
  (hexp:cW P h):(dn V p).real {ω | ¬rE P (p:ℝ) h τ ω}<=exp (-(p:ℝ)*card V/3)+card V*exp (-(p:ℝ)*h/8)+2*card V*((⌈4*card V*M/h⌉₊+1:ℕ):ℝ)*(card V:ℝ)^⌈4*card V*M/h⌉₊*exp (-(p:ℝ)^3*h^2/(256*card V)):=by
 classical
 let μ:=dn V p;let s:=⌈4*(card V:ℝ)*M/h⌉₊;let large:=(DM P s).filter
  (λ U=>(p:ℝ)*h/8<=min (U.card:ℝ) (Uᶜ.card:ℝ))
 let G1:Set (V->Bool):={ω | 2*(p:ℝ)*card V<((aW ω).card:ℝ)};let B₁ (v:V):Set (V->Bool):={ω | ((aX P v (aW ω)).card:ℝ)<(p:ℝ)*h/2};let B₂ (U:Finset V):Set (V->Bool):={ω |
  ((P.interedges (U∩aW ω) (aW ω\(U∩aW ω))).card:ℝ)<(p:ℝ)^2/4*(P.interedges U Uᶜ).card}
 have h₀:μ.real G1<=exp (-(p:ℝ)*card V/3):=by
  have hs:G1⊆{ω | 2*(p:ℝ)*card V<=((aW ω).card:ℝ)}:=by intro ω hω;change 2*(p:ℝ)*card V<((aW ω).card:ℝ) at hω;exact hω.le
  have ht:=Bk p (univ:Finset V);simp only [c7,univ_inter] at ht;exact (measureReal_mono hs (measure_ne_top _ _)).trans ht
 have h₁:μ.real (⋃ v∈(univ:Finset V),B₁ v)<=card V*exp (-(p:ℝ)*h/8):=by
  calc
   _<=∑v:V,μ.real (B₁ v):=measureReal_biUnion_finset_le _ _
   _<=∑_v:V,exp (-(p:ℝ)*h/8):=aK (λ v _=>xK P p (Bm P hexp hr) v)
   _=_:=by simp
 have h₂:μ.real (⋃ U∈large,B₂ U)<=2*card V*((s+1:ℕ):ℝ)*(card V:ℝ)^s*exp (-(p:ℝ)^3*h^2/(256*card V)):=by
  calc
   _<=∑U∈large,μ.real (B₂ U):=measureReal_biUnion_finset_le _ _
   _<=∑_U∈large,2*(card V:ℝ)*exp (-(p:ℝ)^3*h^2/(256*card V)):=by apply aK;intro U hU;exact vW P p hh.le hexp (by omega) U (aD.mp hU).2
   _=(large.card:ℝ)*(2*card V*exp (-(p:ℝ)^3*h^2/(256*card V))):=by simp
   _<=(((s+1:ℕ):ℝ)*(card V:ℝ)^s)*(2*card V*exp (-(p:ℝ)^3*h^2/(256*card V))):=by
    apply aY _ (by positivity);have ht:large.card<=(s+1)*card V^s:=(aU (eW _ _)).trans
      (BW P s (by omega))
    exact_mod_cast ht
   _=_:=by ring
 have e7:{ω | ¬rE P (p:ℝ) h τ ω}⊆(G1∪(⋃ v∈(univ:Finset V),B₁ v))∪(⋃ U∈large,B₂ U):=by
  intro ω hω;by_contra hn;have TB:ω∉G1:=λ h=>hn (Or.inl (Or.inl h))
  have NI (v:V):ω∉B₁ v:=λ h=>hn (Or.inl (Or.inr
   (av.mpr ⟨v,av.mpr ⟨aQ _,h⟩⟩)))
  have NJ (U:Finset V) (hU:U∈large):ω∉B₂ U:=λ h=>hn (Or.inr
   (av.mpr ⟨U,av.mpr ⟨hU,h⟩⟩))
  apply hω;have hd (v:V):(p:ℝ)*h/2<=((aX P v (aW ω)).card:ℝ):=dF (NI v);refine ⟨dF TB,hd,?_⟩;apply xJ P (aW ω) hp hh Lm hτ hM Ou
   vV hε zJ hexp hd
  intro S hS;dsimp only;intro hU;let U:=jq P S;have hSc:S.card<=s:=by have ht:=hS.trans (Nat.le_ceil (4*(card V:ℝ)*M/h));dsimp [s];exact_mod_cast ht
  have hmem:U∈large:=by apply aD.mpr;refine ⟨?_,hU⟩;apply bk.mpr;exact ⟨S,aD.mpr ⟨mem_powerset.mpr (gS _),hSc⟩,rfl⟩
  exact dF (NJ U hmem)
 calc
  _<=μ.real ((G1∪(⋃ v∈(univ:Finset V),B₁ v))∪(⋃ U∈large,B₂ U)):=measureReal_mono e7 (measure_ne_top _ _)
  _<=μ.real (G1∪(⋃ v∈(univ:Finset V),B₁ v))+μ.real (⋃ U∈large,B₂ U):=measureReal_union_le _ _
  _<=μ.real G1+μ.real (⋃ v∈(univ:Finset V),B₁ v)+μ.real (⋃ U∈large,B₂ U):=dS (measureReal_union_le _ _) dH
  _<=_:=dS (dS h₀ h₁) h₂
end af.aV
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz
section
open Filter Asymptotics Real
open scoped Topology
section
namespace af.aV
lemma jB (K c a b:ℝ) (hc:0<c) (hab:a<b):∀ᶠ D:ℝ in atTop,K*D^a<c*D^b:=by
 have ht:Tendsto (λ D:ℝ=>K*D^(a-b)) atTop (𝓝 0):=by have hh:=(tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul K;simpa only [neg_sub,mul_zero] using hh
 filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually_lt_const hc] with D hD Xi;have hb:0<D^b:=d6 hD b;have heq:D^a=D^(a-b)*D^b:=by rw [<-c8 hD];congr 1;ring
 rw [heq,<-mul_assoc];exact mul_lt_mul_of_pos_right Xi hb
lemma jT (a b c:ℝ) (hb:0<b) (hc:0<c):Tendsto (λ D:ℝ=>D^a*exp (-c*D^b)) atTop (𝓝 0):=by
 have ht:=(tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
  (nT hb)
 apply ht.congr';filter_upwards [eventually_gt_atTop (0:ℝ)] with D hD;dsimp only [Function.comp_def];rw [<-lz hD.le,mul_div_cancel₀ _ hb.ne']
lemma wP:∀ᶠ D:ℝ in atTop,log D <=D^(1/10:ℝ):=by filter_upwards [(o8 (show (0:ℝ)<1/10 by norm_num)).eventuallyLE,eventually_ge_atTop (1:ℝ)] with D hD h1;simpa only [kg,gk (nU h1),gk (fG (by linarith) _)] using hD
def ox (c p D:ℝ):ℝ:=exp (-p/3*D^(9/10:ℝ))+D^(51/50:ℝ)*exp (-(p*c/8)*D^(9/10:ℝ))+(2*(4/c+2))*(D^(23/20:ℝ)*exp (-(p^3*c^2/512)*D^(39/50:ℝ)))
lemma ym (c p:ℝ) (hc:0<c) (hp:0<p):Tendsto (ox c p) atTop (𝓝 0):=by
 have h0:=jT 0 (9/10) (p/3) (by norm_num) (by positivity);have h1:=jT (51/50) (9/10) (p*c/8) (by norm_num) (by positivity);have h2:=(jT (23/20) (39/50) (p^3*c^2/512)
  (by norm_num) (by positivity)).const_mul (2*(4/c+2))
 unfold ox;simpa [neg_div,Real.rpow_zero] using (h0.add h1).add h2
def xL (c p D:ℝ) (r:ℕ):Prop:=let h:=c*D^(9/10:ℝ)
 let τ:=D^(37/50:ℝ);let M:=D^(1/100:ℝ)
 2<=r/\τ<p*h/4/\M<=h/\(r:ℝ)*exp (-p*M/4)<1/2/\4*τ/(p*h)+4*τ*M/h<=1/2/\τ+r*(4*τ/(p*h)+4*τ*M/h)<=p^2*h/8/\exp (-p*r/3)+r*exp (-p*h/8)+2*r*((⌈4*r*M/h⌉₊+1:ℕ):ℝ)*(r:ℝ)^⌈4*r*M/h⌉₊*exp (-p^3*h^2/(256*r))<=ox c p D
lemma y6 (c p D:ℝ) (r:ℕ) (hc:0<c) (hp:0<p)
  (hD:1<=D) (A0:0<(r:ℝ)) (yo:(r:ℝ)<=D^(51/50:ℝ))
  (kI:log D <=D^(1/10:ℝ))
  (jF:((51/50)*(4/c+2))*D^(23/100:ℝ)<=(p^3*c^2/512)*D^(39/50:ℝ)):
  let h:=c*D^(9/10:ℝ);let M:=D^(1/100:ℝ)
  2*r*((⌈4*r*M/h⌉₊+1:ℕ):ℝ)*(r:ℝ)^⌈4*r*M/h⌉₊*exp (-p^3*h^2/(256*r))<=(2*(4/c+2))*(D^(23/20:ℝ)*exp (-(p^3*c^2/512)*D^(39/50:ℝ))):=by
 let h:=c*D^(9/10:ℝ);let M:=D^(1/100:ℝ);let K:=4/c+2;have hK:0<K:=by dsimp [K];positivity
 have pT:0<D:=by linarith
 have hh:0<h:=by dsimp [h];positivity
 have TC:0<M:=d6 pT _;have ZV:0< r:=by exact_mod_cast A0
 have hs:((⌈4*r*M/h⌉₊+1:ℕ):ℝ)<=K*D^(13/100:ℝ):=by
  have TD:4*D^(51/50:ℝ)*M/h=(4/c)*D^(13/100:ℝ):=by dsimp [M,h];rw [show (13/100:ℝ)=(51/50+1/100)-9/10 by norm_num,gT pT,c8 pT];field_simp
  calc
   _<=4*r*M/h+2:=by have hs:=(nV (show 0<=4*(r:ℝ)*M/h by positivity)).le;push_cast;linarith
   _<=4*D^(51/50:ℝ)*M/h+2:=by gcongr
   _=(4/c)*D^(13/100:ℝ)+2:=by rw [TD]
   _<=K*D^(13/100:ℝ):=by have hd:=jv hD (show (0:ℝ)<=13/100 by norm_num);dsimp [K];nlinarith
 have UZ:log (r:ℝ)<=(51/50)*log D:=by simpa only [Real.log_rpow pT] using Real.log_le_log A0 yo
 have Xj:(⌈4*r*M/h⌉₊:ℝ)*log (r:ℝ)<=(p^3*c^2/512)*D^(39/50:ℝ):=by
  have hs':(⌈4*r*M/h⌉₊:ℝ)<=K*D^(13/100:ℝ):=by push_cast at hs;linarith
  calc
   _<=K*D^(13/100:ℝ)*((51/50)*log D):=by
    apply iJ hs' UZ
    ·exact nU (by exact_mod_cast (show 1<=r by omega))
    ·positivity
   _<=K*D^(13/100:ℝ)*((51/50)*D^(1/10:ℝ)):=by gcongr
   _=((51/50)*K)*D^(23/100:ℝ):=by have he:=c8 pT (13/100:ℝ) (1/10);norm_num at he;rw [he];ring
   _<=_:=jF
 have BX:c^2*D^(39/50:ℝ)<=h^2/(r:ℝ):=by
  have he:c^2*D^(39/50:ℝ)=h^2/D^(51/50:ℝ):=by dsimp [h];rw [show (39/50:ℝ)=(9/10)*2-51/50 by norm_num,gT pT];have Kp:=lA pT.le (9/10:ℝ) 2;norm_num only [j8] at Kp;rw [show (9/10:ℝ)*2=9/5 by norm_num,Kp];ring
  rw [he];exact div_le_div_of_nonneg_left (iH h) A0 yo
 have O8:exp ((⌈4*r*M/h⌉₊:ℝ)*log (r:ℝ)-p^3*h^2/(256*r))<=exp (-(p^3*c^2/512)*D^(39/50:ℝ)):=by
  apply Real.exp_le_exp.mpr;have hn:=aJ BX (show 0<=p^3/256 by positivity);have q7:(p^3/256)*(h^2/(r:ℝ))=p^3*h^2/(256*r):=by ring
  rw [q7] at hn;nlinarith
 have TE:2*(r:ℝ)*((⌈4*r*M/h⌉₊+1:ℕ):ℝ)<=2*K*D^(23/20:ℝ):=by
  calc
   _<=2*D^(51/50:ℝ)*(K*D^(13/100:ℝ)):=by gcongr
   _=_:=by have he:=c8 pT (51/50:ℝ) (13/100);norm_num at he;rw [he];ring
 have zK:2*r*((⌈4*r*M/h⌉₊+1:ℕ):ℝ)*(r:ℝ)^⌈4*r*M/h⌉₊*exp (-p^3*h^2/(256*r))<=(2*K)*(D^(23/20:ℝ)*exp (-(p^3*c^2/512)*D^(39/50:ℝ))):=by
  have heq:(r:ℝ)^⌈4*r*M/h⌉₊*exp (-p^3*h^2/(256*r))=exp ((⌈4*r*M/h⌉₊:ℝ)*log (r:ℝ)-p^3*h^2/(256*r)):=by rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log A0];simp only [neg_mul,Real.exp_neg,gq]
  rw [mul_assoc (2*(r:ℝ)*_) _ _,heq];exact (iJ TE O8 (exp_pos _).le (by positivity)).trans_eq (by ring)
 exact zK
lemma wQ (c p:ℝ) (hc:0<c) (hp:0<p):∀ᶠ D:ℝ in atTop,∀r:ℕ,D^(9/10:ℝ)<=r->(r:ℝ)<=D^(51/50:ℝ)->xL c p D r:=by
 let K:=4/c+2;have hK:0<K:=by dsimp [K];positivity
 have vV:Tendsto (λ D:ℝ=>D^(51/50:ℝ)*exp (-p/4*D^(1/100:ℝ)))
   atTop (𝓝 0):=by
  convert jT (51/50) (1/100) (p/4)
   (by norm_num) (by positivity) using 1;simp [neg_div]
 filter_upwards [eventually_ge_atTop (1:ℝ),(nT (show (0:ℝ)<9/10 by norm_num)).eventually_ge_atTop 2,jB 1 (p*c/4) (37/50) (9/10) (by positivity) (by norm_num),jB 1 c (1/100) (9/10) hc (by norm_num),vV.eventually_lt_const (show (0:ℝ)<1/2 by norm_num),jB (4/(p*c)) (1/4) (-4/25) 0 (by norm_num) (by norm_num),jB (4/c) (1/4) (-3/20) 0 (by norm_num) (by norm_num),jB 1 (p^2*c/24) (37/50) (9/10) (by positivity) (by norm_num),jB (4/(p*c)) (p^2*c/24) (43/50) (9/10) (by positivity) (by norm_num),jB (4/c) (p^2*c/24) (87/100) (9/10) (by positivity) (by norm_num),wP,jB ((51/50)*K) (p^3*c^2/512) (23/100) (39/50)
   (by positivity) (by norm_num)] with D hD h2 hτ hM hm RG RH ZW ZZ Z0 kI jF
 intro r NK yo;have pT:0<D:=by linarith
 have PN:2<=r:=by exact_mod_cast h2.trans NK
 have A0:0<(r:ℝ):=by exact_mod_cast (show 0< r by omega)
 let h:=c*D^(9/10:ℝ);let τ:=D^(37/50:ℝ);let M:=D^(1/100:ℝ);have hh:0<h:=by dsimp [h];positivity
 have Xk:0<τ:=d6 pT _;have TC:0<M:=d6 pT _;have FZ:4*τ/(p*h)=(4/(p*c))*D^(-4/25:ℝ):=by dsimp [τ,h];rw [show (-4/25:ℝ)=37/50-9/10 by norm_num,gT pT];field_simp
 have F3:4*τ*M/h=(4/c)*D^(-3/20:ℝ):=by dsimp [τ,M,h];rw [show (-3/20:ℝ)=(37/50+1/100)-9/10 by norm_num,gT pT,c8 pT];field_simp
 have TF:D^(51/50:ℝ)*((4/(p*c))*D^(-4/25:ℝ))=(4/(p*c))*D^(43/50:ℝ):=by rw [mul_left_comm,<-c8 pT];norm_num
 have TG:D^(51/50:ℝ)*((4/c)*D^(-3/20:ℝ))=(4/c)*D^(87/100:ℝ):=by rw [mul_left_comm,<-c8 pT];norm_num
 refine ⟨PN,?_,(by simpa only [one_mul] using hM.le),?_,?_,?_,?_⟩
 ·change τ<p*h/4;dsimp [τ,h];simpa only [one_mul,div_mul_eq_mul_div,mul_assoc] using hτ
 ·change (r:ℝ)*exp (-p*M/4)<1/2
  calc
   _<=D^(51/50:ℝ)*exp (-p*M/4):=aY yo (exp_pos _).le
   _<_:=by simpa [M,div_mul_eq_mul_div] using hm
 ·change 4*τ/(p*h)+4*τ*M/h<=1/2;rw [FZ,F3];simp only [Real.rpow_zero,mul_one] at RG RH;linarith
 ·change τ+(r:ℝ)*(4*τ/(p*h)+4*τ*M/h)<=p^2*h/8
  rw [FZ,F3];have ht:(r:ℝ)*((4/(p*c))*D^(-4/25:ℝ)+(4/c)*D^(-3/20:ℝ))<=(4/(p*c))*D^(43/50:ℝ)+(4/c)*D^(87/100:ℝ):=by
   calc
    _<=D^(51/50:ℝ)*((4/(p*c))*D^(-4/25:ℝ)+(4/c)*D^(-3/20:ℝ)):=by apply aY yo;positivity
    _=_:=by rw [mul_add,TF,TG]
  dsimp [τ,h];nlinarith
 ·change exp (-p*r/3)+r*exp (-p*h/8)+2*r*((⌈4*r*M/h⌉₊+1:ℕ):ℝ)*(r:ℝ)^⌈4*r*M/h⌉₊*exp (-p^3*h^2/(256*r))<=ox c p D
  have zK:=y6 c p D r hc hp hD A0 yo kI jF.le;have u6:exp (-p*r/3)<=exp (-p/3*D^(9/10:ℝ)):=by apply exp_le_exp.mpr;have ht:=aJ NK hp.le;nlinarith
  have i6:(r:ℝ)*exp (-p*h/8)<=D^(51/50:ℝ)*exp (-(p*c/8)*D^(9/10:ℝ)):=by
   have heq: -p*h/8=-(p*c/8)*D^(9/10:ℝ):=by dsimp [h];ring
   rw [heq];exact aY yo (exp_pos _).le
  exact dS (dS u6 i6) zK
end af.aV
namespace af.aV
open Filter MeasureTheory Real
universe u
lemma Aw (c:ℝ) (hc:0<c) (p:unitInterval)
  (hp:0<(p:ℝ)) (aaw:(p:ℝ)<1) (ε:ℝ) (hε:0<ε):∃dN:ℝ,∀D:ℝ,dN<=D ->∀(V:Type u) [Fintype V] [DecidableEq V]
   (P:SimpleGraph V) [DecidableRel P.Adj],D^(9/10:ℝ)<=(card V:ℝ)->(card V:ℝ)<=D^(51/50:ℝ)->cW P (c*D^(9/10:ℝ))->
   (dn V p).real {ω | ¬rE P (p:ℝ) (c*D^(9/10:ℝ))
    (D^(37/50:ℝ)) ω}<=ε:=by
 have Lo:∀ᶠ D:ℝ in atTop,1<=D /\(∀r:ℕ,D^(9/10:ℝ)<=r->(r:ℝ)<=D^(51/50:ℝ)->xL c (p:ℝ) D r)/\
   ox c (p:ℝ) D <=ε:=by
  filter_upwards [eventually_ge_atTop (1:ℝ),wQ c (p:ℝ) hc hp,(ym c (p:ℝ) hc hp).eventually_le_const hε] with D h1 h2 h3;exact ⟨h1,h2,h3⟩
 obtain ⟨dN,ko⟩:=Lo.exists_forall_of_atTop;refine ⟨dN,?_⟩;intro D hD V _ _ P _ NK yo hexp;obtain ⟨h1,gN,O9⟩:=ko D hD;have pT:0<D:=by linarith
 obtain ⟨hr,hτ,hM,vV,he,zJ,hbound⟩:=gN (card V) NK yo;exact (wO P p hp (by positivity) (by positivity)
  hτ (by positivity) hM hr vV he zJ hexp).trans (hbound.trans O9)
end af.aV
open MeasureTheory ProbabilityTheory Finset
section
namespace af.aV
def uB (p:unitInterval) (hp:3*(p:ℝ)<=1):PMF (Fin 4):=PMF.ofFintype (λ i=>ENNReal.ofReal (if i=3 then 1-3*(p:ℝ) else (p:ℝ))) (by rw [Fin.sum_univ_four];simp only [show (0:Fin 4)≠3 by decide,show (1:Fin 4)≠3 by decide,show (2:Fin 4)≠3 by decide,↓reduceIte,];rw [<-lB p.property.1 p.property.1,<-lB (by linarith [p.property.1]) p.property.1,<-lB (by linarith [p.property.1]) (by linarith)];norm_num [show (p:ℝ)+(p:ℝ)+(p:ℝ)+(1-3*(p:ℝ))=1 by ring])
def F5 (i:Fin 3) (j:Fin 4):Bool:=decide (j=i.castSucc)
lemma wV (p:unitInterval):ENNReal.ofReal (p:ℝ)=(unitInterval.toNNReal p:ENNReal):=by unfold ENNReal.ofReal;apply aF (λ x:NNReal=>(x:ENNReal));apply aZ;exact Real.coe_toNNReal _ p.property.1
lemma EL (p:unitInterval) (hp:3*(p:ℝ)<=1) (i:Fin 3):MeasurePreserving (F5 i) (uB p hp).toMeasure
   (bernoulliMeasure true false p):=by
 have JQ:0<=(p:ℝ):=p.property.1;have TH:0<=1-3*(p:ℝ):=by linarith
 refine ⟨gV _,?_⟩;apply Measure.ext_iff_singleton.mpr;intro b;rw [Measure.map_apply (gV _) (measurableSet_singleton _)];rw [PMF.toMeasure_apply_fintype];simp only [uB];cases b<;>fin_cases i<;>simp [F5,Fin.sum_univ_four,PMF.ofFintype_apply]
 all_goals
  first
  | exact wV p
  | rw [<-lB JQ JQ,<-lB (by linarith:0<=(p:ℝ)+(p:ℝ)) TH]
    convert wV (unitInterval.symm p) using 1;congr 1;change (p:ℝ)+(p:ℝ)+(1-3*(p:ℝ))=1-(p:ℝ);ring
end af.aV
namespace af.aV
open Finset MeasureTheory ProbabilityTheory
section
variable {V:Type bX} [Fintype V] [DecidableEq V]
def n3 (i:Fin 3) (ω:V->Fin 4):V->Bool:=λ v=>F5 i (ω v)
def rF (V:Type bY) [Fintype V] (p:unitInterval) (hp:3*(p:ℝ)<=1):Measure (V->Fin 4):=Measure.pi (λ _:V=>(uB p hp).toMeasure)
instance JR (p:unitInterval) (hp:3*(p:ℝ)<=1):IsProbabilityMeasure (rF V p hp):=by unfold rF;infer_instance
lemma yp {V:Type cy} [aP:Fintype V] [aO:DecidableEq V] (p:unitInterval) (hp:3*(p:ℝ)<=1) (i:Fin 3):MeasurePreserving (n3 i) (rF V p hp) (dn V p):=by exact measurePreserving_pi _ _ (λ _=>EL p hp i)
lemma y7 {V:Type cz} [aP:Fintype V] [aO:DecidableEq V] (ω:V->Fin 4) (i j:Fin 3) (hij:i≠j):Disjoint (aW (n3 i ω)) (aW (n3 j ω)):=by apply aL.mpr;intro v hi hj;simp only [aW,aD,aQ,b5,n3,F5,decide_eq_true_eq] at hi hj;exact hij (Fin.castSucc_injective 3 (hi.symm.trans hj))
universe u
lemma zL (c:ℝ) (hc:0<c) (p:unitInterval)
  (hp:0<(p:ℝ)) (U0:3*(p:ℝ)<=1):∃dN:ℝ,∀D:ℝ,dN<=D ->∀(V:Type u) [Fintype V] [DecidableEq V]
   (P:Fin 3->SimpleGraph V) [∀i,DecidableRel (P i).Adj],D^(9/10:ℝ)<=(card V:ℝ)->(card V:ℝ)<=D^(51/50:ℝ)->(∀i,cW (P i) (c*D^(9/10:ℝ)))->∃W:Fin 3->Finset V,(∀i j,i≠j->Disjoint (W i) (W j))/\(∀i,((W i).card:ℝ)<=2*(p:ℝ)*card V)/\(∀i v,(p:ℝ)*(c*D^(9/10:ℝ))/2<=((aX (P i) v (W i)).card:ℝ))/\(∀i,b9 (P i) (W i) (D^(37/50:ℝ))):=by
 have hp1:(p:ℝ)<1:=by linarith
 obtain ⟨dN,ko⟩:=Aw.{u} c hc p hp hp1 (1/4) (by norm_num)
 refine ⟨dN,?_⟩;intro D hD V _ _ P _ hlo hhi ob;let μ:=rF V p U0;let B:Fin 3->Set (V->Fin 4):=λ i=>{ω | ¬rE (P i) (p:ℝ) (c*D^(9/10:ℝ)) (D^(37/50:ℝ)) (n3 i ω)}
 have hB:∀i,μ.real (B i)<=1/4:=by
  intro i;have hm:=(yp (V:=V) p U0 i).measure_preimage
   ((Set.Finite.measurableSet (Set.toFinite {ω | ¬rE (P i) (p:ℝ) (c*D^(9/10:ℝ))
    (D^(37/50:ℝ)) ω})).nullMeasurableSet)
  change (μ (B i)).toReal<=1/4;rw [show μ (B i)=(dn V p) {ω | ¬rE (P i) (p:ℝ)
   (c*D^(9/10:ℝ)) (D^(37/50:ℝ)) ω} from hm]
  exact ko D hD V (P i) hlo hhi (ob i)
 have hi:∑i∈(univ:Finset (Fin 3)),μ.real (B i)<1:=by
  calc
   _<=∑i∈(univ:Finset (Fin 3)),(1/4:ℝ):=by exact aK (λ i _=>hB i)
   _<1:=by norm_num
 obtain ⟨ω,hω⟩:=wM (μ:=μ) univ B hi;have xx:∀i,rE (P i) (p:ℝ) (c*D^(9/10:ℝ)) (D^(37/50:ℝ))
   (n3 i ω):=by
  intro i;exact not_not.mp (hω i (aQ i))
 refine ⟨λ i=>aW (n3 i ω),y7 ω,λ i=>(xx i).1,λ i=>(xx i).2.1,λ i=>(xx i).2.2⟩
end
end af.aV
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.Splitting
open MeasureTheory ProbabilityTheory Finset Real
section qe
variable {Ω:Type bX} {I:Type bY} [MeasurableSpace Ω] {μ:Measure Ω} [IsProbabilityMeasure μ]
open aR.af.aV
end qe
section
open aR.af.aV
variable {V:Type cz} [Fintype V] [DecidableEq V]
lemma pZ (P:SimpleGraph V) [DecidableRel P.Adj]
  (U:Finset V):Set.InjOn (λ e:V×V=>s(e.1,e.2)) (P.interedges U Uᶜ:Set (V×V)):=by
 intro e he f hf xH;rcases (kc.mp xH) with h | h
 ·exact h
 ·have Ow:=(P.mem_interedges_iff.mp he).1;have Xl:=(P.mem_interedges_iff.mp hf).2.1;have Il:e.1=f.2:=aF Prod.fst h;exact False.elim ((cU.mp Xl) (Il▸Ow))
def iP (V:Type cP) [Fintype V] (l:ℕ) [NeZero l] :Measure (Sym2 V->Fin l):=Measure.pi (λ _:Sym2 V=>(PMF.uniformOfFintype (Fin l)).toMeasure)
instance JS (l:ℕ) [NeZero l] :IsProbabilityMeasure (iP V l):=by unfold iP;infer_instance
def kZ {l:ℕ} (i:Fin l) (e:Sym2 V) (ω:Sym2 V->Fin l):ℝ:=if ω e=i then 1 else 0
lemma CY {V:Type cL} [aP:Fintype V] [aO:DecidableEq V] {l:ℕ} [NeZero l] (i:Fin l):iIndepFun (kZ (V:=V) i) (iP V l):=by
 exact iIndepFun_pi (X:=λ _:Sym2 V=>λ j:Fin l=>if j=i then (1:ℝ) else 0)
  (λ _=>(gV _).aemeasurable)
lemma Ax {V:Type c9} [aP:Fintype V] [aO:DecidableEq V] {l:ℕ} [NeZero l] (i:Fin l) (e:Sym2 V):∫ ω,kZ i e ω ∂iP V l=1/(l:ℝ):=by
 have hl:=(measurePreserving_eval
  (λ _:Sym2 V=>(PMF.uniformOfFintype (Fin l)).toMeasure) e).hasLaw
 have hi:=hl.integral_comp (f:=λ j:Fin l=>if j=i then (1:ℝ) else 0)
  (gV _).aestronglyMeasurable
 rw [PMF.integral_eq_sum] at hi;simpa [iP,kZ,PMF.uniformOfFintype_apply] using hi
def dI (P:SimpleGraph V) {l:ℕ} (ω:Sym2 V->Fin l) (i:Fin l):SimpleGraph V where
 Adj x y:=P.Adj x y/\ω s(x,y)=i
 symm:=⟨by intro x y h;exact ⟨h.1.symm,by simpa only [bx] using h.2⟩⟩
 loopless:=⟨by intro x h;exact P.irrefl h.1⟩
instance NL (P:SimpleGraph V) [DecidableRel P.Adj]
 {l:ℕ} (ω:Sym2 V->Fin l) (i:Fin l):DecidableRel (dI P ω i).Adj:=λ _ _=>inferInstanceAs (Decidable (_/\_))
lemma BY {V:Type dW} [aP:Fintype V] [aO:DecidableEq V] (P:SimpleGraph V) [DecidableRel P.Adj]
  {l:ℕ} (ω:Sym2 V->Fin l) (i:Fin l) (S T:Finset V):(dI P ω i).interedges S T=(P.interedges S T).filter (λ e=>ω s(e.1,e.2)=i):=by
 ext ⟨x,y⟩;simp only [nQ,aD];change (x∈S/\y∈T/\(P.Adj x y/\ω s(x,y)=i))↔_;tauto
lemma KG (P:SimpleGraph V) [DecidableRel P.Adj]
  {l:ℕ} (ω:Sym2 V->Fin l) (i:Fin l) (S:Finset V):(∑e∈(P.interedges S Sᶜ).image (λ e=>s(e.1,e.2)),kZ i e ω)=(((dI P ω i).interedges S Sᶜ).card:ℝ):=by
 rw [sum_image (pZ P S)];simp only [kZ,sum_boole,BY]
lemma CZ (P:SimpleGraph V) [DecidableRel P.Adj]
  {l:ℕ} [NeZero l] (i:Fin l) (S:Finset V) {h:ℝ}
  (hexp:cW P h) (hS:S.card<=Sᶜ.card):
  (iP V l).real {ω |
   (((dI P ω i).interedges S Sᶜ).card:ℝ)<h*S.card/(2*l)}<=exp (-h*S.card/(8*l)):=by
 let E:=(P.interedges S Sᶜ).image (λ e=>s(e.1,e.2));have lN:E.card=(P.interedges S Sᶜ).card:=nL (pZ P S);have hl:0<(l:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne l)
 have ob:h*S.card<=(E.card:ℝ):=by rw [lN];have he:=hexp S;rwa [f9 (by exact_mod_cast hS)] at he
 have hb:=pH (μ:=iP V l) E
  (λ e=>gV (kZ i e)) (CY i)
  (λ e ω=>by simp only [kZ];split<;>simp)
  (1/(l:ℝ)) (by positivity) (Ax i)
 apply (measureReal_mono (show {ω |
  (((dI P ω i).interedges S Sᶜ).card:ℝ)<h*S.card/(2*l)}⊆{ω | (∑e∈E,kZ i e ω)<=(1/(l:ℝ))*E.card/2} from ?_)).trans
  (hb.trans ?_)
 ·intro ω hω
  change (∑e∈E,kZ i e ω)<=(1/(l:ℝ))*E.card/2;rw [show (∑e∈E,kZ i e ω)=(((dI P ω i).interedges S Sᶜ).card:ℝ) from KG P ω i S];calc
   _<=h*S.card/(2*l):=le_of_lt hω
   _<=(E.card:ℝ)/(2*l):=e5 ob (by positivity)
   _=_:=by ring
 ·apply exp_le_exp.mpr
  have he:=e5 ob (show 0<=8*(l:ℝ) by positivity);calc
   _= -((E.card:ℝ)/(8*l)):=by ring
   _<= -(h*S.card/(8*l)):=neg_le_neg he
   _=_:=by ring
lemma yq (P:SimpleGraph V) [DecidableRel P.Adj] {h:ℝ}
  (ob:∀S:Finset V,S.Nonempty->S.card<=Sᶜ.card->h*S.card<=((P.interedges S Sᶜ).card:ℝ)):cW P h:=by
 intro S;by_cases he:S=∅
 ·simp [he]
 by_cases hc:Sᶜ=∅
 ·simp [hc]
 by_cases hs:S.card<=Sᶜ.card
 ·rw [f9 (by exact_mod_cast hs)];exact ob S (nonempty_iff_ne_empty.mpr he) hs
 ·rw [min_eq_right (by exact_mod_cast le_of_not_ge hs)]
  have hi:=ob Sᶜ (nonempty_iff_ne_empty.mpr hc) (by simpa using le_of_not_ge hs);have NH:(P.interedges Sᶜ S).card=(P.interedges S Sᶜ).card:=by have:=P.symm;exact Rel.card_interedges_comm Sᶜ S
  simpa only [compl_compl,NH] using hi
lemma yu (q:ℝ):(∑S∈(Finset.univ:Finset (Finset V)).erase ∅,q^S.card)=(1+q)^(Fintype.card V)-1:=by
 have hs:=Finset.sum_erase_add (s:=Finset.univ) (λ S:Finset V=>q^S.card)
  (aQ (∅:Finset V))
 have hp:=Finset.prod_one_add (s:=(Finset.univ:Finset V)) (f:=λ _=>q);simp only [Finset.prod_const,c7,Finset.powerset_univ] at hp;simp only [Finset.card_empty,pow_zero] at hs;linarith
lemma w5 (P:SimpleGraph V) [DecidableRel P.Adj]
  {l:ℕ} [NeZero l] {h:ℝ} (hexp:cW P h):(iP V l).real {ω | ∃i,¬cW (dI P ω i) (h/(2*l))}<=l*(exp ((card V:ℝ)*exp (-h/(8*l)))-1):=by
 let JT:Finset (Finset V):=univ.erase ∅;let B (i:Fin l) (S:Finset V):Set (Sym2 V->Fin l):={ω | S.card<=Sᶜ.card/\(((dI P ω i).interedges S Sᶜ).card:ℝ)<h*S.card/(2*l)};let q:ℝ:=exp (-h/(8*l));have cover:{ω | ∃i,¬cW (dI P ω i) (h/(2*l))}⊆⋃ i∈(univ:Finset (Fin l)),⋃ S∈JT,B i S:=by
  intro ω hω;rcases hω with ⟨i,hi⟩;by_contra hn;apply hi;apply yq;intro S hS hs;have hb:ω∉B i S:=by
   intro hm;apply hn;exact av.mpr ⟨i,av.mpr ⟨aQ _,av.mpr ⟨S,av.mpr
     ⟨iK.mpr ⟨hS.ne_empty,aQ _⟩,hm⟩⟩⟩⟩
  have hc:h*S.card/(2*l)<=(((dI P ω i).interedges S Sᶜ).card:ℝ):=by exact dF (λ hf=>hb ⟨hs,hf⟩)
  convert hc using 1;ring
 have hbound (i:Fin l) (S:Finset V):(iP V l).real (B i S)<=q^S.card:=by
  by_cases hs:S.card<=Sᶜ.card
  ·calc
    _<=(iP V l).real {ω |
      (((dI P ω i).interedges S Sᶜ).card:ℝ)<h*S.card/(2*l)}:=measureReal_mono (λ _ hw=>hw.2)
    _<=exp (-h*S.card/(8*l)):=CZ P i S hexp hs
    _=q^S.card:=by dsimp [q];rw [<-exp_nat_mul];congr 1;ring
  ·have he:B i S=∅:=by ext ω;simp [B,hs]
   rw [he,measureReal_empty];exact pow_nonneg (exp_pos _).le _
 calc
  _<=(iP V l).real
    (⋃ i∈(univ:Finset (Fin l)),⋃ S∈JT,B i S):=measureReal_mono cover (measure_ne_top _ _)
  _<=∑i:Fin l,(iP V l).real (⋃ S∈JT,B i S):=measureReal_biUnion_finset_le _ _
  _<=∑i:Fin l,∑S∈JT,(iP V l).real (B i S):=aK (λ _ _=>measureReal_biUnion_finset_le _ _)
  _<=∑_i:Fin l,∑S∈JT,q^S.card:=by apply aK;intro i _;exact aK (λ S _=>hbound i S)
  _=(l:ℝ)*((1+q)^(card V)-1):=by simp only [JT,yu,d5,c7,dU,j7]
  _<=l*(exp ((card V:ℝ)*q)-1):=by
   apply aJ _ (aN l);apply sub_le_sub_right;calc
    _<=(exp q)^(card V):=nZ (by dsimp [q];positivity) (by linarith [add_one_le_exp q]) _
    _=_:=(exp_nat_mul _ _).symm
lemma vX (P:SimpleGraph V) [DecidableRel P.Adj]
  {l:ℕ} [NeZero l] {h:ℝ} (hexp:cW P h)
  (RI:(l:ℝ)*(exp ((card V:ℝ)*exp (-h/(8*l)))-1)<1):∃ω:Sym2 V->Fin l,(∀i,cW (dI P ω i) (h/(2*l)))/\(∀x y,P.Adj x y↔∃i,(dI P ω i).Adj x y)/\(∀i j,i≠j->Disjoint (dI P ω i).edgeSet (dI P ω j).edgeSet):=by
 have he:=(w5 P hexp).trans_lt RI;have hh:∃ω:Sym2 V->Fin l,∀i,cW (dI P ω i) (h/(2*l)):=by
  by_contra hn
  push Not at hn
  have V0:{ω:Sym2 V->Fin l | ∃i,¬cW (dI P ω i) (h/(2*l))}=Set.univ:=Set.eq_univ_of_forall hn;simp only [V0,Measure.real,measure_univ,ENNReal.toReal_one] at he;exact (lt_irrefl _ he)
 obtain ⟨ω,hω⟩:=hh;refine ⟨ω,hω,?_,?_⟩
 ·intro x y;exact ⟨λ hxy=>⟨ω s(x,y),hxy,rfl⟩,λ ⟨_,hxy,_⟩=>hxy⟩
 ·intro i j hij
  apply aI.mpr;intro e hei yP;induction e using bJ with | _ x y=>
   have hi:(dI P ω i).Adj x y:=by simpa using hei
   have hj:(dI P ω j).Adj x y:=by simpa using yP
   exact hij (hi.2.symm.trans hj.2)
end
open aR.af.aV
open Filter Asymptotics
open scoped Topology
noncomputable def p3 (c:ℝ) (l:ℕ) (D:ℝ):ℝ:=(l:ℝ)*(Real.exp (D^(51/50:ℝ)*Real.exp ((-(c/(8*l)))*D^(9/10:ℝ)))-1)
lemma vI (c:ℝ) (hc:0<c) (l:ℕ) (hl:0<l):Tendsto (p3 c l) atTop (𝓝 0):=by
 have RJ:0<(l:ℝ):=by exact_mod_cast hl
 have ht:=jT (51/50) (9/10) (c/(8*l))
  (by norm_num) (by positivity)
 have hh:=((Real.continuous_exp.tendsto 0).comp ht).sub_const 1 |>.const_mul (l:ℝ);unfold p3;convert hh using 1<;>norm_num
universe u
lemma uL (c:ℝ) (hc:0<c) (l:ℕ) (hl:0<l):∃dN:ℝ,∀D:ℝ,dN<=D ->∀(V:Type u) [Fintype V] [DecidableEq V]
   (P:SimpleGraph V) [DecidableRel P.Adj] (h:ℝ),c*D^(9/10:ℝ)<=h->D^(9/10:ℝ)<=(card V:ℝ)->(card V:ℝ)<=D^(51/50:ℝ)->cW P h->∃ω:Sym2 V->Fin l,(∀i,cW (dI P ω i) (h/(2*l)))/\(∀x y,P.Adj x y↔∃i,(dI P ω i).Adj x y)/\(∀i j,i≠j->Disjoint (dI P ω i).edgeSet (dI P ω j).edgeSet):=by
 have:NeZero l:=⟨hl.ne'⟩;have RJ:0<(l:ℝ):=by exact_mod_cast hl
 have Lo:=(vI c hc l hl).eventually_lt_const
  (show (0:ℝ)<1 by norm_num)
 obtain ⟨dN,ko⟩:=Lo.exists_forall_of_atTop;refine ⟨dN,?_⟩;intro D hD V _ _ P _ h hh Z1 yo hexp;apply vX P hexp;apply lt_of_le_of_lt _ (ko D hD);unfold p3;apply aJ _ RJ.le;apply sub_le_sub_right;apply exp_le_exp.mpr;apply iJ yo _ (exp_pos _).le ((aN (card V)).trans yo);apply exp_le_exp.mpr;have he:=e5 hh (show 0<=8*(l:ℝ) by positivity);calc
  -h/(8*l)= -(h/(8*l)):=by ring
  _<= -(c*D^(9/10:ℝ)/(8*l)):=neg_le_neg he
  _= -(c/(8*l))*D^(9/10:ℝ):=by ring
end af.Splitting
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.A3
section
open Finset
variable {I:Type bX} {V:Type bY} [DecidableEq I] [DecidableEq V] [Nonempty V]
lemma Gh (A:Finset I) (uC:I->I)
  (TI:Function.Involutive uC) (Pa:∀i,uC i≠i)
  (N:I->Finset V) (k:ℕ)
  (K6:∀i∈A,A.card<=((N i).card-1)*k):∃f:I->V,(∀i∈A,f i∈N i)/\(∀i∈A,uC i∈A->f i≠f (uC i))/\(∀v,(A.filter (λ i=>f i=v)).card<=k):=by
 induction A using o9 with
 | empty=>exact ⟨λ _=>Classical.choice inferInstance,by simp⟩
 | @insert i A hi ih=>
   obtain ⟨f,hf,zN,rG⟩:=ih (by intro j hj;exact (aU (subset_insert i A)).trans (K6 j (by simp [hj])));have hlt:A.card<((N i).erase (f (uC i))).card*k:=by have h:=K6 i (by simp);have lN:=pred_card_le_card_erase (s:=N i) (a:=f (uC i));have hmul:=Nat.mul_le_mul_right k lN;rw [nW hi] at h;omega
   obtain ⟨v,hv,lG⟩:=exists_card_fiber_lt_of_card_lt_mul (f:=f) hlt;have Xm:=(iK.mp hv).2;have RK:=(iK.mp hv).1;let g:=Function.update f i v;have gi:g i=v:=by simp [g]
   have Lq:∀j,j≠i->g j=f j:=by intro j hj;simp [g,hj]
   refine ⟨g,?_,?_,?_⟩
   ·intro j hj
    rcases bU.mp hj with rfl | hj
    ·simpa only [gi] using Xm
    ·rw [Lq j (ne_of_mem_of_not_mem hj hi)];exact hf j hj
   ·intro j hj PO
    by_cases GO:j=i
    ·subst j;rw [gi,Lq (uC i) (Pa i)];exact RK
    ·rw [Lq j GO]
     by_cases Lr:uC j=i
     ·rw [Lr,gi]
      have Xn:j=uC i:=by rw [<-Lr,TI]
      simpa [Xn] using RK.symm
     ·rw [Lq (uC j) Lr]
      exact zN j (mem_of_mem_insert_of_ne hj GO)
       (mem_of_mem_insert_of_ne PO Lr)
   ·intro w
    have hold:A.filter (λ j=>g j=w)=A.filter (λ j=>f j=w):=by apply filter_congr;intro j hj;rw [Lq j (ne_of_mem_of_not_mem hj hi)]
    rw [po,hold];by_cases DN:v=w
    ·simp only [gi,DN,ej];rw [nW (λ h=>hi (aD.mp h).1)];simpa only [DN] using Nat.succ_le_of_lt lG
    ·simp only [gi,DN,ite_false];exact rG w
lemma w6 (S:Finset I) (N:I->Finset V) (k:ℕ)
  (K6:∀i∈S,2*S.card<=((N i).card-1)*k):∃f:I×Fin 2->V,(∀i∈S,∀t,f (i,t)∈N i)/\(∀i∈S,f (i,0)≠f (i,1))/\(∀v,((S ×ˢ univ).filter (λ i=>f i=v)).card<=k):=by
 let uC:I×Fin 2->I×Fin 2:=λ i=>(i.1,1-i.2)
 have hm:Function.Involutive uC:=by rintro ⟨i,t⟩;fin_cases t<;>rfl
 have Pa:∀i,uC i≠i:=by rintro ⟨i,t⟩;fin_cases t<;>(intro h;have hh:=aF Prod.snd h;norm_num [uC] at hh)
 obtain ⟨f,hf,zN,rG⟩:=Gh (S ×ˢ univ) uC hm Pa
  (λ i=>N i.1) k (by intro i hi;simpa [oE,bK] using K6 i.1 (jt.mp hi).1)
 refine ⟨f,?_,?_,rG⟩
 ·intro i hi t;exact hf (i,t) (by simp [hi])
 ·intro i hi;exact zN (i,0) (by simp [hi]) (by simp [uC,hi])
lemma y8 (S:Finset I) (N:I->Finset V)
  (r d:ℝ) (hr:(S.card:ℝ)<=r) (hd:4<=d)
  (hN:∀i∈S,d/2<=((N i).card:ℝ)):∃f:I×Fin 2->V,(∀i∈S,∀t,f (i,t)∈N i)/\(∀i∈S,f (i,0)≠f (i,1))/\(∀v,((S ×ˢ univ).filter (λ i=>f i=v)).card<=⌈8*r/d⌉₊):=by
 apply w6;intro i hi;have aaK:0<d:=by linarith
 have hr0:0<=r:=dY (aN _) hr;have aaL:=hN i hi;have V5:1<=(N i).card:=by exact_mod_cast (by linarith:(1:ℝ)<=(N i).card)
 have hn:d/4<=(((N i).card-1:ℕ):ℝ):=by rw [Nat.cast_sub V5];push_cast;linarith
 have hk:8*r/d<=(⌈8*r/d⌉₊:ℝ):=Nat.le_ceil _;have RL:0<=(⌈8*r/d⌉₊:ℝ):=aN _;have F6:2*(S.card:ℝ)<=(((N i).card-1:ℕ):ℝ)*(⌈8*r/d⌉₊:ℝ):=by
  calc
   _<=2*r:=by linarith
   _=(d/4)*(8*r/d):=by field_simp;ring
   _<=(d/4)*(⌈8*r/d⌉₊:ℝ):=aJ hk (by positivity)
   _<=_:=aY hn RL
 exact_mod_cast F6
end
end af.A3
namespace af
section
open Finset Real Filter
local instance (p:Prop):Decidable p:=Classical.propDecidable p
noncomputable def kL (η:ℝ):ℝ:=min (η/12) (1/12)
noncomputable def gC (c:ℝ):ℝ:=min c 1/6
universe u
lemma BZ (c η:ℝ) (hc:0<c) (hη:0<η):∃dN:ℝ,∀D:ℝ,dN<=D ->∀(V:Type u) [Fintype V] [DecidableEq V]
   (G P:SimpleGraph V) [DecidableRel P.Adj],P<=G->D^(9/10:ℝ)<=(card V:ℝ)->(card V:ℝ)<=D^(51/50:ℝ)->aR.af.aV.cW P (c*D^(9/10:ℝ))->∃(ω:Sym2 V->Fin 3) (W:Fin 3->Finset V) (f:Fin 3->V×Fin 2->V),(∀i,aR.af.Splitting.dI P ω i<=G)/\(∀i j,i≠j->Disjoint (aR.af.Splitting.dI P ω i).edgeSet
     (aR.af.Splitting.dI P ω j).edgeSet)/\
    (∀i,aR.af.aV.cW (aR.af.Splitting.dI P ω i)
     (gC c*D^(9/10:ℝ)))/\
    (∀i j,i≠j->Disjoint (W i) (W j))/\(∀i,2<=(W i).card)/\(∀i,((W i).card:ℝ)<=2*kL η*card V)/\(∀i,(W i).card<card V)/\((∑i,(W i).card:ℕ):ℝ)<=η*card V/\(∀i,aV.b9 (aR.af.Splitting.dI P ω i) (W i)
     (D^(37/50:ℝ)))/\
    (∀i v,v∉W i->∀t,f i (v,t)∈W i/\(aR.af.Splitting.dI P ω i).Adj v (f i (v,t)))/\
    (∀i v,v∉W i->f i (v,0)≠f i (v,1))/\(∀i w,(((W i)ᶜ ×ˢ univ).filter (λ x=>f i x=w)).card<=⌈8*(card V:ℝ)/(kL η*(gC c*D^(9/10:ℝ)))⌉₊):=by
 let JU:=min c 1;let a:=gC c;let q:=kL η;have TJ:0<JU:=lt_min hc (by norm_num);have ha:0<a:=by dsimp [a,gC];positivity
 have hq:0<q:=by dsimp [q,kL];positivity
 have aax:q<=1/12:=min_le_right _ _;have aay:q<=η/12:=min_le_left _ _;have Xo:3*q<=1:=by linarith
 have Xp:6*q<=η:=by linarith
 have Xq:2*q<1:=by linarith
 let p:unitInterval:=⟨q,hq.le,by linarith⟩;obtain ⟨D₁,K7⟩:=aR.af.Splitting.uL.{u} JU TJ 3 (by norm_num)
 obtain ⟨D₂,F7⟩:=aV.zL.{u} a ha p hq Xo
 have ht:∀ᶠ D:ℝ in atTop,4/(q*a)<=D^(9/10:ℝ):=(nT (by norm_num:(0:ℝ)<9/10)).eventually
   (eventually_ge_atTop _)
 obtain ⟨D₃,TK⟩:=ht.exists_forall_of_atTop;refine ⟨max 1 (max D₁ (max D₂ D₃)),?_⟩;intro D hD V _ _ G P _ oe hlo hhi hexp;have hD1:1<=D:=(b6 _ _).trans hD;have QJ:D₁<=D:=(dY (b6 _ _) (bC _ _)).trans hD;have Pc:D₂<=D:=(dY (b6 _ _) (dY (bC _ _) (bC _ _))).trans hD;have QK:D₃<=D:=(dY (bC _ _) (dY (bC _ _) (bC _ _))).trans hD;have hpow:0<D^(9/10:ℝ):=d6 (by linarith) _;have hd:4<=q*(a*D^(9/10:ℝ)):=by have hh:=(dK (f7 hq ha)).mp (TK D QK);nlinarith
 have hr:0<(card V:ℝ):=hpow.trans_le hlo;have:Nonempty V:=card_pos_iff.mp (by exact_mod_cast hr);have QM:aR.af.aV.cW P (JU*D^(9/10:ℝ)):=by
  intro U;exact (aY
   (aY (min_le_left c 1) hpow.le)
   (le_min (aN _) (aN _))).trans (hexp U)
 obtain ⟨ω,ob,e7,hdisj⟩:=K7 D QJ V P
  (JU*D^(9/10:ℝ)) dH hlo hhi QM
 have PR:∀i,aV.cW (aR.af.Splitting.dI P ω i)
   (a*D^(9/10:ℝ)):=by
  intro i;have heq:a*D^(9/10:ℝ)=JU*D^(9/10:ℝ)/(2*(3:ℝ)):=by dsimp [a,gC,JU];ring
  rw [heq];exact ob i
 obtain ⟨W,RM,Im,M6,TL⟩:=F7 D Pc V
  (λ i=>aR.af.Splitting.dI P ω i) hlo hhi PR
 have TN:∀i,2<=(W i).card:=by
  intro i;let v:V:=Classical.choice inferInstance;have hn:=M6 i v;have hsub:aV.aX (aR.af.Splitting.dI P ω i) v (W i)⊆W i:=eW _ _;have hh:=aU hsub;have hn':(2:ℝ)<=(aV.aX (aR.af.Splitting.dI P ω i) v (W i)).card:=by change q*(a*D^(9/10:ℝ))/2<=_ at hn;linarith
  have RN:2<=(aV.aX (aR.af.Splitting.dI P ω i) v (W i)).card:=by exact_mod_cast hn'
  omega
 have Lu:∀i,(W i).card<card V:=by intro i;have hh:=(Im i).trans_lt (mul_lt_of_lt_one_left hr Xq);exact_mod_cast hh
 have F8:((∑i,(W i).card:ℕ):ℝ)<=η*card V:=by have hh:=aK (λ i (_:i∈(univ:Finset (Fin 3)))=>Im i);simp only [d5,c7,dU,j7] at hh;rw [eV];exact hh.trans (by dsimp [p];nlinarith [aY Xp hr.le])
 have hrep:∀i,∃f:V×Fin 2->V,(∀v∈(W i)ᶜ,∀t,f (v,t)∈aV.aX (aR.af.Splitting.dI P ω i) v (W i))/\(∀v∈(W i)ᶜ,f (v,0)≠f (v,1))/\(∀w,(((W i)ᶜ ×ˢ univ).filter (λ x=>f x=w)).card<=⌈8*(card V:ℝ)/(q*(a*D^(9/10:ℝ)))⌉₊):=by
  intro i;exact A3.y8 (W i)ᶜ
   (λ v=>aV.aX (aR.af.Splitting.dI P ω i) v (W i))
   (card V) (q*(a*D^(9/10:ℝ)))
   (by exact_mod_cast (e4 ((W i)ᶜ))) hd
   (λ v _=>M6 i v)
 choose f hf zN rG using hrep;refine ⟨ω,W,f,?_,hdisj,?_,RM,TN,Im,Lu,F8,TL,?_,?_,rG⟩
 ·intro i x y hxy;exact oe hxy.1
 ·exact PR
 ·intro i v hv t;exact aD.mp (hf i v (cU.mpr hv) t)
 ·intro i v hv;exact zN i v (cU.mpr hv)
end
end af
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af
open Finset
variable {V:Type} [Fintype V] [DecidableEq V]
open aR.af.aV
open aR.af.Splitting
lemma s7
  (P:SimpleGraph V) [DecidableRel P.Adj]
  (h:ℝ) (hexp:cW P h)
  (hr:0<(card V:ℝ))
  (F:Finset (Sym2 V)) (B rH:Finset V)
  (W:V->Finset V)
  (hmono:B⊆rH)
  (iE:(B.card:ℝ)<=(card V:ℝ)/2)
  (hF:(((P.interedges B Bᶜ).filter (λ e=>s(e.1,e.2)∈F)).card:ℝ)<=h*(B.card:ℝ)/4)
  (hW:∀v∈B,((W v).card:ℝ)<=h/4)
  (QN:∀v∈B,∀w∉B,P.Adj v w->s(v,w)∉F->w∉W v->w∈rH):
  (1+h/(2*(card V:ℝ)))*(B.card:ℝ)<=(rH.card:ℝ):=by
 let E:=P.interedges B Bᶜ;let NM:=E.filter (λ e=>s(e.1,e.2)∈F);let NN:=B.biUnion (λ v=>({v}:Finset V) ×ˢ (W v));let NO:=(univ:Finset V) ×ˢ (rH\B);have e7:E⊆NM∪NN∪NO:=by
  intro e he;rcases P.mem_interedges_iff.mp he with ⟨hv,hw,hadj⟩;have PS:e.2∉B:=cU.mp hw;by_cases JV:s(e.1,e.2)∈F
  ·exact cQ _ (cQ _
    (aD.mpr ⟨he,JV⟩))
  by_cases M7:e.2∈W e.1
  ·apply cQ;apply ee;apply bR.mpr;exact ⟨e.1,hv,jt.mpr ⟨by simp,M7⟩⟩
  ·apply ee
   exact jt.mpr ⟨aQ _,aS.mpr
    ⟨QN e.1 hv e.2 PS hadj JV M7,PS⟩⟩
 have B0:E.card<=NM.card+NN.card+NO.card:=(aU e7).trans<|(dG _ _).trans<|l5 (dG _ _) _;have TO:NN.card<=∑v∈B,(W v).card:=by
  simpa [NN,oE] using
   (c5 (s:=B) (t:=λ v=>({v}:Finset V) ×ˢ W v))
 have EO:NO.card=card V*(rH\B).card:=by simp [NO]
 have V6:E.card<=NM.card+(∑v∈B,(W v).card)+card V*(rH\B).card:=by omega
 have hsum:(∑v∈B,((W v).card:ℝ))<=(h/4)*B.card:=by
  calc
   _<=∑_v∈B,h/4:=aK hW
   _=_:=by simp [bK]
 have JW:B.card+Bᶜ.card=card V:=by rw [nO];exact Nat.add_sub_of_le (e4 B)
 have Ox:(B.card:ℝ)+(Bᶜ.card:ℝ)=(card V:ℝ):=by exact_mod_cast JW
 have Pd:(B.card:ℝ)<=(Bᶜ.card:ℝ):=by linarith
 have ob:h*(B.card:ℝ)<=(E.card:ℝ):=by simpa [f9 Pd,E] using hexp B
 have RO:(rH\B).card+B.card=rH.card:=by rw [l6 hmono];exact Nat.sub_add_cancel (aU hmono)
 have Z2:((rH\B).card:ℝ)+(B.card:ℝ)=(rH.card:ℝ):=by exact_mod_cast RO
 have TP:(E.card:ℝ)<=(NM.card:ℝ)+(∑v∈B,((W v).card:ℝ))+(card V:ℝ)*((rH\B).card:ℝ):=by exact_mod_cast V6
 have ER:h*(B.card:ℝ)/2<=(card V:ℝ)*((rH\B).card:ℝ):=by nlinarith [ob,TP,hF,hsum]
 have hdiv:h*(B.card:ℝ)/(2*(card V:ℝ))<=((rH\B).card:ℝ):=by apply (dK (by positivity:0<2*(card V:ℝ))).mpr;nlinarith [ER]
 calc
  (1+h/(2*(card V:ℝ)))*(B.card:ℝ)=(B.card:ℝ)+h*(B.card:ℝ)/(2*(card V:ℝ)):=by ring
  _<=(B.card:ℝ)+((rH\B).card:ℝ):=dS (le_refl _) hdiv
  _=(rH.card:ℝ):=by linarith
def eE (P:SimpleGraph V) (F:Finset (Sym2 V)) (W:Finset V):SimpleGraph V where
 Adj v w:=P.Adj v w/\s(v,w)∉F/\v∉W/\w∉W
 symm:=⟨by intro v w h;exact ⟨h.1.symm,by simpa only [bx] using h.2.1,h.2.2.2,h.2.2.1⟩⟩
 loopless:=⟨by intro v h;exact P.irrefl h.1⟩
noncomputable def jE (G:SimpleGraph V) (s:V) (t:ℕ):Finset V:=by
 classical
 exact univ.filter (λ v=>∃p:G.Walk s v,p.length<=t)
@[simp] lemma oy {V:Type} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V) (s v:V) (t:ℕ):v∈jE G s t↔∃p:G.Walk s v,p.length<=t:=by
 classical
 simp [jE]
lemma Gi (G:SimpleGraph V) (s:V) (t:ℕ):s∈jE G s t:=by exact (oy G s s t).mpr ⟨.nil,by simp⟩
lemma DO (G:SimpleGraph V) (s:V) {t u:ℕ} (GQ:t<=u):jE G s t⊆jE G s u:=by intro v hv;obtain ⟨p,hp⟩:=(oy G s v t).mp hv;exact (oy G s v u).mpr ⟨p,hp.trans GQ⟩
lemma A4 {V:Type} [aP:Fintype V] [aO:DecidableEq V] (P:SimpleGraph V) (F:Finset (Sym2 V)) (W:Finset V)
  {s v:V} (p:(eE P F W).Walk s v) (hs:s∉W):v∉W:=by
 induction p with
 | nil=>exact hs
 | cons hadj p ih=>exact ih hadj.2.2.2
lemma MF (P:SimpleGraph V) (F:Finset (Sym2 V)) (W:Finset V)
  (s:V) (hs:s∉W) (t:ℕ):Disjoint (jE (eE P F W) s t) W:=by
 apply aL.mpr;intro v hv;obtain ⟨p,_⟩:=(oy _ _ _ _).mp hv;exact A4 P F W p hs
lemma KH (G:SimpleGraph V) (s v w:V) (t:ℕ)
  (hv:v∈jE G s t) (hadj:G.Adj v w):w∈jE G s (t+1):=by
 obtain ⟨p,hp⟩:=(oy _ _ _ _).mp hv;apply (oy _ _ _ _).mpr;exact ⟨p.concat hadj,by simpa using l5 hp 1⟩
lemma _root_.aR.af.aV.cW.le_order (P:SimpleGraph V) [DecidableRel P.Adj]
  (h:ℝ) (hexp:cW P h) (hr:2<=card V):h<=(card V:ℝ):=by
 obtain ⟨v⟩:=card_pos_iff.mp (by omega:0<card V);have JW:1<=({v}:Finset V)ᶜ.card:=by simp only [nO,iI];omega
 have Ox:(1:ℝ)<=(({v}:Finset V)ᶜ.card:ℝ):=by exact_mod_cast JW
 have hc:=hexp {v};simp only [iI,gR,f9 Ox,mul_one] at hc;have Ln:=P.card_interedges_le_mul ({v}:Finset V) ({v}:Finset V)ᶜ;simp only [iI,one_mul] at Ln;have hle:=(e4 (({v}:Finset V)ᶜ));exact hc.trans (by exact_mod_cast Ln.trans hle)
noncomputable def jG (r h:ℝ):ℕ:=⌈8*(r/h)*Real.logb 2 (2*r)⌉₊
noncomputable def zO (r:ℝ):ℕ:=⌈Real.logb 2 r⌉₊
noncomputable def dQ (r h:ℝ):ℕ:=2*jG r h*(1+zO r)
lemma In (r h:ℝ) (hr:1<=r) (hh:0<h) (PV:h<=r):r/2<(1+h/(2*r))^jG r h:=by
 have hr0:0< r:=by linarith
 let x:=h/(2*r);have hx0:0<=x:=by dsimp [x];positivity
 have V7:x<=1:=by dsimp [x];apply (dK (by positivity:0<2*r)).mpr;linarith
 have kI:h/(4*r)<=Real.log (1+h/(2*r)):=by
  have heq:h/(4*r)=x/2:=by dsimp [x];ring
  rw [heq];calc
   x/2<=2*x/(x+2):=by apply (e3 (by linarith:0<x+2)).mpr;nlinarith [bZ hx0 (sub_nonneg.mpr V7)]
   _<=Real.log (1+x):=Real.le_log_one_add_of_nonneg hx0
 have RP:0<Real.log 2:=kO (by norm_num);have Z3:Real.log 2<=1:=by have htwo:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2);norm_num at htwo ⊢;exact htwo
 have WU:0<Real.log (2*r):=kO (by linarith);have PW:Real.log (2*r)<=Real.logb 2 (2*r):=by rw [Real.logb];apply (e3 RP).mpr;nlinarith
 have hg:8*(r/h)*Real.logb 2 (2*r)<=(jG r h:ℝ):=Nat.le_ceil _;have QO:2*Real.log (2*r)<=Real.log ((1+h/(2*r))^jG r h):=by
  rw [Real.log_pow];calc
   2*Real.log (2*r)<=2*Real.logb 2 (2*r):=by linarith
   _=(8*(r/h)*Real.logb 2 (2*r))*(h/(4*r)):=by
    field_simp
    ;ring
   _<=(jG r h:ℝ)*(h/(4*r)):=aY hg (by positivity)
   _<=(jG r h:ℝ)*Real.log (1+h/(2*r)):=aJ kI (by positivity)
 have iE:Real.log (r/2)<2*Real.log (2*r):=by have:=Real.log_le_log (by positivity:0< r/2) (by linarith:r/2<=2*r);linarith
 apply (Real.log_lt_log_iff (by positivity:0< r/2) (by positivity)).mp;exact iE.trans_le QO
def cx (F:Finset (Sym2 V)) (v:V):Finset (Sym2 V):=F.filter (λ e=>v∈e)
lemma D4 {V:Type} [aP:Fintype V] [aO:DecidableEq V] (F E:Finset (Sym2 V)) (v:V):cx (F∪E) v=cx F v∪cx E v:=by simp [cx,filter_union]
lemma q8 (F E:Finset (Sym2 V)) (v:V):(cx (F∪E) v).card<=(cx F v).card+(cx E v).card:=by rw [D4];exact dG _ _
lemma C2 (F:Finset (Sym2 V)):∑v:V,(cx F v).card<=2*F.card:=by
 have heq:∑v:V,(cx F v).card=∑e∈F,e.toFinset.card:=by simp only [cx,cV,ck];rw [gD];apply cZ rfl;intro e he;simp [<-Sym2.mem_toFinset]
 rw [heq];calc
  _<=∑_e∈F,2:=aK (λ e _=>by
   rw [Sym2.card_toFinset]
   split<;>norm_num)
  _=2*F.card:=by simp [bK]
lemma nY {V:Type} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V) {s t:V}
  (p:G.Walk s t) (hp:p.IsPath):(cx p.edges.toFinset s).card<=1:=by
 have hsub:cx p.edges.toFinset s⊆{s(s,p.snd)}:=by intro e he;obtain ⟨Oy,hs⟩:=aD.mp he;obtain ⟨v,A5⟩:=Sym2.mem_iff_exists.mp hs;subst e;have hv:=hp.eq_snd_of_mem_edges (bw.mp Oy);simp [hv]
 exact (aU hsub).trans (by simp)
lemma qI (G:SimpleGraph V) {s t:V}
  (p:G.Walk s t) (hp:p.IsPath):(cx p.edges.toFinset t).card<=1:=by
 simpa using nY G p.reverse hp.reverse
lemma og {V:Type} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V) {s t v:V}
  (p:G.Walk s t) (hv:v∉p.support):cx p.edges.toFinset v=∅:=by
 apply l7.mpr;intro e he;obtain ⟨Oy,Oz⟩:=aD.mp he;have hm:=p.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e,bw.mp Oy,Oz⟩);exact hv hm
lemma y9 (G:SimpleGraph V) {s t:V}
  (p:G.Walk s t) (hp:p.IsPath) (v:V):(cx p.edges.toFinset v).card<=2:=by
 by_cases hv:v∈p.support
 ·have Z4:=qI G (p.takeUntil v hv) (hp.takeUntil hv)
  have Z5:=nY G (p.dropUntil v hv) (hp.dropUntil hv);have heq:p.edges.toFinset=(p.takeUntil v hv).edges.toFinset∪(p.dropUntil v hv).edges.toFinset:=by have he:=aF (λ q:G.Walk s t=>q.edges.toFinset) (p.take_spec hv);simpa only [oF,List.toFinset_append] using he.symm
  rw [heq];exact (q8 _ _ v).trans (by omega)
 ·rw [og G p hv];simp
lemma uD (P:SimpleGraph V) [DecidableRel P.Adj]
  (B:Finset V) (F:Finset (Sym2 V)):((P.interedges B Bᶜ).filter (λ e=>s(e.1,e.2)∈F)).card<=∑v∈B,(cx F v).card:=by
 let T:=B.biUnion (λ v=>({v}:Finset V) ×ˢ cx F v);have hc:((P.interedges B Bᶜ).filter (λ e=>s(e.1,e.2)∈F)).card<=T.card:=by
  apply gG (λ e:V×V=>(e.1,s(e.1,e.2)))
  ·intro e he;obtain ⟨Oy,Xr⟩:=aD.mp he;apply bR.mpr;refine ⟨e.1,(P.mem_interedges_iff.mp Oy).1,jt.mpr ⟨by simp,?_⟩⟩;exact aD.mpr ⟨Xr,by simp⟩
  ·intro e he f hf heq
   have V8:=aF Prod.snd heq;exact pZ P B (aD.mp he).1
    (aD.mp hf).1 V8
 have hT:T.card<=∑v∈B,(cx F v).card:=by
  simpa [T] using c5 (s:=B)
   (t:=λ v=>({v}:Finset V) ×ˢ cx F v)
 exact hc.trans hT
lemma w7 (P:SimpleGraph V) [DecidableRel P.Adj]
  (h:ℝ) (hexp:cW P h) (hr:0<(card V:ℝ))
  (F:Finset (Sym2 V)) (W:Finset V) (s:V) (hs:s∉W)
  (hF:∀v,((cx F v).card:ℝ)<=h/4)
  (hW:(W.card:ℝ)<=h/4) (t:ℕ)
  (iE:((jE (eE P F W) s t).card:ℝ)<=(card V:ℝ)/2):(1+h/(2*(card V:ℝ)))*(jE (eE P F W) s t).card<=((jE (eE P F W) s (t+1)).card:ℝ):=by
 classical
 apply s7 P h hexp hr F _ _ (λ _=>W)
  (DO _ s (Nat.le_succ t)) iE
 ·calc
   _<=∑v∈jE (eE P F W) s t,((cx F v).card:ℝ):=by exact_mod_cast uD P (jE (eE P F W) s t) F
   _<=∑_v∈jE (eE P F W) s t,h/4:=aK (λ v _=>hF v)
   _=_:=by simp;ring
 ·exact λ _ _=>hW
 ·intro v hv w _ hadj JV hw;have Xt:=aL.mp (MF P F W s hs t) hv;exact KH _ s v w t hv ⟨hadj,JV,Xt,hw⟩
lemma q9 (P:SimpleGraph V) [DecidableRel P.Adj]
  (h:ℝ) (hh:0<h) (hexp:cW P h) (hr:2<=card V)
  (F:Finset (Sym2 V)) (W:Finset V) (s:V) (hs:s∉W)
  (hF:∀v,((cx F v).card:ℝ)<=h/4)
  (hW:(W.card:ℝ)<=h/4):(card V:ℝ)/2<(jE (eE P F W) s (jG (card V) h)).card:=by
 have Rw:(2:ℝ)<=card V:=by exact_mod_cast hr
 have hr0:(0:ℝ)<card V:=by linarith
 let g:=jG (card V) h;let c:ℝ:=1+h/(2*(card V:ℝ));have hc:0<=c:=by dsimp [c];positivity
 by_contra hnot;have JX:=dF hnot;have hpow:∀j≤g,c^j<=(jE (eE P F W) s j).card:=by
  intro j;induction j with
  | zero=>intro _;have H:=cT.mpr ⟨s,Gi (eE P F W) s 0⟩;have H':1<=(jE (eE P F W) s 0).card:=H;simpa using (cq (α:=ℝ)).mpr H'
  | succ j ih=>
    intro hj;have hmono:((jE (eE P F W) s j).card:ℝ)<=(jE (eE P F W) s g).card:=by exact_mod_cast aU (DO (eE P F W) s (by omega:j<=g))
    have iE:=hmono.trans JX;calc
     c^(j+1)=c*c^j:=by rw [pow_succ];ring
     _<=c*(jE (eE P F W) s j).card:=aJ (ih (by omega)) hc
     _<=(jE (eE P F W) s (j+1)).card:=w7 P h hexp hr0 F W s hs hF hW j iE
 have hg:=In (card V) h (by linarith) hh (hexp.le_order P h hr);exact (not_lt_of_ge ((hpow g dH).trans JX)) hg
lemma yv (P:SimpleGraph V) [DecidableRel P.Adj]
  (h:ℝ) (hh:0<h) (hexp:cW P h) (hr:2<=card V)
  (F:Finset (Sym2 V)) (W:Finset V) (s t:V) (hs:s∉W) (ht:t∉W)
  (hF:∀v,((cx F v).card:ℝ)<=h/4)
  (hW:(W.card:ℝ)<=h/4):∃q:(eE P F W).Walk s t,q.IsPath/\q.length<=2*jG (card V) h:=by
 classical
 let g:=jG (card V) h;let B₁:=jE (eE P F W) s g;let B₂:=jE (eE P F W) t g;have h₁:=q9 P h hh hexp hr F W s hs hF hW;have h₂:=q9 P h hh hexp hr F W t ht hF hW;have TQ:(B₁∩B₂).Nonempty:=by
  apply cT.mp;have hc:=card_union_add_card_inter B₁ B₂;have hu:=e4 (B₁∪B₂);have hsum:(card V:ℝ)<(B₁.card:ℝ)+(B₂.card:ℝ):=by dsimp [B₁,B₂,g];linarith
  have Z6:card V<B₁.card+B₂.card:=by exact_mod_cast hsum
  omega
 obtain ⟨v,hv⟩:=TQ;obtain ⟨p₁,hp₁⟩:=(oy _ s v g).mp (dD.mp hv).1;obtain ⟨p₂,hp₂⟩:=(oy _ t v g).mp (dD.mp hv).2;let w:=p₁.append p₂.reverse;refine ⟨w.bypass,w.bypass_isPath,w.length_bypass_le_length.trans ?_⟩;dsimp [w];simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse];omega
lemma uM (r h:ℝ):2*jG r h<=dQ r h:=by dsimp [dQ];exact Nat.le_mul_of_pos_right _ (by omega)
lemma C3 (r h:ℝ) (hr:1<=r) (hh:0<h):1<=dQ r h/\r<=(dQ r h:ℝ)*h:=by
 have Xu:0<Real.log 2:=kO (by norm_num);have kI:1<=Real.logb 2 (2*r):=by rw [Real.logb];apply (e3 Xu).mpr;simpa using Real.log_le_log (by norm_num:(0:ℝ)<2) (by linarith:2<=2*r)
 have hg:8*(r/h)*Real.logb 2 (2*r)<=(jG r h:ℝ):=Nat.le_ceil _;have aaM:8*r<=(jG r h:ℝ)*h:=by
  calc
   8*r=(8*(r/h))*h:=by field_simp
   _<=(8*(r/h)*Real.logb 2 (2*r))*h:=by apply aY _ hh.le;simpa using aJ kI (show 0<=8*(r/h) by positivity)
   _<=(jG r h:ℝ)*h:=aY hg hh.le
 have Z7:0<jG r h:=by
  have Xv:(0:ℝ)<jG r h:=by nlinarith
  exact_mod_cast Xv
 have V9:jG r h<=dQ r h:=(by omega:jG r h<=2*jG r h).trans (uM r h);refine ⟨by omega,?_⟩;have Z8:(jG r h:ℝ)<=dQ r h:=by exact_mod_cast V9
 nlinarith
lemma JY (L k b z h r:ℝ) (hL:1<=L) (hk:1<=k)
  (hb:1<=b) (hz:0<=z) (hh:0<h) (aaN:0<=r)
  (ER:r<=L*h) (oj:64*(L^2*(k+b)+z)<=h):h/8+2+k<=h/4/\z+b*L<=h/8/\64*L*k*r<=h^2:=by
 have Xw:0<=L:=by linarith
 have RL:0<=k:=by linarith
 have RQ:0<=b:=by linarith
 have Xx:1<=L^2:=one_le_pow₀ hL;have Wa:L<=L^2:=by nlinarith
 have G3:64*(k+b)<=h:=by
  calc
   _<=64*(L^2*(k+b)+z):=by nlinarith [aY Xx (by linarith:0<=k+b)]
   _<=_:=oj
 have aaO:64*(b*L+z)<=h:=by
  calc
   _<=64*(L^2*(k+b)+z):=by nlinarith [aJ Wa RQ,bZ (iH L) RL]
   _<=_:=oj
 have Xy:64*L^2*k<=h:=by nlinarith [bZ (iH L) RQ]
 refine ⟨by linarith,by linarith,?_⟩;calc
  64*L*k*r<=64*L*k*(L*h):=aJ ER (by positivity)
  _=(64*L^2*k)*h:=by ring
  _<=h*h:=aY Xy hh.le
  _=h^2:=by ring
noncomputable def qf (F:Finset (Sym2 V)) (h:ℝ):Finset V:=by
 classical
 exact univ.filter (λ v=>h/8<=((cx F v).card:ℝ))
lemma Gj (F:Finset (Sym2 V)) (h:ℝ) (hh:0<h)
  (hF:128*(F.card:ℝ)<=h^2):(qf F h).card<=h/8:=by
 classical
 have hs:h/8*(qf F h).card<=∑v:V,((cx F v).card:ℝ):=by
  calc
   _=∑_v∈qf F h,h/8:=by simp [bK]
   _<=∑v∈qf F h,((cx F v).card:ℝ):=aK (λ v hv=>(aD.mp hv).2)
   _<=_:=jr (gS _) (by intros;positivity)
 have hsum:(∑v:V,((cx F v).card:ℝ))<=2*(F.card:ℝ):=by exact_mod_cast C2 F
 nlinarith
def cE {P:SimpleGraph V} {s t:V} (q:P.Walk s t):Finset V:=q.support.toFinset\{s,t}
lemma C4 {V:Type} [aP:Fintype V] [aO:DecidableEq V] {P:SimpleGraph V} {s t:V} (q:P.Walk s t):(cE q).card<=q.length:=by
 have hp:=oG q.support;rw [q.length_support] at hp;have Lv:s∈q.support.toFinset∩({s,t}:Finset V):=by simp
 have hint:=cT.mpr ⟨s,Lv⟩;have hd:=card_sdiff_add_card_inter q.support.toFinset ({s,t}:Finset V);dsimp [cE];omega
lemma KI {V:Type} [aP:Fintype V] [aO:DecidableEq V] (P:SimpleGraph V) (F:Finset (Sym2 V)) (W:Finset V):eE P F W<=P:=λ _ _ h=>h.1
lemma D5 (P:SimpleGraph V) (F:Finset (Sym2 V)) (W:Finset V)
  {s t:V} (q:(eE P F W).Walk s t) (hs:s∉W):Disjoint q.support.toFinset W:=by
 apply aL.mpr;intro v hv;exact A4 P F W (q.takeUntil v (bw.mp hv)) hs
lemma Gk {V:Type} [aP:Fintype V] [aO:DecidableEq V] (P:SimpleGraph V) (F:Finset (Sym2 V)) (W:Finset V)
  {s t:V} (q:(eE P F W).Walk s t):Disjoint q.edges.toFinset F:=by
 apply aL.mpr;intro e he;induction e using i8 with
 | hf v w=>exact (q.adj_of_mem_edges (bw.mp he)).2.1
lemma pJ (P:SimpleGraph V) [DecidableRel P.Adj]
  (h:ℝ) (hh:0<h) (hexp:cW P h) (hr:2<=card V)
  (F:Finset (Sym2 V)) (W:Finset V) (s t:V) (hs:s∉W) (ht:t∉W)
  (hF:∀v,((cx F v).card:ℝ)<=h/4)
  (hW:(W.card:ℝ)<=h/4):∃q:P.Walk s t,q.IsPath/\q.length<=dQ (card V) h/\Disjoint q.edges.toFinset F/\Disjoint q.support.toFinset W:=by
 obtain ⟨q,hp,hl⟩:=yv P h hh hexp hr F W s t hs ht hF hW;refine ⟨q.mapLe (KI P F W),hp.mapLe _,?_,?_,?_⟩
 ·simpa using hl.trans (uM (card V) h)
 ·simpa using Gk P F W q
 ·simpa using D5 P F W q hs
lemma D6 {P:SimpleGraph V} {s t:V} (q:P.Walk s t)
  (hp:q.IsPath) (F:Finset (Sym2 V)) (h:ℝ) (load:V->ℕ)
  (i6:∀v,((cx F v).card:ℝ)<=h/8+2+load v)
  (xM:Disjoint q.support.toFinset (qf F h\{s,t})) (v:V):((cx (F∪q.edges.toFinset) v).card:ℝ)<=h/8+2+load v+(if v=s\/v=t then 1 else 0):=by
 classical
 have hadd:((cx (F∪q.edges.toFinset) v).card:ℝ)<=(cx F v).card+(cx q.edges.toFinset v).card:=by exact_mod_cast q8 F q.edges.toFinset v
 by_cases hv:v=s\/v=t
 ·rw [ej hv]
  have Xz:(cx q.edges.toFinset v).card<=1:=by
   rcases hv with rfl | rfl
   ·exact nY P q hp
   ·exact qI P q hp
  have hq:((cx q.edges.toFinset v).card:ℝ)<=1:=by exact_mod_cast Xz
  linarith [i6 v]
 ·rw [if_neg hv]
  by_cases hmem:v∈q.support
  ·have hns:v∉qf F h:=by
    intro Wb;apply aL.mp xM (bw.mpr hmem);exact aS.mpr ⟨Wb,by simpa using hv⟩
   have iE:((cx F v).card:ℝ)<h/8:=by simpa [qf] using hns
   have hq:((cx q.edges.toFinset v).card:ℝ)<=2:=by exact_mod_cast y9 P q hp v
   have:(0:ℝ)<=load v:=by positivity
   linarith
  ·rw [og P q hmem] at hadd;simp only [Finset.card_empty,g3,fq] at hadd;linarith [i6 v]
section Pe
variable {I T:Type} [Fintype I] [DecidableEq I] [DecidableEq T]
variable {P:SimpleGraph V} {x y:I->V}
def b7 (A:Finset I) (x y:I->V) (v:V):ℕ:=(A.filter (λ i=>x i=v\/y i=v)).card
lemma Gm {V:Type} [aP:Fintype V] [aO:DecidableEq V] {I:Type} [kq:Fintype I] [o6:DecidableEq I] {A B:Finset I} (wU:A⊆B) (x y:I->V) (v:V):b7 A x y v<=b7 B x y v:=aU (filter_subset_filter _ wU)
lemma D7 {V:Type} [aP:Fintype V] [aO:DecidableEq V] {I:Type} [kq:Fintype I] [o6:DecidableEq I] (A:Finset I) (i:I) (hi:i∉A) (x y:I->V) (v:V):b7 (insert i A) x y v=b7 A x y v+(if v=x i\/v=y i then 1 else 0):=by
 classical
 by_cases hv:v=x i\/v=y i
 ·have Io:x i=v\/y i=v:=by simpa [gH] using hv
  simp [b7,po,hv,Io,hi]
 ·have Io:¬(x i=v\/y i=v):=by simpa [gH] using hv
  simp [b7,po,hv,Io]
lemma zP {V:Type} [aP:Fintype V] [aO:DecidableEq V] {I:Type} [kq:Fintype I] [o6:DecidableEq I] (A:Finset I) (x y:I->V) (hxy:∀i∈A,x i≠y i):∑v:V,b7 A x y v=2*A.card:=by
 classical
 simp only [b7,cV,ck];rw [gD];have heq:∀i∈A,(∑v:V,if x i=v\/y i=v then 1 else 0)=2:=by
  intro i hi;have hf:(univ.filter λ v=>x i=v\/y i=v)=({x i,y i}:Finset V):=by ext v;simp [gH]
  have hc:({x i,y i}:Finset V).card=2:=by simp [hxy i hi]
  rw [<-hc,<-hf,cV,ck]
 calc
  _=∑_i∈A,2:=cZ rfl heq
  _=_:=by simp [bK]
noncomputable def ro (A:Finset I) (q:∀i,P.Walk (x i) (y i)):Finset (Sym2 V):=A.biUnion (λ i=>(q i).edges.toFinset)
lemma Gn {V:Type} [aP:Fintype V] [aO:DecidableEq V] {I:Type} [kq:Fintype I] [o6:DecidableEq I] {P:SimpleGraph V} {x:I->V} {y:I->V} (A:Finset I) (q:∀i,P.Walk (x i) (y i)) (L:ℕ)
  (hq:∀i∈A,(q i).length<=L):(ro A q).card<=L*A.card:=by
 calc
  _<=∑i∈A,(q i).edges.toFinset.card:=c5
  _<=∑_i∈A,L:=aK (λ i hi=>by have hc:=oG (q i).edges;simpa using hc.trans (by simpa using hq i hi))
  _=_:=by simp [bK]
lemma Ay {V:Type} [aP:Fintype V] [aO:DecidableEq V] {I:Type} [kq:Fintype I] [o6:DecidableEq I] {P:SimpleGraph V} {x:I->V} {y:I->V} (A:Finset I) (i:I) (hi:i∉A)
  (q:∀j,P.Walk (x j) (y j)) (p:P.Walk (x i) (y i)):ro (insert i A) (Function.update q i p)=ro A q∪p.edges.toFinset:=by
 classical
 rw [ro,biUnion_insert];simp only [Function.update_self];rw [union_comm];congr 1;apply biUnion_congr rfl;intro j hj;have GO:j≠i:=by intro h;exact hi (h▸hj)
 rw [Function.update_of_ne GO]
noncomputable def vY (A:Finset I) (q:∀j,P.Walk (x j) (y j))
  (i4:I->T) (i:I):Finset V:=(A.filter (λ j=>i4 j=i4 i)).biUnion (λ j=>cE (q j))
lemma C5 {V:Type} [aP:Fintype V] [aO:DecidableEq V] {I:Type} {T:Type} [o6:Fintype I] [O5:DecidableEq I] [O6:DecidableEq T] {P:SimpleGraph V} {x:I->V} {y:I->V} (A:Finset I) (q:∀j,P.Walk (x j) (y j))
  (i4:I->T) (i:I) (L:ℕ) (b:ℝ)
  (hq:∀j∈A,(q j).length<=L)
  (hb:((univ.filter (λ j=>i4 j=i4 i)).card:ℝ)<=b):((vY A q i4 i).card:ℝ)<=b*L:=by
 have hc:(vY A q i4 i).card<=L*(A.filter (λ j=>i4 j=i4 i)).card:=by
  calc
   _<=∑j∈A.filter (λ j=>i4 j=i4 i),(cE (q j)).card:=c5
   _<=∑_j∈A.filter (λ j=>i4 j=i4 i),L:=aK (λ j hj=>(C4 (q j)).trans (hq j (aD.mp hj).1))
   _=_:=by simp [bK]
 have lN:((A.filter (λ j=>i4 j=i4 i)).card:ℝ)<=b:=by apply dY _ hb;exact_mod_cast aU (filter_subset_filter _ (gS A))
 have hcR:((vY A q i4 i).card:ℝ)<=(L:ℝ)*(A.filter (λ j=>i4 j=i4 i)).card:=by exact_mod_cast hc
 calc
  _<=(L:ℝ)*b:=hcR.trans (aJ lN (by positivity))
  _=_:=bK _ _
structure KJ (P:SimpleGraph V) (x y:I->V) (i4:I->T)
  (Z:I->Finset V) (L:ℕ) (h:ℝ) (A:Finset I)
  (q:∀i,P.Walk (x i) (y i)):Prop where
 simple:∀i∈A,(q i).IsPath
 short:∀i∈A,(q i).length<=L
 uN:∀i∈A,Disjoint (cE (q i)) (Z i)
 DP:∀i∈A,∀j∈A,i≠j->Disjoint (q i).edges.toFinset (q j).edges.toFinset
 DQ:∀i∈A,∀j∈A,i≠j->i4 i=i4 j->Disjoint (cE (q i)) (cE (q j))
 degree:∀v,((cx (ro A q) v).card:ℝ)<=h/8+2+b7 A x y v
lemma M8 (P:SimpleGraph V) [DecidableRel P.Adj]
  (h:ℝ) (hh:0<h) (hexp:cW P h) (hr:2<=Fintype.card V)
  (x y:I->V) (hxy:∀i,x i≠y i) (i4:I->T) (Z:I->Finset V)
  (k b z:ℝ) (hk:1<=k) (hb:1<=b) (hz:0<=z)
  (lG:∀v,(b7 Finset.univ x y v:ℝ)<=k)
  (C6:∀i,((Finset.univ.filter (λ j=>i4 j=i4 i)).card:ℝ)<=b)
  (hZ:∀i,((Z i).card:ℝ)<=z)
  (oj:64*((dQ (Fintype.card V) h:ℝ)^2*(k+b)+z)<=h):∃q:∀i,P.Walk (x i) (y i),(∀i,(q i).IsPath/\(q i).length<=dQ (Fintype.card V) h/\Disjoint (cE (q i)) (Z i))/\
   (∀i j,i≠j->Disjoint (q i).edges.toFinset (q j).edges.toFinset)/\(∀i j,i≠j->i4 i=i4 j->Disjoint (cE (q i)) (cE (q j))):=by
 classical
 let L:=dQ (Fintype.card V) h;have Rw:(2:ℝ)<=Fintype.card V:=by exact_mod_cast hr
 obtain ⟨hL,ER⟩:=C3 (Fintype.card V) h (by linarith) hh;have XA:(1:ℝ)<=L:=by exact_mod_cast hL
 obtain ⟨TR,Ru,NQ⟩:=JY L k b z h (Fintype.card V)
  XA hk hb hz hh (by positivity) ER oj
 have RR:∀(A:Finset I) v,(b7 A x y v:ℝ)<=k:=by
  intro A v;have hm:(b7 A x y v:ℝ)<=b7 Finset.univ x y v:=by exact_mod_cast Gm (gS A) x y v
  exact hm.trans (lG v)
 have Lx:2*(Fintype.card I:ℝ)<=k*Fintype.card V:=by
  have heq:=zP Finset.univ x y (λ i _=>hxy i);have heqR:(∑v:V,(b7 Finset.univ x y v:ℝ))=2*Fintype.card I:=by exact_mod_cast heq
  rw [<-heqR];calc
   _<=∑_v:V,k:=aK (λ v _=>lG v)
   _=_:=by simp [bK]
 have hdefault:∀i,∃p:P.Walk (x i) (y i),p.IsPath:=by
  intro i;obtain ⟨p,hp,_⟩:=pJ P h hh hexp hr ∅ ∅ (x i) (y i)
   (by simp) (by simp) (by intro v;simp [cx];positivity) (by simp;positivity)
  exact ⟨p,hp⟩
 choose MG RU using hdefault;have Ly:∀A:Finset I,∃q:∀i,P.Walk (x i) (y i),KJ P x y i4 Z L h A q:=by
  intro A;induction A using o9 with
  | empty=>
    refine ⟨MG,?_⟩;constructor
    ·simp
    ·simp
    ·simp
    ·simp
    ·simp
    ·intro v;simp only [ro,Finset.biUnion_empty,cx,Finset.filter_empty,Finset.card_empty,g3,b7,fq];linarith
  | @insert i A hi ih=>
    obtain ⟨q,hq⟩:=ih;let F:=ro A q;let S:=qf F h;let B:=vY A q i4 i;let W:=(S∪Z i∪B)\{x i,y i};have RV:128*(F.card:ℝ)<=h^2:=by
     have hc:(F.card:ℝ)<=(L:ℝ)*A.card:=by exact_mod_cast Gn A q L hq.short
     have ha:(A.card:ℝ)<=Fintype.card I:=by exact_mod_cast e4 A
     have u6:2*(A.card:ℝ)<=k*Fintype.card V:=by linarith
     have Z9:=aJ u6 (show 0<=(L:ℝ) by positivity);nlinarith [NQ]
    have hS:(S.card:ℝ)<=h/8:=Gj F h hh RV;have hB:(B.card:ℝ)<=b*L:=C5 A q i4 i L b hq.short (C6 i);have hW:(W.card:ℝ)<=h/4:=by
     have hc:W.card<=S.card+(Z i).card+B.card:=(aU lg).trans ((dG _ _).trans
       (l5 (dG _ _) _))
     have hcR:(W.card:ℝ)<=(S.card:ℝ)+(Z i).card+B.card:=by exact_mod_cast hc
     linarith [hZ i]
    have Pf:∀v,((cx F v).card:ℝ)<=h/4:=by intro v;have hd:=hq.degree v;have hl:=RR A v;dsimp [F];linarith
    obtain ⟨p,hp,hpL,XB,RW⟩:=pJ P h hh hexp hr F W (x i) (y i)
     (by simp [W]) (by simp [W]) Pf hW
    have XC:Disjoint (cE p) (Z i):=by apply aL.mpr;intro v hv XD;obtain ⟨M9,Lz⟩:=aS.mp hv;apply aL.mp RW M9;exact aS.mpr ⟨cQ _ (ee _ XD),Lz⟩
    have Nb:Disjoint p.support.toFinset (qf F h\{x i,y i}):=by apply aL.mpr;intro v hv XE;obtain ⟨hs,he⟩:=aS.mp XE;apply aL.mp RW hv;exact aS.mpr ⟨cQ _ (cQ _ hs),he⟩
    have OA:∀j∈A,Disjoint p.edges.toFinset (q j).edges.toFinset:=by intro j hj;apply aL.mpr;intro e XF heq;exact aL.mp XB XF (bR.mpr ⟨j,hj,heq⟩)
    have OB:∀j∈A,i4 i=i4 j->Disjoint (cE p) (cE (q j)):=by intro j hj htm;apply aL.mpr;intro v M9 PX;obtain ⟨Wd,Lz⟩:=aS.mp M9;apply aL.mp RW Wd;apply aS.mpr;refine ⟨ee _ ?_,Lz⟩;exact bR.mpr ⟨j,aD.mpr ⟨hj,htm.symm⟩,PX⟩
    let q':=Function.update q i p;have zc:q' i=p:=Function.update_self i p q;have tj:∀j∈A,q' j=q j:=by intro j hj;apply Function.update_of_ne;intro GO;exact hi (GO▸hj)
    refine ⟨q',?_⟩;constructor
    ·intro j hj
     rcases bU.mp hj with rfl | hj
     ·simpa only [zc] using hp
     ·simpa only [tj j hj] using hq.simple j hj
    ·intro j hj
     rcases bU.mp hj with rfl | hj
     ·simpa only [zc] using hpL
     ·simpa only [tj j hj] using hq.short j hj
    ·intro j hj
     rcases bU.mp hj with rfl | hj
     ·simpa only [zc] using XC
     ·simpa only [tj j hj] using hq.uN j hj
    ·intro j hj k hk zQ
     rcases bU.mp hj with rfl | B1
     ·have ES:k∈A:=(bU.mp hk).resolve_left (Ne.symm zQ);simpa only [zc,tj k ES] using OA k ES
     ·rcases bU.mp hk with rfl | ES
      ·simpa only [zc,tj j B1] using (OA j B1).symm
      ·simpa only [tj j B1,tj k ES] using hq.DP j B1 k ES zQ
    ·intro j hj k hk zQ htm
     rcases bU.mp hj with rfl | B1
     ·have ES:k∈A:=(bU.mp hk).resolve_left (Ne.symm zQ);simpa only [zc,tj k ES] using OB k ES htm
     ·rcases bU.mp hk with rfl | ES
      ·simpa only [zc,tj j B1] using (OB j B1 htm.symm).symm
      ·simpa only [tj j B1,tj k ES] using hq.DQ j B1 k ES zQ htm
    ·intro v
     have heq:ro (insert i A) q'=F∪p.edges.toFinset:=Ay A i hi q p;rw [heq];have hu:=D6 p hp F h (b7 A x y) hq.degree Nb v;have QS:(b7 (insert i A) x y v:ℝ)=b7 A x y v+(if v=x i\/v=y i then (1:ℝ) else 0):=by rw [D7 A i hi];split_ifs<;>simp
     rw [QS];simpa only [add_assoc] using hu
 obtain ⟨q,hq⟩:=Ly Finset.univ;exact ⟨q,λ i=>⟨hq.simple i (by simp),hq.short i (by simp),hq.uN i (by simp)⟩,λ i j hij=>hq.DP i (by simp) j (by simp) hij,λ i j hij htm=>hq.DQ i (by simp) j (by simp) hij htm⟩
end Pe
end af
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX gu gX iN iO i7
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af
open aR.af.aV
open aR.af.Splitting
section
open Real Filter Asymptotics
lemma C7 (r h:ℝ) (hr:2<=r) (hh:0<h) (PV:h<=r):(dQ r h:ℝ)<=108*(r/h)*(logb 2 r)^2:=by
 have hr0:0< r:=by linarith
 have hl:1<=logb 2 r:=by
  simpa using dL (by norm_num:(1:ℝ)<2)
   (by norm_num:(0:ℝ)<2) hr
 have hR:1<=r/h:=(e3 hh).mpr (by simpa using PV);have kI:logb 2 (2*r)=1+logb 2 r:=by rw [Real.logb_mul (by norm_num) hr0.ne'];norm_num
 have hg:=nV (show 0<=8*(r/h)*logb 2 (2*r) by rw [kI];positivity);have hd:=nV (show 0<=logb 2 r by linarith);change (jG r h:ℝ)<8*(r/h)*logb 2 (2*r)+1 at hg;change (zO r:ℝ)<logb 2 r+1 at hd;rw [kI] at hg;have F6:1<=(r/h)*logb 2 r:=by nlinarith [bZ (sub_nonneg.mpr hR) (sub_nonneg.mpr hl)]
 have hg':(jG r h:ℝ)<=18*(r/h)*logb 2 r:=by nlinarith
 have GR:(1+zO r:ℝ)<=3*logb 2 r:=by linarith
 have hm:=iJ hg' GR (by positivity) (by positivity);dsimp [dQ];push_cast;nlinarith
lemma tq (ε:ℝ) (hε:0<ε):∀ᶠ D:ℝ in atTop,logb 2 D <=D^ε:=by have ho:=(o8 hε).const_mul_left (1/log 2);filter_upwards [ho.eventuallyLE,eventually_ge_atTop (1:ℝ)] with D hD h1;simpa [Real.logb,gq,bK,kg,gk (nU h1),gk (fG (by linarith) ε),abs_of_pos (show 0<(log 2)⁻¹ by positivity),abs_of_pos (kO (by norm_num:(1:ℝ)<2))] using hD
lemma lO (C ε:ℝ) (hε:0<ε):∀ᶠ D:ℝ in atTop,C<=D^ε:=(nT hε).eventually (eventually_ge_atTop C)
lemma ki (C α β:ℝ) (hab:α<β):∀ᶠ D:ℝ in atTop,C*D^α<=D^β:=by
 filter_upwards [lO C (β-α) (by linarith),eventually_gt_atTop (0:ℝ)] with D hc hD;calc
  C*D^α<=D^(β-α)*D^α:=aY hc (fG hD.le _)
  _=D^β:=by rw [<-c8 hD];congr 1;ring
lemma sC (c β γ δ:ℝ) (hc:0<c) (hβ:0<β)
  (PM:0<δ):∀ᶠ D:ℝ in atTop,∀r:ℝ,2<=r->r<=D^β->c*D^γ<=r->(dQ r (c*D^γ):ℝ)<=D^(β-γ+δ):=by
 filter_upwards [tq (δ/4) (by positivity),lO (108*β^2/c) (δ/2) (by positivity),eventually_gt_atTop (1:ℝ)] with D kI hconst hD r hr Kq PV;have hD0:0<D:=by linarith
 have RX:0<D^γ:=d6 hD0 _;have hden:0<c*D^γ:=f7 hc RX;have TT:0<=logb 2 r:=(g4 (by norm_num) (by linarith)).le;have TU:logb 2 r<=β*D^(δ/4):=by
  have hh:=dL (by norm_num:(1:ℝ)<2)
   (by linarith:0< r) Kq
  rw [jH hD0] at hh;exact hh.trans (aJ kI hβ.le)
 have BX:r/(c*D^γ)<=D^(β-γ)/c:=by
  calc
   _<=D^β/(c*D^γ):=e5 Kq hden.le
   _=_:=by rw [gT hD0];ring
 have aaP:(logb 2 r)^2<=β^2*D^(δ/2):=by
  calc
   _<=(β*D^(δ/4))^2:=nZ TT TU 2
   _=_:=by rw [mul_pow,<-lA hD0.le];congr 2;ring
 calc
  (dQ r (c*D^γ):ℝ)<=108*(r/(c*D^γ))*(logb 2 r)^2:=C7 r (c*D^γ) hr hden PV
  _<=108*(D^(β-γ)/c)*(β^2*D^(δ/2)):=by gcongr
  _=(108*β^2/c)*D^(β-γ+δ/2):=by rw [c8 hD0];ring
  _<=D^(δ/2)*D^(β-γ+δ/2):=aY hconst (fG hD0.le _)
  _=D^(β-γ+δ):=by rw [<-c8 hD0];congr 1;ring
lemma C8:∃dN:ℝ,1<dN/\∀D≥dN,∀r:ℝ,D^(9/10:ℝ)<=r->r<=D^(51/50:ℝ)->2<=r/\64*((dQ r (D^(9/10:ℝ)/4):ℝ)^2*(D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ))<=D^(9/10:ℝ)/4:=by
 have A5:∀ᶠ D:ℝ in atTop,∀r:ℝ,D^(9/10:ℝ)<=r->r<=D^(51/50:ℝ)->2<=r/\64*((dQ r (D^(9/10:ℝ)/4):ℝ)^2*(D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ))<=D^(9/10:ℝ)/4:=by
  filter_upwards [sC (1/4) (51/50) (9/10) (2/25)
   (by norm_num) (by norm_num) (by norm_num),ki 1024 (7/10) (9/10) (by norm_num),lO 2 (9/10) (by norm_num),eventually_gt_atTop (1:ℝ)] with D hlen jF htwo hD r hr Kq
  have hD0:0<D:=by linarith
  have PN:2<=r:=htwo.trans hr;have hh:(1/4)*D^(9/10:ℝ)<=r:=by have aaQ:=fG hD0.le (9/10:ℝ);linarith
  have hL:=hlen r PN Kq hh;norm_num at hL;have aaR:(dQ r (D^(9/10:ℝ)/4):ℝ)<=D^(1/5:ℝ):=by convert hL using 1;ring_nf
  have iE:D^(1/100:ℝ)<=D^(3/10:ℝ):=g5 hD.le (by norm_num);have XG:D^(3/10:ℝ)<=D^(7/10:ℝ):=g5 hD.le (by norm_num);have F6:(dQ r (D^(9/10:ℝ)/4):ℝ)^2*(D^(1/100:ℝ)+D^(3/10:ℝ))<=2*D^(7/10:ℝ):=by
   calc
    _<=(D^(1/5:ℝ))^2*(2*D^(3/10:ℝ)):=by gcongr;linarith
    _=_:=by rw [<-lA hD0.le];norm_num;rw [mul_left_comm,<-c8 hD0];norm_num
  refine ⟨PN,?_⟩;nlinarith only [F6,XG,jF]
 obtain ⟨A,hA⟩:=eventually_atTop.mp A5;refine ⟨max A 2,dZ (by norm_num) (bC _ _),?_⟩;intro D hD;exact hA D ((b6 _ _).trans hD)
lemma wR (c p:ℝ) (hc:0<c) (hp:0<p):∀ᶠ D:ℝ in atTop,∀r:ℝ,0<=r->r<=D^(51/50:ℝ)->(⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊:ℝ)<=D^(13/100:ℝ):=by
 filter_upwards [ki (8/(p*c)+1) (3/25) (13/100) (by norm_num),eventually_gt_atTop (1:ℝ)] with D hbound hD r hr Kq;have hD0:0<D:=by linarith
 have hden:0<p*(c*D^(9/10:ℝ)):=by positivity
 have NR:1<=D^(3/25:ℝ):=jv hD.le (by norm_num);have hx:8*r/(p*(c*D^(9/10:ℝ)))<=(8/(p*c))*D^(3/25:ℝ):=by
  calc
   _<=8*D^(51/50:ℝ)/(p*(c*D^(9/10:ℝ))):=by gcongr
   _=_:=by
    have heq:D^(3/25:ℝ)=D^(51/50:ℝ)/D^(9/10:ℝ):=by rw [<-gT hD0];norm_num
    rw [heq];ring
 have NS:=nV (show 0<=8*r/(p*(c*D^(9/10:ℝ))) by positivity);nlinarith only [hx,NS,NR,hbound]
lemma Bn (c p:ℝ) (hc:0<c) (hp:0<p):∃dN:ℝ,1<dN/\∀D≥dN,∀r yy:ℝ,0<=r->r<=D^(51/50:ℝ)->2<=yy->yy<=r->D^(37/50:ℝ)<=yy->64*((dQ yy (D^(37/50:ℝ)):ℝ)^2*((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊:ℝ)+1))<=D^(37/50:ℝ):=by
 have A5:∀ᶠ D:ℝ in atTop,∀r yy:ℝ,0<=r->r<=D^(51/50:ℝ)->2<=yy->yy<=r->D^(37/50:ℝ)<=yy->64*((dQ yy (D^(37/50:ℝ)):ℝ)^2*((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊:ℝ)+1))<=D^(37/50:ℝ):=by
  filter_upwards [sC 1 (51/50) (37/50) (1/100)
   (by norm_num) (by norm_num) (by norm_num),wR c p hc hp,ki 128 (71/100) (37/50) (by norm_num),eventually_gt_atTop (1:ℝ)] with D hlen rG jF hD r yy hr Kq We Wf Wg
  have hD0:0<D:=by linarith
  have hL:=hlen yy We (Wf.trans Kq) (by simpa using Wg);norm_num at hL;have hk:=rG r hr Kq;have NR:1<=D^(13/100:ℝ):=jv hD.le (by norm_num);have F6:(dQ yy (D^(37/50:ℝ)):ℝ)^2*((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊:ℝ)+1)<=2*D^(71/100:ℝ):=by
   calc
    _<=(D^(29/100:ℝ))^2*(2*D^(13/100:ℝ)):=by gcongr;linarith
    _=_:=by rw [<-lA hD0.le];norm_num;rw [mul_left_comm,<-c8 hD0];norm_num
  nlinarith only [F6,jF]
 obtain ⟨A,hA⟩:=eventually_atTop.mp A5;refine ⟨max A 2,dZ (by norm_num) (bC _ _),?_⟩;intro D hD;exact hA D ((b6 _ _).trans hD)
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
lemma r9 {V:Type} [aP:Fintype V] [aO:DecidableEq V] (W:Finset V) (U:Finset (W:Set V)):Uᶜ.image Subtype.val=W\U.image Subtype.val:=by
 ext v;simp only [bk,cU,aS];constructor
 ·rintro ⟨x,hx,rfl⟩;refine ⟨x.property,?_⟩;rintro ⟨y,hy,he⟩;exact hx (aZ he▸hy)
 ·rintro ⟨hv,RB⟩;refine ⟨⟨v,hv⟩,?_,rfl⟩;intro hx;exact RB ⟨⟨v,hv⟩,hx,rfl⟩
lemma uk (P:SimpleGraph V) [DecidableRel P.Adj]
  (W:Finset V) (U:Finset (W:Set V)):(((P.induce (W:Set V)).interedges U Uᶜ).card:ℝ)=((P.interedges (U.image Subtype.val) (W\U.image Subtype.val)).card:ℝ):=by
 classical
 let f:↥(W:Set V)×↥(W:Set V)->V×V:=λ e=>(e.1.val,e.2.val)
 have hf:Function.Injective f:=by
  intro a b h;apply Prod.ext<;>apply aZ
  ·exact aF Prod.fst h
  ·exact aF Prod.snd h
 have heq:((P.induce (W:Set V)).interedges U Uᶜ).image f=P.interedges (U.image Subtype.val) (W\U.image Subtype.val):=by
  rw [<-r9 W U];ext e;simp only [nQ,bk];constructor
  ·rintro ⟨a,⟨ha,hb,hab⟩,rfl⟩;exact ⟨⟨a.1,ha,rfl⟩,⟨a.2,hb,rfl⟩,hab⟩
  ·rintro ⟨⟨x,hx,U1⟩,⟨y,hy,U2⟩,he⟩;refine ⟨(x,y),⟨hx,hy,?_⟩,Prod.ext U1 U2⟩;change P.Adj x.val y.val;simpa only [U1,U2] using he
 rw [<-heq,gI _ hf]
lemma oh (P:SimpleGraph V) [DecidableRel P.Adj]
  (W:Finset V) (h:ℝ) (hexp:b9 P W h):cW (P.induce (W:Set V)) h:=by
 classical
 intro U;have hsub:U.image Subtype.val⊆W:=by rintro v hv;obtain ⟨a,ha,rfl⟩:=bk.mp hv;exact a.property
 have h:=hexp (U.image Subtype.val) hsub;have he:W\U.image Subtype.val=Uᶜ.image Subtype.val:=(r9 W U).symm;rw [he] at h;simp only [gI _ dM] at h;rw [uk,he];exact h
lemma D8 {I:Type} [Fintype I]
  (P:SimpleGraph V) [DecidableRel P.Adj]
  (h:ℝ) (hh:0<h) (hexp:cW P h) (hr:2<=card V)
  (x y:I->V) (k:ℝ) (hk:1<=k)
  (lG:∀v,(b7 univ x y v:ℝ)<=k)
  (oj:64*((dQ (card V) h:ℝ)^2*(k+1))<=h):∃q:∀i,P.Walk (x i) (y i),(∀i,(q i).IsPath/\(q i).length<=dQ (card V) h)/\(∀i j,i≠j->Disjoint (q i).edges.toFinset (q j).edges.toFinset):=by
 classical
 let J:={i:I // x i≠y i};have RY (v:V):(b7 univ (λ i:J=>x i.val) (λ i:J=>y i.val) v:ℝ)<=k:=by
  apply dY _ (lG v);exact_mod_cast (show b7 univ (λ i:J=>x i.val)
    (λ i:J=>y i.val) v<=b7 univ x y v from by
   apply gG Subtype.val
   ·intro a ha;exact aD.mpr ⟨aQ _,(aD.mp ha).2⟩
   ·intro a _ b _ hab;exact aZ hab)
 obtain ⟨q,hq,hd,_⟩:=M8 P h hh hexp hr
  (λ i:J=>x i.val) (λ i:J=>y i.val) (λ i=>i.property)
  (λ i:J=>i) (λ _=>∅) k 1 0 hk (by norm_num) (by norm_num) RY
  (by
   intro i;have he:(univ.filter (λ j:J=>j=i))={i}:=by ext j;simp
   rw [he];simp) (by intro i;simp) (by simpa only [fq] using oj)
 let Q:∀i,P.Walk (x i) (y i):=λ i=>
  if hi:x i=y i then (SimpleGraph.Walk.nil:P.Walk (x i) (x i)).copy rfl hi
  else q ⟨i,hi⟩
 refine ⟨Q,?_,?_⟩
 ·intro i
  by_cases hi:x i=y i
  ·simp [Q,hi]
  ·simpa only [Q,dif_neg hi] using ⟨(hq ⟨i,hi⟩).1,(hq ⟨i,hi⟩).2.1⟩
 ·intro i j hij
  by_cases hi:x i=y i
  ·simp [Q,hi]
  by_cases hj:x j=y j
  ·simp [Q,hj]
  simp only [Q,dif_neg hi,dif_neg hj];exact hd ⟨i,hi⟩ ⟨j,hj⟩ (λ he=>hij (aF Subtype.val he))
lemma C9 {I:Type} [Fintype I]
  (G P:SimpleGraph V) [DecidableRel P.Adj] (oe:P<=G)
  (W:Finset V) (h:ℝ) (hh:0<h)
  (hexp:b9 P W h) (hr:2<=W.card)
  (x y:I->V) (hx:∀i,x i∈W) (hy:∀i,y i∈W)
  (k:ℝ) (hk:1<=k)
  (lG:∀v,(b7 univ x y v:ℝ)<=k)
  (oj:64*((dQ W.card h:ℝ)^2*(k+1))<=h):∃q:∀i,G.Walk (x i) (y i),(∀i,(q i).IsPath/\(q i).length<=dQ W.card h/\∀v∈(q i).support,v∈W)/\
   Pairwise (λ i j=>Disjoint (q i).edgeSet (q j).edgeSet):=by
 classical
 let X:I->(W:Set V):=λ i=>⟨x i,hx i⟩
 let Y:I->(W:Set V):=λ i=>⟨y i,hy i⟩
 have hl (v:(W:Set V)):(b7 univ X Y v:ℝ)<=k:=by simpa only [b7,X,Y,Subtype.ext_iff] using lG v.val
 obtain ⟨q,hq,hd⟩:=D8 (P.induce (W:Set V)) h hh
  (oh P W h hexp) (by simpa using hr) X Y k hk hl
  (by simpa using oj)
 let f:(P.induce (W:Set V)) →g G:={toFun:=Subtype.val,map_rel':=λ ha=>oe ha};have hf:Function.Injective f:=dM;have lN:card ↥(W:Set V)=W.card:=eG W;let Q:∀i,G.Walk (x i) (y i):=λ i=>(q i).map f
 refine ⟨Q,?_,?_⟩
 ·intro i
  refine ⟨(hq i).1.map hf,?_,?_⟩
  ·simpa only [Q,l8,lN] using (hq i).2
  ·intro v hv
   have Io:v∈(q i).support.map f:=by simpa only [Q,oH] using hv
   obtain ⟨a,ha,rfl⟩:=bV.mp Io;exact a.property
 ·intro i j hij
  change Disjoint ((q i).map f).edgeSet ((q j).map f).edgeSet;rw [g6,g6];rw [l9 (fI hf)];apply aI.mpr;intro e he he';exact aL.mp (hd i j hij)
   (by simpa using he) (by simpa using he')
lemma zd (c p:ℝ) (hc:0<c) (hp:0<p):∃dN:ℝ,1<dN/\∀D≥dN,∀(V:Type) [Fintype V] [DecidableEq V],∀(G P:SimpleGraph V) [DecidableRel P.Adj],P<=G->∀W:Finset V,b9 P W (D^(37/50:ℝ))->2<=W.card->(card V:ℝ)<=D^(51/50:ℝ)->∀(I:Type) [Fintype I] (x y:I->V),(∀i,x i∈W)->(∀i,y i∈W)->(∀v,b7 univ x y v<=⌈8*(card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊)->
   ∃q:∀i,G.Walk (x i) (y i),(∀i,(q i).IsPath/\(q i).length<=dQ W.card (D^(37/50:ℝ))/\∀v∈(q i).support,v∈W)/\
    Pairwise (λ i j=>Disjoint (q i).edgeSet (q j).edgeSet):=by
 obtain ⟨dN,ko,B2⟩:=Bn c p hc hp;refine ⟨dN,ko,?_⟩;intro D hD V _ _ G P _ oe W hexp hW hr I _ x y hx hy hl;have pT:0<D:=lt_trans (by norm_num) (ko.trans_le hD);have uO:(D^(37/50:ℝ))<=(W.card:ℝ):=by
  simpa using (oh P W _ hexp).le_order (P.induce (W:Set V)) _
   (by simpa using hW)
 have QU:(W.card:ℝ)<=(card V:ℝ):=by exact_mod_cast W.card_le_univ
 have A0:0<(card V:ℝ):=by
  have XH:(2:ℝ)<=W.card:=by exact_mod_cast hW
  linarith
 have hk:1<=(⌈8*(card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊:ℝ):=by have NS:0<⌈8*(card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊:=Nat.ceil_pos.mpr (by positivity);exact_mod_cast NS
 apply C9 G P oe W (D^(37/50:ℝ)) (by positivity) hexp hW
  x y hx hy _ hk (by intro v;exact_mod_cast hl v)
 exact B2 D hD _ _ A0.le hr (by exact_mod_cast hW) QU uO
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma G4 {A:Type bX} {V:Type bY} [Fintype A] (f:A->V) (k:ℕ)
  (h:∀v,card {a // f a=v}<=k):∃p5:A->Fin k,Function.Injective (λ a=>(f a,p5 a)):=by
 classical
 have he:∀v,Nonempty ({a // f a=v} ↪ Fin k):=by intro v;exact Function.Embedding.nonempty_of_card_le (by simpa using h v)
 let e:=λ v=>Classical.choice (he v)
 refine ⟨λ a=>e (f a) ⟨a,rfl⟩,?_⟩;intro a b hab;have hf:f a=f b:=aF Prod.fst hab;have hs:e (f a) ⟨a,rfl⟩=e (f b) ⟨b,rfl⟩:=aF Prod.snd hab;have hσ:(⟨f a,e (f a) ⟨a,rfl⟩⟩:Σ _:V,Fin k)=⟨f b,e (f b) ⟨b,rfl⟩⟩:=Sigma.ext hf (heq_of_eq hs);let E:(Σ v,{a // f a=v}) ↪ (Σ _:V,Fin k):=Function.Embedding.sigmaMap (Function.Embedding.refl V) e;have heq:(⟨f a,⟨a,rfl⟩⟩:Σ v,{a // f a=v})=⟨f b,⟨b,rfl⟩⟩:=E.injective hσ;exact aF (λ z:Σ v,{a // f a=v}=>z.2.val) heq
def gv {I:Type cy} {V:Type cz} (x y:I->V) (a:I×Fin 2):V:=if a.2=0 then x a.1 else y a.1
lemma ze {I:Type cP} {V:Type cL} [Fintype I]
  (x y:I->V) (hne:∀i,x i≠y i)
  (lG:∀v,(univ.filter (λ i=>x i=v\/y i=v)).card<=2):∃p5:I×Fin 2->Fin 2,Function.Injective (λ a=>(gv x y a,p5 a)):=by
 classical
 apply G4;intro v;let f:{a:I×Fin 2 // gv x y a=v}->{i:I // x i=v\/y i=v}:=λ a=>
  ⟨a.val.1,by
   by_cases h0:a.val.2=0
   ·exact Or.inl (by simpa [gv,h0] using a.property)
   ·exact Or.inr (by simpa [gv,h0] using a.property)⟩
 have hf:Function.Injective f:=by
  intro a b hab;apply aZ;have hi:a.val.1=b.val.1:=aF Subtype.val hab;apply Prod.ext hi;by_contra ht;have RZ:(a.val.2=0/\b.val.2≠0)\/(a.val.2≠0/\b.val.2=0):=by
   have ha:=(a.val.2).isLt;have hb:=(b.val.2).isLt;have hne:(a.val.2).val≠(b.val.2).val:=λ h=>ht (Fin.ext h)
   simp only [Fin.ext_iff,Fin.val_zero];omega
  rcases RZ with h | h
  ·have ha:x a.val.1=v:=by simpa [gv,h.1] using a.property
   have hb:y b.val.1=v:=by simpa [gv,h.2] using b.property
   exact hne _ (ha.trans (hi▸hb).symm)
  ·have ha:y a.val.1=v:=by simpa [gv,h.1] using a.property
   have hb:x b.val.1=v:=by simpa [gv,h.2] using b.property
   exact hne _ ((hi▸hb).trans ha.symm)
 exact (Fintype.card_le_of_injective f hf).trans (by simpa only [mg] using lG v)
lemma zR {A:Type c9} {V:Type dW} (S W:Set V)
  (f:A->V) (p5:A->Fin 2) (r:V×Fin 2->V)
  (LA:Function.Injective (λ a=>(f a,p5 a)))
  (vZ:∀a,f a∈S) (XI:∀v∈S,∀t,r (v,t)∈W)
  (hdisj:Disjoint S W) (hr:∀v∈S,r (v,0)≠r (v,1)):Function.Injective (λ a=>s(f a,r (f a,p5 a))):=by
 intro a b hab;rcases jI.mp hab with he | he
 ·have hf:f a=f b:=he.1
  have hh:r (f a,p5 a)=r (f b,p5 b):=he.2;apply LA;apply Prod.ext hf;have TV:Function.Injective (λ t:Fin 2=>r (f a,t)):=by
   intro i j hij;have h0:=hr (f a) (vZ a);fin_cases i<;>fin_cases j
   ·rfl
   ·exact (h0 hij).elim
   ·exact (h0 hij.symm).elim
   ·rfl
  exact TV (by simpa only [hf] using hh)
 ·have hf:f a=r (f b,p5 b):=he.1
  exact False.elim (aI.mp hdisj (vZ a)
   (hf.symm▸XI (f b) (vZ b) (p5 b)))
lemma w8 {A:Type eo} {V:Type d7} [Fintype A] [DecidableEq V]
  (S:Finset V) (f:A->V) (p5:A->Fin 2) (r:V×Fin 2->V)
  (LA:Function.Injective (λ a=>(f a,p5 a)))
  (vZ:∀a,f a∈S) (k:ℕ)
  (rG:∀v,((S ×ˢ univ).filter (λ a=>r a=v)).card<=k):∀v,(univ.filter (λ a=>r (f a,p5 a)=v)).card<=k:=by
 classical
 intro v;apply dY (gG (λ a=>(f a,p5 a)) ?_ ?_) (rG v)
 ·intro a ha;exact mem_filter.mpr ⟨mem_product.mpr ⟨vZ a,mem_univ _⟩,(mem_filter.mp ha).2⟩
 ·intro a _ b _ hab;exact LA hab
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma yA {V I:Type} [Fintype V] [Fintype I]
  [DecidableEq V] (P:SimpleGraph V) (W:Finset V)
  (x y:I->V) (hne:∀i,x i≠y i)
  (PY:∀i,x i∉W) (PZ:∀i,y i∉W)
  (lG:∀v,b7 univ x y v<=2)
  (r:V×Fin 2->V)
  (hr:∀v,v∉W->∀t,r (v,t)∈W/\P.Adj v (r (v,t)))
  (LB:∀v,v∉W->r (v,0)≠r (v,1))
  (k:ℕ) (rG:∀v,((Wᶜ ×ˢ univ).filter (λ z=>r z=v)).card<=k):∃a b:I->V,(∀i,a i∈W/\P.Adj (x i) (a i))/\(∀i,b i∈W/\P.Adj (y i) (b i))/\Function.Injective (λ z:I×Fin 2=>
    if z.2=0 then s(x z.1,a z.1) else s(y z.1,b z.1))/\
   (∀v,b7 univ a b v<=k)/\(∀i,∃t,a i=r (x i,t))/\(∀i,∃t,b i=r (y i,t)):=by
 classical
 obtain ⟨p5,P5⟩:=ze x y hne (λ v=>by convert lG v using 1;congr 1;ext i;simp only [aD,aQ,b5]);let GS:=gv x y;have ho:∀z:I×Fin 2,GS z∉W:=by
  rintro ⟨i,t⟩;by_cases h:t=0
  ·simpa [GS,gv,h] using PY i
  ·simpa [GS,gv,h] using PZ i
 let a:=λ i=>r (x i,p5 (i,0))
 let b:=λ i=>r (y i,p5 (i,1))
 have GU:=zR (Wᶜ:Finset V) W GS p5 r P5
  (λ z=>cU.mpr (ho z))
  (λ v hv t=>(hr v (cU.mp hv) t).1)
  (aI.mpr (λ _ hv hw=>(cU.mp hv) hw))
  (λ v hv=>LB v (cU.mp hv))
 have TW:=w8 Wᶜ GS p5 r P5
  (λ z=>cU.mpr (ho z)) k rG
 refine ⟨a,b,(λ i=>hr _ (PY i) _),(λ i=>hr _ (PZ i) _),?_,?_,?_,?_⟩
 ·have heq:(λ z:I×Fin 2=>
    if z.2=0 then s(x z.1,a z.1) else s(y z.1,b z.1))=(λ z=>s(GS z,r (GS z,p5 z))):=by
   funext z;rcases z with ⟨i,t⟩;fin_cases t<;>simp [GS,gv,a,b]
  rw [heq];exact GU
 ·intro v
  apply dY (gG
   (λ i=>(i,if a i=v then (0:Fin 2) else 1)) ?_ ?_) (TW v)
  ·intro i hi
   have hi':=(aD.mp hi).2;apply aD.mpr;refine ⟨aQ _,?_⟩;by_cases R0:a i=v
   ·simp [R0,GS,gv,a]
   ·have hi1:b i=v:=hi'.resolve_left R0;simpa [R0,GS,gv,b] using hi1
  ·intro i hi j hj he;exact aF Prod.fst he
 ·intro i;exact ⟨p5 (i,0),rfl⟩
 ·intro i;exact ⟨p5 (i,1),rfl⟩
lemma uE (c p:ℝ) (hc:0<c) (hp:0<p):∃dN:ℝ,1<dN/\∀D≥dN,∀(V:Type) [Fintype V] [DecidableEq V],∀(G P:SimpleGraph V) [DecidableRel P.Adj],P<=G->∀W:Finset V,b9 P W (D^(37/50:ℝ))->2<=W.card->(card V:ℝ)<=D^(51/50:ℝ)->∀(I:Type) [Fintype I] (x y:I->V),(∀i,x i≠y i)->(∀i,x i∉W)->(∀i,y i∉W)->(∀v,b7 univ x y v<=2)->∀r:V×Fin 2->V,(∀v,v∉W->∀t,r (v,t)∈W/\P.Adj v (r (v,t)))->(∀v,v∉W->r (v,0)≠r (v,1))->(∀v,((Wᶜ ×ˢ univ).filter (λ z=>r z=v)).card<=⌈8*(card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊)->
   ∃(a b:I->V) (q:∀i,G.Walk (a i) (b i)),(∀i,G.Adj (x i) (a i)/\G.Adj (y i) (b i))/\Function.Injective (λ z:I×Fin 2=>
     if z.2=0 then s(x z.1,a z.1) else s(y z.1,b z.1))/\
    (∀i,(q i).IsPath/\(q i).length<=dQ W.card (D^(37/50:ℝ))/\∀v∈(q i).support,v∈W)/\
    Pairwise (λ i j=>Disjoint (q i).edgeSet (q j).edgeSet)/\(∀i,∃t,a i=r (x i,t))/\(∀i,∃t,b i=r (y i,t))/\(∀i,(q i).edgeSet⊆P.edgeSet):=by
 obtain ⟨dN,ko,LC⟩:=zd c p hc hp;refine ⟨dN,ko,?_⟩;intro D hD V _ _ G P _ oe W hexp hW hr I _ x y hne hx hy hl r hrep LD rG;obtain ⟨a,b,ha,hb,hs,XJ,ha',hb'⟩:=yA P W x y hne hx hy hl r hrep LD _ rG;obtain ⟨q,hq,hd⟩:=LC D hD V P P dH W hexp hW hr I a b
  (λ i=>(ha i).1) (λ i=>(hb i).1) XJ
 let Q:∀i,G.Walk (a i) (b i):=λ i=>(q i).mapLe oe
 refine ⟨a,b,Q,(λ i=>⟨oe (ha i).2,oe (hb i).2⟩),hs,?_,?_,ha',hb',?_⟩
 ·intro i
  refine ⟨(hq i).1.mapLe oe,?_,?_⟩
  ·simpa only [Q,SimpleGraph.Walk.length_mapLe] using (hq i).2.1
  ·simpa only [Q,SimpleGraph.Walk.support_mapLe_eq_support] using (hq i).2.2
 ·intro i j hij;simpa only [Q,SimpleGraph.Walk.edgeSet_mapLe_eq_edgeSet] using hd hij
 ·intro i;rw [show (Q i).edgeSet=(q i).edgeSet from (q i).edgeSet_mapLe_eq_edgeSet oe];intro e he;exact (q i).edges_subset_edgeSet he
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
open SimpleGraph
variable {V:Type d8} {G:SimpleGraph V} {x y a b:V}
def jU (P:G.Walk a b) (hx:G.Adj x a) (hy:G.Adj y b):G.Walk y x:= .cons hy (P.reverse.concat hx.symm)
lemma Bo (Q:G.Walk x y) (P:G.Walk a b)
  (hQ:Q.IsPath) (K8:0<Q.length) (hP:P.IsPath)
  (hdisj:Q.support.Disjoint P.support) (hx:G.Adj x a) (hy:G.Adj y b):(jU P hx hy).IsPath:=by
 have hxy:x≠y:=by intro h;subst y;have:=hQ.nil_iff_eq.mpr rfl;have hz:Q.length=0:=this.length_eq_zero;omega
 have OC:x∉P.reverse.support:=by simpa using hdisj Q.start_mem_support
 have XK:y∉P.reverse.support:=by simpa using hdisj Q.end_mem_support
 exact (hP.reverse.concat OC hx.symm).cons (by simpa using And.intro XK hxy.symm)
lemma uP (Q:G.Walk x y) (P:G.Walk a b)
  (hQ:Q.IsPath) (K8:0<Q.length) (hP:P.IsPath)
  (hdisj:Q.support.Disjoint P.support) (hx:G.Adj x a) (hy:G.Adj y b):(Q.append (jU P hx hy)).IsCycle/\(Q.append (jU P hx hy)).edgeSet= Q.edgeSet∪P.edgeSet∪{s(x,a),s(y,b)}/\
  3<=(Q.append (jU P hx hy)).length:=by
 have QV:=Bo Q P hQ K8 hP hdisj hx hy;have NU:Q.support.tail.Disjoint (jU P hx hy).support.tail:=by
  rw [ct];intro v hv;have OD:=g7 hv;have XL:v∉P.support:=hdisj OD;have yQ:v≠x:=by have hn:=hQ.support_nodup;rw [<-Q.cons_tail_support,i9] at hn;exact λ heq=>hn.1 (heq▸hv)
  simpa [jU] using And.intro XL yQ
 have LG:=hQ.isCycle_append QV NU (Or.inr (by simp [jU]));refine ⟨LG,?_,?_⟩
 ·ext e;simp only [Walk.edgeSet_append,jU,Walk.edgeSet_cons,Walk.edgeSet_concat,Walk.edgeSet_reverse,b8,eI,dB];rw [bx (a:=x) (b:=a)];tauto
 ·simpa [jU] using (by omega:3<= Q.length+(P.length+1+1))
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma D9 {I:Type d9} {E:Type eO} (e:I×Fin 2->E)
  (he:Function.Injective e):Pairwise (λ i j=>Disjoint ({e (i,0),e (i,1)}:Set E) {e (j,0),e (j,1)}):=by
 intro i j hij;apply aI.mpr;intro a hai haj;simp only [eI,dB] at hai haj;rcases hai with hai | hai<;>rcases haj with haj | haj
 all_goals exact hij (aF Prod.fst (he (hai.symm.trans haj)))
lemma Dd {I:Type fX} {E:Type gu} (A B S:I->Set E)
  (hA:Pairwise λ i j=>Disjoint (A i) (A j))
  (hB:Pairwise λ i j=>Disjoint (B i) (B j))
  (hS:Pairwise λ i j=>Disjoint (S i) (S j))
  (wU:∀i j,Disjoint (A i) (B j))
  (U3:∀i j,Disjoint (A i) (S j))
  (U4:∀i j,Disjoint (B i) (S j)):Pairwise (λ i j=>Disjoint (A i∪B i∪S i) (A j∪B j∪S j)):=by
 intro i j hij;apply aI.mpr;rintro e ((ha | hb) | hs) ((ha' | hb') | hs')
 all_goals first
  | exact aI.mp (hA hij) ha ha'
  | exact aI.mp (hB hij) hb hb'
  | exact aI.mp (hS hij) hs hs'
  | exact aI.mp (wU i j) ha hb'
  | exact aI.mp (U3 i j) ha hs'
  | exact aI.mp (U4 i j) hb hs'
  | exact aI.mp (wU j i) ha' hb
  | exact aI.mp (U3 j i) ha' hs
  | exact aI.mp (U4 j i) hb' hs
lemma Bp {V:Type gX} {I:Type iN} {G:SimpleGraph V}
  {x y a b:I->V} (Q:∀i,G.Walk (x i) (y i))
  (P:∀i,G.Walk (a i) (b i))
  (hx:∀i,G.Adj (x i) (a i)) (hy:∀i,G.Adj (y i) (b i))
  (hQ:∀i,(Q i).IsPath) (K8:∀i,0<(Q i).length)
  (hP:∀i,(P i).IsPath)
  (zN:∀i,(Q i).support.Disjoint (P i).support)
  (LH:Pairwise λ i j=>Disjoint (Q i).edgeSet (Q j).edgeSet)
  (vm:Pairwise λ i j=>Disjoint (P i).edgeSet (P j).edgeSet)
  (R1:Function.Injective (λ z:I×Fin 2=>if z.2=0 then s(x z.1,a z.1) else s(y z.1,b z.1)))
  (XM:∀i j,Disjoint (Q i).edgeSet (P j).edgeSet)
  (XN:∀i j,Disjoint (Q i).edgeSet {s(x j,a j),s(y j,b j)})
  (XO:∀i j,Disjoint (P i).edgeSet {s(x j,a j),s(y j,b j)}):let C:=λ i=>(Q i).append (jU (P i) (hx i) (hy i))
  (∀i,(C i).IsCycle)/\Pairwise (λ i j=>Disjoint (C i).edgeSet (C j).edgeSet)/\(⋃ i,(C i).edgeSet)=(⋃ i,(Q i).edgeSet)∪(⋃ i,(P i).edgeSet)∪(⋃ i,({s(x i,a i),s(y i,b i)}:Set (Sym2 V))):=by
 dsimp only;have hC:=λ i=>uP (Q i) (P i) (hQ i) (K8 i)
  (hP i) (zN i) (hx i) (hy i)
 refine ⟨λ i=>(hC i).1,?_,?_⟩
 ·have XP:Pairwise (λ i j=>Disjoint
    ({s(x i,a i),s(y i,b i)}:Set (Sym2 V)) {s(x j,a j),s(y j,b j)}):=by
   simpa using D9 _ R1
  simpa only [λ i=>(hC i).2.1] using
   Dd (λ i=>(Q i).edgeSet) (λ i=>(P i).edgeSet)
    (λ i=>({s(x i,a i),s(y i,b i)}:Set (Sym2 V)))
    LH vm XP XM XN XO
 ·simp only [λ i=>(hC i).2.1,mj]
end
end af
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX gu gX iN iO i7 jD jV jW jX kB jY kC kD kE kF jZ j0 lC lT lU oA n4 n5 qg qh qi sD sG sH qj sI qk qm qo qs qt qu sJ sK sL sN qv
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma vJ {V:Type bX} {G H:SimpleGraph V}
  {x y a b:V} (p:G.Walk x y) (q:H.Walk a b)
  (h:p.support.Disjoint q.support):Disjoint p.edgeSet q.edgeSet:=by
 apply aI.mpr;intro e he he';induction e using bJ with
 | _ u v=>exact h (p.fst_mem_support_of_mem_edges he) (q.fst_mem_support_of_mem_edges he')
lemma s8 {V:Type bY} {I:Type cy} {G:SimpleGraph V}
  {u v:V} (Q:G.Walk u v) (W:Set V) (x y a b:I->V)
  (hQ:∀z∈Q.support,z∉W) (ha:∀i,a i∈W) (hb:∀i,b i∈W):∀i,Disjoint Q.edgeSet ({s(x i,a i),s(y i,b i)}:Set (Sym2 V)):=by
 intro i;apply aI.mpr;intro e he he';rcases he' with rfl | he'
 ·exact hQ _ (Q.snd_mem_support_of_mem_edges he) (ha i)
 ·have heq:e=s(y i,b i):=he';subst e;exact hQ _ (Q.snd_mem_support_of_mem_edges he) (hb i)
lemma tu {V:Type cz} {I:Type cP} {G:SimpleGraph V}
  {u v:V} (Q:G.Walk u v) (W:Set V) (x y a b:I->V)
  (hQ:∀z∈Q.support,z∈W) (hx:∀i,x i∉W) (hy:∀i,y i∉W):∀i,Disjoint Q.edgeSet ({s(x i,a i),s(y i,b i)}:Set (Sym2 V)):=by
 intro i;apply aI.mpr;intro e he he';rcases he' with rfl | he'
 ·exact hx i (hQ _ (Q.fst_mem_support_of_mem_edges he))
 ·have heq:e=s(y i,b i):=he';subst e;exact hy i (hQ _ (Q.fst_mem_support_of_mem_edges he))
lemma w9 (c p:ℝ) (hc:0<c) (hp:0<p):∃dN:ℝ,1<dN/\∀D≥dN,∀(V:Type) [Fintype V] [DecidableEq V],∀(G P:SimpleGraph V) [DecidableRel P.Adj],P<=G->∀W:Finset V,b9 P W (D^(37/50:ℝ))->2<=W.card->(card V:ℝ)<=D^(51/50:ℝ)->∀(I:Type) [Fintype I] (x y:I->V) (Q:∀i,G.Walk (x i) (y i)),(∀i,(Q i).IsPath)->(∀i,0<(Q i).length)->(∀i v,v∈(Q i).support->v∉W)->Pairwise (λ i j=>Disjoint (Q i).edgeSet (Q j).edgeSet)->(∀v,b7 univ x y v<=2)->∀r:V×Fin 2->V,(∀v,v∉W->∀t,r (v,t)∈W/\P.Adj v (r (v,t)))->(∀v,v∉W->r (v,0)≠r (v,1))->(∀v,((Wᶜ ×ˢ univ).filter (λ z=>r z=v)).card<=⌈8*(card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊)->
   ∃(a b:I->V) (q:∀i,G.Walk (a i) (b i))
    (C:∀i,G.Walk (x i) (x i)),(∀i,(C i).IsCycle)/\Pairwise (λ i j=>Disjoint (C i).edgeSet (C j).edgeSet)/\(∀i,(C i).edgeSet=(Q i).edgeSet∪(q i).edgeSet∪{s(x i,a i),s(y i,b i)})/\
    (∀i,(q i).edgeSet⊆P.edgeSet/\∀v∈(q i).support,v∈W)/\Function.Injective (λ z:I×Fin 2=>if z.2=0 then s(x z.1,a z.1) else s(y z.1,b z.1))/\
    (∀i,∃t,a i=r (x i,t))/\(∀i,∃t,b i=r (y i,t)):=by
 obtain ⟨dN,ko,Pg⟩:=uE c p hc hp;refine ⟨dN,ko,?_⟩;intro D hD V _ _ G P _ oe W hexp hW hr I _ x y Q hQ j4 vZ LH hl r hrep LD rG;have hne:∀i,x i≠y i:=by intro i hi;have hz:=((hQ i).nil_iff_eq.mpr hi).length_eq_zero;have:=j4 i;omega
 have hx:∀i,x i∉W:=λ i=>vZ i _ (Q i).start_mem_support
 have hy:∀i,y i∉W:=λ i=>vZ i _ (Q i).end_mem_support
 obtain ⟨a,b,q,hab,GU,hq,XQ,ha',hb',R2⟩:=Pg D hD V G P oe W hexp hW hr I x y hne hx hy hl r hrep LD rG;have ha:∀i,a i∈W:=λ i=>(hq i).2.2 _ (q i).start_mem_support
 have hb:∀i,b i∈W:=λ i=>(hq i).2.2 _ (q i).end_mem_support
 have hdisj:∀i j,(Q i).support.Disjoint (q j).support:=by intro i j;exact ct.mpr (λ v hv Io=>vZ i v hv ((hq j).2.2 v Io))
 let C:=λ i=>(Q i).append (jU (q i) (hab i).1 (hab i).2)
 have Nc:=Bp Q q (λ i=>(hab i).1) (λ i=>(hab i).2)
  hQ j4 (λ i=>(hq i).1) (λ i=>hdisj i i) LH XQ GU
  (λ i j=>vJ _ _ (hdisj i j))
  (λ i=>s8 (Q i) W x y a b (vZ i) ha hb)
  (λ i=>tu (q i) W x y a b (hq i).2.2 hx hy)
 refine ⟨a,b,q,C,Nc.1,Nc.2.1,?_,?_,GU,ha',hb'⟩
 ·intro i
  exact (uP (Q i) (q i) (hQ i) (j4 i) (hq i).1
   (hdisj i i) (hab i).1 (hab i).2).2.1
 ·intro i;exact ⟨R2 i,(hq i).2.2⟩
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma zS {V:Type cL} (W:Fin 3->Set V)
  (hW:Pairwise λ i j=>Disjoint (W i) (W j)) (x y:V):∃i,x∉W i/\y∉W i:=by
 by_contra R3;have h:∀i,x∈W i\/y∈W i:=by
  intro i
  by_contra! hi
  exact R3 ⟨i,hi⟩
 have U5:=aI.mp (hW (show (0:Fin 3)≠1 by decide));have U6:=aI.mp (hW (show (0:Fin 3)≠2 by decide));have U7:=aI.mp (hW (show (1:Fin 3)≠2 by decide));rcases h 0 with hx0 | hy0<;>rcases h 1 with hx1 | hy1<;>rcases h 2 with hx2 | hy2
 all_goals first
  | exact U5 hx0 hx1
  | exact U6 hx0 hx2
  | exact U7 hx1 hx2
  | exact U5 hy0 hy1
  | exact U6 hy0 hy2
  | exact U7 hy1 hy2
lemma qJ {V:Type c9} (W:Fin 3->Set V)
  (hW:Pairwise λ i j=>Disjoint (W i) (W j)) (e:Sym2 V):∃i,∀v∈e,v∉W i:=by
 induction e using bJ with
 | _ x y=>
   obtain ⟨i,hx,hy⟩:=zS W hW x y;refine ⟨i,?_⟩;intro v hv;rcases Sym2.mem_iff.mp hv with rfl | rfl
   ·exact hx
   ·exact hy
noncomputable def qV {V:Type dW} (W:Fin 3->Set V)
  (hW:Pairwise λ i j=>Disjoint (W i) (W j)) (e:Sym2 V):Fin 3:=(qJ W hW e).choose
lemma qW {V:Type eo} (W:Fin 3->Set V)
  (hW:Pairwise λ i j=>Disjoint (W i) (W j)) (e:Sym2 V):∀v∈e,v∉W (qV W hW e):=(qJ W hW e).choose_spec
def gw {V:Type d7} (G:SimpleGraph V)
  (W:Fin 3->Set V) (hW:Pairwise λ i j=>Disjoint (W i) (W j))
  (i:Fin 3):SimpleGraph V where
 Adj x y:=G.Adj x y/\qV W hW s(x,y)=i
 symm:=⟨by intro x y h;exact ⟨h.1.symm,by simpa only [bx] using h.2⟩⟩
 loopless:=⟨by intro x h;exact G.loopless.irrefl x h.1⟩
lemma kG {V:Type d8} (G:SimpleGraph V)
  (W:Fin 3->Set V) (hW:Pairwise λ i j=>Disjoint (W i) (W j))
  (i:Fin 3):(gw G W hW i).edgeSet={e | e∈G.edgeSet/\qV W hW e=i}:=by
 ext e;induction e using bJ with
 | _ x y=>rfl
lemma qw {V:Type d9} (G:SimpleGraph V)
  (W:Fin 3->Set V) (hW:Pairwise λ i j=>Disjoint (W i) (W j)):(∀i,gw G W hW i<=G)/\(∀i x y,(gw G W hW i).Adj x y->x∉W i/\y∉W i)/\
  Pairwise (λ i j=>Disjoint (gw G W hW i).edgeSet
   (gw G W hW j).edgeSet)/\
  (⋃ i,(gw G W hW i).edgeSet)=G.edgeSet:=by
 refine ⟨λ _ _ _ h=>h.1,?_,?_,?_⟩
 ·intro i x y h;have hx:=qW W hW s(x,y) x (Sym2.mem_mk_left x y);have hy:=qW W hW s(x,y) y (Sym2.mem_mk_right x y);rw [h.2] at hx hy;exact ⟨hx,hy⟩
 ·intro i j hij;rw [kG,kG];exact aI.mpr λ _ he hj=>hij (he.2.symm.trans hj.2)
 ·ext e
  simp only [av,kG,Set.mem_ofPred];constructor
  ·rintro ⟨i,he,_⟩;exact he
  ·intro he;exact ⟨qV W hW e,he,rfl⟩
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
def fD {V:Type eO} (P:SimpleGraph V) (W:Set V):Set (Sym2 V):={e | e∈P.edgeSet/\∀v∈e,v∈W}
noncomputable def gL {V:Type fX} [Fintype V] [DecidableEq V]
  (W:Finset V) (r:V×Fin 2->V):Finset (Sym2 V):=(Wᶜ ×ˢ univ).image (λ z=>s(z.1,r z))
lemma pU {V:Type gu} [Fintype V] [DecidableEq V]
  (W:Finset V) (r:V×Fin 2->V) (e:Sym2 V):e∈gL W r↔∃v∉W,∃t:Fin 2,e=s(v,r (v,t)):=by
 simp only [gL,bk,jt,cU,aQ,and_true,Prod.exists];constructor
 ·rintro ⟨v,t,hv,he⟩;exact ⟨v,hv,t,he.symm⟩
 ·rintro ⟨v,hv,t,he⟩;exact ⟨v,t,hv,he.symm⟩
lemma um {V:Type gX} [Fintype V] [DecidableEq V]
  (W:Finset V) (r:V×Fin 2->V):(gL W r).card<=2*card V:=by
 apply (ju).trans;rw [oE,c7,dU];have:=e4 Wᶜ;omega
lemma Bq {V:Type iN} [Fintype V] [DecidableEq V]
  (P:SimpleGraph V) (W:Finset V) (r:V×Fin 2->V)
  (hr:∀v,v∉W->∀t,P.Adj v (r (v,t))):(gL W r:Set (Sym2 V))⊆P.edgeSet:=by
 intro e he;obtain ⟨v,hv,t,rfl⟩:=(pU W r e).mp he;exact hr v hv t
lemma pD {V:Type iO} [Fintype V] [DecidableEq V]
  (P:SimpleGraph V) (W:Finset V) (r:V×Fin 2->V):Disjoint (fD P W) (gL W r:Set (Sym2 V)):=by
 apply aI.mpr;intro e he he';obtain ⟨v,hv,t,rfl⟩:=(pU W r e).mp he';exact hv (he.2 _ (Sym2.mem_mk_left _ _))
lemma qF {V:Type i7} [Fintype V] [DecidableEq V]
  (G:SimpleGraph V) (P:Fin 3->SimpleGraph V) (W:Fin 3->Finset V)
  (r:Fin 3->V×Fin 2->V)
  (oe:∀i,P i<=G)
  (vm:Pairwise λ i j=>Disjoint (P i).edgeSet (P j).edgeSet)
  (hr:∀i v,v∉W i->∀t,(P i).Adj v (r i (v,t))):let R:=λ i=>fD (P i) (W i)
  let O:=λ i=>(gL (W i) (r i):Set (Sym2 V))
  (∀i,R i⊆G.edgeSet/\O i⊆G.edgeSet)/\Pairwise (λ i j=>Disjoint (R i∪O i) (R j∪O j))/\(∀i,Disjoint (R i) (O i))/\Disjoint (⋃ i,R i) (⋃ i,O i)/\(∑i,(gL (W i) (r i)).card)<=6*card V:=by
 dsimp only;have hR:∀i,fD (P i) (W i)⊆(P i).edgeSet:=λ _ _ he=>he.1
 have hO:=λ i=>Bq (P i) (W i) (r i) (hr i)
 have hU:∀i,fD (P i) (W i)∪(gL (W i) (r i):Set (Sym2 V))⊆(P i).edgeSet:=λ i=>Set.union_subset (hR i) (hO i)
 refine ⟨?_,?_,?_,?_,?_⟩
 ·intro i;exact ⟨(hR i).trans (cD (oe i)),(hO i).trans (cD (oe i))⟩
 ·intro i j hij;exact (vm hij).mono (hU i) (hU j)
 ·exact λ i=>pD (P i) (W i) (r i)
 ·rw [kP]
  intro i;rw [oI];intro j;by_cases hij:i=j
  ·subst j;exact pD (P i) (W i) (r i)
  ·exact (vm hij).mono (hR i) (hO j)
 ·calc
   _<=∑_i:Fin 3,2*card V:=aK (λ i _=>um (W i) (r i))
   _=_:=by simp;omega
lemma yB {V:Type jD} {G:SimpleGraph V}
  (W:Fin 3->Set V) (hW:Pairwise λ i j=>Disjoint (W i) (W j))
  (i:Fin 3) {x y:V} (q:(gw G W hW i).Walk x y)
  (hq:0<q.length):∀v∈q.support,v∉W i:=by
 have hn:¬q.Nil:=by intro h;have hz:=h.length_eq_zero;omega
 intro v hv;obtain ⟨e,he,Oz⟩:=rT hn |>.mp hv;have heG:=q.edges_subset_edgeSet he;have TX:qV W hW e=i:=by rw [kG] at heG;exact heG.2
 exact TX▸qW W hW e v Oz
lemma vd {V:Type jV} (G:SimpleGraph V)
  (W:Fin 3->Set V) (hW:Pairwise λ i j=>Disjoint (W i) (W j))
  (E:Set (Sym2 V)) (hE:E⊆G.edgeSet):let H:=G.deleteEdges E
  let K:=λ i=>gw H W hW i
  Pairwise (λ i j=>Disjoint (K i).edgeSet (K j).edgeSet)/\(∀i,Disjoint (K i).edgeSet E)/\((⋃ i,(K i).edgeSet)∪E=G.edgeSet):=by
 dsimp only;have hh:=qw (G.deleteEdges E) W hW;refine ⟨hh.2.2.1,?_,?_⟩
 ·intro i;apply aI.mpr;intro e he he';have h:=cD (hh.1 i) he;rw [g8] at h;exact h.2 he'
 ·rw [hh.2.2.2,g8];exact mo hE
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
def sO {V:Type jW} (G:SimpleGraph V) (E:Set (Sym2 V)):SimpleGraph V where
 Adj x y:=G.Adj x y/\s(x,y)∈E
 symm:=⟨by intro x y h;exact ⟨h.1.symm,by simpa only [bx] using h.2⟩⟩
 loopless:=⟨by intro x h;exact G.loopless.irrefl x h.1⟩
lemma ET {V:Type jX} (G:SimpleGraph V) (E:Set (Sym2 V)):sO G E<=G:=λ _ _ h=>h.1
lemma B3 {V:Type kB} (G:SimpleGraph V) (E:Set (Sym2 V)):(sO G E).edgeSet=G.edgeSet∩E:=by ext e;induction e using bJ with | _ x y=>rfl
lemma vM {V:Type jY} (G:SimpleGraph V) (E:Set (Sym2 V))
  (hE:E⊆G.edgeSet):(sO G E).edgeSet=E:=by
 rw [B3,Set.inter_eq_right.mpr hE]
def iQ {V:Type kC} {I:Type kD} (C:I->Set (Sym2 V)):Set (Sym2 V):=⋃ i,C i
def iA {V:Type kE} {B:Type kF} {I:Type jZ} (G:SimpleGraph V)
  (R:B->Set (Sym2 V)) (C:I->Set (Sym2 V)) (b:B):SimpleGraph V:=sO G (R b\iQ C)
def lH {V:Type j0} {I:Type lC} [Fintype V] (S:Set (Sym2 V))
 (C:I->Set (Sym2 V)):Finset (Sym2 V):=(S\iQ C).toFinset
lemma De {V:Type lT} {I:Type lU} [Fintype V] (S:Finset (Sym2 V))
  (C:I->Set (Sym2 V)):(lH (↑S) C).card<=S.card:=by
 apply aU;intro e he;simp only [lH,jc,kQ,kR] at he;exact he.1
lemma Ea {V:Type oA} {B:Type n4} {I:Type n5} [Fintype V]
  (G:SimpleGraph V) (R:B->Set (Sym2 V)) (S:Set (Sym2 V))
  (C:I->Set (Sym2 V))
  (hR:∀b,R b⊆G.edgeSet) (hS:S⊆G.edgeSet)
  (xN:Pairwise λ b c=>Disjoint (R b) (R c))
  (hRS:∀b,Disjoint (R b) S)
  (hC:∀i,C i⊆G.edgeSet)
  (aaz:Pairwise λ i j=>Disjoint (C i) (C j))
  (e7:G.edgeSet\((⋃ b,R b)∪S)⊆iQ C):(∀b,(iA G R C b).edgeSet=R b\iQ C)/\Pairwise (λ b c=>Disjoint (iA G R C b).edgeSet
   (iA G R C c).edgeSet)/\
  (∀b i,Disjoint (iA G R C b).edgeSet (C i))/\(∀b,Disjoint (iA G R C b).edgeSet (↑(lH S C):Set _))/\(∀i,Disjoint (C i) (↑(lH S C):Set _))/\(iQ C∪(↑(lH S C):Set _)∪(⋃ b,(iA G R C b).edgeSet))=G.edgeSet:=by
 classical
 have G5 (b:B):(iA G R C b).edgeSet=R b\iQ C:=by apply vM;exact λ e he=>hR b he.1
 have JZ:(↑(lH S C):Set _)=S\iQ C:=by simp only [lH,Set.coe_toFinset]
 have hsub:iQ C⊆G.edgeSet:=by rintro e he;obtain ⟨i,hi⟩:=av.mp he;exact hC i hi
 refine ⟨G5,?_,?_,?_,?_,?_⟩
 ·intro b c hbc;rw [G5 b,G5 c];exact (xN hbc).mono jd jd
 ·intro b i;rw [G5 b];apply aI.mpr;intro e he hi;exact he.2 (av.mpr ⟨i,hi⟩)
 ·intro b;rw [G5 b,JZ];exact (hRS b).mono jd jd
 ·intro i;rw [JZ];apply aI.mpr;intro e hi he;exact he.2 (av.mpr ⟨i,hi⟩)
 ·rw [JZ]
  ext e;constructor
  ·rintro ((he | he) | he)
   ·exact hsub he
   ·exact hS he.1
   ·obtain ⟨b,hb⟩:=av.mp he;rw [G5 b] at hb;exact hR b hb.1
  ·intro he
   by_cases hc:e∈iQ C
   ·exact Or.inl (Or.inl hc)
   by_cases hs:e∈S
   ·exact Or.inl (Or.inr ⟨hs,hc⟩)
   have hr:e∈⋃ b,R b:=by by_contra hr;exact hc (e7 ⟨he,by intro hu;exact hu.elim hr hs⟩)
   obtain ⟨b,hb⟩:=av.mp hr;exact Or.inr (av.mpr ⟨b,by rw [G5 b];exact ⟨hb,hc⟩⟩)
lemma EU {V:Type qg} {I:Type qh} [Fintype V] [Fintype I]
  (S:Finset (Sym2 V)) (C:I->Set (Sym2 V))
  (hI:card I<=3*card V)
  (hS:S.card<=6*card V):card I+(lH (↑S) C).card<=9*card V:=by
 have:=De S C;omega
lemma t4 {V:Type qi} (H:SimpleGraph V)
  (W:Set V) (hW:H.support⊆W):Sym2.map Subtype.val '' (H.induce W).edgeSet=H.edgeSet:=by
 ext e;constructor
 ·rintro ⟨d,hd,rfl⟩
  induction d using bJ with
  | _ x y=>exact hd
 ·intro he
  induction e using bJ with
  | _ x y=>have hx:x∈W:=hW ⟨y,he⟩;have hy:y∈W:=hW ⟨x,he.symm⟩;exact ⟨s(⟨x,hx⟩,⟨y,hy⟩),he,rfl⟩
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma Eb {V:Type qj} {G P:SimpleGraph V} {a b:V}
  (W:Set V) (q:G.Walk a b) (he:q.edgeSet⊆P.edgeSet)
  (hv:∀v∈q.support,v∈W):q.edgeSet⊆fD P W:=by
 intro e h;refine ⟨he h,?_⟩;induction e using bJ with
 | _ x y=>
   intro v hmem;rcases (Sym2.mem_iff.mp hmem) with rfl | rfl
   ·exact hv _ (q.fst_mem_support_of_mem_edges h)
   ·exact hv _ (q.snd_mem_support_of_mem_edges h)
lemma Az {V:Type sI} [Fintype V] [DecidableEq V]
  {G P:SimpleGraph V} (W:Finset V) (r:V×Fin 2->V)
  {x y a b:V} (Q:G.Walk x y) (q:G.Walk a b) (C:G.Walk x x)
  (K:Set (Sym2 V)) (hQ:Q.edgeSet⊆K)
  (hC:C.edgeSet= Q.edgeSet∪q.edgeSet∪{s(x,a),s(y,b)})
  (hq:q.edgeSet⊆P.edgeSet/\∀v∈q.support,v∈W)
  (hx:x∉W) (hy:y∉W)
  (ha:∃t,a=r (x,t)) (hb:∃t,b=r (y,t)):C.edgeSet⊆K∪(fD P W∪(gL W r:Set _)):=by
 rw [hC];have R4:=Eb (W:Set V) q hq.1 hq.2;intro e he;rcases he with (he | he) | he
 ·exact Or.inl (hQ he)
 ·exact Or.inr (Or.inl (R4 he))
 ·apply Or.inr∘Or.inr
  rcases (show e=s(x,a)\/e=s(y,b) by simpa using he) with rfl | rfl
  ·obtain ⟨t,rfl⟩:=ha;exact (pU W r _).mpr ⟨x,hx,t,rfl⟩
  ·obtain ⟨t,rfl⟩:=hb;exact (pU W r _).mpr ⟨y,hy,t,rfl⟩
lemma v5 {E:Type qk} {B:Type qm} {I:B->Type sN}
  (K R:B->Set E) (C:∀b,I b->Set E)
  (R5:Pairwise λ b c=>Disjoint (K b) (K c))
  (xN:Pairwise λ b c=>Disjoint (R b) (R c))
  (U8:∀b c,Disjoint (K b) (R c))
  (hC:∀b i,C b i⊆K b∪R b)
  (Kr:∀b,Pairwise λ i j=>Disjoint (C b i) (C b j)):Pairwise (λ s t:Sigma I=>Disjoint (C s.1 s.2) (C t.1 t.2)):=by
 rintro ⟨b,i⟩ ⟨c,j⟩ hne;by_cases hbc:b=c
 ·subst c;apply Kr b;intro hij;exact hne (by cases hij;rfl)
 ·apply Disjoint.mono (hC b i) (hC c j);rw [mw,mz,mz];exact ⟨⟨R5 hbc,U8 b c⟩,⟨(U8 c b).symm,xN hbc⟩⟩
lemma xO {E:Type qo} {B:Type qs} {I:B->Type qv}
  (K:B->Set E) (Q C:∀b,I b->Set E)
  (hQ:∀b,(⋃ i,Q b i)=K b)
  (Ks:∀b i,Q b i⊆C b i):(⋃ b,K b)⊆⋃ s:Sigma I,C s.1 s.2:=by
 intro e he;obtain ⟨b,hb⟩:=av.mp he;rw [<-hQ b] at hb;obtain ⟨i,hi⟩:=av.mp hb;exact av.mpr ⟨⟨b,i⟩,Ks b i hi⟩
lemma zT {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
  (x y:I->V) (hne:∀i,x i≠y i)
  (lG:∀v,b7 univ x y v<=2):card I<=card V:=by
 classical
 have hs:=zP (univ:Finset I) x y (λ i _=>hne i);have hb:=aK (λ v (_:v∈(univ:Finset V))=>lG v);simp only [c7] at hs;rw [hs] at hb;simp only [d5,c7,jJ] at hb;omega
lemma Ec {V:Type} [Fintype V]
  (I:Fin 3->Type) [∀b,Fintype (I b)]
  (hI:∀b,card (I b)<=card V):card (Sigma I)<=3*card V:=by
 rw [fy];calc
  _<=∑_b:Fin 3,card V:=aK (λ b _=>hI b)
  _=_:=by simp [bK]
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma uF (c p:ℝ) (hc:0<c) (hp:0<p):∃dN:ℝ,1<dN/\∀D≥dN,∀(V:Type) [Fintype V] [DecidableEq V],∀(G:SimpleGraph V) (P K:Fin 3->SimpleGraph V)
    [∀b,DecidableRel (P b).Adj],
   (∀b,P b<=G)->Pairwise (λ b d=>Disjoint (P b).edgeSet (P d).edgeSet)->∀(W:Fin 3->Finset V) (r:Fin 3->V×Fin 2->V),(∀b,b9 (P b) (W b) (D^(37/50:ℝ)))->(∀b,2<=(W b).card)->(card V:ℝ)<=D^(51/50:ℝ)->(∀b v,v∉W b->∀t,r b (v,t)∈W b/\(P b).Adj v (r b (v,t)))->(∀b v,v∉W b->r b (v,0)≠r b (v,1))->(∀b v,(((W b)ᶜ ×ˢ univ).filter (λ z=>r b z=v)).card<=⌈8*(card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊)->
   let T:=λ b=>fD (P b) (W b)∪(gL (W b) (r b):Set (Sym2 V))
   Pairwise (λ b d=>Disjoint (K b).edgeSet (K d).edgeSet)->(∀b d,Disjoint (K b).edgeSet (T d))->∀(I:Fin 3->Type) [∀b,Fintype (I b)]
    (x y:∀b,I b->V) (Q:∀b i,G.Walk (x b i) (y b i)),
   (∀b i,(Q b i).IsPath)->(∀b i,0<(Q b i).length)->(∀b i v,v∈(Q b i).support->v∉W b)->(∀b,Pairwise λ i j=>Disjoint (Q b i).edgeSet (Q b j).edgeSet)->(∀b,(⋃ i,(Q b i).edgeSet)=(K b).edgeSet)->(∀b v,b7 univ (x b) (y b) v<=2)->∃C:∀b i,G.Walk (x b i) (x b i),(∀b i,(C b i).IsCycle)/\Pairwise (λ s t:Sigma I=>
     Disjoint (C s.1 s.2).edgeSet (C t.1 t.2).edgeSet)/\
    (∀b i,(C b i).edgeSet⊆(K b).edgeSet∪T b)/\(⋃ b,(K b).edgeSet)⊆(⋃ s:Sigma I,(C s.1 s.2).edgeSet)/\card (Sigma I)<=3*card V:=by
 classical
 obtain ⟨dN,ko,LI⟩:=w9 c p hc hp;refine ⟨dN,ko,?_⟩;intro D hD V _ _ G P K _ oe vm W r hexp hW hn hr LB rG;dsimp only;intro R5 R6 I _ x y Q hQ j4 vZ LH e7 hl;have hex:∀b:Fin 3,∃(a z:I b->V) (q:∀i,G.Walk (a i) (z i))
    (C:∀i,G.Walk (x b i) (x b i)),(∀i,(C i).IsCycle)/\Pairwise (λ i j=>Disjoint (C i).edgeSet (C j).edgeSet)/\(∀i,(C i).edgeSet=(Q b i).edgeSet∪(q i).edgeSet∪{s(x b i,a i),s(y b i,z i)})/\
    (∀i,(q i).edgeSet⊆(P b).edgeSet/\∀v∈(q i).support,v∈W b)/\Function.Injective (λ z':I b×Fin 2=>if z'.2=0 then s(x b z'.1,a z'.1) else s(y b z'.1,z z'.1))/\
    (∀i,∃t,a i=r b (x b i,t))/\(∀i,∃t,z i=r b (y b i,t)):=by
  intro b;exact LI D hD V G (P b) (oe b) (W b) (hexp b) (hW b) hn
   (I b) (x b) (y b) (Q b) (hQ b) (j4 b) (vZ b) (LH b) (hl b)
   (r b) (hr b) (LB b) (rG b)
 choose a z q C R7 Kr U9 EV aaA ha hz using hex;have hsub:∀b i,(C b i).edgeSet⊆(K b).edgeSet∪(fD (P b) (W b)∪(gL (W b) (r b):Set _)):=by
  intro b i;apply Az (W b) (r b) (Q b i) (q b i) (C b i)
   (K b).edgeSet _ (U9 b i) (EV b i)
   (vZ b i _ (Q b i).start_mem_support)
   (vZ b i _ (Q b i).end_mem_support) (ha b i) (hz b i)
  intro e he;rw [<-e7 b];exact av.mpr ⟨i,he⟩
 have QW:=qF G P W r oe vm
  (λ b v hv t=>(hr b v hv t).2)
 refine ⟨C,R7,?_,hsub,?_,?_⟩
 ·exact v5 (λ b=>(K b).edgeSet)
   (λ b=>fD (P b) (W b)∪(gL (W b) (r b):Set _))
   (λ b i=>(C b i).edgeSet) R5 QW.2.1 R6 hsub Kr
 ·apply xO (λ b=>(K b).edgeSet)
   (λ b i=>(Q b i).edgeSet) (λ b i=>(C b i).edgeSet) e7
  intro b i e he;rw [U9 b i];exact Or.inl (Or.inl he)
 ·apply Ec I;intro b;apply zT (x b) (y b) _ (hl b);intro i hi;have hz:=((hQ b i).nil_iff_eq.mpr hi).length_eq_zero;have hp:=j4 b i;omega
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
noncomputable def gO {V:Type qt} [Fintype V] [DecidableEq V]
  (W:Fin 3->Finset V) (r:Fin 3->V×Fin 2->V):Finset (Sym2 V):=univ.biUnion (λ b=>gL (W b) (r b))
lemma qG {V:Type qu} [Fintype V] [DecidableEq V]
  (W:Fin 3->Finset V) (r:Fin 3->V×Fin 2->V):(gO W r:Set (Sym2 V))=⋃ b,(gL (W b) (r b):Set (Sym2 V)):=by
 ext e;simp [gO]
lemma yC {V:Type sJ} [Fintype V] [DecidableEq V]
  (W:Fin 3->Finset V) (r:Fin 3->V×Fin 2->V):(gO W r).card<=6*card V:=by
 apply (c5).trans;calc
  (∑b:Fin 3,(gL (W b) (r b)).card)<=∑_b:Fin 3,2*card V:=aK (λ b _=>um (W b) (r b))
  _=_:=by simp;omega
lemma zf {V:Type sK} {I:Type sL} [Fintype V] [DecidableEq V] [Fintype I]
  (G:SimpleGraph V) (P:Fin 3->SimpleGraph V)
  (W:Fin 3->Finset V) (r:Fin 3->V×Fin 2->V)
  (oe:∀b,P b<=G)
  (vm:Pairwise λ b d=>Disjoint (P b).edgeSet (P d).edgeSet)
  (hr:∀b v,v∉W b->∀t,(P b).Adj v (r b (v,t)))
  (C:I->Set (Sym2 V)) (hC:∀i,C i⊆G.edgeSet)
  (Kr:Pairwise λ i j=>Disjoint (C i) (C j))
  (hI:card I<=3*card V)
  (e7:G.edgeSet\((⋃ b,fD (P b) (W b))∪(gO W r:Set _))⊆iQ C):
  let R:=λ b=>fD (P b) (W b)
  let H:=iA G R C;let S:=lH (↑(gO W r)) C
  (∀b,(H b).support⊆(W b:Set V))/\(∀b,Sym2.map Subtype.val '' ((H b).induce (W b:Set V)).edgeSet=(H b).edgeSet)/\(∀b,(H b).edgeSet=R b\iQ C)/\Pairwise (λ b d=>Disjoint (H b).edgeSet (H d).edgeSet)/\(∀b i,Disjoint (H b).edgeSet (C i))/\(∀b,Disjoint (H b).edgeSet (S:Set _))/\(∀i,Disjoint (C i) (S:Set _))/\(iQ C∪(S:Set _)∪(⋃ b,(H b).edgeSet))=G.edgeSet/\card I+S.card<=9*card V:=by
 classical
 dsimp only;obtain ⟨hsub,XR,aaa,hRS,WV⟩:=qF G P W r oe vm hr;have hS:(gO W r:Set (Sym2 V))⊆G.edgeSet:=by rw [qG];exact gJ (λ b=>(hsub b).2)
 have xN:Pairwise λ b d=>
   Disjoint (fD (P b) (W b)) (fD (P d) (W d)):=by
  intro b d hbd;exact (XR hbd).mono mB mB
 have XS:∀b,Disjoint (fD (P b) (W b))
   (gO W r:Set (Sym2 V)):=by
  intro b;rw [qG];exact hRS.mono_left (je (λ d=>fD (P d) (W d)) b)
 let R:=λ b=>fD (P b) (W b)
 let H:=iA G R C;have r6:=Ea G R (↑(gO W r)) C
  (λ b=>(hsub b).1) hS xN XS hC Kr e7
 have Df:∀b,(H b).support⊆(W b:Set V):=by intro b v hv;obtain ⟨w,hw⟩:=(H b).mem_support.mp hv;have he:s(v,w)∈(H b).edgeSet:=hw;rw [r6.1 b] at he;exact he.1.2 _ (Sym2.mem_mk_left _ _)
 refine ⟨Df,?_,r6.1,r6.2.1,r6.2.2.1,r6.2.2.2.1,r6.2.2.2.2.1,r6.2.2.2.2.2,?_⟩
 ·intro b;exact t4 (H b) (W b) (Df b)
 ·exact EU (gO W r) C hI (yC W r)
end
end af
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX gu gX iN iO i7 jD jV jW jX kB jY kC kD kE kF jZ j0 lC lT lU oA n4 n5 qg qh qi sD sG sH qj sI qk qm qo qs qt qu sJ sK sL sN qv v7 v8 v9 wc we A6 wj wm Ip Iq Ir It Iu Iv Iw Ix Iy Iz ID IE IG IL IQ IS IT IU IV IW IX
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.cI
open aR.af.aV
open aR.af.Splitting
universe u
section
open SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
def pA {V:Type bX} (S:Set V) (R:V->V->Prop) (v:V):Prop:=∃a∈S,Relation.ReflTransGen R a v
lemma yR {V:Type bY} {S:Set V} {R:V->V->Prop}
  {v:V} (hv:v∈S):pA S R v:=⟨v,hv, .refl⟩
lemma A7 {V:Type cy} {S:Set V} {R:V->V->Prop}
  {v w:V} (hv:pA S R v) (h:R v w):pA S R w:=by
 obtain ⟨a,ha,hr⟩:=hv;exact ⟨a,ha,hr.tail h⟩
lemma J0 {V:Type cz} {S:Set V} {R:V->V->Prop} {v:V}:pA S R v↔v∈S\/∃w,pA S R w/\R w v:=by
 constructor
 ·rintro ⟨a,ha,hr⟩
  rcases hr.cases_tail with rfl | ⟨w,hw,h⟩
  ·exact Or.inl ha
  ·exact Or.inr ⟨w,⟨a,ha,hw⟩,h⟩
 ·rintro (h | ⟨w,hw,h⟩)
  ·exact yR h
  ·exact A7 hw h
lemma Go {V:Type cL} {S T:Set V} {R:V->V->Prop}
  (hS:S⊆T) (hR:∀a b,R a b->b∈T):{v | pA S R v}⊆T:=by
 rintro v ⟨a,ha,hr⟩;rcases hr.cases_tail with rfl | ⟨w,_,h⟩
 ·exact hS ha
 ·exact hR w v h
lemma star_inj {V:Type dW} {x a b:V}:s(x,a)=s(x,b)↔a=b:=by
 rw [jI];constructor
 ·rintro (⟨_,h⟩ | ⟨h,h'⟩)
  ·exact h
  ·exact h'.trans h
 ·intro h;exact Or.inl ⟨rfl,h⟩
structure k4 {V:Type eo} (G:SimpleGraph V) where
 start:V
 finish:V
 walk:G.Walk start finish
 isPath:walk.IsPath
 positive:0<walk.length
lemma k4.QX {V:Type d7} {G:SimpleGraph V} (P:k4 G):P.start≠P.finish:=by intro h;have hz:=(P.isPath.nil_iff_eq.mpr h).length_eq_zero;have:=P.positive;omega
structure iB {V:Type d8} (G:SimpleGraph V) where
 start:V
 finish:V
 walk:G.Walk start finish
 simple:(walk.IsPath/\0<walk.length)\/∃h:finish=start,(walk.copy rfl h).IsCycle
namespace iB
variable {V:Type d9} {G:SimpleGraph V}
def qX (p:k4 G):iB G:=⟨p.start,p.finish,p.walk,Or.inl ⟨p.isPath,p.positive⟩⟩
def zF {v:V} (p:G.Walk v v) (h:p.IsCycle):iB G:=⟨v,v,p,Or.inr ⟨rfl,h⟩⟩
end iB
structure kk {V:Type eO} (G:SimpleGraph V) (x:V) where
 su:V
 oq:V
 adj:G.Adj x su
 walk:G.Walk su oq
 isPath:walk.IsPath
 uN:x∉walk.support
namespace kk
variable {V:Type fX} {G:SimpleGraph V} {x:V}
def os (A:kk G x):k4 G where
 start:=x
 finish:=A.oq
 walk:= .cons A.adj A.walk
 isPath:=A.isPath.cons A.uN
 positive:=by simp
def flip (A:kk G x) (h:G.Adj x A.oq):kk G x where
 su:=A.oq
 oq:=A.su
 adj:=h
 walk:=A.walk.reverse
 isPath:=A.isPath.reverse
 uN:=by simpa using A.uN
@[simp] lemma NV (A:kk G x) (h:G.Adj x A.oq):(A.flip h).walk.edgeSet=A.walk.edgeSet:=by simp [flip]
@[simp] lemma G6 (A:kk G x) (h:G.Adj x A.oq) (v:V):v∈(A.flip h).walk.support↔v∈A.walk.support:=by simp [flip]
lemma IY (A B:kk G x)
  (hd:A.walk.support.Disjoint B.walk.support):((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).IsPath:=by
 apply Walk.IsPath.mk';simp only [Walk.support_append,Walk.support_reverse,Walk.support_cons,mC,List.reverse_cons,kS];apply List.nodup_append'.mpr;refine ⟨List.nodup_reverse.mpr A.isPath.support_nodup,?_,?_⟩
 ·exact i9.mpr ⟨B.uN,B.isPath.support_nodup⟩
 ·rw [ct]
  intro v hv hq;have P6:v∈A.walk.support:=List.mem_reverse.mp hv;rcases dd.mp hq with rfl | hq
  ·exact A.uN P6
  ·exact ct.mp hd P6 hq
def join (A B:kk G x) (hd:A.walk.support.Disjoint B.walk.support):k4 G where
 start:=A.oq
 finish:=B.oq
 walk:=(Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)
 isPath:=IY A B hd
 positive:=by simp only [Walk.length_append,Walk.length_reverse,Walk.length_cons];omega
lemma zg (A B:kk G x) (hd:A.walk.support.Disjoint B.walk.support):(A.join B hd).walk.edgeSet=A.walk.edgeSet∪B.walk.edgeSet∪{s(x,A.su),s(x,B.su)}:=by simp only [join,Walk.edgeSet_append,Walk.edgeSet_reverse,Walk.edgeSet_cons];ext e;simp only [b8,eI,dB];tauto
lemma QY (A B:kk G x) (hd:A.walk.support.Disjoint B.walk.support):A.su≠B.su:=by intro h;exact ct.mp hd A.walk.start_mem_support (by simpa only [h] using B.walk.start_mem_support)
lemma DR (A:kk G x):A.oq≠x:=by intro h;apply A.uN;simpa only [h] using A.walk.end_mem_support
lemma wq (A:kk G x) (v:V):s(x,v)∉A.walk.edgeSet:=by
 intro he;exact A.uN (Walk.mem_support_iff_exists_mem_edges.mpr
  (Or.inr ⟨s(x,v),he,by simp⟩))
def orient (A:kk G x) (bT:Prop) (h:bT->G.Adj x A.oq):kk G x:=if ha:bT then A.flip (h ha) else A
@[simp] lemma LJ (A:kk G x) (bT:Prop) (h:bT->G.Adj x A.oq):(A.orient bT h).walk.edgeSet=A.walk.edgeSet:=by
 by_cases ha:bT
 ·exact (aF (λ B:kk G x=>B.walk.edgeSet)
   (show A.orient bT h=A.flip (h ha) from dif_pos ha)).trans (A.NV _)
 ·exact aF (λ B:kk G x=>B.walk.edgeSet)
   (show A.orient bT h=A from dif_neg ha)
@[simp] lemma MH (A:kk G x) (bT:Prop) (h:bT->G.Adj x A.oq):(A.orient bT h).su=if bT then A.oq else A.su:=by by_cases ha:bT<;>simp [orient,flip,ha]
@[simp] lemma xP (A:kk G x) (bT:Prop)
  (h:bT->G.Adj x A.oq) (v:V):v∈(A.orient bT h).walk.support↔v∈A.walk.support:=by
 by_cases ha:bT
 ·exact (aF (λ B:kk G x=>v∈B.walk.support)
   (show A.orient bT h=A.flip (h ha) from dif_pos ha)).to_iff.trans
    (A.G6 _ v)
 ·exact (aF (λ B:kk G x=>v∈B.walk.support)
   (show A.orient bT h=A from dif_neg ha)).to_iff
lemma IZ (A B:kk G x) (p q:Prop)
  (ha:p->G.Adj x A.oq) (hb:q->G.Adj x B.oq)
  (hd:A.walk.support.Disjoint B.walk.support):(A.orient p ha).walk.support.Disjoint (B.orient q hb).walk.support:=by
 rw [ct];intro v hv hw;exact ct.mp hd ((A.xP p ha v).mp hv)
  ((B.xP q hb v).mp hw)
end kk
inductive Frame {V:Type gu} (G:SimpleGraph V) (x:V) where
 | away (p:k4 G) (avoid:x∉p.walk.support)
 | os (A:kk G x)
 | kJ (A B:kk G x) (disjoint:A.walk.support.Disjoint B.walk.support)
namespace Frame
variable {V:Type gX} {G:SimpleGraph V} {x:V}
def path:Frame G x->k4 G
 | .away p _=>p
 | .os A=>A.os
 | .kJ A B hd=>A.join B hd
def Port:Frame G x->Type
 | .away _ _=>Bool
 | .os _=>Unit
 | .kJ _ _ _=>Bool
def fH:(F:Frame G x)->F.Port->V
 | .away p _,false=>p.start
 | .away p _,true=>p.finish
 | .os A,_=>A.oq
 | .kJ A _ _,false=>A.oq
 | .kJ _ B _,true=>B.oq
def exit:(F:Frame G x)->F.Port->Option V
 | .away _ _,_=>none
 | .os _,_=>none
 | .kJ A _ _,false=>some A.su
 | .kJ _ B _,true=>some B.su
def kM (F:Frame G x) (bT:F.Port->Prop):Set (Sym2 V):={e | ∃p,bT p/\e=s(x,F.fH p)}
def lV (F:Frame G x) (bT:F.Port->Prop):Set (Sym2 V):={e | ∃p,bT p/\∃v,F.exit p=some v/\e=s(x,v)}
lemma EW (F:Frame G x) (p:F.Port):F.fH p≠x:=by
 cases F with
 | away P hx=>
   cases p
   ·change P.start≠x;intro h;apply hx;simpa only [<-h] using P.walk.start_mem_support
   ·change P.finish≠x;intro h;apply hx;simpa only [<-h] using P.walk.end_mem_support
 | os A=>exact A.DR
 | kJ A B hd=>cases p<;>exact kk.DR _
lemma Gp (F:Frame G x) (v:V):(∃p:F.Port,F.fH p=v)↔(F.path.start=v\/F.path.finish=v)/\v≠x:=by
 constructor
 ·rintro ⟨p,rfl⟩
  refine ⟨?_,(F.EW p)⟩;cases F with
  | away P hx=>cases p<;>simp [fH,path]
  | os A=>exact Or.inr rfl
  | kJ A B hd=>cases p<;>simp [fH,path,kk.join]
 ·rintro ⟨he,hx⟩
  cases F with
  | away P hp=>
    rcases he with he | he
    ·exact ⟨false,he⟩
    ·exact ⟨true,he⟩
  | os A=>
    rcases he with he | he
    ·exact (hx he.symm).elim
    ·exact ⟨(),he⟩
  | kJ A B hd=>
    rcases he with he | he
    ·exact ⟨false,he⟩
    ·exact ⟨true,he⟩
lemma vo (F:Frame G x) (p:F.Port) (v:V) (h:F.exit p=some v):s(x,v)∈F.path.walk.edgeSet:=by
 cases F with
 | away P hx=>cases h
 | os A=>cases h
 | kJ A B hd=>
   cases p
   ·cases h
    rw [path,kk.zg];exact Or.inr (by simp)
   ·cases h
    rw [path,kk.zg];exact Or.inr (by simp)
lemma B4 (F:Frame G x) (bT:F.Port->Prop):F.lV bT⊆F.path.walk.edgeSet:=by rintro e ⟨p,hp,v,hv,rfl⟩;exact F.vo p v hv
@[simp] lemma LK (P:k4 G) (hx:x∉P.walk.support)
  (bT:(Frame.away P hx).Port->Prop):(Frame.away P hx).lV bT=∅:=by
 ext e;simp [lV,exit]
@[simp] lemma MI (A:kk G x) (bT:(Frame.os A).Port->Prop):(Frame.os A).lV bT=∅:=by ext e;simp [lV,exit]
lemma KK (P:k4 G) (hx:x∉P.walk.support)
  (bT:(Frame.away P hx).Port->Prop):(Frame.away P hx).kM bT=(if bT false then {s(x,P.start)} else ∅)∪(if bT true then {s(x,P.finish)} else ∅):=by
 ext e;by_cases h0:bT false<;>by_cases h1:bT true<;>simp [kM,fH,Port,Bool.exists_bool,h0,h1,or_comm]
lemma LL (A:kk G x) (bT:(Frame.os A).Port->Prop):(Frame.os A).kM bT=if bT () then {s(x,A.oq)} else ∅:=by ext e;by_cases h:bT ()<;>simp [kM,fH,Port,h]
lemma G7 (A B:kk G x) (hd:A.walk.support.Disjoint B.walk.support)
  (bT:(Frame.kJ A B hd).Port->Prop):(Frame.kJ A B hd).kM bT=(if bT false then {s(x,A.oq)} else ∅)∪(if bT true then {s(x,B.oq)} else ∅):=by
 ext e;by_cases h0:bT false<;>by_cases h1:bT true<;>simp [kM,fH,Port,Bool.exists_bool,h0,h1,or_comm]
lemma I0 (A B:kk G x) (hd:A.walk.support.Disjoint B.walk.support)
  (bT:(Frame.kJ A B hd).Port->Prop):(Frame.kJ A B hd).lV bT=(if bT false then {s(x,A.su)} else ∅)∪(if bT true then {s(x,B.su)} else ∅):=by
 ext e;by_cases h0:bT false<;>by_cases h1:bT true<;>simp [lV,exit,Port,Bool.exists_bool,h0,h1,or_comm]
end Frame
lemma AA {E:Type iN} (B:Set E) (e f a b:E)
  (he:e∉B) (hf:f∉B) (hne:e≠f) (p q:Prop) [Decidable p] [Decidable q] :((B∪{e,f})\((if p then {e} else ∅)∪(if q then {f} else ∅)))∪((if p then {a} else ∅)∪(if q then {b} else ∅))=B∪{if p then a else e,if q then b else f}:=by
 classical
 ext z;by_cases hp:p<;>by_cases hq:q<;>simp only [hp,hq,↓reduceIte,b8,kR,eI,dB,mD]<;>aesop
namespace Frame
variable {V:Type iO} {G:SimpleGraph V} {x:V}
lemma J1 (A B:kk G x) (hd:A.walk.support.Disjoint B.walk.support)
  (bT:(Frame.kJ A B hd).Port->Prop)
  (hadj:∀p,bT p->G.Adj x ((Frame.kJ A B hd).fH p)):∃Q:iB G,Q.walk.edgeSet=((Frame.kJ A B hd).path.walk.edgeSet\(Frame.kJ A B hd).lV bT)∪(Frame.kJ A B hd).kM bT:=by
 have ha:bT false->G.Adj x A.oq:=hadj false;have hb:bT true->G.Adj x B.oq:=hadj true;let A':=A.orient (bT false) ha;let B':=B.orient (bT true) hb;have GR:A'.walk.support.Disjoint B'.walk.support:=A.IZ B _ _ _ _ hd;refine ⟨iB.qX (A'.join B' GR),?_⟩;have he:s(x,A.su)∉A.walk.edgeSet∪B.walk.edgeSet:=by
  rintro (he | he)
  ·exact A.wq _ he
  ·exact B.wq _ he
 have hf:s(x,B.su)∉A.walk.edgeSet∪B.walk.edgeSet:=by
  rintro (he | he)
  ·exact A.wq _ he
  ·exact B.wq _ he
 have hne:s(x,A.su)≠s(x,B.su):=λ h=>A.QY B hd (star_inj.mp h)
 change (A'.join B' GR).walk.edgeSet=_;rw [G7,I0];change (A'.join B' GR).walk.edgeSet=((A.join B hd).walk.edgeSet\_)∪_;rw [kk.zg,kk.zg];dsimp only [A',B'];simp only [kk.LJ,kk.MH];have hh:=(AA _ _ _ s(x,A.oq) s(x,B.oq) he hf hne
  (bT false) (bT true)).symm
 by_cases h0:bT false<;>by_cases h1:bT true
 ·simpa [h0,h1] using hh
 ·simpa [h0,h1] using hh
 ·simpa [h0,h1] using hh
 ·simp [h0,h1]
lemma NW (A:kk G x) (bT:(Frame.os A).Port->Prop)
  (hadj:∀p,bT p->G.Adj x ((Frame.os A).fH p))
  (EO:∀p,bT p->s(x,(Frame.os A).fH p)∉(Frame.os A).path.walk.edgeSet):
  ∃Q:iB G,Q.walk.edgeSet=((Frame.os A).path.walk.edgeSet\(Frame.os A).lV bT)∪(Frame.os A).kM bT:=by
 rw [MI,LL,Set.sdiff_empty];by_cases ha:bT ()
 ·have haG:G.Adj x A.oq:=hadj () ha
  have he:s(A.oq,x)∉A.os.walk.edges:=by intro he;exact EO () ha (bx▸he)
  let c:G.Walk A.oq A.oq:=Walk.cons haG.symm A.os.walk;have hc:c.IsCycle:=Path.cons_isCycle ⟨A.os.walk,A.os.isPath⟩ _ he;refine ⟨iB.zF c hc,?_⟩;change c.edgeSet=_;dsimp only [c,kk.os,path];simp only [Walk.edgeSet_cons,ha,↓reduceIte];rw [bx];ext e;simp only [eI,b8,dB];tauto
 ·refine ⟨iB.qX A.os,?_⟩;simp [iB.qX,path,ha]
lemma MJ (P:k4 G) (hx:x∉P.walk.support)
  (bT:(Frame.away P hx).Port->Prop)
  (hadj:∀p,bT p->G.Adj x ((Frame.away P hx).fH p)):∃Q:iB G,Q.walk.edgeSet=((Frame.away P hx).path.walk.edgeSet\(Frame.away P hx).lV bT)∪(Frame.away P hx).kM bT:=by
 rw [LK,KK,Set.sdiff_empty];change ∃Q:iB G,Q.walk.edgeSet=P.walk.edgeSet∪_;by_cases h0:bT false
 ·have XT:G.Adj x P.start:=hadj false h0
  let q:G.Walk x P.finish:=Walk.cons XT P.walk;have hq:q.IsPath:=P.isPath.cons hx;by_cases h1:bT true
  ·have he:s(P.finish,x)∉q.edges:=by
    intro he;have hh:=hq.length_eq_one_of_mem_edges (bx▸he);have hp:=P.positive;simp only [q,Walk.length_cons] at hh;omega
   have R8:G.Adj x P.finish:=hadj true h1;let c:G.Walk P.finish P.finish:=Walk.cons R8.symm q;have hc:c.IsCycle:=Path.cons_isCycle ⟨q,hq⟩ _ he;refine ⟨iB.zF c hc,?_⟩;change c.edgeSet=_;simp only [c,q,Walk.edgeSet_cons,h0,h1,↓reduceIte];rw [bx];ext e;simp only [eI,b8,dB];tauto
  ·let Q:k4 G:=⟨x,P.finish,q,hq,by simp [q]⟩;refine ⟨iB.qX Q,?_⟩;change q.edgeSet=_;simp only [q,Walk.edgeSet_cons,h0,h1,↓reduceIte,Set.union_empty];ext e;simp only [eI,b8,dB];tauto
 ·by_cases h1:bT true
  ·have R8:G.Adj x P.finish:=hadj true h1;let q:G.Walk x P.start:=Walk.cons R8 P.walk.reverse;have hq:q.IsPath:=P.isPath.reverse.cons (by simpa using hx);let Q:k4 G:=⟨x,P.start,q,hq,by simp [q]⟩;refine ⟨iB.qX Q,?_⟩;change q.edgeSet=_;simp only [q,Walk.edgeSet_cons,Walk.edgeSet_reverse,h0,h1,↓reduceIte,Set.empty_union];ext e;simp only [eI,b8,dB];tauto
  ·refine ⟨iB.qX P,?_⟩;simp [iB.qX,h0,h1]
lemma modify (F:Frame G x) (bT:F.Port->Prop)
  (hadj:∀p,bT p->G.Adj x (F.fH p))
  (EO:∀p,bT p->F.exit p=none->s(x,F.fH p)∉F.path.walk.edgeSet):∃Q:iB G,Q.walk.edgeSet=(F.path.walk.edgeSet\F.lV bT)∪F.kM bT:=by
 cases F with
 | away P hx=>exact MJ P hx bT hadj
 | kJ A B hd=>exact J1 A B hd bT hadj
 | os A=>exact NW A bT hadj (λ p hp=>EO p hp rfl)
end Frame
lemma G8 {E:Type i7} {I:Type jD} (I3 remove add:I->Set E) (I4:Set E)
  (hsub:∀i,remove i⊆I3 i)
  (hold:Pairwise λ i j=>Disjoint (I3 i) (I3 j))
  (hadd:Pairwise λ i j=>Disjoint (add i) (add j))
  (zU:Disjoint I4 (⋃ i,I3 i))
  (ve:(⋃ i,add i)=(⋃ i,remove i)∪I4):Pairwise (λ i j=>Disjoint ((I3 i\remove i)∪add i)
   ((I3 j\remove j)∪add j))/\
  (⋃ i,((I3 i\remove i)∪add i))=(⋃ i,I3 i)∪I4:=by
 have I5:∀i j,Disjoint (I3 i\remove i) (add j):=by
  intro i j;apply aI.mpr;rintro e ⟨hei,hnot⟩ yP;have hh:e∈(⋃ l,remove l)∪I4:=by rw [<-ve];exact av.mpr ⟨j,yP⟩
  rcases hh with hh | hh
  ·obtain ⟨l,Va⟩:=av.mp hh
   by_cases OE:i=l
   ·subst l;exact hnot Va
   ·exact aI.mp (hold OE) hei (hsub l Va)
  ·exact aI.mp zU hh (av.mpr ⟨i,hei⟩)
 constructor
 ·intro i j hij
  exact Disjoint.union_left
   (Disjoint.union_right ((hold hij).mono jd jd) (I5 i j))
   (Disjoint.union_right (I5 j i).symm (hadd hij))
 ·ext e
  constructor
  ·intro he
   obtain ⟨i,hi⟩:=av.mp he;rcases hi with hi | hi
   ·exact Or.inl (av.mpr ⟨i,hi.1⟩)
   ·have hh:e∈(⋃ l,remove l)∪I4:=by
     rw [<-ve];exact av.mpr ⟨i,hi⟩
    rcases hh with hh | hh
    ·obtain ⟨l,hl⟩:=av.mp hh;exact Or.inl (av.mpr ⟨l,hsub l hl⟩)
    ·exact Or.inr hh
  ·rintro (he | he)
   ·obtain ⟨i,hi⟩:=av.mp he
    by_cases hr:e∈remove i
    ·have hh:e∈⋃ l,add l:=by
      rw [ve];exact Or.inl (av.mpr ⟨i,hr⟩)
     obtain ⟨j,hj⟩:=av.mp hh;exact av.mpr ⟨j,Or.inr hj⟩
    ·exact av.mpr ⟨i,Or.inl ⟨hi,hr⟩⟩
   ·have hh:e∈⋃ l,add l:=by rw [ve];exact Or.inr he
    obtain ⟨i,hi⟩:=av.mp hh;exact av.mpr ⟨i,Or.inr hi⟩
inductive k6 {V:Type jV} (G:SimpleGraph V) (x:V) where
 | path (F:Frame G x)
 | cycle {v:V} (c:G.Walk v v) (hc:c.IsCycle)
namespace k6
variable {V:Type jW} {G:SimpleGraph V} {x:V}
def pB:k6 G x->iB G
 | .path F=> .qX F.path
 | .cycle c hc=> .zF c hc
def Port:k6 G x->Type
 | .path F=>F.Port
 | .cycle _ _=>Empty
def fH:(K:k6 G x)->K.Port->V
 | .path F,p=>F.fH p
 | .cycle _ _,p=>nomatch p
def exit:(K:k6 G x)->K.Port->Option V
 | .path F,p=>F.exit p
 | .cycle _ _,p=>nomatch p
def kM (K:k6 G x) (bT:K.Port->Prop):Set (Sym2 V):={e | ∃p,bT p/\e=s(x,K.fH p)}
def lV (K:k6 G x) (bT:K.Port->Prop):Set (Sym2 V):={e | ∃p,bT p/\∃v,K.exit p=some v/\e=s(x,v)}
lemma vo (K:k6 G x) (p:K.Port) (v:V) (h:K.exit p=some v):s(x,v)∈K.pB.walk.edgeSet:=by
 cases K with
 | path F=>exact F.vo p v h
 | cycle c hc=>exact p.elim
lemma Ph (K:k6 G x) (p:K.Port) (v:V) (h:K.exit p=some v):G.Adj x v:=by exact G.mem_edgeSet.mp (K.pB.walk.edges_subset_edgeSet (K.vo p v h))
lemma KL (K:k6 G x) (p:K.Port) (h:K.exit p=none):∀q,K.exit q=none:=by
 cases K with
 | cycle c hc=>exact p.elim
 | path F=>
   cases F with
   | away P hx=>exact λ _=>rfl
   | os A=>exact λ _=>rfl
   | kJ A B hd=>cases p<;>cases h
lemma B4 (K:k6 G x) (bT:K.Port->Prop):K.lV bT⊆K.pB.walk.edgeSet:=by rintro e ⟨p,hp,v,hv,rfl⟩;exact K.vo p v hv
lemma modify (K:k6 G x) (bT:K.Port->Prop)
  (hadj:∀p,bT p->G.Adj x (K.fH p))
  (EO:∀p,bT p->K.exit p=none->s(x,K.fH p)∉K.pB.walk.edgeSet):
  ∃Q:iB G,Q.walk.edgeSet=(K.pB.walk.edgeSet\K.lV bT)∪K.kM bT:=by
 cases K with
 | path F=>exact F.modify bT hadj EO
 | cycle c hc=>
   refine ⟨.zF c hc,?_⟩;have hr:(k6.cycle c hc).lV bT=∅:=by ext e;simp only [lV,fo,mD];exact ⟨λ ⟨p,_⟩=>p.elim,False.elim⟩
   have hi:(k6.cycle c hc).kM bT=∅:=by ext e;simp only [kM,fo,mD];exact ⟨λ ⟨p,_⟩=>p.elim,False.elim⟩
   simp only [hr,hi,Set.sdiff_empty,Set.union_empty];rfl
end k6
lemma G9 {V:Type jX} {I:Type kB} (G:SimpleGraph V) (x:V)
  (K:I->k6 G x) (S:Set V)
  (hS:∀v∈S,G.Adj x v)
  (hold:Pairwise λ i j=>Disjoint (K i).pB.walk.edgeSet (K j).pB.walk.edgeSet)
  (zU:Disjoint {e | ∃v∈S,e=s(x,v)} (⋃ i,(K i).pB.walk.edgeSet))
  (Dg:Set (Σ i,(K i).Port))
  (hinj:Set.InjOn (λ z:Σ i,(K i).Port=>(K z.1).fH z.2) Dg)
  (wu:∀v,G.Adj x v->∃z∈Dg,(K z.1).fH z.2=v):∃Q:I->iB G,(Pairwise λ i j=>Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet)/\(⋃ i,(Q i).walk.edgeSet)=(⋃ i,(K i).pB.walk.edgeSet)∪{e | ∃v∈S,e=s(x,v)}:=by
 let R:V->V->Prop:=λ a b=>∃z∈Dg,(K z.1).fH z.2=a/\(K z.1).exit z.2=some b
 let bT:(i:I)->(K i).Port->Prop:=λ i p=>(⟨i,p⟩:Σ j,(K j).Port)∈Dg/\pA S R ((K i).fH p)
 have GV:∀v,pA S R v->G.Adj x v:=by
  intro v hv;exact Go (T:={v | G.Adj x v}) hS
   (by rintro a b ⟨z,_,_,hz⟩;exact (K z.1).Ph z.2 b hz) hv
 have ve:(⋃ i,(K i).kM (bT i))=(⋃ i,(K i).lV (bT i))∪{e | ∃v∈S,e=s(x,v)}:=by
  ext e;constructor
  ·intro he
   obtain ⟨i,p,hp,rfl⟩:=av.mp he;rcases (J0.mp hp.2) with hs | ⟨w,hw,z,hz,hzw,I6⟩
   ·exact Or.inr ⟨_,hs,rfl⟩
   ·exact Or.inl (av.mpr ⟨z.1,z.2,⟨hz,hzw.symm▸hw⟩,
     _,I6,rfl⟩)
  ·rintro (he | ⟨v,hv,rfl⟩)
   ·obtain ⟨i,p,hp,v,Li,rfl⟩:=av.mp he;have hv:pA S R v:=A7 hp.2 ⟨⟨i,p⟩,hp.1,rfl,Li⟩;obtain ⟨z,hz,I6⟩:=wu v (GV v hv);exact av.mpr ⟨z.1,z.2,⟨hz,I6.symm▸hv⟩,aF (s(x,·)) I6.symm⟩
   ·obtain ⟨z,hz,I6⟩:=wu v (hS v hv);exact av.mpr ⟨z.1,z.2,⟨hz,I6.symm▸yR hv⟩,aF (s(x,·)) I6.symm⟩
 have hadd:Pairwise λ i j=>
   Disjoint ((K i).kM (bT i)) ((K j).kM (bT j)):=by
  intro i j hij;apply aI.mpr;rintro e ⟨p,hp,he⟩ ⟨q,hq,hf⟩;have h:(⟨i,p⟩:Σ l,(K l).Port)=⟨j,q⟩:=hinj hp.1 hq.1 (star_inj.mp (he.symm.trans hf));exact hij (aF Sigma.fst h)
 have EO:∀i p,bT i p->(K i).exit p=none->s(x,(K i).fH p)∉(K i).pB.walk.edgeSet:=by
  intro i p hp hn he;have ha:s(x,(K i).fH p)∈⋃ j,(K j).kM (bT j):=av.mpr ⟨i,p,hp,rfl⟩;rw [ve] at ha;rcases ha with ha | ha
  ·obtain ⟨j,q,hq,v,R9,A5⟩:=av.mp ha
   have yP:s(x,(K i).fH p)∈(K j).pB.walk.edgeSet:=A5▸(K j).vo q v R9;have hij:i=j:=by by_contra h;exact aI.mp (hold h) he yP
   subst j;rw [(K i).KL p hn q] at R9;cases R9
  ·exact aI.mp zU ha (av.mpr ⟨i,he⟩)
 choose Q hQ using λ i=>(K i).modify (bT i)
  (λ p hp=>GV _ hp.2) (EO i)
 have hh:=G8 (λ i=>(K i).pB.walk.edgeSet)
  (λ i=>(K i).lV (bT i)) (λ i=>(K i).kM (bT i))
  {e | ∃v∈S,e=s(x,v)} (λ i=>(K i).B4 _) hold hadd zU ve
 refine ⟨Q,?_,?_⟩
 ·simpa only [hQ] using hh.1
 ·simpa only [hQ] using hh.2
lemma LO {V:Type jY} {I:Type kC} (G:SimpleGraph V) (x:V)
  (K:I->k6 G x) (S:Set V)
  (hS:∀v∈S,G.Adj x v)
  (hold:Pairwise λ i j=>Disjoint (K i).pB.walk.edgeSet (K j).pB.walk.edgeSet)
  (zU:Disjoint {e | ∃v∈S,e=s(x,v)} (⋃ i,(K i).pB.walk.edgeSet))
  (wu:∀v,G.Adj x v->∃i p,(K i).fH p=v):∃Q:I->iB G,(Pairwise λ i j=>Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet)/\(⋃ i,(Q i).walk.edgeSet)=(⋃ i,(K i).pB.walk.edgeSet)∪{e | ∃v∈S,e=s(x,v)}:=by
 let T:={v // G.Adj x v};have hh:∀v:T,∃z:Σ i,(K i).Port,(K z.1).fH z.2=v.val:=by intro v;obtain ⟨i,p,h⟩:=wu v.val v.property;exact ⟨⟨i,p⟩,h⟩
 choose f hf using hh;apply G9 G x K S hS hold zU (Set.range f)
 ·rintro z ⟨v,rfl⟩ w ⟨u,rfl⟩ he;have hvu:v=u:=aZ ((hf v).symm.trans (he.trans (hf u)));exact aF f hvu
 ·intro v hv;exact ⟨f ⟨v,hv⟩,⟨⟨v,hv⟩,rfl⟩,hf ⟨v,hv⟩⟩
namespace kk
variable {V:Type kD} {G:SimpleGraph V} {x b:V}
def vf (w:G.Walk x b) (hp:w.IsPath) (hn:¬w.Nil):kk G x:=match w with
 | .nil=>False.elim (hn .nil)
 | @Walk.cons _ _ _ y _ h q=>⟨y,b,h,q,(Walk.cons_isPath_iff h q).mp hp |>.1,(Walk.cons_isPath_iff h q).mp hp |>.2⟩
@[simp] lemma zV (w:G.Walk x b) (hp:w.IsPath) (hn:¬w.Nil):(vf w hp hn).oq=b:=by
 cases w with
 | nil=>exact (hn .nil).elim
 | cons h q=>rfl
@[simp] lemma zW (w:G.Walk x b) (hp:w.IsPath) (hn:¬w.Nil):(vf w hp hn).walk.support=w.support.tail:=by
 cases w with
 | nil=>exact (hn .nil).elim
 | cons h q=>rfl
@[simp] lemma qx (w:G.Walk x b) (hp:w.IsPath) (hn:¬w.Nil):(vf w hp hn).os.walk.edgeSet=w.edgeSet:=by
 cases w with
 | nil=>exact (hn .nil).elim
 | cons h q=>rfl
end kk
lemma k4.LP {V:Type kE} {G:SimpleGraph V} (P:k4 G) (x:V):∃F:Frame G x,F.path.walk.edgeSet=P.walk.edgeSet/\∀v,(F.path.start=v\/F.path.finish=v)↔(P.start=v\/P.finish=v):=by
 classical
 by_cases hx:x∈P.walk.support
 ·obtain ⟨q,r,hq,hr,P7⟩:=P.isPath.mem_support_iff_exists_append.mp hx
  have hp:(q.append r).IsPath:=P7▸P.isPath;by_cases hqn:q.Nil
  ·have hx:P.start=x:=hqn.eq
   have hrn:¬r.Nil:=by intro hn;exact P.QX (hx.trans hn.eq)
   let A:=kk.vf r hr hrn;refine ⟨.os A,?_,?_⟩
   ·change A.os.walk.edgeSet=P.walk.edgeSet;rw [kk.qx];rw [P7,Walk.edgeSet_append];simp [Walk.edgeSet,Walk.edges_eq_nil.mpr hqn]
   ·intro v;change (x=v\/A.oq=v)↔_;simp only [A,kk.zV,hx]
  ·by_cases hrn:r.Nil
   ·have hx:x=P.finish:=hrn.eq
    have Pj:¬q.reverse.Nil:=by simpa using hqn
    let A:=kk.vf q.reverse hq.reverse Pj;refine ⟨.os A,?_,?_⟩
    ·change A.os.walk.edgeSet=P.walk.edgeSet;rw [kk.qx,Walk.edgeSet_reverse];rw [P7,Walk.edgeSet_append];simp [Walk.edgeSet,Walk.edges_eq_nil.mpr hrn]
    ·intro v;change (x=v\/A.oq=v)↔_;simp only [A,kk.zV,hx,or_comm]
   ·have Pj:¬q.reverse.Nil:=by simpa using hqn
    let A:=kk.vf q.reverse hq.reverse Pj;let B:=kk.vf r hr hrn;have hd:A.walk.support.Disjoint B.walk.support:=by
     rw [kk.zW,kk.zW];have hd:=hp.disjoint_support_of_append hrn;rw [Walk.support_tail_of_not_nil r hrn] at hd;apply ct.mpr;intro v hv hw;exact ct.mp hd
      (by simpa using (g7 hv:v∈q.reverse.support)) hw
    refine ⟨.kJ A B hd,?_,?_⟩
    ·change ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).edgeSet=_;rw [Walk.edgeSet_append,Walk.edgeSet_reverse];change A.os.walk.edgeSet∪B.os.walk.edgeSet=_;rw [kk.qx,kk.qx,Walk.edgeSet_reverse,P7,Walk.edgeSet_append]
    ·intro v;change (A.oq=v\/B.oq=v)↔_;simp only [A,B,kk.zV]
 ·exact ⟨.away P hx,rfl,λ _=>Iff.rfl⟩
namespace iB
variable {V:Type kF} {G H:SimpleGraph V}
lemma isTrail (P:iB G):P.walk.IsTrail:=by
 rcases P.simple with hp | ⟨h,hc⟩
 ·exact hp.1.isTrail
 ·exact (P.walk.isTrail_copy rfl h).mp hc.isTrail
def mapLe (h:H<=G) (P:iB H):iB G:=by
 rcases P with ⟨a,b,w,hs⟩;refine ⟨a,b,w.mapLe h,?_⟩;rcases hs with hp | ⟨hb,hc⟩
 ·exact Or.inl ⟨hp.1.mapLe h,by simpa using hp.2⟩
 ·subst b;exact Or.inr ⟨rfl,by simpa using hc.mapLe h⟩
@[simp] lemma MK (h:H<=G) (P:iB H):(P.mapLe h).walk.edgeSet=P.walk.edgeSet:=by
 cases P
 exact Walk.edgeSet_mapLe_eq_edgeSet _ _
@[simp] lemma Tw (h:H<=G) (P:iB H):(P.mapLe h).start=P.start:=by cases P;rfl
@[simp] lemma Sa (h:H<=G) (P:iB H):(P.mapLe h).finish=P.finish:=by cases P;rfl
lemma I7 (P:iB G) (x:V):∃K:k6 G x,K.pB.walk.edgeSet=P.walk.edgeSet/\∀v,P.start≠P.finish->(P.start=v\/P.finish=v)->v≠x->∃p,K.fH p=v:=by
 rcases P with ⟨a,b,w,hs⟩;rcases hs with hp | ⟨hb,hc⟩
 ·let Q:k4 G:=⟨a,b,w,hp.1,hp.2⟩;obtain ⟨F,he,hv⟩:= Q.LP x;refine ⟨.path F,he,?_⟩;intro v _ he hx;exact (F.Gp v).mpr ⟨(hv v).mpr he,hx⟩
 ·subst b;refine ⟨.cycle w (by simpa using hc),rfl,?_⟩;exact λ _ hn=>(hn rfl).elim
end iB
lemma yD {V:Type jZ} {I:Type j0} [Fintype V] [Fintype I]
  (G:SimpleGraph V) {a b:I->V} (p:∀i,G.Walk (a i) (b i))
  (ht:∀i,(p i).IsTrail)
  (hd:Pairwise λ i j=>Disjoint (p i).edgeSet (p j).edgeSet)
  (hc:(⋃ i,(p i).edgeSet)=G.edgeSet) (v:V):G.degree v=∑i,(p i).edges.countP (λ e=>decide (v∈e)):=by
 classical
 have he:G.edgeFinset=univ.biUnion (λ i=>(p i).edges.toFinset):=by ext e;simp only [cu,<-hc,av,bR,aQ,bw,b5,SimpleGraph.Walk.mem_edgeSet]
 rw [<-G.card_incidenceFinset_eq_degree v,G.incidenceFinset_eq_filter,he,filter_biUnion];rw [j5]
 ·apply cZ rfl
  intro i _;have QZ:((p i).edges.filter (λ e=>decide (v∈e))).toFinset=((p i).edges.toFinset.filter (λ e=>v∈e)):=by simp [List.toFinset_filter]
  rw [<-QZ,eJ ((ht i).edges_nodup.filter _),List.countP_eq_length_filter]
 ·intro i _ j _ hij
  apply aL.mpr;intro e hei yP;exact aI.mp (hd hij)
   (by simpa using (aD.mp hei).1)
   (by simpa using (aD.mp yP).1)
lemma pV {V:Type lC} {I:Type lT} [Fintype V] [Fintype I]
  (G:SimpleGraph V) {a b:I->V} (p:∀i,G.Walk (a i) (b i))
  (ht:∀i,(p i).IsTrail)
  (hd:Pairwise λ i j=>Disjoint (p i).edgeSet (p j).edgeSet)
  (hc:(⋃ i,(p i).edgeSet)=G.edgeSet) (v:V):Even (G.degree v)↔Even (univ.filter
   (λ i=>a i≠b i/\(v=a i\/v=b i))).card:=by
 classical
 rw [yD G p ht hd hc v,even_sum_iff_even_card_odd];have he:(univ.filter (λ i=>Odd ((p i).edges.countP
   (λ e=>decide (v∈e)))))=(univ.filter
   (λ i=>a i≠b i/\(v=a i\/v=b i))):=by
  ext i;simp only [aD,aQ,b5,<-jf,(ht i).even_countP_edges_iff];tauto
 rw [he]
lemma A8 {V:Type lU} {I:Type oA} [Fintype V] [Fintype I]
  (H:SimpleGraph V) (P:I->iB H)
  (hd:Pairwise λ i j=>Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
  (hc:(⋃ i,(P i).walk.edgeSet)=H.edgeSet)
  (v:V) (hv:Odd (H.degree v)):∃i,(P i).start≠(P i).finish/\((P i).start=v\/(P i).finish=v):=by
 classical
 have ho:=(pV H (λ i=>(P i).walk)
  (λ i=>(P i).isTrail) hd hc v).not.mp (jf.mpr hv)
 have hp:0<(univ.filter
   (λ i=>(P i).start≠(P i).finish/\(v=(P i).start\/v=(P i).finish))).card:=by
  by_contra hn;have hz:(univ.filter
   (λ i=>(P i).start≠(P i).finish/\(v=(P i).start\/v=(P i).finish))).card=0:=by omega
  exact ho (hz▸⟨0,rfl⟩)
 obtain ⟨i,hi⟩:=cT.mp hp;exact ⟨i,(aD.mp hi).2.1,by simpa only [gH] using (aD.mp hi).2.2⟩
lemma yS {V:Type n4} {I:Type n5} [Fintype V] [Fintype I]
  (G H:SimpleGraph V) (DS:H<=G) (x:V) (S:Set V)
  (hS:∀v∈S,G.Adj x v)
  (LQ:G.edgeSet=H.edgeSet∪{e | ∃v∈S,e=s(x,v)})
  (zU:Disjoint {e | ∃v∈S,e=s(x,v)} H.edgeSet)
  (Wh:∀v,G.Adj x v->Odd (H.degree v))
  (P:I->iB H)
  (hd:Pairwise λ i j=>Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
  (hc:(⋃ i,(P i).walk.edgeSet)=H.edgeSet):∃Q:I->iB G,(Pairwise λ i j=>Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet)/\(⋃ i,(Q i).walk.edgeSet)=G.edgeSet:=by
 choose K hk hv using λ i=>((P i).mapLe DS).I7 x
 have he:∀i,(K i).pB.walk.edgeSet=(P i).walk.edgeSet:=by intro i;exact (hk i).trans ((P i).MK DS)
 have Vb:(⋃ i,(K i).pB.walk.edgeSet)=H.edgeSet:=by simpa only [he] using hc
 obtain ⟨Q,hQ,Ks⟩:=LO G x K S hS
  (by simpa only [he] using hd) (by rwa [Vb]) (by intro v hxv;obtain ⟨i,hi,hiv⟩:=A8 H P hd hc v (Wh v hxv);obtain ⟨p,hp⟩:=hv i v (by simpa using hi) (by simpa using hiv) hxv.ne.symm;exact ⟨i,p,hp⟩)
 exact ⟨Q,hQ,by simpa only [Vb,<-LQ] using Ks⟩
def lM {V:Type qg} [Fintype V] (G:SimpleGraph V):ℕ:=G.support.toFinset.card
lemma zX {V:Type qh} [Fintype V] {G H:SimpleGraph V} (h:H<=G):lM H<=lM G:=by apply aU;intro v hv;exact jc.mpr (support_mono h (jc.mp hv))
def pK {V:Type qi} [Fintype V] (G:SimpleGraph V):Prop:=∃(k:ℕ) (P:Fin k->iB G),(Pairwise λ i j=>Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)/\(⋃ i,(P i).walk.edgeSet)=G.edgeSet/\2*k<=lM G
def rI {V:Type sD} [Fintype V] (G:SimpleGraph V) (x:V):Set V:={y | G.Adj x y/\Even (G.degree y)}
def o4 {V:Type sG} [Fintype V] (G:SimpleGraph V) (x:V):Set (Sym2 V):={e | ∃y∈rI G x,e=s(x,y)}
def gx {V:Type sH} [Fintype V] (G:SimpleGraph V) (x:V):SimpleGraph V:=G.deleteEdges (o4 G x)
lemma I8 {V:Type qj} [Fintype V] (G:SimpleGraph V) (x:V):o4 G x⊆G.edgeSet:=by rintro e ⟨y,hy,rfl⟩;exact hy.1
lemma xd {V:Type sI} [Fintype V] (G:SimpleGraph V)
  (x v:V) (hxv:G.Adj x v) (he:Even (G.degree v)):(gx G x).neighborFinset v=(G.neighborFinset v).erase x:=by
 classical
 ext w;rw [iK,(gx G x).mem_neighborFinset,G.mem_neighborFinset];rw [gx,mJ];simp only [o4,fo,rI,jI];constructor
 ·rintro ⟨DN,hn⟩;refine ⟨?_,DN⟩;intro hw;subst w;exact hn ⟨v,⟨hxv,he⟩,Or.inr ⟨rfl,rfl⟩⟩
 ·rintro ⟨hw,DN⟩
  refine ⟨DN,?_⟩;rintro ⟨y,_,h⟩;rcases h with ⟨h,_⟩ | ⟨_,h⟩
  ·exact hxv.ne h.symm
  ·exact hw h
lemma xQ {V:Type qk} [Fintype V] (G:SimpleGraph V)
  (x v:V) (hxv:G.Adj x v) (he:¬Even (G.degree v)):(gx G x).neighborFinset v=G.neighborFinset v:=by
 classical
 ext w;rw [(gx G x).mem_neighborFinset,G.mem_neighborFinset];rw [gx,mJ];simp only [o4,fo,rI,jI];refine ⟨λ h=>h.1,λ hw=>⟨hw,?_⟩⟩;rintro ⟨y,hy,h⟩;rcases h with ⟨h,_⟩ | ⟨h,_⟩
 ·exact hxv.ne h.symm
 ·subst y;exact he hy.2
lemma wv {V:Type qm} [Fintype V] (G:SimpleGraph V)
  (x v:V) (hxv:G.Adj x v):Odd ((gx G x).degree v):=by
 classical
 by_cases he:Even (G.degree v)
 ·have lN:=jg (s:=G.neighborFinset v)
   (a:=x) (by simpa using hxv.symm)
  rw [<-xd G x v hxv he,G.card_neighborFinset_eq_degree,(gx G x).card_neighborFinset_eq_degree] at lN;obtain ⟨k,hk⟩:=he;exact ⟨k-1,by omega⟩
 ·rw [<-(gx G x).card_neighborFinset_eq_degree v,xQ G x v hxv he,G.card_neighborFinset_eq_degree];exact jf.mp he
lemma Dh {V:Type qo} [Fintype V] (G:SimpleGraph V) (x:V):G.edgeSet=(gx G x).edgeSet∪o4 G x:=by rw [gx,g8,mo (I8 G x)]
lemma wz {V:Type qs} [Fintype V] (G:SimpleGraph V) (x:V):Disjoint (o4 G x) (gx G x).edgeSet:=by rw [gx,g8];exact Set.disjoint_sdiff_right
lemma Gq {V:Type qt} [Fintype V] (G:SimpleGraph V) (x y:V)
  (hxy:G.Adj x y) (he:Even (G.degree y)):(gx G x).edgeFinset.card<G.edgeFinset.card:=by
 classical
 apply oJ;apply oK.mpr;refine ⟨?_,?_⟩
 ·intro e he
  exact G.mem_edgeFinset.mpr (cD
   (show gx G x<=G from G.deleteEdges_le _)
   ((gx G x).mem_edgeFinset.mp he))
 ·intro h;have hh:s(x,y)∈(gx G x).edgeFinset:=h.symm▸G.mem_edgeFinset.mpr hxy;have hf:s(x,y)∈o4 G x:=⟨y,⟨hxy,he⟩,rfl⟩;exact aI.mp (wz G x) hf (cu.mp hh)
lemma zY {V:Type qu} [Fintype V] (G:SimpleGraph V)
  (Sb:∀H:SimpleGraph V,H.edgeFinset.card<G.edgeFinset.card->pK H)
  (j4:∃y,0<G.degree y/\Even (G.degree y)):pK G:=by
 classical
 obtain ⟨y,hy,he⟩:=j4;obtain ⟨x,hxy⟩:=(G.degree_pos_iff_exists_adj y).mp hy;let H:=gx G x;obtain ⟨k,P,hd,hc,hk⟩:=Sb H (Gq G x y hxy.symm he);obtain ⟨Q,hQ,Ks⟩:=yS G H (G.deleteEdges_le _) x
  (rI G x) (λ _ h=>h.1) (Dh G x)
  (wz G x) (wv G x) P hd hc
 exact ⟨k,Q,hQ,Ks,hk.trans (zX (G.deleteEdges_le _))⟩
lemma Gt {V:Type sJ} (G:SimpleGraph V) (e:Sym2 V) (he:e∈G.edgeSet):∃P:iB G,P.walk.edgeSet={e}:=by
 induction e using bJ with
 | _ a b=>have hab:G.Adj a b:=he;let P:k4 G:=⟨a,b,Walk.cons hab Walk.nil,(Walk.IsPath.nil).cons (by simpa using hab.ne),by simp⟩;exact ⟨.qX P,by simp [iB.qX,P]⟩
lemma Br {V:Type sK} [Fintype V] (G:SimpleGraph V):∃P:Fin G.edgeFinset.card->iB G,(Pairwise λ i j=>Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)/\(⋃ i,(P i).walk.edgeSet)=G.edgeSet:=by
 classical
 choose P hP using λ e:G.edgeSet=>Gt G e.val e.property
 let e:G.edgeSet ≃ Fin G.edgeFinset.card:=(equivFin G.edgeSet).trans
  (finCongr (G.card_edgeSet))
 refine ⟨λ i=>P (e.symm i),?_,?_⟩
 ·intro i j hij;rw [hP,hP];exact mK.mpr (λ h=>hij (e.symm.injective (aZ h)))
 ·ext z
  simp only [av,hP,dB];constructor
  ·rintro ⟨i,rfl⟩;exact (e.symm i).property
  ·intro hz;exact ⟨e ⟨z,hz⟩,by simp⟩
lemma EY {V:Type sL} [Fintype V] (G:SimpleGraph V)
  (hdeg:∀v,G.degree v<=1):pK G:=by
 classical
 obtain ⟨P,hd,hc⟩:=Br G;refine ⟨_,P,hd,hc,?_⟩;rw [<-G.sum_degrees_support_eq_twice_card_edges];simpa [lM] using aK (s:=G.support.toFinset)
  (f:=λ v=>G.degree v) (g:=λ _=>1) (λ v _=>hdeg v)
def eD {V:Type sN} (G:SimpleGraph V) (x y:V):SimpleGraph (Option V) where
 Adj a b:=match a,b with
  | some a,some b=>G.Adj a b/\s(a,b)≠s(x,y)
  | none,some b=>b=x\/b=y
  | some a,none=>a=x\/a=y
  | none,none=>False
 symm:=⟨by
  intro a b h;cases a<;>cases b
  ·exact h
  ·exact h
  ·exact h
  ·exact ⟨h.1.symm,by simpa only [bx] using h.2⟩⟩
 loopless:=⟨by
  intro a h;cases a
  ·exact h
  ·exact G.irrefl h.1⟩
@[simp] lemma Hj {V:Type qv} (G:SimpleGraph V) (x y a b:V):(eD G x y).Adj (some a) (some b)↔G.Adj a b/\s(a,b)≠s(x,y):=Iff.rfl
@[simp] lemma vq {V:Type v7} (G:SimpleGraph V) (x y a:V):(eD G x y).Adj none (some a)↔a=x\/a=y:=Iff.rfl
@[simp] lemma B5 {V:Type v8} (G:SimpleGraph V) (x y a:V):(eD G x y).Adj (some a) none↔a=x\/a=y:=Iff.rfl
@[simp] lemma Nd {V:Type v9} (G:SimpleGraph V) (x y:V):¬(eD G x y).Adj none none:=id
def ew {V:Type wc} (G:SimpleGraph V) (x y:V):SimpleGraph (Option V):=(eD G x y).deleteEdges {s(none,some x)}
@[simp] lemma Vc {V:Type we} (G:SimpleGraph V) (x y a b:V):(ew G x y).Adj (some a) (some b)↔G.Adj a b/\s(a,b)≠s(x,y):=by rw [ew,mJ];simp []
@[simp] lemma B6 {V:Type A6} (G:SimpleGraph V) (x y a:V) (hxy:x≠y):(ew G x y).Adj none (some a)↔a=y:=by rw [ew,mJ];simp only [vq,dB,star_inj,Option.some.injEq];aesop
@[simp] lemma J2 {V:Type wj} (G:SimpleGraph V) (x y a:V) (hxy:x≠y):(ew G x y).Adj (some a) none↔a=y:=by rw [(ew G x y).adj_comm,B6 G x y a hxy]
lemma xR {V:Type wm} [Fintype V] (K:SimpleGraph (Option V)) (v:V):K.degree (some v)=(univ.filter (λ u:V=>K.Adj (some v) (some u))).card+if K.Adj (some v) none then 1 else 0:=by
 classical
 rw [<-K.card_neighborFinset_eq_degree,K.neighborFinset_eq_filter,cV,ck,mL];rw [cV,ck];omega
lemma xS {V:Type Ip} [Fintype V] (K:SimpleGraph (Option V)):K.degree none=(univ.filter (λ u:V=>K.Adj none (some u))).card:=by
 classical
 rw [<-K.card_neighborFinset_eq_degree,K.neighborFinset_eq_filter,cV,ck,mL];rw [cV,ck];simp
lemma sP {V:Type Iq} [Fintype V] (G:SimpleGraph V)
  (x y v:V):(univ.filter λ u:V=>(eD G x y).Adj (some v) (some u))=if v=x then (G.neighborFinset v).erase y else
   if v=y then (G.neighborFinset v).erase x else G.neighborFinset v:=by
 classical
 ext u;by_cases hx:v=x
 ·subst v;simp [gH,and_comm];aesop
 ·by_cases hy:v=y
  ·subst v;simp [hx,gH,and_comm];tauto
  ·simp [hx,hy]
lemma tv {V:Type Ir} [Fintype V] (G:SimpleGraph V)
  (x y v:V) (hxy:G.Adj x y):(eD G x y).degree (some v)=G.degree v:=by
 classical
 rw [xR,sP];by_cases hx:v=x
 ·subst v
  simpa using jg (s:=G.neighborFinset x) (a:=y)
   (by simpa using hxy)
 ·by_cases hy:v=y
  ·subst v
   simpa [hx] using jg (s:=G.neighborFinset y) (a:=x)
    (by simpa using hxy.symm)
  ·simp [hx,hy]
lemma uq {V:Type It} [Fintype V] (G:SimpleGraph V)
  (x y:V) (hxy:G.Adj x y):(eD G x y).degree none=2:=by
 classical
 rw [xS];have he:(univ.filter λ u:V=>(eD G x y).Adj none (some u))={x,y}:=by ext u;simp
 rw [he];simp [hxy.ne]
lemma Bs {V:Type Iu} [Fintype V] (G:SimpleGraph V)
  (x y v:V) (hxy:G.Adj x y):(ew G x y).degree (some v)+(if v=x then 1 else 0)=G.degree v:=by
 classical
 rw [xR];have he:(univ.filter λ u:V=>(ew G x y).Adj (some v) (some u))=(univ.filter λ u:V=>(eD G x y).Adj (some v) (some u)):=by ext u;simp
 rw [he,sP];by_cases hx:v=x
 ·subst v
  simpa [hxy.ne] using jg (s:=G.neighborFinset x) (a:=y)
   (by simpa using hxy)
 ·by_cases hy:v=y
  ·subst v
   simpa [hx,hxy.ne] using jg (s:=G.neighborFinset y) (a:=x)
    (by simpa using hxy.symm)
  ·simp [hx,hy,J2 G x y v hxy.ne]
lemma Ho {V:Type Iv} [Fintype V] (G:SimpleGraph V)
  (x y:V) (hxy:G.Adj x y):(ew G x y).degree none=1:=by
 classical
 rw [xS];have he:(univ.filter λ u:V=>(ew G x y).Adj none (some u))={y}:=by ext u;simp [B6 G x y u hxy.ne]
 rw [he];simp
lemma Bt {V:Type Iw} [Fintype V] (G:SimpleGraph V)
  (x y:V) (hxy:G.Adj x y):(eD G x y).edgeFinset.card=G.edgeFinset.card+1:=by
 classical
 have hd:=(eD G x y).sum_degrees_eq_twice_card_edges;rw [mL,uq G x y hxy] at hd;simp_rw [tv G x y _ hxy] at hd;rw [G.sum_degrees_eq_twice_card_edges] at hd;omega
lemma I9 {V:Type Ix} [Fintype V] (G:SimpleGraph V)
  (x y:V) (hxy:G.Adj x y):(ew G x y).edgeFinset.card=G.edgeFinset.card:=by
 classical
 have he:(ew G x y).edgeFinset=(eD G x y).edgeFinset.erase s(none,some x):=by ext e;rw [(ew G x y).mem_edgeFinset,iK,(eD G x y).mem_edgeFinset];simp [ew,g8,and_comm]
 rw [he,oL,Bt G x y hxy]
 ·omega
 ·exact (eD G x y).mem_edgeFinset.mpr (Or.inl rfl)
lemma AD {V:Type Iy} [Fintype V] (G:SimpleGraph V)
  (x y:V) (hxy:G.Adj x y):lM (eD G x y)=lM G+1:=by
 classical
 have he:(eD G x y).support.toFinset=insert none (G.support.toFinset.image Option.some):=by
  ext v;cases v with
  | none=>simp [<-degree_pos_iff_mem_support,uq G x y hxy]
  | some v=>simp only [jc,bU,oM,bk,Option.some.injEq,false_or,exists_eq_right];rw [<-(eD G x y).degree_pos_iff_mem_support,tv G x y v hxy,G.degree_pos_iff_mem_support]
 dsimp [lM];rw [he,nW,gI]
 ·exact mO V
 ·simp
lemma KM {V:Type Iz} (G:SimpleGraph V) (x y:V) (hxy:G.Adj x y)
  {a b:V} (p:(eD G x y).Walk (some a) (some b)) (hp:p.IsPath):∃q:G.Walk a b,q.IsPath/\q.support=p.support.filterMap id/\∀e:Sym2 V,e∈q.edgeSet↔e.map Option.some∈p.edgeSet\/(e=s(x,y)/\s(none,some x)∈p.edgeSet):=by
 classical
 generalize hn:p.length=n;induction n using jh generalizing a b with
 | h n ih=>
   cases p with
   | nil=>refine ⟨.nil,by simp,by simp,?_⟩;intro e;simp
   | @cons _ v _ h p=>
     have ht:p.IsPath:=hp.of_cons;have ha:some a∉p.support:=(Walk.cons_isPath_iff _ _ |>.mp hp).2;cases v with
     | some c=>
       obtain ⟨q,hq,OF,EV⟩:=ih p.length (by simp only [Walk.length_cons] at hn;omega) p ht rfl;have hac:G.Adj a c:=(Hj G x y a c).mp h |>.1;refine ⟨.cons hac q,hq.cons ?_,?_,?_⟩
       ·intro ha';apply ha;rw [OF] at ha';simpa using ha'
       ·simp [OF]
       ·intro e
        have hinj:Function.Injective (Sym2.map (Option.some:V->Option V)):=fI (mO V);have he:e.map Option.some=s(some a,some c)↔e=s(a,c):=by simpa only [Sym2.map_mk] using (hinj.eq_iff (a:=e) (b:=s(a,c)))
        have Sd:s(none,some x)≠s(some a,some c):=by simp []
        simp only [Walk.edgeSet_cons,eI,he,Sd,false_or,EV];tauto
     | none=>
       cases p with
       | @cons _ v _ h' p=>
         cases v with
         | none=>exact (h'.ne rfl).elim
         | some c=>
           have hac:a≠c:=by intro he;apply ha;simp [he]
           have hae:a=x\/a=y:=(B5 G x y a).mp h;have P8:c=x\/c=y:=(vq G x y c).mp h';have Se:s(a,c)=s(x,y):=by
            rcases hae with rfl | rfl<;>rcases P8 with rfl | rfl
            ·exact (hac rfl).elim
            ·rfl
            ·exact bx
            ·exact (hac rfl).elim
           have Wi:G.Adj a c:=G.mem_edgeSet.mp (Se.symm▸hxy);obtain ⟨q,hq,OF,EV⟩:=ih p.length (by simp only [Walk.length_cons] at hn;omega) p ht.of_cons rfl;refine ⟨.cons Wi q,hq.cons ?_,?_,?_⟩
           ·intro ha'
            apply ha;have hh:some a∈p.support:=by rw [OF] at ha';simpa using ha'
            simp [hh]
           ·simp [OF]
           ·intro e
            have Ow:e.map Option.some≠s(some a,none):=by induction e using i8 with | _ u v=>simp []
            have Kp:e.map Option.some≠s(none,some c):=by induction e using i8 with | _ u v=>simp []
            have hn:s(none,some x)=s(some a,none)\/s(none,some x)=s(none,some c):=by
             rcases hae with rfl | hay
             ·exact Or.inl bx
             ·rcases P8 with rfl | OG
              ·exact Or.inr rfl
              ·exact (hac (hay.trans OG.symm)).elim
            simp only [Walk.edgeSet_cons,eI,Ow,Kp,false_or,Se,EV];tauto
lemma zh {V:Type ID} {I:Type IE} [Fintype V] [Fintype I]
  (G:SimpleGraph V) (P:I->iB G) (S:Finset V)
  (hd:Pairwise λ i j=>Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
  (hc:(⋃ i,(P i).walk.edgeSet)=G.edgeSet)
  (ho:∀v∈S,Odd (G.degree v)) (hk:2*card I<=S.card):∀i,(P i).start≠(P i).finish/\(P i).start∈S/\(P i).finish∈S:=by
 classical
 let fH:I×Bool->V:=λ z=>if z.2 then (P z.1).start else (P z.1).finish
 have he:∀v:S,∃z:I×Bool,fH z=v:=by
  intro v;obtain ⟨i,_,h | h⟩:=A8 G P hd hc v (ho v v.property)
  ·exact ⟨(i,true),h⟩
  ·exact ⟨(i,false),h⟩
 choose pick K9 using he;have hinj:Function.Injective pick:=by intro v w DN;apply aZ;exact (K9 v).symm.trans ((aF fH DN).trans (K9 w))
 have NX:Function.Surjective pick:=by by_contra hn;have hh:=card_lt_of_injective_not_surjective pick hinj hn;simp only [eG,card_prod,card_bool] at hh;omega
 have Q0:Function.Injective fH:=by intro z t heq;obtain ⟨v,rfl⟩:=NX z;obtain ⟨w,rfl⟩:=NX t;have DN:v=w:=aZ (by simpa only [K9] using heq);exact aF pick DN
 have hmem:∀z,fH z∈S:=by intro z;obtain ⟨v,rfl⟩:=NX z;rw [K9];exact v.property
 intro i;refine ⟨?_,hmem (i,true),hmem (i,false)⟩;intro heq;have hh:= Q0 (show fH (i,true)=fH (i,false) from heq);have:=aF Prod.snd hh;contradiction
def kh {V:Type IG} (x y:V) (e:Sym2 V):Sym2 (Option V):=if e=s(x,y) then s(none,some x) else e.map Option.some
lemma EZ {V:Type IL} (G:SimpleGraph V) (x y:V) (aaB:G.Adj x y)
  (e:Sym2 V) (he:e∈G.edgeSet):kh x y e∈(eD G x y).edgeSet:=by
 classical
 by_cases h:e=s(x,y)
 ·simp [kh,h]
 ·rw [kh,if_neg h]
  induction e using bJ with
  | _ a b=>exact ⟨he,h⟩
lemma J3 {V:Type IQ} (G:SimpleGraph V) (x y:V) (hxy:G.Adj x y)
  (P:iB (eD G x y)) (hne:P.start≠P.finish)
  (ha:P.start≠none) (hb:P.finish≠none):∃Q:iB G,∀e,e∈Q.walk.edgeSet↔kh x y e∈P.walk.edgeSet:=by
 classical
 rcases P with ⟨a,b,p,hp⟩;cases a with
 | none=>exact (ha rfl).elim
 | some a=>
   cases b with
   | none=>exact (hb rfl).elim
   | some b=>
     have hab:a≠b:=λ h=>hne (aF some h)
     have F9:p.IsPath:=by
      rcases hp with h | ⟨h,_⟩
      ·exact h.1
      ·exact (hne h.symm).elim
     obtain ⟨q,hq,_,EV⟩:=KM G x y hxy p F9;have j4:0<q.length:=by by_contra hn;exact hab (Walk.eq_of_length_eq_zero (by omega:q.length=0))
     refine ⟨.qX ⟨a,b,q,hq,j4⟩,?_⟩;intro e;change e∈q.edgeSet↔_;rw [EV];by_cases he:e=s(x,y)
     ·subst e
      have hn:(s(x,y):Sym2 V).map some∉p.edgeSet:=by intro h;have hh:=p.edges_subset_edgeSet h;exact hh.2 rfl
      simp only [kh,ite_true,hn,false_or,b5]
     ·simp [kh,he]
lemma E0 {V:Type IS} {I:Type IT} [Fintype I]
  (G:SimpleGraph V) (x y:V) (hxy:G.Adj x y)
  (P:I->iB (eD G x y))
  (hd:Pairwise λ i j=>Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
  (hc:(⋃ i,(P i).walk.edgeSet)=(eD G x y).edgeSet)
  (hp:∀i,(P i).start≠(P i).finish/\(P i).start≠none/\(P i).finish≠none):∃Q:I->iB G,(Pairwise λ i j=>Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet)/\(⋃ i,(Q i).walk.edgeSet)=G.edgeSet:=by
 classical
 choose Q hQ using λ i=>J3 G x y hxy (P i) (hp i).1 (hp i).2.1 (hp i).2.2
 refine ⟨Q,?_,?_⟩
 ·intro i j hij;exact aI.mpr λ e hei yP=>aI.mp (hd hij) ((hQ i e).mp hei) ((hQ j e).mp yP)
 ·apply mW
  ·exact gJ λ i=>(Q i).walk.edges_subset_edgeSet
  ·intro e he;have hrep:=EZ G x y hxy e he;rw [<-hc] at hrep;obtain ⟨i,hi⟩:=av.mp hrep;exact av.mpr ⟨i,(hQ i e).mpr hi⟩
lemma Hr {V:Type IU} [Fintype V] (G:SimpleGraph V)
  (ho:∀v,0<G.degree v->Odd (G.degree v)):Even (lM G):=by
 classical
 have he:G.support.toFinset=univ.filter (λ v=>Odd (G.degree v)):=by ext v;simp only [jc,aD,aQ,b5,<-G.degree_pos_iff_mem_support];refine ⟨ho v,?_⟩;rintro ⟨k,hk⟩;omega
 simpa only [lM,he] using G.even_card_odd_degree_vertices
lemma LR {V:Type IV} {I:Type IW} [Fintype V] [Fintype I]
  (G:SimpleGraph V) (x y:V) (hxy:G.Adj x y)
  (ho:∀v,0<G.degree v->Odd (G.degree v))
  (P:I->iB (ew G x y))
  (hd:Pairwise λ i j=>Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
  (hc:(⋃ i,(P i).walk.edgeSet)=(ew G x y).edgeSet):∃Q:I->iB (eD G x y),(Pairwise λ i j=>Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet)/\(⋃ i,(Q i).walk.edgeSet)=(eD G x y).edgeSet:=by
 classical
 have he:{e:Sym2 (Option V) | ∃v∈({none}:Set (Option V)),e=s(some x,v)}={s(none,some x)}:=by ext e;simp [bx]
 apply yS (eD G x y) (ew G x y)
  ((eD G x y).deleteEdges_le _) (some x) {none}
  (by intro v hv;rcases hv with rfl;exact Or.inl rfl) ?_ ?_ ?_ P hd hc
 ·rw [he,ew,g8];symm;apply mo;intro e he;rcases he with rfl;exact Or.inl rfl
 ·rw [he,ew,g8];exact Set.disjoint_sdiff_right
 ·intro v hv
  cases v with
  | none=>rw [Ho G x y hxy];exact ⟨0,rfl⟩
  | some v=>have hxv:G.Adj x v:=hv.1;have hh:=Bs G x y v hxy;rw [if_neg hxv.ne.symm,fq] at hh;rw [hh];exact ho v ((G.degree_pos_iff_exists_adj v).mpr ⟨x,hxv.symm⟩)
lemma Ja {V:Type IX} [Fintype V] (G:SimpleGraph V)
  (Sb:∀H:SimpleGraph (Option V),H.edgeFinset.card<G.edgeFinset.card->pK H)
  (ho:∀v,0<G.degree v->Odd (G.degree v)) (x:V) (hx:3<=G.degree x):pK G:=by
 classical
 obtain ⟨y,hxy⟩:=(G.degree_pos_iff_exists_adj x).mp (by omega);have hp:∃v,0<(ew G x y).degree v/\Even ((ew G x y).degree v):=by
  refine ⟨some x,?_,?_⟩
  ·have hd:=Bs G x y x hxy;simp only [ite_true] at hd;omega
  ·have hd:=Bs G x y x hxy;simp only [ite_true] at hd;obtain ⟨k,hk⟩:=ho x (by omega);exact ⟨k,by omega⟩
 obtain ⟨k,P,hd,hc,hk⟩:=zY (ew G x y)
  (λ H hh=>Sb H (by rwa [I9 G x y hxy] at hh)) hp
 have hbound:2*k<=lM G+1:=by have hm:=zX ((eD G x y).deleteEdges_le {s(none,some x)});rw [AD G x y hxy] at hm;exact hk.trans hm
 have hk':2*k<=lM G:=by obtain ⟨a,ha⟩:=Hr G ho;omega
 obtain ⟨Q,hQ,Ks⟩:=LR G x y hxy ho P hd hc;let S:=G.support.toFinset.image Option.some;have LS:S.card=lM G:=by exact gI _ (mO V)
 have TY:∀v∈S,Odd ((eD G x y).degree v):=by intro v hv;obtain ⟨w,hw,rfl⟩:=bk.mp hv;rw [tv G x y w hxy];exact ho w ((G.degree_pos_iff_mem_support w).mpr (jc.mp hw))
 have qL:=zh (eD G x y) Q S hQ Ks TY
  (by simpa only [dU,LS] using hk')
 have JQ:∀i,(Q i).start≠(Q i).finish/\(Q i).start≠none/\(Q i).finish≠none:=by
  intro i;refine ⟨(qL i).1,?_,?_⟩
  ·intro h;have hh:=(qL i).2.1;simp only [h,S,bk,oM,and_false,exists_false] at hh
  ·intro h;have hh:=(qL i).2.2;simp only [h,S,bk,oM,and_false,exists_false] at hh
 obtain ⟨R,hR,XU⟩:=E0 G x y hxy Q hQ Ks JQ;exact ⟨k,R,hR,XU,hk'⟩
lemma Di {V:Type u} [Fintype V] (G:SimpleGraph V):pK G:=by
 classical
 suffices ∀(n:ℕ) (W:Type u) [Fintype W] (H:SimpleGraph W),H.edgeFinset.card=n->pK H by exact this G.edgeFinset.card V G rfl
 intro n;induction n using jh with
 | h n ih=>
   intro W _ H B0;by_cases he:∃v,0<H.degree v/\Even (H.degree v)
   ·exact zY H (λ K hk=>ih K.edgeFinset.card (by omega) W K rfl) he
   ·have ho:∀v,0<H.degree v->Odd (H.degree v):=by
     intro v hv;exact jf.mp (λ A5=>he ⟨v,hv,A5⟩)
    by_cases hm:∀v,H.degree v<=1
    ·exact EY H hm
    ·push Not at hm
     obtain ⟨x,hx⟩:=hm;have XV:3<=H.degree x:=by obtain ⟨k,hk⟩:=ho x (by omega);omega
     exact Ja H
      (λ K hk=>ih K.edgeFinset.card (by omega) (Option W) K rfl) ho x XV
end
end af.cI
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX gu gX iN iO i7 jD jV jW jX kB jY kC kD kE kF jZ j0 lC lT lU oA n4 n5
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af
open aR.af.aV
open aR.af.Splitting
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
structure iz {V:Type bX} (G:SimpleGraph V) where
 start:V
 finish:V
 walk:G.Walk start finish
 isPath:walk.IsPath
 positive:0<walk.length
lemma iz.E3 {V:Type bY} {G:SimpleGraph V}
  (P:iz G):P.start≠P.finish:=by
 intro he;have hz:=P.isPath.nil_iff_eq.mpr he;have:=hz.length_eq_zero;have:=P.positive;omega
lemma Ed {V:Type cy} {I:Type cz} [Fintype V] [Fintype I]
  {G:SimpleGraph V} (P:I->iz G)
  (lG:∀v:V,(univ.filter
   (λ i=>(P i).start=v\/(P i).finish=v)).card<=2):
  card I<=card V:=by
 classical
 have hsum:(∑v:V,(univ.filter
   (λ i=>(P i).start=v\/(P i).finish=v)).card)=2*card I:=by
  simp only [cV,ck];rw [gD];have heq:∀i:I,(∑v:V,if (P i).start=v\/(P i).finish=v then 1 else 0)=2:=by
   intro i;have hf:(univ.filter λ v=>
     (P i).start=v\/(P i).finish=v)={(P i).start,(P i).finish}:=by
    ext v;simp [gH]
   have hc:({(P i).start,(P i).finish}:Finset V).card=2:=by simp [(P i).E3]
   rw [<-hc,<-hf,cV,ck]
  simp only [heq,d5,c7,jJ];omega
 have hbound:=aK (λ v (_:v∈(univ:Finset V))=>lG v);rw [hsum] at hbound;simp only [d5,c7,jJ] at hbound;omega
def kA {V:Type cP} [Fintype V] (G:SimpleGraph V):Prop:=∃(k:ℕ) (P:Fin k->iz G),Pairwise (λ i j=>Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)/\(⋃ i,(P i).walk.edgeSet)=G.edgeSet/\(∀v:V,(univ.filter (λ i=>(P i).start=v\/(P i).finish=v)).card<=2)/\k<=card V
def E4 {V:Type cL} (G:SimpleGraph V)
  (s:Set (Sym2 V)):Prop:=(∃(a b:V) (p:G.Walk a b),p.IsPath/\0<p.length/\s=p.edgeSet)\/(∃(a:V) (p:G.Walk a a),p.IsCycle/\s=p.edgeSet)
def tw {V:Type c9} [Fintype V] (G:SimpleGraph V):Prop:=∃(k:ℕ) (parts:Fin k->Set (Sym2 V)),(∀i,E4 G (parts i))/\Pairwise (λ i j=>Disjoint (parts i) (parts j))/\(⋃ i,parts i)=G.edgeSet/\2*k<=card V
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
open scoped BigOperators
def iS {V:Type dW} [Fintype V] (G:SimpleGraph V):SimpleGraph (Option V) where
 Adj x y:=match x,y with
  | some u,some v=>G.Adj u v
  | none,some v=>Even (G.degree v)
  | some u,none=>Even (G.degree u)
  | none,none=>False
 symm:=⟨by
  intro x y h;cases x<;>cases y
  ·exact h
  ·exact h
  ·exact h
  ·exact G.adj_symm h⟩
 loopless:=⟨by
  intro x h;cases x
  ·exact h
  ·exact G.irrefl h⟩
@[simp] theorem zi {V:Type eo} [Fintype V]
 (G:SimpleGraph V) (u v:V):(iS G).Adj (some u) (some v)↔G.Adj u v:=Iff.rfl
@[simp] theorem La {V:Type d7} [Fintype V]
 (G:SimpleGraph V) (v:V):(iS G).Adj none (some v)↔Even (G.degree v):=Iff.rfl
@[simp] theorem yE {V:Type d8} [Fintype V]
 (G:SimpleGraph V) (v:V):(iS G).Adj (some v) none↔Even (G.degree v):=Iff.rfl
lemma AG {V:Type d9} [Fintype V]
  (G:SimpleGraph V) (v:V):(iS G).degree (some v)=G.degree v+if Even (G.degree v) then 1 else 0:=by
 classical
 rw [degree,neighborFinset_eq_filter,cV,ck,mL];simp only [zi,yE];have he:(∑u:V,if G.Adj v u then 1 else 0)=G.degree v:=by rw [<-G.card_neighborFinset_eq_degree v,G.neighborFinset_eq_filter,cV,ck]
 rw [he];omega
lemma zZ {V:Type eO} [Fintype V]
  (G:SimpleGraph V) (v:V):Odd ((iS G).degree (some v)):=by
 rw [AG];by_cases h:Even (G.degree v)
 ·simp only [h,↓reduceIte];rcases h with ⟨k,hk⟩;exact ⟨k,by omega⟩
 ·simpa [h] using jf.mp h
end
end af
namespace af
open aR.af.aV
open aR.af.Splitting
section
open scoped BigOperators
local instance (p:Prop):Decidable p:=Classical.propDecidable p
open aR.af.cI
private lemma LU {V:Type iO} [DecidableEq V]
  (S:Finset V) (f:V->ℕ) (ho:∀v∈S,Odd (f v))
  (hs:∑v∈S,f v<=S.card+1):∀v∈S,f v=1:=by
 intro v hv;by_contra hn;have XW:3<=f v:=by rcases ho v hv with ⟨k,hk⟩;omega
 have EK:∑x∈S,(1+if x=v then 2 else 0)<=∑x∈S,f x:=by
  apply aK;intro x hx;by_cases he:x=v
  ·subst x;simpa using XW
  ·simp only [he,↓reduceIte,fq];rcases ho x hx with ⟨k,hk⟩;omega
 have heq:(∑x∈S,(1+if x=v then 2 else 0))=S.card+2:=by simp [f8,hv]
 omega
lemma zj {V:Type i7} {I:Type jD} [Fintype V] [Fintype I]
  (G:SimpleGraph V) (S:Finset V) {a b:I->V}
  (p:∀i,G.Walk (a i) (b i)) (ht:∀i,(p i).IsTrail)
  (hd:Pairwise λ i j=>Disjoint (p i).edgeSet (p j).edgeSet)
  (hc:(⋃ i,(p i).edgeSet)=G.edgeSet)
  (ho:∀v∈S,Odd (G.degree v))
  (u6:2*card I<=S.card+1):(∀i,a i≠b i)/\(∀v∈S,(univ.filter (λ i=>a i≠b i/\(v=a i\/v=b i))).card=1):=by
 classical
 let load:=λ v:V=>(univ.filter
  (λ i=>a i≠b i/\(v=a i\/v=b i))).card
 let tA:=univ.filter (λ i=>a i≠b i);have P9:∀v∈S,Odd (load v):=by intro v hv;rw [<-jf,<-pV G p ht hd hc v];exact (jf.mpr (ho v hv))
 have Lx:(∑v:V,load v)=2*tA.card:=by
  dsimp [load];simp only [cV,ck];rw [gD];have he:∀i:I,(∑v:V,if a i≠b i/\(v=a i\/v=b i) then 1 else 0)=if a i≠b i then 2 else 0:=by
   intro i;by_cases h:a i=b i
   ·simp [h]
   ·have hf:(univ.filter (λ v=>a i≠b i/\(v=a i\/v=b i)))={a i,b i}:=by ext v;simp [h]
    have lN:({a i,b i}:Finset V).card=2:=by simp [h]
    rw [ej h,<-lN,<-hf,cV,ck]
  simp_rw [he];rw [<-ck];simp only [d5,jJ,mul_one];change tA.card*2=2*tA.card;omega
 have hsub:(∑v∈S,load v)<=∑v:V,load v:=sum_le_sum_of_subset (gS S);have EK:S.card<=∑v∈S,load v:=by
  simpa using aK (s:=S) (f:=λ _=>1) (g:=load)
   (λ v hv=>by rcases P9 v hv with ⟨k,hk⟩;omega)
 have B0:tA.card<=card I:=e4 _;have Sg:=LU S load P9 (by omega);refine ⟨?_,Sg⟩;intro i hi;have Q1:tA⊂univ:=by apply oK.mpr;refine ⟨gS _,?_⟩;intro heq;have hh:i∈tA:=heq.symm▸aQ i;simp [tA,hi] at hh
 have hlt:=oJ Q1;simp only [c7] at hlt;omega
end
end af
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
private lemma uQ {V:Type jV} {G:SimpleGraph V}
  {a b:V} (p:G.Walk a b) (hp:p.IsPath):p.tail.edgeSet={e | e∈p.edgeSet/\a∉e}:=by
 cases p with
 | nil=>ext e;simp
 | @cons a c b h q=>
   have ha:a∉q.support:=(i9.mp hp.support_nodup).1;have hnot:∀e∈q.edgeSet,a∉e:=by
    intro e he hae;exact ha (rU.mpr
     (Or.inr ⟨e,he,hae⟩))
   ext e;simp only [fo,SimpleGraph.Walk.mem_edgeSet,SimpleGraph.Walk.edges_tail,SimpleGraph.Walk.edges_cons,mC,dd];constructor
   ·intro he;exact ⟨Or.inr he,hnot e he⟩
   ·rintro ⟨he | he,hn⟩
    ·subst e;exact (hn (by simp)).elim
    ·exact he
private lemma z3 {V:Type jW} {G:SimpleGraph V}
  {a b:V} (p:G.Walk a b) (hp:p.IsPath):p.dropLast.edgeSet={e | e∈p.edgeSet/\b∉e}:=by
 have he:p.dropLast.edgeSet=p.reverse.tail.edgeSet:=by
  calc
   _=p.dropLast.reverse.edgeSet:=(SimpleGraph.Walk.edgeSet_reverse _).symm
   _=_:=by rw [SimpleGraph.Walk.reverse_dropLast,SimpleGraph.Walk.edgeSet_copy]
 rw [he,uQ p.reverse hp.reverse,SimpleGraph.Walk.edgeSet_reverse]
private lemma pW {V:Type jX} {G:SimpleGraph V}
  {a b v:V} (p:G.Walk a b) (j4:0<p.length)
  (he:∀e∈p.edgeSet,v∉e):v∉p.support:=by
 have hn:¬p.Nil:=by intro hz;have:=hz.length_eq_zero;omega
 intro hv;obtain ⟨e,he',Oz⟩:=rT hn |>.mp hv;exact he e he' Oz
lemma kK {V:Type kB} [DecidableEq V] {G:SimpleGraph V}
  {a b v:V} (p:G.Walk a b) (hp:p.IsPath) (hv:v∈p.support):let q:=(p.takeUntil v hv).dropLast
  let r:=(p.dropUntil v hv).tail
  q.IsPath/\r.IsPath/\Disjoint q.edgeSet r.edgeSet/\q.edgeSet∪r.edgeSet={e | e∈p.edgeSet/\v∉e}/\(0<q.length->v∉q.support)/\(0< r.length->v∉r.support)/\(0<q.length->G.Adj (p.takeUntil v hv).penultimate v)/\(0< r.length->G.Adj v (p.dropUntil v hv).snd):=by
 dsimp only;let t:=p.takeUntil v hv;let d:=p.dropUntil v hv;have ht:t.IsPath:=hp.takeUntil hv;have hd:d.IsPath:=hp.dropUntil hv;have heq:t.append d=p:=p.take_spec hv;have EV:t.dropLast.edgeSet={e | e∈t.edgeSet/\v∉e}:=z3 t ht;have Sh:d.tail.edgeSet={e | e∈d.edgeSet/\v∉e}:=uQ d hd;have hdis:Disjoint t.edgeSet d.edgeSet:=by have hn:=hp.isTrail.edges_nodup;rw [<-heq,oF] at hn;have hn':=(fJ.mp hn).2.2;apply aI.mpr;intro e het DT;exact hn' e het e DT rfl
 refine ⟨ht.dropLast,hd.tail,?_,?_,?_,?_,?_,?_⟩
 ·rw [EV,Sh];exact hdis.mono (λ _ h=>h.1) (λ _ h=>h.1)
 ·have he:t.edgeSet∪d.edgeSet=p.edgeSet:=by
   rw [<-oN,heq]
  rw [EV,Sh];ext e;simp only [b8,fo];rw [<-he];simp only [b8];tauto
 ·intro j4;apply pW _ j4;intro e he;exact (EV▸he).2
 ·intro j4;apply pW _ j4;intro e he;exact (Sh▸he).2
 ·intro j4;apply t.adj_penultimate;intro hn;have hz:=hn.length_eq_zero;change 0<t.dropLast.length at j4;rw [oO,hz] at j4;omega
 ·intro j4;apply d.adj_snd;intro hn;have hz:=hn.length_eq_zero;change 0<d.tail.length at j4;rw [oP,hz] at j4;omega
lemma lP {V:Type jY} [DecidableEq V]
  {G:SimpleGraph V} {a b v:V} (p:G.Walk a b) (hv:v∈p.support):(0<(p.takeUntil v hv).dropLast.length->s((p.takeUntil v hv).penultimate,v)∈p.edgeSet)/\
  (0<(p.dropUntil v hv).tail.length->s(v,(p.dropUntil v hv).snd)∈p.edgeSet):=by
 let t:=p.takeUntil v hv;let d:=p.dropUntil v hv;have heq:t.append d=p:=p.take_spec hv;constructor
 ·intro j4
  have hn:¬t.Nil:=by intro hz;change 0<t.dropLast.length at j4;rw [oO,hz.length_eq_zero] at j4;omega
  have hm:=t.mk_penultimate_end_mem_edges hn;have DT:t.edgeSet∪d.edgeSet=p.edgeSet:=by rw [<-oN,heq]
  exact DT▸Or.inl hm
 ·intro j4
  have hn:¬d.Nil:=by intro hz;change 0<d.tail.length at j4;rw [oP,hz.length_eq_zero] at j4;omega
  have hm:=d.mk_start_snd_mem_edges hn;have DT:t.edgeSet∪d.edgeSet=p.edgeSet:=by rw [<-oN,heq]
  exact DT▸Or.inr hm
lemma sS {V:Type kC} [DecidableEq V]
  {G:SimpleGraph V} {a b v:V} (p:G.Walk a b) (hp:p.IsPath)
  (hv:v∈p.support)
  (hl:0<(p.takeUntil v hv).dropLast.length)
  (hr:0<(p.dropUntil v hv).tail.length):(p.takeUntil v hv).penultimate≠(p.dropUntil v hv).snd:=by
 let t:=p.takeUntil v hv;let d:=p.dropUntil v hv;have heq:t.append d=p:=p.take_spec hv;have XX:¬t.Nil:=by intro hz;change 0<t.dropLast.length at hl;rw [oO,hz.length_eq_zero] at hl;omega
 have XY:¬d.Nil:=by intro hz;change 0<d.tail.length at hr;rw [oP,hz.length_eq_zero] at hr;omega
 have PL:=hp.isTrail.edges_nodup;rw [<-heq,oF] at PL;have hdis:=(fJ.mp PL).2.2;intro zc;have ha:=t.mk_penultimate_end_mem_edges XX;have hb:=d.mk_start_snd_mem_edges XY;apply hdis _ ha _ hb;rw [show t.penultimate=d.snd from zc,bx]
lemma vN {V:Type kD} {I:Type kE} [DecidableEq V] [Fintype I]
  {G:SimpleGraph V} {a b:I->V} {v:V}
  (p:∀i,G.Walk (a i) (b i)) (hp:∀i,(p i).IsPath)
  (hv:∀i,v∈(p i).support)
  (hd:Pairwise λ i j=>Disjoint (p i).edgeSet (p j).edgeSet) (x:V):let Wj:=λ z:I×Bool=>if z.2 then
   0<((p z.1).takeUntil v (hv z.1)).dropLast.length else
   0<((p z.1).dropUntil v (hv z.1)).tail.length
  let z4:=λ z:I×Bool=>if z.2 then
   ((p z.1).takeUntil v (hv z.1)).penultimate else
   ((p z.1).dropUntil v (hv z.1)).snd
  (univ.filter λ z=>Wj z/\z4 z=x).card<=1:=by
 classical
 dsimp only;apply jK.mpr;intro z hz w hw;obtain ⟨i,bi⟩:=z;obtain ⟨j,bj⟩:=w;have hi:=(aD.mp hz).2;have hj:=(aD.mp hw).2;have hei:s(v,x)∈(p i).edgeSet:=by
  cases bi
  ·have hx:((p i).dropUntil v (hv i)).snd=x:=hi.2;simpa only [hx] using (lP (p i) (hv i)).2 hi.1
  ·have hx:((p i).takeUntil v (hv i)).penultimate=x:=hi.2;have he:=(lP (p i) (hv i)).1 hi.1;simpa only [hx,bx] using he
 have yP:s(v,x)∈(p j).edgeSet:=by
  cases bj
  ·have hx:((p j).dropUntil v (hv j)).snd=x:=hj.2;simpa only [hx] using (lP (p j) (hv j)).2 hj.1
  ·have hx:((p j).takeUntil v (hv j)).penultimate=x:=hj.2;have he:=(lP (p j) (hv j)).1 hj.1;simpa only [hx,bx] using he
 have hij:i=j:=by by_contra hn;exact aI.mp (hd hn) hei yP
 subst j;congr 1;cases bi<;>cases bj
 ·rfl
 ·have he:=sS (p i) (hp i) (hv i) hj.1 hi.1;exact (he (hj.2.trans hi.2.symm)).elim
 ·have he:=sS (p i) (hp i) (hv i) hi.1 hj.1;exact (he (hi.2.trans hj.2.symm)).elim
 ·rfl
structure cK {V:Type kF} (G:SimpleGraph V) where
 start:V
 finish:V
 walk:G.Walk start finish
 isPath:walk.IsPath
namespace cK
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type jZ} {I:Type j0} [Fintype I] [DecidableEq V] {G:SimpleGraph V}
def Hu (p:I->cK G) (v:V):={i:I // v∉(p i).walk.support}
def Ga (p:I->cK G) (v:V):={i:I // v∈(p i).walk.support}
def gM (p:I->cK G) (v:V):=Hu p v ⊕ (Ga p v×Bool)
instance (p:I->cK G) (v:V):Fintype (Hu p v):=by
 classical
 exact inferInstanceAs (Fintype {i:I // v∉(p i).walk.support})
instance (p:I->cK G) (v:V):Fintype (Ga p v):=by
 classical
 exact inferInstanceAs (Fintype {i:I // v∈(p i).walk.support})
instance (p:I->cK G) (v:V):Fintype (gM p v):=inferInstanceAs (Fintype (Hu p v ⊕ (Ga p v×Bool)))
def fZ (p:I->cK G) (v:V):gM p v->cK G
 | .inl i=>p i.val
 | .inr (i,true)=>⟨_,_,((p i.val).walk.takeUntil v i.property).dropLast,((p i.val).isPath.takeUntil i.property).dropLast⟩
 | .inr (i,false)=>⟨_,_,((p i.val).walk.dropUntil v i.property).tail,((p i.val).isPath.dropUntil i.property).tail⟩
def parent (p:I->cK G) (v:V):gM p v->I
 | .inl i=>i.val
 | .inr (i,_)=>i.val
def E5 (p:I->cK G) (v x:V):gM p v->Prop
 | .inl i=>(p i.val).start=x\/(p i.val).finish=x
 | .inr (i,true)=>(p i.val).start=x
 | .inr (i,false)=>(p i.val).finish=x
def z4 (p:I->cK G) (v x:V):gM p v->Prop
 | .inl _=>False
 | .inr (i,true)=>((p i.val).walk.takeUntil v i.property).penultimate=x
 | .inr (i,false)=>((p i.val).walk.dropUntil v i.property).snd=x
lemma LV {V:Type lC} {I:Type lT} [aO:Fintype I] [kr:DecidableEq V] {G:SimpleGraph V} (p:I->cK G) (v x:V) (j:gM p v):(fZ p v j).start=x\/(fZ p v j).finish=x↔E5 p v x j\/z4 p v x j:=by
 rcases j with i | ⟨i,b⟩
 ·simp [fZ,E5,z4]
 ·cases b<;>simp [fZ,E5,z4,or_comm]
lemma rJ {V:Type lU} {I:Type oA} [aO:Fintype I] [kr:DecidableEq V] {G:SimpleGraph V} (p:I->cK G) (v:V) (j:gM p v):(fZ p v j).walk.edgeSet⊆(p (parent p v j)).walk.edgeSet:=by
 rcases j with i | ⟨i,b⟩
 ·exact Set.Subset.rfl
 ·have h:=(kK (p i.val).walk (p i.val).isPath i.property).2.2.2.1
  cases b
  ·intro e he
   exact (show e∈{e | e∈(p i.val).walk.edgeSet/\v∉e} from
    h▸Or.inr he).1
  ·intro e he
   exact (show e∈{e | e∈(p i.val).walk.edgeSet/\v∉e} from
    h▸Or.inl he).1
lemma AH {V:Type n4} {I:Type n5} [aO:Fintype I] [kr:DecidableEq V] {G:SimpleGraph V} (p:I->cK G) (v:V) (j:gM p v)
  (j4:0<(fZ p v j).walk.length):v∉(fZ p v j).walk.support:=by
 rcases j with i | ⟨i,b⟩
 ·exact i.property
 ·have h:=kK (p i.val).walk (p i.val).isPath i.property
  cases b
  ·exact h.2.2.2.2.2.1 j4
  ·exact h.2.2.2.2.1 j4
lemma Hz (p:I->cK G) (v:V)
  (hd:Pairwise λ i j=>Disjoint (p i).walk.edgeSet (p j).walk.edgeSet):Pairwise λ j k=>Disjoint (fZ p v j).walk.edgeSet (fZ p v k).walk.edgeSet:=by
 intro j k zQ;by_cases he:parent p v j=parent p v k
 ·rcases j with i | ⟨i,b⟩<;>rcases k with l | ⟨l,c⟩
  ·exact (zQ (aF Sum.inl (aZ he))).elim
  ·exact (i.property (show v∈(p i.val).walk.support from (show i.val=l.val from he).symm▸l.property)).elim
  ·exact (l.property (show v∈(p l.val).walk.support from (show i.val=l.val from he)▸i.property)).elim
  ·have OE:i=l:=aZ he
   subst l;cases b<;>cases c
   ·exact (zQ rfl).elim
   ·exact (kK (p i.val).walk (p i.val).isPath i.property).2.2.1.symm
   ·exact (kK (p i.val).walk (p i.val).isPath i.property).2.2.1
   ·exact (zQ rfl).elim
 ·exact (hd he).mono (rJ p v j) (rJ p v k)
lemma HA (p:I->cK G) (v x:V)
  (hne:∀i,(p i).start≠(p i).finish)
  (lG:(univ.filter λ i=>(p i).start=x\/(p i).finish=x).card<=1):(univ.filter λ j:gM p v=>E5 p v x j).card<=1:=by
 classical
 apply jK.mpr;intro j hj k hk;have XZ:(p (parent p v j)).start=x\/(p (parent p v j)).finish=x:=by
  have h:=(aD.mp hj).2;rcases j with i | ⟨i,b⟩
  ·exact h
  ·cases b
   ·exact Or.inr h
   ·exact Or.inl h
 have X0:(p (parent p v k)).start=x\/(p (parent p v k)).finish=x:=by
  have h:=(aD.mp hk).2;rcases k with i | ⟨i,b⟩
  ·exact h
  ·cases b
   ·exact Or.inr h
   ·exact Or.inl h
 have he:=jK.mp lG (parent p v j)
  (aD.mpr ⟨aQ _,XZ⟩) (parent p v k)
  (aD.mpr ⟨aQ _,X0⟩)
 have hj':=(aD.mp hj).2;have hk':=(aD.mp hk).2;rcases j with i | ⟨i,b⟩<;>rcases k with l | ⟨l,c⟩
 ·exact aF Sum.inl (aZ he)
 ·exact (i.property (show v∈(p i.val).walk.support from (show i.val=l.val from he).symm▸l.property)).elim
 ·exact (l.property (show v∈(p l.val).walk.support from (show i.val=l.val from he)▸i.property)).elim
 ·have OE:i=l:=aZ he
  subst l;cases b<;>cases c
  ·rfl
  ·exact (hne _ (hk'.trans hj'.symm)).elim
  ·exact (hne _ (hj'.trans hk'.symm)).elim
  ·rfl
lemma HC (p:I->cK G) (v x:V)
  (hd:Pairwise λ i j=>Disjoint (p i).walk.edgeSet (p j).walk.edgeSet):(univ.filter λ j:gM p v=>0<(fZ p v j).walk.length/\z4 p v x j).card<=1:=by
 classical
 have h:=vN
  (λ i:Ga p v=>(p i.val).walk) (λ i=>(p i.val).isPath)
  (λ i=>i.property)
  (λ i j hij=>hd (λ he=>hij (aZ he))) x
 apply jK.mpr;intro j hj k hk;have hj':=(aD.mp hj).2;have hk':=(aD.mp hk).2;rcases j with i | ⟨i,b⟩
 ·exact False.elim hj'.2
 rcases k with l | ⟨l,c⟩
 ·exact False.elim hk'.2
 apply aF Sum.inr;apply jK.mp h
 ·apply aD.mpr;refine ⟨aQ _,?_⟩;cases b<;>exact hj'
 ·apply aD.mpr;refine ⟨aQ _,?_⟩;cases c<;>exact hk'
lemma B7 (p:I->cK G) (v x:V)
  (hne:∀i,(p i).start≠(p i).finish)
  (hd:Pairwise λ i j=>Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
  (lG:(univ.filter λ i=>(p i).start=x\/(p i).finish=x).card<=1):(univ.filter λ j:gM p v=>0<(fZ p v j).walk.length/\((fZ p v j).start=x\/(fZ p v j).finish=x)).card<=2:=by
 classical
 let A:=univ.filter (λ j:gM p v=>E5 p v x j);let B:=univ.filter (λ j:gM p v=>0<(fZ p v j).walk.length/\z4 p v x j);have hsub:(univ.filter λ j:gM p v=>
   0<(fZ p v j).walk.length/\((fZ p v j).start=x\/(fZ p v j).finish=x))⊆A∪B:=by
  intro j hj;obtain ⟨j4,JX⟩:=(aD.mp hj).2;rcases (LV p v x j).mp JX with ho | hn
  ·exact cQ _ (aD.mpr ⟨aQ _,ho⟩)
  ·exact ee _ (aD.mpr ⟨aQ _,j4,hn⟩)
 have ha:=HA p v x hne lG;have hb:=HC p v x hd;have hc:=(aU hsub).trans (dG A B);dsimp [A,B] at hc;omega
lemma KN (p:I->cK G) (v:V):(⋃ j:gM p v,(fZ p v j).walk.edgeSet)={e | (∃i,e∈(p i).walk.edgeSet)/\v∉e}:=by
 classical
 ext e;constructor
 ·intro he
  obtain ⟨j,hj⟩:=av.mp he;refine ⟨⟨parent p v j,rJ p v j hj⟩,?_⟩;rcases j with i | ⟨i,b⟩
  ·intro hv
   exact i.property (rU.mpr
    (Or.inr ⟨e,hj,hv⟩))
  ·have h:=(kK (p i.val).walk (p i.val).isPath i.property).2.2.2.1
   cases b
   ·exact (show e∈{e | e∈(p i.val).walk.edgeSet/\v∉e} from
     h▸Or.inr hj).2
   ·exact (show e∈{e | e∈(p i.val).walk.edgeSet/\v∉e} from
     h▸Or.inl hj).2
 ·rintro ⟨⟨i,hi⟩,hv⟩
  by_cases hs:v∈(p i).walk.support
  ·have h:=(kK (p i).walk (p i).isPath hs).2.2.2.1
   have he:e∈((p i).walk.takeUntil v hs).dropLast.edgeSet∪((p i).walk.dropUntil v hs).tail.edgeSet:=h.symm▸⟨hi,hv⟩;rcases he with hl | hr
   ·exact av.mpr ⟨Sum.inr (⟨i,hs⟩,true),hl⟩
   ·exact av.mpr ⟨Sum.inr (⟨i,hs⟩,false),hr⟩
  ·exact av.mpr ⟨Sum.inl ⟨i,hs⟩,hi⟩
lemma Bu (p:I->cK G) (v:V):(⋃ j:{j:gM p v // 0<(fZ p v j).walk.length},(fZ p v j.val).walk.edgeSet)={e | (∃i,e∈(p i).walk.edgeSet)/\v∉e}:=by
 rw [<-KN p v];ext e;constructor
 ·intro he;obtain ⟨j,hj⟩:=av.mp he;exact av.mpr ⟨j.val,hj⟩
 ·intro he
  obtain ⟨j,hj⟩:=av.mp he;have hp:0<(fZ p v j).walk.length:=by
   by_contra hn;have hz:(fZ p v j).walk.length=0:=by omega
   have hn':=SimpleGraph.Walk.length_eq_zero_iff.mp hz;have he':=SimpleGraph.Walk.edges_eq_nil.mpr hn';have hmem:e∈(fZ p v j).walk.edges:=hj;exact List.not_mem_nil (he'▸hmem)
  exact av.mpr ⟨⟨j,hp⟩,hj⟩
def t5 (p:I->cK G) (v:V)
  (j:{j:gM p v // 0<(fZ p v j).walk.length}):cK (G.induce {x | x≠v}):=by
 let q:=fZ p v j.val;have Wk:∀x∈q.walk.support,x∈({x | x≠v}:Set V):=by intro x hx he;subst x;exact AH p v j.val j.property hx
 exact ⟨_,_,q.walk.induce _ Wk,by apply SimpleGraph.Walk.IsPath.of_map (f:=(SimpleGraph.Embedding.induce _).toHom);simpa using q.isPath⟩
end cK
end
end af
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
open scoped BigOperators
lemma qY {V:Type bX} {I:Type bY} [Fintype V] [Fintype I]
  {G:SimpleGraph V} (P:I->iz G)
  (hd:Pairwise λ i j=>Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
  (hc:(⋃ i,(P i).walk.edgeSet)=G.edgeSet)
  (hl:∀x:V,(univ.filter λ i=>(P i).start=x\/(P i).finish=x).card<=2):kA G:=by
 classical
 let e:=(equivFin I).symm;refine ⟨card I,λ j=>P (e j),?_,?_,?_,Ed P hl⟩
 ·intro i j hij;exact hd (λ he=>hij (e.injective he))
 ·rw [<-hc]
  ext z;simp only [av];constructor
  ·rintro ⟨i,hi⟩;exact ⟨e i,hi⟩
  ·rintro ⟨i,hi⟩;exact ⟨e.symm i,by rw [e.apply_symm_apply];exact hi⟩
 ·intro x
  have heq:(univ.filter λ j=>(P (e j)).start=x\/(P (e j)).finish=x).card=(univ.filter λ i=>(P i).start=x\/(P i).finish=x).card:=by
   apply card_bij (λ j _=>e j)
   ·intro i hi;simpa only [aD,aQ,b5] using hi
   ·intro i hi j hj he;exact e.injective he
   ·intro i hi;exact ⟨e.symm i,by simpa using hi,by simp⟩
  rw [heq];exact hl x
def iz.mapIso {V:Type cy} {W:Type cz} {G:SimpleGraph V} {H:SimpleGraph W}
  (f:G ≃g H) (P:iz G):iz H:=⟨f P.start,f P.finish,P.walk.map f.toHom,P.isPath.map f.injective,by simpa using P.positive⟩
lemma zk {V:Type cP} {W:Type cL} [Fintype V] [Fintype W]
  {G:SimpleGraph V} {H:SimpleGraph W} (f:G ≃g H)
  (hp:kA G):kA H:=by
 classical
 obtain ⟨k,P,hd,hc,hl,hk⟩:=hp;apply qY (λ i=>(P i).mapIso f)
 ·intro i j hij;change Disjoint ((P i).walk.map f.toHom).edgeSet ((P j).walk.map f.toHom).edgeSet;simp only [g6];exact (l9 (fI f.injective)).mpr (hd hij)
 ·have HG:Sym2.map f.toHom '' G.edgeSet=H.edgeSet:=by
   ext e;induction e using i8 with | _ u v=>
    constructor
    ·rintro ⟨e,he,heq⟩
     induction e using i8 with | _ a b=>
      have ha:H.Adj (f a) (f b):=f.toHom.map_adj he;exact heq▸ha
    ·intro huv;refine ⟨s(f.symm u,f.symm v),f.symm.toHom.map_adj huv,?_⟩;simp
  change (⋃ i,((P i).walk.map f.toHom).edgeSet)=H.edgeSet;simp_rw [g6];rw [<-Set.image_iUnion,hc,HG]
 ·intro x
  have heq:(univ.filter λ i=>((P i).mapIso f).start=x\/((P i).mapIso f).finish=x)=(univ.filter λ i=>(P i).start=f.symm x\/(P i).finish=f.symm x):=by ext i;simp only [aD,aQ,b5];change (f (P i).start=x\/f (P i).finish=x)↔_;exact or_congr (f.toEquiv.eq_symm_apply.symm) (f.toEquiv.eq_symm_apply.symm)
  rw [heq];exact hl _
namespace cK
variable {V:Type c9} {I:Type dW} [Fintype V] [Fintype I] [DecidableEq V] {G:SimpleGraph V}
lemma xT {V:Type eo} {I:Type d7} [aO:Fintype V] [kr:Fintype I] [kq:DecidableEq V] {G:SimpleGraph V} (p:I->cK G) (v:V)
  (j:{j:gM p v // 0<(fZ p v j).walk.length}):(t5 p v j).walk.map (SimpleGraph.Embedding.induce _).toHom=(fZ p v j.val).walk:=by
 exact SimpleGraph.Walk.map_induce _ _
lemma rK (p:I->cK G) (v:V)
  (j:{j:gM p v // 0<(fZ p v j).walk.length}):Sym2.map (SimpleGraph.Embedding.induce (G:=G) {x | x≠v}).toHom ''
   (t5 p v j).walk.edgeSet=(fZ p v j.val).walk.edgeSet:=by
 calc
  _=((t5 p v j).walk.map
    (SimpleGraph.Embedding.induce {x | x≠v}).toHom).edgeSet:=(g6 _ _).symm
  _=_:=aF (λ q:G.Walk (fZ p v j.val).start
   (fZ p v j.val).finish=>q.edgeSet) (xT p v j)
def sT (p:I->cK G) (v:V)
  (j:{j:gM p v // 0<(fZ p v j).walk.length}):iz (G.induce {x | x≠v}):=
 {t5 p v j with
  positive:=by have h:=aF SimpleGraph.Walk.length (xT p v j);rw [l8] at h;rw [h];exact j.property}
lemma uR (p:I->cK G) (v:V)
  (hne:∀i,(p i).start≠(p i).finish)
  (hd:Pairwise λ i j=>Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
  (hc:(⋃ i,(p i).walk.edgeSet)=G.edgeSet)
  (hl:∀x:V,x≠v->(univ.filter λ i=>(p i).start=x\/(p i).finish=x).card<=1):
  kA (G.induce {x | x≠v}):=by
 classical
 let A:={j:gM p v // 0<(fZ p v j).walk.length};let f:G.induce {x | x≠v} →g G:=(SimpleGraph.Embedding.induce _).toHom;have hf:Function.Injective f:=dM;apply qY (λ j:A=>sT p v j)
 ·intro j k zQ
  have hdis:=Hz p v hd (λ he=>zQ (aZ he));apply aI.mpr;intro e yP X3;have Ow:Sym2.map f e∈(fZ p v j.val).walk.edgeSet:=by rw [<-rK p v j];exact ⟨e,yP,rfl⟩
  have Kp:Sym2.map f e∈(fZ p v k.val).walk.edgeSet:=by rw [<-rK p v k];exact ⟨e,X3,rfl⟩
  exact aI.mp hdis Ow Kp
 ·apply mW
  ·intro e he;obtain ⟨j,hj⟩:=av.mp he;exact (sT p v j).walk.edges_subset_edgeSet hj
  ·intro e he
   have he':Sym2.map f e∈G.edgeSet/\v∉Sym2.map f e:=by
    induction e using i8 with | _ a b=>
     refine ⟨he,?_⟩;change v∉s(a.val,b.val);simpa only [Sym2.map_mk,Sym2.mem_iff,gH] using not_or.mpr ⟨a.property,b.property⟩
   have hmem:Sym2.map f e∈⋃ j:A,(fZ p v j.val).walk.edgeSet:=by rw [Bu];refine ⟨?_,he'.2⟩;exact av.mp (hc.symm▸he'.1)
   obtain ⟨j,hj⟩:=av.mp hmem;rw [<-rK p v j] at hj;obtain ⟨e',he',heq⟩:=hj;have Si:e'=e:=fI hf heq;subst e';exact av.mpr ⟨j,he'⟩
 ·intro x
  have hb:=B7 p v x.val hne hd (hl x.val x.property);have hc':(univ.filter λ j:A=>
    (sT p v j).start=x\/(sT p v j).finish=x).card<=(univ.filter λ j:gM p v=>0<(fZ p v j).walk.length/\((fZ p v j).start=x.val\/(fZ p v j).finish=x.val)).card:=by
   apply gG Subtype.val
   ·intro j hj
    apply aD.mpr;refine ⟨aQ _,j.property,?_⟩;rcases (aD.mp hj).2 with hs | ht
    ·exact Or.inl (aF Subtype.val hs)
    ·exact Or.inr (aF Subtype.val ht)
   ·exact λ _ _ _ _ he=>aZ he
  convert hc'.trans hb using 1
  all_goals first
   | rfl
   | exact aF card (Finset.ext λ i=>by simp only [aD,aQ,b5])
end cK
def Bv {V:Type d8} [Fintype V] (G:SimpleGraph V):G ≃g (iS G).induce {x | x≠none} where
 toEquiv:=Equiv.optionSubtype none ⟨Equiv.refl (Option V),rfl⟩
 map_rel_iff':=Iff.rfl
lemma s9 {V:Type d9} [Fintype V]
  (G:SimpleGraph V) (hL:tw (iS G)):kA G:=by
 classical
 obtain ⟨k,parts,uT,hd,hc,hk⟩:=hL;have hw:∀i:Fin k,∃(a b:Option V) (p:(iS G).Walk a b),p.IsTrail/\(a≠b->p.IsPath)/\parts i=p.edgeSet:=by
  intro i;rcases uT i with ⟨a,b,p,hp,_,he⟩ | ⟨a,p,hp,he⟩
  ·exact ⟨a,b,p,hp.isTrail,λ _=>hp,he⟩
  ·exact ⟨a,a,p,hp.isTrail,λ h=>False.elim (h rfl),he⟩
 choose a b p ht hp he using hw;have GR:Pairwise λ i j=>Disjoint (p i).edgeSet (p j).edgeSet:=by simpa only [he] using hd
 have hc':(⋃ i,(p i).edgeSet)=(iS G).edgeSet:=by simpa only [he] using hc
 let S:Finset (Option V):=univ.image some;have hS:S.card=card V:=by simp only [S,gI _ (mO V),c7]
 have ho:∀x∈S,Odd ((iS G).degree x):=by intro x hx;obtain ⟨y,_,rfl⟩:=bk.mp hx;exact zZ G y
 have hk':2*card (Fin k)<=S.card+1:=by simpa only [dU,card_option,hS] using hk
 obtain ⟨NY,lG⟩:=zj (iS G) S p ht GR hc' ho hk';let P:Fin k->cK (iS G):=λ i=>⟨a i,b i,p i,hp i (NY i)⟩
 have Sj:∀x:Option V,x≠none->(univ.filter λ i=>
   (P i).start=x\/(P i).finish=x).card<=1:=by
  intro x hx;cases x with
  | none=>exact False.elim (hx rfl)
  | some x=>
    have h:=lG (some x) (bk.mpr ⟨x,aQ _,rfl⟩);have hpred:(univ.filter λ i=>a i≠b i/\(some x=a i\/some x=b i))=(univ.filter λ i=>(P i).start=some x\/(P i).finish=some x):=by
     ext i;simp only [aD,aQ,b5,P];constructor
     ·rintro ⟨_,hi⟩;exact hi.elim (λ h=>Or.inl h.symm) (λ h=>Or.inr h.symm)
     ·intro hi;exact ⟨NY i,hi.elim (λ h=>Or.inl h.symm) (λ h=>Or.inr h.symm)⟩
    apply le_of_eq;calc
     _=_:=aF card hpred.symm
     _=1:=by convert h using 1;congr 1;ext i;simp only [aD,aQ,b5]
 have JV:=cK.uR P none NY GR hc' Sj;exact zk (Bv G).symm JV
end
end af
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
lemma xV {V:Type eO} [Fintype V] (G:SimpleGraph V):tw G:=by
 classical
 obtain ⟨k,P,hd,hc,hk⟩:=cI.Di G;refine ⟨k,λ i=>(P i).walk.edgeSet,?_,hd,hc,?_⟩
 ·intro i
  rcases (P i).simple with hp | ⟨h,OG⟩
  ·exact Or.inl ⟨(P i).start,(P i).finish,(P i).walk,hp.1,hp.2,rfl⟩
  ·exact Or.inr ⟨(P i).start,(P i).walk.copy rfl h,OG,by simp⟩
 ·exact hk.trans (e4 _)
lemma ur {V:Type fX} [Fintype V] (G:SimpleGraph V):kA G:=s9 G (xV (iS G))
end
end af
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
def e8 {V:Type} (G:SimpleGraph V)
  (s:Set (Sym2 V)):Prop:=(∃(v:V) (p:G.Walk v v),p.IsCycle/\s=p.edgeSet)\/∃e∈G.edgeSet,s={e}
def e9 {V:Type} (G:SimpleGraph V) (k:ℕ):Prop:=∃parts:Fin k->Set (Sym2 V),(∀i,e8 G (parts i))/\Pairwise (λ i j=>Disjoint (parts i) (parts j))/\(⋃ i,parts i)=G.edgeSet
section
open SimpleGraph
lemma tB {V:Type} {G:SimpleGraph V}
  {s:Set (Sym2 V)} (hs:e8 G s):s⊆G.edgeSet:=by
 rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
 ·exact p.edges_subset_edgeSet
 ·simpa using he
lemma vu {V W:Type} {G:SimpleGraph V} {H:SimpleGraph W}
  (f:G →g H) (hf:Function.Injective f) {s:Set (Sym2 V)}
  (hs:e8 G s):e8 H (Sym2.map f '' s):=by
 rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
 ·exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
 ·refine Or.inr ⟨Sym2.map f e,?_,by simp⟩
  induction e using bJ with | _ x y=>
   exact f.map_adj he
lemma om {V I:Type} [Fintype I] (G:SimpleGraph V)
  (parts:I->Set (Sym2 V)) (hp:∀i,e8 G (parts i))
  (hd:Pairwise (λ i j=>Disjoint (parts i) (parts j)))
  (hu:(⋃ i,parts i)=G.edgeSet):e9 G (card I):=by
 let e:=equivFin I;refine ⟨λ j=>parts (e.symm j),λ j=>hp _,?_,?_⟩
 ·intro i j hij;exact hd (λ he=>hij (e.symm.injective he))
 ·ext x
  simp only [av];rw [<-hu];simp only [av];constructor
  ·rintro ⟨i,hi⟩;exact ⟨e.symm i,hi⟩
  ·rintro ⟨i,hi⟩;exact ⟨e i,by simpa using hi⟩
lemma qK {V:Type} [Fintype V] (G:SimpleGraph V):e9 G (Nat.card G.edgeSet):=by
 classical
 let:Fintype G.edgeSet:=ofFinite _;rw [Nat.card_eq_fintype_card];apply om G (λ e:G.edgeSet=>{e.1})
 ·intro e;exact Or.inr ⟨e.1,e.2,rfl⟩
 ·intro e d DT;exact mK.mpr (λ h=>DT (aZ h))
 ·ext e;simp
lemma yF {V I:Type} [Fintype I] (G:SimpleGraph V)
  (W:I->Type) (H:∀i,SimpleGraph (W i))
  (f:∀i,H i →g G) (hf:∀i,Function.Injective (f i))
  (hdisj:Pairwise (λ i j=>Disjoint (Sym2.map (f i) '' (H i).edgeSet) (Sym2.map (f j) '' (H j).edgeSet)))
  (e7:(⋃ i,Sym2.map (f i) '' (H i).edgeSet)=G.edgeSet)
  (k:I->ℕ) (uT:∀i,e9 (H i) (k i)):e9 G (∑i,k i):=by
 classical
 choose parts hp hd hu using uT;let J:=Σ i,Fin (k i);let P:J->Set (Sym2 V):=λ j=>Sym2.map (f j.1) '' parts j.1 j.2
 have hpart:∀j,e8 G (P j):=by intro j;exact vu (f j.1) (hf j.1) (hp j.1 j.2)
 have hsub:∀i a,parts i a⊆(H i).edgeSet:=by intro i a;exact tB (hp i a)
 have Sk:Pairwise (λ i j=>Disjoint (P i) (P j)):=by
  rintro ⟨i,a⟩ ⟨j,b⟩ hij;by_cases h:i=j
  ·subst j
   have hab:a≠b:=λ he=>hij (by cases he;rfl)
   apply aI.mpr;rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩;have hxy:x=y:=fI (hf i) (he.trans he'.symm);subst y;exact aI.mp (hd i hab) hx hy
  ·exact (hdisj h).mono (jL (hsub i a)) (jL (hsub j b))
 have Q2:(⋃ j,P j)=G.edgeSet:=by
  rw [<-e7];ext e;simp only [av];constructor
  ·rintro ⟨⟨i,a⟩,x,hx,he⟩;exact ⟨i,x,hsub i a hx,he⟩
  ·rintro ⟨i,x,hx,he⟩;rw [<-hu i] at hx;obtain ⟨a,ha⟩:=av.mp hx;exact ⟨⟨i,a⟩,x,ha,he⟩
 have hc:card J=∑i,k i:=by simp [J,fy]
 rw [<-hc];exact om G P hpart Sk Q2
end
end af
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma KO (c η:ℝ) (hc:0<c) (hη:0<η):∃dN:ℝ,1<dN/\∀D≥dN,∀(V:Type) [Fintype V] [DecidableEq V] (G P:SimpleGraph V)
    [DecidableRel P.Adj],P<=G->
   D^(9/10:ℝ)<=(card V:ℝ)->(card V:ℝ)<=D^(51/50:ℝ)->aR.af.aV.cW P (c*D^(9/10:ℝ))->∃(k:ℕ) (parts:Fin k->Set (Sym2 V))
    (W:Fin 3->Finset V) (H:Fin 3->SimpleGraph V),(∀i,e8 G (parts i))/\Pairwise (λ i j=>Disjoint (parts i) (parts j))/\(∀b,H b<=G/\(H b).support⊆(W b:Set V))/\(∀b,(W b).card<card V)/\((∑b,(W b).card:ℕ):ℝ)<=η*card V/\Pairwise (λ b d=>Disjoint (H b).edgeSet (H d).edgeSet)/\(∀b i,Disjoint (H b).edgeSet (parts i))/\((⋃ i,parts i)∪(⋃ b,(H b).edgeSet))=G.edgeSet/\k<=9*card V:=by
 classical
 have ha:0<gC c:=by unfold gC;exact div_pos (lt_min hc (by norm_num)) (by norm_num)
 have hp:0<kL η:=by unfold kL;exact lt_min (div_pos hη (by norm_num)) (by norm_num)
 obtain ⟨D₁,TZ⟩:=BZ c η hc hη;obtain ⟨D₂,F7,LI⟩:=uF
  (gC c) (kL η) ha hp
 refine ⟨max D₁ D₂,F7.trans_le (bC _ _),?_⟩;intro D hD V _ _ G P _ oe hlo hhi hexp;obtain ⟨ω,W,r,Pk,vm,aab,X4,X5,Im,Lu,F8,T0,hr,LB,rG⟩:=TZ D ((b6 _ _).trans hD) V G P oe hlo hhi hexp;let P':=λ b=>aR.af.Splitting.dI P ω b
 have NZ:Pairwise λ b d=>Disjoint (W b:Set V) (W d:Set V):=by intro b d hbd;exact m4.mpr (X4 b d hbd)
 let R:=λ b=>fD (P' b) (W b)
 let T:=λ b=>R b∪(gL (W b) (r b):Set (Sym2 V))
 let E:Set (Sym2 V):=⋃ b,T b;have hres:=qF G P' W r Pk vm
  (λ b v hv t=>(hr b v hv t).2)
 have hE:E⊆G.edgeSet:=gJ λ b=>Set.union_subset (hres.1 b).1 (hres.1 b).2
 let K:=λ b=>gw (G.deleteEdges E)
  (λ b=>(W b:Set V)) NZ b
 have hK:=qw (G.deleteEdges E)
  (λ b=>(W b:Set V)) NZ
 have X6:∀b,K b<=G:=λ b=>(hK.1 b).trans (G.deleteEdges_le E)
 have r6:=vd G (λ b=>(W b:Set V)) NZ E hE;have R6:∀b d,Disjoint (K b).edgeSet (T d):=λ b d=>(r6.2.1 b).mono_right (je T d)
 have hx:∀b:Fin 3,kA (K b):=λ b=>ur (K b)
 choose k Q LH X7 X8 aaS using hx;let x:=λ b i=>(Q b i).start
 let y:=λ b i=>(Q b i).finish
 let q:∀b i,G.Walk (x b i) (y b i):=λ b i=>(Q b i).walk.mapLe (X6 b)
 have X9:∀b i,(q b i).IsPath:=λ b i=>(Q b i).isPath.mapLe _
 have Ya:∀b i,0<(q b i).length:=by intro b i;simpa [q] using (Q b i).positive
 have Yb:∀b i v,v∈(q b i).support->v∉W b:=by
  intro b i v hv;apply yB (λ b=>(W b:Set V)) NZ b
   (Q b i).walk (Q b i).positive v
  simpa [q] using hv
 have LW:∀b,Pairwise λ i j=>Disjoint (q b i).edgeSet (q b j).edgeSet:=by intro b i j hij;simpa [q] using LH b hij
 have Yc:∀b,(⋃ i,(q b i).edgeSet)=(K b).edgeSet:=by intro b;simpa [q] using X7 b
 obtain ⟨C,R7,Kr,aac,e7,B0⟩:=LI D ((bC _ _).trans hD)
  V G P' K Pk vm W r T0 X5 hhi hr LB rG
  r6.1 R6 (λ b=>Fin (k b)) x y q X9 Ya Yb LW Yc
   (by intro b v;dsimp only [b7,x,y];convert X8 b v using 2;ext i;simp)
 let I:=Σ b,Fin (k b);let CE:I->Set (Sym2 V):=λ z=>(C z.1 z.2).edgeSet
 have Yd:∀i,CE i⊆G.edgeSet:=λ i=>(C i.1 i.2).edges_subset_edgeSet
 have Sl:E=(⋃ b,R b)∪(gO W r:Set _):=by simp only [E,T,qG,mj]
 have wu:G.edgeSet\((⋃ b,R b)∪(gO W r:Set _))⊆iQ CE:=by rw [<-Sl,<-g8,<-hK.2.2.2];exact e7
 obtain ⟨Df,N4,aaT,B8,Ye,Yf,Vd,hu,hnum⟩:=zf G P' W r Pk vm
   (λ b v hv t=>(hr b v hv t).2) CE Yd Kr B0 wu
 let H:=iA G R CE;let S:=lH (↑(gO W r)) CE;let J:=I ⊕ S;let parts:J->Set (Sym2 V):=Sum.elim CE (λ e=>{e.val});have xA:(S:Set (Sym2 V))⊆G.edgeSet:=by
  intro e he;have hh:e∈(gO W r:Set _):=by have hh:=he;simp only [kQ,S,lH,jc,kR] at hh;exact hh.1
  exact hE (by rw [Sl];exact Or.inr hh)
 have hpart:∀j,e8 G (parts j):=by
  intro j;rcases j with i | e
  ·exact Or.inl ⟨x i.1 i.2,C i.1 i.2,R7 i.1 i.2,rfl⟩
  ·exact Or.inr ⟨e.val,xA e.property,rfl⟩
 have Sm:Pairwise λ i j=>Disjoint (parts i) (parts j):=by
  intro i j hij;rcases i with i | e<;>rcases j with j | f
  ·exact Kr (λ h=>hij (aF Sum.inl h))
  ·exact (Vd i).mono_right (m5.mpr f.property)
  ·exact (Vd j).symm.mono_left (m5.mpr e.property)
  ·exact mK.mpr (λ h=>hij (aF Sum.inr (aZ h)))
 have So:(⋃ j,parts j)=iQ CE∪(S:Set (Sym2 V)):=by
  ext e;simp only [av,b8,iQ,parts];constructor
  ·rintro ⟨i,hi⟩
   rcases i with i | f
   ·exact Or.inl ⟨i,hi⟩
   ·exact Or.inr ((dB.mp hi)▸f.property)
  ·rintro (⟨i,hi⟩ | he)
   ·exact ⟨Sum.inl i,hi⟩
   ·exact ⟨Sum.inr ⟨e,he⟩,rfl⟩
 let equiv:=equivFin J;refine ⟨card J,λ i=>parts (equiv.symm i),W,H,?_,?_,?_,Lu,F8,B8,?_,?_,?_⟩
 ·exact λ i=>hpart _
 ·intro i j hij;exact Sm (λ h=>hij (equiv.symm.injective h))
 ·intro b;refine ⟨?_,Df b⟩;exact ET G _
 ·intro b i
  rcases GO:equiv.symm i with j | e
  all_goals simp only [GO,parts,Sum.elim_inl,Sum.elim_inr]
  ·exact Ye b j
  ·exact (Yf b).mono_right (m5.mpr e.property)
 ·have he:(⋃ i,parts (equiv.symm i))=⋃ j,parts j:=by
   ext e;simp only [av];exact ⟨λ ⟨i,hi⟩=>⟨equiv.symm i,hi⟩,λ ⟨j,hj⟩=>⟨equiv j,by simpa using hj⟩⟩
  rw [he,So];exact hu
 ·simpa only [J,fO,eG] using hnum
end
end af
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
def aM {V:Type} [Fintype V] (G:SimpleGraph V):ℕ:=Nat.find (show ∃k,e9 G k from ⟨_,qK G⟩)
lemma ov {V:Type} [Fintype V] (G:SimpleGraph V):e9 G (aM G):=Nat.find_spec _
lemma pC {V:Type} [Fintype V] {G:SimpleGraph V} {k:ℕ}
 (h:e9 G k):aM G<=k:=Nat.find_min' _ h
lemma wS {V:Type} [Fintype V] (G:SimpleGraph V):aM G<=Nat.card G.edgeSet:=pC (qK G)
lemma z5 {V I J:Type} [Fintype I] [Fintype J]
  (G:SimpleGraph V) (parts:I->Set (Sym2 V))
  (hp:∀i,e8 G (parts i))
  (hd:Pairwise λ i j=>Disjoint (parts i) (parts j))
  (W:J->Type) (H:∀j,SimpleGraph (W j)) (f:∀j,H j →g G)
  (hf:∀j,Function.Injective (f j))
  (B8:Pairwise λ i j=>Disjoint (Sym2.map (f i) '' (H i).edgeSet)
   (Sym2.map (f j) '' (H j).edgeSet))
  (Kt:∀j i,Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
  (hu:(⋃ i,parts i)∪(⋃ j,Sym2.map (f j) '' (H j).edgeSet)=G.edgeSet)
  (k:J->ℕ) (hD:∀j,e9 (H j) (k j)):e9 G (card I+∑j,k j):=by
 classical
 choose P hP Sp OH using hD;let R:(I ⊕ Σ j,Fin (k j))->Set (Sym2 V):=Sum.elim parts (λ z=>Sym2.map (f z.1) '' P z.1 z.2);have hsub:∀j i,P j i⊆(H j).edgeSet:=λ j i=>tB (hP j i)
 have Yg:∀z,e8 G (R z):=by
  intro z;rcases z with z | ⟨j,i⟩
  ·exact hp z
  ·exact vu (f j) (hf j) (hP j i)
 have Yh:Pairwise λ z t=>Disjoint (R z) (R t):=by
  intro z t Sq;rcases z with z | ⟨j,i⟩<;>rcases t with t | ⟨l,a⟩
  ·exact hd (λ h=>Sq (aF Sum.inl h))
  ·exact ((Kt l z).mono_left (jL (hsub l a))).symm
  ·exact (Kt j t).mono_left (jL (hsub j i))
  ·by_cases Yi:j=l
   ·subst l
    have hia:i≠a:=λ h=>Sq (by cases h;rfl)
    apply aI.mpr;rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩;have hxy:=fI (hf j) (he.trans he'.symm);subst y;exact aI.mp (Sp j hia) hx hy
   ·exact (B8 Yi).mono (jL (hsub j i)) (jL (hsub l a))
 have Yj:(⋃ z,R z)=G.edgeSet:=by
  rw [<-hu];ext e;simp only [av,b8];constructor
  ·rintro ⟨z,hz⟩
   rcases z with z | ⟨j,i⟩
   ·exact Or.inl ⟨z,hz⟩
   ·obtain ⟨x,hx,he⟩:=hz;exact Or.inr ⟨j,x,hsub j i hx,he⟩
  ·rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
   ·exact ⟨Sum.inl i,hi⟩
   ·rw [<-OH j] at hx;obtain ⟨i,hi⟩:=av.mp hx;exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
 simpa only [fO,fy,dU] using
  om G R Yg Yh Yj
lemma z6 {V I J:Type} [Fintype V] [Fintype I] [Fintype J]
  (G:SimpleGraph V) (parts:I->Set (Sym2 V))
  (hp:∀i,e8 G (parts i))
  (hd:Pairwise λ i j=>Disjoint (parts i) (parts j))
  (W:J->Type) [∀j,Fintype (W j)] (H:∀j,SimpleGraph (W j))
  (f:∀j,H j →g G) (hf:∀j,Function.Injective (f j))
  (B8:Pairwise λ i j=>Disjoint (Sym2.map (f i) '' (H i).edgeSet)
   (Sym2.map (f j) '' (H j).edgeSet))
  (Kt:∀j i,Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
  (hu:(⋃ i,parts i)∪(⋃ j,Sym2.map (f j) '' (H j).edgeSet)=G.edgeSet):aM G<=card I+∑j,aM (H j):=pC (z5 G parts hp hd W H f hf B8 Kt hu _
  (λ j=>ov (H j)))
end
end af
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma vw {V W:Type} {G:SimpleGraph V} {H:SimpleGraph W}
  (f:H →g G) (hf:Function.Injective f)
  (hu:Sym2.map f '' H.edgeSet=G.edgeSet) {k:ℕ} (hk:e9 H k):e9 G k:=by
 have:=yF (I:=Unit) G (λ _:Unit=>W) (λ _=>H) (λ _=>f)
  (λ _=>hf) (by intro i j hij;exact False.elim (hij (Subsingleton.elim _ _)))
  (by rw [Set.iUnion_const];exact hu) (λ _=>k) (λ _=>hk)
 simpa using this
lemma wA {V:Type} [Fintype V] (G:SimpleGraph V)
  (A:Finset V) (hA:∀⦃x y⦄,G.Adj x y->x∈A/\y∈A):aM G<=aM (G.induce (A:Set V)):=by
 classical
 let f:G.induce (A:Set V) →g G:=⟨Subtype.val,λ h=>h⟩;have hu:Sym2.map f '' (G.induce (A:Set V)).edgeSet=G.edgeSet:=by
  ext e;constructor
  ·rintro ⟨e,he,rfl⟩;induction e using bJ with | _ x y=>exact he
  ·intro he
   induction e using bJ with
   | _ x y=>exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩
 exact pC (vw f dM hu (ov _))
lemma Dj {V:Type} (G:SimpleGraph V)
  (A:Finset V) (hA:∀⦃x y⦄,G.Adj x y->x∈A/\y∈A)
  {k:ℕ} (hk:e9 (G.induce (A:Set V)) k):e9 G k:=by
 classical
 let f:G.induce (A:Set V) →g G:=⟨Subtype.val,λ h=>h⟩;apply vw f dM _ hk;ext e;constructor
 ·rintro ⟨e,he,rfl⟩;induction e using bJ with | _ x y=>exact he
 ·intro he
  induction e using bJ with
  | _ x y=>exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩
end
end af
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma oc {V I J:Type} [Fintype V] [Fintype I] [Fintype J]
  (G:SimpleGraph V) (parts:I->Set (Sym2 V))
  (hp:∀i,e8 G (parts i))
  (hd:Pairwise λ i j=>Disjoint (parts i) (parts j))
  (H:J->SimpleGraph V) (DS:∀j,H j<=G)
  (B8:Pairwise λ i j=>Disjoint (H i).edgeSet (H j).edgeSet)
  (Kt:∀j i,Disjoint (H j).edgeSet (parts i))
  (hu:(⋃ i,parts i)∪(⋃ j,(H j).edgeSet)=G.edgeSet):aM G<=card I+∑j,aM (H j):=by
 let f:∀j,H j →g G:=λ j=>⟨id,λ h=>DS j h⟩
 have he (j):Sym2.map (f j) '' (H j).edgeSet=(H j).edgeSet:=by have hf:(f j:V->V)=id:=rfl;rw [hf,Sym2.map_id,Set.image_id]
 apply z6 G parts hp hd (λ _=>V) H f (λ _=>oQ)
 ·simpa only [he] using B8
 ·simpa only [he] using Kt
 ·simpa only [he] using hu
lemma vO {V J:Type} [Fintype V] [Fintype J]
  (G:SimpleGraph V) (H:J->SimpleGraph V) (DS:∀j,H j<=G)
  (B8:Pairwise λ i j=>Disjoint (H i).edgeSet (H j).edgeSet)
  (hu:(⋃ j,(H j).edgeSet)=G.edgeSet):aM G<=∑j,aM (H j):=by
 simpa using oc (I:=Empty) G Empty.elim (λ i=>nomatch i)
  (by intro i;exact i.elim) H DS B8 (λ _ i=>nomatch i) (by simpa using hu)
end
end af
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma E9 (c η:ℝ) (hc:0<c) (hη:0<η):∃dN:ℝ,1<dN/\∀D≥dN,∀(n:ℕ) (C:ℝ),0<=C->(∀(W:Type) [Fintype W] (H:SimpleGraph W),card W<n->(aM H:ℝ)<=C*card W)->
   ∀(V:Type) [Fintype V] [DecidableEq V] (G P:SimpleGraph V)
    [DecidableRel P.Adj],P<=G->card V<=n->
   D^(9/10:ℝ)<=(card V:ℝ)->(card V:ℝ)<=D^(51/50:ℝ)->aR.af.aV.cW P (c*D^(9/10:ℝ))->(aM G:ℝ)<=(9+C*η)*card V:=by
 obtain ⟨dN,ko,hres⟩:=KO c η hc hη;refine ⟨dN,ko,?_⟩;intro D hD n C hC ih V _ _ G P _ oe hn hlo hhi he;obtain ⟨k,parts,W,H,hp,hd,DS,Lu,F8,B8,Kt,hu,hk⟩:=hres D hD V G P oe hlo hhi he;have jF (b:Fin 3):(aM (H b):ℝ)<=C*(W b).card:=by
  have hA:∀⦃x y⦄,(H b).Adj x y->x∈W b/\y∈W b:=by intro x y hxy;exact ⟨(DS b).2 ⟨y,hxy⟩,(DS b).2 ⟨x,hxy.symm⟩⟩
  calc
   _<=(aM ((H b).induce (W b:Set V)):ℝ):=cq.mpr (wA _ _ hA)
   _<=C*card (W b:Set V):=ih _ _ (by simpa using (Lu b).trans_le hn)
   _=_:=by simp
 have Wl:=oc G parts hp hd H (λ b=>(DS b).1) B8 Kt hu;have hsum:(∑b,(aM (H b):ℝ))<=C*∑b,((W b).card:ℝ):=by rw [dR];exact aK (λ b _=>jF b)
 have N5:=aJ F8 hC;have hk':(k:ℝ)<=9*card V:=by exact_mod_cast hk
 have aad:(aM G:ℝ)<=k+∑b,(aM (H b):ℝ):=by simpa only [dU,fP,eV] using (cq.mpr Wl:(aM G:ℝ)<=_)
 push_cast at N5;nlinarith
end
end af
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma vz (c η:ℝ) (hc:0<c) (hη:0<η):∃dN:ℝ,1<dN/\∀D≥dN,∀(n:ℕ) (C:ℝ),0<=C->(∀(W:Type) [Fintype W] (H:SimpleGraph W),card W<n->(aM H:ℝ)<=C*card W)->
   ∀(V:Type) [Fintype V] [DecidableEq V] (G P:SimpleGraph V)
    [DecidableRel P.Adj] (A:Finset V),P<=G->A.card<=n->
   (∀⦃x y⦄,G.Adj x y->x∈A/\y∈A)->D^(9/10:ℝ)<=(A.card:ℝ)->(A.card:ℝ)<=D^(51/50:ℝ)->b9 P A (c*D^(9/10:ℝ))->(aM G:ℝ)<=(9+C*η)*A.card:=by
 obtain ⟨dN,ko,jF⟩:=E9 c η hc hη;refine ⟨dN,ko,?_⟩;intro D hD n C hC ih V _ _ G P _ A oe hn hA hlo hhi he;have Sr:=jF D hD n C hC ih (A:Set V) (G.induce (A:Set V))
  (P.induce (A:Set V)) (λ _ _ h=>oe h) (by simpa using hn)
  (by simpa using hlo) (by simpa using hhi) (oh P A _ he)
 calc
  _<=(aM (G.induce (A:Set V)):ℝ):=cq.mpr (wA G A hA)
  _<=_:=by simpa using Sr
end
end af
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX gu gX iN iO i7 jD jV jW jX kB jY kC kD kE kF jZ j0 lC lT lU oA n4 n5 qg qh qi sD sG sH qj sI qk qm qo qs qt qu sJ sK sL sN qv v7 v8 v9 wc we A6 wj wm
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
def Pairing (V:Type bX):={f:V->V // Function.Involutive f/\∀x,f x≠x}
namespace Pairing
variable {V:Type bY} {W:Type cy}
instance:CoeFun (Pairing V) (λ _=>V->V):=⟨Subtype.val⟩
instance [Fintype V] :Fintype (Pairing V):=by
 classical
 unfold Pairing;infer_instance
instance [Fintype V] :DecidableEq (Pairing V):=Classical.decEq _
@[simp] theorem apply_apply (p:Pairing V) (v:V):p (p v)=v:=p.property.1 v
@[simp] theorem apply_ne (p:Pairing V) (v:V):p v≠v:=p.property.2 v
def transport (e:V ≃ W):Pairing V ≃ Pairing W where
 toFun p:=⟨λ x=>e (p (e.symm x)),(by intro x;simp),(by intro x h;have:=aF e.symm h;simp at this)⟩
 invFun p:=⟨λ x=>e.symm (p (e x)),(by intro x;simp),(by intro x h;have:=aF e h;simp at this)⟩
 left_inv p:=by apply aZ;funext x;simp
 right_inv p:=by apply aZ;funext x;simp
@[simp] theorem Qa (e:V ≃ W) (p:Pairing V) (x:W):transport e p x=e (p (e.symm x)):=rfl
lemma vg [Fintype V] (h:Even (card V)):Nonempty (Pairing V):=by
 classical
 obtain ⟨k,hk⟩:=h;let q:Pairing (Fin k ⊕ Fin k):=⟨λ x=>x.swap,(by intro x;cases x<;>rfl),(by intro x h;cases x<;>nomatch h)⟩;let e:(Fin k ⊕ Fin k) ≃ V:=equivOfCardEq (by simpa using hk.symm);exact ⟨transport e q⟩
variable [Fintype V]
def kN (a b:V):ℕ:=by
 classical
 exact card {p:Pairing V // p a=b}
def lI (a b c d:V):ℕ:=by
 classical
 exact card {p:Pairing V // p a=b/\p c=d}
@[simp] theorem KP (a:V):kN a a=0:=by
 classical
 unfold kN;apply card_eq_zero_iff.mpr;exact ⟨λ p=>p.val.apply_ne a p.property⟩
lemma Fa (e:V ≃ V) (a b:V):kN (e a) (e b)=kN a b:=by
 classical
 symm;exact g9 ((transport e).subtypeEquiv (by intro p;simp))
lemma ML (a b c:V) (hab:a≠b) (hac:a≠c):kN a b=kN a c:=by
 classical
 have h:=Fa (Equiv.swap b c) a b;simpa [m6 hab hac] using h.symm
lemma z7 (a b:V) (hab:a≠b):(card V-1)*kN a b=card (Pairing V):=by
 classical
 have hsum:(∑c:V,kN a c)=card (Pairing V):=by unfold kN;rw [<-fy];exact g9 (Equiv.sigmaFiberEquiv (λ p:Pairing V=>p a))
 have heq:(∑c:V,kN a c)=∑c∈(univ.erase a),kN a b:=by rw [<-sum_erase_add _ _ (mem_univ a),KP,fq];apply cZ rfl;intro c hc;exact ML a c b (iK.mp hc).1.symm hab
 rw [heq,d5,oL (mem_univ a)] at hsum;simpa using hsum
lemma Fb (e:V ≃ V) (a b c d:V):lI (e a) (e b) (e c) (e d)=lI a b c d:=by
 classical
 symm;exact g9 ((transport e).subtypeEquiv (by intro p;simp))
lemma MM (a b c d e:V)
  (had:a≠d) (hae:a≠e) (hbd:b≠d) (hbe:b≠e)
  (hcd:c≠d) (P8:c≠e):lI a b c d=lI a b c e:=by
 classical
 have h:=Fb (Equiv.swap d e) a b c d;simpa [m6 had hae,m6 hbd hbe,m6 hcd P8] using h.symm
lemma Fc (a b c d:V) (hac:a≠c) (hbc:b≠c)
  (hd:d=a\/d=b\/d=c):lI a b c d=0:=by
 classical
 unfold lI;apply card_eq_zero_iff.mpr;refine ⟨λ p=>?_⟩;rcases p.property with ⟨hab,hcd⟩;rcases hd with rfl | rfl | rfl
 ·have h:=aF p.val hcd;simp only [apply_apply,hab] at h;exact hbc h.symm
 ·have h:=aF p.val hab;have h':=aF p.val hcd;simp only [apply_apply] at h h';exact hac (h.trans h'.symm)
 ·exact p.val.apply_ne _ hcd
lemma HO (a b c d:V)
  (hab:a≠b) (hac:a≠c) (had:a≠d)
  (hbc:b≠c) (hbd:b≠d) (hcd:c≠d):(Fintype.card V-3)*lI a b c d=kN a b:=by
 classical
 let Q:={p:Pairing V // p a=b};have hsum:(∑e:V,lI a b c e)=kN a b:=by
  have lN:∀e:V,Fintype.card {p:Q // p.val c=e}=lI a b c e:=by intro e;apply g9;exact ⟨λ p=>⟨p.val.val,p.val.property,p.property⟩,λ p=>⟨⟨p.val,p.property.1⟩,p.property.2⟩,λ _=>rfl,λ _=>rfl⟩
  calc
   (∑e:V,lI a b c e)=∑e:V,Fintype.card {p:Q // p.val c=e}:=by simp_rw [lN]
   _=Fintype.card Q:=by rw [<-fy];exact g9 (Equiv.sigmaFiberEquiv (λ p:Q=>p.val c))
   _=kN a b:=rfl
 let S:Finset V:={a,b,c};have LS:S.card=3:=by simp [S,hab,hac,hbc]
 have N5:(∑e:V,lI a b c e)=∑e∈univ\S,lI a b c d:=by
  rw [<-Finset.sum_sdiff (s₁:=S) (s₂:=univ) (by simp)];have hz:∑e∈S,lI a b c e=0:=by apply Finset.sum_eq_zero;intro e he;exact Fc a b c e hac hbc (by simpa [S] using he)
  rw [hz,fq];apply cZ rfl;intro e he;have he':e≠a/\e≠b/\e≠c:=by simpa [S] using (aS.mp he).2
  exact MM a b c e d he'.1.symm had he'.2.1.symm hbd he'.2.2.symm hcd
 rw [N5,d5,Finset.card_sdiff,Finset.inter_univ,LS] at hsum;simpa using hsum
lemma LX (hV:Even (Fintype.card V)) (a b:V) (hab:a≠b):(kN a b:ℝ)/Fintype.card (Pairing V)=1/(Fintype.card V-1:ℝ):=by
 classical
 have hn:2<=Fintype.card V:=Fintype.one_lt_card_iff_nontrivial.mpr ⟨a,b,hab⟩;have Wm:=z7 a b hab;have aae:((Fintype.card V:ℝ)-1)*(kN a b:ℝ)=Fintype.card (Pairing V):=by have h:=aF (λ n:ℕ=>(n:ℝ)) Wm;simpa only [k8,Nat.cast_sub (show 1<=Fintype.card V by omega),gR] using h
 have:Nonempty (Pairing V):=vg hV;have hp:(0:ℝ)<Fintype.card (Pairing V):=by exact_mod_cast Fintype.card_pos
 have hn':(0:ℝ)<Fintype.card V-1:=by
  have Yk:(2:ℝ)<=Fintype.card V:=by exact_mod_cast hn
  linarith
 apply (div_eq_div_iff hp.ne' hn'.ne').mpr;nlinarith
lemma LY (hV:Even (Fintype.card V)) (a b c d:V)
  (hab:a≠b) (hac:a≠c) (had:a≠d)
  (hbc:b≠c) (hbd:b≠d) (hcd:c≠d):(lI a b c d:ℝ)/Fintype.card (Pairing V)=1/((Fintype.card V-1:ℝ)*(Fintype.card V-3:ℝ)):=by
 classical
 have hn:4<=Fintype.card V:=by
  have:({a,b,c,d}:Finset V).card=4:=by simp [hab,hac,had,hbc,hbd,hcd]
  exact this.symm▸e4 _
 have NR:=z7 a b hab;have htwo:=HO a b c d hab hac had hbc hbd hcd;have hb:((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)*(lI a b c d:ℝ)=Fintype.card (Pairing V):=by
  have h1:((Fintype.card V:ℝ)-1)*(kN a b:ℝ)=Fintype.card (Pairing V):=by have h:=aF (λ n:ℕ=>(n:ℝ)) NR;simpa only [k8,Nat.cast_sub (show 1<=Fintype.card V by omega),gR] using h
  have h2:((Fintype.card V:ℝ)-3)*(lI a b c d:ℝ)=kN a b:=by have h:=aF (λ n:ℕ=>(n:ℝ)) htwo;simpa only [k8,Nat.cast_sub (show 3<=Fintype.card V by omega),j8] using h
  nlinarith
 have:Nonempty (Pairing V):=vg hV;have hp:(0:ℝ)<Fintype.card (Pairing V):=by exact_mod_cast Fintype.card_pos
 have hn':(0:ℝ)<Fintype.card V-3:=by
  have Yk:(4:ℝ)<=Fintype.card V:=by exact_mod_cast hn
  linarith
 have RN:(0:ℝ)<Fintype.card V-1:=by linarith
 apply (div_eq_div_iff hp.ne' (f7 RN hn').ne').mpr;nlinarith
end Pairing
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
def bz {α:Type cz} [Fintype α] (f:α->ℝ):ℝ:=(∑x,f x)/card α
lemma wW {α:Type cP} {β:Type cL} [Fintype α] [Fintype β]
  (e:α ≃ β) (f:β->ℝ):bz (λ x=>f (e x))=bz f:=by
 unfold bz;rw [e.sum_comp,g9 e]
lemma qM {α:Type c9} [Fintype α] (f g:α->ℝ):bz (λ x=>f x+g x)=bz f+bz g:=by simp [bz,f8,add_div]
lemma qN {α:Type dW} {ι:Type eo} [Fintype α] (s:Finset ι) (f:ι->α->ℝ):bz (λ x=>∑i∈s,f i x)=∑i∈s,bz (f i):=by unfold bz;rw [gD,sum_div]
lemma Ee {α:Type d8} [Fintype α] [Nonempty α] (r:ℝ):bz (λ _:α=>r)=r:=by
 have h:(Fintype.card α:ℝ)≠0:=by exact_mod_cast Fintype.card_ne_zero
 simp [bz,h]
lemma tC {α:Type d9} [Fintype α] {f g:α->ℝ}
  (h:∀a,f a<=g a):bz f<=bz g:=by
 apply e5 _ (aN _);exact aK (λ a _=>h a)
lemma xW {α:Type eO} {β:Type fX} [Fintype α] [Fintype β]
  (f:α->ℝ) (g:β->ℝ):bz (λ x:α×β=>f x.1*g x.2)=bz f*bz g:=by
 unfold bz;rw [sum_prod_type,card_prod,k8];simp_rw [<-dR];rw [<-sum_mul];ring
lemma AI {α:Type gu} [Fintype α] [Nonempty α] (f:α->ℝ):∃a,f a<=bz f:=by
 have hp:(0:ℝ)<Fintype.card α:=by exact_mod_cast Fintype.card_pos
 have h:∑a,f a<=∑_a:α,bz f:=by simp only [d5,c7,j7,bz];field_simp;rfl
 obtain ⟨a,ha,h⟩:=Finset.exists_le_of_sum_le (Finset.univ_nonempty) h;exact ⟨a,h⟩
lemma uu {α:Type gX} [Fintype α] (P:α->Prop) [DecidablePred P] :bz (λ a=>if P a then 1 else 0)=(card {a // P a}:ℝ)/card α:=by unfold bz;congr 1;simp [mg]
lemma qZ {ι:Type iN} [Fintype ι] [DecidableEq ι] {Ω:ι->Type wc}
  [∀i,Fintype (Ω i)] [∀i,Nonempty (Ω i)] (i:ι) (f:Ω i->ℝ):bz (λ ω:∀j,Ω j=>f (ω i))=bz f:=by
 classical
 let e:=Equiv.piSplitAt i Ω;have he:=wW e.symm (λ ω:∀j,Ω j=>f (ω i));have he':bz (λ x:Ω i×(∀j:{j // j≠i},Ω j.val)=>f x.1)=bz f:=by have h:=xW f (λ _:(∀j:{j // j≠i},Ω j.val)=>(1:ℝ));simpa only [mul_one,Ee] using h
 rw [<-he];simpa [e,Equiv.piSplitAt_symm_apply] using he'
lemma B9 {ι:Type iO} [Fintype ι] [DecidableEq ι] {Ω:ι->Type we}
  [∀i,Fintype (Ω i)] [∀i,Nonempty (Ω i)] (i j:ι) (hij:i≠j)
  (f:Ω i->ℝ) (g:Ω j->ℝ):bz (λ ω:∀k,Ω k=>f (ω i)*g (ω j))=bz f*bz g:=by
 classical
 let e:=Equiv.piSplitAt i Ω;rw [<-wW e.symm (λ ω:∀k,Ω k=>f (ω i)*g (ω j))];have Wn:(λ x=>f (e.symm x i)*g (e.symm x j))=(λ x:Ω i×(∀k:{k // k≠i},Ω k.val)=>f x.1*g (x.2 ⟨j,hij.symm⟩)):=by funext x;simp [e,Equiv.piSplitAt_symm_apply,hij.symm]
 rw [Wn,xW f (λ x:(∀k:{k // k≠i},Ω k.val)=>g (x ⟨j,hij.symm⟩)),qZ]
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
abbrev bl (V:Type i7) [Fintype V] :=Pairing (V ⊕ Fin (card V % 2))
lemma uG (V:Type jD) [Fintype V] :Even (card (V ⊕ Fin (card V % 2))):=by simp only [fO,dU,Nat.even_iff];omega
instance Ng (V:Type jV) [Fintype V] :Nonempty (bl V):=Pairing.vg (uG V)
def ez {V:Type jW} [Fintype V] (p:bl V) (u v:V):Prop:=p (Sum.inl u)=Sum.inl v
instance Pn {V:Type jX} [Fintype V] (p:bl V) (u v:V):Decidable (ez p u v):=Classical.propDecidable _
lemma MO {V:Type jY} [Fintype V] (p:bl V) {u v:V}
  (h:ez p u v):ez p v u:=by
 have hh:=aF p h;simpa only [ez,Pairing.apply_apply] using hh.symm
lemma sv {V:Type jZ} [Fintype V] (u v:V) (huv:u≠v):bz (λ p:bl V=>if ez p u v then 1 else 0)=1/((card V:ℝ)+(card V % 2:ℕ)-1):=by
 classical
 rw [uu];have h:=Pairing.LX (uG V) (Sum.inl u) (Sum.inl v)
  (by simpa using huv)
 simp only [fO,dU,fP] at h;dsimp only [Pairing.kN,ez] at h ⊢;convert h using 1;congr 2
lemma Gv {V:Type j0} [Fintype V] (a b c d:V)
  (hab:a≠b) (hac:a≠c) (had:a≠d)
  (hbc:b≠c) (hbd:b≠d) (hcd:c≠d):bz (λ p:bl V=>if ez p a b/\ez p c d then 1 else 0)=1/(((card V:ℝ)+(card V%2:ℕ)-1)*((card V:ℝ)+(card V%2:ℕ)-3)):=by
 classical
 rw [uu];have h:=Pairing.LY (uG V)
  (Sum.inl a) (Sum.inl b) (Sum.inl c) (Sum.inl d)
  (by simpa using hab) (by simpa using hac) (by simpa using had)
  (by simpa using hbc) (by simpa using hbd) (by simpa using hcd)
 simp only [fO,dU,fP] at h;dsimp only [Pairing.lI,ez] at h ⊢;convert h using 1;congr 2
lemma Fd {V:Type lC} [Fintype V] (hV:2<=card V)
  (u v:V) (huv:u≠v):bz (λ p:bl V=>if ez p u v then 1 else 0)<=1/((card V:ℝ)-1):=by
 classical
 rw [sv u v huv];have hn:(2:ℝ)<=card V:=by exact_mod_cast hV
 have hm:(0:ℝ)<=(card V%2:ℕ):=aN _;exact h9 (by linarith) (by linarith)
lemma z8 {V:Type lT} [Fintype V] (hV:4<=card V)
  (a b c d:V) (hab:a≠b) (hac:a≠c) (had:a≠d)
  (hbc:b≠c) (hbd:b≠d) (hcd:c≠d):bz (λ p:bl V=>if ez p a b/\ez p c d then 1 else 0)<=1/(((card V:ℝ)-1)*((card V:ℝ)-3)):=by
 classical
 rw [Gv a b c d hab hac had hbc hbd hcd];have hn:(4:ℝ)<=card V:=by exact_mod_cast hV
 have hm:(0:ℝ)<=(card V%2:ℕ):=aN _;apply h9 (f7 (by linarith) (by linarith));exact iJ (by linarith) (by linarith) (by linarith) (by linarith)
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma Ef {Ω:Type lU} [Fintype Ω] (P Q:Ω->Prop):bz (λ ω=>if P ω\/Q ω then 1 else 0)<=bz (λ ω=>if P ω then 1 else 0)+bz (λ ω=>if Q ω then 1 else 0):=by rw [<-qM];apply tC;intro ω;by_cases hp:P ω<;>by_cases hq:Q ω<;>simp [hp,hq]
lemma zm {V:Type n4} [Fintype V] (hV:4<=card V)
  (a b c d:V) (hab:a≠b) (hac:a≠c) (had:a≠d)
  (hbc:b≠c) (hbd:b≠d) (hcd:c≠d):bz (λ p:bl V=>if (ez p a c/\ez p b d)\/(ez p a d/\ez p b c) then 1 else 0)<=2/(((card V:ℝ)-1)*((card V:ℝ)-3)):=by
 have h₁:=z8 hV a c b d hac hab had hbc.symm hcd hbd;have h₂:=z8 hV a d b c had hab hac hbd.symm hcd.symm hbc;have h:=Ef
  (λ p:bl V=>ez p a c/\ez p b d)
  (λ p:bl V=>ez p a d/\ez p b c)
 calc
  _<=bz (λ p:bl V=>if ez p a c/\ez p b d then 1 else 0)+bz (λ p:bl V=>if ez p a d/\ez p b c then 1 else 0):=by convert h using 1<;>congr 3<;>funext p<;>split_ifs<;>rfl
  _<=1/(((card V:ℝ)-1)*((card V:ℝ)-3))+1/(((card V:ℝ)-1)*((card V:ℝ)-3)):=dS h₁ h₂
  _=_:=by ring
lemma Bw {I:Type n5} [Fintype I] [DecidableEq I]
  {V:I->Type wj} [∀i,Fintype (V i)] (i j:I) (hij:i≠j)
  (a c:V i) (hac:a≠c) (b d:V j) (hbd:b≠d):bz (λ p:∀k,bl (V k)=>if ez (p i) a c/\ez (p j) b d then 1 else 0)=(1/((card (V i):ℝ)+(card (V i)%2:ℕ)-1))*(1/((card (V j):ℝ)+(card (V j)%2:ℕ)-1)):=by
 have N4:(λ p:∀k,bl (V k)=>
   if ez (p i) a c/\ez (p j) b d then (1:ℝ) else 0)=(λ p=>(if ez (p i) a c then 1 else 0)*(if ez (p j) b d then 1 else 0)):=by
  funext p;split_ifs<;>simp_all
 rw [N4,B9 (Ω:=λ k=>bl (V k)) i j hij
  (λ p=>if ez p a c then 1 else 0) (λ p=>if ez p b d then 1 else 0),sv a c hac,sv b d hbd]
lemma xg {I:Type qg} [Fintype I] [DecidableEq I]
  {V:I->Type wm} [∀i,Fintype (V i)] (i j:I) (hij:i≠j)
  (hi:2<=card (V i)) (hj:2<=card (V j))
  (a c:V i) (hac:a≠c) (b d:V j) (hbd:b≠d):bz (λ p:∀k,bl (V k)=>if ez (p i) a c/\ez (p j) b d then 1 else 0)<=1/(((card (V i):ℝ)-1)*((card (V j):ℝ)-1)):=by
 rw [Bw i j hij a c hac b d hbd,one_div_mul_one_div];have hi':(2:ℝ)<=card (V i):=by exact_mod_cast hi
 have hj':(2:ℝ)<=card (V j):=by exact_mod_cast hj
 have Lr:(0:ℝ)<=(card (V i)%2:ℕ):=aN _;have PO:(0:ℝ)<=(card (V j)%2:ℕ):=aN _;apply h9 (f7 (by linarith) (by linarith));exact iJ (by linarith) (by linarith) (by linarith) (by linarith)
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
namespace Pairing
variable {V:Type qh}
def Jb (p:Pairing V):Setoid V where
 r u v:=u=v\/p u=v
 iseqv:=⟨λ _=>Or.inl rfl,(by
  intro u v h;rcases h with rfl | h
  ·exact Or.inl rfl
  ·exact Or.inr (by have hh:=aF p h;simpa using hh.symm)),(by
  intro u v w h1 h2;rcases h1 with rfl | h1
  ·exact h2
  rcases h2 with rfl | h2
  ·exact Or.inr h1
  ·left;have hh:=aF p h1;simpa only [apply_apply,h2] using hh)⟩
def lX (p:Pairing V):= Quotient (Jb p)
instance [Fintype V] (p:Pairing V):Fintype (lX p):=by
 classical
 unfold lX;infer_instance
instance (p:Pairing V):DecidableEq (lX p):=Classical.decEq _
def project (p:Pairing V) (v:V):lX p:= Quotient.mk (Jb p) v
lemma xh (p:Pairing V) (u v:V):project p u=project p v↔u=v\/p u=v:= Quotient.eq
lemma xX (p:Pairing V):Function.Surjective (project p):=by intro q;exact Quotient.exists_rep q
@[simp] lemma KQ (p:Pairing V) (v:V):project p (p v)=project p v:=(xh p _ _).mpr (Or.inr (apply_apply p v))
lemma N6 [Fintype V] (p:Pairing V) (q:lX p):card {v // project p v=q}=2:=by
 classical
 obtain ⟨x,rfl⟩:=xX p q;rw [mg];have heq:(univ.filter (λ v=>project p v=project p x))={x,p x}:=by
  ext v;simp only [aD,aQ,b5,bU,gd];rw [xh];constructor
  ·rintro (h | h)
   ·exact Or.inl h
   ·right;have hh:=aF p h;simpa only [apply_apply] using hh
  ·rintro (h | h)
   ·exact Or.inl h
   ·right;subst v;simp
 rw [heq];simp [Ne.symm (apply_ne p x)]
lemma Gw [Fintype V] (p:Pairing V):2*card (lX p)=card V:=by
 classical
 have h:(∑q:lX p,card {v // project p v=q})=card V:=by rw [<-fy];exact g9 (Equiv.sigmaFiberEquiv (project p))
 simpa only [N6,d5,c7,jJ,bK] using h
end Pairing
def qy {V:Type qi} [Fintype V] (p:bl V) (v:V):Pairing.lX p:=p.project (Sum.inl v)
lemma yT {V:Type sD} [Fintype V] (p:bl V) (u v:V):qy p u=qy p v↔u=v\/ez p u v:=by simp only [qy,Pairing.xh,Sum.inl.injEq,ez]
lemma Dk {V:Type sG} [Fintype V] (p:bl V)
  (d:Fin (card V % 2)):∃v:V,p (Sum.inr d)=Sum.inl v:=by
 cases h:p (Sum.inr d) with
 | inl v=>exact ⟨v,rfl⟩
 | inr e=>
   have he:e=d:=by apply Fin.ext;have hd:=d.isLt;have he:=e.isLt;have hh:=Nat.mod_lt (card V) (by omega:0<2);omega
   subst e;exact False.elim (p.apply_ne _ h)
lemma Ca {V:Type sH} [Fintype V] (p:bl V):Function.Surjective (qy p):=by
 intro q;obtain ⟨x,rfl⟩:=p.xX q;cases x with
 | inl v=>exact ⟨v,rfl⟩
 | inr d=>obtain ⟨v,hv⟩:=Dk p d;refine ⟨v,?_⟩;change p.project (Sum.inl v)=p.project (Sum.inr d);rw [<-hv,p.KQ]
lemma Fe {V:Type qj} [Fintype V] (p:bl V):card (Pairing.lX p)=card V-card V/2:=by have h:=p.Gw;simp only [fO,dU] at h;omega
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
variable {V:Type qk} {I:Type qm} [Fintype V] [Fintype I] (X:I->Finset V)
abbrev J4:={v:V // ∀i,v∉X i}
abbrev wB:=J4 X ⊕ (Σ i,X i)
def Fh:wB X->V
 | Sum.inl v=>v.val
 | Sum.inr v=>v.2.val
lemma Bx {V:Type qo} {I:Type qs} [aO:Fintype V] [kr:Fintype I] (X:I->Finset V) (hd:Pairwise (λ i j=>Disjoint (X i) (X j))):Function.Bijective (Fh X):=by
 classical
 constructor
 ·rintro (u | ⟨i,u⟩) (v | ⟨j,v⟩) h
  ·exact aF Sum.inl (aZ h)
  ·change u.val=v.val at h;exact False.elim (u.property j (h.symm▸v.property))
  ·change u.val=v.val at h;exact False.elim (v.property i (h▸u.property))
  ·change u.val=v.val at h
   have hij:i=j:=by by_contra hij;exact aL.mp (hd hij) u.property (h.symm▸v.property)
   subst j;exact aF Sum.inr (Sigma.ext rfl (heq_of_eq (aZ h)))
 ·intro v
  by_cases h:∃i,v∈X i
  ·obtain ⟨i,hi⟩:=h;exact ⟨Sum.inr ⟨i,⟨v,hi⟩⟩,rfl⟩
  ·exact ⟨Sum.inl ⟨v,by simpa only [not_exists] using h⟩,rfl⟩
def qz (hd:Pairwise (λ i j=>Disjoint (X i) (X j))):wB X ≃ V:=Equiv.ofBijective (Fh X) (Bx X hd)
abbrev gZ (p:∀i,bl (X i)):=J4 X ⊕ (Σ i,Pairing.lX (p i))
instance (p:∀i,bl (X i)):Fintype (gZ X p):=by
 classical
 unfold gZ;infer_instance
instance (p:∀i,bl (X i)):DecidableEq (gZ X p):=Classical.decEq _
def q0 (p:∀i,bl (X i)):wB X->gZ X p
 | Sum.inl v=>Sum.inl v
 | Sum.inr ⟨i,v⟩=>Sum.inr ⟨i,qy (p i) v⟩
def bD (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
  (p:∀i,bl (X i)):V->gZ X p:=q0 X p∘(qz X hd).symm
lemma z9 (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
  (p:∀i,bl (X i)):Function.Surjective (bD X hd p):=by
 have h:Function.Surjective (q0 X p):=by
  rintro (v | ⟨i,q⟩)
  ·exact ⟨Sum.inl v,rfl⟩
  ·obtain ⟨v,hv⟩:=Ca (p i) q;exact ⟨Sum.inr ⟨i,v⟩,by simp only [q0,hv]⟩
 exact h.comp (qz X hd).symm.surjective
lemma sW (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
  (p:∀i,bl (X i)):card (gZ X p)+∑i,(X i).card/2=card V:=by
 classical
 have hV:=g9 (qz X hd);have Yl:card (J4 X)+∑i,(X i).card=card V:=by simpa only [wB,fO,fy,eG] using hV
 rw [fO,fy,add_assoc,<-f8];simp_rw [Fe,eG,Nat.sub_add_cancel (Nat.div_le_self _ _)];exact Yl
lemma Cc (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
  (p:∀i,bl (X i)):card (gZ X p)=card V-∑i,(X i).card/2:=by
 have h:=sW X hd p;omega
lemma rW (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
  (p:∀i,bl (X i)) (i:I) (v:X i):bD X hd p v.val=Sum.inr ⟨i,qy (p i) v⟩:=by
 have hv:(qz X hd) (Sum.inr ⟨i,v⟩)=v.val:=rfl;rw [bD,Function.comp_apply,<-hv,Equiv.symm_apply_apply];rfl
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type qt} {I:Type qu} [Fintype V] [Fintype I] (X:I->Finset V)
def i5 (p:∀i,bl (X i)) (u v:V):Prop:=∃(i:I) (hu:u∈X i) (hv:v∈X i),ez (p i) ⟨u,hu⟩ ⟨v,hv⟩
lemma s4 (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
  (p:∀i,bl (X i)) (x:wB X):bD X hd p ((qz X hd) x)=q0 X p x:=by
 simp only [bD,Function.comp_apply,Equiv.symm_apply_apply]
lemma jw (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
  (p:∀i,bl (X i)) (u v:V):bD X hd p u=bD X hd p v↔u=v\/i5 X p u v:=by
 constructor
 ·intro h
  obtain ⟨a,rfl⟩:=(qz X hd).surjective u;obtain ⟨b,rfl⟩:=(qz X hd).surjective v;rw [s4,s4] at h;rcases a with a | ⟨i,a⟩<;>rcases b with b | ⟨j,b⟩
  ·exact Or.inl (aF (qz X hd) (aF Sum.inl (Sum.inl.inj h)))
  ·simp only [q0,Sum.inl_ne_inr] at h
  ·simp only [q0,Sum.inr_ne_inl] at h
  ·have hh:=Sum.inr.inj h
   have hij:=aF Sigma.fst hh;change i=j at hij;subst j;have Wo:qy (p i) a=qy (p i) b:=by simpa only [Sigma.mk.inj_iff,heq_eq_eq,b5] using hh
   obtain hab | hab:=(yT (p i) a b).mp Wo
   ·subst b;exact Or.inl rfl
   ·exact Or.inr ⟨i,a.property,b.property,hab⟩
 ·rintro (rfl | ⟨i,hu,hv,hp⟩)
  ·rfl
  ·rw [rW X hd p i ⟨u,hu⟩,rW X hd p i ⟨v,hv⟩];congr 2;exact (yT (p i) ⟨u,hu⟩ ⟨v,hv⟩).mpr (Or.inr hp)
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type qv} {I:Type v7} [Fintype V] [Fintype I] (X:I->Finset V)
 (hd:Pairwise (λ i j=>Disjoint (X i) (X j))) (p:∀i,bl (X i))
lemma vB {u v:V} (huv:u≠v):(Sym2.map (bD X hd p) s(u,v)).IsDiag↔i5 X p u v:=by simp only [Sym2.map_mk,Sym2.mk_isDiag_iff,jw,huv,false_or]
lemma zn {v u w:V} (OI:u≠w)
  (h:Sym2.map (bD X hd p) s(v,u)=Sym2.map (bD X hd p) s(v,w)):i5 X p u w:=by
 have h:=(kc (p:=(bD X hd p v,bD X hd p u))
  (q:=(bD X hd p v,bD X hd p w))).mp h
 simp only [Prod.mk.injEq,Prod.swap_prod_mk] at h;have he:bD X hd p u=bD X hd p w:=by
  rcases h with h | h
  ·exact h.2
  ·exact h.2.trans h.1
 exact ((jw X hd p u w).mp he).resolve_left OI
lemma p7 {u v x y:V}
  (uV:u≠x) (A9:u≠y) (yQ:v≠x) (uW:v≠y)
  (h:Sym2.map (bD X hd p) s(u,v)=Sym2.map (bD X hd p) s(x,y)):
  (i5 X p u x/\i5 X p v y)\/(i5 X p u y/\i5 X p v x):=by
 have h:=(kc (p:=(bD X hd p u,bD X hd p v))
  (q:=(bD X hd p x,bD X hd p y))).mp h
 simp only [Prod.mk.injEq,Prod.swap_prod_mk] at h;rcases h with h | h
 ·exact Or.inl ⟨((jw X hd p u x).mp h.1).resolve_left uV,((jw X hd p v y).mp h.2).resolve_left uW⟩
 ·exact Or.inr ⟨((jw X hd p u y).mp h.1).resolve_left A9,((jw X hd p v x).mp h.2).resolve_left yQ⟩
lemma AJ {V:Type v8} {I:Type v9} [aO:Fintype V] [kr:Fintype I] (X:I->Finset V) (p:(i:I)->af.Batch.bl (Subtype λ x=>x∈X i)) {u v x y:V}
  (uV:i5 X p u x) (uW:i5 X p v y):(∃i,u∈X i/\v∈X i/\x∈X i/\y∈X i)\/(∃i j,i≠j/\u∈X i/\x∈X i/\v∈X j/\y∈X j):=by
 obtain ⟨i,hu,hx,_⟩:=uV;obtain ⟨j,hv,hy,_⟩:=uW;by_cases hij:i=j
 ·subst j;exact Or.inl ⟨i,hu,hv,hx,hy⟩
 ·exact Or.inr ⟨i,j,hij,hu,hx,hv,hy⟩
end
end af.Batch
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX gu gX iN iO i7 jD jV jW jX kB jY kC kD kE kF jZ j0
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type bX} [Fintype V] (G:SimpleGraph V)
def aX (X:Finset V) (v:V):ℕ:=(X.filter (G.Adj v)).card
def e6 (X:Finset V):SimpleGraph V where
 Adj u v:=G.Adj u v/\u∈X/\v∈X
 symm:=⟨λ _ _ h=>⟨h.1.symm,h.2.2,h.2.1⟩⟩
 loopless:=⟨λ _ h=>G.irrefl h.1⟩
lemma q1 (X:Finset V) (v:V):aX G X v<=G.degree v:=by
 classical
 rw [<-G.card_neighborFinset_eq_degree];apply aU;intro x hx;exact (G.mem_neighborFinset v x).mpr (aD.mp hx).2
lemma xY {V:Type bY} [aP:Fintype V] (G:SimpleGraph V) (X:Finset V) (v:V):aX G X v=∑x∈X,if G.Adj v x then 1 else 0:=by
 classical
 simp only [aX,cV,ck]
lemma wC (X:Finset V):∑v,aX G X v=∑x∈X,G.degree x:=by
 classical
 simp_rw [xY];rw [gD];apply cZ rfl;intro x hx;simp_rw [G.adj_comm (v:=x)];rw [<-ck];have he:univ.filter (G.Adj x)=G.neighborFinset x:=by ext y;simp
 simp [he]
lemma Dl (X:Finset V) (v:V):(e6 G X).degree v=if v∈X then aX G X v else 0:=by
 classical
 rw [<-oR];by_cases hv:v∈X
 ·simp only [hv,ite_true];congr 1;ext x;rw [oT,aD];change (G.Adj v x/\v∈X/\x∈X)↔_;tauto
 ·have he:(e6 G X).neighborFinset v=∅:=by
   ext x;simp only [oT,notMem_empty];change (G.Adj v x/\v∈X/\x∈X)↔False;tauto
  simp [he,hv]
lemma Aa (X:Finset V):2*(e6 G X).edgeFinset.card=∑x∈X,aX G X x:=by
 classical
 rw [<-sum_degrees_eq_twice_card_edges];simp_rw [Dl];simp
lemma wX (X:Finset V) (a:ℝ)
  (ha:∀x∈X,(G.degree x:ℝ)<=a):2*((e6 G X).edgeFinset.card:ℝ)<=a*X.card:=by
 have q7:=aF (λ n:ℕ=>(n:ℝ)) (Aa G X);push_cast at q7;rw [q7];calc
  _<=∑x∈X,a:=aK λ x hx=>(cq.mpr (q1 G X x)).trans (ha x hx)
  _=_:=by simp [bK]
lemma Jc (X:Finset V) (a:ℝ)
  (ha:∀x∈X,(G.degree x:ℝ)<=a):(∑v,aX G X v:ℝ)<=a*X.card:=by
 have q7:=aF (λ n:ℕ=>(n:ℝ)) (wC G X);push_cast at q7;rw [q7];simpa [bK] using aK (s:=X) (λ x hx=>ha x hx)
lemma Gx (X:Finset V) (a:ℝ) (ha:1<=a)
  (i6:∀x∈X,(G.degree x:ℝ)<=a)
  (tD:∀v,(aX G X v:ℝ)<=a):((∑v,(aX G X v).choose 2:ℕ):ℝ)<=a*(a-1)*X.card/2:=by
 have hb (v:V):((aX G X v).choose 2:ℝ)<=(a-1)*(aX G X v)/2:=by rw [oU];have hn:(0:ℝ)<=aX G X v:=aN _;have hn':=tD v;nlinarith
 calc
  _=∑v,((aX G X v).choose 2:ℝ):=by push_cast;rfl
  _<=∑v,(a-1)*(aX G X v)/2:=aK λ v _=>hb v
  _=(a-1)/2*∑v,(aX G X v:ℝ):=by rw [dR];apply cZ rfl;intro v hv;ring
  _<=(a-1)/2*(a*X.card):=aJ
   (Jc G X a i6) (by positivity)
  _=_:=by ring
def gP (X Y:Finset V):ℕ:=∑x∈X,aX G Y x
lemma yU (X Y:Finset V):gP G X Y=gP G Y X:=by
 classical
 simp only [gP,xY];rw [gD];apply cZ rfl;intro y hy;apply cZ rfl;intro x hx;simp only [G.adj_comm]
lemma Fj (X Y:Finset V) (a:ℝ)
  (i6:∀y∈Y,(G.degree y:ℝ)<=a):(gP G X Y:ℝ)<=a*Y.card:=by
 rw [yU];simp only [gP,eV];calc
  _<=∑y∈Y,a:=aK λ y hy=>(cq.mpr (q1 G X y)).trans (i6 y hy)
  _=_:=by simp [bK]
lemma Ac {I:Type cy} [Fintype I] (X:I->Finset V)
  (hd:Pairwise (λ i j=>Disjoint (X i) (X j))) (v:V):∑i,aX G (X i) v<=G.degree v:=by
 classical
 have hb:((univ:Finset I):Set I).PairwiseDisjoint
   (λ i=>(X i).filter (G.Adj v)):=by
  intro i hi j hj hij;exact (hd hij).mono (eW _ _) (eW _ _)
 simp only [aX];rw [<-j5 hb,<-G.card_neighborFinset_eq_degree];apply aU;intro x hx;obtain ⟨i,hi,hx⟩:=bR.mp hx;exact (G.mem_neighborFinset v x).mpr (aD.mp hx).2
lemma By {I:Type cz} [Fintype I] (X:I->Finset V)
  (hd:Pairwise (λ i j=>Disjoint (X i) (X j))) (i:I) (a:ℝ)
  (i6:∀x∈X i,(G.degree x:ℝ)<=a):(∑j,gP G (X i) (X j):ℝ)<=a*(X i).card:=by
 simp only [gP,eV];rw [gD];calc
  _<=∑x∈X i,a:=by
   apply aK;intro x hx;have hn:=Ac G X hd x;have hn':(∑j,(aX G (X j) x:ℝ))<=G.degree x:=by exact_mod_cast hn
   exact hn'.trans (i6 x hx)
  _=_:=by simp [bK]
lemma Je {I:Type cP} [Fintype I] (X:I->Finset V)
  (hd:Pairwise (λ i j=>Disjoint (X i) (X j))) (a:ℝ) (ha:0<=a)
  (u6:∀i,0<(X i).card)
  (i6:∀i x,x∈X i->(G.degree x:ℝ)<=a) (i:I):(∑j,((gP G (X i) (X j):ℝ)^2/((X i).card*(X j).card)))<=a^2:=by
 have Lr:(0:ℝ)<(X i).card:=by exact_mod_cast u6 i
 calc
  _<=∑j,a/(X i).card*(gP G (X i) (X j):ℝ):=by
   apply aK;intro j hj;have PO:(0:ℝ)<(X j).card:=by exact_mod_cast u6 j
   have he:=Fj G (X i) (X j) a (i6 j);have hn:(0:ℝ)<=gP G (X i) (X j):=aN _;apply (dK (f7 Lr PO)).mpr;field_simp;nlinarith
  _=a/(X i).card*∑j,(gP G (X i) (X j):ℝ):=by rw [dR]
  _<=a/(X i).card*(a*(X i).card):=aJ
   (By G X hd i a (i6 i)) (by positivity)
  _=a^2:=by field_simp
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
def jP {α:Type cL} {β:Type c9} [DecidableEq α] [DecidableEq β] (f:α->β) (s:Finset α):Finset (Finset α):=by
 classical
 exact (s.powersetCard 2).filter (λ p=>(p.image f).card=1)
lemma qA {α:Type dW} {β:Type eo} [DecidableEq α] [DecidableEq β] (f:α->β) (s:Finset α) (p:Finset α):p∈jP f s↔p⊆s/\p.card=2/\(p.image f).card=1:=by
 classical
 simp [jP,and_assoc]
lemma wY {α:Type d7} {β:Type d8} [DecidableEq α] [DecidableEq β] (f:α->β) {s t:Finset α} (h:s⊆t):jP f s⊆jP f t:=by
 classical
 intro p hp;rw [qA] at hp ⊢;exact ⟨hp.1.trans h,hp.2⟩
lemma AK {α:Type d9} {β:Type eO} [DecidableEq α] [DecidableEq β] (f:α->β) (s:Finset α)
  {a b:α} (ha:a∈s) (hb:b∈s) (hne:a≠b) (heq:f a=f b):{a,b}∈jP f s:=by
 classical
 rw [qA];refine ⟨?_,by simp [hne],by simp [heq]⟩;intro x hx;rcases bU.mp hx with rfl | hx
 ·exact ha
 ·exact gd.mp hx▸hb
lemma HQ {α:Type fX} {β:Type gu} [DecidableEq α] [DecidableEq β] (f:α->β) (s:Finset α):∃t⊆s,Set.InjOn f (t:Set α)/\t.image f=s.image f/\s.card-t.card<=(jP f s).card:=by
 classical
 refine strongInductionOn s ?_;intro s ih;by_cases hinj:Set.InjOn f (s:Set α)
 ·exact ⟨s,Subset.rfl,hinj,rfl,by simp⟩
 simp only [Set.InjOn,kQ,not_forall] at hinj;obtain ⟨a,ha,b,hb,heq,hne⟩:=hinj;have hsub:s.erase a⊂s:=erase_ssubset ha;obtain ⟨t,ht,hinj,himage,jF⟩:=ih (s.erase a) hsub;have Jf:=AK f s ha hb hne heq;have hnot:({a,b}:Finset α)∉jP f (s.erase a):=by intro hp;have hh:=(qA f _ _).mp hp;have:=hh.1 (show a∈({a,b}:Finset α) by simp);simp at this
 have hlt:(jP f (s.erase a)).card<(jP f s).card:=by apply oJ;exact oK.mpr ⟨wY f (jm _ _),λ he=>hnot (he▸Jf)⟩
 have Q3:(s.erase a).image f=s.image f:=by
  apply le_antisymm
  ·exact image_subset_image (jm _ _)
  ·intro y hy
   obtain ⟨x,hx,rfl⟩:=bk.mp hy;by_cases Su:x=a
   ·subst x;exact bk.mpr ⟨b,by simp [hb,Ne.symm hne],heq.symm⟩
   ·exact bk.mpr ⟨x,by simp [hx,Su],rfl⟩
 refine ⟨t,ht.trans (jm _ _),hinj,himage.trans Q3,?_⟩;have lN:=oL ha;have aaU:=aU ht;omega
lemma HR {α:Type gX} {β:Type iN} [DecidableEq α] [DecidableEq β] (f:α->β) (s:Finset α) (qB:β->Prop) [DecidablePred qB] :∃t⊆s,(∀x∈t,¬qB (f x))/\Set.InjOn f (t:Set α)/\t.image f=(s.filter (λ x=>¬qB (f x))).image f/\s.card-t.card<=(s.filter (λ x=>qB (f x))).card+(jP f (s.filter (λ x=>¬qB (f x)))).card:=by
 classical
 obtain ⟨t,ht,hinj,himage,jF⟩:=HQ f (s.filter (λ x=>¬qB (f x)));refine ⟨t,ht.trans (eW _ _),?_,hinj,himage,?_⟩
 ·intro x hx;exact (aD.mp (ht hx)).2
 ·have hpart:=card_filter_add_card_filter_not (s:=s) (p:=λ x=>qB (f x));have hle:=aU ht;omega
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
def xk {V:Type iO} {W:Type i7} [Fintype V] (G:SimpleGraph V) (projMap:V->W):ℕ:=by
 classical
 let s:=G.edgeFinset;exact (s.filter (λ e=>(Sym2.map projMap e).IsDiag)).card+(jP (Sym2.map projMap) (s.filter (λ e=>¬(Sym2.map projMap e).IsDiag))).card
lemma vP {V:Type jD} {W:Type jV} [Fintype V]
  (G:SimpleGraph V) (projMap:V->W):∃(gW:Finset (Sym2 V)) (Q:SimpleGraph W),gW⊆G.edgeFinset/\(G.edgeFinset\gW).card<=xk G projMap/\Q.edgeSet=((gW.image (Sym2.map projMap):Finset (Sym2 W)):Set (Sym2 W))/\(∀e∈Q.edgeSet,∃! f,f∈gW/\Sym2.map projMap f=e):=by
 classical
 obtain ⟨t,ht,xx,hinj,himage,jF⟩:=HR (Sym2.map projMap) G.edgeFinset Sym2.IsDiag;let Q:SimpleGraph W:=fromEdgeSet (t.image (Sym2.map projMap):Set (Sym2 W));have hQ:Q.edgeSet=(t.image (Sym2.map projMap):Set (Sym2 W)):=by
  rw [edgeSet_fromEdgeSet];ext e;constructor
  ·exact λ h=>h.1
  ·intro he;refine ⟨he,?_⟩;obtain ⟨f,hf,rfl⟩:=bk.mp he;exact xx f hf
 refine ⟨t,Q,ht,?_,hQ,?_⟩
 ·rw [l6 ht];exact jF
 ·intro e he;rw [hQ] at he;obtain ⟨f,hf,hfe⟩:=bk.mp he;refine ⟨f,⟨hf,hfe⟩,?_⟩;intro g hg;exact hinj hg.1 hf (hg.2.trans hfe.symm)
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type jW} {I:Type jX} [Fintype V] [Fintype I] (X:I->Finset V)
 (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
lemma Gy {V:Type kB} {I:Type jY} [aO:Fintype V] [kr:Fintype I] (X:I->Finset V) (p:∀i,bl (X i)) {u v:V}
  (h:i5 X p u v):i5 X p v u:=by
 obtain ⟨i,hu,hv,hp⟩:=h;exact ⟨i,hv,hu,MO (p i) hp⟩
lemma qC {V:Type kC} {I:Type kD} [aO:Fintype V] [kr:Fintype I] (X:I->Finset V) (hd:Pairwise λ i j=>Disjoint (X i) (X j)) (p:∀i,bl (X i)) (i:I)
  (u v:X i):i5 X p u v↔ez (p i) u v:=by
 constructor
 ·rintro ⟨j,hu,hv,hp⟩
  have hij:i=j:=by by_contra hij;exact aL.mp (hd hij) u.property hu
  subst j;exact hp
 ·intro hp;exact ⟨i,u.property,v.property,hp⟩
lemma Cd {V:Type kE} {I:Type kF} [aO:Fintype V] [kr:Fintype I] (X:I->Finset V) (hd:Pairwise λ i j=>Disjoint (X i) (X j)) (p:∀i,bl (X i)) (i:I)
  {u v:V} (hu:u∈X i) (hp:i5 X p u v):v∈X i:=by
 obtain ⟨j,hu',hv,hp⟩:=hp;have hij:i=j:=by by_contra hij;exact aL.mp (hd hij) hu hu'
 exact hij.symm▸hv
def oB (p:∀i,bl (X i)) (s:Finset V):Prop:=∃u∈s,∃v∈s,u≠v/\i5 X p u v
lemma rL (p:∀i,bl (X i)) (u v:V) (huv:u≠v):oB X p {u,v}↔i5 X p u v:=by
 constructor
 ·rintro ⟨a,ha,b,hb,hab,hp⟩
  simp only [bU,gd] at ha hb;rcases ha with rfl | rfl<;>rcases hb with rfl | rfl
  ·exact False.elim (hab rfl)
  ·exact hp
  ·exact Gy X p hp
  ·exact False.elim (hab rfl)
 ·intro hp;exact ⟨u,by simp,v,by simp,huv,hp⟩
lemma nX {Ω:Type jZ} {A:Type j0} [Fintype Ω]
  (s:Finset A) (P:Ω->A->Prop):bz (λ ω=>((s.filter (P ω)).card:ℝ))=∑a∈s,bz (λ ω=>if P ω a then 1 else 0):=by
 have hf (ω:Ω):((s.filter (P ω)).card:ℝ)=∑a∈s,if P ω a then 1 else 0:=by rw [cV,eV];simp only [gR,ck]
 simp_rw [hf];exact qN s _
include hd in
lemma uw (i:I) (s:Finset V)
  (hs:s⊆X i) (hc:s.card=2) (hm:2<=(X i).card):bz (λ p:∀j,bl (X j)=>if oB X p s then 1 else 0)<=1/((X i).card-1:ℝ):=by
 classical
 obtain ⟨u,v,huv,rfl⟩:=card_eq_two.mp hc;have hu:=hs (show u∈({u,v}:Finset V) by simp);have hv:=hs (show v∈({u,v}:Finset V) by simp);have he (p:∀j,bl (X j)):oB X p {u,v}↔ez (p i) ⟨u,hu⟩ ⟨v,hv⟩:=(rL X p u v huv).trans (qC X hd p i ⟨u,hu⟩ ⟨v,hv⟩);simp_rw [he];rw [qZ (Ω:=λ j=>bl (X j)) i
  (λ p=>if ez p ⟨u,hu⟩ ⟨v,hv⟩ then 1 else 0)]
 convert Fd (V:=(X i)) (by simpa using hm) ⟨u,hu⟩ ⟨v,hv⟩
  (λ h=>huv (aF Subtype.val h)) using 1;simp
def uX (G:SimpleGraph V) (p:∀i,bl (X i)) (i:I) (v:V):=(((X i).filter (G.Adj v)).powersetCard 2).filter (oB X p)
include hd in
lemma Eg (G:SimpleGraph V) (i:I) (v:V)
  (hm:2<=(X i).card):bz (λ p:∀j,bl (X j)=>((uX X G p i v).card:ℝ))<=((aX G (X i) v).choose 2:ℝ)/((X i).card-1:ℝ):=by
 classical
 change bz (λ p=>(((((X i).filter (G.Adj v)).powersetCard 2).filter
  (oB X p)).card:ℝ))<=_
 rw [nX];calc
  _<=∑_s∈((X i).filter (G.Adj v)).powersetCard 2,1/((X i).card-1:ℝ):=by apply aK;intro s hs;obtain ⟨hs,hc⟩:=lu.mp hs;exact uw X hd i s (hs.trans (eW _ _)) hc hm
  _=_:=by simp [nP,aX,gq]
lemma n9 {G:SimpleGraph V} {S:Finset V} {u v:V}:s(u,v)∈(e6 G S).edgeFinset↔G.Adj u v/\u∈S/\v∈S:=by simp only [cu,ic];rfl
def jy (G:SimpleGraph V) (S T:Finset V):SimpleGraph V where
 Adj u v:=G.Adj u v/\((u∈S/\v∈T)\/(u∈T/\v∈S))
 symm:=⟨λ _ _ h=>⟨h.1.symm,h.2.elim (λ h=>Or.inr ⟨h.2,h.1⟩)
  (λ h=>Or.inl ⟨h.2,h.1⟩)⟩⟩
 loopless:=⟨λ _ h=>G.irrefl h.1⟩
lemma Eh (G:SimpleGraph V) {e f:Sym2 V}
  (he:e∈G.edgeFinset) (hf:f∈G.edgeFinset) (xH:e≠f):(∃v u w,v≠u/\v≠w/\u≠w/\e=s(v,u)/\f=s(v,w))\/(∃u v x y,u≠v/\x≠y/\u≠x/\u≠y/\v≠x/\v≠y/\e=s(u,v)/\f=s(x,y)):=by
 obtain ⟨a,b⟩:=e;obtain ⟨c,d⟩:=f;have hab:a≠b:=(cu.mp he).ne;have hcd:c≠d:=(cu.mp hf).ne;by_cases hac:a=c
 ·subst c;refine Or.inl ⟨a,b,d,hab,hcd,?_,rfl,rfl⟩;intro hbd;exact xH (hbd▸rfl)
 by_cases had:a=d
 ·subst d;refine Or.inl ⟨a,b,c,hab,hcd.symm,?_,rfl,bx⟩;intro hbc;subst c;exact xH bx
 by_cases hbc:b=c
 ·subst c;refine Or.inl ⟨b,a,d,hab.symm,hcd,?_,bx,rfl⟩;intro had;subst d;exact xH bx
 by_cases hbd:b=d
 ·subst d;refine Or.inl ⟨b,a,c,hab.symm,hcd.symm,?_,bx,bx⟩;intro hac;subst c;exact xH rfl
 exact Or.inr ⟨a,b,c,d,hab,hcd,hac,had,hbc,hbd,rfl,rfl⟩
lemma yG (i:I) (hm:4<=(X i).card)
  (u v x y:X i) (huv:u≠v) (uV:u≠x) (A9:u≠y)
  (yQ:v≠x) (uW:v≠y) (hxy:x≠y):bz (λ p:∀j,bl (X j)=>
   if Sym2.map (bD X hd p) s((u:V),(v:V))=Sym2.map (bD X hd p) s((x:V),(y:V)) then 1 else 0)<=
   2/(((X i).card-1:ℝ)*((X i).card-3:ℝ)):=by
 classical
 have hmono:bz (λ p:∀j,bl (X j)=>
   if Sym2.map (bD X hd p) s((u:V),(v:V))=Sym2.map (bD X hd p) s((x:V),(y:V)) then 1 else 0)<=
   bz (λ p:∀j,bl (X j)=>
   if (ez (p i) u x/\ez (p i) v y)\/(ez (p i) u y/\ez (p i) v x) then 1 else 0):=by
  apply tC;intro p;by_cases hc:Sym2.map (bD X hd p) s((u:V),(v:V))=Sym2.map (bD X hd p) s((x:V),(y:V))
  ·have hh:=p7 X hd p (λ h=>uV (aZ h))
    (λ h=>A9 (aZ h)) (λ h=>yQ (aZ h))
    (λ h=>uW (aZ h)) hc
   have he:(ez (p i) u x/\ez (p i) v y)\/(ez (p i) u y/\ez (p i) v x):=by simpa only [qC X hd p i] using hh
   simp only [ej hc,ej he,le_refl]
  ·rw [if_neg hc];split_ifs<;>norm_num
 apply hmono.trans;rw [qZ (Ω:=λ j=>bl (X j)) i
  (λ p=>if (ez p u x/\ez p v y)\/(ez p u y/\ez p v x)
   then 1 else 0)]
 simpa only [eG] using zm
  (V:=(X i)) (by simpa using hm) u v x y huv uV A9 yQ uW hxy
lemma AL (i j:I) (hij:i≠j)
  (hi:2<=(X i).card) (hj:2<=(X j).card)
  (u x:X i) (v y:X j) (uV:u≠x) (uW:v≠y):bz (λ p:∀k,bl (X k)=>
   if Sym2.map (bD X hd p) s((u:V),(v:V))=Sym2.map (bD X hd p) s((x:V),(y:V)) then 1 else 0)<=
   1/(((X i).card-1:ℝ)*((X j).card-1:ℝ)):=by
 classical
 have A9:(u:V)≠y:=by intro h;exact aL.mp (hd hij) u.property (h▸y.property)
 have yQ:(v:V)≠x:=by intro h;exact aL.mp (hd hij) (h▸x.property) v.property
 have hmono:bz (λ p:∀k,bl (X k)=>
   if Sym2.map (bD X hd p) s((u:V),(v:V))=Sym2.map (bD X hd p) s((x:V),(y:V)) then 1 else 0)<=
   bz (λ p:∀k,bl (X k)=>
   if ez (p i) u x/\ez (p j) v y then 1 else 0):=by
  apply tC;intro p;by_cases hc:Sym2.map (bD X hd p) s((u:V),(v:V))=Sym2.map (bD X hd p) s((x:V),(y:V))
  ·have hh:=p7 X hd p (λ h=>uV (aZ h))
    A9 yQ (λ h=>uW (aZ h)) hc
   have he:ez (p i) u x/\ez (p j) v y:=by
    rcases hh with hh | hh
    ·exact ⟨(qC X hd p i u x).mp hh.1,(qC X hd p j v y).mp hh.2⟩
    ·have hy:=Cd X hd p i u.property hh.1;exact False.elim (aL.mp (hd hij) hy y.property)
   simp only [ej hc,ej he,le_refl]
  ·rw [if_neg hc];split_ifs<;>norm_num
 apply hmono.trans;simpa only [eG] using xg
  (V:=λ k=>X k) i j hij (by simpa using hi) (by simpa using hj) u x uV v y uW
end
end af.Batch
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX gu gX iN iO i7 jD jV jW jX kB jY kC kD kE kF jZ j0 lC lT lU
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type bX} {I:Type bY} [Fintype V] [Fintype I] (X:I->Finset V)
 (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
lemma Jg (G:SimpleGraph V) (S T:Finset V) (Ym:Disjoint S T):(jy G S T).edgeFinset.card=gP G S T:=by
 classical
 have hdeg (v:V):(jy G S T).degree v=(if v∈S then aX G T v else 0)+(if v∈T then aX G S v else 0):=by
  rw [<-oR];have Wp:(jy G S T).neighborFinset v=(if v∈S then T.filter (G.Adj v) else ∅)∪(if v∈T then S.filter (G.Adj v) else ∅):=by ext x;simp only [oT,gQ];change (G.Adj v x/\((v∈S/\x∈T)\/(v∈T/\x∈S)))↔_;split_ifs<;>simp_all only [aD,notMem_empty]<;>tauto
  rw [Wp,j9]
  ·split_ifs<;>simp [aX]
  ·split_ifs with hs ht ht
   ·exact False.elim (aL.mp Ym hs ht)
   all_goals simp
 have hh:=(jy G S T).sum_degrees_eq_twice_card_edges;simp_rw [hdeg] at hh;rw [f8] at hh;have hS:(∑v,if v∈S then aX G T v else 0)=gP G S T:=by simp [gP]
 have hT:(∑v,if v∈T then aX G S v else 0)=gP G T S:=by simp [gP]
 rw [hS,hT,yU G T S] at hh;omega
def qd (p:∀i,bl (X i)) (q:Finset (Sym2 V)):Prop:=(q.image (Sym2.map (bD X hd p))).card=1
lemma tJ (p:∀i,bl (X i)) (e f:Sym2 V):qd X hd p {e,f}↔Sym2.map (bD X hd p) e=Sym2.map (bD X hd p) f:=by
 classical
 by_cases h:Sym2.map (bD X hd p) e=Sym2.map (bD X hd p) f
 ·simp [qd,h]
 ·simp [qd,h,card_pair h]
def lJ (q:Finset (Sym2 V)):Prop:=∃u v x y:V,u≠v/\x≠y/\u≠x/\u≠y/\v≠x/\v≠y/\q={s(u,v),s(x,y)}
def nF (H:SimpleGraph V) (p:∀i,bl (X i)):=((H.edgeFinset.powersetCard 2).filter lJ).filter (qd X hd p)
def zo (G:SimpleGraph V) (p:∀i,bl (X i)) (i:I):=(e6 G (X i)).edgeFinset.filter
  (λ e=>(Sym2.map (bD X hd p) e).IsDiag)
lemma Fk (G:SimpleGraph V) (i:I) (hm:2<=(X i).card):bz (λ p:∀j,bl (X j)=>((zo X hd G p i).card:ℝ))<=((e6 G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ):=by
 classical
 change bz (λ p=>(((e6 G (X i)).edgeFinset.filter _).card:ℝ))<=_;have P6:=nX (s:=(e6 G (X i)).edgeFinset)
  (P:=λ (p:∀j,bl (X j)) e=>(Sym2.map (bD X hd p) e).IsDiag)
 calc
  _=∑e∈(e6 G (X i)).edgeFinset,bz (λ p:∀j,bl (X j)=>
     if (Sym2.map (bD X hd p) e).IsDiag then 1 else 0):=by
   convert P6 using 1<;>congr 4
   ·funext p;congr 2;ext e;simp only [aD]
   ·funext e;congr 1;funext p;split_ifs<;>rfl
  _<=_:=by
   calc
    _<=∑_e∈(e6 G (X i)).edgeFinset,1/((X i).card-1:ℝ):=by
     apply aK;intro e he;obtain ⟨u,v⟩:=e;obtain ⟨huv,hu,hv⟩:=n9.mp he;have heq (p:∀j,bl (X j)):(Sym2.map (bD X hd p) s(u,v)).IsDiag↔oB X p {u,v}:=(vB X hd p huv.ne).trans (rL X p u v huv.ne).symm;simp_rw [heq];exact uw X hd i {u,v} (by intro z hz;rcases bU.mp hz with rfl | hz;exact hu;exact gd.mp hz▸hv)
      (by simp [huv.ne]) hm
    _=_:=by simp [gq]
lemma xZ (G:SimpleGraph V) (i:I) (hm:4<=(X i).card):bz (λ p:∀j,bl (X j)=>
   ((nF X hd (e6 G (X i)) p).card:ℝ))<=((e6 G (X i)).edgeFinset.card.choose 2:ℝ)*(2/(((X i).card-1:ℝ)*((X i).card-3:ℝ))):=by
 classical
 change bz (λ p=>(((((e6 G (X i)).edgeFinset.powersetCard 2).filter lJ).filter _).card:ℝ))<=_;rw [nX];calc
  _<=∑_q∈((e6 G (X i)).edgeFinset.powersetCard 2).filter lJ,2/(((X i).card-1:ℝ)*((X i).card-3:ℝ)):=by
   apply aK;intro q hq;obtain ⟨hq,hdis⟩:=aD.mp hq;obtain ⟨u,v,x,y,huv,hxy,uV,A9,yQ,uW,rfl⟩:=hdis;have hsub:=(lu.mp hq).1;obtain ⟨he,hu,hv⟩:=n9.mp (hsub (by simp:s(u,v)∈({s(u,v),s(x,y)}:Finset (Sym2 V))));obtain ⟨hf,hx,hy⟩:=n9.mp (hsub (by simp:s(x,y)∈({s(u,v),s(x,y)}:Finset (Sym2 V))));simp_rw [tJ];exact yG X hd i hm ⟨u,hu⟩ ⟨v,hv⟩ ⟨x,hx⟩ ⟨y,hy⟩
    (λ h=>huv (aF Subtype.val h)) (λ h=>uV (aF Subtype.val h))
    (λ h=>A9 (aF Subtype.val h)) (λ h=>yQ (aF Subtype.val h))
    (λ h=>uW (aF Subtype.val h)) (λ h=>hxy (aF Subtype.val h))
  _<=_:=by
   simp only [d5,j7];apply aY
   ·exact_mod_cast (card_filter_le _ _).trans_eq (nP _ _)
   ·have:(4:ℝ)<=(X i).card:=by exact_mod_cast hm
    exact fF (by norm_num) (bZ (by linarith) (by linarith))
lemma Bz {V:Type cy} {I:Type cz} [aO:Fintype V] [kr:Fintype I] (X:I->Finset V) (G:SimpleGraph V) (i j:I)
  (q:Finset (Sym2 V)) (hq:q⊆(jy G (X i) (X j)).edgeFinset)
  (hdis:lJ q):∃(u x:X i) (v y:X j),u≠x/\v≠y/\q={s((u:V),(v:V)),s((x:V),(y:V))}:=by
 classical
 obtain ⟨u,v,x,y,huv,hxy,uV,A9,yQ,uW,rfl⟩:=hdis;have he:=cu.mp (hq (by simp:s(u,v)∈({s(u,v),s(x,y)}:Finset (Sym2 V))));have hf:=cu.mp (hq (by simp:s(x,y)∈({s(u,v),s(x,y)}:Finset (Sym2 V))));rcases he.2 with ⟨Qb,Ku⟩ | ⟨LZ,Nh⟩<;>rcases hf.2 with ⟨Ve,Vf⟩ | ⟨Vg,Vh⟩
 ·exact ⟨⟨u,Qb⟩,⟨x,Ve⟩,⟨v,Ku⟩,⟨y,Vf⟩,(λ h=>uV (aF Subtype.val h)),(λ h=>uW (aF Subtype.val h)),rfl⟩
 ·refine ⟨⟨u,Qb⟩,⟨y,Vh⟩,⟨v,Ku⟩,⟨x,Vg⟩,(λ h=>A9 (aF Subtype.val h)),(λ h=>yQ (aF Subtype.val h)),?_⟩;rw [bx (a:=y) (b:=x)]
 ·refine ⟨⟨v,Nh⟩,⟨x,Ve⟩,⟨u,LZ⟩,⟨y,Vf⟩,(λ h=>yQ (aF Subtype.val h)),(λ h=>A9 (aF Subtype.val h)),?_⟩;rw [bx (a:=v) (b:=u)]
 ·refine ⟨⟨v,Nh⟩,⟨y,Vh⟩,⟨u,LZ⟩,⟨x,Vg⟩,(λ h=>uW (aF Subtype.val h)),(λ h=>uV (aF Subtype.val h)),?_⟩;rw [bx (a:=v) (b:=u),bx (a:=y) (b:=x)]
lemma Ad (G:SimpleGraph V) (i j:I) (hij:i≠j)
  (hi:2<=(X i).card) (hj:2<=(X j).card):bz (λ p:∀k,bl (X k)=>((nF X hd (jy G (X i) (X j)) p).card:ℝ))<=((gP G (X i) (X j)).choose 2:ℝ)*(1/(((X i).card-1:ℝ)*((X j).card-1:ℝ))):=by
 classical
 change bz (λ p=>(((((jy G (X i) (X j)).edgeFinset.powersetCard 2).filter lJ).filter _).card:ℝ))<=_;rw [nX];calc
  _<=∑_q∈((jy G (X i) (X j)).edgeFinset.powersetCard 2).filter lJ,1/(((X i).card-1:ℝ)*((X j).card-1:ℝ)):=by
   apply aK;intro q hq;obtain ⟨hq,hdis⟩:=aD.mp hq;obtain ⟨u,x,v,y,uV,uW,rfl⟩:=Bz X G i j q
    (lu.mp hq).1 hdis
   simp_rw [tJ];exact AL X hd i j hij hi hj u x v y uV uW
  _<=_:=by
   rw [<-Jg G (X i) (X j) (hd hij)];simp only [d5,j7];apply aY
   ·exact_mod_cast (card_filter_le _ _).trans_eq (nP _ _)
   ·have:(2:ℝ)<=(X i).card:=by exact_mod_cast hi
    have:(2:ℝ)<=(X j).card:=by exact_mod_cast hj
    exact fF (by norm_num) (bZ (by linarith) (by linarith))
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type cP} {I:Type cL} [Fintype V] [Fintype I] (X:I->Finset V)
 (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
lemma Ce (H:SimpleGraph V) (p:∀i,bl (X i))
  (q:Finset (Sym2 V)):q∈nF X hd H p↔q⊆H.edgeFinset/\q.card=2/\lJ q/\qd X hd p q:=by
 classical
 simp [nF,and_assoc]
lemma Ch {G:SimpleGraph V} {S T:Finset V} {u v:V}:s(u,v)∈(jy G S T).edgeFinset↔G.Adj u v/\((u∈S/\v∈T)\/(u∈T/\v∈S)):=by rw [cu];rfl
lemma r3 (G:SimpleGraph V) (p:∀i,bl (X i))
  {u v x y:V} (he:G.Adj u v) (hf:G.Adj x y)
  (uV:i5 X p u x) (uW:i5 X p v y):(∃i,{s(u,v),s(x,y)}⊆(e6 G (X i)).edgeFinset)\/(∃i j,i≠j/\{s(u,v),s(x,y)}⊆(jy G (X i) (X j)).edgeFinset):=by
 classical
 rcases AJ X p uV uW with ⟨i,hu,hv,hx,hy⟩ | ⟨i,j,hij,hu,hx,hv,hy⟩
 ·left
  refine ⟨i,?_⟩;intro e he';rcases bU.mp he' with rfl | he'
  ·exact n9.mpr ⟨he,hu,hv⟩
  ·exact gd.mp he'▸n9.mpr ⟨hf,hx,hy⟩
 ·right
  refine ⟨i,j,hij,?_⟩;intro e he';rcases bU.mp he' with rfl | he'
  ·exact Ch.mpr ⟨he,Or.inl ⟨hu,hv⟩⟩
  ·exact gd.mp he'▸Ch.mpr ⟨hf,Or.inl ⟨hx,hy⟩⟩
def Dm (G:SimpleGraph V) (p:∀i,bl (X i)):Finset (Finset (Sym2 V)):=univ.biUnion λ i=>univ.biUnion λ v=>(uX X G p i v).image (λ q=>q.image (λ u=>s(v,u)))
def yI (G:SimpleGraph V) (p:∀i,bl (X i)):Finset (Finset (Sym2 V)):=univ.biUnion λ i=>nF X hd (e6 G (X i)) p
def Jh (G:SimpleGraph V) (p:∀i,bl (X i)):Finset (Finset (Sym2 V)):=univ.biUnion λ i=>(univ.erase i).biUnion λ j=>nF X hd (jy G (X i) (X j)) p
lemma BA (G:SimpleGraph V) (p:∀i,bl (X i)):jP (Sym2.map (bD X hd p)) G.edgeFinset⊆Dm X G p∪yI X hd G p∪Jh X hd G p:=by
 classical
 intro q hq;obtain ⟨hsub,lN,himage⟩:=(qA _ _ _).mp hq;obtain ⟨e,f,xH,rfl⟩:=card_eq_two.mp lN;have he:=hsub (by simp:e∈({e,f}:Finset (Sym2 V)));have hf:=hsub (by simp:f∈({e,f}:Finset (Sym2 V)));have A5:qd X hd p {e,f}:=himage;have heq:=(tJ X hd p e f).mp A5;rcases Eh G he hf xH with Q4 | hdis
 ·obtain ⟨v,u,w,hvu,DN,OI,rfl,rfl⟩:= Q4
  have Jf:=zn X hd p OI heq;obtain ⟨i,hu,hw,Sv⟩:=Jf;apply cQ;apply cQ;apply bR.mpr;refine ⟨i,aQ _,bR.mpr ⟨v,aQ _,?_⟩⟩;apply bk.mpr;refine ⟨{u,w},?_,by simp⟩;apply aD.mpr;refine ⟨lu.mpr ⟨?_,by simp [OI]⟩,?_⟩
  ·intro z hz
   rcases bU.mp hz with rfl | hz
   ·exact aD.mpr ⟨hu,cu.mp he⟩
   ·exact gd.mp hz▸aD.mpr ⟨hw,cu.mp hf⟩
  ·exact (rL X p u w OI).mpr ⟨i,hu,hw,Sv⟩
 ·obtain ⟨u,v,x,y,huv,hxy,uV,A9,yQ,uW,rfl,rfl⟩:=hdis
  have hdis:lJ ({s(u,v),s(x,y)}:Finset (Sym2 V)):=⟨u,v,x,y,huv,hxy,uV,A9,yQ,uW,rfl⟩;have Sx:(∃i,{s(u,v),s(x,y)}⊆(e6 G (X i)).edgeFinset)\/(∃i j,i≠j/\{s(u,v),s(x,y)}⊆(jy G (X i) (X j)).edgeFinset):=by
   rcases p7 X hd p uV A9 yQ uW heq with hh | hh
   ·exact r3 X G p (cu.mp he)
     (cu.mp hf) hh.1 hh.2
   ·have hh':=r3 X G p (cu.mp he)
     (cu.mp hf).symm hh.1 hh.2
    simpa only [bx (a:=y) (b:=x)] using hh'
  rcases Sx with ⟨i,hi⟩ | ⟨i,j,hij,Sy⟩
  ·apply cQ;apply ee;exact bR.mpr ⟨i,aQ _,(Ce X hd _ p _).mpr ⟨hi,by simp [xH],hdis,A5⟩⟩
  ·apply ee;apply bR.mpr;refine ⟨i,aQ _,bR.mpr ⟨j,by simp [hij.symm],?_⟩⟩;exact (Ce X hd _ p _).mpr ⟨Sy,by simp [xH],hdis,A5⟩
lemma Gz (G:SimpleGraph V) (p:∀i,bl (X i)):G.edgeFinset.filter (λ e=>(Sym2.map (bD X hd p) e).IsDiag)⊆univ.biUnion (λ i=>zo X hd G p i):=by
 classical
 intro e he;obtain ⟨he,Qc⟩:=aD.mp he;obtain ⟨u,v⟩:=e;have huv:=cu.mp he;obtain ⟨i,hu,hv,hp⟩:=(vB X hd p huv.ne).mp Qc;exact bR.mpr ⟨i,aQ _,aD.mpr ⟨n9.mpr ⟨huv,hu,hv⟩,Qc⟩⟩
def oC (G:SimpleGraph V) (p:∀i,bl (X i)):ℕ:=∑i,((zo X hd G p i).card+(∑v,(uX X G p i v).card)+(nF X hd (e6 G (X i)) p).card+∑j∈univ.erase i,(nF X hd (jy G (X i) (X j)) p).card)
lemma Ae (G:SimpleGraph V) (p:∀i,bl (X i)):xk G (bD X hd p)<=oC X hd G p:=by
 classical
 have hl:=(aU (Gz X hd G p)).trans
  (c5)
 have hc:=(aU (BA X hd G p)).trans
  (dG _ _)
 have hw:(Dm X G p).card<=∑i,∑v,(uX X G p i v).card:=by apply c5.trans;apply aK;intro i hi;apply c5.trans;exact aK λ v hv=>ju
 have hi:(yI X hd G p).card<=∑i,(nF X hd (e6 G (X i)) p).card:=c5;have hx:(Jh X hd G p).card<=∑i,∑j∈univ.erase i,(nF X hd (jy G (X i) (X j)) p).card:=by apply c5.trans;exact aK λ i hi=>c5
 have hc':=aU (wY (Sym2.map (bD X hd p))
  (eW (λ e=>¬(Sym2.map (bD X hd p) e).IsDiag) G.edgeFinset))
 have Yn:=dG (Dm X G p) (yI X hd G p);unfold xk oC;simp only [f8];omega
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type c9} {I:Type dW} [Fintype V] [Fintype I] (X:I->Finset V)
 (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
lemma t6 (m:ℝ) (hm:8<=m):m/(m-1)<=8/7:=by apply (dK (show 0< m-1 by linarith)).mpr;linarith
lemma HW (m:ℝ) (hm:8<=m):m/(m-3)<=8/5:=by apply (dK (show 0< m-3 by linarith)).mpr;linarith
lemma vC (n:ℕ):(n.choose 2:ℝ)<=(n:ℝ)^2/2:=by rw [oU];have:=aN (α:=ℝ) n;nlinarith
lemma Ej (m a e:ℝ) (hm:8<=m) (he:2*e<=a*m):e/(m-1)+(a*(a-1)*m/2)/(m-1)<=(4/7)*a^2:=by
 have hp:0< m-1:=by linarith
 calc
  _=(e+a*(a-1)*m/2)/(m-1):=by ring
  _<=(a^2*m/2)/(m-1):=(div_le_div_iff_of_pos_right hp).mpr (by nlinarith)
  _=(a^2/2)*(m/(m-1)):=by ring
  _<=(a^2/2)*(8/7):=aJ (t6 m hm) (by positivity)
  _=_:=by ring
lemma BB (m a:ℝ) (e:ℕ) (hm:8<=m) (ha:0<=a)
  (he:2*(e:ℝ)<=a*m):(e.choose 2:ℝ)*(2/((m-1)*(m-3)))<=(16/35)*a^2:=by
 have hp:0< m-1:=by linarith
 have RD:0< m-3:=by linarith
 have Kp:(e:ℝ)^2<=(a*m/2)^2:=by apply sq_le_sq₀ (aN _) (by positivity) |>.mpr;linarith
 calc
  _<=((e:ℝ)^2/2)*(2/((m-1)*(m-3))):=aY
   (vC e) (by positivity)
  _=(e:ℝ)^2/((m-1)*(m-3)):=by ring
  _<=(a*m/2)^2/((m-1)*(m-3)):=e5 Kp (by positivity)
  _=(a^2/4)*((m/(m-1))*(m/(m-3))):=by field_simp;ring
  _<=(a^2/4)*((8/7)*(8/5)):=aJ
   (iJ (t6 m hm) (HW m hm)
    (by positivity) (by norm_num)) (by positivity)
  _=_:=by ring
lemma Ek (m n:ℝ) (e:ℕ) (hm:8<=m) (hn:8<=n):(e.choose 2:ℝ)*(1/((m-1)*(n-1)))<=(32/49)*((e:ℝ)^2/(m*n)):=by
 have hp:0< m-1:=by linarith
 have hq:0<n-1:=by linarith
 have aaV:0< m:=by linarith
 have hn0:0<n:=by linarith
 calc
  _<=((e:ℝ)^2/2)*(1/((m-1)*(n-1))):=aY
   (vC e) (by positivity)
  _=((e:ℝ)^2/(2*m*n))*((m/(m-1))*(n/(n-1))):=by field_simp
  _<=((e:ℝ)^2/(2*m*n))*((8/7)*(8/7)):=aJ
   (iJ (t6 m hm) (t6 n hn)
    (by positivity) (by norm_num)) (by positivity)
  _=_:=by ring
lemma Dn (G:SimpleGraph V) (i:I) (a:ℝ) (ha:1<=a)
  (hm:8<=(X i).card)
  (i6:∀x∈X i,(G.degree x:ℝ)<=a)
  (tD:∀v,(aX G (X i) v:ℝ)<=a):bz (λ p:∀j,bl (X j)=>((zo X hd G p i).card:ℝ)+∑v,((uX X G p i v).card:ℝ))<=(4/7)*a^2:=by
 classical
 rw [qM,qN];have hp:0<((X i).card:ℝ)-1:=by
  have:(8:ℝ)<=(X i).card:=by exact_mod_cast hm
  linarith
 calc
  _<=((e6 G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ)+∑v,((aX G (X i) v).choose 2:ℝ)/((X i).card-1:ℝ):=dS (Fk X hd G i (by omega))
    (aK λ v _=>Eg X hd G i v (by omega))
  _=((e6 G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ)+(∑v,((aX G (X i) v).choose 2:ℝ))/((X i).card-1:ℝ):=by rw [sum_div]
  _<=((e6 G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ)+(a*(a-1)*(X i).card/2)/((X i).card-1:ℝ):=by apply add_le_add_right;exact e5 (by exact_mod_cast Gx G (X i) a ha i6 tD) hp.le
  _<=_:=Ej _ _ _ (by exact_mod_cast hm) (wX G (X i) a i6)
lemma AM (G:SimpleGraph V) (i:I) (a:ℝ) (ha:0<=a)
  (hm:8<=(X i).card) (i6:∀x∈X i,(G.degree x:ℝ)<=a):bz (λ p:∀j,bl (X j)=>((nF X hd (e6 G (X i)) p).card:ℝ))<=(16/35)*a^2:=
 (xZ X hd G i (by omega)).trans
  (BB _ _ _ (by exact_mod_cast hm) ha (wX G (X i) a i6))
lemma Dp (G:SimpleGraph V) (i:I) (a:ℝ) (ha:0<=a)
  (hm:∀i,8<=(X i).card)
  (i6:∀i x,x∈X i->(G.degree x:ℝ)<=a):bz (λ p:∀k,bl (X k)=>∑j∈univ.erase i,((nF X hd (jy G (X i) (X j)) p).card:ℝ))<=(32/49)*a^2:=by
 classical
 rw [qN];calc
  _<=∑j∈univ.erase i,(32/49)*((gP G (X i) (X j):ℝ)^2/((X i).card*(X j).card)):=by
   apply aK;intro j hj;have hij:=(iK.mp hj).1.symm;exact (Ad X hd G i j hij (by have:=hm i;omega) (by have:=hm j;omega)).trans
    (Ek _ _ _ (by exact_mod_cast hm i) (by exact_mod_cast hm j))
  _<=∑j,(32/49)*((gP G (X i) (X j):ℝ)^2/((X i).card*(X j).card)):=by apply jr (jm _ _);intro j hj hj';positivity
  _=(32/49)*∑j,((gP G (X i) (X j):ℝ)^2/((X i).card*(X j).card)):=by rw [dR]
  _<=_:=aJ (Je G X hd a ha (by intro i;have:=hm i;omega) i6 i) (by norm_num)
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type eo} {I:Type d7} [Fintype V] [Fintype I]
lemma Ci (G:SimpleGraph V) (X:I->Finset V)
  (hd:Pairwise (λ i j=>Disjoint (X i) (X j))) (a:ℝ) (ha:1<=a)
  (hm:∀i,8<=(X i).card) (L0:∀i,a^2<=(X i).card)
  (i6:∀i x,x∈X i->(G.degree x:ℝ)<=a)
  (tD:∀i v,(aX G (X i) v:ℝ)<=a):bz (λ p:∀i,bl (X i)=>(oC X hd G p:ℝ))<=2*∑i,((X i).card:ℝ):=by
 classical
 simp only [oC,eV,fP];rw [qN,dR];apply aK;intro i hi;rw [qM,qM];have Il:=Dn X hd G i a ha (hm i) (i6 i) (tD i);have hint:=AM X hd G i a (by linarith) (hm i) (i6 i);have I5:=Dp X hd G i a (by linarith) hm i6;calc
  _<=(4/7)*a^2+(16/35)*a^2+(32/49)*a^2:=dS (dS Il hint) I5
  _<=2*((X i).card:ℝ):=by nlinarith [L0 i,iH a]
lemma L4 (G:SimpleGraph V) (X:I->Finset V)
  (hd:Pairwise (λ i j=>Disjoint (X i) (X j))) (a:ℝ) (ha:1<=a)
  (hm:∀i,8<=(X i).card) (L0:∀i,a^2<=(X i).card)
  (i6:∀i x,x∈X i->(G.degree x:ℝ)<=a)
  (tD:∀i v,(aX G (X i) v:ℝ)<=a):∃(p:∀i,bl (X i)) (gW:Finset (Sym2 V))
   (Q:SimpleGraph (gZ X p)),gW⊆G.edgeFinset/\(G.edgeFinset\gW).card<=2*∑i,(X i).card/\Q.edgeSet=((gW.image (Sym2.map (bD X hd p)):Finset (Sym2 (gZ X p))):Set (Sym2 (gZ X p)))/\
   (∀e∈Q.edgeSet,∃! f,f∈gW/\Sym2.map (bD X hd p) f=e)/\card (gZ X p)=card V-∑i,(X i).card/2:=by
 classical
 obtain ⟨p,hp⟩:=AI (λ p:∀i,bl (X i)=>(oC X hd G p:ℝ));have Sz:=hp.trans (Ci G X hd a ha hm L0 i6 tD);have jF:oC X hd G p<=2*∑i,(X i).card:=by exact_mod_cast Sz
 obtain ⟨gW,Q,hsub,O9,hQ,hrep⟩:=vP G (bD X hd p);exact ⟨p,gW,Q,hsub,O9.trans ((Ae X hd G p).trans jF),hQ,hrep,Cc X hd p⟩
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type d8} [Fintype V] (G:SimpleGraph V)
def fk (X:Finset V) (a:ℝ):Finset V:=univ.filter (λ v=>a<(aX G X v:ℝ))
lemma tK (X:Finset V) (a:ℝ) (v:V):v∈fk G X a↔a<(aX G X v:ℝ):=by simp [fk]
lemma n6 (X Y:Finset V) (a:ℝ)
  (hY:∀v∈Y,(G.degree v:ℝ)<=a):Disjoint (fk G X a) Y:=by
 apply aL.mpr;intro v hv hy;have h₁:=(tK G X a v).mp hv;have h₂:(aX G X v:ℝ)<=G.degree v:=by exact_mod_cast q1 G X v
 exact (not_lt_of_ge (h₂.trans (hY v hy))) h₁
lemma BC (X:Finset V) (a:ℝ) (ha:0<a)
  (hX:∀v∈X,(G.degree v:ℝ)<=a):(fk G X a).card<=X.card:=by
 have hsum:a*(fk G X a).card<=∑v∈fk G X a,(aX G X v:ℝ):=by
  calc
   _=∑_v∈fk G X a,a:=by simp [bK]
   _<=_:=aK λ v hv=>((tK G X a v).mp hv).le
 have hsub:(∑v∈fk G X a,(aX G X v:ℝ))<=∑v,(aX G X v:ℝ):=jr (gS _) (by intros;positivity);have Lx:(∑v,(aX G X v:ℝ))<=a*X.card:=by rw [<-eV,wC G X,eV];simpa [bK] using aK (s:=X) (λ v hv=>hX v hv)
 have hh:=hsum.trans (hsub.trans Lx);have:=(mul_le_mul_iff_right₀ ha).mp hh;exact_mod_cast this
variable {I:Type d9} [Fintype I] (X:I->Finset V)
def kH (a:ℝ) (i:I):SimpleGraph V:=jy G (X i) (fk G (X i) a)
lemma Fl {V:Type eO} [aP:Fintype V] (G:SimpleGraph V) {I:Type fX} [kq:Fintype I] (X:I->Finset V) (a:ℝ) (i:I):kH G X a i<=G:=λ _ _ h=>h.1
lemma Ag {V:Type gu} [aP:Fintype V] (G:SimpleGraph V) {I:Type gX} [kq:Fintype I] (X:I->Finset V) (a:ℝ)
  (hd:Pairwise (λ i j=>Disjoint (X i) (X j)))
  (i6:∀i v,v∈X i->(G.degree v:ℝ)<=a):Pairwise (λ i j=>Disjoint (kH G X a i).edgeSet
   (kH G X a j).edgeSet):=by
 intro i j hij;apply aI.mpr;intro e hei yP;induction e using bJ with
 | _ u v=>
   change G.Adj u v/\((u∈X i/\v∈fk G (X i) a)\/(u∈fk G (X i) a/\v∈X i)) at hei;change G.Adj u v/\((u∈X j/\v∈fk G (X j) a)\/(u∈fk G (X j) a/\v∈X j)) at yP;rcases hei.2 with hi | hi<;>rcases yP.2 with hj | hj
   ·exact aL.mp (hd hij) hi.1 hj.1
   ·exact aL.mp
     (n6 G (X j) (X i) a (i6 i)) hj.1 hi.1
   ·exact aL.mp
     (n6 G (X i) (X j) a (i6 j)) hi.1 hj.1
   ·exact aL.mp (hd hij) hi.2 hj.2
def nJ (a:ℝ):SimpleGraph V where
 Adj u v:=G.Adj u v/\∀i,¬(kH G X a i).Adj u v
 symm:=⟨λ _ _ h=>⟨h.1.symm,λ i hi=>h.2 i hi.symm⟩⟩
 loopless:=⟨λ _ h=>G.irrefl h.1⟩
lemma GA {V:Type iN} [aP:Fintype V] (G:SimpleGraph V) {I:Type iO} [kq:Fintype I] (X:I->Finset V) (a:ℝ):nJ G X a<=G:=λ _ _ h=>h.1
lemma Ah {V:Type i7} [aP:Fintype V] (G:SimpleGraph V) {I:Type jD} [kq:Fintype I] (X:I->Finset V) (a:ℝ) (ha:0<=a) (i:I) (v:V):(aX (nJ G X a) (X i) v:ℝ)<=a:=by
 by_cases hv:v∈fk G (X i) a
 ·have he:(X i).filter ((nJ G X a).Adj v)=∅:=by
   apply l7.mpr;intro u hu;obtain ⟨Qb,hvu⟩:=aD.mp hu;exact hvu.2 i ⟨hvu.1,Or.inr ⟨hv,Qb⟩⟩
  simpa [aX,he] using ha
 ·have JQ:(aX G (X i) v:ℝ)<=a:=dF (λ hh=>hv ((tK G (X i) a v).mpr hh))
  apply dY _ JQ;exact_mod_cast aU (show
   (X i).filter ((nJ G X a).Adj v)⊆(X i).filter (G.Adj v) from
   λ u hu=>aD.mpr ⟨(aD.mp hu).1,(aD.mp hu).2.1⟩)
lemma Cj (a:ℝ) (v:V):(nJ G X a).degree v<=G.degree v:=by
 classical
 exact degree_le_of_le (GA G X a)
lemma Ck (a:ℝ):(nJ G X a).edgeSet∪(⋃ i,(kH G X a i).edgeSet)=G.edgeSet/\
  Disjoint (nJ G X a).edgeSet
   (⋃ i,(kH G X a i).edgeSet):=by
 constructor
 ·ext e
  induction e using bJ with
  | _ u v=>
    simp only [b8,av,ic];change (G.Adj u v/\∀i,¬(kH G X a i).Adj u v)\/(∃i,(kH G X a i).Adj u v)↔G.Adj u v;constructor
    ·rintro (h | ⟨i,hi⟩)
     ·exact h.1
     ·exact hi.1
    ·intro h
     by_cases he:∃i,(kH G X a i).Adj u v
     ·exact Or.inr he
     ·exact Or.inl ⟨h,λ i hi=>he ⟨i,hi⟩⟩
 ·apply aI.mpr
  intro e he hf;induction e using bJ with
  | _ u v=>obtain ⟨i,hi⟩:=av.mp hf;exact he.2 i hi
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
structure uY {V:Type jV} (G:SimpleGraph V) where
 start:V
 finish:V
 walk:G.Walk start finish
 simple:walk.IsPath
lemma tL {V:Type jW} {G:SimpleGraph V} (X H:Set V)
  (yV:∀{u v},G.Adj u v->(u∈X/\v∈H)\/(u∈H/\v∈X))
  {a b:V} (p:G.Walk a b) (hp:0<p.length):(a∈X\/a∈H)/\(b∈X\/b∈H):=by
 have hn:¬p.Nil:=by intro h;have:=h.length_eq_zero;omega
 constructor
 ·exact (yV (p.adj_snd hn)).elim (λ h=>Or.inl h.1) (λ h=>Or.inr h.1)
 ·exact (yV (p.adj_penultimate hn)).elim (λ h=>Or.inr h.2) (λ h=>Or.inl h.2)
lemma El {V:Type jX} {G:SimpleGraph V} (X H:Set V)
  (hd:Disjoint X H)
  (yV:∀{u v},G.Adj u v->(u∈X/\v∈H)\/(u∈H/\v∈X))
  {a b:V} (p:G.Walk a b) (hp:0<p.length) (ha:a∈H):p.snd∈X:=by
 have hn:¬p.Nil:=by intro h;have:=h.length_eq_zero;omega
 rcases yV (p.adj_snd hn) with h | h
 ·exact False.elim (aI.mp hd h.1 ha)
 ·exact h.2
lemma rz {V:Type kB} {G:SimpleGraph V} (X H:Set V)
  (hd:Disjoint X H)
  (yV:∀{u v},G.Adj u v->(u∈X/\v∈H)\/(u∈H/\v∈X))
  {a b:V} (p:G.Walk a b) (hp:0<p.length) (hb:b∈H):p.penultimate∈X:=by
 have hn:¬p.Nil:=by intro h;have:=h.length_eq_zero;omega
 rcases yV (p.adj_penultimate hn) with h | h
 ·exact h.1
 ·exact False.elim (aI.mp hd h.2 hb)
lemma En {V:Type jY} {G:SimpleGraph V} (X H:Set V)
  (hd:Disjoint X H)
  (yV:∀{u v},G.Adj u v->(u∈X/\v∈H)\/(u∈H/\v∈X))
  {a b:V} (p:G.Walk a b) (hs:p.IsPath) (hp:0<p.length):∃q:uY G,q.walk.edgeSet⊆p.edgeSet/\p.length<=q.walk.length+2/\(0<q.walk.length->q.start∈X/\q.finish∈X):=by
 have qL:=tL X H yV p hp;by_cases ha:a∈H
 ·have Vi:=El X H hd yV p hp ha
  by_cases hb:b∈H
  ·refine ⟨⟨p.snd,p.tail.penultimate,p.tail.dropLast,hs.tail.dropLast⟩,?_,?_,?_⟩
   ·intro e he;simp only [Walk.mem_edgeSet,Walk.edges_dropLast,Walk.edges_tail] at he ⊢;exact g7 (List.mem_of_mem_dropLast he)
   ·simp only [Walk.length_dropLast,Walk.length_tail];omega
   ·intro j4
    have ht:0<p.tail.length:=by change 0<p.tail.dropLast.length at j4;rw [Walk.length_dropLast] at j4;omega
    exact ⟨Vi,rz X H hd yV p.tail ht hb⟩
  ·refine ⟨⟨p.snd,b,p.tail,hs.tail⟩,?_,?_,?_⟩
   ·intro e he;simp only [Walk.mem_edgeSet,Walk.edges_tail] at he ⊢;exact g7 he
   ·simp only [Walk.length_tail];omega
   ·intro _;exact ⟨Vi,qL.2.resolve_right hb⟩
 ·by_cases hb:b∈H
  ·refine ⟨⟨a,p.penultimate,p.dropLast,hs.dropLast⟩,?_,?_,?_⟩
   ·intro e he;simp only [Walk.mem_edgeSet,Walk.edges_dropLast] at he ⊢;exact List.mem_of_mem_dropLast he
   ·simp only [Walk.length_dropLast];omega
   ·intro _;exact ⟨qL.1.resolve_right ha,rz X H hd yV p hp hb⟩
  ·exact ⟨⟨a,b,p,hs⟩,Set.Subset.rfl,by change p.length<=p.length+2;omega,λ _=>⟨qL.1.resolve_right ha,qL.2.resolve_right hb⟩⟩
lemma Cl {V:Type kC} {G:SimpleGraph V} (X H:Set V)
  (hd:Disjoint X H)
  (yV:∀{u v},G.Adj u v->(u∈X/\v∈H)\/(u∈H/\v∈X))
  {a b:V} (p:G.Walk a b) (hp:0<p.length) (ha:a∈X) (hb:b∈X):2<=p.length:=by
 by_contra h;have hlen:p.length=1:=by omega
 rcases yV (Walk.adj_of_length_eq_one hlen) with he | he
 ·exact aI.mp hd hb he.2
 ·exact aI.mp hd ha he.1
lemma wD {V:Type kD} {G:SimpleGraph V}
  {a b:V} (p:G.Walk a b) (hp:p.IsPath):p.edges.toFinset.card=p.length:=by
 classical
 rw [eJ hp.isTrail.edges_nodup,Walk.length_edges]
lemma yJ {V:Type kE} {G:SimpleGraph V} (X H:Set V)
  (hd:Disjoint X H)
  (yV:∀{u v},G.Adj u v->(u∈X/\v∈H)\/(u∈H/\v∈X))
  {a b:V} (p:G.Walk a b) (hs:p.IsPath) (hp:0<p.length):∃(q:uY G) (Fn:Finset (Sym2 V)),Fn.card<=2/\Disjoint (Fn:Set (Sym2 V)) q.walk.edgeSet/\(Fn:Set (Sym2 V))∪q.walk.edgeSet=p.edgeSet/\(0<q.walk.length->q.start∈X/\q.finish∈X/\2<=q.walk.length):=by
 classical
 obtain ⟨q,hsub,hlen,qL⟩:=En X H hd yV p hs hp;have Yo:q.walk.edges.toFinset⊆p.edges.toFinset:=by intro e he;exact bw.mpr (hsub (bw.mp he))
 refine ⟨q,p.edges.toFinset\q.walk.edges.toFinset,?_,?_,?_,?_⟩
 ·rw [l6 Yo,wD p hs,wD q.walk q.simple];omega
 ·rw [aI];intro e he hq;exact (aS.mp he).2 (bw.mpr hq)
 ·ext e
  simp only [b8,kQ,aS,bw,Walk.mem_edgeSet];constructor
  ·rintro (h | h)
   ·exact h.1
   ·exact hsub h
  ·intro h
   by_cases he:e∈q.walk.edges
   ·exact Or.inr he
   ·exact Or.inl ⟨h,he⟩
 ·intro j4;obtain ⟨ha,hb⟩:=qL j4;exact ⟨ha,hb,Cl X H hd yV q.walk j4 ha hb⟩
lemma Fo {V:Type kF} {G:SimpleGraph V} {a b:V}
  (p:G.Walk a b) (q:G.Walk b a) (hp:p.IsPath) (hq:q.IsPath)
  (hlen:2<=p.length)
  (xM:∀v∈q.support,v≠a->v≠b->v∉p.support):(p.append q).IsCycle/\(p.append q).edgeSet=p.edgeSet∪q.edgeSet:=by
 refine ⟨hp.isCycle_append hq ?_ (Or.inl (by omega)),Walk.edgeSet_append p q⟩;rw [ct];intro v M9 PX;have OJ:v≠a:=by intro h;subst v;have hn:=hp.support_nodup;rw [<-p.cons_tail_support] at hn;exact hn.notMem M9
 have SB:v≠b:=by intro h;subst v;have hn:=hq.support_nodup;rw [<-q.cons_tail_support] at hn;exact hn.notMem PX
 exact xM v (g7 PX) OJ SB (g7 M9)
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma BD {V:Type jZ} {I:Type j0} [Fintype V] [Fintype I]
  {G:SimpleGraph V} (P:I->iz G) (S:Finset V)
  (qL:∀i,(P i).start∈S/\(P i).finish∈S)
  (lG:∀v,(univ.filter (λ i=>(P i).start=v\/(P i).finish=v)).card<=2):card I<=S.card:=by
 classical
 have heq:∑v∈S,(univ.filter (λ i=>(P i).start=v\/(P i).finish=v)).card=2*card I:=by
  simp only [cV,ck];rw [gD];have hc:∀i:I,(∑v∈S,if (P i).start=v\/(P i).finish=v then 1 else 0)=2:=by
   intro i;have hf:S.filter (λ v=>(P i).start=v\/(P i).finish=v)={(P i).start,(P i).finish}:=by
    ext v;simp only [aD,bU,gd];constructor
    ·intro h;simpa only [gH] using h.2
    ·intro h
     rcases h with rfl | rfl
     ·exact ⟨(qL i).1,Or.inl rfl⟩
     ·exact ⟨(qL i).2,Or.inr rfl⟩
   rw [<-ck,hf];simp [(P i).E3]
  simp_rw [hc];simp [bK]
 have hb:=aK (λ v (_:v∈S)=>lG v);rw [heq] at hb;simp only [d5,jJ] at hb;omega
lemma MP {V:Type lC} [Fintype V] (G:SimpleGraph V)
  (X:Finset V) (a:ℝ) (ha:0<a)
  (hdeg:∀v∈X,(G.degree v:ℝ)<=a):let H:=fk G X a
  let B:=jy G X H
  ∃(k:ℕ) (P:Fin k->iz B),Pairwise (λ i j=>Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)/\(⋃ i,(P i).walk.edgeSet)=B.edgeSet/\k<=2*X.card:=by
 classical
 dsimp only;obtain ⟨k,P,hd,hu,hl,_⟩:=ur (jy G X (fk G X a));refine ⟨k,P,hd,hu,?_⟩;have JX:∀i,(P i).start∈X∪fk G X a/\(P i).finish∈X∪fk G X a:=by
  intro i;have h:=tL (X:Set V) (fk G X a:Set V)
   (λ {_ _} (h:(jy G X (fk G X a)).Adj _ _)=>h.2) (P i).walk (P i).positive
  exact ⟨gQ.mpr h.1,gQ.mpr h.2⟩
 have hk:=BD P (X∪fk G X a) JX hl;rw [dU] at hk;have hh:=BC G X a ha hdeg;exact hk.trans ((dG _ _).trans (by omega))
structure kW {V I:Type} [Fintype V] [Fintype I]
  (G:SimpleGraph V) (X:I->Finset V)
  (hd:Pairwise λ i j=>Disjoint (X i) (X j)) where
 pairing:∀i,bl (X i)
 quotient:SimpleGraph (gZ X pairing)
 gW:Finset (Sym2 V)
 qB:Finset (Sym2 V)
 count:I->ℕ
 path:∀i,Fin (count i)->uY G
 count_le:∀i,count i<=2*(X i).card
 SC:qB.card<=6*∑i,(X i).card
 Ai:∀i j,0<(path i j).walk.length->(path i j).start∈X i/\(path i j).finish∈X i/\2<=(path i j).walk.length
 J5:Pairwise λ z w:Σ i,Fin (count i)=>Disjoint (path z.1 z.2).walk.edgeSet (path w.1 w.2).walk.edgeSet
 OK:∀i j,Disjoint (qB:Set (Sym2 V)) (path i j).walk.edgeSet
 Cm:∀i j,Disjoint (gW:Set (Sym2 V)) (path i j).walk.edgeSet
 L5:Disjoint (qB:Set (Sym2 V)) (gW:Set (Sym2 V))
 cover:(qB:Set (Sym2 V))∪(gW:Set (Sym2 V))∪(⋃ (i) (j),(path i j).walk.edgeSet)=G.edgeSet
 Cn:quotient.edgeSet=(Sym2.map (bD X hd pairing)) '' (gW:Set (Sym2 V))
 Ji:∀e∈quotient.edgeSet,∃! f,f∈gW/\Sym2.map (bD X hd pairing) f=e
 order:card (gZ X pairing)=card V-∑i,(X i).card/2
lemma kW.N7 {V I:Type} [Fintype V] [Fintype I]
  {G:SimpleGraph V} {X:I->Finset V} {hd}
  (b:kW G X hd):(b.qB:Set (Sym2 V))⊆G.edgeSet:=by
 rw [<-b.cover];exact Set.subset_union_of_subset_left (mB) _
lemma kW.Bb {V I:Type} [Fintype V] [Fintype I]
  {G:SimpleGraph V} {X:I->Finset V} {hd}
  (b:kW G X hd):(b.gW:Set (Sym2 V))⊆G.edgeSet:=by
 rw [<-b.cover];exact Set.subset_union_of_subset_left (Set.subset_union_right) _
lemma KR {V I:Type} [Fintype V] [Fintype I]
  (G:SimpleGraph V) (X:I->Finset V)
  (hd:Pairwise λ i j=>Disjoint (X i) (X j))
  (a:ℝ) (ha:1<=a) (hm:∀i,8<=(X i).card)
  (L0:∀i,a^2<=(X i).card)
  (hdeg:∀i v,v∈X i->(G.degree v:ℝ)<=a):Nonempty (kW G X hd):=by
 classical
 let H:=kH G X a;let T:=nJ G X a;have SD:=Ag G X a hd hdeg;have hT:=Ck G X a;have L6:∀i,∃(k:ℕ) (P:Fin k->iz (H i)),Pairwise (λ j l=>Disjoint (P j).walk.edgeSet (P l).walk.edgeSet)/\(⋃ j,(P j).walk.edgeSet)=(H i).edgeSet/\k<=2*(X i).card:=λ i=>MP G (X i) a (by linarith) (hdeg i)
 choose k P Sp Vj hk using L6;have T2:∀i j,∃(q:uY (H i)) (S:Finset (Sym2 V)),S.card<=2/\Disjoint (S:Set _) q.walk.edgeSet/\(S:Set _)∪q.walk.edgeSet=(P i j).walk.edgeSet/\(0<q.walk.length->q.start∈X i/\q.finish∈X i/\2<=q.walk.length):=by
  intro i j;exact yJ (X i:Set V) (fk G (X i) a:Set V)
   (by simpa only [m4] using
    (n6 G (X i) (X i) a (hdeg i)).symm)
   (λ {_ _} (h:(H i).Adj _ _)=>h.2) (P i j).walk (P i j).isPath (P i j).positive
 choose q S T3 Yp J6 T4 using T2;let zq:∀i,Fin (k i)->uY G:=λ i j=>⟨(q i j).start,(q i j).finish,(q i j).walk.map (SimpleGraph.Hom.ofLE (Fl G X a i)),(q i j).simple.map (oQ)⟩
 have J7:∀i j,(zq i j).walk.edgeSet=(q i j).walk.edgeSet:=by intro i j;simp [zq,Walk.edgeSet_map,SimpleGraph.Hom.ofLE]
 have T6:∀i j,(zq i j).walk.length=(q i j).walk.length:=λ i j=>Walk.length_map _ _
 have xA:∀i j,(S i j:Set _)⊆(P i j).walk.edgeSet:=by intro i j;rw [<-J6 i j];exact mB
 have wE:∀i j,(zq i j).walk.edgeSet⊆(P i j).walk.edgeSet:=by intro i j;rw [J7,<-J6 i j];exact Set.subset_union_right
 have Jj:∀i j,(P i j).walk.edgeSet⊆(H i).edgeSet:=λ i j=>(P i j).walk.edges_subset_edgeSet
 have OL:Pairwise λ z w:Σ i,Fin (k i)=>
   Disjoint (P z.1 z.2).walk.edgeSet (P w.1 w.2).walk.edgeSet:=by
  rintro ⟨i,j⟩ ⟨l,m⟩ hne;by_cases hi:i=l
  ·subst l;exact Sp i (λ he=>hne (by cases he;rfl))
  ·exact (SD hi).mono (Jj _ _) (Jj _ _)
 let B:=univ.biUnion λ z:Σ i,Fin (k i)=>S z.1 z.2
 have hB:(B:Set (Sym2 V))=⋃ i,⋃ j,(S i j:Set (Sym2 V)):=by ext e;simp [B]
 have aaf:B.card<=4*∑i,(X i).card:=by
  have hc:B.card<=∑z:Σ i,Fin (k i),(S z.1 z.2).card:=c5;have hj:(∑z:Σ i,Fin (k i),(S z.1 z.2).card)<=2*∑i,k i:=by
   calc
    _<=∑z:Σ i,Fin (k i),2:=aK (λ z _=>T3 z.1 z.2)
    _=_:=by simp [fy,bK]
  have hk':=aK (λ i (_:i∈(univ:Finset I))=>hk i);rw [<-dR] at hk';omega
 have Q5:(B:Set (Sym2 V))⊆⋃ i,(H i).edgeSet:=by rw [hB];exact gJ (λ i=>gJ (λ j=>Set.subset_iUnion_of_subset i ((xA i j).trans (Jj i j))))
 have Wq:∀i j,Disjoint (B:Set (Sym2 V)) (zq i j).walk.edgeSet:=by
  intro i j;rw [hB,kP];intro l;rw [kP];intro m;by_cases he:(⟨l,m⟩:Σ i,Fin (k i))=⟨i,j⟩
  ·cases he
   rw [J7];exact Yp i j
  ·exact (OL he).mono (xA l m) (wE i j)
 have T7:∀i v,v∈X i->(T.degree v:ℝ)<=a:=by intro i v hv;exact (show (T.degree v:ℝ)<=G.degree v by exact_mod_cast Cj G X a v).trans (hdeg i v hv)
 obtain ⟨p,R,Q,hR,Wr,hQ,hrep,uO⟩:=L4 T X hd a ha hm L0 T7
  (Ah G X a (by linarith))
 let A:=T.edgeFinset\R;have hA:(A:Set (Sym2 V))=T.edgeSet\(R:Set (Sym2 V)):=by simp [A,coe_edgeFinset]
 have SE:(R:Set (Sym2 V))⊆T.edgeSet:=by intro e he;exact cu.mp (hR he)
 refine ⟨⟨p,Q,R,A∪B,k,zq,hk,?_,?_,?_,?_,?_,?_,?_,?_,hrep,uO⟩⟩
 ·exact (dG _ _).trans (by have hn:A.card<=2*∑i,(X i).card:=Wr;omega)
 ·intro i j hp;simpa only [zq,Walk.length_map] using T4 i j (by rwa [T6] at hp)
 ·intro z w hzw;exact (OL hzw).mono (wE _ _) (wE _ _)
 ·intro i j
  rw [coe_union,mw];refine ⟨?_,Wq i j⟩;apply hT.2.mono
  ·rw [hA];exact jd
  ·exact (wE i j).trans ((Jj i j).trans (je (λ i=>(H i).edgeSet) i))
 ·intro i j;exact hT.2.mono SE ((wE i j).trans ((Jj i j).trans (je (λ i=>(H i).edgeSet) i)))
 ·rw [coe_union,mw];refine ⟨?_,hT.2.symm.mono Q5 SE⟩;rw [hA];exact Set.disjoint_sdiff_left
 ·have Jk:(B:Set (Sym2 V))∪(⋃ i,⋃ j,(zq i j).walk.edgeSet)=⋃ i,(H i).edgeSet:=by
   rw [hB,<-mj];congr 1;funext i;rw [<-mj];simp_rw [J7,J6];exact Vj i
  rw [coe_union];have Yq:(A:Set (Sym2 V))∪(R:Set (Sym2 V))=T.edgeSet:=by rw [hA];exact mo SE
  calc
   _=((A:Set _)∪(R:Set _))∪((B:Set _)∪⋃ i,⋃ j,(zq i j).walk.edgeSet):=by ext e;simp only [b8];tauto
   _=T.edgeSet∪⋃ i,(H i).edgeSet:=by rw [Yq,Jk]
   _=G.edgeSet:=hT.1
 ·simpa only [coe_image] using hQ
end
end af.Batch
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma x5 {V I:Type} [Fintype V] [Fintype I]
  (X:I->Finset V) (hd:Pairwise λ i j=>Disjoint (X i) (X j))
  (p:∀i,bl (X i)) (W:Finset V) (hX:∀i,X i⊆W):(W.image (bD X hd p)).card+∑i,(X i).card/2=W.card:=by
 classical
 let projMap:=bD X hd p;have hi:Set.InjOn projMap (↑Wᶜ:Set V):=by
  intro x hx y hy h;rcases (jw X hd p x y).mp h with he | ⟨i,Jl,Nj,_⟩
  ·exact he
  ·exact False.elim (cU.mp hx (hX i Jl))
 have GR:Disjoint (W.image projMap) (Wᶜ.image projMap):=by
  apply aL.mpr;rintro z hz L7;obtain ⟨x,hx,rfl⟩:=bk.mp hz;obtain ⟨y,hy,he⟩:=bk.mp L7;rcases (jw X hd p y x).mp he with he | ⟨i,Nj,Jl,_⟩
  ·subst y;exact cU.mp hy hx
  ·exact cU.mp hy (hX i Nj)
 have hu:W.image projMap∪Wᶜ.image projMap=univ:=by rw [<-image_union,union_compl];exact image_univ_of_surjective (z9 X hd p)
 have hc:=j9 GR;rw [hu,c7,nL hi] at hc;have hc':=nO W;have h:=sW X hd p;dsimp only [projMap] at hc;have Yr:=e4 W;omega
lemma kW.x6 {V I:Type} [Fintype V] [Fintype I]
  {G:SimpleGraph V} {X:I->Finset V} {hd}
  (b:kW G X hd) (W:Finset V)
  (hW:∀⦃x y⦄,G.Adj x y->x∈W/\y∈W):∀⦃x y⦄,b.quotient.Adj x y->x∈W.image (bD X hd b.pairing)/\y∈W.image (bD X hd b.pairing):=by
 classical
 intro x y hxy;have he:s(x,y)∈b.quotient.edgeSet:=hxy;rw [b.Cn] at he;obtain ⟨e,he,heq⟩:=he;induction e using bJ with
 | _ u v=>
   have huv:G.Adj u v:=b.Bb he;have hu:=mem_image_of_mem (bD X hd b.pairing) (hW huv).1;have hv:=mem_image_of_mem (bD X hd b.pairing) (hW huv).2;change s(bD X hd b.pairing u,bD X hd b.pairing v)=s(x,y) at heq;rcases jI.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
   ·exact ⟨hu,hv⟩
   ·exact ⟨hv,hu⟩
end
end af.Batch
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX gu gX iN iO i7 jD
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Real Filter Asymptotics
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
lemma vh {A B:Type} [DecidableEq A] [DecidableEq B]
  {H:SimpleGraph A} {J:SimpleGraph B} (f:H →g J)
  (hf:Function.Injective f) {a b:A} (p:H.Walk a b):cE (p.map f)=(cE p).image f:=by
 classical
 simp only [cE,oH];rw [image_sdiff _ _ hf];have hm:(p.support.map f).toFinset=p.support.toFinset.image f:=by ext v;simp
 rw [hm];simp
lemma Eo {I T:Type} [Fintype I]
  (G P:SimpleGraph V) [DecidableRel P.Adj] (oe:P<=G)
  (W:Finset V) (h:ℝ) (hh:0<h)
  (hexp:b9 P W h) (hr:2<=W.card)
  (x y:I->V) (hx:∀i,x i∈W) (hy:∀i,y i∈W)
  (hxy:∀i,x i≠y i) (i4:I->T) (Z:I->Finset V)
  (k b z:ℝ) (hk:1<=k) (hb:1<=b) (hz:0<=z)
  (lG:∀v,(b7 univ x y v:ℝ)<=k)
  (C6:∀i,((univ.filter (λ j=>i4 j=i4 i)).card:ℝ)<=b)
  (hZ:∀i,((Z i).card:ℝ)<=z)
  (oj:64*((dQ W.card h:ℝ)^2*(k+b)+z)<=h):∃q:∀i,G.Walk (x i) (y i),(∀i,(q i).IsPath/\(q i).length<=dQ W.card h/\(∀v∈(q i).support,v∈W)/\(q i).edgeSet⊆P.edgeSet/\Disjoint (cE (q i)) (Z i))/\
   Pairwise (λ i j=>Disjoint (q i).edgeSet (q j).edgeSet)/\(∀i j,i≠j->i4 i=i4 j->Disjoint (cE (q i)) (cE (q j))):=by
 classical
 let X:I->(W:Set V):=λ i=>⟨x i,hx i⟩
 let Y:I->(W:Set V):=λ i=>⟨y i,hy i⟩
 let Z':I->Finset (W:Set V):=λ i=>univ.filter (λ v=>v.val∈Z i)
 have hl (v:(W:Set V)):(b7 univ X Y v:ℝ)<=k:=by simpa only [b7,X,Y,Subtype.ext_iff] using lG v.val
 have L7:∀i,((Z' i).card:ℝ)<=z:=by
  intro i;apply dY _ (hZ i);have hc:(Z' i).card<=(Z i).card:=by
   apply gG Subtype.val
   ·intro v hv;exact (aD.mp hv).2
   ·exact dM.injOn
  exact_mod_cast hc
 obtain ⟨q,hq,hd,ht⟩:=M8 (P.induce (W:Set V)) h hh
  (oh P W h hexp) (by simpa using hr) X Y
  (λ i he=>hxy i (aF Subtype.val he)) i4 Z' k b z hk hb hz hl C6 L7
  (by simpa using oj)
 let f:(P.induce (W:Set V)) →g G:={toFun:=Subtype.val,map_rel':=λ ha=>oe ha};have hf:Function.Injective f:=dM;have lN:card ↥(W:Set V)=W.card:=eG W;let Q:∀i,G.Walk (x i) (y i):=λ i=>(q i).map f
 refine ⟨Q,?_,?_,?_⟩
 ·intro i
  refine ⟨(hq i).1.map hf,?_,?_,?_,?_⟩
  ·simpa only [Q,l8,lN] using (hq i).2.1
  ·intro v hv
   have Io:v∈(q i).support.map f:=by simpa only [Q,oH] using hv
   obtain ⟨a,ha,rfl⟩:=bV.mp Io;exact a.property
  ·intro e he
   rw [g6] at he;obtain ⟨d,hd,rfl⟩:=he;induction d using bJ with
   | _ a b=>exact (q i).adj_of_mem_edges hd
  ·rw [show Q i=(q i).map f from rfl,vh f hf];apply aL.mpr;intro v hv I6;obtain ⟨a,ha,rfl⟩:=bk.mp hv;exact aL.mp (hq i).2.2 ha (by simpa [Z',f] using I6)
 ·intro i j hij;change Disjoint ((q i).map f).edgeSet ((q j).map f).edgeSet;rw [g6,g6,l9 (fI hf)];apply aI.mpr;intro e he he';exact aL.mp (hd i j hij) (by simpa using he) (by simpa using he')
 ·intro i j hij SF;change Disjoint (cE ((q i).map f)) (cE ((q j).map f));rw [vh f hf,vh f hf,disjoint_image hf];exact ht i j hij SF
lemma Cp:∃dN:ℝ,1<dN/\∀D≥dN,∀(A:Type) [Fintype A] [DecidableEq A],∀(G P:SimpleGraph A) [DecidableRel P.Adj],P<=G->∀W:Finset A,b9 P W (D^(9/10:ℝ)/4)->D^(9/10:ℝ)<=(W.card:ℝ)->(W.card:ℝ)<=D^(51/50:ℝ)->∀(I T:Type) [Fintype I] (x y:I->A),(∀i,x i∈W)->(∀i,y i∈W)->(∀i,x i≠y i)->∀(i4:I->T) (Z:I->Finset A),(∀v,(b7 univ x y v:ℝ)<=D^(1/100:ℝ))->(∀i,((univ.filter (λ j=>i4 j=i4 i)).card:ℝ)<=D^(3/10:ℝ))->(∀i,((Z i).card:ℝ)<=2*D^(3/10:ℝ))->∃q:∀i,G.Walk (x i) (y i),(∀i,(q i).IsPath/\(q i).length<=dQ W.card (D^(9/10:ℝ)/4)/\(∀v∈(q i).support,v∈W)/\(q i).edgeSet⊆P.edgeSet/\Disjoint (cE (q i)) (Z i))/\
    Pairwise (λ i j=>Disjoint (q i).edgeSet (q j).edgeSet)/\(∀i j,i≠j->i4 i=i4 j->Disjoint (cE (q i)) (cE (q j))):=by
 obtain ⟨dN,ko,hm⟩:=C8;refine ⟨dN,ko,?_⟩;intro D hD A _ _ G P _ oe W hexp T8 T9 I T _ x y hx hy hxy i4 Z hl ht hZ;have hD1:1<D:=ko.trans_le hD;have hD0:0<D:=lt_trans zero_lt_one hD1;obtain ⟨hr,oj⟩:=hm D hD W.card T8 T9;apply Eo G P oe W _ (by positivity) hexp (by exact_mod_cast hr)
  x y hx hy hxy i4 Z _ _ _ _ _ (by positivity) hl ht hZ oj
 ·exact jv hD1.le (by norm_num)
 ·exact jv hD1.le (by norm_num)
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open SimpleGraph
variable {V:Type bX} {G:SimpleGraph V}
structure t7 (G:SimpleGraph V) where
 start:V
 finish:V
 walk:G.Walk start finish
inductive iT (G:SimpleGraph V):V->V->Type _
 | single {u v:V} (p:G.Walk u v):iT G u v
 | cons {u v w z:V} (p:G.Walk u v) (h:G.Adj v w)
    (q:iT G w z):iT G u z
namespace iT
variable {u v:V}
def walk:{u v:V}->iT G u v->G.Walk u v
 | _,_, .single p=>p
 | _,_, .cons p h q=>p.append (.cons h q.walk)
def gY:{u v:V}->iT G u v->List (t7 G)
 | u,v, .single p=>[⟨u,v,p⟩]
 | u,_, .cons (v:=v) p _ q=>⟨u,v,p⟩ :: q.gY
def Bc:{u v:V}->iT G u v->Set (Sym2 V)
 | _,_, .single _=>∅
 | _,_, .cons (v:=v) (w:=w) _ _ q=>{s(v,w)}∪q.Bc
def r7 (q:iT G u v):Set (Sym2 V):=⋃ p∈q.gY,p.walk.edgeSet
lemma mem_support_iff (q:iT G u v) (x:V):x∈q.walk.support↔∃p∈q.gY,x∈p.walk.support:=by
 induction q with
 | single p=>simp [walk,gY]
 | cons p h q ih=>
   simp only [walk,Walk.mem_support_append_iff,Walk.support_cons,dd,ih,gY,dd];constructor
   ·rintro (hp | rfl | ⟨r,hr,hx⟩)
    ·exact ⟨_,Or.inl rfl,hp⟩
    ·exact ⟨_,Or.inl rfl,p.end_mem_support⟩
    ·exact ⟨r,Or.inr hr,hx⟩
   ·rintro ⟨r,rfl | hr,hx⟩
    ·exact Or.inl hx
    ·exact Or.inr (Or.inr ⟨r,hr,hx⟩)
lemma Ep (q:iT G u v)
  (hp:∀p∈q.gY,p.walk.IsPath)
  (hd:q.gY.Pairwise (λ p r=>p.walk.support.Disjoint r.walk.support)):q.walk.IsPath:=by
 induction q with
 | single p=>exact hp ⟨_,_,p⟩ (by simp [gY])
 | cons p h q ih=>
   have Sm:=(iu.mp hd).1;have hqt:=ih (λ r hr=>hp r (by simp [gY,hr]))
    (iu.mp hd).2
   have hpt:=hp ⟨_,_,p⟩ (by simp [gY]);have hdisj:p.support.Disjoint q.walk.support:=by rw [ct];intro x hx Yt;obtain ⟨r,hr,Yu⟩:=q.mem_support_iff x |>.mp Yt;exact Sm r hr hx Yu
   apply Walk.IsPath.mk';simpa only [walk,Walk.support_append,Walk.support_cons,mC]
    using (List.nodup_append').mpr ⟨hpt.support_nodup,hqt.support_nodup,hdisj⟩
lemma HX (q:iT G u v):q.gY.length<=q.walk.length+1:=by
 induction q with
 | single p=>simp [gY,walk]
 | cons p h q ih=>simp only [gY,kT,walk,Walk.length_append,Walk.length_cons];omega
lemma edgeSet_eq (q:iT G u v):q.walk.edgeSet=q.Bc∪q.r7:=by
 induction q with
 | single p=>simp [walk,Bc,r7,gY]
 | cons p h q ih=>simp only [walk,Walk.edgeSet_append,Walk.edgeSet_cons,ih,Bc,r7,gY];ext e;simp only [b8,dB,eI,av,dd,exists_prop,or_and_right,exists_or,exists_eq_left];tauto
lemma MQ (q:iT G u v) (hc:G.Adj v u)
  (hp:∀p∈q.gY,p.walk.IsPath)
  (hd:q.gY.Pairwise (λ p r=>p.walk.support.Disjoint r.walk.support))
  (hn:3<=q.gY.length):(Walk.cons hc q.walk).IsCycle/\(Walk.cons hc q.walk).edgeSet={s(v,u)}∪q.Bc∪q.r7/\3<=(Walk.cons hc q.walk).length:=by
 have F9:=q.Ep hp hd;have WW:=q.HX;have he:s(v,u)∉q.walk.edges:=by intro he;have hh:=F9.length_eq_one_of_mem_edges (bx▸he);omega
 refine ⟨Path.cons_isCycle ⟨q.walk,F9⟩ hc he,?_,?_⟩
 ·rw [Walk.edgeSet_cons,q.edgeSet_eq];ext e;simp only [b8,eI,dB];tauto
 ·simp only [Walk.length_cons];omega
end iT
namespace t7
def Ai (p:t7 G):Set V:={p.start,p.finish}
end t7
namespace iT
variable {W:Type bY} {Q:SimpleGraph W}
def vD (s t:W->V) (q:∀z,G.Walk (s z) (t z)):{a b:W}->(p:Q.Walk a b)->(∀d∈p.darts,G.Adj (t d.fst) (s d.snd))->iT G (s a) (t b)
 | _,_, .nil,_=> .single (q _)
 | a,b, .cons (v:=c) h p,hr=> .cons (q a)
    (hr ⟨(a,c),h⟩ (by simp))
    (vD s t q p (by intro d hd;exact hr d (by simp [hd])))
lemma Cq (s t:W->V) (q:∀z,G.Walk (s z) (t z))
  {a b:W} (p:Q.Walk a b)
  (hr:∀d∈p.darts,G.Adj (t d.fst) (s d.snd)):(vD s t q p hr).gY=p.support.map (λ z=>(⟨s z,t z,q z⟩:t7 G)):=by
 induction p with
 | nil=>rfl
 | cons h p ih=>simp [vD,gY,ih]
lemma KS (s t:W->V) (q:∀z,G.Walk (s z) (t z))
  {a b:W} (p:Q.Walk a b)
  (hr:∀d∈p.darts,G.Adj (t d.fst) (s d.snd)):(vD s t q p hr).Bc={e | ∃d∈p.darts,e=s(t d.fst,s d.snd)}:=by
 induction p with
 | nil=>ext e;simp [vD,Bc]
 | cons h p ih=>ext e;simp [vD,Bc,ih,]
lemma Er (s t:W->V) (q:∀z,G.Walk (s z) (t z))
  {a b:W} (p:Q.Walk a b)
  (hr:∀d∈p.darts,G.Adj (t d.fst) (s d.snd)):(vD s t q p hr).r7=⋃ z∈p.support,(q z).edgeSet:=by
 rw [r7,Cq];ext e;simp only [av,bV,exists_prop];constructor
 ·rintro ⟨r,⟨z,hz,rfl⟩,he⟩;exact ⟨z,hz,he⟩
 ·rintro ⟨z,hz,he⟩;exact ⟨⟨s z,t z,q z⟩,⟨z,hz,rfl⟩,he⟩
end iT
lemma Et {W:Type cy} {Q:SimpleGraph W}
  (s t:W->V) (q:∀z,G.Walk (s z) (t z))
  {a:W} (p:Q.Walk a a) (hp:p.IsCycle)
  (hr:∀d∈p.dropLast.darts,G.Adj (t d.fst) (s d.snd))
  (hc:G.Adj (t p.penultimate) (s a))
  (hq:∀z∈p.dropLast.support,(q z).IsPath)
  (zN:∀z∈p.dropLast.support,∀w∈p.dropLast.support,z≠w->(q z).support.Disjoint (q w).support):
  ∃c:G.Walk (t p.penultimate) (t p.penultimate),c.IsCycle/\c.edgeSet={s(t p.penultimate,s a)}∪{e | ∃d∈p.dropLast.darts,e=s(t d.fst,s d.snd)}∪(⋃ z∈p.dropLast.support,(q z).edgeSet):=by
 let chain:=iT.vD s t q p.dropLast hr;have hv:chain.gY=p.dropLast.support.map (λ z=>(⟨s z,t z,q z⟩:t7 G)):=iT.Cq s t q p.dropLast hr;have L6:∀v∈chain.gY,v.walk.IsPath:=by intro v Vk;rw [hv] at Vk;obtain ⟨z,hz,rfl⟩:=bV.mp Vk;exact hq z hz
 have Jf:chain.gY.Pairwise (λ v w=>v.walk.support.Disjoint w.walk.support):=by
  rw [hv,m7];apply (oV).mpr;intro i j hi hj hij;have hne:p.dropLast.support[i]≠p.dropLast.support[j] :=by intro he;have Sy:=hp.isPath_dropLast.support_nodup.getElem_inj_iff.mp he;omega
  exact zN _ (List.getElem_mem _) _ (List.getElem_mem _) hne
 have hn:3<=chain.gY.length:=by rw [hv,List.length_map,Walk.length_support,Walk.length_dropLast];have:=hp.three_le_length;omega
 obtain ⟨LG,LQ,_⟩:=chain.MQ hc L6 Jf hn;refine ⟨Walk.cons hc chain.walk,LG,?_⟩;rw [LQ,iT.KS,iT.Er]
section
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma x7 {W:Type cz} {Q:SimpleGraph W}
  (projMap:V->W) (S:Set (Sym2 V)) (Kw:S⊆G.edgeSet)
  (hrep:∀e∈Q.edgeSet,∃f∈S,Sym2.map projMap f=e):∃R:Q.Dart->G.Dart,∀d,(R d).edge∈S/\projMap (R d).fst=d.fst/\projMap (R d).snd=d.snd:=by
 have hex:∀d:Q.Dart,∃r:G.Dart,r.edge∈S/\projMap r.fst=d.fst/\projMap r.snd=d.snd:=by
  intro d;obtain ⟨f,hf,HG⟩:=hrep d.edge d.edge_mem;induction f using bJ with
  | _ x y=>
    have hadj:G.Adj x y:=Kw hf;change s(projMap x,projMap y)=s(d.fst,d.snd) at HG;rcases jI.mp HG with he | he
    ·exact ⟨⟨(x,y),hadj⟩,hf,he.1,he.2⟩
    ·refine ⟨⟨(y,x),hadj.symm⟩,?_,he.2,he.1⟩;change s(y,x)∈S;simpa only [bx] using hf
 exact Classical.axiomOfChoice hex
def Dq {A:Type cP} {W:Type cL} (L:List A) (f:A->W) (g:A->V)
  (BE:V) (z:W):V:=if h:∃d∈L,f d=z then g h.choose else BE
lemma GW {A:Type c9} {W:Type dW} (L:List A) (f:A->W) (g:A->V)
  (BE:V) (hn:(L.map f).Nodup) {d:A} (hd:d∈L):Dq L f g BE (f d)=g d:=by
 have hex:∃e∈L,f e=f d:=⟨d,hd,rfl⟩;rw [Dq,dif_pos hex];congr 1;exact List.inj_on_of_nodup_map hn hex.choose_spec.1 hd hex.choose_spec.2
lemma Fp {W:Type eo} {Q:SimpleGraph W}
  (projMap:V->W) (R:Q.Dart->G.Dart)
  (Ds:∀d,projMap (R d).fst=d.fst/\projMap (R d).snd=d.snd)
  {a:W} (p:Q.Walk a a) (hp:p.IsCycle) (BE:V):∃s t:W->V,(∀d∈p.darts,t d.fst=(R d).fst/\s d.snd=(R d).snd)/\(∀z∈p.dropLast.support,projMap (s z)=z/\projMap (t z)=z):=by
 let s:=Dq p.darts (λ d=>d.snd) (λ d=>(R d).snd) BE;let t:=Dq p.darts (λ d=>d.fst) (λ d=>(R d).fst) BE;have Yv:(p.darts.map (λ d=>d.fst)).Nodup:=by rw [Walk.map_fst_darts];exact hp.nodup_dropLast_support
 have hns:(p.darts.map (λ d=>d.snd)).Nodup:=by rw [Walk.map_snd_darts];exact hp.support_nodup
 have ht:∀d∈p.darts,t d.fst=(R d).fst:=λ d hd=>GW _ _ _ _ Yv hd
 have hs:∀d∈p.darts,s d.snd=(R d).snd:=λ d hd=>GW _ _ _ _ hns hd
 refine ⟨s,t,λ d hd=>⟨ht d hd,hs d hd⟩,?_⟩;intro z hz;have L7:z∈p.support.dropLast:=by rw [<-p.support_dropLast hp.not_nil];exact hz
 have Sq:z∈p.support.tail:=p.tail_support_perm_dropLast_support.mem_iff.mpr L7;have Yw:z∈p.darts.map (λ d=>d.fst):=by rwa [Walk.map_fst_darts]
 have SG:z∈p.darts.map (λ d=>d.snd):=by rwa [Walk.map_snd_darts]
 obtain ⟨d,hd,he⟩:=bV.mp Yw;obtain ⟨e,he',Yx⟩:=bV.mp SG;exact ⟨by rw [<-Yx,hs e he'];exact (Ds e).2,by rw [<-he,ht d hd];exact (Ds d).1⟩
lemma KT {W:Type d7} {Q:SimpleGraph W} {a b:W}
  (p:Q.Walk a b) (hp:¬p.Nil):(⟨(p.penultimate,b),p.adj_penultimate hp⟩:Q.Dart)∈p.darts:=by
 have he:=aF Walk.darts (p.concat_dropLast (p.adj_penultimate hp));rw [Walk.darts_concat] at he;rw [<-he];simp
lemma GB {W:Type d8} {Q:SimpleGraph W} {a b:W}
  (p:Q.Walk a b) (hp:¬p.Nil):p.darts=p.dropLast.darts ++ [⟨(p.penultimate,b),p.adj_penultimate hp⟩] :=by
 have he:=aF Walk.darts (p.concat_dropLast (p.adj_penultimate hp));simpa only [Walk.darts_concat,List.concat_eq_append] using he.symm
lemma zu {W:Type d9} {Q:SimpleGraph W}
  (R:Q.Dart->G.Dart) (s t:W->V)
  {a:W} (p:Q.Walk a a) (hp:p.IsCycle)
  (tM:∀d∈p.darts,t d.fst=(R d).fst/\s d.snd=(R d).snd)
  (q:∀z,G.Walk (s z) (t z))
  (hq:∀z∈p.dropLast.support,(q z).IsPath)
  (zN:∀z∈p.dropLast.support,∀w∈p.dropLast.support,z≠w->(q z).support.Disjoint (q w).support):
  ∃(v:V) (c:G.Walk v v),c.IsCycle/\c.edgeSet={e | ∃d∈p.darts,e=(R d).edge}∪(⋃ z∈p.dropLast.support,(q z).edgeSet):=by
 let last:Q.Dart:=⟨(p.penultimate,a),p.adj_penultimate hp.not_nil⟩;have hlast:last∈p.darts:=KT p hp.not_nil;have hsub:p.dropLast.darts⊆p.darts:=by rw [Walk.darts_dropLast];exact List.dropLast_subset _
 have DT:∀d∈p.darts,s(t d.fst,s d.snd)=(R d).edge:=by intro d hd;rw [(tM d hd).1,(tM d hd).2];rfl
 have hadj:∀d∈p.darts,G.Adj (t d.fst) (s d.snd):=by intro d hd;rw [(tM d hd).1,(tM d hd).2];exact (R d).adj
 obtain ⟨c,hc,he⟩:=Et s t q p hp
  (λ d hd=>hadj d (hsub hd)) (hadj last hlast) hq zN
 refine ⟨_,c,hc,?_⟩;rw [he];have SH:{s(t p.penultimate,s a)}∪{e | ∃d∈p.dropLast.darts,e=s(t d.fst,s d.snd)}={e | ∃d∈p.darts,e=(R d).edge}:=by
  ext e;simp only [b8,dB,fo];constructor
  ·rintro (rfl | ⟨d,hd,rfl⟩)
   ·exact ⟨last,hlast,DT last hlast⟩
   ·exact ⟨d,hsub hd,DT d (hsub hd)⟩
  ·rintro ⟨d,hd,rfl⟩
   rw [GB p hp.not_nil] at hd;simp only [fQ,jM] at hd;rcases hd with hd | rfl
   ·exact Or.inr ⟨d,hd,(DT d (hsub hd)).symm⟩
   ·exact Or.inl (DT last hlast).symm
 rw [SH]
def Aj {W:Type gu} (S:Set W) (s t:W->V):Set V:={v | ∃z∈S,v=s z\/v=t z}
def nG {W:Type gX} (s t:W->V) (q:∀z,G.Walk (s z) (t z))
 (z:W):Set V:={x | x∈(q z).support/\x≠s z/\x≠t z}
lemma zv {W:Type iN}
  (S:Set W) (projMap:V->W) (s t:W->V)
  (q:∀z,G.Walk (s z) (t z))
  (Qd:∀z∈S,projMap (s z)=z/\projMap (t z)=z)
  (xM:∀z∈S,Disjoint (nG s t q z) (Aj S s t))
  (Fr:∀z∈S,∀w∈S,z≠w->Disjoint (nG s t q z) (nG s t q w)):
  ∀z∈S,∀w∈S,z≠w->(q z).support.Disjoint (q w).support:=by
 intro z hz w hw hzw;rw [ct];intro x hx hy;by_cases Lb:x=s z\/x=t z
 ·have Yy:x∈Aj S s t:=⟨z,hz,Lb⟩
  by_cases Dt:x=s w\/x=t w
  ·have OM:projMap x=z:=by rcases Lb with rfl | rfl<;>simp_all
   have ON:projMap x=w:=by rcases Dt with rfl | rfl<;>simp_all
   exact hzw (OM.symm.trans ON)
  ·exact aI.mp (xM w hw)
    ⟨hy,λ he=>Dt (Or.inl he),λ he=>Dt (Or.inr he)⟩ Yy
 ·have Vl:x∈nG s t q z:=⟨hx,λ he=>Lb (Or.inl he),λ he=>Lb (Or.inr he)⟩
  by_cases Dt:x=s w\/x=t w
  ·exact aI.mp (xM z hz) Vl ⟨w,hw,Dt⟩
  ·exact aI.mp (Fr z hz w hw hzw) Vl
    ⟨hy,λ he=>Dt (Or.inl he),λ he=>Dt (Or.inr he)⟩
lemma r4 {W:Type iO} {Q:SimpleGraph W}
  (R:Q.Dart->G.Dart) (s t:W->V)
  {a:W} (p:Q.Walk a a) (hp:p.IsCycle)
  (tM:∀d∈p.darts,t d.fst=(R d).fst/\s d.snd=(R d).snd):Aj {z | z∈p.dropLast.support} s t={v | ∃d∈p.darts,v=(R d).fst\/v=(R d).snd}:=by
 have Vm:p.darts.map (λ d=>d.fst)=p.dropLast.support:=by rw [Walk.map_fst_darts,p.support_dropLast hp.not_nil]
 have Vn:∀z,z∈p.darts.map (λ d=>d.snd)↔z∈p.dropLast.support:=by intro z;rw [Walk.map_snd_darts,p.support_dropLast hp.not_nil];exact p.tail_support_perm_dropLast_support.mem_iff
 ext v;constructor
 ·rintro ⟨z,hz,hv | hv⟩
  ·obtain ⟨d,hd,Yz⟩:=bV.mp ((Vn z).mpr hz);exact ⟨d,hd,Or.inr (hv.trans (by rw [<-Yz];exact (tM d hd).2))⟩
  ·have L7:z∈p.darts.map (λ d=>d.fst):=by rwa [Vm]
   obtain ⟨d,hd,YA⟩:=bV.mp L7;exact ⟨d,hd,Or.inl (hv.trans (by rw [<-YA];exact (tM d hd).1))⟩
 ·rintro ⟨d,hd,hv | hv⟩
  ·refine ⟨d.fst,?_,Or.inr (hv.trans (tM d hd).1.symm)⟩;rw [<-Vm];exact bV.mpr ⟨d,hd,rfl⟩
  ·exact ⟨d.snd,(Vn _).mp (bV.mpr ⟨d,hd,rfl⟩),Or.inl (hv.trans (tM d hd).2.symm)⟩
end
end af.Batch
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
def zz {I:Type bX} {V:Type bY} [Fintype I] (x y:I->V) (v:V):ℕ:=(univ.filter λ i=>x i=v\/y i=v).card
lemma Cr {V:Type cy} {I:Type cz} {B:Type cP} [Fintype V] [Fintype I]
  [DecidableEq V] (G:SimpleGraph V) [DecidableRel G.Adj]
  (E:B->Set (Sym2 V))
  (hE:Pairwise λ b c=>Disjoint (E b) (E c))
  (jz:I->B) (x y:I->V)
  (Q6:∀i j v,jz i=jz j->(x i=v\/y i=v)->(x j=v\/y j=v)->i=j)
  (N8:∀i v,x i=v\/y i=v->∃w,G.Adj v w/\s(v,w)∈E (jz i)) (v:V):
  zz x y v<=G.degree v:=by
 classical
 let S:={i:I // x i=v\/y i=v};have hs (i:S):=N8 i.val v i.property;let f:S->G.neighborFinset v:=λ i=>⟨(hs i).choose,by simpa using (hs i).choose_spec.1⟩
 have hf:Function.Injective f:=by
  intro i j hij;have he:(hs i).choose=(hs j).choose:=aF Subtype.val hij;apply aZ;by_cases ho:jz i.val=jz j.val
  ·exact Q6 i.val j.val v ho i.property j.property
  ·exact False.elim (aI.mp (hE ho)
    (hs i).choose_spec.2 (by rw [he];exact (hs j).choose_spec.2))
 have hc:=Fintype.card_le_of_injective f hf;have hn:Fintype.card (G.neighborFinset v)=G.degree v:=by rw [eG,oR]
 rw [hn] at hc;have YB:Fintype.card S=zz x y v:=by simp only [S,mg,zz];congr 1;ext i;simp
 rw [YB] at hc;exact hc
lemma AN {V:Type cL} {G:SimpleGraph V} {a b:V}
  (p:G.Walk a b) (hp:¬p.Nil):∃w,G.Adj a w/\s(a,w)∈p.edgeSet:=by
 exact ⟨p.snd,p.adj_snd hp,p.mk_start_snd_mem_edges hp⟩
lemma Ak {V:Type c9} {G:SimpleGraph V} {a b:V}
  (p:G.Walk a b) (hp:¬p.Nil):∃w,G.Adj b w/\s(b,w)∈p.edgeSet:=by
 refine ⟨p.penultimate,(p.adj_penultimate hp).symm,?_⟩;change s(b,p.penultimate)∈p.edges;simpa only [bx] using p.mk_penultimate_end_mem_edges hp
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma AO {V I:Type} [Fintype I]
  (x y:I->V) (s:I->Prop) (v:V):b7 univ (λ i:{i // s i}=>x i) (λ i=>y i) v<=b7 univ x y v:=by
 classical
 simp only [b7];apply gG (λ i:{i // s i}=>i.val)
 ·intro i hi;simpa using hi
 ·intro i _ j _ h;exact aZ h
lemma x8:∃dN:ℝ,1<dN/\∀D≥dN,∀(V R I T:Type) [Fintype V] [Fintype R] [Fintype I],∀(G:SimpleGraph V) (P:R->SimpleGraph V) (U:R->Finset V),(∀r,P r<=G)->Pairwise (λ r s=>Disjoint (P r).edgeSet (P s).edgeSet)->Pairwise (λ r s=>Disjoint (U r) (U s))->(∀r,b9 (P r) (U r) (D^(9/10:ℝ)/4))->(∀r,D^(9/10:ℝ)<=((U r).card:ℝ)/\((U r).card:ℝ)<=D^(51/50:ℝ))->∀(jz:I->R) (x y:I->V),(∀i,x i∈U (jz i)/\y i∈U (jz i)/\x i≠y i)->∀(i4:I->T) (Z:I->Finset V),(∀v,(b7 univ x y v:ℝ)<=D^(1/100:ℝ))->(∀i,((univ.filter (λ j=>i4 j=i4 i)).card:ℝ)<=D^(3/10:ℝ))->(∀i,((Z i).card:ℝ)<=2*D^(3/10:ℝ))->∃q:∀i,G.Walk (x i) (y i),(∀i,(q i).IsPath/\(∀v∈(q i).support,v∈U (jz i))/\(q i).edgeSet⊆(P (jz i)).edgeSet/\Disjoint (cE (q i)) (Z i))/\
    Pairwise (λ i j=>Disjoint (q i).edgeSet (q j).edgeSet)/\(∀i j,i≠j->i4 i=i4 j->Disjoint (cE (q i)) (cE (q j))):=by
 classical
 obtain ⟨dN,ko,LC⟩:=Cp;refine ⟨dN,ko,?_⟩;intro D hD V R I T _ _ _ G P U oe vm Cs he hr jz x y hxy i4 Z hl ht hZ;let J:=λ r=>{i // jz i=r}
 have hex:∀r,∃q:∀i:J r,G.Walk (x i) (y i),(∀i,(q i).IsPath/\(∀v∈(q i).support,v∈U r)/\(q i).edgeSet⊆(P r).edgeSet/\Disjoint (cE (q i)) (Z i))/\
   Pairwise (λ i j=>Disjoint (q i).edgeSet (q j).edgeSet)/\(∀i j:J r,i≠j->i4 i=i4 j->Disjoint (cE (q i)) (cE (q j))):=by
  intro r;obtain ⟨q,hq,hd,hi⟩:=LC D hD V G (P r) (oe r) (U r) (he r) (hr r).1 (hr r).2
   (J r) T (λ i=>x i) (λ i=>y i)
   (λ i=>by simpa only [<-i.property] using (hxy i).1)
   (λ i=>by simpa only [<-i.property] using (hxy i).2.1)
   (λ i=>(hxy i).2.2) (λ i=>i4 i) (λ i=>Z i)
   (λ v=>(show (b7 univ (λ i:J r=>x i) (λ i=>y i) v:ℝ)<=b7 univ x y v by exact_mod_cast AO x y (λ i=>jz i=r) v).trans (hl v))
   (λ i=>dY (by
    apply cq.mpr;apply gG (λ i:J r=>i.val)
    ·intro j hj;simpa using hj
    ·intro j _ l _ h;exact aZ h) (ht i)) (λ i=>hZ i)
  exact ⟨q,λ i=>⟨(hq i).1,(hq i).2.2⟩,hd,hi⟩
 choose q hq hd hi using hex;let f:∀i,G.Walk (x i) (y i):=λ i=>q (jz i) ⟨i,rfl⟩
 have hf (i:I) (r:R) (h:jz i=r):f i=q r ⟨i,h⟩:=by subst r;rfl
 refine ⟨f,λ i=>hq _ _,?_,?_⟩
 ·intro i j hij
  by_cases hh:jz i=jz j
  ·have h:=hd (jz i) (show (⟨i,rfl⟩:J (jz i))≠⟨j,hh.symm⟩ from
    λ h=>hij (aF Subtype.val h))
   rw [hf j (jz i) hh.symm];exact h
  ·exact (vm hh).mono (hq _ _).2.2.1 (hq _ _).2.2.1
 ·intro i j hij C6
  by_cases hh:jz i=jz j
  ·have h:=hi (jz i) ⟨i,rfl⟩ ⟨j,hh.symm⟩
    (λ h=>hij (aF Subtype.val h)) C6
   rw [hf j (jz i) hh.symm];exact h
  ·apply (Cs hh).mono
   ·intro v hv;exact (hq (jz i) ⟨i,rfl⟩).2.1 v (bw.mp (aS.mp hv).1)
   ·intro v hv;exact (hq (jz j) ⟨j,rfl⟩).2.1 v (bw.mp (aS.mp hv).1)
structure pL {V:Type} (G:SimpleGraph V) where
 W:Type
 Nk:Fintype W
 Q:SimpleGraph W
 base:W
 cycle:Q.Walk base base
 isCycle:cycle.IsCycle
 rep:Q.Dart->G.Dart
 start:W->V
 finish:W->V
 project:V->W
 Jm:∀d∈cycle.darts,finish d.fst=(rep d).fst/\start d.snd=(rep d).snd
 xl:∀z∈cycle.dropLast.support,project (start z)=z/\project (finish z)=z
 Nl:∀z,z∉cycle.dropLast.support->start z=finish z
instance pL.Tx {V:Type} {G:SimpleGraph V} (c:pL G):Fintype c.W:=c.Nk
namespace pL
variable {V:Type} {G:SimpleGraph V} (c:pL G)
def edges:Set (Sym2 V):={e | ∃d∈c.cycle.darts,e=(c.rep d).edge}
def vertices:Finset V:=c.cycle.darts.toFinset.biUnion λ d=>{(c.rep d).fst,(c.rep d).snd}
abbrev Switch:={z:c.W // z∈c.cycle.dropLast.support/\c.start z≠c.finish z}
instance:Fintype c.Switch:=inferInstanceAs (Fintype {_z:c.W // _})
lemma edges_subset:c.edges⊆G.edgeSet:=by rintro e ⟨d,hd,rfl⟩;exact (c.rep d).edge_mem
lemma Pp (z:c.W) (hz:z∈c.cycle.dropLast.support):∃d∈c.cycle.darts,d.fst=z:=by
 have h:z∈c.cycle.darts.map (λ d=>d.fst):=by rw [Walk.map_fst_darts,<-c.cycle.support_dropLast c.isCycle.not_nil];exact hz
 exact bV.mp h
lemma Pq (z:c.W) (hz:z∈c.cycle.dropLast.support):∃d∈c.cycle.darts,d.snd=z:=by
 have h:z∈c.cycle.darts.map (λ d=>d.snd):=by rw [Walk.map_snd_darts];apply c.cycle.tail_support_perm_dropLast_support.mem_iff.mpr;rw [<-c.cycle.support_dropLast c.isCycle.not_nil];exact hz
 exact bV.mp h
lemma GC (z:c.Switch) (v:V) (hv:c.start z=v\/c.finish z=v):∃w,G.Adj v w/\s(v,w)∈c.edges:=by
 rcases hv with rfl | rfl
 ·obtain ⟨d,hd,he⟩:=c.Pq z z.property.1
  have hh:=(c.Jm d hd).2;rw [he] at hh;refine ⟨(c.rep d).fst,?_,?_⟩
  ·rw [hh];exact (c.rep d).adj.symm
  ·refine ⟨d,hd,?_⟩;rw [hh];exact bx
 ·obtain ⟨d,hd,he⟩:=c.Pp z z.property.1
  have hh:=(c.Jm d hd).1;rw [he] at hh;refine ⟨(c.rep d).snd,?_,?_⟩
  ·rw [hh];exact (c.rep d).adj
  ·refine ⟨d,hd,?_⟩;rw [hh];rfl
lemma Jn (z w:c.Switch) (v:V)
  (hz:c.start z=v\/c.finish z=v) (hw:c.start w=v\/c.finish w=v):z=w:=by
 apply aZ;have hf:∀(z:c.Switch),c.start z=v\/c.finish z=v->c.project v=z:=by
  intro z hz;rcases hz with h | h
  ·rw [<-h];exact (c.xl z z.property.1).1
  ·rw [<-h];exact (c.xl z z.property.1).2
 exact (hf z hz).symm.trans (hf w hw)
lemma Ct:c.vertices.card<=2*c.cycle.dropLast.support.toFinset.card:=by
 have Il:c.vertices.card<=2*c.cycle.darts.toFinset.card:=by
  calc
   _<=∑d∈c.cycle.darts.toFinset,({(c.rep d).fst,(c.rep d).snd}:Finset V).card:=c5
   _<=∑d∈c.cycle.darts.toFinset,2:=aK (λ d _=>card_le_two)
   _=_:=by simp [bK]
 have hd:c.cycle.darts.toFinset.card<=c.cycle.dropLast.support.toFinset.card:=by
  calc
   _<=c.cycle.darts.length:=oG _
   _=c.cycle.dropLast.support.length:=by rw [Walk.length_darts,Walk.length_support,Walk.length_dropLast];have:=c.isCycle.three_le_length;omega
   _=c.cycle.dropLast.support.toFinset.card:=(eJ c.isCycle.isPath_dropLast.support_nodup).symm
 omega
lemma mem_vertices (v:V):v∈c.vertices↔∃d∈c.cycle.darts,v=(c.rep d).fst\/v=(c.rep d).snd:=by simp [vertices]
lemma complete [DecidableEq V]
  (Dv:∀z:c.Switch,G.Walk (c.start z) (c.finish z))
  (hs:∀z,(Dv z).IsPath)
  (ha:∀z,Disjoint (cE (Dv z)) c.vertices)
  (hd:Pairwise λ z w=>Disjoint (cE (Dv z)) (cE (Dv w))):∃(v:V) (p:G.Walk v v),p.IsCycle/\p.edgeSet=c.edges∪⋃ z,(Dv z).edgeSet:=by
 classical
 let gY:∀z,G.Walk (c.start z) (c.finish z):=λ z=>
  if h:z∈c.cycle.dropLast.support/\c.start z≠c.finish z then Dv ⟨z,h⟩
  else (Walk.nil:G.Walk (c.start z) (c.start z)).copy rfl (by
   by_cases hz:z∈c.cycle.dropLast.support
   ·exact not_not.mp (λ hn=>h ⟨hz,hn⟩)
   ·exact c.Nl z hz)
 have hv (z:c.Switch):gY z=Dv z:=by simp only [gY,dif_pos z.property]
 have N9 (z:c.W) (hz:¬(z∈c.cycle.dropLast.support/\c.start z≠c.finish z)):(gY z).Nil:=by simp only [gY,dif_neg hz,Walk.nil_copy,Walk.nil_nil]
 have F9:∀z,(gY z).IsPath:=by
  intro z;by_cases hz:z∈c.cycle.dropLast.support/\c.start z≠c.finish z
  ·simpa only [gY,dif_pos hz] using hs ⟨z,hz⟩
  ·simp [gY,dif_neg hz]
 have Fr (z:c.W):nG c.start c.finish gY z=(cE (gY z):Set V):=by ext v;simp [nG,cE]
 have Q7:∀z∈c.cycle.dropLast.support,Disjoint
   (nG c.start c.finish gY z) {v | ∃d∈c.cycle.darts,v=(c.rep d).fst\/v=(c.rep d).snd}:=by
  intro z hz;rw [Fr];have he:{v | ∃d∈c.cycle.darts,v=(c.rep d).fst\/v=(c.rep d).snd}=(c.vertices:Set V):=by ext v;exact (c.mem_vertices v).symm
  rw [he,m4];by_cases hne:c.start z≠c.finish z
  ·rw [hv ⟨z,hz,hne⟩];exact ha _
  ·have hn:=N9 z (by tauto);simp [aL,cE,Walk.nil_iff_support_eq.mp hn]
 have Ua:Pairwise λ z w:{z // z∈c.cycle.dropLast.support}=>
   Disjoint (nG c.start c.finish gY z) (nG c.start c.finish gY w):=by
  intro z w hzw;rw [Fr,Fr,m4];by_cases hz:c.start z≠c.finish z
  ·by_cases hw:c.start w≠c.finish w
   ·rw [hv ⟨z,z.property,hz⟩,hv ⟨w,w.property,hw⟩];exact hd (λ h=>hzw (aZ (aF (λ t:c.Switch=>(t:c.W)) h)))
   ·have hn:=N9 w (by tauto);simp [aL,cE,Walk.nil_iff_support_eq.mp hn];tauto
  ·have hn:=N9 z (by tauto);simp [aL,cE,Walk.nil_iff_support_eq.mp hn]
 obtain ⟨v,p,hp,N8⟩:=zu c.rep c.start c.finish c.cycle c.isCycle c.Jm gY
  (λ z _=>F9 z) (zv {z | z∈c.cycle.dropLast.support}
   c.project c.start c.finish gY c.xl
   (by intro z hz;rw [r4 c.rep c.start c.finish c.cycle c.isCycle c.Jm];exact Q7 z hz)
   (λ z hz w hw hzw=>Ua (show (⟨z,hz⟩:{z // z∈c.cycle.dropLast.support})≠⟨w,hw⟩ from
    λ h=>hzw (aF Subtype.val h))))
 refine ⟨v,p,hp,N8.trans ?_⟩;congr 1;ext e;simp only [av];constructor
 ·rintro ⟨z,hz,he⟩
  by_cases hne:c.start z≠c.finish z
  ·exact ⟨⟨z,hz,hne⟩,by rwa [hv ⟨z,hz,hne⟩] at he⟩
  ·have hn:=N9 z (by tauto);have hh:=he;simp [Walk.edgeSet,Walk.edges_eq_nil.mpr hn] at hh
 ·rintro ⟨z,he⟩;exact ⟨z,z.property.1,by rwa [hv]⟩
end pL
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
structure fY {V:Type} (G:SimpleGraph V) where
 oD:Type
 xB:Fintype oD
 x:oD ->V
 y:oD ->V
 ne:∀i,x i≠y i
 edges:Set (Sym2 V)
 subset:edges⊆G.edgeSet
 vertices:Finset V
 Dw:∀i v,x i=v\/y i=v->∃w,s(v,w)∈edges
 unique:∀i j v,(x i=v\/y i=v)->(x j=v\/y j=v)->i=j
 complete:∀q:∀i,G.Walk (x i) (y i),(∀i,(q i).IsPath)->(∀i,Disjoint (cE (q i)) vertices)->Pairwise (λ i j=>Disjoint (cE (q i)) (cE (q j)))->e8 G (edges∪⋃ i,(q i).edgeSet)
instance fY.Qe {V:Type} {G:SimpleGraph V} (c:fY G):Fintype c.oD:=c.xB
namespace fY
variable {V:Type} {G:SimpleGraph V}
def zF (c:pL G):fY G where
 oD:=c.Switch
 xB:=inferInstance
 x:=λ i=>c.start i
 y:=λ i=>c.finish i
 ne:=λ i=>i.property.2
 edges:=c.edges
 subset:=c.edges_subset
 vertices:=c.vertices
 Dw:=λ i v h=>by obtain ⟨w,_,he⟩:=c.GC i v h;exact ⟨w,he⟩
 unique:=c.Jn
 complete:=by intro q hs ha hd;obtain ⟨v,p,hp,he⟩:=c.complete q hs ha hd;exact Or.inl ⟨v,p,hp,he.symm⟩
def L8 (e:Sym2 V) (he:e∈G.edgeSet):fY G where
 oD:=Empty
 xB:=inferInstance
 x:=Empty.elim
 y:=Empty.elim
 ne:=λ i=>i.elim
 edges:={e}
 subset:=m5.mpr he
 vertices:=∅
 Dw:=λ i=>i.elim
 unique:=λ i=>i.elim
 complete:=by intro q _ _ _;exact Or.inr ⟨e,he,by simp⟩
def qX {x y:V} (p:G.Walk x y) (hp:p.IsPath) (hl:2<=p.length):fY G where
 oD:=Unit
 xB:=inferInstance
 x:=λ _=>y
 y:=λ _=>x
 ne:=λ _ he=>by have hn:p.Nil:=hp.nil_iff_eq.mpr he.symm;have:=Walk.length_eq_zero_iff.mpr hn;omega
 edges:=p.edgeSet
 subset:=p.edges_subset_edgeSet
 vertices:=p.support.toFinset
 Dw:=by
  intro i v hv;have hn:¬p.Nil:=λ h=>by have:=Walk.length_eq_zero_iff.mpr h;omega
  rcases hv with rfl | rfl
  ·obtain ⟨w,_,he⟩:=Ak p hn;exact ⟨w,he⟩
  ·obtain ⟨w,_,he⟩:=AN p hn;exact ⟨w,he⟩
 unique:=λ _ _ _ _ _=>Subsingleton.elim _ _
 complete:=by
  intro q hs ha hd;obtain ⟨hc,he⟩:=Fo p (q ()) hp (hs ()) hl (by
   intro v hv Su YC Li;exact aL.mp (ha ())
    (by simp [cE,hv,Su,YC]) (bw.mpr Li))
  refine Or.inl ⟨x,p.append (q ()),hc,?_⟩;have hh:∀i:Unit,q i=q ():=λ i=>by cases i;rfl
  simp_rw [hh,Set.iUnion_const];exact he.symm
end fY
lemma zA:∃dN:ℝ,1<dN/\∀D≥dN,∀(V R B:Type) [Fintype V] [Fintype R] [Fintype B],∀(G F:SimpleGraph V) (P:R->SimpleGraph V) (U:R->Finset V),F<=G->(∀r,P r<=G)->Pairwise (λ r s=>Disjoint (P r).edgeSet (P s).edgeSet)->Pairwise (λ r s=>Disjoint (U r) (U s))->(∀r,Disjoint F.edgeSet (P r).edgeSet)->(∀r,b9 (P r) (U r) (D^(9/10:ℝ)/4))->(∀r,D^(9/10:ℝ)<=((U r).card:ℝ)/\((U r).card:ℝ)<=D^(51/50:ℝ))->∀(b:B->fY G),(∀j,(b j).edges⊆F.edgeSet)->Pairwise (λ j k=>Disjoint (b j).edges (b k).edges)->∀jz:(j:B)->(b j).oD ->R,(∀j i,(b j).x i∈U (jz j i)/\(b j).y i∈U (jz j i))->(∀j i,(F.degree ((b j).x i):ℝ)<=D^(1/100:ℝ)/\(F.degree ((b j).y i):ℝ)<=D^(1/100:ℝ))->
   (∀j,(Fintype.card (b j).oD:ℝ)<=D^(3/10:ℝ))->(∀j,((b j).vertices.card:ℝ)<=2*D^(3/10:ℝ))->∃(parts:B->Set (Sym2 V)) (used:Set (Sym2 V)),(∀j,e8 G (parts j))/\Pairwise (λ j k=>Disjoint (parts j) (parts k))/\used⊆⋃ r,(P r).edgeSet/\Disjoint F.edgeSet used/\(⋃ j,parts j)=(⋃ j,(b j).edges)∪used:=by
 classical
 obtain ⟨dN,ko,hr⟩:=x8;refine ⟨dN,ko,?_⟩;intro D hD V R B _ _ _ G F P U GX oe vm Cs SI he u6 b hsub hdis jz qL hdeg hnum OO;let I:=Σ j,(b j).oD;let x:I->V:=λ i=>(b i.1).x i.2
 let y:I->V:=λ i=>(b i.1).y i.2
 have hl (v:V):(b7 univ x y v:ℝ)<=D^(1/100:ℝ):=by
  have lG:b7 univ x y v<=F.degree v:=by
   have hh:=Cr F (λ j=>(b j).edges) hdis
    Sigma.fst x y (by
     rintro ⟨j,i⟩ ⟨k,l⟩ v h h₁ h₂;dsimp only at h;subst k;congr 1;exact (b j).unique i l v h₁ h₂) (by
     rintro ⟨j,i⟩ v h;obtain ⟨w,hw⟩:=(b j).Dw i v h;exact ⟨w,hsub j hw,hw⟩) v
   simpa [zz,b7] using hh
  by_cases hz:b7 univ x y v=0
  ·rw [hz,g3];exact fG (by linarith) _
  ·have hp:0<(univ.filter λ i=>x i=v\/y i=v).card:=by
    change 0<b7 univ x y v;omega
   obtain ⟨⟨j,i⟩,hi⟩:=cT.mp hp;have hv:(b j).x i=v\/(b j).y i=v:=(aD.mp hi).2;have hh:(F.degree v:ℝ)<=D^(1/100:ℝ):=by
    rcases hv with rfl | rfl
    ·exact (hdeg j i).1
    ·exact (hdeg j i).2
   exact (cq.mpr lG).trans hh
 have C6 (i:I):((univ.filter λ j:I=>j.1=i.1).card:ℝ)<=D^(3/10:ℝ):=by
  have hc:(univ.filter λ j:I=>j.1=i.1).card=Fintype.card (b i.1).oD:=by
   rw [cV,ck,Fintype.sum_sigma];calc
    _=∑j:B,if j=i.1 then Fintype.card (b j).oD else 0:=by apply cZ rfl;intro j _;by_cases hh:j=i.1<;>simp [hh]
    _=_:=by simp
  rw [hc];exact hnum i.1
 obtain ⟨q,hq,LW,R4⟩:=hr D hD V R I B G P U oe vm Cs he u6
  (λ i=>jz i.1 i.2) x y (λ i=>⟨(qL i.1 i.2).1,(qL i.1 i.2).2,(b i.1).ne i.2⟩)
  Sigma.fst (λ i=>(b i.1).vertices) hl C6 (λ i=>OO i.1)
 let used:=⋃ i,(q i).edgeSet;let parts:=λ j=>(b j).edges∪⋃ i,(q ⟨j,i⟩).edgeSet
 have hu:used⊆⋃ r,(P r).edgeSet:=by apply gJ;intro i;exact Set.subset_iUnion_of_subset (jz i.1 i.2) (hq i).2.2.1
 have Nm:Disjoint F.edgeSet used:=by refine oI.mpr (λ i=>?_);exact (SI _).mono_right (hq i).2.2.1
 have Vo:∀j,Disjoint (b j).edges used:=λ j=>Nm.mono_left (hsub j)
 refine ⟨parts,used,?_,?_,hu,Nm,?_⟩
 ·intro j
  exact (b j).complete (λ i=>q ⟨j,i⟩) (λ i=>(hq _).1) (λ i=>(hq _).2.2.2)
   (λ i l OE=>R4 _ _ (λ h=>OE (eq_of_heq (Sigma.mk.inj_iff.mp h).2)) rfl)
 ·intro j k zQ
  apply mw.mpr;constructor
  ·apply mz.mpr;constructor
   ·exact hdis zQ
   ·exact (Vo j).mono_right (gJ (λ i=>je (λ z:I=>(q z).edgeSet) ⟨k,i⟩))
  ·apply mz.mpr;constructor
   ·exact ((Vo k).mono_right (gJ (λ i=>je (λ z:I=>(q z).edgeSet) ⟨j,i⟩))).symm
   ·apply kP.mpr;intro i;apply oI.mpr;intro l;exact LW (λ h=>zQ (aF Sigma.fst h))
 ·ext e
  simp only [parts,used,av,b8];constructor
  ·rintro ⟨j,he|⟨i,hi⟩⟩
   ·exact Or.inl ⟨j,he⟩
   ·exact Or.inr ⟨⟨j,i⟩,hi⟩
  ·rintro (⟨j,he⟩|⟨⟨j,i⟩,he⟩)
   ·exact ⟨j,Or.inl he⟩
   ·exact ⟨j,Or.inr ⟨i,he⟩⟩
end
end af.Batch
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma q5 {V W:Type} [Fintype W]
  {G:SimpleGraph V} {Q:SimpleGraph W} (projMap:V->W)
  (S:Set (Sym2 V)) (Kw:S⊆G.edgeSet)
  (hrep:∀e∈Q.edgeSet,∃! f,f∈S/\Sym2.map projMap f=e)
  {a:W} (p:Q.Walk a a) (hp:p.IsCycle)
  (M:ℕ) (hM:p.dropLast.support.toFinset.card<=M):∃b:fY G,b.edges={e | e∈S/\Sym2.map projMap e∈p.edgeSet}/\card b.oD <=M/\b.vertices.card<=2*M/\∀i,projMap (b.x i)=projMap (b.y i):=by
 classical
 obtain ⟨R,hR⟩:=x7 projMap S Kw (λ e he=>(hrep e he).exists);let BE:=(R ⟨(a,p.snd),p.adj_snd hp.not_nil⟩).fst;obtain ⟨s,t,tM,Qd⟩:=Fp projMap R (λ d=>(hR d).2) p hp BE;have Ws (d:Q.Dart) (hd:d∈p.darts):d.fst∈p.dropLast.support:=by rw [p.support_dropLast hp.not_nil,<-Walk.map_fst_darts];exact bV.mpr ⟨d,hd,rfl⟩
 have Wt (d:Q.Dart) (hd:d∈p.darts):d.snd∈p.dropLast.support:=by rw [p.support_dropLast hp.not_nil];apply p.tail_support_perm_dropLast_support.mem_iff.mp;rw [<-Walk.map_snd_darts];exact bV.mpr ⟨d,hd,rfl⟩
 let c:pL G:={
  W:=W,Nk:=inferInstance,Q:= Q,base:=a,cycle:=p,isCycle:=hp,rep:=R,start:=λ z=>if z∈p.dropLast.support then s z else BE,finish:=λ z=>if z∈p.dropLast.support then t z else BE,project:=projMap,Jm:=by intro d hd;simpa only [ej (Ws d hd),ej (Wt d hd)] using tM d hd,xl:=by intro z hz;simpa only [ej hz] using Qd z hz,Nl:=by intro z hz;simp only [if_neg hz]
 }
 have HG (d:Q.Dart):Sym2.map projMap (R d).edge=d.edge:=by change s(projMap (R d).fst,projMap (R d).snd)=s(d.fst,d.snd);rw [(hR d).2.1,(hR d).2.2]
 have he:c.edges={e | e∈S/\Sym2.map projMap e∈p.edgeSet}:=by
  ext e;constructor
  ·rintro ⟨d,hd,rfl⟩;refine ⟨(hR d).1,?_⟩;rw [HG];change d.edge∈p.edges;rw [Walk.edges_eq_map_darts];exact bV.mpr ⟨d,hd,rfl⟩
  ·rintro ⟨hS,he⟩;change Sym2.map projMap e∈p.edges at he;rw [Walk.edges_eq_map_darts] at he;obtain ⟨d,hd,hde⟩:=bV.mp he;refine ⟨d,hd,?_⟩;exact (hrep d.edge d.edge_mem).unique ⟨hS,hde.symm⟩ ⟨(hR d).1,HG d⟩
 refine ⟨fY.zF c,he,?_,?_,?_⟩
 ·change card c.Switch<=M
  apply dY _ hM;apply gG (λ i:c.Switch=>i.val)
  ·intro z hz;exact bw.mpr z.property.1
  ·intro z _ w _ h;exact aZ h
 ·exact c.Ct.trans (Nat.mul_le_mul_left _ hM)
 ·intro i;change c.Switch at i;exact (c.xl i i.property.1).1.trans (c.xl i i.property.1).2.symm
lemma zB {V W:Type} [Fintype W]
  {G:SimpleGraph V} {Q:SimpleGraph W} (projMap:V->W)
  (S:Set (Sym2 V)) (Kw:S⊆G.edgeSet)
  (A:Finset W) (hA:∀⦃x y⦄,Q.Adj x y->x∈A/\y∈A)
  (hrep:∀e∈Q.edgeSet,∃! f,f∈S/\Sym2.map projMap f=e)
  (s:Set (Sym2 W)) (hs:e8 Q s):∃b:fY G,b.edges={e | e∈S/\Sym2.map projMap e∈s}/\card b.oD <=A.card/\b.vertices.card<=2*A.card/\∀i,projMap (b.x i)=projMap (b.y i):=by
 rcases hs with ⟨a,p,hp,rfl⟩ | ⟨e,he,rfl⟩
 ·exact q5 projMap S Kw hrep p hp A.card (by apply aU;intro z hz;rw [bw,p.support_dropLast hp.not_nil,<-Walk.map_fst_darts] at hz;obtain ⟨d,hd,rfl⟩:=bV.mp hz;exact (hA d.adj).1)
 ·obtain ⟨f,hf,Ub⟩:=hrep e he
  refine ⟨fY.L8 f (Kw hf.1),?_,by change card Empty<=_;simp,by simp [fY.L8],λ i=>i.elim⟩;ext g;change g=f↔g∈S/\Sym2.map projMap g∈({e}:Set (Sym2 W));constructor
  ·intro h;subst g;exact ⟨hf.1,hf.2⟩
  ·rintro ⟨hg,YD⟩;exact Ub g ⟨hg,YD⟩
lemma vQ {V W:Type} [Fintype W]
  {G:SimpleGraph V} {Q:SimpleGraph W} (projMap:V->W)
  (S:Set (Sym2 V)) (Kw:S⊆G.edgeSet)
  (A:Finset W) (hA:∀⦃x y⦄,Q.Adj x y->x∈A/\y∈A)
  (himage:Sym2.map projMap '' S= Q.edgeSet)
  (hrep:∀e∈Q.edgeSet,∃! f,f∈S/\Sym2.map projMap f=e)
  {k:ℕ} (hQ:e9 Q k):∃b:Fin k->fY G,Pairwise (λ i j=>Disjoint (b i).edges (b j).edges)/\(⋃ i,(b i).edges)=S/\(∀i,card (b i).oD <=A.card/\(b i).vertices.card<=2*A.card/\∀j,projMap ((b i).x j)=projMap ((b i).y j)):=by
 classical
 obtain ⟨parts,hp,hd,e7⟩:=hQ;choose b hb hnum hv Ds using λ i=>zB projMap S Kw A hA hrep (parts i) (hp i)
 refine ⟨b,?_,?_,λ i=>⟨hnum i,hv i,Ds i⟩⟩
 ·intro i j hij;rw [hb i,hb j];exact aI.mpr (λ _ hi hj=>aI.mp (hd hij) hi.2 hj.2)
 ·ext e
  simp only [av];constructor
  ·rintro ⟨i,hi⟩;rw [hb i] at hi;exact hi.1
  ·intro he
   have hq:Sym2.map projMap e∈Q.edgeSet:=by rw [<-himage];exact Set.mem_image_of_mem _ he
   rw [<-e7] at hq;obtain ⟨i,hi⟩:=av.mp hq;exact ⟨i,by rw [hb i];exact ⟨he,hi⟩⟩
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma Jo {V:Type} {G:SimpleGraph V} (W:Finset V)
  (hW:∀⦃x y⦄,G.Adj x y->x∈W/\y∈W)
  {x y:V} (p:G.Walk x y) (hp:0<p.length):p.support.toFinset⊆W:=by
 classical
 intro v hv;obtain ⟨e,he,hv⟩:=Walk.mem_support_iff_exists_mem_edges_of_not_nil
  (p:=p) (by simpa only [Walk.length_eq_zero_iff.symm] using (Nat.ne_of_gt hp)) |>.mp (bw.mp hv)
 induction e using bJ with
 | _ a b=>
   have hab:G.Adj a b:=p.edges_subset_edgeSet he;rcases Sym2.mem_iff.mp hv with rfl | rfl
   ·exact (hW hab).1
   ·exact (hW hab).2
structure lW {V I:Type} [Fintype I]
  (G J:SimpleGraph V) (X:I->Finset V) (W:Finset V) (qB:Finset (Sym2 V)) (k:ℕ) where
 Index:Type
 finiteIndex:Fintype Index
 block:Index->fY G
 count:card Index<=k+2*∑i,(X i).card
 disjoint:Pairwise λ i j=>Disjoint (block i).edges (block j).edges
 Fv:∀i,Disjoint (qB:Set (Sym2 V)) (block i).edges
 cover:(qB:Set (Sym2 V))∪(⋃ i,(block i).edges)=J.edgeSet
 arity:∀i,card (block i).oD <=W.card
 vertices:∀i,(block i).vertices.card<=2*W.card
 jz:(i:Index)->(block i).oD ->I
 Ai:∀i j,(block i).x j∈X (jz i j)/\(block i).y j∈X (jz i j)
instance lW.instFiniteIndex {V I:Type} [Fintype I] {G J:SimpleGraph V} {X:I->Finset V} {W:Finset V} {qB:Finset (Sym2 V)} {k:ℕ} (c:lW G J X W qB k):Fintype c.Index:=c.finiteIndex
lemma lW.subset {V I:Type} [Fintype I]
  {G J:SimpleGraph V} {X:I->Finset V} {W qB k}
  (b:lW G J X W qB k) (i:b.Index):(b.block i).edges⊆J.edgeSet:=by
 rw [<-b.cover];intro e he;exact Or.inr (av.mpr ⟨i,he⟩)
lemma GD {V I:Type} [Fintype V] [Fintype I]
  (G J:SimpleGraph V) (Vq:J<=G) (W:Finset V)
  (hW:∀⦃x y⦄,J.Adj x y->x∈W/\y∈W)
  (X:I->Finset V) (hd:Pairwise λ i j=>Disjoint (X i) (X j))
  (hX:∀i,X i⊆W) (b:kW J X hd)
  {k:ℕ} (hk:e9 b.quotient k):Nonempty (lW G J X W b.qB k):=by
 classical
 let projMap:=bD X hd b.pairing;let A:=W.image projMap;have zI:A.card<=W.card:=ju;obtain ⟨q,LW,Vr,hqn⟩:=vQ projMap (b.gW:Set (Sym2 V))
  (b.Bb.trans (cD Vq)) A (b.x6 W hW)
  b.Cn.symm (by simpa only [kQ] using b.Ji) hk
 have wE (j):(q j).edges⊆(b.gW:Set (Sym2 V)):=by rw [<-Vr];intro e he;exact av.mpr ⟨j,he⟩
 have hex (j) (i:(q j).oD):∃r,(q j).x i∈X r/\(q j).y i∈X r:=by
  obtain he | ⟨r,hx,hy,_⟩:=(jw X hd b.pairing _ _).mp ((hqn j).2.2 i)
  ·exact False.elim ((q j).ne i he)
  ·exact ⟨r,hx,hy⟩
 choose own Wu using hex;let P:={z:Σ i,Fin (b.count i) // 0<(b.path z.1 z.2).walk.length};let path:∀z:P,G.Walk (b.path z.1.1 z.1.2).start (b.path z.1.1 z.1.2).finish:=λ z=>(b.path z.1.1 z.1.2).walk.map (SimpleGraph.Hom.ofLE Vq)
 have hpe (z:P):(path z).edgeSet=(b.path z.1.1 z.1.2).walk.edgeSet:=by simp [path,Walk.edgeSet_map,SimpleGraph.Hom.ofLE]
 have YF (z:P):(path z).IsPath:=(b.path z.1.1 z.1.2).simple.map oQ;have YG (z:P):2<=(path z).length:=by simpa only [path,Walk.length_map] using (b.Ai z.1.1 z.1.2 z.property).2.2
 let t:P->fY G:=λ z=>fY.qX (path z) (YF z) (YG z)
 have L9 (z:P):(t z).edges=(b.path z.1.1 z.1.2).walk.edgeSet:=hpe z;have YH (z:P):(t z).vertices.card<=W.card:=by
  apply aU;change (path z).support.toFinset⊆W;simpa [path,Walk.support_map,SimpleGraph.Hom.ofLE] using
   Jo W hW (b.path z.1.1 z.1.2).walk z.property
 have YI (z:P):card (t z).oD <=W.card:=by change card Unit<=W.card;simpa using cT.mpr ⟨(b.path z.1.1 z.1.2).start,hX z.1.1 (b.Ai z.1.1 z.1.2 z.property).1⟩
 have GQ:(⋃ z,(t z).edges)=⋃ i,⋃ j,(b.path i j).walk.edgeSet:=by
  ext e;simp only [av];constructor
  ·rintro ⟨z,hz⟩;exact ⟨z.1.1,z.1.2,(L9 z)▸hz⟩
  ·rintro ⟨i,j,hj⟩
   have hp:0<(b.path i j).walk.length:=by by_contra h;have hn:=Walk.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h);have he:=Walk.edges_eq_nil.mpr hn;change e∈(b.path i j).walk.edges at hj;rw [he] at hj;contradiction
   exact ⟨⟨⟨i,j⟩,hp⟩,by rw [L9];exact hj⟩
 refine ⟨{
  Index:=Fin k ⊕ P,finiteIndex:=inferInstance,block:=Sum.elim q t,count:=?_,disjoint:=?_,Fv:=?_,cover:=?_,arity:=?_,vertices:=?_,jz:=λ j=>match j with | Sum.inl j=>own j | Sum.inr z=>λ _=>z.1.1,Ai:=?_
 }⟩
 ·have hp:card P<=2*∑i,(X i).card:=by
   calc
    _<=card (Σ i,Fin (b.count i)):=card_subtype_le _
    _=∑i,b.count i:=by simp
    _<=∑i,2*(X i).card:=aK (λ i _=>b.count_le i)
    _=_:=by rw [<-dR]
  simpa only [fO,dU] using Nat.add_le_add_left hp k
 ·intro j l hne
  rcases j with j | j<;>rcases l with l | l<;>dsimp only [Sum.elim_inl,Sum.elim_inr]
  ·exact LW (λ h=>hne (aF Sum.inl h))
  ·exact (b.Cm l.1.1 l.1.2).mono (wE j) (by rw [L9])
  ·exact ((b.Cm j.1.1 j.1.2).mono (wE l) (by rw [L9])).symm
  ·rw [L9,L9];exact b.J5 (λ h=>hne (aF Sum.inr (aZ h)))
 ·rintro (j | z)<;>dsimp only [Sum.elim_inl,Sum.elim_inr]
  ·exact b.L5.mono_right (wE j)
  ·rw [L9];exact b.OK _ _
 ·
  simp only [Set.iUnion_sum,Sum.elim_inl,Sum.elim_inr];rw [Vr,GQ,<-Set.union_assoc];exact b.cover
 ·rintro (j | z)
  ·exact (hqn j).1.trans zI
  ·exact YI z
 ·rintro (j | z)
  ·exact (hqn j).2.1.trans (Nat.mul_le_mul_left _ zI)
  ·exact (YH z).trans (by omega)
 ·rintro (j | z) i
  ·exact Wu j i
  ·exact ⟨(b.Ai z.1.1 z.1.2 z.property).2.1,(b.Ai z.1.1 z.1.2 z.property).1⟩
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma Al:∃dN:ℝ,1<dN/\∀D≥dN,∀(V R B:Type) [Fintype V] [Fintype R] [Fintype B],∀(G F:SimpleGraph V) (P:R->SimpleGraph V) (U:R->Finset V),F<=G->(∀r,P r<=G)->Pairwise (λ r s=>Disjoint (P r).edgeSet (P s).edgeSet)->Pairwise (λ r s=>Disjoint (U r) (U s))->(∀r,Disjoint F.edgeSet (P r).edgeSet)->(∀r,b9 (P r) (U r) (D^(9/10:ℝ)/4))->(∀r,D^(9/10:ℝ)<=((U r).card:ℝ)/\((U r).card:ℝ)<=D^(51/50:ℝ))->∀(J:B->SimpleGraph V) (W:B->Finset V),(∀b,J b<=F)->Pairwise (λ b c=>Disjoint (J b).edgeSet (J c).edgeSet)->(⋃ b,(J b).edgeSet)=F.edgeSet->(∀b,∀⦃x y⦄,(J b).Adj x y->x∈W b/\y∈W b)->(∀b,((W b).card:ℝ)<=D^(3/10:ℝ))->∀(I:B->Type) [∀b,Fintype (I b)] (X:∀b,I b->Finset V)
    (Kx:∀b,Pairwise λ i j=>Disjoint (X b i) (X b j)),
   (∀b i,X b i⊆W b)->∀rX:∀b,I b->R,(∀b i,X b i⊆U (rX b i))->(∀b i v,v∈X b i->(F.degree v:ℝ)<=D^(1/100:ℝ))->∀(Am:∀b,kW (J b) (X b) (Kx b)) (k:B->ℕ),(∀b,e9 (Am b).quotient (k b))->∃(K:Type) (_:Fintype K) (parts:K->Set (Sym2 V)) (used:Set (Sym2 V)),card K<=(∑b,k b)+8*∑b,∑i,(X b i).card/\(∀j,e8 G (parts j))/\Pairwise (λ j l=>Disjoint (parts j) (parts l))/\used⊆⋃ r,(P r).edgeSet/\Disjoint F.edgeSet used/\(⋃ j,parts j)=F.edgeSet∪used:=by
 classical
 obtain ⟨dN,ko,An⟩:=zA;refine ⟨dN,ko,?_⟩;intro D hD V R B _ _ _ G F P U GX oe vm Cs SI he hr J W Nn OP SJ hW Jp I _ X Kx Qg rX Qi hdeg Am k hk;have hT (b:B):=GD G (J b) ((Nn b).trans GX) (W b) (hW b)
  (X b) (Kx b) (Qg b) (Am b) (hk b)
 let T:∀b,lW G (J b) (X b) (W b) (Am b).qB (k b):=λ b=>Classical.choice (hT b)
 let Q:=Σ b,(T b).Index;let q:Q->fY G:=λ z=>(T z.1).block z.2
 have wE (z:Q):(q z).edges⊆F.edgeSet:=((T z.1).subset z.2).trans (cD (Nn z.1));have LW:Pairwise λ z w:Q=>Disjoint (q z).edges (q w).edges:=by
  rintro ⟨b,i⟩ ⟨c,j⟩ hne;by_cases hh:b=c
  ·subst c;exact (T b).disjoint (λ h=>hne (by cases h;rfl))
  ·exact (OP hh).mono ((T b).subset i) ((T c).subset j)
 let jz:(z:Q)->(q z).oD ->R:=λ z i=>rX z.1 ((T z.1).jz z.2 i)
 obtain ⟨parts,used,uT,Q8,Lc,Nm,e7⟩:=An D hD V R Q G F P U GX oe vm Cs SI he hr q wE LW jz
   (λ z i=>⟨Qi _ _ ((T z.1).Ai z.2 i).1,Qi _ _ ((T z.1).Ai z.2 i).2⟩)
   (λ z i=>⟨hdeg _ _ _ ((T z.1).Ai z.2 i).1,hdeg _ _ _ ((T z.1).Ai z.2 i).2⟩)
   (λ z=>(cq.mpr ((T z.1).arity z.2)).trans (Jp z.1))
   (λ z=>(cq.mpr ((T z.1).vertices z.2)).trans (by push_cast;exact aJ (Jp z.1) (by norm_num)))
 let S:=Σ b,(Am b).qB;let e:S->Sym2 V:=λ z=>z.2.val
 have xA (z:S):e z∈(J z.1).edgeSet:=(Am z.1).N7 z.2.property;have Vs (z:S):e z∈F.edgeSet:=cD (Nn z.1) (xA z);have hinj:Function.Injective e:=by
  rintro ⟨b,i⟩ ⟨c,j⟩ h;by_cases hh:b=c
  ·subst c;exact Sigma.ext rfl (heq_of_eq (aZ h))
  ·exact False.elim (aI.mp (OP hh) (xA ⟨b,i⟩) (h▸xA ⟨c,j⟩))
 have Ud (z:S) (w:Q):e z∉(q w).edges:=by
  intro hw;by_cases hh:z.1=w.1
  ·rcases z with ⟨b,z⟩;rcases w with ⟨c,w⟩;dsimp only at hh;subst c;exact aI.mp ((T b).Fv w) z.property hw
  ·exact aI.mp (OP hh) (xA z) ((T w.1).subset w.2 hw)
 have Ma (z:S) (w:Q):e z∉parts w:=by
  intro hw;have hu:e z∈⋃ w,parts w:=av.mpr ⟨w,hw⟩;rw [e7] at hu;rcases hu with hu | hu
  ·obtain ⟨w,hw⟩:=av.mp hu;exact Ud z w hw
  ·exact aI.mp Nm (Vs z) hu
 have OQ:(⋃ z:S,{e z})∪(⋃ w:Q,(q w).edges)=F.edgeSet:=by
  rw [<-SJ];ext f;simp only [b8,av,dB];constructor
  ·rintro (⟨z,hz⟩ | ⟨w,hw⟩)
   ·exact ⟨z.1,hz▸xA z⟩
   ·exact ⟨w.1,(T w.1).subset w.2 hw⟩
  ·rintro ⟨b,hb⟩
   rw [<-(T b).cover] at hb;rcases hb with hb | hb
   ·exact Or.inl ⟨⟨b,⟨f,hb⟩⟩,rfl⟩
   ·obtain ⟨j,hj⟩:=av.mp hb;exact Or.inr ⟨⟨b,j⟩,hj⟩
 refine ⟨Q ⊕ S,inferInstance,Sum.elim parts (λ z=>{e z}),used,?_,?_,?_,Lc,Nm,?_⟩
 ·have hq:card Q<=(∑b,k b)+2*∑b,∑i,(X b i).card:=by
   calc
    _=∑b,card (T b).Index:=fy
    _<=∑b,(k b+2*∑i,(X b i).card):=aK (λ b _=>(T b).count)
    _=_:=by rw [f8,<-dR]
  have hs:card S<=6*∑b,∑i,(X b i).card:=by
   calc
    _=∑b,(Am b).qB.card:=by simp [S,fy]
    _<=∑b,6*∑i,(X b i).card:=aK (λ b _=>(Am b).SC)
    _=_:=by rw [<-dR]
  rw [fO];omega
 ·rintro (j | z)
  ·exact uT j
  ·exact Or.inr ⟨e z,cD GX (Vs z),rfl⟩
 ·rintro (i | i) (j | j) hij<;>dsimp only [Sum.elim_inl,Sum.elim_inr]
  ·exact Q8 (λ h=>hij (aF Sum.inl h))
  ·exact (Set.disjoint_singleton_right).mpr (Ma j i)
  ·exact (Set.disjoint_singleton_left).mpr (Ma i j)
  ·exact mK.mpr (λ h=>hij (aF Sum.inr (hinj h)))
 ·simp only [Set.iUnion_sum,Sum.elim_inl,Sum.elim_inr]
  rw [e7];calc
   _=((⋃ z:S,{e z})∪(⋃ w:Q,(q w).edges))∪used:=by rw [Set.union_comm ((⋃ w:Q,(q w).edges)∪used),Set.union_assoc]
   _=_:=by rw [OQ]
end
end af.Batch
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.Batch.Splitting
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open MeasureTheory ProbabilityTheory Finset Real
section qe
variable {Ω:Type bX} {I:Type bY} [MeasurableSpace Ω] {μ:Measure Ω} [IsProbabilityMeasure μ]
end qe
section
variable {V:Type cz} [Fintype V] [DecidableEq V]
end
open Filter Asymptotics
open scoped Topology
universe u
end af.Batch.Splitting
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Real
def f6 (x:ℝ):ℝ:=if x=1 then 1/2 else max (1/2) (1-1/sqrt (logb 2 x))
lemma HY:f6 1=1/2:=by simp [f6]
lemma k7 (x:ℝ):1/2<=f6 x/\f6 x<=1:=by
 by_cases hx:x=1
 ·norm_num [f6,hx]
 ·simp only [f6,hx,ite_false];exact ⟨b6 _ _,max_le (by norm_num) (by linarith [one_div_nonneg.mpr (Real.sqrt_nonneg (logb 2 x))])⟩
lemma Cu:MonotoneOn f6 (Set.Ici 1):=by
 intro x hx y hy hxy;by_cases hx1:x=1
 ·simpa [hx1,HY] using (k7 y).1
 have SK:1<x:=lt_of_le_of_ne hx (Ne.symm hx1);have Wv:1<y:=SK.trans_le hxy;have kI:logb 2 x<=logb 2 y:=dL (by norm_num)
  (by linarith) hxy
 have Ue:0<logb 2 x:=g4 (by norm_num) SK;have hinv:=h9 (Real.sqrt_pos.mpr Ue) (m8 kI);simp only [f6,hx1,ne_of_gt Wv,ite_false];exact max_le_max dH (by linarith)
lemma tO (x:ℝ) (kI:4<=logb 2 x):f6 x=1-1/sqrt (logb 2 x):=by
 have hx:x≠1:=by intro hx;subst x;norm_num at kI
 have Uf:2<=sqrt (logb 2 x):=by convert m8 kI using 1;norm_num
 have hinv:1/sqrt (logb 2 x)<=1/2:=h9 (by norm_num) Uf;simp only [f6,hx,ite_false];exact max_eq_right (by linarith)
def jQ:ℝ:=1/sqrt (3/10)-1
lemma Fw:0<jQ:=by
 have hs:0<sqrt (3/10:ℝ):=Real.sqrt_pos.mpr (by norm_num);have YJ:sqrt (3/10:ℝ)<1:=by exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
 dsimp [jQ];have hh:=(one_lt_div hs).mpr YJ;linarith
lemma Ao (D n:ℝ) (hD:1<D) (hn:D <=n)
  (hw:40/3<=logb 2 D):jQ/sqrt (logb 2 D)<=f6 n-f6 (D^(3/10:ℝ)):=by
 have hD0:0<D:=by linarith
 have hw0:0<logb 2 D:=by linarith
 have Ug:logb 2 D <=logb 2 n:=dL (by norm_num) hD0 hn;have Qj:logb 2 (D^(3/10:ℝ))=(3/10)*logb 2 D:=by exact jH hD0
 rw [tO n (by linarith),tO (D^(3/10:ℝ)) (by rw [Qj];linarith),Qj];have hinv:=h9 (Real.sqrt_pos.mpr hw0)
  (m8 Ug)
 have q7:1/sqrt ((3/10)*logb 2 D)-1/sqrt (logb 2 D)=jQ/sqrt (logb 2 D):=by rw [Real.sqrt_mul (by norm_num:(0:ℝ)<=3/10)];dsimp [jQ];field_simp
 rw [<-q7];linarith
lemma x9 (A w:ℝ) (hA:0<=A) (hw0:0<w)
  (hw:((A+1)/jQ)^2<=w):(A+1)/w<=jQ/sqrt w:=by
 have hd:=Fw;have BX:0<=(A+1)/jQ:=by positivity
 have hs:(A+1)/jQ<=sqrt w:=by have hh:=m8 hw;simpa [Real.sqrt_sq BX] using hh
 have hm:A+1<=jQ*sqrt w:=by have:=(dK hd).mp hs;simpa [bK] using this
 apply (nS hw0 (Real.sqrt_pos.mpr hw0)).mpr;have hmul:=aY hm (Real.sqrt_nonneg w);simpa [mul_assoc,Real.mul_self_sqrt hw0.le] using hmul
lemma AQ (D n S C A₁ A₂:ℝ)
  (hD:1<D) (hn:D <=n) (hS:0<=S) (hC:0<=C)
  (Jq:0<=A₁) (YK:0<=A₂) (Vt:7*A₂<=C)
  (hw:40/3<=logb 2 D)
  (ob:((A₁+1)/jQ)^2<=logb 2 D):A₂*(S+n/logb 2 D)+(C/100)*S+C*f6 (D^(3/10:ℝ))*(n-S/3+A₁*n/logb 2 D)<=C*f6 n*n:=by
 let f:=f6 (D^(3/10:ℝ));obtain ⟨Ww,SM⟩:=k7 (D^(3/10:ℝ));have hw0:0<logb 2 D:=by linarith
 have hn0:0<=n:=by linarith
 have PS:0<=n/logb 2 D:=fF hn0 hw0.le;have SN:A₂+C/100-C*f/3<=0:=by dsimp [f];nlinarith [aJ Ww hC]
 have OR:=mul_nonpos_of_nonpos_of_nonneg SN hS;have SO:A₂<=C:=by linarith
 have SP:C*f*A₁<=C*A₁:=by exact aY (by simpa [f] using aJ SM hC) Jq
 have Vu:=aY (dS SO SP) PS;have habs:=x9 A₁ (logb 2 D) Jq hw0 ob;have Uh:=Ao D n hD hn hw;have Oa:=aJ (habs.trans Uh) (bZ hC hn0);change A₂*(S+n/logb 2 D)+(C/100)*S+C*f*(n-S/3+A₁*n/logb 2 D)<=_;change C*n*((A₁+1)/logb 2 D)<=C*n*(f6 n-f) at Oa;simp only [gq] at OR Vu Oa ⊢;nlinarith only [OR,Vu,Oa]
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
lemma Ap (P:SimpleGraph V) [DecidableRel P.Adj]
  (W:Finset V) (h:ℝ) (he:cW (P.induce (W:Set V)) h):b9 P W h:=by
 intro A hA;let B:Finset (W:Set V):=univ.filter (λ x=>x.val∈A);have SQ:B.image Subtype.val=A:=by
  ext x;simp only [bk];constructor
  ·rintro ⟨y,hy,rfl⟩;exact (aD.mp hy).2
  ·intro hx;exact ⟨⟨x,hA hx⟩,by simp [B,hx],rfl⟩
 have hcomp:=r9 W B;rw [SQ] at hcomp;have hh:=he B;rw [uk,SQ] at hh;have hc:B.card=A.card:=by rw [<-SQ,gI _ dM]
 have YL:Bᶜ.card=(W\A).card:=by rw [<-hcomp,gI _ dM]
 simpa only [hc,YL] using hh
lemma Ev {V:Type} [aP:Fintype V] [aO:DecidableEq V] {P Q:SimpleGraph V} [DecidableRel P.Adj] [DecidableRel Q.Adj]
  {W:Finset V} {h:ℝ} (he:b9 P W h) (YM:P<= Q):b9 Q W h:=by
 intro A hA;exact (he A hA).trans (cq.mpr (aU (by intro e he;simp only [nQ] at he ⊢;exact ⟨he.1,he.2.1,YM he.2.2⟩)))
lemma BF:∃dN:ℝ,∀D≥dN,∀(V:Type) [Fintype V] [DecidableEq V] (R:SimpleGraph V) (W:Finset V),(∀⦃x y⦄,R.Adj x y->x∈W/\y∈W)->D^(9/10:ℝ)<=(W.card:ℝ)->(W.card:ℝ)<=D^(51/50:ℝ)->b9 R W (D^(9/10:ℝ))->∃P T:SimpleGraph V,P<=R/\T<=R/\Disjoint P.edgeSet T.edgeSet/\P.edgeSet∪T.edgeSet=R.edgeSet/\b9 P W (D^(9/10:ℝ)/4)/\b9 T W (D^(9/10:ℝ)/4):=by
 obtain ⟨dN,q2⟩:=aR.af.Splitting.uL 1 (by norm_num) 2 (by norm_num);refine ⟨dN,?_⟩;intro D hD V _ _ R W hW hlo hhi he;let R':=R.induce (W:Set V);have he':aR.af.aV.cW R' (D^(9/10:ℝ)):=oh R W _ he;obtain ⟨ω,hω,e7,hdis⟩:=q2 D hD (W:Set V) R' (D^(9/10:ℝ))
  (by simp) (by simpa using hlo) (by simpa using hhi) he'
 let f:(W:Set V) ↪ V:=⟨Subtype.val,dM⟩;let Q (i:Fin 2):=(aR.af.Splitting.dI R' ω i).map f;have Qk (i:Fin 2):Q i<=R:=by apply (map_le_iff_le_comap _ _ _).mpr;exact λ _ _ h=>h.1
 have N4 (i):(Q i).induce (W:Set V)=aR.af.Splitting.dI R' ω i:=comap_map_eq f _;have hexp (i):@b9 V _ (Q i) (λ _ _=>Classical.propDecidable _) W (D^(9/10:ℝ)/4):=by
  apply @Ap V _ _ (Q i) (λ _ _=>Classical.propDecidable _) W;have Wx:cW (aR.af.Splitting.dI R' ω i) (D^(9/10:ℝ)/4):=by simpa only [cW,aR.af.aV.cW,j8,show (2:ℝ)*2=4 by norm_num] using hω i
  convert Wx using 1;simp only [N4]
 have Mb (i):(Q i).edgeSet=Sym2.map (Subtype.val:↥(W:Set V)->V) ''
  (aR.af.Splitting.dI R' ω i).edgeSet:=edgeSet_map f _
 refine ⟨Q 0,Q 1,Qk 0,Qk 1,?_,?_,hexp 0,hexp 1⟩
 ·rw [Mb,Mb];apply aI.mpr;rintro e ⟨a,ha,hae⟩ ⟨b,hb,hbe⟩;have hab:=fI dM (hae.trans hbe.symm);subst b;exact aI.mp (hdis 0 1 (by decide)) ha hb
 ·apply mW
  ·exact Set.union_subset (cD (Qk 0)) (cD (Qk 1))
  ·intro e YN
   induction e using bJ with
   | _ x y=>
     have hxy:R.Adj x y:=YN;obtain ⟨i,hi⟩:=(e7 ⟨x,(hW hxy).1⟩ ⟨y,(hW hxy).2⟩).mp hxy;have hm:s(x,y)∈(Q i).edgeSet:=by rw [Mb];exact ⟨s(⟨x,(hW hxy).1⟩,⟨y,(hW hxy).2⟩),hi,rfl⟩
     fin_cases i
     ·exact Or.inl hm
     ·exact Or.inr hm
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
def n7 {V:Type} (R:SimpleGraph V) (used:Set (Sym2 V)):SimpleGraph V:=R\fromEdgeSet used
lemma q3 {V:Type} (R:SimpleGraph V) (used:Set (Sym2 V)):(n7 R used).edgeSet=R.edgeSet\used:=by simp [n7,edgeSet_sdiff]
lemma qD {V:Type} (R:SimpleGraph V) (used:Set (Sym2 V)):n7 R used<=R:=λ _ _ h=>h.1
lemma BG {V:Type} {R T:SimpleGraph V} {used:Set (Sym2 V)}
  (No:T<=R) (GQ:Disjoint T.edgeSet used):T<=n7 R used:=by
 apply oW.mp;rw [q3];exact λ _ he=>⟨cD No he,λ hu=>aI.mp GQ he hu⟩
lemma Cv {V A:Type} (R P T:A->SimpleGraph V)
  (xN:Pairwise λ i j=>Disjoint (R i).edgeSet (R j).edgeSet)
  (Ky:∀i,P i<=R i) (No:∀i,T i<=R i)
  (YO:∀i,Disjoint (T i).edgeSet (P i).edgeSet)
  (used:Set (Sym2 V)) (hu:used⊆⋃ i,(P i).edgeSet):∀i,Disjoint (T i).edgeSet used:=by
 intro i;apply aI.mpr;intro e he YP;obtain ⟨j,hj⟩:=av.mp (hu YP);by_cases hij:i=j
 ·subst j;exact aI.mp (YO i) he hj
 ·exact aI.mp (xN hij) (cD (No i) he)
   (cD (Ky j) hj)
lemma BH {V A K:Type} [Fintype V] [Fintype A] [Fintype K]
  (G F:SimpleGraph V) (R:A->SimpleGraph V)
  (Kz:∀i,R i<=G)
  (xN:Pairwise λ i j=>Disjoint (R i).edgeSet (R j).edgeSet)
  (KA:∀i,Disjoint F.edgeSet (R i).edgeSet)
  (e7:F.edgeSet∪(⋃ i,(R i).edgeSet)=G.edgeSet)
  (parts:K->Set (Sym2 V)) (hp:∀k,e8 G (parts k))
  (hd:Pairwise λ j k=>Disjoint (parts j) (parts k))
  (used:Set (Sym2 V)) (hu:used⊆⋃ i,(R i).edgeSet)
  (uT:(⋃ k,parts k)=F.edgeSet∪used):aM G<=card K+∑i,aM (n7 (R i) used):=by
 apply oc G parts hp hd (λ i=>n7 (R i) used)
  (λ i=>(qD _ _).trans (Kz i))
 ·intro i j hij
  exact (xN hij).mono (cD (qD _ _))
   (cD (qD _ _))
 ·intro i k
  rw [q3];apply aI.mpr;intro e he hp;have hpe:e∈F.edgeSet∪used:=uT▸av.mpr ⟨k,hp⟩;rcases hpe with hpe | hpe
  ·exact aI.mp (KA i) hpe he.1
  ·exact he.2 hpe
 ·rw [uT,<-e7]
  simp_rw [q3];ext e;simp only [b8,av,kR];constructor
  ·rintro ((hf | hu') | ⟨i,hi,_⟩)
   ·exact Or.inl hf
   ·exact Or.inr (av.mp (hu hu'))
   ·exact Or.inr ⟨i,hi⟩
  ·rintro (hf | ⟨i,hi⟩)
   ·exact Or.inl (Or.inl hf)
   ·by_cases he:e∈used
    ·exact Or.inl (Or.inr he)
    ·exact Or.inr ⟨i,hi,he⟩
lemma BI {V I:Type} [Fintype V] [Fintype I]
  (J:SimpleGraph V) (X:I->Finset V) (hd:Pairwise λ i j=>Disjoint (X i) (X j))
  (p:kW J X hd) (W:Finset V)
  (hW:∀⦃x y⦄,J.Adj x y->x∈W/\y∈W)
  (hX:∀i,X i⊆W) (n:ℕ) (M t:ℝ) (aaW:0<=t) (hn:W.card<n) (hM:(W.card:ℝ)<=M)
  (ih:∀(A:Type) [Fintype A] (H:SimpleGraph A),card A<n->(card A:ℝ)<=M->(aM H:ℝ)<=t*card A):
  ∃k,e9 p.quotient k/\(k:ℝ)<=t*((W.card:ℝ)-∑i,((X i).card/2:ℕ)):=by
 classical
 let A:=W.image (bD X hd p.pairing);let H:=p.quotient.induce (A:Set (gZ X p.pairing));have ho:A.card+∑i,(X i).card/2=W.card:=x5 X hd p.pairing W hX;have hn':card (A:Set (gZ X p.pairing))<n:=by simp only [oX,eG];omega
 refine ⟨aM H,Dj _ A (p.x6 W hW) (ov H),?_⟩;have hc:=ih (A:Set (gZ X p.pairing)) H hn' (by simp only [oX,eG];exact (cq.mpr (by omega:A.card<=W.card)).trans hM);simp only [oX,eG] at hc;have heq:(A.card:ℝ)=(W.card:ℝ)-∑i,((X i).card/2:ℕ):=by
  have hh:(A.card:ℝ)+∑i,((X i).card/2:ℕ)=W.card:=by exact_mod_cast ho
  linarith
 rwa [heq] at hc
end
end af.Batch
namespace af.Batch
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma vT:∃dN:ℝ,1<dN/\∀D≥dN,∀(V A B:Type) [Fintype V] [Fintype A] [Fintype B],∀(G F:SimpleGraph V) (R:A->SimpleGraph V) (U:A->Finset V),F<=G->(∀r,R r<=G)->Pairwise (λ r s=>Disjoint (R r).edgeSet (R s).edgeSet)->Pairwise (λ r s=>Disjoint (U r) (U s))->(∀r,∀⦃x y⦄,(R r).Adj x y->x∈U r/\y∈U r)->(∀r,Disjoint F.edgeSet (R r).edgeSet)->F.edgeSet∪(⋃ r,(R r).edgeSet)=G.edgeSet->(∀r,b9 (R r) (U r) (D^(9/10:ℝ)))->(∀r,D^(9/10:ℝ)<=((U r).card:ℝ)/\((U r).card:ℝ)<=D^(51/50:ℝ))->∀(J:B->SimpleGraph V) (W:B->Finset V),(∀b,J b<=F)->Pairwise (λ b c=>Disjoint (J b).edgeSet (J c).edgeSet)->(⋃ b,(J b).edgeSet)=F.edgeSet->(∀b,∀⦃x y⦄,(J b).Adj x y->x∈W b/\y∈W b)->(∀b,((W b).card:ℝ)<=D^(3/10:ℝ))->∀(I:B->Type) [∀b,Fintype (I b)] (X:∀b,I b->Finset V)
   (aaC:∀b,Pairwise λ i j=>Disjoint (X b i) (X b j)),
  (∀b i,X b i⊆W b)->∀rX:∀b,I b->A,(∀b i,X b i⊆U (rX b i))->(∀b i v,v∈X b i->(F.degree v:ℝ)<=D^(1/100:ℝ))->1<=D^(1/100:ℝ)->(∀b i,8<=(X b i).card)->(∀b i,(D^(1/100:ℝ))^2<=(X b i).card)->∀(n:ℕ) (t:ℝ),0<=t->(∀b,(W b).card<n)->(∀(Q:Type) [Fintype Q] (H:SimpleGraph Q),card Q<n->(card Q:ℝ)<=D^(3/10:ℝ)->(aM H:ℝ)<=t*card Q)->
  ∃H:A->SimpleGraph V,(∀r,H r<=R r)/\(∀r,b9 (H r) (U r) (D^(9/10:ℝ)/4))/\(aM G:ℝ)<=t*((∑b,((W b).card:ℝ))-∑b,∑i,((X b i).card/2:ℕ))+8*(∑b,∑i,((X b i).card:ℝ))+∑r,(aM (H r):ℝ):=by
 obtain ⟨D₁,q2⟩:=BF;obtain ⟨D₂,F7,An⟩:=Al;refine ⟨max D₁ D₂,dZ F7 (bC _ _),?_⟩;intro D hD V A B _ _ _ G F R U GX Kz xN Cs Ql KA e7 he hr
  J W Nn OP SJ hW Jp I _ X Kx Qg rX Qi hdeg ha hm L0 n t ht hn ih
 have hs (r:A):=q2 D ((b6 _ _).trans hD) V (R r) (U r)
  (Ql r) (hr r).1 (hr r).2 (he r)
 choose P T Ky No YQ Vj OS YS using hs;have vm:Pairwise λ r s=>Disjoint (P r).edgeSet (P s).edgeSet:=λ _ _ h=>(xN h).mono (cD (Ky _)) (cD (Ky _))
 have hp (b:B):Nonempty (kW (J b) (X b) (Kx b)):=KR (J b) (X b) (Kx b) (D^(1/100:ℝ)) ha (hm b) (L0 b)
   (λ i v hv=>(cq.mpr (degree_le_of_le (Nn b))).trans (hdeg b i v hv))
 let Am (b:B):=Classical.choice (hp b);have hq (b:B):=BI (J b) (X b) (Kx b) (Am b) (W b)
  (hW b) (Qg b) n (D^(3/10:ℝ)) t ht (hn b) (Jp b) ih
 choose k hk YU using hq;obtain ⟨K,hK,parts,used,B0,uT,hdis,Lc,Nm,MR⟩:=An D ((bC _ _).trans hD) V A B G F P U GX
   (λ r=>(Ky r).trans (Kz r)) vm Cs
   (λ r=>(KA r).mono_right (cD (Ky r))) OS hr
   J W Nn OP SJ hW Jp I X Kx Qg rX Qi hdeg Am k hk
 let:Fintype K:=hK;have SR:used⊆⋃ r,(R r).edgeSet:=Lc.trans (Set.iUnion_mono λ r=>cD (Ky r));have YV:=Cv R P T xN Ky No (λ r=>(YQ r).symm) used Lc;let H (r:A):=n7 (R r) used;have jF:=BH G F R Kz xN KA e7 parts uT hdis used SR MR;refine ⟨H,λ r=>qD _ _,λ r=>?_,?_⟩
 ·exact Ev (YS r) (BG (No r) (YV r))
 ·have YW:(card K:ℝ)<=(∑b,(k b:ℝ))+8*(∑b,∑i,((X b i).card:ℝ)):=by
   exact_mod_cast B0
  have Ui:=aK (s:=univ) (λ b _=>YU b);have YX:(∑b,(k b:ℝ))<=t*((∑b,((W b).card:ℝ))-∑b,∑i,((X b i).card/2:ℕ)):=by simpa only [dR,sum_sub_distrib,mul_sub,eV] using Ui
  have hc:(aM G:ℝ)<=(card K:ℝ)+∑r,(aM (H r):ℝ):=by exact_mod_cast jF
  linarith
end
end af.Batch
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
universe u
open Finset SimpleGraph
variable {V:Type bX} [Fintype V] [DecidableEq V]
structure DFSState (G:SimpleGraph V) where
 stack:List V
 finished:Finset V
 dJ:Finset V
 nodup:stack.Nodup
 chain:stack.IsChain G.Adj
 f_s:Disjoint finished stack.toFinset
 Np:Disjoint finished dJ
 OT:Disjoint stack.toFinset dJ
 cover:finished∪stack.toFinset∪dJ=univ
 separation:∀x∈finished,∀y∈dJ,¬G.Adj x y
namespace DFSState
variable {G:SimpleGraph V}
lemma card_eq (s:DFSState G):card V=s.finished.card+s.stack.length+s.dJ.card:=by have hdis:Disjoint (s.finished∪s.stack.toFinset) s.dJ:=disjoint_union_left.mpr ⟨s.Np,s.OT⟩;have hc:=aF card s.cover;rw [j9 hdis,j9 s.f_s,eJ s.nodup,c7] at hc;exact hc.symm
lemma Q9 (s:DFSState G) (hs:s.stack=[]) (v:V) (hv:v∈s.dJ):∃t:DFSState G,t.finished=s.finished/\t.dJ.card+1=s.dJ.card:=by
 have hvf:v∉s.finished:=λ hf=>aL.mp s.Np hf hv
 refine ⟨⟨[v],s.finished,s.dJ.erase v,by simp,by simp,?_,?_,?_,?_,?_⟩,rfl,?_⟩
 ·simpa using hvf
 ·exact s.Np.mono_right (jm _ _)
 ·simp
 ·change s.finished∪{v}∪s.dJ.erase v=univ;rw [union_assoc,singleton_union,insert_erase hv];simpa only [hs,List.toFinset_nil,union_empty] using s.cover
 ·intro x hx y hy;exact s.separation x hx y (mem_of_mem_erase hy)
 ·exact jg hv
lemma push (s:DFSState G) (v w:V) (L:List V) (hs:s.stack=v::L)
  (hw:w∈s.dJ) (hadj:G.Adj w v):∃t:DFSState G,t.finished=s.finished/\t.dJ.card+1=s.dJ.card:=by
 have YY:w∉s.stack:=λ h=>aL.mp s.OT
  (bw.mpr h) hw
 have YZ:w∉s.finished:=λ h=>aL.mp s.Np h hw
 refine ⟨⟨w::s.stack,s.finished,s.dJ.erase w,?_,?_,?_,?_,?_,?_,?_⟩,rfl,?_⟩
 ·exact i9.mpr ⟨YY,s.nodup⟩
 ·rw [hs];exact List.IsChain.cons_cons hadj (hs▸s.chain)
 ·simpa using And.intro YZ s.f_s
 ·exact s.Np.mono_right (jm _ _)
 ·rw [List.toFinset_cons,m9];exact ⟨(by simp),s.OT.mono_right (jm _ _)⟩
 ·ext x
  have hx:x∈s.finished∪s.stack.toFinset∪s.dJ:=by rw [s.cover];simp
  simp only [gQ] at hx;simp only [List.toFinset_cons,gQ,bU,iK,aQ,iff_true];by_cases Vv:x=w
  ·exact Or.inl (Or.inr (Or.inl Vv))
  ·rcases hx with (h|h)|h
   ·exact Or.inl (Or.inl h)
   ·exact Or.inl (Or.inr (Or.inr h))
   ·exact Or.inr ⟨Vv,h⟩
 ·intro x hx y hy;exact s.separation x hx y (mem_of_mem_erase hy)
 ·exact jg hw
lemma pop (s:DFSState G) (v:V) (L:List V) (hs:s.stack=v::L)
  (hn:∀w∈s.dJ,¬G.Adj v w):∃t:DFSState G,t.finished.card=s.finished.card+1/\t.dJ=s.dJ:=by
 have hvf:v∉s.finished:=λ hv=>aL.mp s.f_s hv (by simp [hs])
 have hvu:v∉s.dJ:=λ hv=>aL.mp s.OT (by simp [hs]) hv
 have hL:L.toFinset⊆s.stack.toFinset:=by rw [hs];simp
 have hnd:v∉L/\L.Nodup:=by simpa only [hs,i9] using s.nodup
 have Y0:v∉L:=hnd.1;refine ⟨⟨L,insert v s.finished,s.dJ,?_,?_,?_,?_,?_,?_,?_⟩,?_,rfl⟩
 ·exact hnd.2
 ·exact (hs▸s.chain).of_cons
 ·exact m9.mpr ⟨by simpa using Y0,s.f_s.mono_right hL⟩
 ·exact m9.mpr ⟨hvu,s.Np⟩
 ·exact s.OT.mono_left hL
 ·simpa [hs,insert_union] using s.cover
 ·intro x hx y hy
  rcases bU.mp hx with rfl|hx
  ·exact hn y hy
  ·exact s.separation x hx y hy
 ·exact nW hvf
lemma Jr (s:DFSState G) (hs:s.finished.card<=s.dJ.card):∃t:DFSState G,t.finished.card=t.dJ.card:=by
 generalize hd:s.dJ.card-s.finished.card=d;induction d using jh generalizing s with
 | h d ih=>
   by_cases heq:s.finished.card=s.dJ.card
   ·exact ⟨s,heq⟩
   have hlt:s.finished.card<s.dJ.card:=lt_of_le_of_ne hs heq;have aag:0<d:=by omega
   cases Mc:s.stack with
   | nil=>obtain ⟨v,hv⟩:=cT.mp (show 0<s.dJ.card by omega);obtain ⟨t,KB,GQ⟩:=s.Q9 Mc v hv;apply ih (t.dJ.card-t.finished.card) (by rw [KB];omega) t (by rw [KB];omega) rfl
   | cons v L=>
     by_cases hn:∃w∈s.dJ,G.Adj v w
     ·obtain ⟨w,hw,hadj⟩:=hn;obtain ⟨t,KB,GQ⟩:=s.push v w L Mc hw hadj.symm;apply ih (t.dJ.card-t.finished.card) (by rw [KB];omega) t (by rw [KB];omega) rfl
     ·push Not at hn
      obtain ⟨t,KB,GQ⟩:=s.pop v L Mc hn;apply ih (t.dJ.card-t.finished.card) (by rw [KB,GQ];omega) t (by rw [KB,GQ];omega) rfl
end DFSState
lemma zC (G:SimpleGraph V):∃s:DFSState G,s.finished.card=s.dJ.card:=by let s:DFSState G:=⟨[],∅,univ,by simp,by simp,by simp,by simp,by simp,by simp,by simp⟩;exact s.Jr (by simp [s])
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset SimpleGraph
variable {V:Type bY} [Fintype V] [DecidableEq V]
def k5 (G:SimpleGraph V) [DecidableRel G.Adj] (U:Finset V):Finset V:=univ.filter (λ v=>v∉U/\∃u∈U,G.Adj u v)
def s5 (G:SimpleGraph V) [DecidableRel G.Adj] (α:ℝ):Prop:=∀U:Finset V,U.Nonempty->2*U.card<=card V->α*U.card<=((k5 G U).card:ℝ)
lemma DFSState.Jt (G:SimpleGraph V) [DecidableRel G.Adj] (s:DFSState G):k5 G s.dJ⊆s.stack.toFinset:=by
 intro v hv;obtain ⟨_,hvu,u,hu,hadj⟩:=aD.mp hv;have hc:v∈s.finished∪s.stack.toFinset∪s.dJ:=by rw [s.cover];simp
 rcases gQ.mp hc with h|h
 ·rcases gQ.mp h with h|h
  ·exact (s.separation v h u hu hadj.symm).elim
  ·exact h
 ·exact (hvu h).elim
lemma GF (G:SimpleGraph V) [DecidableRel G.Adj]
  (α:ℝ) (DU:α<=1) (hexp:s5 G α):∃L:List V,L.Nodup/\L.IsChain G.Adj/\α*card V/3<=(L.length:ℝ):=by
 obtain ⟨s,heq⟩:=zC G;refine ⟨s.stack,s.nodup,s.chain,?_⟩;have hc:=s.card_eq;rw [heq] at hc;have hcR:(card V:ℝ)=2*(s.dJ.card:ℝ)+(s.stack.length:ℝ):=by exact_mod_cast (show card V=2*s.dJ.card+s.stack.length by omega)
 have hN:((k5 G s.dJ).card:ℝ)<=(s.stack.length:ℝ):=by have ht:=aU (s.Jt G);rw [eJ s.nodup] at ht;exact_mod_cast ht
 by_cases hU:s.dJ.Nonempty
 ·have iE:2*s.dJ.card<=card V:=by omega
  have he:=(hexp s.dJ hU iE).trans hN;have ht:(0:ℝ)<=s.stack.length:=aN _;have ha:=aY DU ht;nlinarith
 ·have hu:s.dJ.card=0:=by simp [pG.mp hU]
  rw [hu,g3,mul_zero,zero_add] at hcR;nlinarith [show (0:ℝ)<=s.stack.length from aN _,aY DU (show (0:ℝ)<=s.stack.length from aN _)]
end af.eF
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset SimpleGraph
variable {V:Type bX} [Fintype V] [DecidableEq V]
def eE (G:SimpleGraph V) (J:Finset V):SimpleGraph V where
 Adj x y:=G.Adj x y/\x∉J/\y∉J
 symm:=⟨λ _x _y h=>⟨h.1.symm,h.2.2,h.2.1⟩⟩
 loopless:=⟨λ _x h=>G.irrefl h.1⟩
lemma Bd {V:Type bY} [aP:Fintype V] [aO:DecidableEq V] {H:SimpleGraph V} {L:List V} (hL:L.IsChain H.Adj)
  {x y:V} (hx:x∈L) (hy:y∈L):H.Reachable x y:=by
 let:Trans H.Reachable H.Reachable H.Reachable:=⟨λ h₁ h₂=>h₁.trans h₂⟩;cases L with
 | nil=>simp at hx
 | cons a L=>
   have hC:(a::L).IsChain H.Reachable:=hL.imp (λ _ _ h=>h.reachable);have ha:∀b∈a::L,H.Reachable a b:=by
    intro b hb;rcases dd.mp hb with rfl|hb
    ·exact .refl _
    ·exact hC.rel_cons hb
   exact (ha x hx).symm.trans (ha y hy)
lemma HZ (G:SimpleGraph V) [DecidableRel G.Adj]
  (α m:ℝ) (DU:0<=α) (hexp:s5 G α)
  (X Z J:Finset V) (hX:X.Nonempty) (hZ:Z.Nonempty)
  (Md:Disjoint X J) (OU:Disjoint Z J)
  (Me:∀x∈X,∀y∈X,(eE G J).Reachable x y)
  (WX:∀x∈Z,∀y∈Z,(eE G J).Reachable x y)
  (SU:m<=(X.card:ℝ)) (SV:m<=(Z.card:ℝ))
  (hJ:(J.card:ℝ)<α*m):∃x∈X,∃z∈Z,(eE G J).Reachable x z:=by
 classical
 by_contra hn;obtain ⟨x,hx⟩:=hX;obtain ⟨z,hz⟩:=hZ;let H:=eE G J;let A:Finset V:=univ.filter (λ v=>v∉J/\H.Reachable x v);let B:Finset V:=univ\(J∪A);have Vw:X⊆A:=by intro y hy;exact mem_filter.mpr ⟨mem_univ _,(aL.mp Md hy),Me x hx y hy⟩
 have Y1:∀y∈Z,¬H.Reachable x y:=by intro y hy hr;exact hn ⟨x,hx,y,hy,hr⟩
 have Vx:Z⊆B:=by intro y hy;simp only [B,aS,mem_univ,b5,mem_union,not_or];refine ⟨aL.mp OU hy,?_⟩;intro ha;exact Y1 y hy (mem_filter.mp ha).2.2
 have wU:Disjoint A B:=by apply aL.mpr;intro y ha hb;exact (mem_sdiff.mp hb).2 (mem_union_right J ha)
 have hc:A.card+B.card<=card V:=by rw [<-card_union_of_disjoint wU];exact card_le_univ _
 have Ob:k5 G A⊆J:=by intro v hv;obtain ⟨_,OJ,u,hu,hadj⟩:=mem_filter.mp hv;by_contra Ku;obtain ⟨_,LZ,Y2⟩:=mem_filter.mp hu;have Oc:H.Adj u v:=⟨hadj,LZ,Ku⟩;exact OJ (mem_filter.mpr ⟨mem_univ _,Ku,Y2.trans Oc.reachable⟩)
 have Od:k5 G B⊆J:=by
  intro v hv;obtain ⟨_,SB,u,hu,hadj⟩:=mem_filter.mp hv;by_contra Ku;have OJ:v∈A:=by by_contra Y3;exact SB (mem_sdiff.mpr ⟨mem_univ _,by simpa using And.intro Ku Y3⟩)
  obtain ⟨_,_,hrv⟩:=mem_filter.mp OJ;have LZ:u∉J:=λ h=>(mem_sdiff.mp hu).2 (mem_union_left A h)
  have Oc:H.Adj v u:=⟨hadj.symm,Ku,LZ⟩;have Y4:u∈A:=mem_filter.mpr ⟨mem_univ _,LZ,hrv.trans Oc.reachable⟩;exact (mem_sdiff.mp hu).2 (mem_union_right J Y4)
 have OV (Q:Finset V) (hne:Q.Nonempty) (iE:2*Q.card<=card V)
   (hm:m<=(Q.card:ℝ)) (hb:k5 G Q⊆J):False:=by
  have he:=hexp Q hne iE;have hc:((k5 G Q).card:ℝ)<=J.card:=by exact_mod_cast card_le_card hb
  have hh:=aJ hm DU;linarith
 by_cases iE:2*A.card<=card V
 ·exact OV A ⟨x,Vw hx⟩ iE
   (SU.trans (by exact_mod_cast card_le_card Vw)) Ob
 ·exact OV B ⟨z,Vx hz⟩ (by omega)
   (SV.trans (by exact_mod_cast card_le_card Vx)) Od
lemma KU {V:Type cy} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V) (J:Finset V) {x z:V}
  (p:(eE G J).Walk x z) (hx:x∉J):∀w∈p.support,w∉J:=by
 induction p with
 | nil=>simpa using hx
 | @cons u v z hadj p ih=>
   intro w hw;rcases dd.mp hw with rfl|hw
   ·exact hx
   ·exact ih hadj.2.2 w hw
lemma BJ (G:SimpleGraph V) (X Z J:Finset V)
  (Md:Disjoint X J)
  (hr:∃x∈X,∃z∈Z,(eE G J).Reachable x z):∃x∈X,∃z∈Z,∃p:G.Walk x z,p.IsPath/\∀w∈p.support,w∉J/\(w∈X->w=x)/\(w∈Z->w=z):=by
 classical
 let H:=eE G J;let P:ℕ->Prop:=λ k=>∃x∈X,∃z∈Z,∃p:H.Walk x z,p.IsPath/\p.length=k
 have hP:∃k,P k:=by obtain ⟨x,hx,z,hz,hr⟩:=hr;obtain ⟨p,hp⟩:=hr.exists_isPath;exact ⟨p.length,x,hx,z,hz,p,hp,rfl⟩
 obtain ⟨x,hx,z,hz,p,hp,Gb⟩:=Nat.find_spec hP;have JP:∀a∈X,∀b∈Z,∀q:H.Walk a b,q.IsPath->p.length<=q.length:=by intro a ha b hb q hq;rw [Gb];exact Nat.find_min' hP ⟨a,ha,b,hb,q,hq,rfl⟩
 have hsub:H<=G:=λ _ _ h=>h.1
 refine ⟨x,hx,z,hz,p.mapLe hsub,(hp.mapLe hsub),?_⟩;intro w hw;rw [Walk.support_mapLe_eq_support] at hw;refine ⟨KU G J p (aL.mp Md hx) w hw,?_,?_⟩
 ·intro SW;by_contra hne;have hlt:=Walk.length_dropUntil_lt_length hw hne;have hle:=JP w SW z hz (p.dropUntil w hw) (hp.dropUntil hw);omega
 ·intro SX;by_contra hne;have hlt:=Walk.length_takeUntil_lt_length hw hne;have hle:=JP x hx w SX (p.takeUntil w hw) (hp.takeUntil hw);omega
lemma H7 {V:Type cz} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V) (x z:V) (B:List V)
  (hC:(x :: (B ++ [z])).IsChain G.Adj):∃p:G.Walk x z,p.support=x :: (B ++ [z]):=by
 let L:=x :: (B ++ [z]);have hn:L≠[] :=by simp [L]
 let p:=Walk.ofSupport L hn hC;have hx:L.head hn=x:=rfl;have hz:L.getLast hn=z:=by simp [L]
 exact ⟨p.copy hx hz,by change ((Walk.ofSupport L hn hC).copy hx hz).support=L;rw [Walk.support_copy,Walk.support_ofSupport]⟩
lemma Ew (G:SimpleGraph V) (X J Z:List V)
  (hnd:(X ++ J ++ Z).Nodup) (hC:(X ++ J ++ Z).IsChain G.Adj)
  (hj:1<=J.length)
  (hc:∃x∈X,∃z∈Z,∃q:G.Walk x z,q.IsPath/\∀w∈q.support,w∉J/\(w∈X->w=x)/\(w∈Z->w=z)):
  ∃a:V,∃c:G.Walk a a,c.IsCycle/\J.length+2<=c.length:=by
 obtain ⟨x,hx,z,hz,q,hq,xM⟩:=hc;obtain ⟨A,B,hX⟩:=List.mem_iff_append.mp hx;obtain ⟨C,D,hZ⟩:=List.mem_iff_append.mp hz;let M:=x :: ((B ++ J ++ C) ++ [z]);have heq:X ++ J ++ Z=A ++ (M ++ D):=by simp [hX,hZ,M,kS]
 have Y5:M.IsChain G.Adj:=by rw [heq] at hC;exact hC.right_of_append.left_of_append
 have Y6:M.Nodup:=by rw [heq] at hnd;exact (fJ.mp (fJ.mp hnd).2.1).1
 obtain ⟨p,Nb⟩:=H7 G x z (B ++ J ++ C) Y5;have hp:p.IsPath:=by rw [Walk.isPath_def,Nb];exact Y6
 have hlen:J.length+1<=p.length:=by have ht:=p.length_support;rw [Nb] at ht;simp only [kT,ng] at ht;omega
 have Vy:x∉p.support.tail:=by have hn:=hp.support_nodup;rw [<-p.cons_tail_support] at hn;exact (i9.mp hn).1
 have SG:z∉q.reverse.support.tail:=by have hn:=hq.reverse.support_nodup;rw [<-q.reverse.cons_tail_support] at hn;exact (i9.mp hn).1
 have hdis:p.support.tail.Disjoint q.reverse.support.tail:=by
  apply ct.mpr;intro w Vz VA;have Y7:w∈q.support:=by simpa using g7 VA
  obtain ⟨Y8,SW,SX⟩:=xM w Y7;have VB:w∈X ++ J ++ Z:=by
   rw [heq];have:w∈M:=by change w∈x :: ((B ++ J ++ C) ++ [z]);rw [<-Nb];exact g7 Vz
   simp only [fQ];exact Or.inr (Or.inl this)
  simp only [fQ] at VB;rcases VB with (hw|hw)|hw
  ·exact Vy (SW hw▸Vz)
  ·exact Y8 hw
  ·exact SG (SX hw▸VA)
 have Y9:x≠z:=by
  intro he;have hz:z∈p.support.tail:=by simp [Nb]
  exact Vy (he▸hz)
 have aah:1<=q.length:=by
  by_contra hh;have:q.length=0:=by omega
  exact Y9 (Walk.eq_of_length_eq_zero this)
 refine ⟨x,p.append q.reverse,hp.isCycle_append hq.reverse hdis (Or.inl (by omega)),?_⟩;simp only [Walk.length_append,Walk.length_reverse];omega
lemma wF (G:SimpleGraph V) [DecidableRel G.Adj]
  (α:ℝ) (DU:0<α) (Mh:α<=1) (hexp:s5 G α)
  (hq:1<=α^2*card V/100):∃a:V,∃c:G.Walk a a,c.IsCycle/\α^2*card V/100<(c.length:ℝ):=by
 classical
 obtain ⟨L,hnd,hchain,hL⟩:=GF G α Mh hexp;let q:=α^2*card V/100;let j:=⌊q⌋₊;have VC:0<=q:=by dsimp [q];linarith
 have Pt:(j:ℝ)<=q:=Nat.floor_le VC;have aaD:q<(j:ℝ)+1:=Nat.lt_floor_add_one q;have aaX:1<=j:=by exact (Nat.le_floor_iff VC).mpr (by simpa [q] using hq)
 have Xw:(0:ℝ)<=L.length:=aN _;have hu0:(0:ℝ)<=card V:=aN _;have Za:α^2<=α:=by nlinarith
 have aaY:2*q<=α*card V/6:=by have hh:=aY Za hu0;dsimp [q];nlinarith [bZ (le_of_lt DU) hu0]
 have Zb:2*(j+1)<=L.length:=by
  have Ra:2*((j:ℝ)+1)<=(L.length:ℝ):=by have aaZ:1<=q:=hq;linarith
  exact_mod_cast Ra
 let k:=(L.length-j)/2;let X:=L.take k;let J:=(L.drop k).take j;let Z:=(L.drop k).drop j;have heq:L=X ++ J ++ Z:=by dsimp [X,J,Z];rw [kS,List.take_append_drop,List.take_append_drop]
 have hk:k<=L.length:=by dsimp [k];omega
 have SY:j<=(L.drop k).length:=by simp only [List.length_drop];dsimp [k];omega
 have Uj:X.length=k:=by simp [X,List.length_take,f9 hk]
 have Qm:J.length=j:=by dsimp [J];rw [List.length_take,f9 SY]
 have Uk:Z.length=L.length-k-j:=by simp only [Z,List.length_drop]
 have Rb:L.length<=4*X.length:=by rw [Uj];dsimp [k];omega
 have Rc:L.length<=4*Z.length:=by rw [Uk];dsimp [k];omega
 rw [heq] at hnd hchain;have VD:X.Nodup:=(fJ.mp (fJ.mp hnd).1).1;have Zc:J.Nodup:=(fJ.mp (fJ.mp hnd).1).2.1;have VE:Z.Nodup:=(fJ.mp hnd).2.1;have Md:X.Disjoint J:=(fJ.mp hnd).1.disjoint;have OU:Z.Disjoint J:=by have hd:=hnd.disjoint;exact ct.mpr (λ w Zd Ze=>ct.mp hd (oY X Ze) Zd)
 have SZ:Disjoint X.toFinset J.toFinset:=by apply aL.mpr;intro w hw S2;exact ct.mp Md (bw.mp hw) (bw.mp S2)
 have Wy:Disjoint Z.toFinset J.toFinset:=by apply aL.mpr;intro w hw S2;exact ct.mp OU (bw.mp hw) (bw.mp S2)
 have Me:∀x∈X.toFinset,∀y∈X.toFinset,(eE G J.toFinset).Reachable x y:=by intro x hx y hy;apply Bd (L:=X) _ (bw.mp hx) (bw.mp hy);apply hchain.left_of_append.left_of_append.imp_of_mem_imp;intro a b ha hb hab;exact ⟨hab,λ hj=>ct.mp Md ha (bw.mp hj),λ hj=>ct.mp Md hb (bw.mp hj)⟩
 have S3:∀x∈Z.toFinset,∀y∈Z.toFinset,(eE G J.toFinset).Reachable x y:=by intro x hx y hy;apply Bd (L:=Z) _ (bw.mp hx) (bw.mp hy);apply hchain.right_of_append.imp_of_mem_imp;intro a b ha hb hab;exact ⟨hab,λ hj=>ct.mp OU ha (bw.mp hj),λ hj=>ct.mp OU hb (bw.mp hj)⟩
 have Wz:X.toFinset.Nonempty:=by rw [<-cT,eJ VD];omega
 have WA:Z.toFinset.Nonempty:=by rw [<-cT,eJ VE];omega
 have SU:(L.length:ℝ)/4<=X.toFinset.card:=by
  rw [eJ VD];have:(L.length:ℝ)<=4*(X.length:ℝ):=by exact_mod_cast Rb
  linarith
 have SV:(L.length:ℝ)/4<=Z.toFinset.card:=by
  rw [eJ VE];have:(L.length:ℝ)<=4*(Z.length:ℝ):=by exact_mod_cast Rc
  linarith
 have Rd:(J.toFinset.card:ℝ)<α*((L.length:ℝ)/4):=by rw [eJ Zc,Qm];have hmul:=aJ hL (le_of_lt DU);dsimp [q] at Pt;nlinarith
 obtain ⟨x,hx,z,hz,p,hp,Re⟩:=BJ G X.toFinset Z.toFinset J.toFinset SZ
  (HZ G α ((L.length:ℝ)/4) (le_of_lt DU) hexp
   X.toFinset Z.toFinset J.toFinset Wz WA SZ Wy Me S3 SU SV Rd)
 obtain ⟨a,c,hc,hlen⟩:=Ew G X J Z hnd hchain (by omega)
  ⟨x,bw.mp hx,z,bw.mp hz,p,hp,by simpa using Re⟩
 refine ⟨a,c,hc,?_⟩;rw [Qm] at hlen;have RJ:(j:ℝ)+2<=c.length:=by exact_mod_cast hlen
 change q<(c.length:ℝ);linarith
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Classical
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset SimpleGraph Classical
variable {V:Type cP} [Fintype V] [DecidableEq V]
def fW (G:SimpleGraph V) (A:Finset V):Prop:=∀⦃x y⦄,G.Adj x y->x∈A/\y∈A
structure aE (V:Type cL) [DecidableEq V] where
 vertices:Finset V
 graph:SimpleGraph V
 supported:fW graph vertices
noncomputable def jR (G:SimpleGraph V) (A:Finset V):SimpleGraph V where
 Adj x y:=G.Adj x y/\x∈A/\y∈A
 symm:=⟨λ _ _ h=>⟨h.1.symm,h.2.2,h.2.1⟩⟩
 loopless:=⟨λ _ h=>G.irrefl h.1⟩
noncomputable def o5 (G:SimpleGraph V) (A B:Finset V):SimpleGraph V where
 Adj x y:=G.Adj x y/\((x∈A/\y∈B)\/(x∈B/\y∈A))
 symm:=⟨λ _ _ h=>⟨h.1.symm,h.2.elim (λ h=>Or.inr ⟨h.2,h.1⟩)
  (λ h=>Or.inl ⟨h.2,h.1⟩)⟩⟩
 loopless:=⟨λ _ h=>G.irrefl h.1⟩
noncomputable def dw (L:List (SimpleGraph V)) (x y:V):ℕ:=by
 classical
 exact L.countP (λ H=>H.Adj x y)
def cj (G:SimpleGraph V) (L:List (SimpleGraph V)):Prop:=∀x y,dw L x y=if G.Adj x y then 1 else 0
noncomputable def cw (G:SimpleGraph V):ℕ:=by
 classical
 exact G.edgeFinset.card
noncomputable def rM (G:SimpleGraph V) (A B:Finset V):ℕ:=by
 classical
 exact (G.interedges A B).card
def b9 (G:SimpleGraph V) (A:Finset V) (h:ℝ):Prop:=∀U⊆A,h*min (U.card:ℝ) ((A\U).card:ℝ)<=rM G U (A\U)
@[simp] lemma Ex {V:Type c9} [aP:Fintype V] [aO:DecidableEq V] (x y:V):dw [] x y=0:=by
 classical
 simp [dw]
@[simp] lemma iW {V:Type dW} [aP:Fintype V] [aO:DecidableEq V] (H:SimpleGraph V) (L) (x y:V):dw (H::L) x y=(if H.Adj x y then 1 else 0)+dw L x y:=by
 classical
 simp [dw,List.countP_cons,Nat.add_comm]
@[simp] lemma dV {V:Type eo} [aP:Fintype V] [aO:DecidableEq V] (L M:List (SimpleGraph V)) (x y:V):dw (L++M) x y=dw L x y+dw M x y:=by
 classical
 simp [dw]
lemma H8 {V:Type d7} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V) (A:Finset V):jR G A<=G:=λ _ _ h=>h.1
lemma p8 {V:Type d8} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V) (A:Finset V):fW (jR G A) A:=λ _ _ h=>h.2
lemma sw {V:Type d9} [aP:Fintype V] [aO:DecidableEq V] {G:SimpleGraph V} {L:List (SimpleGraph V)}
  (h:cj G L) {H:SimpleGraph V} (hH:H∈L):H<=G:=by
 classical
 intro x y hxy;by_contra hn;have hc:=h x y;simp only [hn,ite_false] at hc;have hp:0<dw L x y:=by simpa [dw,List.countP_pos_iff] using (show ∃K∈L,K.Adj x y from ⟨H,hH,hxy⟩)
 omega
@[simp] lemma DV {V:Type eO} [aP:Fintype V] [aO:DecidableEq V] :cw (⊥:SimpleGraph V)=0:=by
 classical
 apply card_eq_zero.mpr;apply l7.mpr;intro e he;simp only [cu,edgeSet_bot,mD] at he
open Real
noncomputable def f4 (T x:ℝ):ℝ:=1+1/logb 2 (T/2)-1/logb 2 (max x (T/2))
lemma H9:(1/4:ℝ)<=logb 2 (4/3):=by
 have h:=dL (b:=2) (x:=2) (y:=(4/3:ℝ)^4)
  (by norm_num) (by norm_num) (by norm_num)
 rw [Real.logb_pow] at h;norm_num only [Real.logb_self_eq_one,j8] at h;have kI:0<Real.log 2:=kO (by norm_num);nlinarith
lemma vE (T x:ℝ) (hT:4<=T):1<=f4 T x/\f4 T x<=2:=by
 have PW:1<=logb 2 (T/2):=by
  have hh:=dL (b:=2) (x:=2) (y:=T/2)
   (by norm_num) (by norm_num) (by linarith)
  norm_num [Real.logb] at hh;exact hh
 have kI:=dL (b:=2) (x:=T/2) (y:=max x (T/2))
  (by norm_num) (by linarith) (bC _ _)
 have iE:0<logb 2 (T/2):=by linarith
 have G3:0<logb 2 (max x (T/2)):=by linarith
 have S4:1/logb 2 (max x (T/2))<=1/logb 2 (T/2):=h9 iE kI;have VF:1/logb 2 (T/2)<=1:=(kd iE).mpr PW;dsimp [f4];constructor
 ·linarith
 ·linarith [one_div_pos.mpr G3]
lemma AR (T:ℝ) (hT:4<=T):Monotone (f4 T):=by
 intro x y hxy;have j4:0<T/2:=by linarith
 have Ul:0<logb 2 (max x (T/2)):=g4 (by norm_num) (dZ (by linarith:1<T/2) (bC _ _));have kI:=dL (b:=2) (by norm_num)
  (dZ j4 (bC x (T/2))) (max_le_max hxy dH)
 have hi:=h9 Ul kI;dsimp [f4];linarith
lemma zD (T u u₁:ℝ) (hT:4<=T) (hu:T<u)
  (h₁:u₁<=3*u/4):(1/4:ℝ)/(logb 2 u)^2<=f4 T u-f4 T u₁:=by
 let M:=max u₁ (T/2);have hu0:0<u:=by linarith
 have S5:0<M:=dZ (by linarith:0<T/2) (bC _ _);have aa0:M<=3*u/4:=max_le h₁ (by linarith);have WB:M<=u:=by linarith
 have Nq:0<logb 2 u:=g4 (by norm_num) (by linarith);have Zg:0<logb 2 M:=g4 (by norm_num)
  (dZ (by linarith:1<T/2) (bC _ _))
 have WC:logb 2 M<=logb 2 u:=dL (by norm_num) S5 WB;have Oe:(4/3:ℝ)<=u/M:=(e3 S5).mpr (by linarith);have Qn:=dL (b:=2) (x:=4/3) (y:=u/M)
  (by norm_num) (by norm_num) Oe
 rw [Real.logb_div hu0.ne' S5.ne'] at Qn;have Of:(1/4:ℝ)<=logb 2 u-logb 2 M:=H9.trans Qn;have Pv:max u (T/2)=u:=max_eq_left (by linarith);dsimp [f4];rw [Pv];change (1/4:ℝ)/(logb 2 u)^2<=(1+1/logb 2 (T/2)-1/logb 2 u)-(1+1/logb 2 (T/2)-1/logb 2 M);have q7:(1+1/logb 2 (T/2)-1/logb 2 u)-(1+1/logb 2 (T/2)-1/logb 2 M)=(logb 2 u-logb 2 M)/(logb 2 M*logb 2 u):=by field_simp;ring
 rw [q7];apply (nS (sq_pos_of_pos Nq) (f7 Zg Nq)).mpr;have hm:=aY WC Nq.le;nlinarith [iH (logb 2 u)]
lemma ya (T u u₁ u₂:ℝ) (hT:4<=T) (hu:T<u)
  (Qo:0<=u₁) (Um:0<=u₂) (h₁:u₁<=3*u/4) (h₂:u₂<=u)
  (hsum:u₁+u₂<=u+(1/32:ℝ)*u₁/(logb 2 u)^2):u₁*f4 T u₁+u₂*f4 T u₂<=u*f4 T u:=by
 have WD:=zD T u u₁ hT hu h₁;have hmono:=AR T hT h₂;obtain ⟨aai,SM⟩:=vE T u hT;have Pw:=aJ WD Qo;have WE:=aJ hmono Um;have Nq:0<logb 2 u:=g4 (by norm_num) (by linarith);have hden:0<(logb 2 u)^2:=sq_pos_of_pos Nq;have Mj:=aY hsum (by linarith:0<=f4 T u);have aa1:0<=u₁/(logb 2 u)^2:=fF Qo hden.le;have BX:u₁*((1/4:ℝ)/(logb 2 u)^2)=(1/4:ℝ)*(u₁/(logb 2 u)^2):=by ring
 have Rg:((1/32:ℝ)*u₁/(logb 2 u)^2)*f4 T u=(1/32:ℝ)*(u₁/(logb 2 u)^2)*f4 T u:=by ring
 simp only [add_mul] at Mj;rw [Rg] at Mj;rw [BX] at Pw;nlinarith
noncomputable def gU (G:SimpleGraph V) (U:Finset V):Finset V:=univ.filter (λ v=>v∉U/\∃u∈U,G.Adj u v)
lemma GG {G:SimpleGraph V} {A U:Finset V} (hG:fW G A):gU G U⊆A:=by intro x hx;obtain ⟨u,hu,hadj⟩:=(aD.mp hx).2.2;exact (hG hadj).2
lemma Ey (G:SimpleGraph V) (U:Finset V):Disjoint U (gU G U):=by apply aL.mpr;intro x hx hn;exact (aD.mp hn).2.1 hx
lemma AS {G:SimpleGraph V} {A U:Finset V}
  (hG:fW G A) (Zh:U⊆A):fW (G\jR G (U∪gU G U)) (A\U):=by
 intro x y hxy;obtain ⟨hx,hy⟩:=hG hxy.1;have hb (x y:V) (hxy:G.Adj x y) (hx:x∈U):y∈U∪gU G U:=by
  by_cases hy:y∈U
  ·exact cQ _ hy
  ·exact ee _ (aD.mpr ⟨aQ _,hy,x,hx,hxy⟩)
 constructor
 ·refine aS.mpr ⟨hx,λ OW=>?_⟩;exact hxy.2 ⟨hxy.1,cQ _ OW,hb x y hxy.1 OW⟩
 ·refine aS.mpr ⟨hy,λ Nr=>?_⟩;exact hxy.2 ⟨hxy.1,hb y x hxy.1.symm Nr,cQ _ Nr⟩
lemma Ez {G:SimpleGraph V} {A U:Finset V} {T:ℝ}
  (hT:4<=T) (qU:T<(A.card:ℝ)) (hU:U⊆A)
  (hne:U.Nonempty) (u7:2*U.card<=A.card)
  (Nu:((gU G U).card:ℝ)<(1/32:ℝ)*U.card/(logb 2 A.card)^2):(U∪gU G U).Nonempty/\(A\U).Nonempty/\((U∪gU G U).card:ℝ)<=3*A.card/4/\(A\U).card<A.card/\((U∪gU G U).card:ℝ)+(A\U).card<=A.card+(1/32:ℝ)*(U∪gU G U).card/(logb 2 A.card)^2:=by
 have hu:0<U.card:=hne.card_pos;have kI:1<=logb 2 (A.card:ℝ):=by
  have h:=dL (b:=2) (x:=2) (y:=A.card)
   (by norm_num) (by norm_num) (by linarith)
  norm_num [Real.logb] at h;exact h
 have hd:0<(logb 2 (A.card:ℝ))^2:=by positivity
 have Oe:(1/32:ℝ)/(logb 2 (A.card:ℝ))^2<=1/2:=by apply (dK hd).mpr;nlinarith [iH (logb 2 (A.card:ℝ)-1)]
 have iE:((gU G U).card:ℝ)<(U.card:ℝ)/2:=by
  have hm:=aY Oe (aN U.card);have q7:(1/32:ℝ)/(logb 2 (A.card:ℝ))^2*U.card=(1/32:ℝ)*U.card/(logb 2 (A.card:ℝ))^2:=by ring
  rw [q7] at hm;linarith
 have Px:=j9 (Ey G U);have Py:=ni hU;have VG:((U∪gU G U).card:ℝ)=U.card+(gU G U).card:=by exact_mod_cast Px
 have VH:((A\U).card:ℝ)+U.card=A.card:=by exact_mod_cast Py
 have Zi:2*(U.card:ℝ)<=A.card:=by exact_mod_cast u7
 have aaE:(1/32:ℝ)*U.card/(logb 2 A.card)^2<=(1/32:ℝ)*(U∪gU G U).card/(logb 2 A.card)^2:=by gcongr;exact subset_union_left
 refine ⟨hne.mono subset_union_left,?_,?_,?_,?_⟩
 ·exact cT.mp (by omega)
 ·linarith
 ·omega
 ·linarith
lemma BK {G K:SimpleGraph V} {L M:List (SimpleGraph V)}
  (hle:K<=G) (hL:cj K L) (hM:cj (G\K) M):cj G (L++M):=by
 intro x y;have h₁:=hL x y;have h₂:=hM x y;have hk:=@hle x y;simp only [dV,sdiff_adj] at h₂ ⊢;by_cases hK:K.Adj x y<;>by_cases hG:G.Adj x y<;>simp_all
lemma KV (G:SimpleGraph V) (A:Finset V) (T:ℝ)
  (hT:4<=T) (hA:A.Nonempty) (hG:fW G A)
  (q2:∀B⊆A,∀H:SimpleGraph V,H<=G->fW H B->T<(B.card:ℝ)->∃U⊆B,U.Nonempty/\2*U.card<=B.card/\((gU H U).card:ℝ)<(1/32:ℝ)*U.card/(logb 2 B.card)^2):
  ∃L:List (aE V),(∀P∈L,P.vertices⊆A/\P.vertices.Nonempty/\(P.vertices.card:ℝ)<=T)/\(∀x∈A,∃P∈L,x∈P.vertices)/\cj G (L.map aE.graph)/\(L.map (λ P=>(P.vertices.card:ℝ)*f4 T P.vertices.card)).sum<=(A.card:ℝ)*f4 T A.card:=by
 classical
 induction hn:A.card using jh generalizing A G with
 | h n ih=>
   by_cases iE:(A.card:ℝ)<=T
   ·let P:aE V:=⟨A,G,hG⟩
    refine ⟨[P],?_,?_,?_,?_⟩
    ·intro Q hQ;simp only [jM] at hQ;subst Q;exact ⟨Subset.refl _,hA,iE⟩
    ·intro x hx;exact ⟨P,by simp,hx⟩
    ·intro x y;simp [P]
    ·simp [P,<-hn]
   ·have qU:T<(A.card:ℝ):=iG iE
    obtain ⟨U,hU,hne,u7,Nu⟩:=q2 A (Subset.refl _) G dH hG qU;let B:=gU G U;let A₁:=U∪B;let A₂:=A\U;let G₁:=jR G A₁;let G₂:=G\G₁;have Jq:A₁⊆A:=union_subset hU (GG hG);have Qp:A₂⊆A:=lg;have Oh:G₁<=G:=H8 G A₁;have Qr:G₂<=G:=sdiff_le;have F4:fW G₁ A₁:=p8 G A₁;have CS:fW G₂ A₂:=AS hG hU;obtain ⟨NI,NJ,Mk,Ml,hsum⟩:=Ez hT qU hU hne u7 Nu;have S6:A₁.card<n:=by
     have hn0:(0:ℝ)<A.card:=by linarith
     have hlt:(A₁.card:ℝ)<A.card:=lt_of_le_of_lt Mk (by linarith);exact hn▸(Nat.cast_lt.mp hlt)
    have S7:A₂.card<n:=hn▸Ml;have Nv (D:Finset V) (hD:D⊆A) (K:SimpleGraph V) (hK:K<=G):∀C⊆D,∀H:SimpleGraph V,H<=K->fW H C->T<(C.card:ℝ)->∃U⊆C,U.Nonempty/\2*U.card<=C.card/\((gU H U).card:ℝ)<(1/32:ℝ)*U.card/(logb 2 C.card)^2:=by intro C hC H hH hs qU;exact q2 C (hC.trans hD) H (hH.trans hK) hs qU
    obtain ⟨L,hL,Un,Mm,Zj⟩:=ih _ S6 G₁ A₁ NI F4
     (Nv A₁ Jq G₁ Oh) rfl
    obtain ⟨M,hM,Up,S8,Zk⟩:=ih _ S7 G₂ A₂ NJ CS
     (Nv A₂ Qp G₂ Qr) rfl
    refine ⟨L++M,?_,?_,?_,?_⟩
    ·intro P hP
     rcases fQ.mp hP with hP | hP
     ·obtain ⟨hsub,hne,hbound⟩:=hL P hP;exact ⟨hsub.trans Jq,hne,hbound⟩
     ·obtain ⟨hsub,hne,hbound⟩:=hM P hP;exact ⟨hsub.trans Qp,hne,hbound⟩
    ·intro x hx
     by_cases OW:x∈U
     ·obtain ⟨P,hP,OC⟩:=Un x (cQ _ OW);exact ⟨P,List.mem_append_left _ hP,OC⟩
     ·obtain ⟨P,hP,OC⟩:=Up x (aS.mpr ⟨hx,OW⟩);exact ⟨P,oY _ hP,OC⟩
    ·simpa only [gK] using BK Oh Mm S8
    ·simp only [gK,nj]
     have hsub:=ya T A.card A₁.card A₂.card hT qU
      (aN _) (aN _) Mk (by exact_mod_cast Ml.le) hsum
     rw [<-hn];linarith
end af.eF
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe u
universe bX bY cy cz cP cL c9
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset SimpleGraph Classical
variable {V:Type bX} [Fintype V] [DecidableEq V]
lemma qO {V:Type bY} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V) (S:Finset (Sym2 V))
  (hS:∀e,e∈S↔e∈G.edgeSet):cw G=S.card:=by
 unfold cw;congr 1;ext e;simp only [cu];exact (hS e).symm
def lY (K:SimpleGraph V):Prop:=∃a:V,∃p:K.Walk a a,p.IsCycle/\K.edgeSet=p.edgeSet
def r8 (G:SimpleGraph V) (ℓ:ℝ):Prop:=∀a:V,∀p:G.Walk a a,p.IsCycle->(p.length:ℝ)<ℓ
lemma r8.mono {V:Type cy} [aP:Fintype V] [aO:DecidableEq V] {G H:SimpleGraph V} {ℓ:ℝ}
  (h:r8 G ℓ) (hle:H<=G):r8 H ℓ:=by
 intro a p hp;simpa using h a (p.mapLe hle) (hp.mapLe hle)
lemma EA (G:SimpleGraph V) {a:V} (p:G.Walk a a) (hp:p.IsCycle):∃K:SimpleGraph V,K<=G/\lY K/\cw K=p.length:=by
 classical
 let K:=fromEdgeSet p.edgeSet;have he:K.edgeSet=p.edgeSet:=by rw [edgeSet_fromEdgeSet,sdiff_eq_left];exact aI.mpr (λ e he hd=>G.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he) hd)
 have hle:K<=G:=oW.mp (he▸p.edges_subset_edgeSet);have KC:∀e∈p.edges,e∈K.edgeSet:=by intro e he';rw [he];exact he'
 refine ⟨K,hle,⟨a,p.transfer K KC,hp.transfer KC,?_⟩,?_⟩
 ·simpa using he
 ·rw [qO K p.edges.toFinset (by
   intro e;simp only [bw,he];rfl)]
  exact (eJ hp.isTrail.edges_nodup).trans p.length_edges
lemma EC {G K:SimpleGraph V} (hle:K<=G):cw (G\K)+cw K=cw G:=by
 classical
 rw [qO (G\K) (G.edgeFinset\K.edgeFinset) (by
  intro e;simp only [aS,cu,edgeSet_sdiff,kR]),
  qO K K.edgeFinset (by intro e;simp),qO G G.edgeFinset (by intro e;simp)]
 exact ni (edgeFinset_mono hle)
lemma ED {K:SimpleGraph V} (h:lY K):0<cw K:=by
 classical
 obtain ⟨a,p,hp,he⟩:=h;have hf:K.edgeFinset=p.edges.toFinset:=by ext e;simp only [cu,he,bw];rfl
 simp only [cw,hf,eJ hp.isTrail.edges_nodup,SimpleGraph.Walk.length_edges];exact hp.three_le_length.trans_lt' (by omega)
lemma Fx (G:SimpleGraph V) (ℓ:ℝ):∃(H:SimpleGraph V) (L:List (SimpleGraph V)),H<=G/\r8 H ℓ/\(∀K∈L,lY K/\ℓ<=(cw K:ℝ))/\cj G (H::L)/\(L.length:ℝ)*ℓ+cw H<=cw G:=by
 classical
 induction hn:cw G using jh generalizing G with
 | h n ih=>
   by_cases Qt:r8 G ℓ
   ·refine ⟨G,[],dH,Qt,by simp,?_,?_⟩
    ·intro x y;simp
    ·simp [<-hn]
   ·obtain ⟨a,p,hp,Gb⟩:∃a,∃p:G.Walk a a,p.IsCycle/\ℓ<=(p.length:ℝ):=by
     by_contra hh;apply Qt;intro a p hp;by_contra hlen;exact hh ⟨a,p,hp,dF hlen⟩
    obtain ⟨K,hle,hK,Qu⟩:=EA G p hp;have heq:=EC hle;have j4:=ED hK;have hlt:cw (G\K)<n:=by omega
    obtain ⟨H,L,hH,OX,hL,hpart,oj⟩:=ih _ hlt (G\K) rfl;refine ⟨H,K::L,hH.trans sdiff_le,OX,?_,?_,?_⟩
    ·intro J hJ
     rcases dd.mp hJ with rfl | hJ
     ·exact ⟨hK,by simpa [Qu] using Gb⟩
     ·exact hL J hJ
    ·intro x y;have hh:=@hH x y;have hk:=@hle x y;have he:=hpart x y;simp only [iW,sdiff_adj] at he ⊢;by_cases hG:G.Adj x y<;>by_cases hK:K.Adj x y<;>by_cases hH:H.Adj x y<;>simp_all
    ·have heqR:(cw (G\K):ℝ)+cw K=cw G:=by exact_mod_cast heq
     have WY:ℓ<=(cw K:ℝ):=by simpa [Qu] using Gb
     simp only [kT,fP,gR];rw [<-hn];nlinarith
open Real Filter Asymptotics
lemma BL:∀ᶠ u:ℝ in atTop,4<=u/\u^(199/200:ℝ)<=((1/32:ℝ)/(logb 2 u)^2)^2*u/100:=by
 have kI:=(isLittleO_log_rpow_rpow_atTop (4:ℝ)
  (s:=1/200) (by norm_num)).const_mul_left ((102400:ℝ)/(log 2)^4)
 filter_upwards [eventually_ge_atTop (4:ℝ),kI.eventuallyLE] with u hu hh;have hu0:0<u:=by linarith
 have UZ:0<=log u:=log_nonneg (by linarith);have aaF:0<log 2:=log_pos (by norm_num);have Nq:0<logb 2 u:=logb_pos (by norm_num) (by linarith);have hr0:0<=u^(1/200:ℝ):=rpow_nonneg hu0.le _;have Uq:0<=(102400:ℝ)/(log 2)^4*(log u)^(4:ℝ):=by positivity
 simp only [kg,gk Uq,gk hr0] at hh;have hden:(102400:ℝ)*(logb 2 u)^4<=u^(1/200:ℝ):=by
  calc
   (102400:ℝ)*(logb 2 u)^4=(102400:ℝ)/(log 2)^(4:ℕ)*(log u)^(4:ℕ):=by simp only [Real.logb,div_pow];ring
   _<=u^(1/200:ℝ):=by simpa only [show (4:ℝ)=((4:ℕ):ℝ) by norm_num,Real.rpow_natCast] using hh
 have hm:=aJ hden (rpow_nonneg hu0.le (199/200:ℝ));have he:u^(199/200:ℝ)*u^(1/200:ℝ)=u:=by rw [<-c8 hu0];norm_num
 rw [he] at hm;refine ⟨hu,?_⟩;have q7:((1/32:ℝ)/(logb 2 u)^2)^2*u/100=u/(102400*(logb 2 u)^4):=by
  field_simp
  ;ring
 rw [q7];exact (e3 (by positivity:(0:ℝ)<102400*(logb 2 u)^4)).mpr (by nlinarith)
lemma Cw:∃Aq:ℝ,∀D≥Aq,4<=D /\4<=D^(51/50:ℝ)/\∀u:ℝ,D^(51/50:ℝ)<u->0<(1/32:ℝ)/(logb 2 u)^2/\(1/32:ℝ)/(logb 2 u)^2<=1/\1<=((1/32:ℝ)/(logb 2 u)^2)^2*u/100/\D^(101/100:ℝ)<((1/32:ℝ)/(logb 2 u)^2)^2*u/100:=by
 obtain ⟨Q,hQ⟩:=eventually_atTop.mp BL;refine ⟨max 4 Q,?_⟩;intro D hD;have Qv:4<=D:=(b6 _ _).trans hD;have hD1:1<=D:=by linarith
 have DW:0<D:=by linarith
 have VI:D <=D^(51/50:ℝ):=by
  simpa only [Real.rpow_one] using g5 hD1
   (by norm_num:(1:ℝ)<=51/50)
 refine ⟨Qv,Qv.trans VI,?_⟩;intro u hu;have Zl:Q<=u:=(bC 4 Q).trans (hD.trans (VI.trans hu.le));obtain ⟨aa2,hq⟩:=hQ u Zl;have kI:1<=logb 2 u:=by
  have h:=dL (b:=2) (x:=2) (y:=u)
   (by norm_num) (by norm_num) (by linarith)
  norm_num [Real.logb] at h;exact h
 have hd:0<(logb 2 u)^2:=by positivity
 have DU:0<(1/32:ℝ)/(logb 2 u)^2:=by positivity
 have Mh:(1/32:ℝ)/(logb 2 u)^2<=1:=by apply (kd hd).mpr;nlinarith [iH (logb 2 u-1)]
 have B2:D^(101/100:ℝ)<u^(199/200:ℝ):=by
  have Nw:=Real.rpow_lt_rpow (fG DW.le (51/50:ℝ)) hu
   (by norm_num:(0:ℝ)<199/200)
  rw [<-lz DW.le] at Nw;have hle:=g5 hD1
   (by norm_num:(101/100:ℝ)<=(51/50)*(199/200))
  exact hle.trans_lt Nw
 have Ur:1<=D^(101/100:ℝ):=jv hD1 (by norm_num);exact ⟨DU,Mh,Ur.trans (B2.le.trans hq),B2.trans_le hq⟩
lemma Cx (G:SimpleGraph V) (A:Finset V) (hG:fW G A)
  (U:Finset {x // x∈A}):gU G (U.image Subtype.val)=(gU (G.induce (A:Set V)) U).image Subtype.val:=by
 classical
 ext y;constructor
 ·intro hy
  obtain ⟨_,Nr,x,hx,hxy⟩:=aD.mp hy;have Ot:=(hG hxy).2;obtain ⟨x',Jl,heq⟩:=bk.mp hx;refine bk.mpr ⟨⟨y,Ot⟩,aD.mpr ⟨aQ _,?_,?_⟩,rfl⟩
  ·intro Nj;exact Nr (bk.mpr ⟨⟨y,Ot⟩,Nj,rfl⟩)
  ·exact ⟨x',Jl,by simpa only [induce_adj,heq] using hxy⟩
 ·intro hy
  obtain ⟨y',Nj,rfl⟩:=bk.mp hy;obtain ⟨_,Nr,x,hx,hxy⟩:=aD.mp Nj;refine aD.mpr ⟨aQ _,?_,?_⟩
  ·intro hy;obtain ⟨z,hz,heq⟩:=bk.mp hy;have Si:z=y':=aZ heq;exact Nr (Si▸hz)
  ·exact ⟨x,bk.mpr ⟨x,hx,rfl⟩,hxy⟩
lemma rN (G:SimpleGraph V) (A:Finset V)
  (hG:fW G A) (ℓ:ℝ) (OX:r8 G ℓ)
  (DU:0<(1/32:ℝ)/(logb 2 A.card)^2)
  (Mh:(1/32:ℝ)/(logb 2 A.card)^2<=1)
  (hq:1<=((1/32:ℝ)/(logb 2 A.card)^2)^2*A.card/100)
  (B2:ℓ<((1/32:ℝ)/(logb 2 A.card)^2)^2*A.card/100):∃U⊆A,U.Nonempty/\2*U.card<=A.card/\((gU G U).card:ℝ)<(1/32:ℝ)*U.card/(logb 2 A.card)^2:=by
 classical
 by_contra R3;let H:=G.induce (A:Set V);let α:=(1/32:ℝ)/(logb 2 A.card)^2;have hexp:s5 H α:=by
  intro U hU u7;let W:=U.image Subtype.val;have hW:W⊆A:=by intro x hx;obtain ⟨x',Jl,rfl⟩:=bk.mp hx;exact x'.property
  have lN:W.card=U.card:=gI _ dM;have WG:W.Nonempty:=hU.image _;have S9:2*W.card<=A.card:=by simpa [lN] using u7
  have hs:¬((gU G W).card:ℝ)<(1/32:ℝ)*W.card/(logb 2 A.card)^2:=λ hs=>R3 ⟨W,hW,WG,S9,hs⟩
  have hbound:=dF hs;have heq:=Cx G A hG U;have Mo:=aF card heq;rw [gI _ dM] at Mo;have hext:k5 H U=gU H U:=by rfl
  rw [hext];change α*(U.card:ℝ)<=(gU H U).card;rw [<-Mo];dsimp [α];rw [<-lN];calc
   (1/32:ℝ)/(logb 2 A.card)^2*(W.card:ℝ)=(1/32:ℝ)*(W.card:ℝ)/(logb 2 A.card)^2:=by ring
   _<=((gU G W).card:ℝ):=hbound
 have Zm:1<=α^2*(card {x // x∈A})/100:=by simpa [α] using hq
 obtain ⟨a,p,hp,Gb⟩:=wF H α DU Mh hexp Zm;let f:H →g G:=⟨Subtype.val,λ h=>h⟩;have hc:=hp.map (f:=f) (by exact dM);have hlen:=OX a.val (p.map f) hc;simp only [l8] at hlen;have Ta:α^2*(A.card:ℝ)/100<(p.length:ℝ):=by simpa using Gb
 dsimp [α] at Ta;linarith
lemma yK (D x:ℝ) (hD:4<=D):f4 (D^(51/50:ℝ)) x<=1+2/logb 2 D:=by
 have hD1:1<=D:=by linarith
 have DW:0<D:=by linarith
 have aa3:2<=logb 2 D:=by
  have h:=dL (b:=2) (x:=4) (y:=D)
   (by norm_num) (by norm_num) hD
  have h4:logb 2 (4:ℝ)=2:=by rw [show (4:ℝ)=2^(2:ℕ) by norm_num,Real.logb_pow];norm_num
  rw [h4] at h;exact h
 have WH:0<logb 2 D:=by linarith
 have Qw:logb 2 (D^(51/50:ℝ)/2)=(51/50:ℝ)*logb 2 D-1:=by rw [Real.logb_div (d6 DW _).ne' (by norm_num),jH DW];norm_num
 have VJ:0<logb 2 (D^(51/50:ℝ)/2):=by rw [Qw];linarith
 have S4:1/logb 2 (D^(51/50:ℝ)/2)<=2/logb 2 D:=by apply (nS VJ WH).mpr;rw [Qw];linarith
 have Pz:0<D^(51/50:ℝ)/2:=by positivity
 have Rh:=dL (b:=2) (by norm_num) Pz
  (bC x (D^(51/50:ℝ)/2))
 have Ut:0<logb 2 (max x (D^(51/50:ℝ)/2)):=dZ VJ Rh;have hinv:=one_div_pos.mpr Ut;dsimp [f4];linarith
lemma BN {G H:SimpleGraph V} {C L:List (SimpleGraph V)}
  (hG:cj G (H::C)) (hH:cj H L):cj G (C++L):=by
 intro x y;have h:=hG x y;simp only [iW] at h;rw [dV,hH x y];omega
lemma MS:∃Aq:ℝ,∀D≥Aq,∀(V:Type u) [Fintype V] [DecidableEq V]
   (G:SimpleGraph V) (A:Finset V),A.Nonempty->fW G A->2*(cw G:ℝ)/A.card<=D ->
  ∃(C:List (SimpleGraph V)) (L:List (aE V)),(∀K∈C,lY K/\D^(101/100:ℝ)<=(cw K:ℝ))/\(C.length:ℝ)<=A.card/(2*D^(1/100:ℝ))/\(∀P∈L,P.vertices⊆A/\P.vertices.Nonempty/\(P.vertices.card:ℝ)<=D^(51/50:ℝ))/\(∀x∈A,∃P∈L,x∈P.vertices)/\cj G (C++L.map aE.graph)/\(L.map (λ P=>(P.vertices.card:ℝ))).sum<=(1+2/logb 2 D)*A.card:=by
 classical
 obtain ⟨Aq,GU⟩:=Cw;refine ⟨Aq,?_⟩;intro D hD V _ _ G A hA hG hdeg;obtain ⟨Qv,VK,hnum⟩:=GU D hD;have DW:0<D:=by linarith
 have VL:(0:ℝ)<A.card:=by exact_mod_cast hA.card_pos
 obtain ⟨H,C,DS,OX,hC,Tb,oj⟩:=Fx G (D^(101/100:ℝ));have Zn:fW H A:=λ _ _ h=>hG (DS h)
 have q2:∀B⊆A,∀K:SimpleGraph V,K<=H->fW K B->D^(51/50:ℝ)<(B.card:ℝ)->∃U⊆B,U.Nonempty/\2*U.card<=B.card/\((gU K U).card:ℝ)<(1/32:ℝ)*U.card/(logb 2 B.card)^2:=by intro B hB K hK hs qU;obtain ⟨ha,Zo,hq,hm⟩:=hnum B.card qU;exact rN K B hs _ (OX.mono hK) ha Zo hq hm
 obtain ⟨L,hL,wu,Mm,jF⟩:=KV H A (D^(51/50:ℝ)) VK hA Zn q2;refine ⟨C,L,hC,?_,hL,wu,BN Tb Mm,?_⟩
 ·have aaj:=(dK VL).mp hdeg
  have he:D^(101/100:ℝ)=D*D^(1/100:ℝ):=by rw [show (101/100:ℝ)=1+1/100 by norm_num,c8 DW,Real.rpow_one]
  rw [he] at oj;apply (e3 (by positivity:(0:ℝ)<2*D^(1/100:ℝ))).mpr;have WZ:(0:ℝ)<=cw H:=aN _;nlinarith
 ·have Ri:=yK D A.card Qv
  have Zp:(L.map (λ P=>(P.vertices.card:ℝ))).sum<=(L.map (λ P=>(P.vertices.card:ℝ)*f4 (D^(51/50:ℝ)) P.vertices.card)).sum:=by apply kU;intro P hP;have hb:=(vE (D^(51/50:ℝ)) P.vertices.card VK).1;have hm:=aJ hb (aN P.vertices.card);simpa using hm
  have hmul:=aJ Ri VL.le;nlinarith
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset SimpleGraph Classical Real
variable {V:Type cz} [Fintype V] [DecidableEq V]
lemma vi (G H:SimpleGraph V):cw (G ⊔ H)<=cw G+cw H:=by
 classical
 simpa [cw,edgeFinset_sup] using dG G.edgeFinset H.edgeFinset
lemma J8 (G:SimpleGraph V) (A B:Finset V) (hd:Disjoint A B):cw (o5 G A B)=rM G A B:=by
 classical
 have hinj:Set.InjOn (λ e:V×V=>s(e.1,e.2)) (G.interedges A B:Set (V×V)):=by
  intro e he f hf hh;rcases kc.mp hh with hh | hh
  ·exact hh
  ·have Zq:=(G.mem_interedges_iff.mp he).1;have Zr:=(G.mem_interedges_iff.mp hf).2.1;have heq:e.1=f.2:=aF Prod.fst hh;exact False.elim (aL.mp hd Zq (heq.symm▸Zr))
 have heq:(o5 G A B).edgeFinset=(G.interedges A B).image (λ e:V×V=>s(e.1,e.2)):=by
  ext e;induction e using i8 with | _ x y=>
   simp only [cu,ic];constructor
   ·rintro ⟨hxy,(⟨hx,hy⟩|⟨hx,hy⟩)⟩
    ·exact bk.mpr ⟨(x,y),G.mem_interedges_iff.mpr ⟨hx,hy,hxy⟩,rfl⟩
    ·exact bk.mpr ⟨(y,x),G.mem_interedges_iff.mpr ⟨hy,hx,hxy.symm⟩,bx⟩
   ·rintro h
    obtain ⟨⟨a,b⟩,hab,he⟩:=bk.mp h;obtain ⟨ha,hb,hg⟩:=G.mem_interedges_iff.mp hab;rcases (kc (p:=(a,b)) (q:=(x,y))).mp he with he | he
    ·cases he;exact ⟨hg,Or.inl ⟨ha,hb⟩⟩
    ·cases he;exact ⟨hg.symm,Or.inr ⟨hb,ha⟩⟩
 simp only [cw,heq,nL hinj,rM]
lemma GI {a b:ℕ} (ha:0<a) (hb:0<b):min a b+a*a.log2+b*b.log2<=(a+b)*(a+b).log2:=by
 have hm:Monotone Nat.log2:=by intro m n h;simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b:=2) h)
 have aa4:=hm (show a<=a+b by omega);have aa5:=hm (show b<=a+b by omega);rcases le_total a b with hab | hba
 ·have u7:=hm (show 2*a<=a+b by omega);rw [Nat.log2_two_mul (by omega)] at u7;rw [f9 hab];nlinarith
 ·have u7:=hm (show 2*b<=a+b by omega);rw [Nat.log2_two_mul (by omega)] at u7;rw [min_eq_right hba];nlinarith
lemma GJ {G K G₁ G₂ H₁ H₂:SimpleGraph V}
  {L₁ L₂:List (SimpleGraph V)}
  (hp₁:cj G₁ (H₁::L₁)) (hp₂:cj G₂ (H₂::L₂))
  (e7:∀x y,G.Adj x y↔K.Adj x y\/G₁.Adj x y\/G₂.Adj x y)
  (Ld:Disjoint K G₁) (Lf:Disjoint K G₂) (Qx:Disjoint G₁ G₂):cj G ((K ⊔ H₁ ⊔ H₂)::(L₁++L₂)):=by
 classical
 have hle₁:H₁<=G₁:=sw hp₁ (by simp);have hle₂:H₂<=G₂:=sw hp₂ (by simp);intro x y;have h₁:=hp₁ x y;have h₂:=hp₂ x y;have Ld:=nq.mp Ld x y;have Lf:=nq.mp Lf x y;have Qx:=nq.mp Qx x y;have aak:=@hle₁ x y;have aal:=@hle₂ x y;have hc:=e7 x y;simp only [iW,dV,nv] at *;by_cases hK:K.Adj x y<;>by_cases Oh:G₁.Adj x y<;>by_cases Qr:G₂.Adj x y<;>by_cases aam:H₁.Adj x y<;>by_cases aan:H₂.Adj x y<;>simp_all
lemma Dx {V:Type cP} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V) (A U:Finset V)
  (hG:fW G A) (Zh:U⊆A):(∀x y,G.Adj x y↔(o5 G U (A\U)).Adj x y\/(jR G U).Adj x y\/(jR G (A\U)).Adj x y)/\
  Disjoint (o5 G U (A\U)) (jR G U)/\Disjoint (o5 G U (A\U)) (jR G (A\U))/\Disjoint (jR G U) (jR G (A\U)):=by
 constructor
 ·intro x y;change G.Adj x y↔(G.Adj x y/\_)\/(G.Adj x y/\_)\/(G.Adj x y/\_);have hs:=@hG x y;simp only [aS];tauto
 ·simp only [nq,o5,jR,aS];tauto
lemma Cy {V:Type cL} [aP:Fintype V] [aO:DecidableEq V] {G:SimpleGraph V} {A:Finset V}
  (hG:fW G A) (hA:A.card<=1):G=⊥:=by
 ext x y;constructor
 ·intro h;obtain ⟨hx,hy⟩:=hG h;have hxy:=jK.mp hA x hx y hy;exact False.elim (G.ne_of_adj h hxy)
 ·simp
lemma J9 (G:SimpleGraph V) (A:Finset V)
  (hG:fW G A) (σ:ℝ) (hσ:0<=σ):∃(R:List (aE V)) (H:SimpleGraph V),(∀P∈R,P.vertices⊆A/\2<=P.vertices.card/\b9 P.graph P.vertices σ)/\
   R.Pairwise (λ P Q=>Disjoint P.vertices Q.vertices)/\cj G (H :: R.map aE.graph)/\fW H A/\(cw H:ℝ)<=σ*A.card*A.card.log2:=by
 classical
 induction lN:A.card using jh generalizing A G with
 | h n ih=>
   by_cases iE:A.card<=1
   ·have he:=Cy hG iE
    refine ⟨[],⊥,by simp,by simp,?_,?_,?_⟩
    ·subst G;intro x y;simp
    ·intro x y h;exact False.elim h
    ·simp only [DV,g3];positivity
   by_cases hexp:b9 G A σ
   ·refine ⟨[⟨A,G,hG⟩],⊥,?_,by simp,?_,?_,?_⟩
    ·intro P hP;have he:=jM.mp hP;subst P;exact ⟨λ _ h=>h,by change 2<=A.card;omega,hexp⟩
    ·intro x y;simp
    ·intro x y h;exact False.elim h
    ·simp only [DV,g3];positivity
   unfold b9 at hexp
   push Not at hexp
   obtain ⟨U,hU,ob⟩:=hexp;have OY:Disjoint U (A\U):=aL.mpr
    (λ _ hu hb=>(aS.mp hb).2 hu)
   have aaG:(0:ℝ)<=rM G U (A\U):=aN _;have Zs:0<σ:=by by_contra h;have:σ=0:=le_antisymm (dF h) hσ;rw [this,zero_mul] at ob;linarith
   have Uu:0<U.card:=by
    by_contra h;have hz:U.card=0:=by omega
    simp [hz] at ob;linarith [min_le_left (0:ℝ) ((A\U).card:ℝ)]
   have Uv:0<(A\U).card:=by
    by_contra h;have hz:(A\U).card=0:=by omega
    simp [hz] at ob;linarith [min_le_right (U.card:ℝ) (0:ℝ)]
   have WI:=ni hU;have WJ:U.card<n:=by omega
   have WK:(A\U).card<n:=by omega
   obtain ⟨WL,H₁,Qy,Ld,hp₁,F4,aao⟩:=ih U.card WJ (jR G U) U
    (p8 G U) rfl
   obtain ⟨WM,H₂,Qz,Lf,hp₂,CS,aap⟩:=ih (A\U).card WK (jR G (A\U)) (A\U)
    (p8 G (A\U)) rfl
   let K:=o5 G U (A\U);obtain ⟨e7,Rj,Rk,Rl⟩:=Dx G A U hG hU;refine ⟨WL++WM,K ⊔ H₁ ⊔ H₂,?_,?_,?_,?_,?_⟩
   ·intro P hP
    rcases fQ.mp hP with hP | hP
    ·obtain ⟨Tc,OH,OS⟩:= Qy P hP;exact ⟨Tc.trans hU,OH,OS⟩
    ·obtain ⟨Tc,OH,OS⟩:= Qz P hP;exact ⟨Tc.trans lg,OH,OS⟩
   ·apply List.pairwise_append.mpr
    refine ⟨Ld,Lf,?_⟩;intro P hP Q hQ;exact OY.mono
     (Qy P hP).1 (Qz Q hQ).1
   ·simpa only [gK] using GJ hp₁ hp₂ e7 Rj Rk Rl
   ·intro x y h
    rcases h with (h|h)|h
    ·exact hG h.1
    ·exact ⟨hU (F4 h).1,hU (F4 h).2⟩
    ·exact ⟨(aS.mp (CS h).1).1,(aS.mp (CS h).2).1⟩
   ·have Td:cw K=rM G U (A\U):=J8 G U (A\U) OY
    have jF:(cw (K⊔H₁⊔H₂):ℝ)<=cw K+cw H₁+cw H₂:=by
     exact_mod_cast (vi (K⊔H₁) H₂).trans
      (l5 (vi K H₁) _)
    have Te:=GI Uu Uv;have Uw:min (U.card:ℝ) ((A\U).card:ℝ)+U.card*U.card.log2+(A\U).card*(A\U).card.log2<=(A.card:ℝ)*A.card.log2:=by
     have he:U.card+(A\U).card=A.card:=by omega
     rw [he] at Te;exact_mod_cast Te
    have Oa:=aJ Uw hσ;rw [Td] at jF;rw [<-lN];nlinarith
lemma GK {n:ℕ} (hn:0<n):(n.log2:ℝ)<=Real.logb 2 n:=by apply (Real.le_logb_iff_rpow_le (by norm_num:(1:ℝ)<2) (by exact_mod_cast hn)).mpr;rw [Real.rpow_natCast,Nat.log2_eq_log_two];exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
lemma Cz {V:Type c9} [aP:Fintype V] [aO:DecidableEq V] {G:SimpleGraph V} {A:Finset V} {σ:ℝ}
  (hA:2<=A.card) (he:b9 G A σ):σ+1<=A.card:=by
 classical
 obtain ⟨x,hx⟩:=cT.mp (show 0<A.card by omega);have hsub:{x}⊆A:=singleton_subset_iff.mpr hx;have lN:=ni hsub;simp only [iI] at lN;have hB:(1:ℝ)<=(A\{x}).card:=by exact_mod_cast (show 1<=(A\{x}).card by omega)
 have hc:=he {x} hsub;simp only [iI,gR,f9 hB,mul_one] at hc;have hbound:rM G {x} (A\{x})<=(A\{x}).card:=by simpa only [rM,iI,one_mul] using G.card_interedges_le_mul {x} (A\{x})
 have W0:(rM G {x} (A\{x}):ℝ)<=(A\{x}).card:=by exact_mod_cast hbound
 have heqR:((A\{x}).card:ℝ)+1=A.card:=by exact_mod_cast lN
 linarith
open Filter Asymptotics Real in
lemma Ju:∀ᶠ D:ℝ in atTop,1<=D /\2*D^(9/10:ℝ)*logb 2 (D^(51/50:ℝ))<=D^(19/20:ℝ):=by
 have aaq:0<log 2:=log_pos (by norm_num);have he:=((o8 (by norm_num:(0:ℝ)<1/20)).const_mul_left
  ((51/25:ℝ)/log 2)).eventuallyLE
 filter_upwards [eventually_ge_atTop (1:ℝ),he] with D hD h;have DW:0<D:=by linarith
 have hn:0<=(51/25:ℝ)/log 2*log D:=bZ (by positivity) (nU hD);have hh:(51/25:ℝ)/log 2*log D <=D^(1/20:ℝ):=by simpa only [kg,gk hn,gk (fG DW.le _)] using h
 refine ⟨hD,?_⟩;calc
  2*D^(9/10:ℝ)*logb 2 (D^(51/50:ℝ))=D^(9/10:ℝ)*((51/25:ℝ)/log 2*log D):=by rw [jH DW];simp only [Real.logb];ring
  _<=D^(9/10:ℝ)*D^(1/20:ℝ):=aJ hh (by positivity)
  _=D^(19/20:ℝ):=by rw [<-c8 DW];norm_num
lemma Dy:∃PA:ℝ,∀D≥PA,∀(V:Type u) [Fintype V] [DecidableEq V]
   (G:SimpleGraph V) (A:Finset V),A.Nonempty->fW G A->(A.card:ℝ)<=D^(51/50:ℝ)->
  ∃(R:List (aE V)) (H:SimpleGraph V),(∀P∈R,P.vertices⊆A/\D^(9/10:ℝ)<=P.vertices.card/\(P.vertices.card:ℝ)<=D^(51/50:ℝ)/\b9 P.graph P.vertices (D^(9/10:ℝ)))/\
   R.Pairwise (λ P Q=>Disjoint P.vertices Q.vertices)/\cj G (H :: R.map aE.graph)/\fW H A/\2*(cw H:ℝ)/A.card<=D^(19/20:ℝ):=by
 classical
 obtain ⟨PA,gN⟩:=Filter.eventually_atTop.mp Ju;refine ⟨PA,?_⟩;intro D hD V _ _ G A hA hG hhi;obtain ⟨K7,Mr⟩:=gN D hD;have DW:0<D:=by linarith
 have VM:0<A.card:=cT.mpr hA;have Tf:(0:ℝ)<A.card:=by exact_mod_cast VM
 obtain ⟨R,H,hR,hd,hp,hs,jF⟩:=J9 G A hG (D^(9/10:ℝ)) (by positivity);refine ⟨R,H,?_,hd,hp,hs,?_⟩
 ·intro P hP
  obtain ⟨hsub,u6,hexp⟩:=hR P hP;have hlo:=Cz u6 hexp;have hle:(P.vertices.card:ℝ)<=A.card:=by exact_mod_cast aU hsub
  exact ⟨hsub,by linarith,hle.trans hhi,hexp⟩
 ·have kI:=(GK VM).trans
   (dL (by norm_num:(1:ℝ)<2) Tf hhi)
  have hmul:=aJ kI (show 0<=D^(9/10:ℝ)*(A.card:ℝ) by positivity);have W1:=aY Mr Tf.le;apply (dK Tf).mpr;nlinarith
end af.eF
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe u
universe bX bY cy cz cP cL
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open Finset SimpleGraph Classical Real
variable {V:Type bX} [Fintype V] [DecidableEq V]
lemma qH {I:Type bY} (L:List I)
  (g:I->SimpleGraph V) (f:I->List (SimpleGraph V))
  (h:∀i∈L,cj (g i) (f i)) (x y:V):dw (L.flatMap f) x y=dw (L.map g) x y:=by
 induction L with
 | nil=>simp
 | cons i L ih=>simp only [jN,dV,fB,iW];rw [h i (by simp),ih (λ j hj=>h j (by simp [hj]))]
lemma CB {I:Type cy} {G:SimpleGraph V}
  {C:List (SimpleGraph V)} {L:List I}
  {g:I->SimpleGraph V} {f:I->List (SimpleGraph V)}
  (hp:cj G (C ++ L.map g))
  (h:∀i∈L,cj (g i) (f i)):cj G (C ++ L.flatMap f):=by
 intro x y;simpa only [dV,qH L g f h] using hp x y
lemma MU:∃Aq:ℝ,∀D≥Aq,∀(V:Type u) [Fintype V] [DecidableEq V]
   (G:SimpleGraph V) (A:Finset V),A.Nonempty->fW G A->2*(cw G:ℝ)/A.card<=D ->
  ∃(C:List (SimpleGraph V)) (L:List (aE V))
   (R:aE V->List (aE V))
   (H:aE V->SimpleGraph V),(∀K∈C,lY K/\D^(101/100:ℝ)<=(cw K:ℝ))/\(C.length:ℝ)<=A.card/(2*D^(1/100:ℝ))/\(∀P∈L,P.vertices⊆A/\P.vertices.Nonempty/\(P.vertices.card:ℝ)<=D^(51/50:ℝ))/\
   (∀x∈A,∃P∈L,x∈P.vertices)/\(L.map (λ P=>(P.vertices.card:ℝ))).sum<=(1+2/logb 2 D)*A.card/\(∀P∈L,(∀Q∈R P,Q.vertices⊆P.vertices/\D^(9/10:ℝ)<= Q.vertices.card/\(Q.vertices.card:ℝ)<=D^(51/50:ℝ)/\b9 Q.graph Q.vertices (D^(9/10:ℝ)))/\
    (R P).Pairwise (λ Q T=>Disjoint Q.vertices T.vertices)/\cj P.graph (H P :: (R P).map aE.graph)/\fW (H P) P.vertices/\2*(cw (H P):ℝ)/P.vertices.card<=D^(19/20:ℝ))/\
   cj G (C ++ L.flatMap (λ P=>H P :: (R P).map aE.graph)):=by
 classical
 obtain ⟨D₁,h₁⟩:=MS.{u}
 obtain ⟨D₂,h₂⟩:=Dy.{u}
 refine ⟨max D₁ D₂,?_⟩;intro D hD V _ _ G A hA hs hd;obtain ⟨C,L,hC,Zt,hL,e7,hp,jF⟩:=h₁ D ((b6 _ _).trans hD) V G A hA hs hd;have hres:∀P:aE V,∃(R:List (aE V)) (H:SimpleGraph V),P∈L->(∀Q∈R,Q.vertices⊆P.vertices/\D^(9/10:ℝ)<= Q.vertices.card/\(Q.vertices.card:ℝ)<=D^(51/50:ℝ)/\b9 Q.graph Q.vertices (D^(9/10:ℝ)))/\
    R.Pairwise (λ Q T=>Disjoint Q.vertices T.vertices)/\cj P.graph (H :: R.map aE.graph)/\fW H P.vertices/\2*(cw H:ℝ)/P.vertices.card<=D^(19/20:ℝ):=by
  intro P;by_cases hP:P∈L
  ·obtain ⟨R,H,xx⟩:=h₂ D ((bC _ _).trans hD) V
    P.graph P.vertices (hL P hP).2.1 P.supported (hL P hP).2.2
   exact ⟨R,H,λ _=>xx⟩
  ·exact ⟨[],⊥,λ hp=>False.elim (hP hp)⟩
 choose R H hR using hres;refine ⟨C,L,R,H,hC,Zt,hL,e7,jF,hR,?_⟩;exact CB hp (λ P hP=>(hR P hP).2.2.1)
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Real Filter Finset
open scoped Topology
def jA:ℝ:=19/20
def aT (n:ℝ) (j:ℕ):ℝ:=n^(jA^j)
lemma t8:0<jA:=by norm_num [jA]
lemma yW:jA<1:=by norm_num [jA]
lemma wZ (n:ℝ):aT n 0=n:=by simp [aT]
lemma tP (n:ℝ) (hn:0<n) (j:ℕ):0<aT n j:=d6 hn _
lemma EE (n:ℝ) (hn:0<=n) (j:ℕ):aT n (j+1)=(aT n j)^jA:=by simp only [aT,pow_succ,lz hn]
lemma q4 (n:ℝ) (hn:1<n) (j:ℕ):1<aT n j:=by
 simpa [aT] using Real.rpow_lt_rpow_of_exponent_lt hn
  (pow_pos t8 j)
lemma yX (n:ℝ) (hn:1<=n) (j:ℕ):aT n j<=n:=by have hp:jA^j<=1:=pow_le_one₀ t8.le yW.le;simpa [aT] using g5 hn hp
lemma yb (n:ℝ) (hn:0<n) (j:ℕ):logb 2 (aT n j)=jA^j*logb 2 n:=by exact jH hn
lemma k3 (n:ℝ) (hn:1<n) (j:ℕ):0<logb 2 (aT n j):=by exact g4 (by norm_num) (q4 n hn j)
lemma AT (n:ℝ) (hn:0<n) (j:ℕ):logb 2 (aT n (j+1))=jA*logb 2 (aT n j):=by rw [yb n hn,yb n hn,pow_succ];ring
lemma tQ (n:ℝ) (hn:0<=n) (i K:ℕ):aT n (i+K)=(aT n i)^(jA^K):=by simp only [aT,pow_add,lz hn]
lemma vF:(51/50:ℝ)*jA^200<1/1000/\jA^201<1/1000:=by norm_num [jA]
lemma BO (n:ℝ) (hn:0<n):Tendsto (aT n) atTop (𝓝 1):=by
 have ht:=(Real.continuous_const_rpow (ne_of_gt hn)).tendsto 0;change Tendsto (λ j:ℕ=>n^(jA^j)) atTop (𝓝 1);simpa only [Function.comp_def,Real.rpow_zero] using
  ht.comp (tendsto_pow_atTop_nhds_zero_of_lt_one t8.le yW)
lemma yc (n dO:ℝ) (hD:1<dO) (hn:dO<=n):∃m:ℕ,0< m/\aT n m<dO/\∀j< m,dO<=aT n j:=by
 have hn0:0<n:=lt_trans (by norm_num) (hD.trans_le hn);have he:∀ᶠ j in atTop,aT n j<dO:=(BO n hn0).eventually (gt_mem_nhds hD);have hex:∃j,aT n j<dO:=he.exists;refine ⟨Nat.find hex,?_,Nat.find_spec hex,?_⟩
 ·by_contra hm
  have hz:Nat.find hex=0:=by omega
  have:=Nat.find_spec hex;rw [hz,wZ] at this;linarith
 ·intro j hj;exact dF (Nat.find_min hex hj)
lemma tT (n:ℝ) (hn:1<n) (j:ℕ):(∑l∈range (j+1),1/logb 2 (aT n l))<=20/logb 2 (aT n j):=by
 induction j with
 | zero=>simp only [zero_add,nw,sum_range_zero,zero_add];exact e5 (by norm_num) (k3 n hn 0).le
 | succ j ih=>
   rw [nw];have hb:(∑x∈range (j+1),1/logb 2 (aT n x))+1/logb 2 (aT n (j+1))<=20/logb 2 (aT n j)+1/logb 2 (aT n (j+1)):=by linarith [ih]
   apply hb.trans_eq;rw [AT n (by linarith)];have hz:logb 2 (aT n j)≠0:=ne_of_gt (k3 n hn j);dsimp [jA];field_simp
   ;ring
lemma Dz {x:ℝ} (hx:0<=x) (Zu:x<=1/2):exp x<=1+2*x:=by apply (Real.exp_bound_div_one_sub_of_interval hx (by linarith)).trans;apply (dK (by linarith:0<1-x)).mpr;nlinarith
lemma vG (n C₀:ℝ) (hn:1<n) (hC:0<=C₀) (j:ℕ)
  (ob:40*C₀<=logb 2 (aT n j)):(∏l∈Finset.range (j+1),(1+C₀/logb 2 (aT n l)))<=1+40*C₀/logb 2 (aT n j):=by
 have hL:=k3 n hn j;have hsum:(∑l∈Finset.range (j+1),C₀/logb 2 (aT n l))<=20*C₀/logb 2 (aT n j):=by
  have hh:=aJ (tT n hn j) hC;calc
   _<=C₀*(20/logb 2 (aT n j)):=by simpa only [dR,mul_one_div] using hh
   _=_:=by ring
 calc
  _<=∏l∈Finset.range (j+1),exp (C₀/logb 2 (aT n l)):=by
   apply Finset.prod_le_prod
   ·intro l hl;have:=fF hC (k3 n hn l).le;linarith
   ·intro l hl;simpa [add_comm] using Real.add_one_le_exp (C₀/logb 2 (aT n l))
  _=exp (∑l∈Finset.range (j+1),C₀/logb 2 (aT n l)):=(Real.exp_sum _ _).symm
  _<=exp (20*C₀/logb 2 (aT n j)):=Real.exp_le_exp.mpr hsum
  _<=1+2*(20*C₀/logb 2 (aT n j)):=by apply Dz (fF (by positivity) hL.le);apply (dK hL).mpr;linarith
  _=_:=by ring
lemma AU (n:ℝ) (hn:1<n) (j:ℕ) (A:ℕ->ℝ)
  (hA:∀l∈range (j+1),A l<=2*n)
  (Mr:∀l∈range (j+1),1/(aT n l)^(1/100:ℝ)<=1/logb 2 (aT n l)):
  (∑l∈range (j+1),A l/(2*(aT n l)^(1/100:ℝ)))<=20*n/logb 2 (aT n j):=by
 have hn0:0<n:=by linarith
 calc
  _<=∑l∈range (j+1),n*(1/logb 2 (aT n l)):=by
   apply aK;intro l hl;have hp:0<(aT n l)^(1/100:ℝ):=d6 (tP n hn0 l) _;calc
    _<=2*n/(2*(aT n l)^(1/100:ℝ)):=e5 (hA l hl) (by positivity)
    _=n*(1/(aT n l)^(1/100:ℝ)):=by ring
    _<=_:=aJ (Mr l hl) hn0.le
  _=n*(∑l∈range (j+1),1/logb 2 (aT n l)):=(dR _ _ _).symm
  _<=n*(20/logb 2 (aT n j)):=aJ (tT n hn j) hn0.le
  _=_:=by ring
end
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
structure cO (P:aE V) where
 cycles:List (SimpleGraph V)
 boxes:List (aE V)
 lD:aE V->List (aE V)
 remainder:aE V->SimpleGraph V
 xE:∀K∈cycles,lY K
 rO:∀B∈boxes,B.vertices⊆P.vertices
 wG:P.vertices.Nonempty->∀B∈boxes,B.vertices.Nonempty
 Fy:∀v∈P.vertices,∃B∈boxes,v∈B.vertices
 tU:∀B∈boxes,∀R∈lD B,R.vertices⊆B.vertices
 t9:∀B∈boxes,(lD B).Pairwise λ R S=>Disjoint R.vertices S.vertices
 oi:∀B∈boxes,fW (remainder B) B.vertices
 r5:∀B∈boxes,cj B.graph (remainder B :: (lD B).map aE.graph)
 partition:cj P.graph (cycles ++ boxes.map aE.graph)
def cO.Bounded {P:aE V} (s:cO P) (D:ℝ):Prop:=(s.cycles.length:ℝ)<=P.vertices.card/(2*D^(1/100:ℝ))/\(s.boxes.map (λ B=>(B.vertices.card:ℝ))).sum<=(1+2/logb 2 D)*P.vertices.card/\(∀B∈s.boxes,(B.vertices.card:ℝ)<=D^(51/50:ℝ))/\(∀B∈s.boxes,∀R∈s.lD B,D^(9/10:ℝ)<=(R.vertices.card:ℝ)/\(R.vertices.card:ℝ)<=D^(51/50:ℝ)/\b9 R.graph R.vertices (D^(9/10:ℝ)))/\
 (∀B∈s.boxes,2*(cw (s.remainder B):ℝ)/B.vertices.card<=D^(19/20:ℝ))
def cO.trivial (P:aE V):cO P where
 cycles:=[]
 boxes:=[P]
 lD:=λ _=>[]
 remainder:=aE.graph
 xE:=by simp
 rO:=by simp
 wG:=by simp
 Fy:=by intro v hv;exact ⟨P,by simp,hv⟩
 tU:=by simp
 t9:=by simp
 oi:=λ B _=>B.supported
 r5:=by intro B _ x y;simp
 partition:=by intro x y;simp
lemma Ka:∃Aq:ℝ,∀(V:Type) [Fintype V] [DecidableEq V],∃split:∀(abk:ℝ) (P:aE V),cO P,∀D≥Aq,∀P,P.vertices.Nonempty->2*(cw P.graph:ℝ)/P.vertices.card<=D ->(split D P).Bounded D:=by
 obtain ⟨Aq,GU⟩:=MU;refine ⟨Aq,?_⟩;intro V _ _;have hex (D:ℝ) (P:aE V):∃s:cO P,Aq<=D ->P.vertices.Nonempty->2*(cw P.graph:ℝ)/P.vertices.card<=D ->s.Bounded D:=by
  by_cases h:Aq<=D /\P.vertices.Nonempty/\2*(cw P.graph:ℝ)/P.vertices.card<=D
  ·obtain ⟨C,L,R,H,hC,Zv,hL,e7,uO,hR,hpart⟩:=GU D h.1 V P.graph P.vertices h.2.1 P.supported h.2.2
   have Tg:cj P.graph (C ++ L.map aE.graph):=by
    intro x y;rw [dV,<-qH L aE.graph
     (λ B=>H B :: (R B).map aE.graph) (λ B hB=>(hR B hB).2.2.1)]
    simpa only [dV] using hpart x y
   let s:cO P:={
    cycles:=C,boxes:=L,lD:=R,remainder:=H
    xE:=λ K hK=>(hC K hK).1
    rO:=λ B hB=>(hL B hB).1
    wG:=λ _ B hB=>(hL B hB).2.1
    Fy:=e7
    tU:=λ B hB Q hQ=>(hR B hB).1 Q hQ |>.1
    t9:=λ B hB=>(hR B hB).2.1
    oi:=λ B hB=>(hR B hB).2.2.2.1
    r5:=λ B hB=>(hR B hB).2.2.1
    partition:=Tg}
   refine ⟨s,λ _ _ _=>⟨Zv,uO,λ B hB=>(hL B hB).2.2,?_,?_⟩⟩
   ·exact λ B hB Q hQ=>(hR B hB).1 Q hQ |>.2
   ·exact λ B hB=>(hR B hB).2.2.2.2
  ·exact ⟨cO.trivial P,λ hD hP hdeg=>False.elim (h ⟨hD,hP,hdeg⟩)⟩
 choose s hs using hex;exact ⟨s,λ D hD P hP hdeg=>hs D P hD hP hdeg⟩
def cO.children {P:aE V} (s:cO P):List (aE V):=s.boxes.pmap (λ B hB=>⟨B.vertices,s.remainder B,s.oi B hB⟩) (λ _ h=>h)
lemma cO.Mt {V:Type} [aP:Fintype V] [aO:DecidableEq V] {P:aE V} (s:cO P) (Q:aE V):Q∈s.children↔∃B∈s.boxes,Q.vertices=B.vertices/\Q.graph=s.remainder B:=by
 simp only [cO.children,List.mem_pmap];constructor
 ·rintro ⟨B,hB,rfl⟩;exact ⟨B,hB,rfl,rfl⟩
 ·rintro ⟨B,hB,hv,hg⟩;refine ⟨B,hB,?_⟩;cases Q;cases B;simp_all
lemma cO.Fz {V:Type} [aP:Fintype V] [aO:DecidableEq V] {P:aE V} (s:cO P)
  {α:Type cz} (f:Finset V->SimpleGraph V->α):s.children.map (λ Q=>f Q.vertices Q.graph)=s.boxes.map (λ B=>f B.vertices (s.remainder B)):=by
 unfold cO.children;rw [List.map_pmap];change List.pmap (λ B (_:B∈s.boxes)=>f B.vertices (s.remainder B)) s.boxes _=_;exact List.pmap_eq_map (λ B (h:B∈s.boxes)=>h)
lemma CF {V:Type} [aP:Fintype V] [aO:DecidableEq V] (L:List (Finset V)) (A:Finset V)
  (hd:L.Pairwise Disjoint) (hA:∀B∈L,B⊆A):(L.map card).sum<=A.card:=by
 induction L generalizing A with
 | nil=>simp
 | cons B L ih=>
   obtain ⟨Zw,hd⟩:=iu.mp hd;have VN:=hA B (by simp);have Zx:∀C∈L,C⊆A\B:=by intro C hC v hv;exact aS.mpr ⟨hA C (by simp [hC]) hv,λ hb=>aL.mp (Zw C hC) hb hv⟩
   have hh:=ih (A\B) hd Zx;have hc:=l6 VN;have W2:=aU VN;simp only [fB,iw];omega
def bF (L:List (aE V)):ℝ:=(L.map (λ P=>(P.vertices.card:ℝ))).sum
lemma qP {V:Type} [aP:Fintype V] [aO:DecidableEq V] (L:List (aE V)):0<=bF L:=List.sum_nonneg (λ x hx=>by obtain ⟨P,_,rfl⟩:=bV.mp hx;positivity)
@[simp] lemma xo {V:Type} [aP:Fintype V] [aO:DecidableEq V] :bF ([] :List (aE V))=0:=rfl
@[simp] lemma n8 {V:Type} [aP:Fintype V] [aO:DecidableEq V] (P:aE V) (L):bF (P::L)=P.vertices.card+bF L:=rfl
@[simp] lemma qQ {V:Type} [aP:Fintype V] [aO:DecidableEq V] (L M:List (aE V)):bF (L++M)=bF L+bF M:=by simp [bF]
lemma j3 {I:Type cP} (L:List I) (f:I->List (aE V)):bF (L.flatMap f)=(L.map (λ i=>bF (f i))).sum:=by
 induction L with
 | nil=>simp
 | cons i L ih=>simp [ih]
lemma cO.yL {P:aE V} (s:cO P):bF s.children=bF s.boxes:=by unfold bF;rw [s.Fz (λ A _=>(A.card:ℝ))]
lemma cO.MV {P:aE V} (s:cO P) {B:aE V}
  (hB:B∈s.boxes):bF (s.lD B)<=B.vertices.card:=by
 have hh:=CF ((s.lD B).map aE.vertices) B.vertices
  (m7.mpr (s.t9 B hB)) (by intro A hA;obtain ⟨Q,hQ,rfl⟩:=bV.mp hA;exact s.tU B hB Q hQ)
 simpa [bF,jn,Function.comp_def] using (cq.mpr hh:(_:ℝ)<=_)
end
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
abbrev cv (V:Type) [Fintype V] [DecidableEq V] :=ℕ->(P:aE V)->cO P
def jC (s:cv V) (j:ℕ) (L:List (aE V)):List (aE V):=L.flatMap λ P=>(s j P).children
def advance (s:cv V) (j:ℕ):ℕ->List (aE V)->List (aE V)
 | 0,L=>L
 | k+1,L=>jC s (j+k) (advance s j k L)
@[simp] lemma tV (s:cv V) (j) (L):advance s j 0 L=L:=rfl
@[simp] lemma lK (s:cv V) (j k) (L):advance s j (k+1) L=jC s (j+k) (advance s j k L):=rfl
lemma uZ (s:cv V) (j k l) (L):advance s j (k+l) L=advance s (j+k) l (advance s j k L):=by
 induction l with
 | zero=>simp
 | succ l ih=>simp only [Nat.add_succ,lK,ih,Nat.add_assoc]
lemma s6 (s:cv V) (j k) {I:Type cL}
  (L:List I) (f:I->List (aE V)):advance s j k (L.flatMap f)=L.flatMap (λ i=>advance s j k (f i)):=by
 induction k with
 | zero=>rfl
 | succ k ih=>simp only [lK,jC,ih,List.flatMap_assoc]
lemma oa (s:cv V) (j) (L) (Q:aE V):Q∈jC s j L↔∃P∈L,∃B∈(s j P).boxes,Q.vertices=B.vertices/\Q.graph=(s j P).remainder B:=by simp only [jC,kV,cO.Mt]
lemma CI (s:cv V) (j k) (L) (A:Finset V)
  (hA:∀P∈L,P.vertices⊆A):∀Q∈advance s j k L,Q.vertices⊆A:=by
 induction k with
 | zero=>exact hA
 | succ k ih=>intro Q hQ;obtain ⟨P,hP,B,hB,hv,_⟩:=(oa s (j+k) _ Q).mp hQ;rw [hv];exact ((s (j+k) P).rO B hB).trans (ih P hP)
lemma pN (s:cv V) (j k) (L)
  (hL:∀P∈L,P.vertices.Nonempty):∀Q∈advance s j k L,Q.vertices.Nonempty:=by
 induction k with
 | zero=>exact hL
 | succ k ih=>intro Q hQ;obtain ⟨P,hP,B,hB,hv,_⟩:=(oa s (j+k) _ Q).mp hQ;rw [hv];exact (s (j+k) P).wG (ih P hP) B hB
lemma DX (s:cv V) (j k) (L) (P:aE V) (hP:P∈L)
  (v:V) (hv:v∈P.vertices):∃Q∈advance s j k L,v∈Q.vertices:=by
 induction k with
 | zero=>exact ⟨P,hP,hv⟩
 | succ k ih=>obtain ⟨Q,hQ,OD⟩:=ih;obtain ⟨B,hB,Zy⟩:=(s (j+k) Q).Fy v OD;let T:aE V:=⟨B.vertices,(s (j+k) Q).remainder B,(s (j+k) Q).oi B hB⟩;exact ⟨T,(oa s (j+k) _ T).mpr ⟨Q,hQ,B,hB,rfl,rfl⟩,Zy⟩
lemma Kb {V:Type} [aP:Fintype V] [aO:DecidableEq V] (L:List (aE V)) (v:V):v∈L.foldr (λ (P:aE V) (U:Finset V)=>P.vertices∪U) ∅↔∃P∈L,v∈P.vertices:=by
 induction L with
 | nil=>simp
 | cons P L ih=>simp only [List.foldr_cons,gQ,ih,dd];aesop
lemma Jv {V:Type} [aP:Fintype V] [aO:DecidableEq V] (L:List (aE V)):((L.foldr (λ (P:aE V) (U:Finset V)=>P.vertices∪U) ∅).card:ℝ)<=bF L:=by
 induction L with
 | nil=>simp
 | cons P L ih=>
   simp only [List.foldr_cons,n8];have hc:=dG P.vertices (L.foldr (λ (P:aE V) (U:Finset V)=>P.vertices∪U) ∅);have hc':((P.vertices∪L.foldr (λ (P:aE V) (U:Finset V)=>P.vertices∪U) ∅).card:ℝ)<=P.vertices.card+(L.foldr (λ (P:aE V) (U:Finset V)=>P.vertices∪U) ∅).card:=by exact_mod_cast hc
   linarith
lemma FF (L:List (aE V)) (A:Finset V)
  (e7:∀v∈A,∃P∈L,v∈P.vertices):(A.card:ℝ)<=bF L:=by
 have hsub:A⊆L.foldr (λ (P:aE V) (U:Finset V)=>P.vertices∪U) ∅:=λ v hv=>(Kb L v).mpr (e7 v hv)
 exact (cq.mpr (aU hsub)).trans (Jv L)
lemma FH (s:cv V) (j k) (P:aE V):(P.vertices.card:ℝ)<=bF (advance s j k [P]):=FF _ _ (λ v hv=>DX s j k [P] P (by simp) v hv)
lemma DA (s:cv V) (j) (L:List (aE V)) (D:ℝ)
  (hb:∀P∈L,(s j P).Bounded D):bF (jC s j L)<=(1+2/logb 2 D)*bF L:=by
 induction L with
 | nil=>simp [jC]
 | cons P L ih=>have hP:=(hb P (by simp)).2.1;have hL:=ih (λ Q hQ=>hb Q (by simp [hQ]));simp only [jC,jN,qQ,cO.yL,n8] at hL ⊢;change bF (s j P).boxes<=_ at hP;nlinarith
lemma DY (s:cv V) (n dO:ℝ) (hn:0<=n)
  (hs:∀l P,dO<=aT n l->P.vertices.Nonempty->2*(cw P.graph:ℝ)/P.vertices.card<=aT n l->(s l P).Bounded (aT n l))
  (j k:ℕ) (L:List (aE V))
  (hL:∀P∈L,P.vertices.Nonempty)
  (hdeg:∀P∈L,2*(cw P.graph:ℝ)/P.vertices.card<=aT n j)
  (ob:∀l,j<=l->l<j+k->dO<=aT n l):∀P∈advance s j k L,2*(cw P.graph:ℝ)/P.vertices.card<=aT n (j+k):=by
 induction k with
 | zero=>simpa using hdeg
 | succ k ih=>
   intro Q hQ;obtain ⟨P,hP,B,hB,hv,hg⟩:=(oa s (j+k) _ Q).mp hQ;have Uz:=ih (λ l Th hl=>ob l Th (by omega)) P hP;have hb:=hs (j+k) P (ob (j+k) (by omega) (by omega))
    (pN s j k L hL P hP) Uz
   rw [hv,hg,show j+(k+1)=(j+k)+1 by omega,EE n hn];exact hb.2.2.2.2 B hB
lemma Jw (s:cv V) (n dO:ℝ) (hn:0<=n)
  (hs:∀l P,dO<=aT n l->P.vertices.Nonempty->2*(cw P.graph:ℝ)/P.vertices.card<=aT n l->(s l P).Bounded (aT n l))
  (j k:ℕ) (L:List (aE V))
  (hL:∀P∈L,P.vertices.Nonempty)
  (hdeg:∀P∈L,2*(cw P.graph:ℝ)/P.vertices.card<=aT n j)
  (ob:∀l,j<=l->l<=j+k->dO<=aT n l):∀P∈advance s j k L,(s (j+k) P).Bounded (aT n (j+k)):=by
 intro P hP;exact hs (j+k) P (ob _ (by omega) (by omega)) (pN s j k L hL P hP)
  (DY s n dO hn hs j k L hL hdeg (λ l Th hl=>ob l Th (by omega)) P hP)
lemma rB (s:cv V) (n:ℝ) (hn:1<n)
  (j k:ℕ) (L:List (aE V))
  (hb:∀l<k,∀P∈advance s j l L,(s (j+l) P).Bounded (aT n (j+l))):bF (advance s j k L)<=bF L*∏l∈range (j+k),(1+2/logb 2 (aT n l)):=by
 have Tj (l):1<=1+2/logb 2 (aT n l):=by have:=fF (by norm_num:(0:ℝ)<=2) (k3 n hn l).le;linarith
 induction k with
 | zero=>simp only [tV,jo];exact le_mul_of_one_le_right (qP L) (one_le_prod (λ l _=>Tj l))
 | succ k ih=>
   have hm:=DA s (j+k) (advance s j k L) (aT n (j+k))
    (hb k (by omega))
   have hi:=aJ (ih (λ l hl=>hb l (by omega))) ((Tj (j+k)).trans' (by norm_num:(0:ℝ)<=1));rw [lK,show j+(k+1)=(j+k)+1 by omega,prod_range_succ];calc
    _<=(1+2/logb 2 (aT n (j+k)))*bF (advance s j k L):=hm
    _<=_:=by nlinarith only [hi]
end
end af.eF
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
def f5 (L:List (SimpleGraph V)):SimpleGraph V:=L.foldr (· ⊔ ·) ⊥
@[simp] lemma Rm {V:Type} [aP:Fintype V] [aO:DecidableEq V] :f5 ([] :List (SimpleGraph V))=⊥:=rfl
@[simp] lemma Be {V:Type} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V) (L):f5 (G::L)=G ⊔ f5 L:=rfl
lemma nK {V:Type} [aP:Fintype V] [aO:DecidableEq V] (L:List (SimpleGraph V)) (x y:V):(f5 L).Adj x y↔∃G∈L,G.Adj x y:=by
 induction L with
 | nil=>simp
 | cons G L ih=>simp only [Be,nv,ih,dd];aesop
lemma sB (L:List (SimpleGraph V)) (x y:V):0<dw L x y↔(f5 L).Adj x y:=by simp [dw,List.countP_pos_iff,nK]
lemma DB {G:SimpleGraph V} {L:List (SimpleGraph V)}
  (h:cj G L):f5 L=G:=by
 ext x y;rw [<-sB,h x y];split_ifs<;>simp_all
lemma pO (L:List (SimpleGraph V))
  (h:∀x y,dw L x y<=1):cj (f5 L) L:=by
 intro x y;have hh:=h x y;rw [<-sB];split_ifs<;>omega
lemma AV {V:Type} [aP:Fintype V] [aO:DecidableEq V] {L M:List (SimpleGraph V)} (h:L.Sublist M) (x y:V):dw L x y<=dw M x y:=by exact List.Sublist.countP_le h
lemma BP {G:SimpleGraph V} {L M:List (SimpleGraph V)}
  (hp:cj G M) (h:L.Sublist M):cj (f5 L) L:=by
 apply pO;intro x y;have hh:=AV h x y;rw [hp x y] at hh;split_ifs at hh<;>omega
lemma FI {L M:List (SimpleGraph V)} (h:L.Sublist M):f5 L<=f5 M:=by intro x y hxy;obtain ⟨G,hG,hxy⟩:=(nK _ _ _).mp hxy;exact (nK _ _ _).mpr ⟨G,h.subset hG,hxy⟩
lemma GM (L M:List (SimpleGraph V)):f5 (L++M)=f5 L ⊔ f5 M:=by ext x y;simp only [nK,fQ,nv];aesop
lemma FJ (L:List (SimpleGraph V)):cw (f5 L)<=(L.map cw).sum:=by
 induction L with
 | nil=>simp
 | cons G L ih=>simp only [Be,fB,iw];exact (vi G (f5 L)).trans (Nat.add_le_add_left ih _)
def lZ (s:cv V) (j:ℕ) (L:List (aE V)):List (SimpleGraph V):=L.flatMap λ P=>(s j P).cycles
def i3 (s:cv V) (j:ℕ) (L:List (aE V)):List (aE V):=L.flatMap λ P=>(s j P).boxes.flatMap (s j P).lD
lemma cO.Tk {P:aE V} (s:cO P) (x y:V):dw (s.cycles ++ (s.boxes.flatMap s.lD).map aE.graph ++
   s.children.map aE.graph) x y=if P.graph.Adj x y then 1 else 0:=by
 have h:=s.partition x y;rw [dV] at h;rw [<-qH s.boxes aE.graph
  (λ B=>s.remainder B :: (s.lD B).map aE.graph) s.r5] at h
 have he:dw (s.boxes.flatMap (λ B=>s.remainder B ::
   (s.lD B).map aE.graph)) x y=dw ((s.boxes.flatMap s.lD).map aE.graph) x y+dw (s.children.map aE.graph) x y:=by
  rw [s.Fz (λ _ G=>G)];induction s.boxes with
  | nil=>simp
  | cons B L ih=>simp only [jN,gK,fB,dV,iW] at *;omega
 rw [he] at h;simpa only [dV,Nat.add_assoc] using h
lemma Mu (s:cv V) (j) (L:List (aE V)) (x y:V):dw (lZ s j L ++ (i3 s j L).map aE.graph ++
   (jC s j L).map aE.graph) x y=dw (L.map aE.graph) x y:=by
 induction L with
 | nil=>simp [lZ,i3,jC]
 | cons P L ih=>have hp:=(s j P).Tk x y;simp only [lZ,i3,jC,jN,gK,fB,dV,iW] at ih hp ⊢;omega
def eu (s:cv V) (j:ℕ):ℕ->List (aE V)->List (SimpleGraph V)
 | 0,_=>[]
 | k+1,L=>eu s j k L ++ lZ s (j+k) (advance s j k L)
def cJ (s:cv V) (j:ℕ):ℕ->List (aE V)->List (aE V)
 | 0,_=>[]
 | k+1,L=>cJ s j k L ++ i3 s (j+k) (advance s j k L)
lemma MW (s:cv V) (j k) (L:List (aE V)) (x y:V):dw (eu s j k L ++ (cJ s j k L).map aE.graph ++
   (advance s j k L).map aE.graph) x y=dw (L.map aE.graph) x y:=by
 induction k with
 | zero=>simp [eu,cJ]
 | succ k ih=>have h:=Mu s (j+k) (advance s j k L) x y;simp only [eu,cJ,lK,gK,dV] at ih h ⊢;omega
lemma ud (s:cv V) (j k) (P:aE V):cj P.graph (eu s j k [P] ++ (cJ s j k [P]).map aE.graph ++
   (advance s j k [P]).map aE.graph):=by
 intro x y;rw [MW];simp
lemma Ia (s:cv V) (j) (L:List (aE V)):∀G∈lZ s j L,lY G:=by intro G hG;obtain ⟨P,_,hG⟩:=kV.mp hG;exact (s j P).xE G hG
lemma Bf (s:cv V) (j k) (L:List (aE V)):∀G∈eu s j k L,lY G:=by
 induction k with
 | zero=>simp [eu]
 | succ k ih=>
   intro G hG;rcases fQ.mp hG with h | h
   ·exact ih G h
   ·exact Ia s (j+k) _ G h
lemma Ib (s:cv V) (j) (L:List (aE V)):bF (i3 s j L)<=bF (jC s j L):=by
 induction L with
 | nil=>simp [i3,jC]
 | cons P L ih=>
   have hs:bF ((s j P).boxes.flatMap (s j P).lD)<=bF (s j P).boxes:=by rw [j3];unfold bF;exact kU (λ B hB=>(s j P).MV hB)
   simp only [i3,jC,jN,qQ,cO.yL] at ih ⊢;linarith
lemma FK (s:cv V) (j) (L:List (aE V)) (D:ℝ)
  (hb:∀P∈L,(s j P).Bounded D):((lZ s j L).length:ℝ)<=bF L/(2*D^(1/100:ℝ)):=by
 induction L with
 | nil=>simp [lZ]
 | cons P L ih=>have hp:=(hb P (by simp)).1;have hl:=ih (λ Q hQ=>hb Q (by simp [hQ]));simp only [lZ,jN,ng,fP,n8];rw [add_div];exact dS hp hl
lemma Jx (s:cv V) (j k) (L:List (aE V)):bF (cJ s j k L)=∑l∈range k,bF (i3 s (j+l) (advance s j l L)):=by
 induction k with
 | zero=>simp [cJ]
 | succ k ih=>simp [cJ,ih,nw]
lemma GN (s:cv V) (j k) (L:List (aE V)):((eu s j k L).length:ℝ)=∑l∈range k,((lZ s (j+l) (advance s j l L)).length:ℝ):=by
 induction k with
 | zero=>simp [eu]
 | succ k ih=>simp [eu,ih,nw]
end
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph
end
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
end
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
end
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open SimpleGraph Finset
local instance (p:Prop):Decidable p:=Classical.propDecidable p
end
end af.eF
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
lemma o7 {A:Type bX} {R:A->A->Prop} {L:List A}
  (h:L.Pairwise R) (hs:(∀⦃left right⦄,R left right->R right left)):Pairwise λ i j:Fin L.length=>R (L.get i) (L.get j):=by
 intro i j hij;rcases lt_or_gt_of_ne (show i.val≠j.val from λ he=>hij (Fin.ext he)) with hlt | hgt
 ·exact oV.mp h i.val j.val i.isLt j.isLt hlt
 ·exact hs (oV.mp h j.val i.val j.isLt i.isLt hgt)
lemma wH {A:Type bY} {M:Type cy} [AddCommMonoid M] (L:List A) (f:A->M):(∑i:Fin L.length,f (L.get i))=(L.map f).sum:=by
 rw [<-List.sum_ofFn];calc
  _=(List.map f (List.ofFn L.get)).sum:=by rw [List.map_ofFn];rfl
  _=_:=by rw [List.ofFn_get]
lemma uz {G:SimpleGraph V} {L:List (SimpleGraph V)}
  (h:cj G L):L.Pairwise λ H K=>Disjoint H.edgeSet K.edgeSet:=by
 induction L generalizing G with
 | nil=>simp
 | cons H L ih=>
   apply iu.mpr;refine ⟨?_,ih (BP h (List.sublist_cons_self _ _))⟩;intro K hK;apply aI.mpr;intro e he he';induction e using bJ with
   | _ x y=>
     have hc:=h x y;have hp:0<dw L x y:=by rw [sB,nK];exact ⟨K,hK,he'⟩
     have hxy:H.Adj x y:=he;simp only [iW,hxy,ite_true] at hc;split_ifs at hc<;>omega
lemma Ic (L:List (SimpleGraph V)):(⋃ i:Fin L.length,(L.get i).edgeSet)=(f5 L).edgeSet:=by
 ext e;induction e using bJ with
 | _ x y=>
   simp only [av,ic];rw [nK];constructor
   ·rintro ⟨i,h⟩;exact ⟨_,L.get_mem i,h⟩
   ·rintro ⟨H,hH,h⟩;obtain ⟨i,rfl⟩:=nB.mp hH;exact ⟨i,h⟩
lemma yd {G:SimpleGraph V} {L:List (SimpleGraph V)}
  (h:cj G L):aM G<=(L.map aM).sum:=by
 rw [<-wH L aM];apply vO G (λ i:Fin L.length=>L.get i)
 ·intro i;exact sw h (L.get_mem i)
 ·exact o7 (uz h) (λ _ _ h=>h.symm)
 ·rw [Ic,DB h]
lemma AW {V:Type} [aP:Fintype V] [aO:DecidableEq V] {G:SimpleGraph V} (h:lY G):aM G<=1:=by
 apply pC;have hp:e8 G G.edgeSet:=by obtain ⟨a,p,hp,he⟩:=h;exact Or.inl ⟨a,p,hp,he⟩
 refine ⟨λ _=>G.edgeSet,λ _=>hp,?_,?_⟩
 ·intro i j hij;exact False.elim (hij (Subsingleton.elim i j))
 ·ext e;simp only [av];exact ⟨λ ⟨_,h⟩=>h,λ h=>⟨(0:Fin 1),h⟩⟩
lemma rC {V:Type} [aP:Fintype V] [aO:DecidableEq V] (G:SimpleGraph V):aM G<=cw G:=by have h:=wS G;rw [Nat.card_eq_fintype_card,card_edgeSet] at h;exact h
lemma nI {G:SimpleGraph V} {L:List (SimpleGraph V)}
  (h:cj G L):(aM G:ℝ)<=(L.map (λ H=>(aM H:ℝ))).sum:=by
 have hh:(aM G:ℝ)<=((L.map aM).sum:ℕ):=cq.mpr (yd h);simpa [jn,Function.comp_def] using hh
lemma pQ (L:List (SimpleGraph V))
  (h:∀G∈L,lY G):(L.map (λ H=>(aM H:ℝ))).sum<=L.length:=by
 calc
  _<=(L.map (λ _=>(1:ℝ))).sum:=kU (λ G hG=>by exact_mod_cast AW (h G hG))
  _=_:=by simp
end
end af.eF
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY cy cz cP cL c9 dW eo d7 d8 d9 eO fX gu gX
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.oo
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset
variable {I:Type bX} [DecidableEq I]
def eU (w:I->ℕ) (b:Finset I):ℝ:=∑i∈b,(w i:ℝ)
lemma ye {I:Type bY} [aP:DecidableEq I] (w:I->ℕ) (b:Finset I):0<=eU w b:=by exact sum_nonneg (λ _ _=>aN _)
lemma yM (w:I->ℕ) (A:Finset I) (B:ℝ) (hB:0<B)
  (hw:∀i∈A,(w i:ℝ)<=B/2):∃P:List (Finset I),P.Pairwise Disjoint/\(∀i,i∈A↔∃b∈P,i∈b)/\(∀b∈P,b.Nonempty/\eU w b<=B)/\(∀b∈P.tail,B/2<eU w b)/\(P.map (eU w)).sum=eU w A:=by
 induction A using o9 with
 | empty=>
   refine ⟨[],by simp,?_,by simp,by simp,?_⟩
   ·simp
   ·simp [eU]
 | @insert a A ha ih=>
   obtain ⟨P,hdisj,e7,Oi,Jk,DC⟩:=ih (λ i hi=>hw i (by simp [hi]));have aa6:=hw a (by simp);have Tl:∀b∈P,a∉b:=by intro b hb hab;exact ha ((e7 a).mpr ⟨b,hb,hab⟩)
   cases P with
   | nil=>
     have aa7:A=∅:=by apply l7.mpr;intro i hi;simpa using (e7 i).mp hi
     subst A;refine ⟨[{a}],by simp,?_,?_,by simp,?_⟩
     ·intro i;simp
     ·intro b hb;simp only [jM] at hb;subst b;exact ⟨by simp,by simp [eU];linarith⟩
     ·simp
   | cons b bs=>
     have hab:a∉b:=Tl b (by simp);obtain ⟨aaH,aa8⟩:=Oi b (by simp);by_cases Tm:eU w b<=B/2
     ·refine ⟨insert a b :: bs,?_,?_,?_,?_,?_⟩
      ·rw [iu];refine ⟨?_,(iu.mp hdisj).2⟩;intro d hd;exact m9.mpr ⟨Tl d (by simp [hd]),(iu.mp hdisj).1 d hd⟩
      ·intro i
       constructor
       ·intro hia
        rcases bU.mp hia with hia | hi
        ·exact ⟨insert a b,by simp,by simp [hia]⟩
        ·obtain ⟨d,hd,q7⟩:=(e7 i).mp hi
         rcases dd.mp hd with hd | hd
         ·subst d;exact ⟨insert a b,by simp,nC q7⟩
         ·exact ⟨d,by simp [hd],q7⟩
       ·rintro ⟨d,hd,q7⟩
        rcases dd.mp hd with rfl | hd
        ·rcases bU.mp q7 with rfl | Zz
         ·simp
         ·exact nC ((e7 i).mpr ⟨b,by simp,Zz⟩)
        ·exact nC ((e7 i).mpr ⟨d,by simp [hd],q7⟩)
      ·intro d hd
       rcases dd.mp hd with rfl | hd
       ·refine ⟨by simp,?_⟩;simp only [eU,sum_insert hab];change (w a:ℝ)+eU w b<=B;linarith
       ·exact Oi d (by simp [hd])
      ·simpa using Jk
      ·simp only [fB,iw] at DC ⊢
       rw [show eU w (insert a b)=(w a:ℝ)+eU w b by
        simp [eU,hab],show eU w (insert a A)=(w a:ℝ)+eU w A by
        simp [eU,ha]]
       linarith
     ·refine ⟨{a} :: b :: bs,?_,?_,?_,?_,?_⟩
      ·rw [iu];exact ⟨λ d hd=>disjoint_singleton_left.mpr (Tl d hd),hdisj⟩
      ·intro i
       constructor
       ·intro hi
        rcases bU.mp hi with hia | hi
        ·exact ⟨{a},by simp,by simp [hia]⟩
        ·obtain ⟨d,hd,q7⟩:=(e7 i).mp hi;exact ⟨d,List.mem_cons_of_mem _ hd,q7⟩
       ·rintro ⟨d,hd,q7⟩
        rcases dd.mp hd with rfl | hd
        ·exact bU.mpr (Or.inl (gd.mp q7))
        ·exact nC ((e7 i).mpr ⟨d,hd,q7⟩)
      ·intro d hd
       rcases dd.mp hd with rfl | hd
       ·exact ⟨by simp,by simp [eU];linarith⟩
       ·exact Oi d hd
      ·intro d hd
       rcases dd.mp hd with rfl | hd
       ·exact iG Tm
       ·exact Jk d hd
      ·simp only [fB,iw] at DC ⊢;simp only [eU,sum_singleton,sum_insert ha] at DC ⊢;linarith
lemma Jy {I:Type cy} [aP:DecidableEq I] (w:I->ℕ) (P:List (Finset I)) (t:ℝ)
  (ht:∀b∈P,t<=eU w b):(P.length:ℝ)*t<=(P.map (eU w)).sum:=by
 induction P with
 | nil=>simp
 | cons b bs ih=>have hb:=ht b (by simp);have aa9:=ih (λ d hd=>ht d (by simp [hd]));simp only [kT,fP,gR,fB,iw];nlinarith
lemma AX (w:I->ℕ) (A:Finset I) (B:ℝ) (hB:0<B)
  (hw:∀i∈A,(w i:ℝ)<=B/2):∃P:List (Finset I),P.Pairwise Disjoint/\(∀i,i∈A↔∃b∈P,i∈b)/\(∀b∈P,b.Nonempty/\eU w b<=B)/\(P.map (eU w)).sum=eU w A/\(P.length:ℝ)<=1+2*eU w A/B:=by
 obtain ⟨P,hd,hc,hb,ht,hm⟩:=yM w A B hB hw;refine ⟨P,hd,hc,hb,hm,?_⟩;have NU:=Jy w P.tail (B/2) (λ b hb=>(ht b hb).le);cases P with
 | nil=>simp only [List.length_nil,g3];have hh:=fF (bZ (by norm_num:(0:ℝ)<=2) (ye w A)) hB.le;linarith
 | cons b bs=>
   simp only [mC,kT,fP,gR] at NU ⊢;simp only [fB,iw] at hm;have RQ:=ye w b;have aba:(bs.length:ℝ)<=2*eU w A/B:=by apply (e3 hB).mpr;linarith
   linarith
end
end af.oo
namespace af.oo
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open scoped BigOperators
private lemma DZ {V:Type cz} {I:Type cP} [DecidableEq V] [Fintype I]
  (S:Finset V) (W:I->Finset V)
  (h:S⊆univ.biUnion W):S.card<=∑i,(W i).card:=(aU h).trans c5
private lemma wI {V:Type cL} {J:Type c9} [DecidableEq V] [Fintype J]
  (R:J->Finset V) (hR:Pairwise λ i j=>Disjoint (R i) (R j))
  (S:Finset V):(S∩univ.biUnion R).card=∑j,(S∩R j).card:=by
 rw [inter_biUnion];apply j5;intro i _ j _ hij;exact (hR hij).mono ke ke
lemma FL {V:Type dW} {I:Type eo} {J:Type d7} [DecidableEq V]
  [Fintype I] [Fintype J]
  (Y good:Finset V) (W:I->Finset V) (R:J->Finset V)
  (abb:∀i,W i⊆Y) (UA:∀j,R j⊆Y)
  (e7:Y⊆univ.biUnion W)
  (hR:Pairwise λ i j=>Disjoint (R i) (R j))
  (keep:I->J->Prop) [∀i j,Decidable (keep i j)] :let bT:=∑i,∑j,if keep i j then (W i∩R j∩good).card else 0
  let skipped:=∑i,∑j,if keep i j then 0 else (W i∩R j∩good).card
  (∑j,(R j).card)<=bT+skipped+(Y\good).card/\bT+Y.card<=(∑j,(R j).card)+∑i,(W i).card:=by
 classical
 dsimp only;let U:=univ.biUnion R;have hU:U⊆Y:=by intro v hv;obtain ⟨j,_,hj⟩:=bR.mp hv;exact UA j hj
 have lN:U.card=∑j,(R j).card:=by apply j5;intro i _ j _ hij;exact hR hij
 let mass:=∑i,∑j,(W i∩R j∩good).card;let Oj:=∑i,(W i∩U).card;have q2:(∑i,∑j,if keep i j then (W i∩R j∩good).card else 0)+(∑i,∑j,if keep i j then 0 else (W i∩R j∩good).card)=mass:=by dsimp [mass];rw [<-f8];apply cZ rfl;intro i _;rw [<-f8];apply cZ rfl;intro j _;split_ifs<;>omega
 have xx:(U∩good).card<=mass:=by
  have hc:U∩good⊆univ.biUnion (λ i=>W i∩U∩good):=by
   intro v hv;obtain ⟨i,hi,Nh⟩:=bR.mp (e7 (hU (dD.mp hv).1));exact bR.mpr ⟨i,hi,dD.mpr
    ⟨dD.mpr ⟨Nh,(dD.mp hv).1⟩,(dD.mp hv).2⟩⟩
  apply (DZ (U∩good) _ hc).trans;apply le_of_eq;apply cZ rfl;intro i _;have heq:W i∩U∩good=(W i∩good)∩U:=by ext v;simp only [dD];tauto
  rw [heq,wI R hR];apply cZ rfl;intro j _;congr 1;ext v;simp only [dD];tauto
 have td:(U\good).card<=(Y\good).card:=by apply aU;intro v hv;exact aS.mpr ⟨hU (aS.mp hv).1,(aS.mp hv).2⟩
 have DC:mass<=Oj:=by apply aK;intro i _;rw [wI R hR];exact aK λ j _=>aU iF
 have WN:(Y\U).card<=∑i,(W i\U).card:=by apply DZ;intro v hv;obtain ⟨i,hi,Nh⟩:=bR.mp (e7 (aS.mp hv).1);exact bR.mpr ⟨i,hi,aS.mpr ⟨Nh,(aS.mp hv).2⟩⟩
 have hY:U.card+(Y\U).card=Y.card:=by simpa only [inter_eq_right.mpr hU] using oZ Y U
 have F8:Oj+(∑i,(W i\U).card)=∑i,(W i).card:=by dsimp [Oj];rw [<-f8];exact cZ rfl λ i _=>oZ (W i) U
 have ZA:=oZ U good;constructor<;>omega
end
end af.oo
namespace af.oo
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
open aR.af.eF
structure wJ {V:Type} (F:SimpleGraph V) (Y:Finset V) (B T:ℝ) where
 Index:Type
 finite:Fintype Index
 graph:Index->SimpleGraph V
 vertices:Index->Finset V
 Mv:∀i,graph i<=F
 disjoint:Pairwise λ i j=>Disjoint (graph i).edgeSet (graph j).edgeSet
 Jz:(⋃ i,(graph i).edgeSet)=F.edgeSet
 supported:∀i,∀⦃x y⦄,(graph i).Adj x y->x∈vertices i/\y∈vertices i
 subset:∀i,vertices i⊆Y
 FM:Y⊆univ.biUnion vertices
 order_le:∀i,((vertices i).card:ℝ)<=B
 Kc:(∑i,((vertices i).card:ℝ))<=T
 count_le:(card Index:ℝ)<=1+2*T/B
instance wJ.instFinite {V:Type} {F:SimpleGraph V} {Y:Finset V} {B T:ℝ} (c:wJ F Y B T):Fintype c.Index:=c.finite
lemma EG {V I:Type} [Fintype I]
  (F:SimpleGraph V) (Y:Finset V) (H:I->SimpleGraph V) (U:I->Finset V)
  (B8:Pairwise λ i j=>Disjoint (H i).edgeSet (H j).edgeSet)
  (hu:(⋃ i,(H i).edgeSet)=F.edgeSet)
  (hU:∀i,∀⦃x y⦄,(H i).Adj x y->x∈U i/\y∈U i)
  (OZ:∀i,U i⊆Y) (hY:Y⊆univ.biUnion U)
  (B:ℝ) (hB:0<B) (iE:∀i,((U i).card:ℝ)<=B/2):Nonempty (wJ F Y B (∑i,((U i).card:ℝ))):=by
 classical
 obtain ⟨L,QA,ZB,ZC,ZD,UB⟩:=AX (λ i=>(U i).card) univ B hB (λ i _=>iE i);let A:=Fin L.length;let GY (a:A):Finset I:=L.get a;let W (a:A):=(GY a).biUnion U;let J (a:A):SimpleGraph V:=⨆ i∈GY a,H i;have UC:Pairwise λ a b=>Disjoint (GY a) (GY b):=o7 QA (λ _ _ h=>h.symm)
 have Nx (i:I):∃a:A,i∈GY a:=by obtain ⟨b,hb,hi⟩:=(ZB i).mp (mem_univ _);obtain ⟨k,hk⟩:=nB.mp hb;exact ⟨k,by change i∈L.get k;rwa [hk]⟩
 have FN (a:A):(J a).edgeSet=⋃ i∈GY a,(H i).edgeSet:=by
  ext e;induction e using bJ with
  | _ x y=>simp [J,ic,iSup_adj]
 have QB (a:A):(J a).edgeSet⊆F.edgeSet:=by rw [FN,<-hu];exact Set.iUnion₂_subset λ i _=>je (λ j:I=>(H j).edgeSet) i
 have Mw (a:A):((W a).card:ℝ)<=eU (λ i=>(U i).card) (GY a):=by have hh:=c5 (s:=GY a) (t:=U);dsimp only [W,eU];exact_mod_cast hh
 have ZE:Pairwise λ a b=>Disjoint (J a).edgeSet (J b).edgeSet:=by
  intro a b hab;rw [FN,FN];apply aI.mpr;rintro e he he';obtain ⟨i,hi,he⟩:=nD.mp he;obtain ⟨j,hj,he'⟩:=nD.mp he';have hij:i≠j:=by rintro rfl;exact aL.mp (UC hab) hi hj
  exact aI.mp (B8 hij) he he'
 refine ⟨{
  Index:=A
  finite:=inferInstance
  graph:=J
  vertices:=W
  Mv:=λ a=>oW.mp (QB a)
  disjoint:=ZE
  Jz:=?_
  supported:=?_
  subset:=?_
  FM:=?_
  order_le:=?_
  Kc:=?_
  count_le:=?_}⟩
 ·apply mW (gJ QB);intro e he;rw [<-hu] at he;obtain ⟨i,hi⟩:=av.mp he;obtain ⟨a,hia⟩:=Nx i;exact av.mpr ⟨a,by rw [FN];exact nD.mpr ⟨i,hia,hi⟩⟩
 ·intro a x y hxy;have he:s(x,y)∈(J a).edgeSet:=hxy;rw [FN] at he;obtain ⟨i,hi,he⟩:=nD.mp he;exact ⟨bR.mpr ⟨i,hi,(hU i he).1⟩,bR.mpr ⟨i,hi,(hU i he).2⟩⟩
 ·intro a v hv;obtain ⟨i,_,hi⟩:=bR.mp hv;exact OZ i hi
 ·intro v hv;obtain ⟨i,_,hi⟩:=bR.mp (hY hv);obtain ⟨a,ha⟩:=Nx i;exact bR.mpr ⟨a,mem_univ _,bR.mpr ⟨i,ha,hi⟩⟩
 ·intro a;exact (Mw a).trans ((ZC (GY a) (L.get_mem a)).2)
 ·calc
   _<=∑a,eU (λ i=>(U i).card) (GY a):=aK (λ a _=>Mw a)
   _=_:=by rw [wH,ZD];rfl
 ·simpa only [A,dU,eU] using UB
end
end af.oo
namespace af.oo
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
open aR.af.eF
section
open Finset SimpleGraph
local instance (p:Prop):Decidable p:=Classical.propDecidable p
def tW {V:Type} [Fintype V] (F:SimpleGraph V) (Y:Finset V) (a:ℝ):Finset V:=Y.filter λ v=>(F.degree v:ℝ)<=a
lemma zE {V:Type} [Fintype V] (F:SimpleGraph V) (Y:Finset V) (a:ℝ):a*((Y\tW F Y a).card:ℝ)<=2*(F.edgeFinset.card:ℝ):=by
 classical
 let qB:=Y\tW F Y a;have td (v) (hv:v∈qB):a<=(F.degree v:ℝ):=by have hn:=(aS.mp hv).2;exact le_of_lt (iG (λ h=>hn (aD.mpr ⟨(aS.mp hv).1,h⟩)))
 calc
  _=∑v∈qB,a:=by simp [qB,bK]
  _<=∑v∈qB,(F.degree v:ℝ):=aK td
  _<=∑v,(F.degree v:ℝ):=jr (gS _) (by intros;positivity)
  _=_:=by exact_mod_cast F.sum_degrees_eq_twice_card_edges
structure Ar {V R B:Type} [Fintype V] [Fintype R] [Fintype B]
  (F:SimpleGraph V) (Y:Finset V) (W:B->Finset V) (U:R->Finset V) (a L:ℝ) where
 Index:B->Type
 finite:∀b,Fintype (Index b)
 vertices:∀b,Index b->Finset V
 Mx:∀b,Index b->R
 FO:∀b i,vertices b i⊆W b
 D3:∀b i,vertices b i⊆U (Mx b i)
 disjoint:∀b,Pairwise λ i j=>Disjoint (vertices b i) (vertices b j)
 degree_le:∀b i v,v∈vertices b i->(F.degree v:ℝ)<=a
 large:∀b i,L<=((vertices b i).card:ℝ)
 lower:(∑r,((U r).card:ℝ))-((Y\tW F Y a).card:ℝ) -
  L*card B*card R<=∑b,∑i,((vertices b i).card:ℝ)
 upper:(∑b,∑i,((vertices b i).card:ℝ))+Y.card<=(∑r,((U r).card:ℝ))+∑b,((W b).card:ℝ)
instance Ar.instFinite {V R B:Type} [Fintype V] [Fintype R] [Fintype B] {F:SimpleGraph V} {Y:Finset V} {W:B->Finset V} {U:R->Finset V} {a L:ℝ} (c:Ar F Y W U a L) (b:B):Fintype (c.Index b):=c.finite b
lemma DE {V R B:Type} [Fintype V] [Fintype R] [Fintype B]
  (F:SimpleGraph V) (Y:Finset V) (W:B->Finset V) (U:R->Finset V) (a L:ℝ)
  (hL:0<=L) (hW:∀b,W b⊆Y) (hU:∀r,U r⊆Y)
  (wu:Y⊆univ.biUnion W) (VO:Pairwise λ r s=>Disjoint (U r) (U s)):Nonempty (Ar F Y W U a L):=by
 classical
 let good:=tW F Y a;let S (b:B) (r:R):=W b∩U r∩good;let keep (b:B) (r:R):=L<=((S b r).card:ℝ);let I (b:B):={r:R // keep b r};let X (b:B) (i:I b):=S b i.val;have hsum (b:B):(∑i:I b,((X b i).card:ℝ))=∑r,if keep b r then ((S b r).card:ℝ) else 0:=by rw [<-ck];simpa only [subtype_univ] using (sum_subtype_eq_sum_filter (s:=univ) (p:=keep b) (λ r=>((S b r).card:ℝ)))
 have hadd:=FL Y good W U hW hU wu VO keep;dsimp only at hadd;have EK:(∑r,((U r).card:ℝ))<=(∑b,∑r,if keep b r then ((S b r).card:ℝ) else 0)+(∑b,∑r,if keep b r then 0 else ((S b r).card:ℝ))+((Y\good).card:ℝ):=by exact_mod_cast hadd.1
 have QC:(∑b,∑r,if keep b r then ((S b r).card:ℝ) else 0)+Y.card<=(∑r,((U r).card:ℝ))+∑b,((W b).card:ℝ):=by exact_mod_cast hadd.2
 have Lg:(∑b,∑r,if keep b r then 0 else ((S b r).card:ℝ))<=L*card B*card R:=by
  calc
   _<=∑_b:B,∑_r:R,L:=by
    apply aK;intro b _;apply aK;intro r _;split_ifs with hk
    ·exact hL
    ·exact le_of_lt (iG hk)
   _=_:=by simp;ring
 refine ⟨{
  Index:=I
  finite:=λ _=>inferInstance
  vertices:=X
  Mx:=λ _ i=>i.val
  FO:=λ _ _=>iF.trans iF
  D3:=λ _ _=>iF.trans ke
  disjoint:=?_
  degree_le:=?_
  large:=λ _ i=>i.property
  lower:=?_
  upper:=?_}⟩
 ·intro b i j hij
  exact (VO (λ h=>hij (aZ h))).mono
   (iF.trans ke)
   (iF.trans ke)
 ·intro b i v hv;exact (aD.mp (dD.mp hv).2).2
 ·simp_rw [hsum];dsimp only [good] at EK Lg;linarith
 ·simpa only [hsum] using QC
lemma Ie {k:ℕ} (hk:8<=k):(k:ℝ)/3<=(k/2:ℕ):=by
 have h:k<=3*(k/2):=by omega
 have h':(k:ℝ)<=3*(k/2:ℕ):=by exact_mod_cast h
 linarith
end
end af.oo
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset
lemma Ig (S:ℕ->ℝ) (hS:∀j,0<=S j) (K N:ℕ)
  (Df:∀j,N<=j->S j=0) (hne:∃j,0<S j):∃i,0<S i/\∑j∈range (i+K+1),S j<=4*(K+1:ℝ)*S i:=by
 let A:=(range N).filter (λ j=>0<S j);have hA:A.Nonempty:=by obtain ⟨j,hj⟩:=hne;exact ⟨j,by simp only [A,mem_filter,mem_range];exact ⟨by by_contra hn;rw [Df j (by omega)] at hj;linarith,hj⟩⟩
 let i₀:=A.min' hA;have My:i₀∈A:=A.min'_mem hA;have WO:0<S i₀:=(mem_filter.mp My).2;have Lv:(∑j∈range (i₀+1),S j)=S i₀:=by
  apply sum_eq_single i₀
  ·intro j hj GO
   by_contra Tn;have Lh:0<S j:=lt_of_le_of_ne (hS j) (Ne.symm Tn);have B1:j∈A:=by simp only [A,mem_filter,mem_range];refine ⟨?_,Lh⟩;have abd:=(mem_range.mp (mem_filter.mp My).1);have Pt:=mem_range.mp hj;omega
   have JP:i₀<=j:=A.min'_le j B1;have Pt:=mem_range.mp hj;omega
  ·intro hi;exact (hi (by simp)).elim
 let B:=A.filter (λ i=>(∑j∈range (i+1),S j)<=2*(K+1:ℝ)*S i);have hB:B.Nonempty:=by refine ⟨i₀,mem_filter.mpr ⟨My,?_⟩⟩;rw [Lv];have hK:(0:ℝ)<=K:=aN K;nlinarith
 let i:=B.max' hB;have VP:i∈B:=B.max'_mem hB;have ZF:i∈A:=(mem_filter.mp VP).1;have UD:0<S i:=(mem_filter.mp ZF).2;have hinv:(∑j∈range (i+1),S j)<=2*(K+1:ℝ)*S i:=(mem_filter.mp VP).2;refine ⟨i,UD,?_⟩;by_contra ND;have ZG:4*(K+1:ℝ)*S i<∑j∈range (i+K+1),S j:=iG ND;have Ny:2*(K+1:ℝ)*S i<∑j∈Ico (i+1) (i+K+1),S j:=by have q2:=Finset.sum_range_add_sum_Ico S (by omega:i+1<=i+K+1);linarith
 have Ih:(Ico (i+1) (i+K+1)).Nonempty:=by by_contra hh;rw [pG.mp hh] at Ny;simp only [Finset.sum_empty] at Ny;have hK:(0:ℝ)<=K:=aN K;nlinarith
 obtain ⟨j,ZH,Pv⟩:=Finset.exists_max_image (Ico (i+1) (i+K+1)) S Ih;have hsum:(∑l∈Ico (i+1) (i+K+1),S l)<=(K:ℝ)*S j:=by
  calc
   _<=∑_l∈Ico (i+1) (i+K+1),S j:=sum_le_sum Pv
   _=_:=by simp []
 have W3:2*S i<S j:=by have hK:(0:ℝ)<=K:=aN K;nlinarith
 have Lh:0<S j:=by linarith
 have B1:j∈A:=by simp only [A,mem_filter,mem_range];exact ⟨by by_contra abe;rw [Df j (by omega)] at Lh;linarith,Lh⟩
 have WQ:=Finset.mem_Ico.mp ZH;have Ly:(∑l∈Ico (i+1) (j+1),S l)<=(K:ℝ)*S j:=by
  calc
   _<=∑l∈Ico (i+1) (i+K+1),S l:=by
    apply sum_le_sum_of_subset_of_nonneg
    ·intro l hl;simp only [mem_Ico] at hl ⊢;omega
    ·intro l _ _;exact hS l
   _<=_:=hsum
 have UE:(∑l∈range (j+1),S l)<=2*(K+1:ℝ)*S j:=by have q2:=Finset.sum_range_add_sum_Ico S (by omega:i+1<=j+1);have hK:(0:ℝ)<=K:=aN K;nlinarith
 have ZI:j∈B:=mem_filter.mpr ⟨B1,UE⟩;have GO:j<=i:=B.le_max' j ZI;omega
end
end af
end
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
def KW:Prop:=∃C:ℝ,0<C/\∀(n:ℕ) (G:SimpleGraph (Fin n)),∃k:ℕ,e9 G k/\(k:ℝ)<=C*n
end af
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
universe bX bY
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
def cO.rest {P:aE V} (s:cO P) (B:aE V):aE V:=if h:B∈s.boxes then ⟨B.vertices,s.remainder B,s.oi B h⟩ else B
@[simp] lemma cO.u8 {V:Type} [aP:Fintype V] [aO:DecidableEq V] {P:aE V} (s:cO P) (B):(s.rest B).vertices=B.vertices:=by unfold cO.rest;split_ifs<;>rfl
lemma cO.DG {V:Type} [aP:Fintype V] [aO:DecidableEq V] {P:aE V} (s:cO P) {B} (hB:B∈s.boxes):(s.rest B).graph=s.remainder B:=by simp [cO.rest,hB]
lemma cO.rP {V:Type} [aP:Fintype V] [aO:DecidableEq V] {P:aE V} (s:cO P):s.children=s.boxes.map s.rest:=by unfold cO.children;rw [<-List.pmap_eq_map (f:=s.rest) (λ B (hB:B∈s.boxes)=>hB)];apply List.pmap_congr_left;intro B hB;simp [cO.rest,hB]
lemma tZ (s:cv V) (j k) {I:Type bX}
  (L:List I) (f:I->List (aE V)):(cJ s j k (L.flatMap f)).Perm (L.flatMap (λ i=>cJ s j k (f i))):=by
 induction k with
 | zero=>simp [cJ]
 | succ k ih=>simp only [cJ,s6,i3,List.flatMap_assoc];apply (ih.append_right _).trans;exact List.flatMap_append_perm _ _ _
lemma yf (s:cv V) (j k) {I:Type bY}
  (L:List I) (f:I->List (aE V)):(eu s j k (L.flatMap f)).Perm (L.flatMap (λ i=>eu s j k (f i))):=by
 induction k with
 | zero=>simp [eu]
 | succ k ih=>simp only [eu,s6,lZ,List.flatMap_assoc];apply (ih.append_right _).trans;exact List.flatMap_append_perm _ _ _
lemma xq (s:cv V) (j k l) (L:List (aE V)):cJ s j (k+l) L=cJ s j k L ++ cJ s (j+k) l (advance s j k L):=by
 induction l with
 | zero=>simp [cJ]
 | succ l ih=>simp [cJ,ih,uZ,Nat.add_assoc,kS]
lemma CJ (s:cv V) (j k l) (L:List (aE V)):eu s j (k+l) L=eu s j k L ++ eu s (j+k) l (advance s j k L):=by
 induction l with
 | zero=>simp [eu]
 | succ l ih=>simp [eu,ih,uZ,Nat.add_assoc,kS]
lemma Ii (s:cv V) (j k) {L M:List (aE V)}
  (h:∀P∈L,P∈M):∀Q∈advance s j k L,Q∈advance s j k M:=by
 induction k with
 | zero=>exact h
 | succ k ih=>intro Q hQ;obtain ⟨P,hP,B,hB,hv,hg⟩:=(oa s (j+k) _ Q).mp hQ;exact (oa s (j+k) _ Q).mpr ⟨P,ih P hP,B,hB,hv,hg⟩
lemma yY (s:cv V) (i k) (L:List (aE V))
  {P B:aE V} (hP:P∈advance s 0 i L) (hB:B∈(s i P).boxes):∀Q∈advance s (i+1) k [(s i P).rest B],Q∈advance s 0 (i+1+k) L:=by
 rw [uZ,d3];apply Ii;intro Q hQ;simp only [jM] at hQ;subst Q;simp only [lK,d3];apply (oa s i _ _).mpr;exact ⟨P,hP,B,hB,(s i P).u8 B,(s i P).DG hB⟩
lemma MY {B R:aE V} (A:List (aE V))
  (Nz:cj B.graph (R.graph :: A.map aE.graph))
  (s:cv V) (j k:ℕ):cj B.graph
   (eu s j k [R] ++ (cJ s j k [R]).map aE.graph ++
    [f5 ((advance s j k [R]).map aE.graph ++ A.map aE.graph)]):=by
 let L:=(advance s j k [R]).map aE.graph ++ A.map aE.graph;have hL:cj (f5 L) L:=by apply pO;intro x y;have hb:=Nz x y;have hr:=ud s j k R x y;simp only [iW,dV] at hb hr ⊢;dsimp only [L];rw [dV];split_ifs at hb hr<;>omega
 intro x y;have hb:=Nz x y;have hr:=ud s j k R x y;have hl:=hL x y;simp only [iW,dV,Ex,jo] at hb hr hl ⊢;dsimp only [L] at hl;rw [dV] at hl;omega
lemma wL (L:List (aE V)) (c:ℝ)
  (h:∀P∈L,(aM P.graph:ℝ)<=c*P.vertices.card):(L.map (λ P=>(aM P.graph:ℝ))).sum<=c*bF L:=by
 induction L with
 | nil=>simp
 | cons P L ih=>have hp:=h P (by simp);have hl:=ih (λ Q hQ=>h Q (by simp [hQ]));simp only [fB,iw,n8];nlinarith
lemma Ij {B R:aE V} (A:List (aE V))
  (Nz:cj B.graph (R.graph :: A.map aE.graph))
  (s:cv V) (j k:ℕ) (c q:ℝ)
  (hp:∀P∈cJ s j k [R],(aM P.graph:ℝ)<=c*P.vertices.card)
  (hq:(aM (f5 ((advance s j k [R]).map aE.graph ++
   A.map aE.graph)):ℝ)<=q):
  (aM B.graph:ℝ)<=(eu s j k [R]).length+c*bF (cJ s j k [R])+q:=by
 have hh:=nI (MY A Nz s j k);have hc:=pQ (eu s j k [R]) (Bf s j k [R]);have hm:=wL (cJ s j k [R]) c hp;simp only [gK,nj,fB,List.map_nil,iw,List.sum_nil,fq,jn,Function.comp_def] at hh;linarith
end
end af.eF
end
section
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Real Filter
def od:ℝ:=804
def lQ:ℝ:=1/(100*od)
def ug:ℝ:=80/(eF.jA^200)
def xu:ℝ:=ug+4/3
def t3:ℝ:=max (9*od+8) (9*ug)
lemma Bg:0<od:=by norm_num [od]
lemma xG:0<lQ:=by norm_num [lQ,od]
lemma O0:0<ug:=by unfold ug;exact div_pos (by norm_num) (pow_pos eF.t8 _)
lemma JA:0<=xu:=by unfold xu;linarith [O0]
lemma JC:0<=t3:=by unfold t3;exact (by norm_num [od] :(0:ℝ)<=9*od+8).trans (b6 _ _)
structure gz (vj D:ℝ):Prop where
 u0:1<D
 oz:vj<=logb 2 D
 GZ:1/(D^(1/100:ℝ))<=1/logb 2 D
 G0:D^(1/1000:ℝ)<=D^(3/10:ℝ)/2
 KD:2*D^(-9/1000:ℝ)<=1/logb 2 D
 JE:D^(-87/100:ℝ)+4*D^(-3/20:ℝ)<=1/logb 2 D
 FQ:8<=D^(3/100:ℝ)
lemma lR (C ε:ℝ) (hC:0<=C) (hε:0<ε):∀ᶠ D:ℝ in atTop,C*D^(-ε)<=1/logb 2 D:=by
 filter_upwards [aR.af.tq (ε/2) (by positivity),aR.af.ki C (ε/2) ε (by linarith),eventually_gt_atTop (1:ℝ)] with D hl hc hD;have hd:0<D:=by linarith
 have hw:0<logb 2 D:=g4 (by norm_num) hD;have hp:0<D^ε:=d6 hd _;apply (e3 hw).mpr;calc
  _=(C*logb 2 D)/D^ε:=by rw [Real.rpow_neg hd.le];ring
  _<=1:=(kd hp).mpr ((aJ hl hC).trans hc)
lemma AY (vj:ℝ):∃dN:ℝ,1<dN/\∀D≥dN,gz vj D:=by
 have A5:∀ᶠ D:ℝ in atTop,gz vj D:=by
  filter_upwards [eventually_gt_atTop (1:ℝ),(Real.tendsto_logb_atTop (by norm_num:(1:ℝ)<2)).eventually (eventually_ge_atTop vj),lR 1 (1/100) (by norm_num) (by norm_num),aR.af.ki 2 (1/1000) (3/10) (by norm_num),lR 2 (9/1000) (by norm_num) (by norm_num),lR 2 (87/100) (by norm_num) (by norm_num),lR 8 (3/20) (by norm_num) (by norm_num),aR.af.lO 8 (3/100) (by norm_num)] with D hD hw hc hb td F4 CS UF;refine ⟨hD,hw,?_,by linarith,by simpa only [neg_div] using td,?_,UF⟩
  ·simpa only [one_mul,Real.rpow_neg (by linarith:0<=D),one_div] using hc
  ·simp only [neg_div];linarith
 obtain ⟨A,hA⟩:=eventually_atTop.mp A5;refine ⟨max A 2,dZ (by norm_num:(1:ℝ)<2) (bC _ _),?_⟩;intro D hD;exact hA D ((b6 _ _).trans hD)
lemma gz.KX {w D:ℝ} (h:gz w D):(D^(1/100:ℝ))^2<=D^(3/100:ℝ):=by rw [<-lA (by linarith [h.u0] :0<=D)];apply g5 h.u0.le;norm_num
lemma gz.O1 {w D y b:ℝ} (h:gz w D) (hy:0<=y)
  (hb:D^(1/100:ℝ)*b<=2*y*D^(1/1000:ℝ)):b<=y/logb 2 D:=by
 have hd:0<D:=by linarith [h.u0]
 have hp:0<D^(1/100:ℝ):=d6 hd _;calc
  b<=2*y*D^(1/1000:ℝ)/D^(1/100:ℝ):=(e3 hp).mpr (by simpa [bK] using hb)
  _=y*(2*D^(-9/1000:ℝ)):=by
   have he:D^(1/1000:ℝ)/D^(1/100:ℝ)=D^(-9/1000:ℝ):=by rw [<-gT hd];norm_num
   rw [show 2*y*D^(1/1000:ℝ)/D^(1/100:ℝ)=(2*y)*(D^(1/1000:ℝ)/D^(1/100:ℝ)) by ring,he];ring
  _<=y*(1/logb 2 D):=aJ h.KD hy
  _=_:=by ring
lemma gz.Ol {w D y T b r:ℝ} (h:gz w D)
  (hy:0<=y) (abf:0<=b) (hr:0<=r)
  (abg:y<=D^(51/50:ℝ)) (hT:T<=2*y)
  (abh:b<=1+2*T/D^(3/10:ℝ)) (ZJ:D^(9/10:ℝ)*r<=y):D^(3/100:ℝ)*b*r<=y/logb 2 D:=by
 have hd:0<D:=by linarith [h.u0]
 have hB:0<D^(3/10:ℝ):=d6 hd _;have hS:0<D^(9/10:ℝ):=d6 hd _;have hL:0<=D^(3/100:ℝ):=fG hd.le _;have hb':b<=1+4*y/D^(3/10:ℝ):=by have ht:=e5 (by linarith:2*T<=4*y) hB.le;linarith
 have To:r<=y/D^(9/10:ℝ):=(e3 hS).mpr (by simpa [bK] using ZJ);have FZ:D^(3/100:ℝ)/D^(9/10:ℝ)=D^(-87/100:ℝ):=by rw [<-gT hd];norm_num
 have F3:D^(51/50:ℝ)*D^(3/100:ℝ)/(D^(3/10:ℝ)*D^(9/10:ℝ))=D^(-3/20:ℝ):=by rw [<-c8 hd,<-c8 hd,<-gT hd];norm_num
 calc
  _<=D^(3/100:ℝ)*(1+4*y/D^(3/10:ℝ))*(y/D^(9/10:ℝ)):=by gcongr
  _=y*(D^(3/100:ℝ)/D^(9/10:ℝ)+4*y*(D^(3/100:ℝ)/(D^(3/10:ℝ)*D^(9/10:ℝ)))):=by ring
  _<=y*(D^(3/100:ℝ)/D^(9/10:ℝ)+4*D^(51/50:ℝ)*(D^(3/100:ℝ)/(D^(3/10:ℝ)*D^(9/10:ℝ)))):=by gcongr
  _=y*(D^(-87/100:ℝ)+4*D^(-3/20:ℝ)):=by rw [FZ,<-F3];ring
  _<=y*(1/logb 2 D):=aJ h.JE hy
  _=_:=by ring
end
end af
end
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
def vk (L:List (aE V)):ℝ:=(L.map (λ Q=>(aM Q.graph:ℝ))).sum
lemma CK (L:List (aE V)) (f:aE V->ℝ)
  (h:∀P∈L,(aM P.graph:ℝ)<=f P):vk L<=(L.map f).sum:=kU h
lemma KE (s:cv V) (j k) (P:aE V) (c:ℝ)
  (hp:∀Q∈cJ s j k [P],(aM Q.graph:ℝ)<=c*Q.vertices.card):(aM P.graph:ℝ)<=((eu s j k [P]).length:ℝ)+c*bF (cJ s j k [P])+vk (advance s j k [P]):=by
 have hh:=nI (ud s j k P);have hc:=pQ _ (Bf s j k [P]);have hm:=wL _ c hp;simp only [gK,nj,jn,Function.comp_def] at hh;dsimp only [vk];linarith
lemma Om (s:cv V) (j) (P:aE V):(aM P.graph:ℝ)<=((s j P).cycles.length:ℝ)+vk (s j P).boxes:=by have hh:=nI (s j P).partition;have hc:=pQ _ (s j P).xE;simp only [gK,nj,jn,Function.comp_def] at hh;dsimp only [vk];linarith
lemma Bh {V:Type} [aP:Fintype V] [aO:DecidableEq V] {L M:List (aE V)} (h:L.Perm M):bF L=bF M:=(h.map _).sum_eq
lemma Kd (s:cv V) (j k) (L:List (aE V)):(L.map (λ P=>((eu s j k [P]).length:ℝ))).sum=((eu s j k L).length:ℝ):=by have h:=(yf s j k L (λ P=>[P])).length_eq;simp only [nE] at h;rw [h,List.length_flatMap];simp [Function.comp_def]
lemma Kh (s:cv V) (j k) (L:List (aE V)):(L.map (λ P=>bF (cJ s j k [P]))).sum=bF (cJ s j k L):=by have h:=Bh (tZ s j k L (λ P=>[P]));simpa only [nE,j3] using h.symm
lemma MZ (s:cv V) (j k) (L:List (aE V)):(L.map (λ P=>bF (advance s j k [P]))).sum=bF (advance s j k L):=by have h:=aF bF (s6 s j k L (λ P=>[P]));simpa only [nE,j3] using h.symm
lemma BQ (s:cv V) (j k) (P:aE V):(eu s j (k+1) [P]).Perm ((s j P).cycles ++
   (s j P).boxes.flatMap (λ B=>eu s (j+1) k [(s j P).rest B])):=by
 rw [show k+1=1+k by omega,CJ];simp only [eu,tV,List.nil_append,lZ,iy,jo,lK,jC,jo,iy,cO.rP];have hh:=yf s (j+1) k (s j P).boxes (λ B=>[(s j P).rest B]);simp only [<-o0] at hh;exact hh.append_left _
lemma u5 (s:cv V) (j k) (P:aE V):(cJ s j (k+1) [P]).Perm ((s j P).boxes.flatMap (s j P).lD ++
   (s j P).boxes.flatMap (λ B=>cJ s (j+1) k [(s j P).rest B])):=by
 rw [show k+1=1+k by omega,xq];simp only [cJ,tV,List.nil_append,i3,iy,jo,lK,jC,jo,iy,cO.rP];have hh:=tZ s (j+1) k (s j P).boxes (λ B=>[(s j P).rest B]);simp only [<-o0] at hh;exact hh.append_left _
lemma EH (s:cv V) (j k) (P:aE V):advance s j (k+1) [P]=(s j P).boxes.flatMap (λ B=>advance s (j+1) k [(s j P).rest B]):=by rw [show k+1=1+k by omega,uZ];simp only [lK,tV,jo,jC,iy,cO.rP];simpa only [<-o0] using s6 s (j+1) k (s j P).boxes (λ B=>[(s j P).rest B])
lemma EI (s:cv V) (j k) (P:aE V) (c α β γ:ℝ)
  (hp:∀B∈(s j P).boxes,∀Q∈cJ s (j+1) k [(s j P).rest B],(aM Q.graph:ℝ)<=c*Q.vertices.card)
  (hq:∀B∈(s j P).boxes,(aM (f5 ((advance s (j+1) k [(s j P).rest B]).map aE.graph ++
    ((s j P).lD B).map aE.graph)):ℝ)<=
   c*bF ((s j P).lD B)+α*bF (advance s (j+1) k [(s j P).rest B])+β*bF ((s j P).lD B)+γ*B.vertices.card):
  (aM P.graph:ℝ)<=((eu s j (k+1) [P]).length:ℝ)+c*bF (cJ s j (k+1) [P])+α*bF (advance s j (k+1) [P])+β*bF (i3 s j [P])+γ*bF (jC s j [P]):=by
 have hb (B) (hB:B∈(s j P).boxes):=Ij ((s j P).lD B)
  (R:=(s j P).rest B) (by simpa only [cO.DG _ hB] using (s j P).r5 B hB)
  s (j+1) k c _ (hp B hB) (hq B hB)
 have hh:=(Om s j P).trans (dS (le_refl _) (CK _ _ hb));have hc:=(BQ s j k P).length_eq;have hm:=Bh (u5 s j k P);rw [hc,ng,fP,List.length_flatMap,hm,qQ,j3,j3,EH,j3];simp only [i3,jC,iy,cO.yL,j3];simp only [List.sum_map_add,o3] at hh;simp only [Nat.cast_list_sum,jn,Function.comp_def,bF] at hh ⊢;linarith
lemma DH (s:cv V) (i k) (P:aE V) (c α β γ:ℝ)
  (hp:∀Q∈cJ s 0 (i+(k+1)) [P],(aM Q.graph:ℝ)<=c*Q.vertices.card)
  (hq:∀Q∈advance s 0 i [P],∀B∈(s i Q).boxes,(aM (f5 ((advance s (i+1) k [(s i Q).rest B]).map aE.graph ++
    ((s i Q).lD B).map aE.graph)):ℝ)<=
   c*bF ((s i Q).lD B)+α*bF (advance s (i+1) k [(s i Q).rest B])+β*bF ((s i Q).lD B)+γ*B.vertices.card):
  (aM P.graph:ℝ)<=((eu s 0 (i+(k+1)) [P]).length:ℝ)+c*bF (cJ s 0 (i+(k+1)) [P])+α*bF (advance s 0 (i+(k+1)) [P])+β*bF (i3 s i (advance s 0 i [P]))+γ*bF (advance s 0 (i+1) [P]):=by
 have he:cJ s 0 (i+(k+1)) [P]=cJ s 0 i [P] ++
  cJ s i (k+1) (advance s 0 i [P]):=by rw [xq,d3]
 have UG:∀Q∈cJ s 0 i [P],(aM Q.graph:ℝ)<=c*Q.vertices.card:=by intro Q hQ;apply hp;rw [he];exact List.mem_append_left _ hQ
 have ZK (Q) (hQ:Q∈advance s 0 i [P]) (B) (hB:B∈(s i Q).boxes)
   (R) (hR:R∈cJ s (i+1) k [(s i Q).rest B]):(aM R.graph:ℝ)<=c*R.vertices.card:=by
  apply hp R;rw [he,fQ];right;have h₁:=tZ s i (k+1) (advance s 0 i [P]) (λ Q=>[Q]);simp only [nE] at h₁;rw [h₁.mem_iff];apply kV.mpr;refine ⟨Q,hQ,?_⟩;rw [(u5 s i k Q).mem_iff,fQ];exact Or.inr (kV.mpr ⟨B,hB,hR⟩)
 have hh:=(KE s 0 i P c UG).trans (dS (le_refl _)
  (CK _ _ (λ Q hQ=>EI s i k Q c α β γ (ZK Q hQ) (hq Q hQ))))
 rw [CJ,xq,uZ,d3,ng,fP,qQ];simp only [List.sum_map_add,o3,Kd,Kh,MZ] at hh;have hS:((advance s 0 i [P]).map (λ Q=>bF (i3 s i [Q]))).sum=bF (i3 s i (advance s 0 i [P])):=by simp only [i3,iy,j3]
 have hN:((advance s 0 i [P]).map (λ Q=>bF (jC s i [Q]))).sum=bF (advance s 0 (i+1) [P]):=by simp only [jC,iy,lK,d3,j3]
 rw [hS,hN] at hh;linarith
end
end af.eF
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
structure dz (P:aE V) (dO:ℝ) where
 d4:cv V
 count:ℕ
 positive:0<count
 cutoff:∀j<count,dO<=aT P.vertices.card j
 Ki:aT P.vertices.card count<dO
 bounded:∀j<count,∀Q∈advance d4 0 j [P],(d4 j Q).Bounded (aT P.vertices.card j)
 degree:∀j≤ count,∀Q∈advance d4 0 j [P],2*(cw Q.graph:ℝ)/Q.vertices.card<=aT P.vertices.card j
lemma Kj:∃dN:ℝ,1<dN/\∀dO≥dN,∀(V:Type) [Fintype V] [DecidableEq V] (P:aE V),dO<=(P.vertices.card:ℝ)->2*(cw P.graph:ℝ)/P.vertices.card<=P.vertices.card->Nonempty (dz P dO):=by
 obtain ⟨Aq,GU⟩:=Ka;refine ⟨max Aq 2,dZ (by norm_num:(1:ℝ)<2) (bC _ _),?_⟩;intro dO hD V _ _ P hn hdeg;have hD1:1<dO:=dZ (by norm_num:(1:ℝ)<2) ((bC _ _).trans hD);have hn1:1<(P.vertices.card:ℝ):=hD1.trans_le hn;have hne:P.vertices.Nonempty:=cT.mp (by exact_mod_cast (by linarith:(0:ℝ)<P.vertices.card));obtain ⟨split,q2⟩:=GU V;let s:cv V:=λ j Q=>split (aT P.vertices.card j) Q
 have hs:∀j Q,dO<=aT P.vertices.card j->Q.vertices.Nonempty->2*(cw Q.graph:ℝ)/Q.vertices.card<=aT P.vertices.card j->(s j Q).Bounded (aT P.vertices.card j):=by intro j Q hj hQ hd;exact q2 _ ((b6 _ _).trans (hD.trans hj)) Q hQ hd
 obtain ⟨m,hm,hlast,ob⟩:=yc P.vertices.card dO hD1 hn;have hL:∀Q∈[P],Q.vertices.Nonempty:=by simpa using hne
 have QA:∀Q∈[P],2*(cw Q.graph:ℝ)/Q.vertices.card<=aT P.vertices.card 0:=by simpa only [jM,forall_eq,wZ] using hdeg
 refine ⟨{d4:=s,count:=m,positive:=hm,cutoff:=ob,Ki:=hlast,bounded:=?_,degree:=?_}⟩
 ·intro j hj
  simpa only [d3] using Jw s P.vertices.card dO (aN _) hs
   0 j [P] hL QA (λ l _ hl=>ob l (by omega))
 ·intro j hj
  simpa only [d3] using DY s P.vertices.card dO (aN _) hs
   0 j [P] hL QA (λ l _ hl=>ob l (by omega))
variable {P:aE V} {dO:ℝ}
abbrev dz.frontier (H:dz P dO) (j:ℕ):=advance H.d4 0 j [P]
abbrev dz.scale (_H:dz P dO) (j:ℕ):=aT (P.vertices.card:ℝ) j
abbrev dz.mass (H:dz P dO) (j:ℕ):=bF (H.frontier j)
abbrev dz.rD (H:dz P dO) (j:ℕ):=bF (i3 H.d4 j (H.frontier j))
lemma dz.On (H:dz P dO) (j):(P.vertices.card:ℝ)<=H.mass j:=FH H.d4 0 j P
lemma dz.JF (H:dz P dO) (hn:1<(P.vertices.card:ℝ))
  (kI:∀j<H.count,80<=logb 2 (H.scale j)) (j) (hj:j<H.count):H.mass (j+1)<=(1+80/logb 2 (H.scale j))*P.vertices.card:=by
 have hh:=rB H.d4 P.vertices.card hn 0 (j+1) [P]
  (λ l hl=>by simpa only [d3] using H.bounded l (by omega))
 have hx:=vG P.vertices.card 2 hn (by norm_num) j (by norm_num;exact kI j hj);simp only [d3,n8,xo,fq] at hh;have Jl:=aJ hx (aN P.vertices.card:(0:ℝ)<=_);norm_num only [show (40:ℝ)*2=80 by norm_num] at Jl;dsimp only [dz.mass,dz.frontier,dz.scale] at *;nlinarith
lemma dz.DI (H:dz P dO) (hn:1<(P.vertices.card:ℝ))
  (kI:∀j<H.count,80<=logb 2 (H.scale j)) (k) (hk:k<=H.count):H.mass k<=2*P.vertices.card:=by
 cases k with
 | zero=>simp only [dz.mass,dz.frontier,tV,n8,xo,fq];nlinarith [(aN P.vertices.card:(0:ℝ)<=_)]
 | succ j=>
   have hj:j<H.count:=by omega
   have hh:=H.JF hn kI j hj;have hl:=kI j hj;have hd:80/logb 2 (H.scale j)<=1:=(kd (by linarith)).mpr hl;have hc:(0:ℝ)<=P.vertices.card:=aN _;nlinarith
lemma dz.KY (H:dz P dO) (hn:1<(P.vertices.card:ℝ))
  (kI:∀j<H.count,80<=logb 2 (H.scale j)) (j) (hj:j<H.count):H.rD j<=2*P.vertices.card:=(Ib H.d4 j (H.frontier j)).trans (by simpa only [dz.mass,dz.frontier,lK,d3] using H.DI hn kI (j+1) (by omega))
lemma dz.FR (H:dz P dO) (hn:1<(P.vertices.card:ℝ))
  (gN:∀j<H.count,af.gz 80 (H.scale j)) (j) (hj:j<H.count):((eu H.d4 0 (j+1) [P]).length:ℝ)<=20*P.vertices.card/logb 2 (H.scale j):=by
 rw [GN];apply (aK (λ l hl=>?_)).trans
  (AU P.vertices.card hn j (λ l=>H.mass l)
   (λ l hl=>H.DI hn (λ a ha=>(gN a ha).oz) l (by have:=j6.mp hl;omega))
   (λ l hl=>(gN l (by have:=j6.mp hl;omega)).GZ))
 simpa only [d3] using FK H.d4 l (H.frontier l) (H.scale l)
  (H.bounded l (by have:=j6.mp hl;omega))
lemma dz.subset (H:dz P dO) (j):∀Q∈H.frontier j,Q.vertices⊆P.vertices:=CI H.d4 0 j [P] P.vertices (by simp)
lemma dz.rO (H:dz P dO) (j) {Q B:aE V}
  (hQ:Q∈H.frontier j) (hB:B∈(H.d4 j Q).boxes):B.vertices⊆P.vertices:=((H.d4 j Q).rO B hB).trans (H.subset j Q hQ)
lemma dz.Kk (H:dz P dO) (j) (hj:j<H.count)
  {Q:aE V} (hQ:Q∈H.frontier (j+1)):(Q.vertices.card:ℝ)<=(H.scale j)^(51/50:ℝ):=by
 simp only [dz.frontier,lK,d3] at hQ;obtain ⟨T,hT,B,hB,hv,_⟩:=(oa H.d4 j _ Q).mp hQ;rw [hv];exact (H.bounded j hj T hT).2.2.1 B hB
lemma dz.Oo (H:dz P dO) (hn:1<(P.vertices.card:ℝ))
  (kI:∀j<H.count,80<=logb 2 (H.scale j)) (i k)
  (CL:i+k<H.count) {Q B:aE V}
  (hQ:Q∈H.frontier i) (hB:B∈(H.d4 i Q).boxes):bF (advance H.d4 (i+1) k [(H.d4 i Q).rest B])<=(1+80/logb 2 (H.scale (i+k)))*B.vertices.card:=by
 have hh:=rB H.d4 P.vertices.card hn (i+1) k [(H.d4 i Q).rest B]
  (λ l hl R hR=>by
   have hr:=yY H.d4 i l [P] hQ hB R hR;have he:i+1+l=(i+l)+1:=by omega
   exact H.bounded (i+1+l) (by omega) R hr)
 have hx:=vG P.vertices.card 2 hn (by norm_num) (i+k)
  (by norm_num;exact kI (i+k) CL)
 simp only [n8,xo,fq,cO.u8] at hh;rw [show i+1+k=(i+k)+1 by omega] at hh;have Jl:=aJ hx (aN B.vertices.card:(0:ℝ)<=_);norm_num only [show (40:ℝ)*2=80 by norm_num] at Jl;dsimp only [dz.scale] at *;nlinarith
lemma dz.Kl (H:dz P dO) (hn:1<(P.vertices.card:ℝ))
  (kI:∀j<H.count,80<=logb 2 (H.scale j)) (i k)
  (CL:i+k<H.count) {Q B:aE V}
  (hQ:Q∈H.frontier i) (hB:B∈(H.d4 i Q).boxes):bF (advance H.d4 (i+1) k [(H.d4 i Q).rest B])<=2*B.vertices.card:=by
 have hh:=H.Oo hn kI i k CL hQ hB;have hl:=kI (i+k) CL;have hd:80/logb 2 (H.scale (i+k))<=1:=(kd (by linarith)).mpr hl;have hc:(0:ℝ)<=B.vertices.card:=aN _;nlinarith
lemma dz.O2 (H:dz P dO) (hn:1<(P.vertices.card:ℝ)) (i)
  (CL:i+200<H.count) {Q B R:aE V}
  (hQ:Q∈H.frontier i) (hB:B∈(H.d4 i Q).boxes)
  (hR:R∈advance H.d4 (i+1) 200 [(H.d4 i Q).rest B]):(R.vertices.card:ℝ)<=(H.scale i)^(1/1000:ℝ)/\2*(cw R.graph:ℝ)/R.vertices.card<=(H.scale i)^(1/1000:ℝ):=by
 have hr:=yY H.d4 i 200 [P] hQ hB R hR;have To:R∈H.frontier ((i+200)+1):=by convert hr using 1
 have hd:1<H.scale i:=q4 P.vertices.card hn i;constructor
 ·have hh:=H.Kk (i+200) CL To;apply hh.trans;dsimp only [dz.scale];rw [tQ _ (by positivity),<-lz (by linarith:0<=aT P.vertices.card i)];apply g5 hd.le;nlinarith [vF.1]
 ·have hh:=H.degree ((i+200)+1) (by omega) R To;apply hh.trans;rw [show i+200+1=i+201 by omega];dsimp only [dz.scale];rw [tQ _ (by positivity)];exact g5 hd.le vF.2.le
end
end af.eF
end
section
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma DJ {V A:Type} [Fintype A] [DecidableEq V]
  (U:A->Finset V) (Y:Finset V) (hd:Pairwise λ r s=>Disjoint (U r) (U s))
  (hu:∀r,U r⊆Y):(∑r,((U r).card:ℝ))<=Y.card:=by
 have hc:(univ.biUnion U).card=∑r,(U r).card:=j5 (λ i _ j _ hij=>hd hij);have hs:univ.biUnion U⊆Y:=by intro v hv;obtain ⟨r,_,hv⟩:=bR.mp hv;exact hu r hv
 have hh:=aU hs;rw [hc] at hh;exact_mod_cast hh
lemma Ik:∃dN:ℝ,1<dN/\∀D≥dN,∀vj:ℝ,gz vj D ->∀(V A:Type) [Fintype V] [Fintype A],∀(G F:SimpleGraph V) (R:A->SimpleGraph V) (U:A->Finset V) (Y:Finset V),F<=G->(∀r,R r<=G)->Pairwise (λ r s=>Disjoint (R r).edgeSet (R s).edgeSet)->Pairwise (λ r s=>Disjoint (U r) (U s))->(∀r,U r⊆Y)->(∀r,∀⦃x y⦄,(R r).Adj x y->x∈U r/\y∈U r)->(∀r,Disjoint F.edgeSet (R r).edgeSet)->F.edgeSet∪(⋃ r,(R r).edgeSet)=G.edgeSet->(∀r,aR.af.aV.b9 (R r) (U r) (D^(9/10:ℝ)))->(∀r,D^(9/10:ℝ)<=((U r).card:ℝ)/\((U r).card:ℝ)<=D^(51/50:ℝ))->((Y.card:ℝ)<=D^(51/50:ℝ))->2*(F.edgeFinset.card:ℝ)<=2*Y.card*D^(1/1000:ℝ)->∀T:ℝ,T<=2*Y.card->∀_b:oo.wJ F Y (D^(3/10:ℝ)) T,∀(n:ℕ) (C t:ℝ),0<=C->0<=t->Y.card<=n->D^(3/10:ℝ)<n->(∀(Q:Type) [Fintype Q] (H:SimpleGraph Q),card Q<n->(aM H:ℝ)<=C*card Q)->
  (∀(Q:Type) [Fintype Q] (H:SimpleGraph Q),card Q<n->(card Q:ℝ)<=D^(3/10:ℝ)->(aR.af.aM H:ℝ)<=t*card Q)->
  (aR.af.aM G:ℝ)<=t*(T-(∑r,((U r).card:ℝ))/3+(2/3)*Y.card/logb 2 D)+8*((∑r,((U r).card:ℝ))+T-Y.card)+(9+C*lQ)*(∑r,((U r).card:ℝ)):=by
 obtain ⟨D₁,K7,An⟩:=Batch.vT;obtain ⟨D₂,F7,Tp⟩:=vz (1/4) lQ (by norm_num) xG;refine ⟨max D₁ D₂,dZ K7 (b6 _ _),?_⟩;intro D hD vj gN V A _ _ G F R U Y GX Kz xN Cs OZ Ql KA wu hexp uO
  hY hF T hT b n C t hC ht Tq iE ih Mz
 have hD0:0<D:=by linarith [gN.u0]
 have ha:1<=D^(1/100:ℝ):=jv gN.u0.le (by norm_num);obtain ⟨a⟩:=oo.DE F Y b.vertices U (D^(1/100:ℝ)) (D^(3/100:ℝ))
  (fG hD0.le _) b.subset OZ b.FM Cs
 let:=a.finite;have UF (j) (i:a.Index j):8<=(a.vertices j i).card:=by have hh:=gN.FQ.trans (a.large j i);exact_mod_cast hh
 have Rn (j) (i:a.Index j):(D^(1/100:ℝ))^2<=(a.vertices j i).card:=gN.KX.trans (a.large j i);have hn (j):(b.vertices j).card<n:=by exact_mod_cast (b.order_le j).trans_lt iE
 obtain ⟨H,ZL,UH,jF⟩:=An D ((b6 _ _).trans hD) V A b.Index G F R U
  GX Kz xN Cs Ql KA wu hexp uO b.graph b.vertices b.Mv b.disjoint b.Jz
  b.supported b.order_le a.Index a.vertices a.disjoint a.FO a.Mx a.D3
  a.degree_le ha UF Rn n t ht hn Mz
 have hp (r:A):(aR.af.aM (H r):ℝ)<=(9+C*lQ)*(U r).card:=by
  have hh:=Tp D ((bC _ _).trans hD) n C hC ih V (H r) (H r) (U r) dH
   ((aU (OZ r)).trans Tq) (λ x y h=>Ql r (ZL r h)) (uO r).1 (uO r).2
   (by simpa only [b9,aR.af.aV.b9,show (1/4:ℝ)*D^(9/10:ℝ)=D^(9/10:ℝ)/4 by ring] using UH r)
  exact hh
 have aar:(∑r,(aR.af.aM (H r):ℝ))<=(9+C*lQ)*(∑r,((U r).card:ℝ)):=by simpa only [dR] using aK (s:=univ) (λ r _=>hp r)
 have td:((Y\oo.tW F Y (D^(1/100:ℝ))).card:ℝ)<=Y.card/logb 2 D:=gN.O1 (aN _) ((oo.zE F Y (D^(1/100:ℝ))).trans hF);have Ro:D^(9/10:ℝ)*(card A:ℝ)<=Y.card:=by
  calc
   _=∑_r:A,D^(9/10:ℝ):=by simp [bK]
   _<=∑r,((U r).card:ℝ):=aK (λ r _=>(uO r).1)
   _<=_:=DJ U Y Cs OZ
 have Lg:=gN.Ol (aN Y.card) (aN (card b.Index))
  (aN (card A)) hY hT b.count_le Ro
 have EK:(∑r,((U r).card:ℝ))-2*Y.card/logb 2 D <=∑j,∑i,((a.vertices j i).card:ℝ):=by have hh:=a.lower;simp only [gq] at td Lg hh ⊢;linarith only [hh,td,Lg]
 have QC:(∑j,∑i,((a.vertices j i).card:ℝ))<=(∑r,((U r).card:ℝ))+T-Y.card:=by have hh:=a.upper;have hm:=b.Kc;linarith
 have u7:(∑j,∑i,((a.vertices j i).card:ℝ))/3<=∑j,∑i,(((a.vertices j i).card/2:ℕ):ℝ):=by simp only [sum_div];apply aK;intro j _;apply aK;intro i _;exact oo.Ie (UF j i)
 have hq:(∑j,((b.vertices j).card:ℝ))-∑j,∑i,(((a.vertices j i).card/2:ℕ):ℝ)<=T-(∑r,((U r).card:ℝ))/3+(2/3)*Y.card/logb 2 D:=by have hm:=b.Kc;simp only [gq] at hm EK u7 ⊢;linarith only [hm,EK,u7]
 have abi:=aJ hq ht;push_cast at jF;linarith
end
end af
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
lemma rQ (L:List (aE V)):(⋃ i:Fin L.length,(L.get i).graph.edgeSet)=(f5 (L.map aE.graph)).edgeSet:=by
 ext e;induction e using bJ with
 | _ x y=>
   simp only [av,ic];rw [nK];constructor
   ·rintro ⟨i,hi⟩;exact ⟨_,bV.mpr ⟨_,L.get_mem i,rfl⟩,hi⟩
   ·rintro ⟨G,hG,hxy⟩;obtain ⟨Q,hQ,rfl⟩:=bV.mp hG;obtain ⟨i,rfl⟩:=nB.mp hQ;exact ⟨i,hxy⟩
lemma CN {B R:aE V} (A:List (aE V))
  (Nz:cj B.graph (R.graph :: A.map aE.graph))
  (s:cv V) (j k:ℕ):cj (f5 ((advance s j k [R]).map aE.graph ++ A.map aE.graph))
   ((advance s j k [R]).map aE.graph ++ A.map aE.graph):=by
 apply pO;intro x y;have hb:=Nz x y;have hr:=ud s j k R x y;simp only [iW,dV] at hb hr ⊢;split_ifs at hb hr<;>omega
lemma BS:∃dN:ℝ,1<dN/\∀D≥dN,∀vj:ℝ,af.gz vj D ->∀(V:Type) [Fintype V] (L A:List (aE V)) (Y:Finset V),cj (f5 (L.map aE.graph ++ A.map aE.graph))
   (L.map aE.graph ++ A.map aE.graph)->
  A.Pairwise (λ R S=>Disjoint R.vertices S.vertices)->(∀R∈A,R.vertices⊆Y)->(∀Q∈L,Q.vertices⊆Y)->(∀v∈Y,∃Q∈L,v∈Q.vertices)->(∀Q∈L,Q.vertices.Nonempty/\(Q.vertices.card:ℝ)<=D^(1/1000:ℝ)/\2*(cw Q.graph:ℝ)/Q.vertices.card<=D^(1/1000:ℝ))->
  (∀R∈A,D^(9/10:ℝ)<=(R.vertices.card:ℝ)/\(R.vertices.card:ℝ)<=D^(51/50:ℝ)/\b9 R.graph R.vertices (D^(9/10:ℝ)))->
  (Y.card:ℝ)<=D^(51/50:ℝ)->bF L<=2*Y.card->∀(n:ℕ) (C t:ℝ),0<=C->0<=t->Y.card<=n->D^(3/10:ℝ)<n->(∀(Q:Type) [Fintype Q] (H:SimpleGraph Q),card Q<n->(af.aM H:ℝ)<=C*card Q)->
  (∀(Q:Type) [Fintype Q] (H:SimpleGraph Q),card Q<n->(card Q:ℝ)<=D^(3/10:ℝ)->(aR.af.aM H:ℝ)<=t*card Q)->
  (aM (f5 (L.map aE.graph ++ A.map aE.graph)):ℝ)<=(9+C*af.lQ)*bF A+(t+8)*bF L+(8-t/3)*bF A+((2/3)*t/logb 2 D-8)*Y.card:=by
 obtain ⟨dN,ko,WR⟩:=af.Ik;refine ⟨dN,ko,?_⟩;intro D hD vj gN V _ L A Y hpart ZM ZN ZO e7 hL hA hY DC
  n C t hC ht Tq iE ih Mz
 let F:=f5 (L.map aE.graph);let G:=f5 (L.map aE.graph ++ A.map aE.graph);let R (r:Fin A.length):=(A.get r).graph;let U (r:Fin A.length):=(A.get r).vertices;have hp:=List.pairwise_append.mp (uz hpart);have ZP:=o7 (m7.mp hp.1) (λ _ _ h=>h.symm);have xN:Pairwise (λ r s=>Disjoint (R r).edgeSet (R s).edgeSet):=o7 (m7.mp hp.2.1) (λ _ _ h=>h.symm);have Cs:Pairwise (λ r s=>Disjoint (U r) (U s)):=o7 ZM (λ _ _ h=>h.symm);have KA (r):Disjoint F.edgeSet (R r).edgeSet:=by
  rw [<-rQ];exact kP.mpr (λ i=>hp.2.2 _ (bV.mpr ⟨_,L.get_mem i,rfl⟩)
   _ (bV.mpr ⟨_,A.get_mem r,rfl⟩))
 have GX:F<=G:=FI (List.sublist_append_left _ _);have Kz (r):R r<=G:=by intro x y hxy;exact (nK _ _ _).mpr ⟨_,oY _ (bV.mpr ⟨_,A.get_mem r,rfl⟩),hxy⟩
 have wu:F.edgeSet∪(⋃ r,(R r).edgeSet)=G.edgeSet:=by
  change F.edgeSet∪(⋃ r:Fin A.length,(A.get r).graph.edgeSet)=_;rw [rQ];ext e;induction e using bJ with
  | _ x y=>simp only [b8,ic,G,GM,nv,F]
 have hB:0<D^(3/10:ℝ):=d6 (by linarith [gN.u0]) _;obtain ⟨b⟩:=oo.EG F Y (λ i:Fin L.length=>(L.get i).graph)
  (λ i=>(L.get i).vertices) ZP (rQ L)
  (λ i x y hxy=>(L.get i).supported hxy) (λ i=>ZO _ (L.get_mem i))
  (by intro v hv;obtain ⟨Q,hQ,OD⟩:=e7 v hv;obtain ⟨i,rfl⟩:=nB.mp hQ;exact bR.mpr ⟨i,mem_univ _,OD⟩)
  (D^(3/10:ℝ)) hB (λ i=>((hL _ (L.get_mem i)).2.1).trans gN.G0)
 have hsum:(∑i:Fin L.length,((L.get i).vertices.card:ℝ))=bF L:=wH L (λ Q=>(Q.vertices.card:ℝ));have UI:(∑i:Fin A.length,((U i).card:ℝ))=bF A:=wH A (λ Q=>(Q.vertices.card:ℝ));have hF:2*(F.edgeFinset.card:ℝ)<=2*Y.card*D^(1/1000:ℝ):=by
  have hh:=(cq.mpr (FJ (L.map aE.graph)):(_:ℝ)<=_);have hdeg:(L.map (λ Q=>2*(cw Q.graph:ℝ))).sum<=bF L*D^(1/1000:ℝ):=by
   unfold bF;rw [<-List.sum_map_mul_right];apply kU;intro Q hQ;have hc:(0:ℝ)<Q.vertices.card:=by exact_mod_cast cT.mpr (hL Q hQ).1
   simpa only [bK] using (dK hc).mp (hL Q hQ).2.2
  simp only [Nat.cast_list_sum,jn,Function.comp_def] at hh;rw [o3] at hdeg;have hx:=aY DC (fG (show (0:ℝ)<=D by linarith [gN.u0]) (1/1000:ℝ));change 2*(cw F:ℝ)<=_;linarith
 have jF:=WR D hD vj gN V (Fin A.length) G F R U Y GX Kz xN Cs
  (λ r=>ZN _ (A.get_mem r)) (λ r x y hxy=>(A.get r).supported hxy) KA wu
  (λ r=>(hA _ (A.get_mem r)).2.2)
  (λ r=>⟨(hA _ (A.get_mem r)).1,(hA _ (A.get_mem r)).2.1⟩)
  hY hF (∑i:Fin L.length,((L.get i).vertices.card:ℝ)) (by simpa only [hsum] using DC)
  b n C t hC ht Tq iE ih Mz
 rw [hsum,UI] at jF;change (aM G:ℝ)<=_;convert jF using 1<;>first | rfl | ring
end
end af.eF
end
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]
lemma Km (s:cv V) (j k:ℕ) (L:List (aE V))
  {R:aE V} (hR:R∈cJ s j k L):∃l<k,R∈i3 s (j+l) (advance s j l L):=by
 induction k with
 | zero=>simp [cJ] at hR
 | succ k ih=>
   rcases fQ.mp hR with h | h
   ·obtain ⟨l,hl,hR⟩:=ih h;exact ⟨l,by omega,hR⟩
   ·exact ⟨k,by omega,h⟩
lemma xw:∃dN:ℝ,1<dN/\∀dO≥dN,∀(V:Type) [Fintype V] [DecidableEq V] (P:aE V) (H:dz P dO),∀(C:ℝ),0<=C->(∀(Q:Type) [Fintype Q] (G:SimpleGraph Q),card Q<P.vertices.card->(af.aM G:ℝ)<=C*card Q)->
  ∀k≤H.count,∀R∈cJ H.d4 0 k [P],(aM R.graph:ℝ)<=(9+C*af.lQ)*R.vertices.card:=by
 obtain ⟨dN,ko,JG⟩:=af.vz 1 af.lQ (by norm_num) af.xG;refine ⟨dN,ko,?_⟩;intro dO hD V _ _ P H C hC ih k hk R hR;obtain ⟨j,zQ,hR⟩:=Km H.d4 0 k [P] hR;simp only [d3] at hR;obtain ⟨Q,hQ,B,hB,hR⟩:=(by simpa [i3,kV] using hR:∃Q∈H.frontier j,∃B∈(H.d4 j Q).boxes,R∈(H.d4 j Q).lD B);have hj:j<H.count:=by omega
 have hb:=(H.bounded j hj Q hQ).2.2.2.1 B hB R hR;have hsub:=((H.d4 j Q).tU B hB R hR).trans (H.rO j hQ hB);exact JG (H.scale j) (hD.trans (H.cutoff j hj)) P.vertices.card C hC ih V R.graph R.graph R.vertices
  dH (aU hsub) R.supported hb.1 hb.2.1 (by simpa only [one_mul,aR.af.aV.b9,b9,rM,dz.scale] using hb.2.2)
lemma AZ:∃dN:ℝ,1<dN/\∀dO≥dN,∀(V:Type) [Fintype V] (P:aE V) (H:dz P dO),1<(P.vertices.card:ℝ)->(∀j<H.count,af.gz 80 (H.scale j))->∀i,i+200<H.count->∀C t:ℝ,0<=C->0<=t->(∀(Q:Type) [Fintype Q] (G:SimpleGraph Q),card Q<P.vertices.card->(af.aM G:ℝ)<=C*card Q)->
  (∀(Q:Type) [Fintype Q] (G:SimpleGraph Q),card Q<P.vertices.card->(card Q:ℝ)<=(H.scale i)^(3/10:ℝ)->(aR.af.aM G:ℝ)<=t*card Q)->
  (∀R∈cJ H.d4 0 (i+201) [P],(aM R.graph:ℝ)<=(9+C*af.lQ)*R.vertices.card)->
  (aM P.graph:ℝ)<=((eu H.d4 0 (i+201) [P]).length:ℝ)+(9+C*af.lQ)*bF (cJ H.d4 0 (i+201) [P])+(t+8)*H.mass (i+201)+(8-t/3)*H.rD i+((2/3)*t/logb 2 (H.scale i)-8)*H.mass (i+1):=by
 obtain ⟨dN,ko,MA⟩:=BS;refine ⟨dN,ko,?_⟩;intro dO hD V _ P H hn gN i CL C t hC ht ih Mz hp;have hi:i<H.count:=by omega
 have hne:P.vertices.Nonempty:=cT.mp (by exact_mod_cast (by linarith:(0:ℝ)<P.vertices.card));have iE:(H.scale i)^(3/10:ℝ)<(P.vertices.card:ℝ):=by apply dZ _ (yX P.vertices.card hn.le i);have hd:=q4 P.vertices.card hn i;simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hd (by norm_num:(3/10:ℝ)<1)
 apply DH H.d4 i 200 P (9+C*af.lQ)
  (t+8) (8-t/3) ((2/3)*t/logb 2 (H.scale i)-8) hp
 intro Q hQ B hB;have PC:=pN H.d4 0 i [P] (by simpa using hne) Q hQ;have WS:=(H.d4 i Q).wG PC B hB;have UJ:((H.d4 i Q).rest B).vertices.Nonempty:=by simpa only [cO.u8] using WS
 exact MA (H.scale i) (hD.trans (H.cutoff i hi)) 80 (gN i hi) V
  (advance H.d4 (i+1) 200 [(H.d4 i Q).rest B]) ((H.d4 i Q).lD B) B.vertices
  (CN _ (by simpa only [cO.DG _ hB] using (H.d4 i Q).r5 B hB) _ _ _)
  ((H.d4 i Q).t9 B hB) ((H.d4 i Q).tU B hB)
  (CI H.d4 (i+1) 200 [(H.d4 i Q).rest B] B.vertices (by simp))
  (λ v hv=>DX H.d4 (i+1) 200 [(H.d4 i Q).rest B] ((H.d4 i Q).rest B) (by simp) v (by simpa only [cO.u8] using hv))
  (λ R hR=>⟨pN H.d4 (i+1) 200 [(H.d4 i Q).rest B] (by simpa using UJ) R hR,H.O2 hn i CL hQ hB hR⟩)
  ((H.bounded i hi Q hQ).2.2.2.1 B hB) ((H.bounded i hi Q hQ).2.2.1 B hB)
  (H.Kl hn (λ j hj=>(gN j hj).oz) i 200 CL hQ hB)
  P.vertices.card C t hC ht (aU (H.rO i hQ hB)) iE ih Mz
end
end af.eF
end
section
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Real
lemma JH (q n S M L Nt UK C t w:ℝ)
  (hn:0<=n) (hS:0<=S) (hC:0<=C) (ht:0<=t) (hw:0<w)
  (hM:M<=od*S) (hL:L<=ug*n/w)
  (ZQ:Nt<=n+ug*n/w) (aas:n<=UK) (UL:UK<=2*n)
  (hq:q<=L+(9+C*lQ)*M+(t+8)*Nt+(8-t/3)*S+((2/3)*t/w-8)*UK):q<=t3*(S+n/w)+(C/100)*S+t*(n-S/3+xu*n/w):=by
 have hη:=xG;have hc:=aJ hM (by positivity:0<=9+C*lQ);have hT:=aJ ZQ (by linarith:0<=t+8);have hI:=aJ UL (by positivity:0<=(2/3)*t/w);have VQ: -8*UK<= -8*n:=by linarith
 have hA:=aY (b6 (9*od+8) (9*ug)) hS;have hB:=aY (bC (9*od+8) (9*ug)) (fF hn hw.le);change (9*od+8)*S<=t3*S at hA;change 9*ug*(n/w)<=t3*(n/w) at hB;simp only [lQ,od,xu,gq] at hc hT hI VQ hA hB hq hL ⊢;nlinarith only [hc,hT,hI,VQ,hA,hB,hq,hL]
lemma DK (q n M C dO:ℝ) (hn:0<=n) (hC:0<=C)
  (JI:4*(20+dO+18*od)<=C) (hM:M<=2*od*n)
  (hq:q<=(20+dO)*n+(9+C*lQ)*M):q<=C*Batch.f6 n*n:=by
 have hη:=xG;have hc:=aJ hM (by positivity:0<=9+C*lQ);have G3:=aY JI hn;have PI:=aJ (Batch.k7 n).1 (bZ hC hn);have QD:0<=C*n:=bZ hC hn;simp only [lQ,od] at hc G3 hq;nlinarith only [hq,hc,G3,PI,QD]
end
end af
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V] {P:aE V} {dO:ℝ}
lemma dz.NA (H:dz P dO) (hn:1<(P.vertices.card:ℝ)) (i):logb 2 (H.scale (i+200))=jA^200*logb 2 (H.scale i):=by dsimp only [dz.scale];rw [tQ _ (by positivity)];exact jH (tP _ (by linarith) _)
lemma dz.PJ (H:dz P dO) (hn:1<(P.vertices.card:ℝ))
  (gN:∀j<H.count,af.gz 80 (H.scale j)) (i)
  (CL:i+200<H.count):H.mass (i+201)<=(P.vertices.card:ℝ)+af.ug*P.vertices.card/logb 2 (H.scale i):=by
 have hh:=H.JF hn (λ j hj=>(gN j hj).oz) (i+200) CL;rw [H.NA hn] at hh;convert hh using 1;try omega
 unfold af.ug;simp only [gq,mul_inv_rev];ring
lemma dz.Oq (H:dz P dO) (hn:1<(P.vertices.card:ℝ))
  (gN:∀j<H.count,af.gz 80 (H.scale j)) (i)
  (CL:i+200<H.count):((eu H.d4 0 (i+201) [P]).length:ℝ)<=af.ug*P.vertices.card/logb 2 (H.scale i):=by
 have hh:=H.FR hn gN (i+200) CL;rw [H.NA hn] at hh;have hw:0<logb 2 (H.scale i):=k3 _ hn i;calc
  _<=20*P.vertices.card/(jA^200*logb 2 (H.scale i)):=hh
  _<=80*P.vertices.card/(jA^200*logb 2 (H.scale i)):=e5 (by nlinarith [(aN P.vertices.card:(0:ℝ)<=_)]) (by positivity)
  _=_:=by unfold af.ug;simp only [gq,mul_inv_rev];ring
lemma dz.KZ (H:dz P dO) (hn:1<(P.vertices.card:ℝ))
  (gN:∀j<H.count,af.gz 80 (H.scale j)):vk (H.frontier H.count)<=dO*P.vertices.card:=by
 have hne:P.vertices.Nonempty:=cT.mp (by exact_mod_cast (by linarith:(0:ℝ)<P.vertices.card));have hD:0<=dO:=by have hh:=H.Ki;have hd:=tP P.vertices.card (by linarith) H.count;linarith
 have jF:∀Q∈H.frontier H.count,(aM Q.graph:ℝ)<=(dO/2)*Q.vertices.card:=by
  intro Q hQ;have PC:=pN H.d4 0 H.count [P] (by simpa using hne) Q hQ;have hc:(0:ℝ)<Q.vertices.card:=by exact_mod_cast cT.mpr PC
  have hg:=(dK hc).mp (H.degree H.count dH Q hQ);have hh:=aY H.Ki.le hc.le;have he:=(cq.mpr (rC Q.graph):(_:ℝ)<=_);nlinarith only [hg,hh,he]
 have hh:=wL (H.frontier H.count) (dO/2) jF;have hm:=aJ (H.DI hn (λ j hj=>(gN j hj).oz) H.count dH)
  (fF hD (by norm_num:(0:ℝ)<=2))
 change vk (H.frontier H.count)<=(dO/2)*H.mass H.count at hh;nlinarith only [hh,hm]
lemma dz.K3 (H:dz P dO) (hn:1<(P.vertices.card:ℝ))
  (gN:∀j<H.count,af.gz 80 (H.scale j)) (c:ℝ)
  (hp:∀R∈cJ H.d4 0 H.count [P],(aM R.graph:ℝ)<=c*R.vertices.card):(aM P.graph:ℝ)<=(20+dO)*P.vertices.card+c*bF (cJ H.d4 0 H.count [P]):=by
 have jF:=KE H.d4 0 H.count P c hp;have he:=H.KZ hn gN;obtain ⟨j,hj⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt H.positive);have OG:=H.FR hn gN j (by omega);have hw:=(gN j (by omega)).oz;have hdiv:20*(P.vertices.card:ℝ)/logb 2 (H.scale j)<=20*P.vertices.card:=div_le_self (by positivity) (by linarith);rw [hj] at jF he ⊢;nlinarith only [jF,he,OG,hdiv]
end
end af.eF
end
end
end
end aR
namespace aR
open Finset SimpleGraph Fintype
section
open Filter Asymptotics Real
open scoped Topology
section
open MeasureTheory ProbabilityTheory Finset
section
namespace af.eF
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V] {P:aE V} {dO:ℝ}
def dz.ku (H:dz P dO) (j:ℕ):ℝ:=if j<H.count then H.rD j else 0
lemma dz.rS (H:dz P dO) (j):0<=H.ku j:=by
 unfold dz.ku;split_ifs
 ·exact qP _
 ·rfl
lemma dz.yg (H:dz P dO) (j) (hj:H.count<=j):H.ku j=0:=by simp only [dz.ku,if_neg (by omega:¬j<H.count)]
lemma dz.vH (H:dz P dO) (k) (hk:k<=H.count):bF (cJ H.d4 0 k [P])=∑j∈range k,H.ku j:=by rw [Jx];apply cZ rfl;intro j hj;simp only [d3,dz.ku,ej (by have:=j6.mp hj;omega:j<H.count)]
lemma dz.K4 (H:dz P dO):bF (cJ H.d4 0 H.count [P])=0\/∃i<H.count,0<H.rD i/\∀k≤H.count,k<=i+201->bF (cJ H.d4 0 k [P])<=af.od*H.rD i:=by
 by_cases he:∃j,0<H.ku j
 ·right
  obtain ⟨i,hi,QE⟩:=af.Ig H.ku H.rS
   200 H.count H.yg he
  have JJ:i<H.count:=by by_contra hi';rw [H.yg i (by omega)] at hi;linarith
  simp only [dz.ku,ej JJ] at hi;refine ⟨i,JJ,hi,?_⟩;intro k hk abj;rw [H.vH k hk];have hh:(∑j∈range k,H.ku j)<=∑j∈range (i+200+1),H.ku j:=jr (Finset.range_mono (by omega)) (λ j _ _=>H.rS j);apply hh.trans;norm_num only [dz.ku,ej JJ,af.od,j8] at QE ⊢;exact QE
 ·left;rw [H.vH H.count dH];apply Finset.sum_eq_zero;intro j _;exact le_antisymm (dF (λ h=>he ⟨j,h⟩)) (H.rS j)
end
end af.eF
end
section
namespace af
open aR.af.cI
open aR.af.aV
open aR.af.Splitting
section
open Finset SimpleGraph Real
local instance (p:Prop):Decidable p:=Classical.propDecidable p
lemma Bi {V:Type} [Fintype V] (G:SimpleGraph V):2*(eF.cw G:ℝ)<=(card V:ℝ)^2:=by
 classical
 have h:(G.edgeFinset.card:ℝ)<=((card V).choose 2:ℝ):=cq.mpr G.card_edgeFinset_le_card_choose_two;rw [oU] at h;change 2*(G.edgeFinset.card:ℝ)<=_;nlinarith [(aN (card V):(0:ℝ)<=_)]
lemma yi {V:Type} [Fintype V] (G:SimpleGraph V):aM G=aR.af.aM G:=by rfl
lemma FU {V:Type} [Fintype V] (G:SimpleGraph V):aM G=aR.af.aM G:=by rfl
lemma JK:∃C:ℝ,0<C/\∀(V:Type) [Fintype V] (G:SimpleGraph V),(aM G:ℝ)<=C*Batch.f6 (card V)*card V:=by
 classical
 let vj:ℝ:=max 80 (((xu+1)/Batch.jQ)^2);obtain ⟨UM,ha,Rq⟩:=eF.Kj;obtain ⟨UN,hb,Tr⟩:=eF.xw;obtain ⟨Dc,hc,WT⟩:=eF.AZ;obtain ⟨UO,hr,Ts⟩:=AY vj;let dO:ℝ:=max (max UM UN) (max Dc UO);have VR:UM<=dO:=(b6 UM UN).trans (b6 _ _);have ZR:UN<=dO:=(bC UM UN).trans (b6 _ _);have ZS:Dc<=dO:=(b6 Dc UO).trans (bC _ _);have ZT:UO<=dO:=(bC Dc UO).trans (bC _ _);have Tt:1<dO:=ha.trans_le VR;let C:ℝ:=max (4*(20+dO+18*od)) (7*t3);have JI:4*(20+dO+18*od)<=C:=b6 _ _;have Vt:7*t3<=C:=bC _ _;have QF:0<C:=dZ (by linarith [Bg]) JI;have hC:0<=C:= QF.le;refine ⟨C,QF,?_⟩;have UP:∀n:ℕ,∀(V:Type) [Fintype V],card V=n->∀(G:SimpleGraph V),(aM G:ℝ)<=C*Batch.f6 (card V)*card V:=by
  intro n;induction n using jh with
  | h n ih=>
    intro V _ hn G;subst n;have hn0:(0:ℝ)<=card V:=aN _;by_cases iE:(card V:ℝ)<dO
    ·have he:=Bi G
     have hq:(aM G:ℝ)<=eF.cw G:=cq.mpr (eF.rC G);have QG:=aY iE.le hn0;have PI:=aJ (Batch.k7 (card V)).1
      (bZ hC hn0)
     have G3:=aY JI hn0;have hP:=bZ Bg.le hn0;nlinarith only [he,hq,QG,PI,G3,hP]
    ·have QG:dO<=(card V:ℝ):=dF iE
     have hn1:1<(card V:ℝ):=Tt.trans_le QG;let P:eF.aE V:=⟨univ,G,λ _ _ _=>⟨mem_univ _,mem_univ _⟩⟩;have JG:P.vertices.card=card V:=c7;have hp1:1<(P.vertices.card:ℝ):=by simpa only [JG] using hn1
     have hdeg:2*(eF.cw P.graph:ℝ)/P.vertices.card<=P.vertices.card:=by apply (dK (by linarith:(0:ℝ)<P.vertices.card)).mpr;simpa only [JG,P,pow_two] using Bi G
     obtain ⟨H⟩:=Rq dO VR V P (by simpa only [JG] using QG) hdeg;have NB:∀j<H.count,gz vj (H.scale j):=by intro j hj;exact Ts _ (ZT.trans (H.cutoff j hj))
     have gN:∀j<H.count,gz 80 (H.scale j):=by intro j hj;have hh:=NB j hj;exact ⟨hh.u0,(b6 _ _).trans hh.oz,hh.GZ,hh.G0,hh.KD,hh.JE,hh.FQ⟩
     have VS:∀(Q:Type) [Fintype Q] (F:SimpleGraph Q),card Q<P.vertices.card->(aM F:ℝ)<=C*card Q:=by
      intro Q _ F hQ;have hh:=ih (card Q) (by simpa only [JG] using hQ) Q rfl F;have hp:=aJ (Batch.k7 (card Q)).2
       (bZ hC (aN (card Q):(0:ℝ)<=_))
      nlinarith only [hh,hp]
     have Gd:=Tr dO ZR V P H C hC VS;have terminal (hm:eF.bF (eF.cJ H.d4 0 H.count [P])<=2*od*P.vertices.card):(aM G:ℝ)<=C*Batch.f6 (card V)*card V:=by have hh:=H.K3 hp1 gN (9+C*lQ) (Gd H.count dH);have ht:=DK _ P.vertices.card _ C dO (aN _) hC JI hm hh;simpa only [JG,P,<-yi] using ht
     rcases H.K4 with hz | ⟨i,JJ,hi,NC⟩
     ·apply terminal;rw [hz];exact bZ (bZ (by norm_num) Bg.le) (aN _)
     ·by_cases Of:i+200<H.count
      ·let t:=C*Batch.f6 ((H.scale i)^(3/10:ℝ))
       have ht:0<=t:=bZ hC (by linarith [(Batch.k7 ((H.scale i)^(3/10:ℝ))).1]);have Mz:∀(Q:Type) [Fintype Q] (F:SimpleGraph Q),card Q<P.vertices.card->(card Q:ℝ)<=(H.scale i)^(3/10:ℝ)->(aR.af.aM F:ℝ)<=t*card Q:=by
        intro Q _ F hQ VT;have hh:=ih (card Q) (by simpa only [JG] using hQ) Q rfl F;by_cases h0:card Q=0
        ·simpa only [h0,g3,mul_zero,<-FU] using hh
        ·have h1:(1:ℝ)<=card Q:=by exact_mod_cast (by omega:1<=card Q)
         have hp:=Batch.Cu h1 (h1.trans VT) VT;have RD:=aJ hp
          (bZ hC (aN (card Q):(0:ℝ)<=_))
         change (aM F:ℝ)<=C*Batch.f6 ((H.scale i)^(3/10:ℝ))*card Q;nlinarith only [hh,RD]
       have MA:=WT dO ZS V P H hp1 gN i Of C t hC ht VS Mz
        (Gd (i+201) (by omega))
       have Rr:=JH _ P.vertices.card (H.rD i)
        (eF.bF (eF.cJ H.d4 0 (i+201) [P]))
        ((eF.eu H.d4 0 (i+201) [P]).length:ℝ)
        (H.mass (i+201)) (H.mass (i+1)) C t (logb 2 (H.scale i))
        (aN _) (eF.qP _) hC ht
        (by linarith [(gN i JJ).oz])
        (NC (i+201) (by omega) dH) (H.Oq hp1 gN i Of)
        (H.PJ hp1 gN i Of) (H.On (i+1))
        (H.DI hp1 (λ j hj=>(gN j hj).oz) (i+1) (by omega)) MA
       have habs:=Batch.AQ (H.scale i) P.vertices.card (H.rD i)
        C xu t3 (gN i JJ).u0 (eF.yX _ hp1.le i)
        (eF.qP _) hC JA JC Vt
        (by linarith [(gN i JJ).oz])
        ((bC _ _).trans (NB i JJ).oz)
       have Tu:=Rr.trans habs;simpa only [JG,P,<-yi] using Tu
      ·apply terminal
       calc
        _<=od*H.rD i:=NC H.count dH (by omega)
        _<=od*(2*P.vertices.card):=aJ
         (H.KY hp1 (λ j hj=>(gN j hj).oz) i JJ) Bg.le
        _=_:=by ring
 intro V _ G;exact UP (card V) V rfl G
lemma MB:KW:=by
 obtain ⟨C,hC,jF⟩:=JK;refine ⟨C,hC,?_⟩;intro n G;refine ⟨aM G,ov G,?_⟩;have hh:=jF (Fin n) G;simp only [dU] at hh;have hp:=aJ (Batch.k7 n).2
  (bZ hC.le (aN n:(0:ℝ)<=_))
 nlinarith only [hh,hp]
end
end af
end
end
end
end aR
namespace p9
open Filter SimpleGraph
open scoped Classical
private lemma Kn {V:Type*} [Fintype V] (G:SimpleGraph V)
  (s:Set (Sym2 V))
  (h:(∃(v:V) (w:G.Walk v v),w.IsCycle/\s=w.edgeSet)\/∃e∈G.edgeSet,s={e}):
  ∃H:G.Subgraph,Erdos184.IsCycleOrEdge H.coe/\H.edgeSet=s:=by
 classical
 rcases h with ⟨v,w,hw,rfl⟩ | ⟨e,he,rfl⟩
 ·refine ⟨w.toSubgraph,Or.inl ⟨w.toSubgraph_connected.coe,?_⟩,w.edgeSet_toSubgraph⟩;intro x;rw [Subgraph.coe_degree];change Fintype.card (w.toSubgraph.neighborSet (x:V))=2;rw [Set.fintypeCard_eq_ncard];exact hw.ncard_neighborSet_toSubgraph_eq_two ((w.mem_verts_toSubgraph).mp x.property)
 ·induction e using bJ with
  | h a b=>
    let H:=G.subgraphOfAdj he;have hH:H.edgeSet={s(a,b)}:=G.edgeSet_subgraphOfAdj he;refine ⟨H,Or.inr ?_,hH⟩;have O3:=Set.ncard_image_of_injective H.coe.edgeSet
     (fI (f:=Subtype.val) dM)
    rw [H.image_coe_edgeSet_coe,hH,Set.ncard_singleton] at O3;rw [<-Set.ncard_coe_finset,coe_edgeFinset];exact O3.symm
private lemma FX {V:Type*} [Fintype V] (G:SimpleGraph V)
  (k:ℕ) (A:Fin k->Set (Sym2 (Fin (Fintype.card V))))
  (Gd:∀i,(∃(v:Fin (Fintype.card V))
   (w:(G.comap (Fintype.equivFin V).symm).Walk v v),w.IsCycle/\A i=w.edgeSet)\/∃e∈(G.comap (Fintype.equivFin V).symm).edgeSet,A i={e})
  (hdisj:Pairwise λ i j=>Disjoint (A i) (A j))
  (e7:(⋃ i,A i)=(G.comap (Fintype.equivFin V).symm).edgeSet):∃D:Finset G.Subgraph,(∀H∈D,Erdos184.IsCycleOrEdge H.coe)/\G.IsDecomposition D /\D.card<=k:=by
 classical
 let f:=(Fintype.equivFin V).symm;let F:(G.comap f) →g G:=⟨f,λ h=>h⟩;have hf:Function.Injective F:=f.injective;have CQ:Sym2.map F '' (G.comap f).edgeSet=G.edgeSet:=by
  ext e;constructor
  ·rintro ⟨e',he',rfl⟩
   induction e' using bJ with
   | h a b=>exact F.map_adj he'
  ·intro he
   induction e using bJ with
   | h a b=>
     refine ⟨s(f.symm a,f.symm b),?_,?_⟩
     ·change (G.comap f).Adj (f.symm a) (f.symm b);change G.Adj (f (f.symm a)) (f (f.symm b));simpa only [Equiv.apply_symm_apply,ic] using he
     ·simp only [Sym2.map_mk];change s(f (f.symm a),f (f.symm b))=s(a,b);simp
 have PK (i:Fin k):∃H:G.Subgraph,Erdos184.IsCycleOrEdge H.coe/\H.edgeSet=Sym2.map F '' A i:=by
  apply Kn;rcases Gd i with ⟨v,w,hw,ha⟩ | ⟨e,he,ha⟩
  ·refine Or.inl ⟨F v,w.map F,hw.map hf,?_⟩;rw [ha,Walk.edgeSet_map]
  ·refine Or.inr ⟨Sym2.map F e,?_,by simp [ha]⟩;rw [<-CQ];exact ⟨e,he,rfl⟩
 choose H hH Os using PK;refine ⟨Finset.univ.image H,?_,⟨?_,?_⟩,?_⟩
 ·intro J hJ;obtain ⟨i, -,rfl⟩:=bk.mp hJ;exact hH i
 ·intro J hJ K hK hne
  obtain ⟨i, -,rfl⟩:=bk.mp hJ;obtain ⟨j, -,rfl⟩:=bk.mp hK;change Disjoint (H i).edgeSet (H j).edgeSet;rw [Os,Os];exact (l9 (fI hf)).2
   (hdisj (λ eq=>hne (aF H eq)))
 ·calc
   (⋃ J∈(Finset.univ.image H:Finset G.Subgraph),J.edgeSet)=⋃ i,(H i).edgeSet:=by
    ext e;simp only [av,bk,aQ,b5];constructor
    ·rintro ⟨J,⟨i,rfl⟩,he⟩;exact ⟨i,he⟩
    ·rintro ⟨i,he⟩;exact ⟨H i,⟨i,rfl⟩,he⟩
   _=Sym2.map F '' (⋃ i,A i):=by simp_rw [Os,Set.image_iUnion]
   _=G.edgeSet:=by rw [e7,CQ]
 ·simpa using (ju (s:=Finset.univ) (f:=H))
private lemma CR (n:ℕ):∀x:ℝ,x<=n+1->∃m:ℕ,Real.log^[m] x<=1:=by
 induction n with
 | zero=>intro x hx;exact ⟨0,by simpa using hx⟩
 | succ n ih=>
   intro x hx;by_cases h1:x<=1
   ·exact ⟨0,by simpa using h1⟩
   ·have j4:0<x:=by linarith
    have kI:=Real.log_le_sub_one_of_pos j4;obtain ⟨m,hm⟩:=ih (Real.log x) (by push_cast at hx;linarith);exact ⟨m+1,by simpa [Function.iterate_succ_apply] using hm⟩
private lemma FY {x:ℝ} (hx:1<x):1<=Real.iteratedLog x:=by
 obtain ⟨n,hn⟩:=exists_nat_ge (x-1);obtain ⟨m,hm⟩:=CR n x (by linarith);have hmem:Real.iteratedLog x∈{k:ℕ | Real.log^[k] x<=1}:=Nat.sInf_mem ⟨m,hm⟩
 by_contra h;have h0:Real.iteratedLog x=0:=by omega
 rw [h0] at hmem;have hx1:x<=1:=by simpa using hmem
 linarith
end p9
open scoped Classical in
theorem OMA.solution : type_of% @Erdos184.erdos_184.variants.bucic_montgomery := by
 classical
 obtain ⟨C,hC,UQ⟩:=aR.af.MB
 refine ⟨λ n=>C*n,Asymptotics.IsBigO.of_bound C ?_,?_⟩
 ·filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have h1:(1:ℝ)<=(Real.iteratedLog (n:ℝ):ℝ):=by
   have h2:(1:ℝ)<(n:ℝ):=by exact_mod_cast (show 1<n by omega)
   exact_mod_cast p9.FY h2
  have hn0:(0:ℝ)<=(n:ℝ):=aN n
  have QD:0<=C*(n:ℝ):=bZ hC.le hn0
  rw [kg,kg,gk QD,
   gk (bZ hn0 (by linarith))]
  nlinarith [aJ h1 QD]
 ·intro V _ _ G
  obtain ⟨k,⟨A,hA,O4,Tv⟩,hk⟩:=
   UQ (Fintype.card V) (G.comap (Fintype.equivFin V).symm)
  obtain ⟨D,hD,Ko,UR⟩:=
   p9.FX G k A hA O4 Tv
  exact ⟨D,hD,Ko,(cq.mpr UR).trans hk⟩
