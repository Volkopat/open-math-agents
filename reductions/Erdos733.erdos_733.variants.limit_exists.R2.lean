import FormalConjectures.ErdosProblems.«733»
import Mathlib

/-!
# Counting profiles in a window about the square root

Record the multiplicity of each line size in the window and in its complement.
Sizes below the integer fourth root and above the rich-line cutoff have separate
bounded encodings of negligible entropy. The rich-line bound uses only that two
different lines meet in at most one point.
The construction of the finite line set and the finiteness argument are adapted
from the project's merged proof of Erdos733.erdos_733.variants.limit_exists.R1.H1.
-/
-- Credit: @Pixelstorm44
open Erdos733 EuclideanGeometry Finset Filter Topology

namespace OMA.R_Erdos733_erdos_733_variants_limit_exists_R2

/-- Growth of the multiplicity records in each fixed square-root window. -/
def H1 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, Tendsto (fun n : ℕ =>
    let record := fun (X : List ℕ) (x : ℕ) =>
      if n.sqrt ≤ k*x ∧ x ≤ k*n.sqrt then X.count x else 0
    Real.log ((record '' allLinesSequences n).ncard : ℝ) / Real.sqrt n) atTop (𝓝 c)

/-- The intermediate sizes outside a sufficiently wide window have small entropy.
Both extreme ranges have already been paid for in the unconditional encoding. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, 1 ≤ k ∧ ∀ᶠ n : ℕ in atTop,
    let a := n.sqrt.sqrt
    let record := fun (X : List ℕ) (x : ℕ) =>
      if a ≤ x ∧ x ≤ n / (a+1) + a ∧ ¬ (n.sqrt ≤ k*x ∧ x ≤ k*n.sqrt)
      then X.count x else 0
    Real.log ((record '' allLinesSequences n).ncard : ℝ) / Real.sqrt n ≤ ε

section Proof

private noncomputable def through (u v : ℝ²) (hne : u ≠ v) : Line :=
  ⟨affineSpan ℝ {u,v}, ⟨u, left_mem_affineSpan_pair _ _ _⟩, by
    rw [IsLine, direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.mpr hne)⟩

private theorem through_left (u v : ℝ²) (hne : u ≠ v) : u ∈ (through u v hne).val :=
  left_mem_affineSpan_pair _ _ _

private theorem through_right (u v : ℝ²) (hne : u ≠ v) : v ∈ (through u v hne).val :=
  right_mem_affineSpan_pair _ _ _

private theorem eq_through {ℓ : Line} {u v : ℝ²} (hu : u ∈ ℓ.val) (hv : v ∈ ℓ.val) (hne : u ≠ v) :
    ℓ = through u v hne := by
  have hc : Collinear ℝ (ℓ.val : Set ℝ²) := by
    rw [collinear_iff_finrank_le_one, ← direction_affineSpan, AffineSubspace.affineSpan_coe]
    exact ℓ.property.2.le
  apply Subtype.ext
  simp only [through]
  rw [hc.affineSpan_eq_of_ne hu hv hne, AffineSubspace.affineSpan_coe]

open scoped Classical in
private noncomputable def lines (P : Finset ℝ²) : Finset Line :=
  P.offDiag.attach.image (fun uv => through uv.val.1 uv.val.2 (mem_offDiag.mp uv.property).2.2)

private theorem mem_lines {P : Finset ℝ²} {ℓ : Line} : ℓ ∈ lines P ↔ 2 ≤ lineCount P ℓ := by
  classical
  constructor
  · intro h
    obtain ⟨uv, -, rfl⟩ := mem_image.mp h
    obtain ⟨hu,hv,hn⟩ := mem_offDiag.mp uv.property
    unfold lineCount
    exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr
      ⟨uv.val.1, mem_filter.mpr ⟨hu, through_left _ _ _⟩,
        uv.val.2, mem_filter.mpr ⟨hv, through_right _ _ _⟩, hn⟩)
  · intro h
    unfold lineCount at h
    obtain ⟨u,hu,v,hv,hn⟩ := Finset.one_lt_card.mp (show 1 < _ from h)
    obtain ⟨huP,huL⟩ := mem_filter.mp hu
    obtain ⟨hvP,hvL⟩ := mem_filter.mp hv
    exact mem_image.mpr ⟨⟨(u,v), mem_offDiag.mpr ⟨huP,hvP,hn⟩⟩,
      mem_attach _ _, (eq_through huL hvL hn).symm⟩

private theorem card_lines (P : Finset ℝ²) : (lines P).card ≤ P.card*P.card := by
  classical
  calc
    (lines P).card ≤ P.offDiag.card := by unfold lines; exact card_image_le.trans_eq card_attach
    _ ≤ P.card*P.card := by
      rw [← card_product]
      exact card_le_card fun _ h => mem_product.mpr ⟨(mem_offDiag.mp h).1, (mem_offDiag.mp h).2.1⟩

private theorem finite_sequences (n : ℕ) : (allLinesSequences n).Finite := by
  classical
  let W := ⋃ m : Fin (n*n+1), Set.range (fun F : Fin m.val → Fin (n+1) =>
    List.ofFn fun i => (F i).val)
  have hW : W.Finite := by
    unfold W
    exact Set.finite_iUnion fun _ => Set.finite_range _
  apply hW.subset
  intro X hX
  obtain ⟨P,hP,L,hL,rfl⟩ := hX
  have hLe : L = lines P := Finset.ext fun ℓ => (hL ℓ).trans mem_lines.symm
  subst L
  let Y := lineSizeSequence P (lines P)
  have hlen : Y.length ≤ n*n := by
    simpa [Y, lineSizeSequence, lineSizeMultiset, hP] using card_lines P
  let m : Fin (n*n+1) := ⟨Y.length, by omega⟩
  have hvals (a : ℕ) (ha : a ∈ Y) : a ≤ n := by
    simp only [Y, lineSizeSequence, lineSizeMultiset, Multiset.mem_sort, Multiset.mem_map] at ha
    obtain ⟨ℓ,hℓ,rfl⟩ := ha
    rw [← hP]
    exact Finset.card_le_card (filter_subset _ _)
  let F (i : Fin m.val) : Fin (n+1) :=
    ⟨Y[i.val], Nat.lt_succ_of_le (hvals _ (List.getElem_mem _))⟩
  change Y ∈ W
  exact Set.mem_iUnion.mpr ⟨m, ⟨F, List.ofFn_getElem⟩⟩

private theorem profiles_nonempty (n : ℕ) : (allLinesSequences n).Nonempty := by
  obtain ⟨P, hp⟩ := Finset.exists_card_eq (α := ℝ²) n
  exact ⟨lineSizeSequence P (lines P), P, hp, lines P, fun _ => mem_lines, rfl⟩

private theorem profile_bounds {n : ℕ} {X : List ℕ} (hx : X ∈ allLinesSequences n) :
    X.Pairwise (· ≤ ·) ∧ X.length ≤ n*n := by
  obtain ⟨P,hP,L,hL,rfl⟩ := hx
  have he : L = lines P := Finset.ext fun ℓ => (hL ℓ).trans mem_lines.symm
  subst L
  exact ⟨Multiset.pairwise_sort _ _, by
    simpa [lineSizeSequence, lineSizeMultiset, hP] using card_lines P⟩

/-- Above this size, a family of lines has at most `a` members. -/
private def cutoff (n a : ℕ) := n / (a+1) + a

theorem rich_lines_bound (P : Finset ℝ²) (L : Finset Line) (a : ℕ) :
    (L.filter (fun l => cutoff P.card a < lineCount P l)).card ≤ a := by
  classical
  let pts (l : Line) := P.filter (fun p => p ∈ l.val)
  have meet {l m : Line} (hne : l ≠ m) : (pts l ∩ pts m).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    by_contra huv
    obtain ⟨hu₁,hu₂⟩ := Finset.mem_inter.mp hu
    obtain ⟨hv₁,hv₂⟩ := Finset.mem_inter.mp hv
    exact hne ((eq_through (Finset.mem_filter.mp hu₁).2 (Finset.mem_filter.mp hv₁).2 huv).trans
      (eq_through (Finset.mem_filter.mp hu₂).2 (Finset.mem_filter.mp hv₂).2 huv).symm)
  let q := P.card / (a+1) + 1
  have pack (T : Finset Line) (hs : T.card ≤ a+1)
      (hr : ∀ l ∈ T, cutoff P.card a < lineCount P l) :
      T.card * q ≤ (T.biUnion pts).card := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert l T hl ih =>
      rw [Finset.card_insert_of_notMem hl] at hs ⊢
      have old := ih (by omega) (fun m hm => hr m (Finset.mem_insert_of_mem hm))
      have hmeet : (pts l ∩ T.biUnion pts).card ≤ T.card := by
        rw [Finset.inter_biUnion]
        exact (Finset.card_biUnion_le_card_mul T _ 1 fun m hm =>
          meet (l := l) (m := m) (fun h => hl (h.symm ▸ hm))).trans_eq (Nat.mul_one _)
      have rich := hr l (Finset.mem_insert_self _ _)
      change P.card / (a+1) + a < (pts l).card at rich
      have hcard := Finset.card_union_add_card_inter (pts l) (T.biUnion pts)
      rw [Finset.biUnion_insert, Nat.add_mul, Nat.one_mul]
      dsimp [q] at *
      omega
  by_contra! h
  obtain ⟨T,hT,hc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt h)
  have lower := pack T hc.le (fun l hl => (Finset.mem_filter.mp (hT hl)).2)
  have upper : (T.biUnion pts).card ≤ P.card := by
    apply Finset.card_le_card
    intro p hp
    obtain ⟨l,_,hl⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hl).1
  rw [hc] at lower
  exact (Nat.lt_mul_div_succ P.card (Nat.succ_pos a)).not_ge (lower.trans upper)

private def high (n : ℕ) (X : List ℕ) :=
  X.filter (fun x => decide (cutoff n n.sqrt.sqrt < x))

private theorem high_length {n : ℕ} {X : List ℕ} (hx : X ∈ allLinesSequences n) :
    (high n X).length ≤ n.sqrt.sqrt := by
  obtain ⟨P,rfl,L,_,rfl⟩ := hx
  rw [high, ← List.countP_eq_length_filter, ← Multiset.coe_countP, lineSizeSequence,
    Multiset.sort_eq, lineSizeMultiset, Multiset.countP_map]
  exact rich_lines_bound P L _

private theorem value_bound {n : ℕ} {X : List ℕ} (hx : X ∈ allLinesSequences n)
    {x : ℕ} (h : x ∈ X) : x ≤ n := by
  classical
  obtain ⟨P,rfl,L,_,rfl⟩ := hx
  simp only [lineSizeSequence,lineSizeMultiset,Multiset.mem_sort,Multiset.mem_map] at h
  obtain ⟨l,_,rfl⟩ := h
  exact Finset.card_filter_le _ _

private def highCode (n : ℕ) (X : List ℕ) (i : Fin n.sqrt.sqrt) : Option (Fin (n+1)) :=
  (high n X)[i.val]?.map (fun x => ⟨min x n, Nat.lt_succ_of_le (min_le_right _ _)⟩)

private theorem high_decode {n : ℕ} {X : List ℕ} (hx : X ∈ allLinesSequences n)
    (i : Fin n.sqrt.sqrt) : (highCode n X i).map Fin.val = (high n X)[i.val]? := by
  cases h : (high n X)[i.val]? with
  | none => simp [highCode,h]
  | some x =>
    obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp h
    have hm : x ∈ high n X := he ▸ List.getElem_mem hi
    simp [highCode, h, min_eq_left (value_bound hx (List.mem_filter.mp hm).1)]

private def window (k n x : ℕ) : Prop := n.sqrt ≤ k*x ∧ x ≤ k*n.sqrt

private instance (k n x : ℕ) : Decidable (window k n x) := by unfold window; infer_instance

private def band (k n : ℕ) (X : List ℕ) (x : ℕ) : ℕ :=
  if window k n x then X.count x else 0

private def tail (k n : ℕ) (X : List ℕ) (x : ℕ) : ℕ :=
  if n.sqrt.sqrt ≤ x ∧ x ≤ cutoff n n.sqrt.sqrt ∧ ¬ window k n x then X.count x else 0

private noncomputable def rate (n m : ℕ) : ℝ := Real.log (m : ℝ) / Real.sqrt n



private def low (n : ℕ) (X : List ℕ) (i : Fin n.sqrt.sqrt) : Fin (n*n+1) :=
  ⟨min (X.count i.val) (n*n), Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem profile_count_bound (k n : ℕ) :
    (allLinesSequences n).ncard ≤
      (n*n+2)^(2*n.sqrt.sqrt) * ((band k n '' allLinesSequences n).ncard *
        (tail k n '' allLinesSequences n).ncard) := by
  classical
  let U := (Set.univ : Set ((Fin n.sqrt.sqrt → Fin (n*n+1)) × (Fin n.sqrt.sqrt → Option (Fin (n+1))))) ×ˢ
    ((band k n '' allLinesSequences n) ×ˢ (tail k n '' allLinesSequences n))
  let enc (X : List ℕ) := ((low n X, highCode n X), band k n X, tail k n X)
  have maps : ∀ X ∈ allLinesSequences n, enc X ∈ U := fun X h =>
    ⟨Set.mem_univ _, Set.mem_image_of_mem _ h, Set.mem_image_of_mem _ h⟩
  have inj : Set.InjOn enc (allLinesSequences n) := by
    intro X hx Y hy he
    obtain ⟨hsx, hlx⟩ := profile_bounds hx
    obtain ⟨hsy, hly⟩ := profile_bounds hy
    apply List.Perm.eq_of_pairwise' hsx hsy
    apply List.perm_iff_count.mpr
    intro x
    by_cases hw : window k n x
    · simpa [enc, band, hw] using congrArg (fun z => z.2.1 x) he
    by_cases hh : cutoff n n.sqrt.sqrt < x
    · have eqhigh : high n X = high n Y := by
        apply List.ext_getElem?
        intro j
        by_cases hj : j < n.sqrt.sqrt
        · let i : Fin n.sqrt.sqrt := ⟨j,hj⟩
          exact (high_decode hx i).symm.trans ((congrArg (fun z => (z.1.2 i).map Fin.val) he).trans
            (high_decode hy i))
        · rw [List.getElem?_eq_none (by have := high_length hx; omega),
              List.getElem?_eq_none (by have := high_length hy; omega)]
      have hc := congrArg (List.count x) eqhigh
      have hp : (fun t => decide (cutoff n n.sqrt.sqrt < t)) x = true := by simp [hh]
      unfold high at hc
      simpa only [List.count_filter (p := fun t : ℕ => decide (cutoff n n.sqrt.sqrt < t))
        (a := x) hp] using hc
    by_cases h : n.sqrt.sqrt ≤ x
    · simpa [enc, tail, h, hw, Nat.le_of_not_gt hh] using congrArg (fun z => z.2.2 x) he
    let i : Fin n.sqrt.sqrt := ⟨x, by omega⟩
    have h1 : X.count x ≤ n*n := List.count_le_length.trans hlx
    have h2 : Y.count x ≤ n*n := List.count_le_length.trans hly
    simpa [enc, low, i, min_eq_left h1, min_eq_left h2] using
      congrArg (fun z => (z.1.1 i).val) he
  have hu : U.Finite := Set.finite_univ.prod
    (((finite_sequences n).image _).prod ((finite_sequences n).image _))
  have raw := Set.ncard_le_ncard_of_injOn enc maps inj hu
  simp [U, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card] at raw
  apply raw.trans
  apply Nat.mul_le_mul_right
  rw [two_mul, pow_add]
  apply Nat.mul_le_mul <;> apply Nat.pow_le_pow_left <;> have := Nat.le_mul_self n <;> omega

private noncomputable def cost (n : ℕ) : ℝ :=
  (2*(n.sqrt.sqrt : ℝ)) * Real.log ((n:ℝ)*n+2) / Real.sqrt n

private theorem rate_bounds (k n : ℕ) :
    rate n ((band k n '' allLinesSequences n).ncard) ≤ rate n (allLinesSequences n).ncard ∧
    rate n (allLinesSequences n).ncard ≤ rate n ((band k n '' allLinesSequences n).ncard)
      + rate n ((tail k n '' allLinesSequences n).ncard) + cost n := by
  have hf := (Set.ncard_pos (finite_sequences n)).mpr (profiles_nonempty n)
  have hb := (Set.ncard_pos ((finite_sequences n).image (band k n))).mpr
    ((profiles_nonempty n).image _)
  have ht := (Set.ncard_pos ((finite_sequences n).image (tail k n))).mpr
    ((profiles_nonempty n).image _)
  constructor
  · apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply Real.log_le_log (by exact_mod_cast hb)
    exact_mod_cast Set.ncard_image_le (f := band k n) (finite_sequences n)
  · rw [rate, rate, rate, cost, ← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have h := Real.log_le_log (by exact_mod_cast hf : (0:ℝ) < ((allLinesSequences n).ncard : ℝ))
      (Nat.cast_le (α := ℝ) |>.mpr (profile_count_bound k n))
    push_cast at h
    have hb' : ((band k n '' allLinesSequences n).ncard : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have ht' : ((tail k n '' allLinesSequences n).ncard : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [Real.log_mul (by positivity) (mul_ne_zero hb' ht'), Real.log_pow,
      Real.log_mul hb' ht'] at h
    push_cast at h
    linarith

theorem cost_vanishes : Tendsto cost atTop (𝓝 0) := by
  have hlog := ((isLittleO_log_rpow_atTop (r := (1/4:ℝ)) (by norm_num)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have upper : Tendsto (fun n : ℕ => 6 * (Real.log n / (n:ℝ)^(1/4:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (6:ℝ))).mul hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper
  · filter_upwards with n
    unfold cost
    apply div_nonneg _ (Real.sqrt_nonneg _)
    exact mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith [sq_nonneg (n:ℝ)]))
  · filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hp : 0 < (n:ℝ) := by linarith
    have hq : 0 < (n:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos hp _
    have hs (m : ℕ) : (m.sqrt:ℝ) ≤ Real.sqrt m :=
      Real.le_sqrt_of_sq_le (by simpa [pow_two] using (Nat.cast_le (α := ℝ)).mpr (Nat.sqrt_le m))
    have h4 : (n.sqrt.sqrt:ℝ) ≤ (n:ℝ)^(1/4:ℝ) := by
      calc
        _ ≤ Real.sqrt (Real.sqrt n) := (hs _).trans (Real.sqrt_le_sqrt (hs n))
        _ = _ := by rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hp.le]; norm_num
    have hcube : (n:ℝ)*n+2 ≤ (n:ℝ)^3 := by nlinarith [mul_nonneg (sq_nonneg (n:ℝ)) (show 0 ≤ (n:ℝ)-2 by linarith), sq_nonneg ((n:ℝ)-1)]
    have hl := Real.log_le_log (by positivity) hcube
    rw [Real.log_pow] at hl
    have hden : Real.sqrt n = (n:ℝ)^(1/4:ℝ) * (n:ℝ)^(1/4:ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]; norm_num
    rw [cost, hden]
    calc
      _ ≤ ((2*(n:ℝ)^(1/4:ℝ)) * (3 * Real.log n)) / _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul (mul_le_mul_of_nonneg_left h4 (by norm_num)) _ (Real.log_nonneg (by nlinarith [sq_nonneg (n:ℝ)])) (by positivity)
        simpa using hl
      _ = _ := by field_simp; ring

theorem main : H1 → H2 → type_of% @Erdos733.erdos_733.variants.limit_exists := by
  intro hwin htail
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have he : 0 < ε / 5 := by linarith
  obtain ⟨k, hk, ht⟩ := htail _ he
  obtain ⟨c, hc⟩ := hwin k hk
  change Tendsto (fun n => rate n ((band k n '' allLinesSequences n).ncard)) atTop (𝓝 c) at hc
  change ∀ᶠ n in atTop, rate n ((tail k n '' allLinesSequences n).ncard) ≤ ε / 5 at ht
  have hw := (Metric.tendsto_nhds.mp hc) _ he
  have hcost := cost_vanishes.eventually (gt_mem_nhds he)
  have approx : ∀ᶠ n : ℕ in atTop,
      c - ε/5 < rate n (allLinesSequences n).ncard ∧
      rate n (allLinesSequences n).ncard < c + 3*(ε/5) := by
    filter_upwards [ht,hw,hcost] with n ht' hw' hcost'
    rw [Real.dist_eq, abs_lt] at hw'
    obtain ⟨hl,hu⟩ := rate_bounds k n
    change cost n < ε / 5 at hcost'
    constructor <;> linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp approx
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  change -ε < rate m (allLinesSequences m).ncard - rate n (allLinesSequences n).ncard ∧ _
  obtain ⟨hm₁,hm₂⟩ := hN m hm
  obtain ⟨hn₁,hn₂⟩ := hN n hn
  change _ ∧ rate m (allLinesSequences m).ncard - rate n (allLinesSequences n).ncard < ε
  constructor <;> linarith

end Proof

end OMA.R_Erdos733_erdos_733_variants_limit_exists_R2
