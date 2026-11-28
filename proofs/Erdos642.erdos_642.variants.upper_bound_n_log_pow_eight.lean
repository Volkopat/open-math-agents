import FormalConjectures.ErdosProblems.«642»
import Mathlib

/-!
Erdős 642: the logarithmic density bound for cycles with many chords.

The proof follows Draganić, Methuku, Munhá Correia, and Sudakov, arXiv:2306.09157.
The probabilistic argument uses finite transition weights on a common trace space,
with the bipartite mixing bound applied at compatible parities. An odd base stride
allows the even-stride sample banks to stay on their respective sides while both
banks contribute edges in the same residue class of the full walk.

The prior coarse extremal upper bound is from @senamakel's merged proof of the
three-halves-power variant and is used to justify the floor in the number of stars.
-/

section Erdos642ReductionFile

/- The regular-expander reduction for the upper bound on Erdős Problem 642. -/

namespace Erdos642

open SimpleGraph

variable {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}

theorem isChord_map (f : H →g G) (hf : Function.Injective f)
    {u v : V} (c : H.Walk u v) (e : Sym2 V) :
    c.IsChord e → (c.map f).IsChord (Sym2.map f e) := by
  refine Sym2.inductionOn e ?_
  intro a b he
  obtain ⟨hab, hn, ha, hb⟩ := Walk.isChord_sym2Mk.mp he
  rw [Sym2.map_mk, Walk.isChord_sym2Mk]
  refine ⟨f.map_adj hab, ?_, ?_, ?_⟩
  · rw [Walk.edges_map]
    intro hedges
    obtain ⟨e', he', heq⟩ := List.mem_map.mp hedges
    have heq' : e' = s(a, b) := Sym2.map.injective hf (heq.trans (Sym2.map_mk f a b).symm)
    exact hn (heq' ▸ he')
  · rw [Walk.support_map]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  · rw [Walk.support_map]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩

private theorem finite_chords {u v : W} (c : G.Walk u v) :
    {e : Sym2 W | c.IsChord e}.Finite := by
  refine c.support.sym2.finite_toSet.subset ?_
  intro e
  refine Sym2.inductionOn e ?_
  intro a b he
  obtain ⟨_, _, ha, hb⟩ := Walk.isChord_sym2Mk.mp he
  exact List.mk_mem_sym2 ha hb

theorem cyclesHaveMoreVerticesThanChords_of_injective_hom
    (f : H →g G) (hf : Function.Injective f)
    (hG : CyclesHaveMoreVerticesThanChords G) : CyclesHaveMoreVerticesThanChords H := by
  intro v c hc
  have hcard : {e : Sym2 V | c.IsChord e}.ncard ≤
      {e : Sym2 W | (c.map f).IsChord e}.ncard :=
    Set.ncard_le_ncard_of_injOn (Sym2.map f) (isChord_map f hf c)
      (Sym2.map.injective hf).injOn (finite_chords (c.map f))
  have hlt := hG (f v) (c.map f) (hc.map hf)
  rw [Walk.length_map] at hlt
  exact hcard.trans_lt hlt

end Erdos642

namespace OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1

open Filter Asymptotics

/-- The almost-regular bipartite expander extracted in DMMS24, Lemma 2.4. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
    Real.log n ^ 2 ≤ 2 * (G.edgeSet.ncard : ℝ) / n →
      ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ ∃ H : SimpleGraph (Fin m), ∃ f : H →g G,
        Function.Injective f ∧ H.IsBipartite ∧
        (∀ u v : Fin m, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) ∧
        (2 * (G.edgeSet.ncard : ℝ) / n) / (600 * Real.log n) ≤
          2 * (H.edgeSet.ncard : ℝ) / m ∧
        (∀ S : Finset (Fin m), 2 * S.card ≤ m →
          (1 / (10 * Real.log n)) * (2 * (H.edgeSet.ncard : ℝ) / m) * S.card ≤
            ({e ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}.ncard : ℝ))

/-- The random-walk argument in DMMS24, Section 3, restricted to the extracted graphs. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ n → ∀ H : SimpleGraph (Fin m),
    H.IsBipartite →
    (∀ u v : Fin m, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) →
    Real.log n ^ 7 / 600 ≤ 2 * (H.edgeSet.ncard : ℝ) / m →
    (∀ S : Finset (Fin m), 2 * S.card ≤ m →
      (1 / (10 * Real.log n)) * (2 * (H.edgeSet.ncard : ℝ) / m) * S.card ≤
        ({e ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}.ncard : ℝ)) →
    ¬ Erdos642.CyclesHaveMoreVerticesThanChords H

theorem main : H1 → H2 → type_of% @Erdos642.erdos_642.variants.upper_bound_n_log_pow_eight := by
  intro hextract hforce
  have hnlarge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [hextract, hforce, hnlarge, eventually_ge_atTop (1 : ℕ)]
    with n hclean hcycle hlog hn
  simp only [Real.norm_natCast, Real.norm_of_nonneg (show 0 ≤ (n : ℝ) * Real.log n ^ 8 by positivity),
    one_mul]
  obtain ⟨G, hG, hm⟩ := Erdos642.exists_maxEdges n
  rw [← hm]
  by_contra! hedges
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hlogPos : 0 < Real.log n := zero_lt_one.trans_le hlog
  have hratio : Real.log n ^ 8 ≤ (G.edgeSet.ncard : ℝ) / n :=
    (le_div_iff₀ hnpos).mpr (by simpa only [mul_comm] using hedges.le)
  have havg : Real.log n ^ 8 ≤ 2 * (G.edgeSet.ncard : ℝ) / n :=
    hratio.trans (div_le_div_of_nonneg_right
      (by linarith only [show 0 ≤ (G.edgeSet.ncard : ℝ) by positivity]) hnpos.le)
  have hpow : Real.log n ^ 2 ≤ Real.log n ^ 8 := pow_le_pow_right₀ hlog (by decide)
  obtain ⟨m, hmpos, hmle, H, f, hf, hbp, hreg, hd, hexp⟩ := hclean G (hpow.trans havg)
  have hnormalize : Real.log n ^ 8 / (600 * Real.log n) = Real.log n ^ 7 / 600 := by
    field_simp [hlogPos.ne']
  have hdegree : Real.log n ^ 7 / 600 ≤ 2 * (H.edgeSet.ncard : ℝ) / m := by
    rw [← hnormalize]
    exact (div_le_div_of_nonneg_right havg (by positivity : 0 ≤ 600 * Real.log n)).trans hd
  exact hcycle m hmpos hmle H hbp hreg hdegree hexp (Erdos642.cyclesHaveMoreVerticesThanChords_of_injective_hom f hf hG)

end OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1

end Erdos642ReductionFile

section Erdos642ExtractionFile

/-
# Erdős 642: dense bipartite expander extraction

Take a half-edge cut, use nested matchings to regularize one bipartite subgraph,
and select a minimum-size induced slice meeting a logarithmic density threshold.
The final slice retains the required average degree and expansion.

Sources: Draganić, Methuku, Munhá Correia, and Sudakov, arXiv:2306.09157,
Lemma 2.4, and Bucić et al., arXiv:1809.01468, for the nested-matching argument.
Credit: @justusklocke-cloud
-/


/- A logarithmic density threshold for extracting an expanding induced subgraph. -/

namespace Erdos642DensityIncrement

open Finset

variable {V : Type*} [DecidableEq V]

private noncomputable def threshold (N m : ℕ) : ℝ :=
  (1 + Real.log m / Real.log N) / 2

private theorem threshold_bounds {N m : ℕ} (hN : 0 < Real.log N) (hm : 0 < m) (hmN : m ≤ N) :
    1 / 2 ≤ threshold N m ∧ threshold N m ≤ 1 := by
  have hA : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hB : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have h₁ := div_nonneg (Real.log_nonneg hA) hN.le
  have h₂ : Real.log m / Real.log N ≤ 1 := (div_le_iff₀ hN).mpr
    (by simpa only [one_mul] using Real.log_le_log (show (0 : ℝ) < m by positivity) hB)
  exact ⟨by unfold threshold; linarith only [h₁], by unfold threshold; linarith only [h₂]⟩

private theorem threshold_mono {N u s : ℕ} (hN : 0 < Real.log N) (hu : 0 < u) (hus : u ≤ s) :
    threshold N u ≤ threshold N s := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hus' : (u : ℝ) ≤ s := by exact_mod_cast hus
  have he := div_le_div_of_nonneg_right (Real.log_le_log hu' hus') hN.le
  unfold threshold
  linarith only [he]

private theorem threshold_half {N u s : ℕ}
    (hN : 0 < Real.log N) (hu : 0 < u) (hus : 2 * u ≤ s) (hsN : s ≤ N) :
    threshold N u ≤ (1 - 2 * (1 / (10 * Real.log N))) * threshold N s := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hprod : (2 : ℝ) * u ≤ s := by exact_mod_cast hus
  have he := Real.log_le_log (show (0 : ℝ) < 2 * u by positivity) hprod
  rw [Real.log_mul (by norm_num) hu'.ne'] at he
  have hlog2 : (2 / 5 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    linarith only [h]
  have hlogDiff : (2 / 5 : ℝ) ≤ Real.log s - Real.log u := by linarith only [he,hlog2]
  have hd := div_le_div_of_nonneg_right hlogDiff hN.le
  rw [sub_div] at hd
  have hgap : 2 * (1 / (10 * Real.log N)) ≤ threshold N s - threshold N u := by
    have heq : 2 * (1 / (10 * Real.log N)) = ((2 / 5) / Real.log N) / 2 := by
      field_simp
      ring
    rw [heq]
    unfold threshold
    linarith only [hd]
  have hS := (threshold_bounds hN (show 0 < s by omega) hsN).2
  have hlow := mul_le_mul_of_nonneg_left hS (show 0 ≤ 2 * (1 / (10 * Real.log N)) by positivity)
  linarith only [hgap,hlow]

/-- A nonempty minimal set satisfying a logarithmic density threshold has
minimum degree at least half its average and the stated edge expansion. -/
theorem exists_expanding_subset (A : Finset V) (edges : Finset V → ℝ)
    (degree : Finset V → V → ℝ) (cut : Finset V → Finset V → ℝ)
    {N : ℕ} (hN : 1 ≤ Real.log N) (hAN : A.card ≤ N) (hA : A.Nonempty)
    (hEdges : 0 < edges A)
    (hOne : ∀ v, edges {v} = 0)
    (hErase : ∀ S ⊆ A, ∀ v ∈ S, edges S = edges (S.erase v) + degree S v)
    (hSplit : ∀ S ⊆ A, ∀ U ⊆ S, edges S = edges U + edges (S \ U) + cut S U)
    (hEmptyCut : ∀ S ⊆ A, cut S ∅ = 0) :
    ∃ S ⊆ A, S.Nonempty ∧
      let avg := 2 * edges S / (S.card : ℝ)
      (2 * edges A / (A.card : ℝ)) / 2 ≤ avg ∧
      (∀ v ∈ S, avg / 2 ≤ degree S v) ∧
      (∀ U ⊆ S, 2 * U.card ≤ S.card →
        (1 / (10 * Real.log N)) * avg * (U.card : ℝ) ≤ cut S U) := by
  classical
  let d := 2 * edges A / (A.card : ℝ)
  let ρ := 1 / (10 * Real.log N)
  have hL : 0 < Real.log N := by linarith only [hN]
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ₂ : 0 ≤ 1 - 2 * ρ := by
    have h := (div_le_iff₀ (show (0 : ℝ) < 10 * Real.log N by positivity)).mpr
      (show 1 ≤ (1 / 2 : ℝ) * (10 * Real.log N) by linarith only [hN])
    change ρ ≤ (1 / 2 : ℝ) at h
    linarith only [h]
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hd : 0 < d := by dsimp [d]; positivity
  let D : Finset (Finset V) := A.powerset.filter fun S =>
    S.Nonempty ∧ ((S.card : ℝ) * (threshold N S.card * d) ≤ 2 * edges S)
  have hDin : A ∈ D := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (subset_refl _),hA,?_⟩
    have h := mul_le_mul_of_nonneg_right (threshold_bounds hL hA.card_pos hAN).2 hd.le
    calc
      _ ≤ (A.card : ℝ) * d := mul_le_mul_of_nonneg_left (by simpa only [one_mul] using h) hApos.le
      _ = _ := by dsimp only [d]; field_simp
  obtain ⟨S,hSD,hMin⟩ := Finset.exists_min_image D Finset.card ⟨A,hDin⟩
  obtain ⟨hSA,hS,hST⟩ := mem_filter.mp hSD
  have hSA' := mem_powerset.mp hSA
  let avg := 2 * edges S / (S.card : ℝ)
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hS0 : 1 < S.card := by
    by_contra! h
    have hScard : S.card = 1 := Nat.le_antisymm h hS.card_pos
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hScard
    have hw := (threshold_bounds hL hS.card_pos ((card_le_card hSA').trans hAN)).1
    have hwPos : 0 < threshold N S.card := by linarith only [hw]
    have hp : 0 < (S.card : ℝ) * (threshold N S.card * d) := by positivity
    have hES : edges S = 0 := hv ▸ hOne v
    rw [hES] at hST
    linarith only [hp,hST]
  have hAvgT : threshold N S.card * d ≤ avg :=
    (le_div_iff₀ hSc).mpr (by simpa only [mul_comm] using hST)
  have hAvg : d / 2 ≤ avg := by
    have h := mul_le_mul_of_nonneg_right
      (threshold_bounds hL hS.card_pos ((card_le_card hSA').trans hAN)).1 hd.le
    exact (by linarith only [h] : d / 2 ≤ threshold N S.card * d).trans hAvgT
  have hEq : (S.card : ℝ) * avg = 2 * edges S := by dsimp [avg]; field_simp
  have hFail (T : Finset V) (hTS : T ⊆ S) (hT : T.Nonempty) (hTlt : T.card < S.card) :
      2 * edges T < (T.card : ℝ) * (threshold N T.card * d) := by
    by_contra! hb
    exact (not_le_of_gt hTlt) (hMin T (mem_filter.mpr
      ⟨mem_powerset.mpr (hTS.trans hSA'), hT, hb⟩))
  refine ⟨S,hSA',hS,hAvg,?_,?_⟩
  · intro v hv
    by_contra! hdeg
    let T := S.erase v
    have hTc : T.card = S.card - 1 := card_erase_of_mem hv
    have hT : T.Nonempty := card_pos.mp (by omega)
    have hTlt : T.card < S.card := by omega
    have hF := hFail T (erase_subset _ _) hT hTlt
    have hM := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right (threshold_mono hL hT.card_pos hTlt.le) hd.le).trans hAvgT)
      (Nat.cast_nonneg T.card)
    have hTcR : (T.card : ℝ) = (S.card : ℝ) - 1 := by
      rw [hTc,Nat.cast_sub (by omega : 1 ≤ S.card),Nat.cast_one]
    have hE := hErase S hSA' v hv
    change edges S = edges T + degree S v at hE
    rw [hTcR] at hM hF
    linarith only [hF,hM,hE,hEq,hdeg]
  · intro U hUS hUhalf
    change ρ * avg * (U.card : ℝ) ≤ cut S U
    by_cases hU : U.Nonempty
    swap
    · have hz : U = ∅ := not_nonempty_iff_eq_empty.mp hU
      rw [hz,hEmptyCut S hSA']
      simp
    by_contra! hbad
    let W := S \ U
    have hCardW : W.card = S.card - U.card := card_sdiff_of_subset hUS
    have hW : W.Nonempty := card_pos.mp (by have := hU.card_pos; omega)
    have hUlt : U.card < S.card := by have := hU.card_pos; omega
    have hWlt : W.card < S.card := by have := hU.card_pos; omega
    have hWc : (W.card : ℝ) = (S.card : ℝ) - (U.card : ℝ) := by
      rw [hCardW,Nat.cast_sub hUlt.le]
    have hUF := hFail U hUS hU hUlt
    have hWF := hFail W sdiff_subset hW hWlt
    have hWt := (mul_le_mul_of_nonneg_right (threshold_mono hL hW.card_pos hWlt.le) hd.le).trans hAvgT
    have hUt : threshold N U.card * d ≤ (1 - 2 * ρ) * avg := by
      calc
        _ ≤ ((1 - 2 * ρ) * threshold N S.card) * d :=
          mul_le_mul_of_nonneg_right (threshold_half hL hU.card_pos hUhalf
            ((card_le_card hSA').trans hAN)) hd.le
        _ = (1 - 2 * ρ) * (threshold N S.card * d) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hAvgT hρ₂
    have hWL := hWF.trans_le (mul_le_mul_of_nonneg_left hWt (Nat.cast_nonneg W.card))
    have hUL := hUF.trans_le (mul_le_mul_of_nonneg_left hUt (Nat.cast_nonneg U.card))
    have hSum := hSplit S hSA' U hUS
    change edges S = edges U + edges W + cut S U at hSum
    rw [hWc] at hWL
    linarith only [hWL,hUL,hSum,hEq,hbad]

end Erdos642DensityIncrement



/- Edge, boundary and degree counts for a finite induced graph. -/

namespace Erdos642InducedCounts

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def internalEdges (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset ∩ S.sym2

def degreeWithin (S : Finset V) (v : V) : ℕ :=
  (G.neighborFinset v ∩ S).card

noncomputable def cutEdges (S U : Finset V) : Finset (Sym2 V) := by
  classical
  exact (internalEdges G S).filter
    (fun e => ∃ a ∈ U, ∃ b ∈ S \ U, e = s(a,b))

@[simp] theorem mk_mem_internalEdges {S : Finset V} {a b : V} :
    s(a,b) ∈ internalEdges G S ↔ G.Adj a b ∧ a ∈ S ∧ b ∈ S := by
  rw [internalEdges,mem_inter,mem_edgeFinset,mem_edgeSet,Finset.mk_mem_sym2_iff]

@[simp] theorem mk_mem_cutEdges {S U : Finset V} {a b : V} :
    s(a,b) ∈ cutEdges G S U ↔ G.Adj a b ∧ a ∈ S ∧ b ∈ S ∧
      ((a ∈ U ∧ b ∉ U) ∨ (b ∈ U ∧ a ∉ U)) := by
  constructor
  · intro h
    obtain ⟨hS,x,hx,y,hy,heq⟩ := mem_filter.mp h
    obtain ⟨he,ha,hb⟩ := (mk_mem_internalEdges G).mp hS
    refine ⟨he,ha,hb,?_⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨hx,(mem_sdiff.mp hy).2⟩
    · exact Or.inr ⟨hx,(mem_sdiff.mp hy).2⟩
  · rintro ⟨he,ha,hb,h⟩
    refine mem_filter.mpr ⟨(mk_mem_internalEdges G).mpr ⟨he,ha,hb⟩,?_⟩
    rcases h with ⟨haU,hbU⟩ | ⟨hbU,haU⟩
    · exact ⟨a,haU,b,mem_sdiff.mpr ⟨hb,hbU⟩,rfl⟩
    · exact ⟨b,hbU,a,mem_sdiff.mpr ⟨ha,haU⟩,Sym2.eq_swap⟩

@[simp] theorem internal_edges_empty : internalEdges G ∅ = ∅ := by
  ext e
  induction e using Sym2.inductionOn with
  | hf a b => simp [mk_mem_internalEdges]

@[simp] theorem internal_edges_singleton (v : V) : internalEdges G {v} = ∅ := by
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
    simp only [mk_mem_internalEdges,mem_singleton,notMem_empty,iff_false]
    rintro ⟨he,rfl,rfl⟩
    exact G.ne_of_adj he rfl

@[simp] theorem cut_edges_empty (S : Finset V) : cutEdges G S ∅ = ∅ := by
  ext e
  induction e using Sym2.inductionOn with
  | hf a b => simp [mk_mem_cutEdges]

theorem internal_edges_split {S U : Finset V} (hU : U ⊆ S) :
    internalEdges G S = (internalEdges G U ∪ internalEdges G (S \ U)) ∪ cutEdges G S U := by
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
    have ha : a ∈ U → a ∈ S := fun hm => hU hm
    have hb : b ∈ U → b ∈ S := fun hm => hU hm
    simp only [mk_mem_internalEdges,mk_mem_cutEdges,mem_union,mem_sdiff]
    tauto

theorem card_internalEdges_split {S U : Finset V} (hU : U ⊆ S) :
    (internalEdges G S).card =
      (internalEdges G U).card + (internalEdges G (S \ U)).card + (cutEdges G S U).card := by
  classical
  have hUD : Disjoint (internalEdges G U) (internalEdges G (S \ U)) := by
    rw [Finset.disjoint_left]
    intro e hA hB
    induction e using Sym2.inductionOn with
    | hf a b =>
      exact (mem_sdiff.mp ((mk_mem_internalEdges G).mp hB).2.1).2 ((mk_mem_internalEdges G).mp hA).2.1
  have hCut : Disjoint (internalEdges G U ∪ internalEdges G (S \ U)) (cutEdges G S U) := by
    rw [Finset.disjoint_left]
    intro e hA hB
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp only [mem_union,mk_mem_internalEdges,mem_sdiff] at hA
      simp only [mk_mem_cutEdges] at hB
      tauto
  rw [internal_edges_split G hU,card_union_of_disjoint hCut,card_union_of_disjoint hUD]

theorem cut_edges_singleton {S : Finset V} {v : V} (hv : v ∈ S) :
    cutEdges G S {v} = (G.neighborFinset v ∩ S).map (Sym2.mkEmbedding v) := by
  ext e
  constructor
  · intro h
    obtain ⟨hS,x,hx,y,hy,rfl⟩ := mem_filter.mp h
    rw [mem_singleton] at hx
    subst x
    have hadj := ((mk_mem_internalEdges G).mp hS).1
    exact mem_map.mpr ⟨y,mem_inter.mpr ⟨(mem_neighborFinset G v y).mpr hadj,(mem_sdiff.mp hy).1⟩,rfl⟩
  · intro he
    obtain ⟨y,hy,rfl⟩ := mem_map.mp he
    obtain ⟨hyG,hyS⟩ := mem_inter.mp hy
    have hadj := (mem_neighborFinset G v y).mp hyG
    exact (mk_mem_cutEdges G).mpr ⟨hadj,hv,hyS,Or.inl
      ⟨mem_singleton_self _, by simpa only [mem_singleton] using G.ne_of_adj hadj |>.symm⟩⟩

theorem card_internalEdges_erase {S : Finset V} {v : V} (hv : v ∈ S) :
    (internalEdges G S).card = (internalEdges G (S.erase v)).card + degreeWithin G S v := by
  have h := card_internalEdges_split G (singleton_subset_iff.mpr hv)
  rw [internal_edges_singleton,card_empty,zero_add,cut_edges_singleton G hv,card_map,
    sdiff_singleton_eq_erase] at h
  exact h

theorem card_induced_edges (S : Finset V) :
    ((G.induce (S : Set V)).edgeFinset).card = (internalEdges G S).card := by
  have h := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce (G := G) (s := (S : Set V)))
  simp only [card_map,Finset.toFinset_coe] at h
  change _ = (internalEdges G S).card at h
  convert h using 2
  ext e
  simp only [mem_edgeFinset]

theorem degree_induced (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v = degreeWithin G S v.val := by
  have h := congrArg Finset.card (SimpleGraph.map_neighborFinset_induce (G := G) (s := (S : Set V)) v)
  simp only [card_map,Finset.toFinset_coe] at h
  change _ = degreeWithin G S v.val at h
  rw [← card_neighborFinset_eq_degree]
  convert h using 2
  ext x
  simp only [mem_neighborFinset]

theorem degree_within_le (S : Finset V) (v : V) : degreeWithin G S v ≤ G.degree v :=
  (card_le_card inter_subset_left).trans_eq (card_neighborFinset_eq_degree G v)

end Erdos642InducedCounts



/- Nested matchings for the regularization lemma of Bucić, Kwan, Pokrovskiy,
Sudakov, Tran and Wagner. -/

namespace Erdos642AlmostRegular

open Finset

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

def row (F : Finset (X × Y)) (x : X) : Finset Y :=
  (F.filter (fun e => e.1 = x)).image Prod.snd

def columns (F : Finset (X × Y)) (S : Finset X) : Finset Y :=
  S.biUnion (row F)

@[simp] theorem mem_row {F : Finset (X × Y)} {x : X} {y : Y} :
    y ∈ row F x ↔ (x, y) ∈ F := by
  simp only [row, mem_image, mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hab, rfl⟩, rfl⟩
    exact hab
  · intro h
    exact ⟨x, y, ⟨h, rfl⟩, rfl⟩

@[simp] theorem mem_columns {F : Finset (X × Y)} {S : Finset X} {y : Y} :
    y ∈ columns F S ↔ ∃ x ∈ S, (x, y) ∈ F := by
  simp [columns]

theorem columns_mono {F G : Finset (X × Y)} {S T : Finset X}
    (hG : G ⊆ F) (hS : S ⊆ T) : columns G S ⊆ columns F T := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_columns.mp hy
  exact mem_columns.mpr ⟨x, hS hx, hG hxy⟩

/-- A single matching between its two endpoint sets. -/
structure MatchingLayer (X Y : Type*) where
  left : Finset X
  right : Finset Y
  matching : left ≃ right

def MatchingLayer.edges (M : MatchingLayer X Y) : Finset (X × Y) :=
  M.left.attach.image (fun x => (x.1, (M.matching x).1))

theorem MatchingLayer.pair_mem_edges (M : MatchingLayer X Y) (x : M.left) :
    (x.1, (M.matching x).1) ∈ M.edges := mem_image_of_mem _ (mem_attach _ _)

theorem MatchingLayer.edge_ends (M : MatchingLayer X Y) {x : X} {y : Y} (h : (x, y) ∈ M.edges) :
    x ∈ M.left ∧ y ∈ M.right := by
  obtain ⟨a, _, he⟩ := mem_image.mp h
  have hx : a.1 = x := congrArg Prod.fst he
  have hy : (M.matching a).1 = y := congrArg Prod.snd he
  exact ⟨hx ▸ a.2, hy ▸ (M.matching a).2⟩

omit [DecidableEq X] [DecidableEq Y] in
theorem MatchingLayer.card_eq (M : MatchingLayer X Y) : M.left.card = M.right.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr M.matching

theorem MatchingLayer.existsUnique_left (M : MatchingLayer X Y) {x : X} (hx : x ∈ M.left) :
    ∃! y, (x, y) ∈ M.edges := by
  refine ⟨(M.matching ⟨x, hx⟩).1, M.pair_mem_edges ⟨x, hx⟩, ?_⟩
  intro y hy
  obtain ⟨a, _, ha⟩ := mem_image.mp hy
  have hax : a = ⟨x, hx⟩ := Subtype.ext (congrArg Prod.fst ha)
  exact (congrArg Prod.snd ha).symm.trans (congrArg (fun a => (M.matching a).1) hax)

theorem MatchingLayer.existsUnique_right (M : MatchingLayer X Y) {y : Y} (hy : y ∈ M.right) :
    ∃! x, (x, y) ∈ M.edges := by
  let b : M.right := ⟨y, hy⟩
  let a := M.matching.symm b
  have hab : M.matching a = b := M.matching.apply_symm_apply _
  have hEdge : (a.1, y) ∈ M.edges := by
    simpa only [hab] using M.pair_mem_edges a
  refine ⟨a.1, hEdge, ?_⟩
  intro x hx
  obtain ⟨u, _, hu⟩ := mem_image.mp hx
  have hMa : M.matching u = M.matching a :=
    (Subtype.ext (congrArg Prod.snd hu)).trans hab.symm
  exact (congrArg Prod.fst hu).symm.trans (congrArg Subtype.val (M.matching.injective hMa))

private theorem MatchingLayer.right_subset_columns {F : Finset (X × Y)} {S : Finset X}
    (M : MatchingLayer X Y) (hM : M.edges ⊆ F) (hS : M.left ⊆ S) :
    M.right ⊆ columns F S := by
  intro y hy
  obtain ⟨x, hx, _⟩ := M.existsUnique_right hy
  exact mem_columns.mpr ⟨x, hS (M.edge_ends hx).1, hM hx⟩

private theorem MatchingLayer.row_card_le_one (M : MatchingLayer X Y) (x : X) :
    (row M.edges x).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  have hax := mem_row.mp ha
  have hbx := mem_row.mp hb
  obtain ⟨y, _, hy⟩ := M.existsUnique_left (M.edge_ends hax).1
  exact (hy a hax).trans (hy b hbx).symm

private theorem card_row_le_sdiff_add_one (F : Finset (X × Y)) (M : MatchingLayer X Y) (x : X) :
    (row F x).card ≤ (row (F \ M.edges) x).card + 1 := by
  classical
  have hsub : row F x ⊆ row (F \ M.edges) x ∪ row M.edges x := by
    intro y hy
    by_cases he : (x, y) ∈ M.edges
    · exact mem_union_right _ (mem_row.mpr he)
    · exact mem_union_left _ (mem_row.mpr (mem_sdiff.mpr ⟨mem_row.mp hy, he⟩))
  exact ((card_le_card hsub).trans (card_union_le _ _)).trans
    (Nat.add_le_add_left (M.row_card_le_one x) _)

/-- A smallest nonexpanding row family has a perfect matching to its neighborhood. -/
theorem exists_matching_layer (F : Finset (X × Y)) (S : Finset X)
    (hS : S.Nonempty) (hpos : ∀ x ∈ S, (row F x).Nonempty)
    (hbal : (columns F S).card ≤ S.card) :
    ∃ M : MatchingLayer X Y, M.left ⊆ S ∧ M.left.Nonempty ∧
      M.right = columns F M.left ∧ M.edges ⊆ F := by
  classical
  let family := S.powerset.filter (fun T => T.Nonempty ∧ (columns F T).card ≤ T.card)
  have hfamily : S ∈ family := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hS, hbal⟩
  obtain ⟨T, hT, hMin⟩ := exists_min_image family card ⟨S, hfamily⟩
  obtain ⟨hTS, hTne, hTbal⟩ := mem_filter.mp hT
  have hTS := mem_powerset.mp hTS
  obtain ⟨a, ha⟩ := hTne
  have hNTpos : 0 < (columns F T).card := by
    obtain ⟨b, hb⟩ := hpos a (hTS ha)
    exact card_pos.mpr ⟨b, mem_columns.mpr ⟨a, ha, mem_row.mp hb⟩⟩
  have hTcard : (columns F T).card = T.card := by
    apply le_antisymm hTbal
    by_contra! hlt
    let U := T.erase a
    have hcard : U.card = T.card - 1 := card_erase_of_mem ha
    have hUne : U.Nonempty := card_pos.mp (by omega)
    have hUT : U ⊆ T := erase_subset _ _
    have hNU := card_le_card (columns_mono (F := F) Subset.rfl hUT)
    have hUbal : (columns F U).card ≤ U.card := by omega
    have hUF : U ∈ family := mem_filter.mpr
      ⟨mem_powerset.mpr (hUT.trans hTS), hUne, hUbal⟩
    have hmin := hMin U hUF
    omega
  have hHall (U : Finset X) (hUT : U ⊆ T) : U.card ≤ (columns F U).card := by
    by_contra! hcontra
    have hUne : U.Nonempty := card_pos.mp (by omega)
    have hUF : U ∈ family := mem_filter.mpr
      ⟨mem_powerset.mpr (hUT.trans hTS), hUne, hcontra.le⟩
    have hEq : U = T := eq_of_subset_of_card_le hUT (hMin U hUF)
    subst U
    exact (not_lt_of_ge hTcard.ge) hcontra
  obtain ⟨f, hf, hfr⟩ := (all_card_le_biUnion_card_iff_existsInjective' (fun x : T => row F x.1)).mp
    (by
      intro U
      let I : T ↪ X := Function.Embedding.subtype _
      have hUT : U.map I ⊆ T := by
        intro x hx
        obtain ⟨a, _, rfl⟩ := mem_map.mp hx
        exact a.2
      have hC : columns F (U.map I) = U.biUnion (fun x : T => row F x.1) := by
        ext y
        simp only [mem_columns, mem_map, mem_biUnion, mem_row]
        constructor
        · rintro ⟨x, ⟨a, ha, he⟩, hx⟩
          change a.1 = x at he
          subst x
          exact ⟨a, ha, hx⟩
        · rintro ⟨a, ha, h⟩
          exact ⟨a.1, ⟨a, ha, rfl⟩, h⟩
      simpa only [card_map, hC] using hHall _ hUT)
  have hfr' (x : T) : f x ∈ columns F T := mem_columns.mpr ⟨x.1, x.2, mem_row.mp (hfr x)⟩
  let f' (x : T) : columns F T := ⟨f x, hfr' x⟩
  have hfinj : Function.Injective f' := fun _ _ he => hf (congrArg Subtype.val he)
  have hfsurj : Function.Surjective f' := by
    have hCard : Fintype.card T = Fintype.card (columns F T) := by
      simp only [Fintype.card_coe]
      exact le_antisymm (hHall T Subset.rfl) hTbal
    exact (Fintype.bijective_iff_injective_and_card f').mpr ⟨hfinj, hCard⟩ |>.2
  let M : MatchingLayer X Y := ⟨T, columns F T, Equiv.ofBijective f' ⟨hfinj, hfsurj⟩⟩
  refine ⟨M, hTS, ⟨a, ha⟩, rfl, ?_⟩
  intro p hp
  obtain ⟨x, _, rfl⟩ := mem_image.mp hp
  exact mem_row.mp (hfr x)

/-- Starting from a nonempty row family whose neighborhood is no larger,
iterate the Hall step and remove each matching before choosing the next. -/
theorem exists_nested_matchings (F : Finset (X × Y)) (S : Finset X) (δ : ℕ)
    (hS : S.Nonempty) (hdeg : ∀ x ∈ S, δ ≤ (row F x).card)
    (hbal : (columns F S).card ≤ S.card) :
    ∃ M : Fin δ → MatchingLayer X Y,
      (∀ i, (M i).left ⊆ S ∧ (M i).left.Nonempty ∧ (M i).edges ⊆ F) ∧
      ∀ i j, i < j → (M j).left ⊆ (M i).left ∧
        (M j).right ⊆ (M i).right ∧ Disjoint (M i).edges (M j).edges := by
  classical
  induction δ generalizing F S with
  | zero =>
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨M, hMS, hMpos, hMright, hMF⟩ := exists_matching_layer F S hS
      (fun x hx => card_pos.mp (by have h := hdeg x hx; omega)) hbal
    have hdegs (x : X) (hx : x ∈ M.left) : k ≤ (row (F \ M.edges) x).card := by
      have ha := hdeg x (hMS hx)
      have hb := card_row_le_sdiff_add_one F M x
      omega
    have hbal' : (columns (F \ M.edges) M.left).card ≤ M.left.card := by
      rw [M.card_eq, hMright]
      exact card_le_card (columns_mono sdiff_subset Subset.rfl)
    obtain ⟨L, hL, hnest⟩ := ih (F \ M.edges) M.left hMpos hdegs hbal'
    refine ⟨Fin.cases M L, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun u => ?_) i
      · simpa only [Fin.cases_zero] using And.intro hMS (And.intro hMpos hMF)
      · simp only [Fin.cases_succ]
        exact ⟨(hL u).1.trans hMS, (hL u).2.1, (hL u).2.2.trans sdiff_subset⟩
    · intro i j hij
      have casesIndex (i : Fin (k + 1)) : i = 0 ∨ ∃ u : Fin k, i = u.succ :=
        Fin.cases (Or.inl rfl) (fun u => Or.inr ⟨u, rfl⟩) i
      rcases casesIndex i with rfl | ⟨u, rfl⟩ <;> rcases casesIndex j with rfl | ⟨v, rfl⟩
      · exact (lt_irrefl _ hij).elim
      · simp only [Fin.cases_zero, Fin.cases_succ]
        have hR := (L v).right_subset_columns (hL v).2.2 (hL v).1
        rw [hMright]
        refine ⟨(hL v).1, hR.trans (columns_mono sdiff_subset Subset.rfl), ?_⟩
        exact disjoint_left.mpr (fun e he hL' => (mem_sdiff.mp ((hL v).2.2 hL')).2 he)
      · exact (Fin.not_lt_zero _ hij).elim
      · simpa only [Fin.cases_succ] using hnest u v (Fin.succ_lt_succ_iff.mp hij)

/-- A list of positive neighborhood sizes bounded by N cannot decay by a factor
of more than two at every one of k prescribed steps when N < 2^k. -/
theorem exists_dyadic_window {δ N k s : ℕ} (a : Fin δ → ℕ)
    (hpos : ∀ i, 0 < a i) (hbound : ∀ i, a i ≤ N)
    (hk : k * s < δ) (hN : N < 2 ^ k) :
    ∃ p q : Fin δ, q.val = p.val + s ∧ a p ≤ 2 * a q := by
  classical
  let b (j : ℕ) : ℕ := if h : j * s < δ then a ⟨j * s, h⟩ else 0
  have hb (j : ℕ) (hj : j ≤ k) : j * s < δ :=
    (Nat.mul_le_mul_right s hj).trans_lt hk
  have h0 : b 0 ≤ N := by simpa only [b, dif_pos (hb 0 (by omega))] using hbound ⟨_, hb 0 (by omega)⟩
  have h1 : 1 ≤ b k := by simpa only [b, dif_pos hk] using Nat.succ_le_of_lt (hpos ⟨k * s, hk⟩)
  by_contra! hfail
  have hdecay (j : ℕ) (hj : j < k) : 2 * b (j + 1) ≤ b j := by
    have hj' := hb j hj.le
    have hnext := hb (j + 1) (by omega)
    have hs : (j + 1) * s = j * s + s := by rw [Nat.add_mul, Nat.one_mul]
    simpa only [b, dif_pos hj', dif_pos hnext] using
      (hfail ⟨j * s, hj'⟩ ⟨(j + 1) * s, hnext⟩ hs).le
  have hind (j : ℕ) (hj : j ≤ k) : 2 ^ j * b j ≤ b 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Nat.mul_assoc]
      exact (Nat.mul_le_mul_left _ (hdecay j (by omega))).trans (ih (by omega))
  have hpow : 2 ^ k ≤ b 0 :=
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ k) h1 : 2 ^ k ≤ 2 ^ k * b k).trans
      (hind k le_rfl)
  omega

def column (F : Finset (X × Y)) (y : Y) : Finset X :=
  (F.filter (fun e => e.2 = y)).image Prod.fst

@[simp] theorem mem_column {F : Finset (X × Y)} {x : X} {y : Y} :
    x ∈ column F y ↔ (x, y) ∈ F := by
  simp only [column, mem_image, mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hab, rfl⟩, rfl⟩
    exact hab
  · intro h
    exact ⟨x, y, ⟨h, rfl⟩, rfl⟩

/-- Form a bounded-degree bipartite graph by retaining the right endpoint set
of the last matching in a consecutive block. -/
theorem exists_matching_window_graph {δ : ℕ} {F : Finset (X × Y)} {S : Finset X}
    (M : Fin δ → MatchingLayer X Y)
    (hM : ∀ i, (M i).left ⊆ S ∧ (M i).left.Nonempty ∧ (M i).edges ⊆ F)
    (hnest : ∀ i j, i < j → (M j).left ⊆ (M i).left ∧
      (M j).right ⊆ (M i).right ∧ Disjoint (M i).edges (M j).edges)
    (p q : Fin δ) (hpq : p ≤ q) (hsmall : (M p).right.card ≤ 2 * (M q).right.card) :
    ∃ L : Finset X, ∃ R : Finset Y, ∃ E : Finset (X × Y),
      L ⊆ S ∧ L.Nonempty ∧ R.Nonempty ∧ E ⊆ F ∧ E ⊆ L ×ˢ R ∧ L.card ≤ 2 * R.card ∧
      E.card = (q.val + 1 - p.val) * R.card ∧
      (∀ x, (row E x).card ≤ q.val + 1 - p.val) ∧
      ∀ y ∈ R, (column E y).card = q.val + 1 - p.val := by
  classical
  let L := (M p).left
  let R := (M q).right
  let J := Finset.Icc p q
  let parts (i : Fin δ) := (M i).edges.filter fun e => e.2 ∈ R
  let E := J.biUnion parts
  have hJ : J.card = q.val + 1 - p.val := Fin.card_Icc _ _
  have hleft (i : Fin δ) (hi : i ∈ J) : (M i).left ⊆ L := by
    rcases lt_or_eq_of_le (mem_Icc.mp hi).1 with h | rfl
    · exact (hnest _ _ h).1
    · exact Subset.rfl
  have hright (i : Fin δ) (hi : i ∈ J) : R ⊆ (M i).right := by
    rcases lt_or_eq_of_le (mem_Icc.mp hi).2 with h | rfl
    · exact (hnest _ _ h).2.1
    · exact Subset.rfl
  have hR : R.Nonempty := card_pos.mp (by
    change 0 < (M q).right.card
    rw [← (M q).card_eq]
    exact (hM q).2.1.card_pos)
  have hEF : E ⊆ F := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact (hM i).2.2 (mem_filter.mp hi).1
  have hELR : E ⊆ L ×ˢ R := by
    rintro ⟨x, y⟩ he
    obtain ⟨i, hI, hi⟩ := mem_biUnion.mp he
    have h := mem_filter.mp hi
    exact mem_product.mpr ⟨hleft i hI ((M i).edge_ends h.1).1, h.2⟩
  have hRows (x : X) : (row E x).card ≤ J.card := by
    have hE : row E x = J.biUnion (fun i => row (parts i) x) := by
      ext y
      simp only [E, mem_row, mem_biUnion]
    rw [hE]
    have hsingle (i : Fin δ) (_ : i ∈ J) : (row (parts i) x).card ≤ 1 := by
      have hsub : row (parts i) x ⊆ row (M i).edges x := by
        intro y hy
        exact mem_row.mpr (mem_filter.mp (mem_row.mp hy)).1
      exact (card_le_card hsub).trans ((M i).row_card_le_one x)
    simpa only [Nat.mul_one] using card_biUnion_le_card_mul J _ 1 hsingle
  have hCols (y : Y) (hy : y ∈ R) : (column E y).card = J.card := by
    have hE : column E y = J.biUnion (fun i => column (parts i) y) := by
      ext x
      simp only [E, mem_column, mem_biUnion]
    have hOne (i : Fin δ) (hi : i ∈ J) : (column (parts i) y).card = 1 := by
      obtain ⟨x, hx, hUnique⟩ := (M i).existsUnique_right (hright i hi hy)
      apply card_eq_one.mpr
      refine ⟨x, ?_⟩
      ext u
      constructor
      · intro hu
        exact mem_singleton.mpr (hUnique u (mem_filter.mp (mem_column.mp hu)).1)
      · intro hu
        have hux := mem_singleton.mp hu
        subst u
        exact mem_column.mpr (mem_filter.mpr ⟨hx, hy⟩)
    have hDis : (J : Set (Fin δ)).PairwiseDisjoint (fun i => column (parts i) y) := by
      intro i _ j _ hij
      apply disjoint_left.mpr
      intro x hx hz
      have hi := (mem_filter.mp (mem_column.mp hx)).1
      have hj := (mem_filter.mp (mem_column.mp hz)).1
      rcases lt_or_gt_of_ne hij with h | h
      · exact disjoint_left.mp (hnest i j h).2.2 hi hj
      · exact disjoint_left.mp (hnest j i h).2.2 hj hi
    rw [hE, card_biUnion hDis]
    calc
      (∑ i ∈ J, (column (parts i) y).card) = ∑ _i ∈ J, 1 := sum_congr rfl hOne
      _ = J.card := by simp
  have hEdgeCount : E.card = J.card * R.card := by
    rw [card_eq_sum_card_fiberwise (f := Prod.snd) (s := E) (t := R)
      (fun e he => (mem_product.mp (hELR he)).2)]
    calc
      (∑ y ∈ R, (E.filter (fun e => e.2 = y)).card) = ∑ _y ∈ R, J.card := by
        apply sum_congr rfl
        intro y hy
        rw [← hCols y hy]
        unfold column
        symm
        apply card_image_of_injOn
        intro e he f hf hef
        exact Prod.ext hef ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm)
      _ = _ := by simp [Nat.mul_comm]
  refine ⟨L, R, E, (hM p).1, (hM p).2.1, hR, hEF, hELR, ?_, ?_, ?_, ?_⟩
  · exact (M p).card_eq.le.trans hsmall
  · rwa [← hJ]
  · simpa only [← hJ] using hRows
  · simpa only [← hJ] using hCols

/-- The number of consecutive matchings kept by the dyadic argument. -/
def windowWidth (N δ : ℕ) : ℕ :=
  (δ - 1) / (Nat.log 2 N + 1) + 1

/-- The combinatorial part of regularization. The retained edge set has
maximum degree at most the block width and average degree at least two thirds
of the block width. -/
theorem exists_bounded_degree_block (F : Finset (X × Y)) (S : Finset X) (N δ : ℕ)
    (hS : S.Nonempty) (hδ : 0 < δ) (hdeg : ∀ x ∈ S, δ ≤ (row F x).card)
    (hbal : (columns F S).card ≤ S.card) (hN : (columns F S).card ≤ N) :
    ∃ L : Finset X, ∃ R : Finset Y, ∃ E : Finset (X × Y),
      L ⊆ S ∧ R ⊆ columns F S ∧ L.Nonempty ∧ R.Nonempty ∧
      E ⊆ F ∧ E ⊆ L ×ˢ R ∧ L.card ≤ 2 * R.card ∧
      E.card = windowWidth N δ * R.card ∧
      (∀ x, (row E x).card ≤ windowWidth N δ) ∧
      ∀ y ∈ R, (column E y).card = windowWidth N δ := by
  obtain ⟨M, hM, hnest⟩ := exists_nested_matchings F S δ hS hdeg hbal
  let k := Nat.log 2 N + 1
  let s := (δ - 1) / k
  have hks : k * s < δ := by
    have h := Nat.div_mul_le_self (δ - 1) k
    change k * ((δ - 1) / k) < δ
    rw [Nat.mul_comm]
    omega
  have hpow : N < 2 ^ k := Nat.lt_pow_succ_log_self (by decide) N
  have hR (i : Fin δ) : (M i).right ⊆ columns F S :=
    (M i).right_subset_columns (hM i).2.2 (hM i).1
  have hpos (i : Fin δ) : 0 < (M i).right.card := by
    rw [← (M i).card_eq]
    exact (hM i).2.1.card_pos
  obtain ⟨p, q, hq, hRatio⟩ := exists_dyadic_window (fun i => (M i).right.card)
    hpos (fun i => (card_le_card (hR i)).trans hN) hks hpow
  have hpq : p ≤ q := by
    change p.val ≤ q.val
    rw [hq]
    exact Nat.le_add_right _ _
  have hwidth : q.val + 1 - p.val = windowWidth N δ := by
    change q.val + 1 - p.val = s + 1
    rw [hq, Nat.add_assoc, Nat.add_sub_cancel_left]
  -- The explicit witnesses of the matching-window proof are retained
  -- through its endpoint subset conclusions.
  obtain ⟨L, R, E, hLS, hLne, hRne, hEF, hELR, hRatio', hCount, hRow, hCol⟩ :=
    exists_matching_window_graph M hM hnest p q hpq hRatio
  have hRC : R ⊆ columns F S := by
    intro y hy
    have hcol := hCol y hy
    have hpos : 0 < (column E y).card := by
      rw [hcol, hwidth]
      exact Nat.succ_pos _
    obtain ⟨x, hx⟩ := card_pos.mp hpos
    have hxy := mem_column.mp hx
    exact mem_columns.mpr ⟨x, hLS (mem_product.mp (hELR hxy)).1, hEF hxy⟩
  rw [hwidth] at hCount hRow hCol
  exact ⟨L, R, E, hLS, hRC, hLne, hRne, hEF, hELR, hRatio', hCount, hRow, hCol⟩

/-- Delete low-degree vertices while preserving density, by taking a
cardinality-minimal vertex set with the original edge-to-vertex ratio. -/
theorem exists_min_degree_subset {V : Type*} [DecidableEq V] (A : Finset V)
    (edges : Finset V → ℝ) (degree : Finset V → V → ℝ) (hA : A.Nonempty)
    (hZero : edges ∅ = 0)
    (hErase : ∀ S ⊆ A, ∀ v ∈ S, edges S = edges (S.erase v) + degree S v) :
    ∃ S ⊆ A, S.Nonempty ∧ edges A / (A.card : ℝ) ≤ edges S / (S.card : ℝ) ∧
      ∀ v ∈ S, edges A / (A.card : ℝ) ≤ degree S v := by
  classical
  let d := edges A / (A.card : ℝ)
  let family := A.powerset.filter fun S => S.Nonempty ∧ d * (S.card : ℝ) ≤ edges S
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hAfam : A ∈ family := mem_filter.mpr
    ⟨mem_powerset.mpr Subset.rfl, hA, le_of_eq (div_mul_cancel₀ _ hAcard.ne')⟩
  obtain ⟨S, hS, hmin⟩ := exists_min_image family card ⟨A, hAfam⟩
  obtain ⟨hSA, hSne, hSd⟩ := mem_filter.mp hS
  have hsub := mem_powerset.mp hSA
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  refine ⟨S, hsub, hSne, (le_div_iff₀ hScard).mpr hSd, ?_⟩
  intro v hv
  let T := S.erase v
  have hTle : edges T ≤ d * (T.card : ℝ) := by
    by_cases hT : T.Nonempty
    · by_contra! hb
      have hTsub : T ⊆ A := (erase_subset _ _).trans hsub
      have hTfam : T ∈ family := mem_filter.mpr ⟨mem_powerset.mpr hTsub, hT, hb.le⟩
      exact (not_le_of_gt (card_erase_lt_of_mem hv)) (hmin T hTfam)
    · have he : T = ∅ := not_nonempty_iff_eq_empty.mp hT
      simp [he, hZero]
  have hc : (S.card : ℝ) = (T.card : ℝ) + 1 := by
    exact_mod_cast (card_erase_add_one hv).symm
  have h := hErase S hsub v hv
  change d ≤ degree S v
  rw [hc, mul_add, mul_one] at hSd
  linarith only [h, hSd, hTle]

/-- Convert the dyadic width to the natural logarithm used in DMMS24. -/
theorem windowWidth_log_bound {N δ : ℕ} (hN : 2 ≤ Real.log N) (hδ : 0 < δ) :
    (δ : ℝ) / ((5 / 2) * Real.log N) ≤ (windowWidth N δ : ℝ) := by
  have hNne : N ≠ 0 := by
    intro he
    norm_num [he] at hN
  have hpow : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 hNne
  have hln := Real.log_le_log (show (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 N by positivity) hpow
  rw [Real.log_pow] at hln
  have hln2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    convert h using 1; norm_num
  have hNlog : (Nat.log 2 N : ℝ) * (1 / 2) ≤ Real.log N :=
    (mul_le_mul_of_nonneg_left hln2 (by positivity)).trans hln
  have hk : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ (5 / 2) * Real.log N := by
    push_cast
    linarith only [hNlog, hN]
  let k := Nat.log 2 N + 1
  have hkpos : 0 < k := Nat.succ_pos _
  have hDiv : δ - 1 < windowWidth N δ * k := by
    exact (Nat.div_lt_iff_lt_mul hkpos).mp (Nat.lt_succ_self ((δ - 1) / k))
  have hNat : δ ≤ k * windowWidth N δ := by
    rw [Nat.mul_comm]
    omega
  have hReal : (δ : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) * (windowWidth N δ : ℝ) := by
    exact_mod_cast hNat
  apply (div_le_iff₀ (show (0 : ℝ) < (5 / 2) * Real.log N by linarith)).mpr
  calc
    _ ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) * (windowWidth N δ : ℝ) := hReal
    _ ≤ ((5 / 2) * Real.log N) * (windowWidth N δ : ℝ) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = _ := mul_comm _ _

end Erdos642AlmostRegular


/- Almost-regular subgraphs of bipartite graphs, using the nested-matching proof. -/

namespace Erdos642Regularization

open Finset SimpleGraph Erdos642AlmostRegular Erdos642InducedCounts

variable {V : Type*} [Fintype V] [DecidableEq V]

private def oriented (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V) :
    Finset (V × V) := (L ×ˢ R).filter (fun p => G.Adj p.1 p.2)

private theorem row_oriented {G : SimpleGraph V} [DecidableRel G.Adj] {L R : Finset V}
    {x : V} (hx : x ∈ L) : row (oriented G L R) x = G.neighborFinset x ∩ R := by
  ext y
  simp [oriented, hx, and_comm]

private def ofOriented (E : Finset (V × V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => (x, y) ∈ E)

private instance (E : Finset (V × V)) : DecidableRel (ofOriented E).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ ((_, _) ∈ E ∨ (_, _) ∈ E)))

omit [Fintype V] [DecidableEq V] in
private theorem ofOriented_adj {E : Finset (V × V)} {x y : V} :
    (ofOriented E).Adj x y ↔ x ≠ y ∧ ((x, y) ∈ E ∨ (y, x) ∈ E) := Iff.rfl

omit [Fintype V] [DecidableEq V] in
private theorem ofOriented_le {E : Finset (V × V)} {G : SimpleGraph V}
    (h : ∀ p ∈ E, G.Adj p.1 p.2) : ofOriented E ≤ G := by
  intro x y ha
  rcases (ofOriented_adj.mp ha).2 with he | he
  · exact h (x, y) he
  · exact (h (y, x) he).symm

omit [Fintype V] [DecidableEq V] in
private theorem ofOriented_isBipartiteWith {E : Finset (V × V)} {L R : Finset V}
    (hLR : Disjoint L R) (hE : E ⊆ L ×ˢ R) :
    (ofOriented E).IsBipartiteWith (L : Set V) (R : Set V) := by
  refine ⟨Finset.disjoint_coe.mpr hLR, ?_⟩
  intro x y h
  rcases (ofOriented_adj.mp h).2 with he | he
  · exact Or.inl (mem_product.mp (hE he))
  · exact Or.inr ⟨(mem_product.mp (hE he)).2, (mem_product.mp (hE he)).1⟩

private theorem ofOriented_neighbors_left {E : Finset (V × V)} {L R : Finset V}
    (hLR : Disjoint L R) (hE : E ⊆ L ×ˢ R) {x : V} (hx : x ∈ L) :
    (ofOriented E).neighborFinset x = row E x := by
  ext y
  rw [mem_neighborFinset, mem_row, ofOriented_adj]
  constructor
  · rintro ⟨_, he | he⟩
    · exact he
    · exact (disjoint_left.mp hLR hx (mem_product.mp (hE he)).2).elim
  · intro h
    have hy := (mem_product.mp (hE h)).2
    exact ⟨fun hxy => disjoint_left.mp hLR hx (hxy.symm ▸ hy), Or.inl h⟩

private theorem ofOriented_neighbors_right {E : Finset (V × V)} {L R : Finset V}
    (hLR : Disjoint L R) (hE : E ⊆ L ×ˢ R) {y : V} (hy : y ∈ R) :
    (ofOriented E).neighborFinset y = column E y := by
  ext x
  rw [mem_neighborFinset, mem_column, ofOriented_adj]
  constructor
  · rintro ⟨_, he | he⟩
    · exact (disjoint_left.mp hLR (mem_product.mp (hE he)).1 hy).elim
    · exact he
  · intro h
    have hx := (mem_product.mp (hE h)).1
    exact ⟨fun hyx => disjoint_left.mp hLR hx (hyx ▸ hy), Or.inr h⟩

private theorem ofOriented_internalEdges_card {E : Finset (V × V)} {L R : Finset V}
    (hLR : Disjoint L R) (hE : E ⊆ L ×ˢ R) :
    (Erdos642InducedCounts.internalEdges (ofOriented E) (L ∪ R)).card = E.card := by
  let f (p : V × V) := s(p.1, p.2)
  have hEq : Erdos642InducedCounts.internalEdges (ofOriented E) (L ∪ R) = E.image f := by
    ext e
    induction e using Sym2.inductionOn with
    | hf x y =>
      rw [mk_mem_internalEdges, ofOriented_adj]
      constructor
      · rintro ⟨⟨_, he | he⟩, _, _⟩
        · exact mem_image.mpr ⟨(x, y), he, rfl⟩
        · exact mem_image.mpr ⟨(y, x), he, Sym2.eq_swap⟩
      · intro h
        obtain ⟨⟨u, v⟩, huv, he⟩ := mem_image.mp h
        obtain ⟨hL, hR⟩ := mem_product.mp (hE huv)
        have hne : u ≠ v := fun he => disjoint_left.mp hLR hL (he.symm ▸ hR)
        change s(u, v) = s(x, y) at he
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨⟨hne, Or.inl huv⟩, mem_union_left _ hL, mem_union_right _ hR⟩
        · exact ⟨⟨hne.symm, Or.inr huv⟩, mem_union_right _ hR, mem_union_left _ hL⟩
  rw [hEq]
  apply card_image_of_injOn
  rintro ⟨a, b⟩ hab ⟨x, y⟩ hxy he
  change s(a, b) = s(x, y) at he
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact (disjoint_left.mp hLR (mem_product.mp (hE hab)).1 (mem_product.mp (hE hxy)).2).elim

/-- The density-preserving minimum-degree trim for an induced finite graph. -/
theorem trim_min_degree (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (hA : A.Nonempty) :
    ∃ S ⊆ A, S.Nonempty ∧
      ((Erdos642InducedCounts.internalEdges G A).card : ℝ) / A.card ≤ ((Erdos642InducedCounts.internalEdges G S).card : ℝ) / S.card ∧
      ∀ x ∈ S, ((Erdos642InducedCounts.internalEdges G A).card : ℝ) / A.card ≤ degreeWithin G S x := by
  apply exists_min_degree_subset A (fun S => ((Erdos642InducedCounts.internalEdges G S).card : ℝ))
    (fun S x => (degreeWithin G S x : ℝ)) hA (by simp)
  intro S _ x hx
  exact_mod_cast card_internalEdges_erase G hx

private theorem regular_core_of_parts
    (G : SimpleGraph V) [DecidableRel G.Adj] (S L R : Finset V) (N δ : ℕ)
    (hLS : L ⊆ S) (hRS : R ⊆ S) (hLR : Disjoint L R) (hL : L.Nonempty)
    (hbal : R.card ≤ L.card) (hN : S.card ≤ N) (hδ : 0 < δ)
    (hNbr : ∀ x ∈ L, G.neighborFinset x ∩ S ⊆ R)
    (hdeg : ∀ x ∈ S, δ ≤ degreeWithin G S x) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj), ∃ U ⊆ S, U.Nonempty ∧
      K ≤ G ∧ K.IsBipartite ∧
      (windowWidth N δ : ℝ) / 3 ≤ ((Erdos642InducedCounts.internalEdges K U).card : ℝ) / U.card ∧
      (∀ x ∈ U, (windowWidth N δ : ℝ) / 3 ≤ degreeWithin K U x) ∧
      ∀ x ∈ U, degreeWithin K U x ≤ windowWidth N δ := by
  classical
  let F := oriented G L R
  have hrows (x : V) (hx : x ∈ L) : row F x = G.neighborFinset x ∩ S := by
    rw [row_oriented hx]
    apply Subset.antisymm
    · exact inter_subset_inter Subset.rfl hRS
    · exact subset_inter inter_subset_left (hNbr x hx)
  have hcols : columns F L ⊆ R := by
    intro y hy
    obtain ⟨x, _, hxy⟩ := mem_columns.mp hy
    exact (mem_product.mp (mem_filter.mp hxy).1).2
  obtain ⟨L', R', E, hL', hR', hLne, hRne, hEF, hE, hRatio, hEcard, hxMax, hyReg⟩ :=
    exists_bounded_degree_block F L N δ hL hδ
      (fun x hx => by rw [hrows x hx]; exact hdeg x (hLS hx))
      ((card_le_card hcols).trans hbal) ((card_le_card hcols).trans ((card_le_card hRS).trans hN))
  have hR'' := hR'.trans hcols
  have hdisj : Disjoint L' R' := disjoint_of_subset_left hL' (disjoint_of_subset_right hR'' hLR)
  let K := ofOriented E
  let U := L' ∪ R'
  have hUK : U ⊆ S := union_subset (hL'.trans hLS) (hR''.trans hRS)
  have hU : U.Nonempty := hLne.mono (subset_union_left)
  have hAvg : (windowWidth N δ : ℝ) / 3 ≤ ((Erdos642InducedCounts.internalEdges K U).card : ℝ) / U.card := by
    have hcount : (Erdos642InducedCounts.internalEdges K U).card = windowWidth N δ * R'.card :=
      (ofOriented_internalEdges_card hdisj hE).trans hEcard
    have hsize : U.card ≤ 3 * R'.card := by
      change (L' ∪ R').card ≤ _
      rw [card_union_of_disjoint hdisj]
      omega
    have hsizeR : (U.card : ℝ) ≤ 3 * (R'.card : ℝ) := by exact_mod_cast hsize
    have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
    apply (le_div_iff₀ hUpos).mpr
    rw [hcount, Nat.cast_mul]
    calc
      _ ≤ (windowWidth N δ : ℝ) / 3 * (3 * (R'.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hsizeR (by positivity)
      _ = _ := by ring
  have hK : K ≤ G := ofOriented_le (fun e he => (mem_filter.mp (hEF he)).2)
  have hKbp : K.IsBipartite := (ofOriented_isBipartiteWith hdisj hE).isBipartite
  obtain ⟨W, hWU, hW, hDense, hMin⟩ := trim_min_degree K U hU
  refine ⟨K, inferInstance, W, hWU.trans hUK, hW, hK, hKbp, hAvg.trans hDense,
    fun x hx => hAvg.trans (hMin x hx), ?_⟩
  intro x hx
  have hxU : x ∈ L' ∪ R' := hWU hx
  refine (degree_within_le K W x).trans ?_
  rw [← card_neighborFinset_eq_degree]
  rcases mem_union.mp hxU with hxL | hxR
  · change ((ofOriented E).neighborFinset x).card ≤ _
    rw [ofOriented_neighbors_left hdisj hE hxL]
    exact hxMax x
  · change ((ofOriented E).neighborFinset x).card ≤ _
    rw [ofOriented_neighbors_right hdisj hE hxR, hyReg x hxR]

/-- An initially bipartite graph with minimum degree at least δ on S
has an almost-regular subgraph obtained from a block of nested matchings. -/
theorem regular_core_of_bipartite_min_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (N δ : ℕ)
    (hbip : G.IsBipartite) (hS : S.Nonempty) (hN : S.card ≤ N) (hδ : 0 < δ)
    (hdeg : ∀ x ∈ S, δ ≤ degreeWithin G S x) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj), ∃ U ⊆ S, U.Nonempty ∧
      K ≤ G ∧ K.IsBipartite ∧
      (windowWidth N δ : ℝ) / 3 ≤ ((Erdos642InducedCounts.internalEdges K U).card : ℝ) / U.card ∧
      (∀ x ∈ U, (windowWidth N δ : ℝ) / 3 ≤ degreeWithin K U x) ∧
      ∀ x ∈ U, degreeWithin K U x ≤ windowWidth N δ := by
  classical
  obtain ⟨A, B, hab⟩ := hbip.exists_isBipartiteWith
  let L := S.filter fun x => x ∈ A
  let R := S.filter fun x => x ∈ B
  have hLS : L ⊆ S := filter_subset _ _
  have hRS : R ⊆ S := filter_subset _ _
  have hLR : Disjoint L R := disjoint_left.mpr fun _ hL hR =>
    Set.disjoint_left.mp hab.disjoint (mem_filter.mp hL).2 (mem_filter.mp hR).2
  have hNbL (x : V) (hx : x ∈ L) : G.neighborFinset x ∩ S ⊆ R := by
    intro y hy
    obtain ⟨hxy, hyS⟩ := mem_inter.mp hy
    exact mem_filter.mpr ⟨hyS, hab.mem_of_mem_adj (mem_filter.mp hx).2 ((mem_neighborFinset _ _ _).mp hxy)⟩
  have hNbR (x : V) (hx : x ∈ R) : G.neighborFinset x ∩ S ⊆ L := by
    intro y hy
    obtain ⟨hxy, hyS⟩ := mem_inter.mp hy
    exact mem_filter.mpr ⟨hyS, hab.symm.mem_of_mem_adj (mem_filter.mp hx).2 ((mem_neighborFinset _ _ _).mp hxy)⟩
  have hsome : L.Nonempty ∨ R.Nonempty := by
    obtain ⟨x, hx⟩ := hS
    have hxp : 0 < (G.neighborFinset x ∩ S).card := hδ.trans_le (hdeg x hx)
    obtain ⟨y, hy⟩ := card_pos.mp hxp
    have hxy := (mem_neighborFinset G x y).mp (mem_inter.mp hy).1
    rcases hab.mem_of_adj hxy with hl | hr
    · exact Or.inl ⟨x, mem_filter.mpr ⟨hx, hl.1⟩⟩
    · exact Or.inr ⟨x, mem_filter.mpr ⟨hx, hr.1⟩⟩
  by_cases hbal : R.card ≤ L.card
  · have hL : L.Nonempty := hsome.elim id (fun h => card_pos.mp (h.card_pos.trans_le hbal))
    exact regular_core_of_parts G S L R N δ hLS hRS hLR hL hbal hN hδ hNbL hdeg
  · have hbal' : L.card ≤ R.card := Nat.le_of_lt (Nat.lt_of_not_ge hbal)
    have hR : R.Nonempty := hsome.elim (fun h => card_pos.mp (h.card_pos.trans_le hbal')) id
    exact regular_core_of_parts G S R L N δ hRS hLS hLR.symm hR hbal' hN hδ hNbR hdeg

/-- A bipartite input has a nonempty 3-almost-regular subgraph, with degree loss
less than the bound used for the ambient graph in DMMS24. -/
theorem exists_almost_regular_bipartite
    (G : SimpleGraph V) [DecidableRel G.Adj] {N : ℕ}
    (hN : 2 ≤ Real.log N) (hV : Fintype.card V ≤ N) (hbip : G.IsBipartite)
    (hEdge : 0 < G.edgeFinset.card) :
    ∃ (U : Finset V) (K : SimpleGraph V), U.Nonempty ∧ K ≤ G ∧
      let H := K.induce (U : Set V)
      (2 * (G.edgeSet.ncard : ℝ) / Fintype.card V) / (10 * Real.log N) ≤
        2 * (H.edgeSet.ncard : ℝ) / U.card ∧
      ∀ v w : U, (H.neighborSet v).ncard ≤ 3 * (H.neighborSet w).ncard := by
  classical
  have hA : (univ : Finset V).Nonempty := by
    obtain ⟨e, _⟩ := card_pos.mp hEdge
    induction e using Sym2.inductionOn with
    | hf x y => exact ⟨x, mem_univ _⟩
  have hFull : Erdos642InducedCounts.internalEdges G (univ : Finset V) = G.edgeFinset := by
    simp [Erdos642InducedCounts.internalEdges, Finset.sym2_univ]
  let a : ℝ := (G.edgeFinset.card : ℝ) / Fintype.card V
  let δ : ℕ := ⌈a⌉₊
  have ha : 0 < a := by
    apply div_pos
    · exact_mod_cast hEdge
    · exact_mod_cast (show 0 < Fintype.card V by simpa using hA.card_pos)
  have hδ : 0 < δ := Nat.ceil_pos.mpr ha
  obtain ⟨S, hSsub, hS, _, hm⟩ := trim_min_degree G (univ : Finset V) hA
  have hMin (x : V) (hx : x ∈ S) : δ ≤ degreeWithin G S x :=
    Nat.ceil_le.mpr (by simpa only [a, hFull, card_univ] using hm x hx)
  have hSn : S.card ≤ N := (card_le_card hSsub).trans (by simpa using hV)
  obtain ⟨K, decK, T, _, hT, hKG, _, hRatio, hLow, hHigh⟩ :=
    regular_core_of_bipartite_min_degree G S N δ hbip hS hSn hδ hMin
  let _ : DecidableRel K.Adj := decK
  have hL : 0 < Real.log N := by linarith only [hN]
  have haWidth : a / ((5 / 2) * Real.log N) ≤ (windowWidth N δ : ℝ) :=
    (div_le_div_of_nonneg_right (Nat.le_ceil a) (by positivity)).trans (windowWidth_log_bound hN hδ)
  refine ⟨T, K, hT, hKG, ?_, ?_⟩
  · rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    change (2 * (G.edgeFinset.card : ℝ) / Fintype.card V) / (10 * Real.log N) ≤
      2 * (((K.induce (T : Set V)).edgeFinset).card : ℝ) / T.card
    rw [card_induced_edges]
    have heq : (2 * (G.edgeFinset.card : ℝ) / Fintype.card V) / (10 * Real.log N) =
        (a / ((5 / 2) * Real.log N)) / 2 := by
      dsimp only [a]
      field_simp
      ring
    rw [heq]
    have hwidth0 : (0 : ℝ) ≤ windowWidth N δ := Nat.cast_nonneg _
    rw [mul_div_assoc]
    linarith only [haWidth, hRatio, hwidth0]
  · intro v w
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    change ((K.induce (T : Set V)).neighborFinset v).card ≤
      3 * ((K.induce (T : Set V)).neighborFinset w).card
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, degree_induced, degree_induced]
    have hv : (degreeWithin K T v.1 : ℝ) ≤ (windowWidth N δ : ℝ) :=
      by exact_mod_cast hHigh v.1 v.2
    have hw := hLow w.1 w.2
    exact_mod_cast (show (degreeWithin K T v.1 : ℝ) ≤ 3 * (degreeWithin K T w.1 : ℝ) by
      linarith only [hv, hw])

end Erdos642Regularization


/- Expansion and near-regularity after the induced cleaning step. -/

namespace Erdos642ExpandingSlice

open Finset SimpleGraph Erdos642InducedCounts
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem internal_edges_univ : Erdos642InducedCounts.internalEdges G (univ : Finset V) = G.edgeFinset := by
  simp [Erdos642InducedCounts.internalEdges, Finset.sym2_univ]

omit [DecidableEq V] in
private theorem degree_le_six_average [Nonempty V]
    (hReg : ∀ v w : V, G.degree v ≤ 6 * G.degree w) (v : V) :
    (G.degree v : ℝ) ≤ 6 * (2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) := by
  have hpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hpos).mpr
  have hSum : (∑ w : V, (G.degree w : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  calc
    _ = ∑ _w : V, (G.degree v : ℝ) := by simp [mul_comm]
    _ ≤ ∑ w : V, 6 * (G.degree w : ℝ) := by
      exact Finset.sum_le_sum fun w _ => by exact_mod_cast hReg v w
    _ = 6 * (2 * (G.edgeFinset.card : ℝ)) := by rw [← Finset.mul_sum,hSum]

/-- The induced cleaning step preserves half the average degree and improves
the absolute bound on the degree ratio to 24. -/
theorem regular_graph_has_expanding_slice [Nonempty V]
    {N : ℕ} (hN : 1 ≤ Real.log N) (hV : Fintype.card V ≤ N)
    (hEdge : 0 < G.edgeFinset.card)
    (hReg : ∀ v w : V, G.degree v ≤ 6 * G.degree w) :
    ∃ S : Finset V, S.Nonempty ∧
      let avg := 2 * ((Erdos642InducedCounts.internalEdges G S).card : ℝ) / (S.card : ℝ)
      (2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) / 2 ≤ avg ∧
      (∀ v ∈ S, ∀ w ∈ S, degreeWithin G S v ≤ 24 * degreeWithin G S w) ∧
      ∀ U ⊆ S, 2 * U.card ≤ S.card →
        (1 / (10 * Real.log N)) * avg * (U.card : ℝ) ≤ (cutEdges G S U).card := by
  classical
  obtain ⟨S,hSU,hS,hAvg,hDegree,hCut⟩ :=
    Erdos642DensityIncrement.exists_expanding_subset (univ : Finset V)
      (fun S => ((Erdos642InducedCounts.internalEdges G S).card : ℝ))
      (fun S v => (degreeWithin G S v : ℝ))
      (fun S U => ((cutEdges G S U).card : ℝ)) hN
      (by simpa only [card_univ] using hV) univ_nonempty
      (by rw [internal_edges_univ]; exact_mod_cast hEdge)
      (by intro v; rw [internal_edges_singleton,card_empty,Nat.cast_zero])
      (by intro S _ v hv; exact_mod_cast card_internalEdges_erase G hv)
      (by intro S _ U hUS; exact_mod_cast card_internalEdges_split G hUS)
      (by intro S _; rw [cut_edges_empty,card_empty,Nat.cast_zero])
  simp only [internal_edges_univ,card_univ] at hAvg
  refine ⟨S,hS,hAvg,?_,hCut⟩
  intro v hv w hw
  have hV₀ := degree_le_six_average G hReg v
  have hV₁ : (degreeWithin G S v : ℝ) ≤ G.degree v := by exact_mod_cast degree_within_le G S v
  have hW := hDegree w hw
  have hRatio : (degreeWithin G S v : ℝ) ≤ 24 * (degreeWithin G S w : ℝ) := by
    linarith only [hV₀,hV₁,hW,hAvg]
  exact_mod_cast hRatio

end Erdos642ExpandingSlice



/- Relabeling a finite induced slice preserves the quantities in the expansion lemma. -/

namespace Erdos642SliceTransport

open Finset SimpleGraph Erdos642InducedCounts

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem cut_ncard_eq {W : Type*} {S : Finset V} (e : W ≃ S) (T : Finset W) :
    let H := (G.induce (S : Set V)).comap e
    let p : W ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
    {a ∈ H.edgeSet | ∃ u v : W, u ∈ T ∧ v ∉ T ∧ a = s(u,v)}.ncard =
      (cutEdges G S (T.map p)).card := by
  classical
  let H := (G.induce (S : Set V)).comap e
  let p : W ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
  let B : Set (Sym2 W) := {a ∈ H.edgeSet | ∃ u v : W, u ∈ T ∧ v ∉ T ∧ a = s(u,v)}
  change B.ncard = (cutEdges G S (T.map p)).card
  have hmem (x : W) : p x ∈ S := (e x).property
  have hmap (x : W) : p x ∈ T.map p ↔ x ∈ T := Finset.mem_map' p
  have himage : Sym2.map p '' B = (cutEdges G S (T.map p) : Set (Sym2 V)) := by
    ext a
    constructor
    · rintro ⟨b, ⟨hb, u, v, hu, hv, rfl⟩, rfl⟩
      rw [Sym2.map_mk]
      exact (mk_mem_cutEdges G).mpr
        ⟨show H.Adj u v from hb, hmem u, hmem v, Or.inl ⟨(hmap _).mpr hu, (hmap _).not.mpr hv⟩⟩
    · intro ha
      induction a using Sym2.inductionOn with
      | hf x y =>
        obtain ⟨hadj, hx, hy, hcut⟩ := (mk_mem_cutEdges G).mp ha
        let u := e.symm ⟨x, hx⟩
        let v := e.symm ⟨y, hy⟩
        have hux : p u = x := by simp [p, u]
        have hvy : p v = y := by simp [p, v]
        have huv : H.Adj u v := by
          change G.Adj (p u) (p v)
          simpa only [hux, hvy] using hadj
        rcases hcut with ⟨hxT, hyT⟩ | ⟨hyT, hxT⟩
        · have hu : u ∈ T := (hmap u).mp (hux ▸ hxT)
          have hv : v ∉ T := (hmap v).not.mp (hvy ▸ hyT)
          refine ⟨s(u,v), ⟨(show s(u,v) ∈ H.edgeSet from huv), u, v, hu, hv, rfl⟩, ?_⟩
          rw [Sym2.map_mk, hux, hvy]
        · have hv : v ∈ T := (hmap v).mp (hvy ▸ hyT)
          have hu : u ∉ T := (hmap u).not.mp (hux ▸ hxT)
          refine ⟨s(v,u), ⟨(show s(v,u) ∈ H.edgeSet from huv.symm), v, u, hv, hu, rfl⟩, ?_⟩
          rw [Sym2.map_mk, hux, hvy, Sym2.eq_swap]
  rw [← Set.ncard_image_of_injective B (Sym2.map.injective p.injective), himage,
    Set.ncard_coe_finset]

/-- Transfer a slice to the exact finite vertex type and preserve its lower average bound. -/
theorem transport_expanding_slice
    {n : ℕ} {K : SimpleGraph (Fin n)} (φ : G →g K) (hφ : Function.Injective φ)
    (hBip : G.IsBipartite) {S : Finset V} (hS : S.Nonempty) {A : ℝ}
    (hAvg : A ≤ 2 * ((Erdos642InducedCounts.internalEdges G S).card : ℝ) / (S.card : ℝ))
    (hReg : ∀ v ∈ S, ∀ w ∈ S, degreeWithin G S v ≤ 24 * degreeWithin G S w)
    (hCut : ∀ U ⊆ S, 2 * U.card ≤ S.card →
      (1 / (10 * Real.log n)) * (2 * ((Erdos642InducedCounts.internalEdges G S).card : ℝ) / (S.card : ℝ)) *
        (U.card : ℝ) ≤ (cutEdges G S U).card) :
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ ∃ H : SimpleGraph (Fin m), ∃ f : H →g K,
      Function.Injective f ∧ H.IsBipartite ∧
      (∀ u v : Fin m, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) ∧
      A ≤ 2 * (H.edgeSet.ncard : ℝ) / m ∧
      (∀ T : Finset (Fin m), 2 * T.card ≤ m →
        (1 / (10 * Real.log n)) * (2 * (H.edgeSet.ncard : ℝ) / m) * T.card ≤
          ({a ∈ H.edgeSet | ∃ u v : Fin m, u ∈ T ∧ v ∉ T ∧ a = s(u,v)}.ncard : ℝ)) := by
  classical
  let e : Fin S.card ≃ S := S.equivFin.symm
  let p : Fin S.card ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
  let J := G.induce (S : Set V)
  let H := J.comap e
  let iso : H ≃g J := Iso.comap e J
  let i : H →g G := ⟨p, fun h => h⟩
  have hi : Function.Injective i := p.injective
  let f := φ.comp i
  have hf : Function.Injective f := hφ.comp hi
  have hCard : S.card ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hEdges : H.edgeSet.ncard = (Erdos642InducedCounts.internalEdges G S).card := by
    rw [Set.ncard_eq_toFinset_card']
    exact iso.card_edgeFinset_eq.trans (card_induced_edges G S)
  have hDeg (v : Fin S.card) : (H.neighborSet v).ncard = degreeWithin G S (p v) := by
    rw [Set.ncard_eq_toFinset_card']
    change (H.neighborFinset v).card = _
    rw [card_neighborFinset_eq_degree, ← iso.degree_eq v]
    exact degree_induced G S (e v)
  refine ⟨S.card, hS.card_pos, hCard, H, f, hf, hBip.of_hom i, ?_, ?_, ?_⟩
  · intro u v
    rw [hDeg u, hDeg v]
    exact (hReg (p u) (e u).property (p v) (e v).property).trans (by omega)
  · simpa only [hEdges] using hAvg
  · intro T hT
    let U := T.map p
    have hUS : U ⊆ S := by
      intro x hx
      obtain ⟨v, _, rfl⟩ := mem_map.mp hx
      exact (e v).property
    have hU : U.card = T.card := card_map _
    have hBoundary := cut_ncard_eq G e T
    change {a ∈ H.edgeSet | ∃ u v : Fin S.card, u ∈ T ∧ v ∉ T ∧ a = s(u,v)}.ncard =
      (cutEdges G S U).card at hBoundary
    rw [hEdges, hBoundary]
    simpa only [hU] using hCut U hUS (by simpa only [hU] using hT)

end Erdos642SliceTransport



/- A bipartite spanning subgraph retaining at least half the edges. -/

namespace Erdos642BipartiteCut

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def cutGraph (G : SimpleGraph V) (χ : V → Bool) : SimpleGraph V :=
  G ⊓ SimpleGraph.fromRel (fun a b => χ a ≠ χ b)

omit [Fintype V] [DecidableEq V] in
theorem cut_graph_adj (G : SimpleGraph V) (χ : V → Bool) {a b : V} :
    (cutGraph G χ).Adj a b ↔ G.Adj a b ∧ χ a ≠ χ b := by
  simp only [cutGraph, inf_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h,-,h' | h'⟩
    · exact ⟨h,h'⟩
    · exact ⟨h,h'.symm⟩
  · rintro ⟨h,h'⟩
    exact ⟨h,G.ne_of_adj h,Or.inl h'⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (χ : V → Bool) :
    DecidableRel (cutGraph G χ).Adj :=
  fun _ _ => decidable_of_iff _ (cut_graph_adj G χ).symm

private def toggle (a : V) (χ : V → Bool) (b : V) : Bool :=
  if b = a then !χ b else χ b

omit [Fintype V] in
private theorem toggle_involutive (a : V) : Function.Involutive (toggle a) := by
  intro χ
  funext b
  by_cases hb : b = a <;> simp [toggle,hb]

private theorem not_ne_iff_eq (x y : Bool) : ((!x) ≠ y) ↔ x = y := by
  cases x <;> cases y <;> decide

private theorem edge_half_colorings (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    2 * (((univ : Finset (V → Bool)).filter fun χ => e ∈ (cutGraph G χ).edgeFinset).card) =
      Fintype.card (V → Bool) := by
  classical
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hAdj : G.Adj a b := (mem_edgeSet _).mp (mem_edgeFinset.mp he)
    have hab : a ≠ b := G.ne_of_adj hAdj
    have hMem (χ : V → Bool) : s(a,b) ∈ (cutGraph G χ).edgeFinset ↔ χ a ≠ χ b := by
      rw [mem_edgeFinset,mem_edgeSet,cut_graph_adj]
      exact and_iff_right hAdj
    let U := (univ : Finset (V → Bool))
    let C := U.filter (fun χ => s(a,b) ∈ (cutGraph G χ).edgeFinset)
    let D := U.filter (fun χ => s(a,b) ∉ (cutGraph G χ).edgeFinset)
    have hToggle (χ : V → Bool) :
        s(a,b) ∈ (cutGraph G (toggle a χ)).edgeFinset ↔ s(a,b) ∉ (cutGraph G χ).edgeFinset := by
      simp only [hMem,toggle,if_true,if_neg hab.symm,not_ne_iff_eq,not_ne_iff]
    have hEq : C.card = D.card := by
      apply Finset.card_nbij' (toggle a) (toggle a)
      · intro χ hχ
        have hm := (mem_filter.mp hχ).2
        exact mem_filter.mpr ⟨mem_univ _,fun h => ((hToggle χ).mp h) hm⟩
      · intro χ hχ
        have hm := (mem_filter.mp hχ).2
        exact mem_filter.mpr ⟨mem_univ _,(hToggle χ).mpr hm⟩
      · intro χ _
        exact toggle_involutive a χ
      · intro χ _
        exact toggle_involutive a χ
    have hCD : C.card + D.card = U.card := Finset.card_filter_add_card_filter_not _
    rw [← hEq,card_univ] at hCD
    change 2 * C.card = _
    omega

theorem exists_half_edge_bipartite (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧ G.edgeSet.ncard ≤ 2 * H.edgeSet.ncard := by
  classical
  let U := (univ : Finset (V → Bool))
  let E := G.edgeFinset
  let C (χ : V → Bool) := (cutGraph G χ).edgeFinset
  have hC (χ : V → Bool) : C χ ⊆ E :=
    edgeFinset_mono (show cutGraph G χ ≤ G from inf_le_left)
  have hSum : (∑ χ ∈ U, 2 * (C χ).card) = U.card * E.card := by
    calc
      _ = ∑ χ ∈ U, ∑ e ∈ E, 2 * (if e ∈ C χ then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro χ _
        have hCE : E.filter (fun e => e ∈ C χ) = C χ := by
          ext e
          simp only [mem_filter]
          exact and_iff_right_of_imp (fun h => hC χ h)
        rw [← Finset.mul_sum,← Finset.card_filter,hCE]
      _ = ∑ e ∈ E, ∑ χ ∈ U, 2 * (if e ∈ C χ then 1 else 0) := Finset.sum_comm
      _ = ∑ e ∈ E, U.card := by
        apply Finset.sum_congr rfl
        intro e he
        rw [← Finset.mul_sum,← Finset.card_filter,card_univ]
        exact edge_half_colorings G he
      _ = _ := by simp [Nat.mul_comm]
  have hExists : ∃ χ, E.card ≤ 2 * (C χ).card := by
    by_contra! h
    have hlt := Finset.sum_lt_sum_of_nonempty (s := U)
      (show U.Nonempty from ⟨fun _ => false,mem_univ _⟩) (fun χ _ => h χ)
    have : (∑ χ ∈ U, E.card) = U.card * E.card := by simp
    rw [this,hSum] at hlt
    exact (lt_irrefl _) hlt
  obtain ⟨χ,hχ⟩ := hExists
  refine ⟨cutGraph G χ,inf_le_left,?_,?_⟩
  · let e : Bool ≃ Fin 2 := Fintype.equivFinOfCardEq (by decide)
    exact ⟨Coloring.mk (fun v => e (χ v))
      (fun {_ _} h he => ((cut_graph_adj G χ).mp h).2 (e.injective he))⟩
  · rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    exact hχ

end Erdos642BipartiteCut


namespace Erdos642ExpanderGoal

abbrev H1 : Prop := OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1.H1

end Erdos642ExpanderGoal


namespace Erdos642ExpansionH1

open Filter Finset SimpleGraph
open Erdos642BipartiteCut Erdos642ExpandingSlice Erdos642SliceTransport

/-- The regularization input supplies a dense induced slice of a bipartite subgraph. -/
def Regularization : Prop :=
  ∀ n : ℕ, 2 ≤ Real.log n → ∀ B : SimpleGraph (Fin n), B.IsBipartite →
    Real.log n ^ 2 / 2 ≤ 2 * (B.edgeSet.ncard : ℝ) / n →
    ∃ (U : Finset (Fin n)) (K : SimpleGraph (Fin n)), U.Nonempty ∧ K ≤ B ∧
      let H := K.induce (U : Set (Fin n))
      (2 * (B.edgeSet.ncard : ℝ) / n) / (100 * Real.log n) ≤
        2 * (H.edgeSet.ncard : ℝ) / U.card ∧
      ∀ v w : U, (H.neighborSet v).ncard ≤ 6 * (H.neighborSet w).ncard

/-- The bipartite cut, logarithmic cleaning, and transport assemble the exact
extraction statement once the almost-regular subgraph theorem is provided. -/
theorem h1_of_regularization (hReg : Regularization) : Erdos642ExpanderGoal.H1 := by
  have hLarge : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hLarge,eventually_ge_atTop (1 : ℕ)] with n hN hn
  intro G hG
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLog : 0 < Real.log n := by linarith only [hN]
  let avg (H : SimpleGraph (Fin n)) : ℝ := 2 * (H.edgeSet.ncard : ℝ) / n
  have hGpos : 0 < avg G := by
    have h := sq_pos_of_pos hLog
    exact h.trans_le hG
  obtain ⟨B,hBG,hB,hBCount⟩ := exists_half_edge_bipartite G
  have hHalf : avg G / 2 ≤ avg B := by
    have h : (G.edgeSet.ncard : ℝ) ≤ 2 * (B.edgeSet.ncard : ℝ) := by exact_mod_cast hBCount
    have h' := div_le_div_of_nonneg_right h hnR.le
    calc
      avg G / 2 = (G.edgeSet.ncard : ℝ) / n := by dsimp only [avg]; ring
      _ ≤ avg B := h'
  have hBasis : Real.log n ^ 2 / 2 ≤ avg B := (div_le_div_of_nonneg_right hG (by norm_num)).trans hHalf
  obtain ⟨U,K,hU,hKB,hDensity,hRatio⟩ := hReg n hN B hB hBasis
  let J : SimpleGraph U := K.induce (U : Set (Fin n))
  let j : J →g B := ⟨Subtype.val, fun h => hKB h⟩
  let φ : J →g G := (Hom.ofLE hBG).comp j
  have hφ : Function.Injective φ := Subtype.val_injective
  have hJB : J.IsBipartite := hB.of_hom j
  let _ : Nonempty U := ⟨⟨hU.choose,hU.choose_spec⟩⟩
  have hJCard : Fintype.card U ≤ n := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using U.card_le_univ
  have hJEdges : J.edgeSet.ncard = J.edgeFinset.card := by
    rw [← Set.ncard_coe_finset,coe_edgeFinset]
  change avg B / (100 * Real.log n) ≤ 2 * (J.edgeSet.ncard : ℝ) / U.card at hDensity
  rw [hJEdges] at hDensity
  have hJPos : 0 < J.edgeFinset.card := by
    have hd : 0 < (avg B) / (100 * Real.log n) :=
      div_pos ((show 0 < avg G / 2 by positivity).trans_le hHalf) (by positivity)
    have h := hd.trans_le hDensity
    have hU' : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
    have hp := (lt_div_iff₀ hU').mp h
    have hp' : (0 : ℝ) < J.edgeFinset.card := by linarith only [hp]
    exact_mod_cast hp'
  have hJR (v w : U) : J.degree v ≤ 6 * J.degree w := by
    have h := hRatio v w
    rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card'] at h
    exact h
  obtain ⟨S,hS,hAvgS,hR,hCut⟩ := regular_graph_has_expanding_slice J
    (by linarith only [hN]) hJCard hJPos hJR
  have hAvg : avg G / (600 * Real.log n) ≤
      2 * ((Erdos642InducedCounts.internalEdges J S).card : ℝ) / (S.card : ℝ) := by
    have hd : (avg B) / (100 * Real.log n) ≤ 2 * (J.edgeFinset.card : ℝ) / (Fintype.card U : ℝ) := by
      simpa only [Fintype.card_coe] using hDensity
    calc
      _ ≤ avg G / (400 * Real.log n) :=
        div_le_div_of_nonneg_left hGpos.le (by positivity) (by linarith only [hLog])
      _ = ((avg G / 2) / (100 * Real.log n)) / 2 := by ring
      _ ≤ ((avg B) / (100 * Real.log n)) / 2 :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hHalf (by positivity)) (by norm_num)
      _ ≤ (2 * (J.edgeFinset.card : ℝ) / (Fintype.card U : ℝ)) / 2 :=
        div_le_div_of_nonneg_right hd (by norm_num)
      _ ≤ _ := hAvgS
  exact transport_expanding_slice J φ hφ hJB hS hAvg hR hCut

theorem regularization : Regularization := by
  intro n hN B hB hInput
  classical
  have hL : 0 < Real.log n := by linarith only [hN]
  have hAvg : 0 < 2 * (B.edgeSet.ncard : ℝ) / n := by
    exact (show 0 < Real.log n ^ 2 / 2 by positivity).trans_le hInput
  have hCard : B.edgeSet.ncard = B.edgeFinset.card := by
    rw [← Set.ncard_coe_finset,coe_edgeFinset]
  rw [hCard] at hAvg
  have hEdges : 0 < B.edgeFinset.card := by
    by_contra! h
    have hz : B.edgeFinset.card = 0 := Nat.eq_zero_of_le_zero h
    simp [hz] at hAvg
  obtain ⟨U,K,hU,hKB,hDensity,hDegrees⟩ :=
    Erdos642Regularization.exists_almost_regular_bipartite B hN
      (by simp) hB hEdges
  have hBound : (2 * (B.edgeSet.ncard : ℝ) / n) / (100 * Real.log n) ≤
      (2 * (B.edgeSet.ncard : ℝ) / n) / (10 * Real.log n) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hL])
  refine ⟨U,K,hU,hKB,hBound.trans (by simpa only [Fintype.card_fin] using hDensity),?_⟩
  intro v w
  exact (hDegrees v w).trans (by omega)

end Erdos642ExpansionH1


theorem Erdos642ExpansionH1.proved_h1 : OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1.H1 :=
  Erdos642ExpansionH1.h1_of_regularization Erdos642ExpansionH1.regularization

end Erdos642ExtractionFile

section Erdos642FiniteProbabilityFile

/- A finite adapted lower-tail estimate for the random-walk sampling argument. -/

namespace Erdos642FiniteProbability

open Finset

variable {α : Type*} [Fintype α]

/-- Backward evaluation of an n-step payoff at time t and initial state x. -/
noncomputable def future (K : ℕ → α → α → ℝ) (payoff : α → ℝ) : ℕ → ℕ → α → ℝ
  | 0, _, x => payoff x
  | n + 1, t, x => ∑ y : α, K t x y * future K payoff n (t + 1) y

@[simp] theorem future_zero (K : ℕ → α → α → ℝ) (payoff : α → ℝ) (t : ℕ) (x : α) :
    future K payoff 0 t x = payoff x := rfl

theorem future_succ (K : ℕ → α → α → ℝ) (payoff : α → ℝ) (n t : ℕ) (x : α) :
    future K payoff (n + 1) t x = ∑ y : α, K t x y * future K payoff n (t + 1) y := rfl

/-- The rows are transition probabilities through the given time horizon. -/
def IsStochasticThrough (K : ℕ → α → α → ℝ) (N : ℕ) : Prop :=
  ∀ t < N, ∀ x : α, (∀ y : α, 0 ≤ K t x y) ∧ ∑ y : α, K t x y = 1

/-- Expected indicator of the terminal score being at most s. -/
noncomputable def lowerTail (K : ℕ → α → α → ℝ) (score : α → ℕ)
    (s : ℝ) (n t : ℕ) (x : α) : ℝ :=
  future K (fun y => if (score y : ℝ) ≤ s then 1 else 0) n t x

private noncomputable def potential (score : α → ℕ) (s : ℝ) (x : α) : ℝ :=
  if (score x : ℝ) ≤ s then Real.exp (-(score x : ℝ)) else 0

omit [Fintype α] in
private theorem potential_nonneg (score : α → ℕ) (s : ℝ) (x : α) :
    0 ≤ potential score s x := by
  unfold potential
  split <;> positivity

omit [Fintype α] in
private theorem potential_le (score : α → ℕ) (s : ℝ) (x : α) :
    potential score s x ≤ Real.exp (-(score x : ℝ)) := by
  unfold potential
  split
  · exact le_rfl
  · positivity

private theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have ht : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp 1]
  rw [Real.exp_neg, inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith only [ht])

omit [Fintype α] in
private theorem potential_decreases_on_success (score : α → ℕ) (s : ℝ) {x y : α}
    (hx : (score x : ℝ) ≤ s) (hxy : score x < score y) :
    potential score s y ≤ potential score s x / 2 := by
  have hxy' : (score x : ℝ) + 1 ≤ score y := by exact_mod_cast Nat.succ_le_of_lt hxy
  calc
    _ ≤ Real.exp (-(score y : ℝ)) := potential_le score s y
    _ ≤ Real.exp (-(score x : ℝ) - 1) := Real.exp_le_exp.mpr (by linarith only [hxy'])
    _ = Real.exp (-(score x : ℝ)) * Real.exp (-1) := by rw [sub_eq_add_neg, Real.exp_add]
    _ ≤ Real.exp (-(score x : ℝ)) * (1 / 2) :=
      mul_le_mul_of_nonneg_left exp_neg_one_le_half (Real.exp_nonneg _)
    _ = _ := by rw [potential, if_pos hx]; ring

private theorem potential_step_bound (K : ℕ → α → α → ℝ) (score : α → ℕ) (s p : ℝ)
    (t : ℕ) (x : α) (hnonneg : ∀ y : α, 0 ≤ K t x y) (hnorm : ∑ y : α, K t x y = 1)
    (hmono : ∀ y, 0 < K t x y → score x ≤ score y)
    (hsuccess : (score x : ℝ) ≤ s →
      p ≤ ∑ y ∈ (univ : Finset α).filter (fun y => score x < score y), K t x y) :
    (∑ y : α, K t x y * potential score s y) ≤
      (1 - p / 2) * potential score s x := by
  classical
  by_cases hx : (score x : ℝ) ≤ s
  · let A := (univ : Finset α).filter fun y => score x < score y
    let B := (univ : Finset α).filter fun y => ¬ score x < score y
    let w := potential score s x
    have hwn : 0 ≤ w := potential_nonneg _ _ _
    have hTotal : (∑ y ∈ A, K t x y) + (∑ y ∈ B, K t x y) = 1 := by
      rw [show (∑ y ∈ A, K t x y) + (∑ y ∈ B, K t x y) = ∑ y : α, K t x y from
        sum_filter_add_sum_filter_not _ _ _]
      exact hnorm
    have hA (y : α) (hy : y ∈ A) : potential score s y ≤ w / 2 :=
      potential_decreases_on_success score s hx (mem_filter.mp hy).2
    have hB (y : α) (hy : y ∈ B) : K t x y * potential score s y ≤ K t x y * w := by
      by_cases hk : K t x y = 0
      · simp [hk]
      · have hpos : 0 < K t x y := lt_of_le_of_ne (hnonneg y) (Ne.symm hk)
        have he : score y = score x :=
          le_antisymm (Nat.le_of_not_gt (mem_filter.mp hy).2) (hmono y hpos)
        simp [w, potential, he]
    have hEnough : p ≤ ∑ y ∈ A, K t x y := hsuccess hx
    have hEnough' := mul_le_mul_of_nonneg_right hEnough (show 0 ≤ w / 2 by positivity)
    calc
      _ = (∑ y ∈ A, K t x y * potential score s y) +
          (∑ y ∈ B, K t x y * potential score s y) :=
        (sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ (∑ y ∈ A, K t x y * (w / 2)) + (∑ y ∈ B, K t x y * w) :=
        add_le_add (sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hA y hy) (hnonneg y)))
          (sum_le_sum hB)
      _ = w - (∑ y ∈ A, K t x y) * (w / 2) := by
        rw [← sum_mul, ← sum_mul]
        have h := congrArg (fun z : ℝ => z * w) hTotal
        nlinarith only [h]
      _ ≤ _ := by change _ ≤ (1 - p / 2) * w; nlinarith only [hEnough']
  · have hz : ∀ y : α, K t x y * potential score s y = 0 := by
      intro y
      by_cases hk : K t x y = 0
      · simp [hk]
      · have hpos : 0 < K t x y := lt_of_le_of_ne (hnonneg y) (Ne.symm hk)
        have hxy : (score x : ℝ) ≤ score y := by exact_mod_cast hmono y hpos
        have hy : ¬ (score y : ℝ) ≤ s := fun h => hx (hxy.trans h)
        simp [potential, hy]
    simp only [hz, Finset.sum_const_zero]
    simp [potential, hx]

/-- Iterate any one-step upper bound with a nonnegative kernel. -/
theorem future_le_of_step (K : ℕ → α → α → ℝ) (payoff weight : α → ℝ)
    {N : ℕ} {C q : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hnonneg : ∀ t < N, ∀ x y : α, 0 ≤ K t x y)
    (hbase : ∀ x, payoff x ≤ C * weight x)
    (hstep : ∀ t < N, ∀ x : α, (∑ y : α, K t x y * weight y) ≤ q * weight x) :
    ∀ n t : ℕ, t + n ≤ N → ∀ x : α, future K payoff n t x ≤ C * q ^ n * weight x := by
  intro n
  induction n with
  | zero => intro t _ x; simpa only [future_zero, pow_zero, mul_one] using hbase x
  | succ n ih =>
    intro t htn x
    have ht : t < N := by omega
    have hnext : (t + 1) + n ≤ N := by omega
    rw [future_succ]
    calc
      _ ≤ ∑ y : α, K t x y * (C * q ^ n * weight y) :=
        sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih (t + 1) hnext y) (hnonneg t ht x y))
      _ = C * q ^ n * (∑ y : α, K t x y * weight y) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro y _
        ring
      _ ≤ C * q ^ n * (q * weight x) :=
        mul_le_mul_of_nonneg_left (hstep t ht x) (mul_nonneg hC (pow_nonneg hq _))
      _ = _ := by rw [pow_succ]; ring

/-- A nondecreasing score with conditional success mass at least p while the
score is at most s has an exponential upper bound on its terminal lower tail.
The score may jump by more than one, and the transition law can be adapted
by including the observed history in the state. -/
theorem lowerTail_le_exp (K : ℕ → α → α → ℝ) (score : α → ℕ)
    (N : ℕ) (s p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hK : IsStochasticThrough K N)
    (hmono : ∀ t < N, ∀ x y, 0 < K t x y → score x ≤ score y)
    (hsuccess : ∀ t < N, ∀ x, (score x : ℝ) ≤ s →
      p ≤ ∑ y ∈ (univ : Finset α).filter (fun y => score x < score y), K t x y)
    (x : α) :
    lowerTail K score s N 0 x ≤ Real.exp (s - (score x : ℝ) - (N : ℝ) * p / 2) := by
  let payoff : α → ℝ := fun y => if (score y : ℝ) ≤ s then 1 else 0
  let q := 1 - p / 2
  have hq : 0 ≤ q := by dsimp [q]; linarith only [hp1]
  have hbase (y : α) : payoff y ≤ Real.exp s * potential score s y := by
    by_cases hy : (score y : ℝ) ≤ s
    · simp only [payoff, potential, if_pos hy, ← Real.exp_add]
      exact Real.one_le_exp (by linarith only [hy])
    · simp [payoff, potential, hy]
  have hiter := future_le_of_step K payoff (potential score s)
    (Real.exp_nonneg s) hq (fun t ht y => (hK t ht y).1) hbase
    (fun t ht y => potential_step_bound K score s p t y (hK t ht y).1 (hK t ht y).2
      (hmono t ht y) (hsuccess t ht y)) N 0 (by omega) x
  have hqpow : q ^ N ≤ Real.exp (-(N : ℝ) * p / 2) := by
    have hqle : q ≤ Real.exp (-(p / 2)) := Real.one_sub_le_exp_neg _
    have hpow := pow_le_pow_left₀ hq hqle N
    rw [← Real.exp_nat_mul] at hpow
    have he : (N : ℝ) * -(p / 2) = -(N : ℝ) * p / 2 := by ring
    rwa [he] at hpow
  calc
    lowerTail K score s N 0 x ≤ Real.exp s * q ^ N * potential score s x := hiter
    _ ≤ Real.exp s * Real.exp (-(N : ℝ) * p / 2) * Real.exp (-(score x : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hqpow (Real.exp_nonneg _))
        (potential_le _ _ _) (potential_nonneg _ _ _) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- When the desired count is at most one quarter of the guaranteed mean,
its lower-tail probability is at most exp(-s). -/
theorem lowerTail_le_exp_neg_of_le_quarter (K : ℕ → α → α → ℝ) (score : α → ℕ)
    (N : ℕ) (s p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hK : IsStochasticThrough K N)
    (hmono : ∀ t < N, ∀ x y, 0 < K t x y → score x ≤ score y)
    (hsuccess : ∀ t < N, ∀ x, (score x : ℝ) ≤ s →
      p ≤ ∑ y ∈ (univ : Finset α).filter (fun y => score x < score y), K t x y)
    (hs : s ≤ (N : ℝ) * p / 4) (x : α) :
    lowerTail K score s N 0 x ≤ Real.exp (-s) := by
  apply (lowerTail_le_exp K score N s p hp0 hp1 hK hmono hsuccess x).trans
  exact Real.exp_le_exp.mpr (by linarith only [hs, Nat.cast_nonneg (α := ℝ) (score x)])

/-- Backward expectations preserve pointwise domination for a stochastic kernel. -/
theorem future_mono {K : ℕ → α → α → ℝ} {N : ℕ} (hK : IsStochasticThrough K N)
    {f g : α → ℝ} (hfg : ∀ x, f x ≤ g x) :
    ∀ n t : ℕ, t + n ≤ N → ∀ x : α, future K f n t x ≤ future K g n t x := by
  intro n
  induction n with
  | zero => intro t _ x; exact hfg x
  | succ n ih =>
    intro t htn x
    rw [future_succ, future_succ]
    exact sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
      (ih (t + 1) (by omega) y) ((hK t (by omega) x).1 y)

@[simp] theorem future_zero_payoff (K : ℕ → α → α → ℝ) :
    ∀ n t : ℕ, ∀ x : α, future K (fun _ => 0) n t x = 0 := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro t x; simp [future_succ, ih]

theorem future_add (K : ℕ → α → α → ℝ) (f g : α → ℝ) :
    ∀ n t : ℕ, ∀ x : α,
      future K (fun y => f y + g y) n t x = future K f n t x + future K g n t x := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro t x; simp only [future_succ, ih, mul_add, sum_add_distrib]

theorem future_finset_sum {I : Type*} (K : ℕ → α → α → ℝ) (J : Finset I)
    (f : I → α → ℝ) (n t : ℕ) (x : α) :
    future K (fun y => ∑ i ∈ J, f i y) n t x = ∑ i ∈ J, future K (f i) n t x := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert i J hi ih => simp [hi, future_add, ih]

/-- Terminal probability of a predicate on the state. -/
noncomputable def eventMass (K : ℕ → α → α → ℝ) (P : α → Prop) (n t : ℕ) (x : α) : ℝ := by
  classical
  exact future K (fun y => if P y then 1 else 0) n t x

/-- The finite union bound for terminal events. -/
theorem eventMass_union_le {I : Type*} {K : ℕ → α → α → ℝ} {N : ℕ}
    (hK : IsStochasticThrough K N) (J : Finset I) (P : I → α → Prop)
    (n t : ℕ) (htn : t + n ≤ N) (x : α) :
    eventMass K (fun y => ∃ i ∈ J, P i y) n t x ≤
      ∑ i ∈ J, eventMass K (P i) n t x := by
  classical
  let f i (y : α) : ℝ := @ite ℝ (P i y) (Classical.propDecidable _) 1 0
  have hp (y : α) :
      @ite ℝ (∃ i ∈ J, P i y) (Classical.propDecidable _) 1 0 ≤ ∑ i ∈ J, f i y := by
    by_cases he : ∃ i ∈ J, P i y
    · rw [if_pos he]
      obtain ⟨i, hi, hiy⟩ := he
      have hterm : f i y = 1 := if_pos hiy
      rw [← hterm]
      exact single_le_sum (f := fun j => f j y) (fun j _ => by unfold f; split <;> positivity) hi
    · rw [if_neg he]
      exact sum_nonneg (fun i _ => by unfold f; split <;> positivity)
  exact (future_mono hK hp n t htn x).trans_eq (future_finset_sum K J f n t x)

/-- Evaluation over consecutive time blocks is iterated conditioning. -/
theorem future_split (K : ℕ → α → α → ℝ) (f : α → ℝ) (m n : ℕ) :
    ∀ t : ℕ, ∀ x : α, future K f (m + n) t x =
      future K (fun y => future K f n (t + m) y) m t x := by
  induction m with
  | zero => intro t x; simp
  | succ m ih =>
    intro t x
    rw [Nat.succ_add, future_succ, future_succ]
    apply sum_congr rfl
    intro y _
    have hTime : (t + 1) + m = t + (m + 1) := by omega
    rw [ih (t + 1) y, hTime]

theorem future_one {K : ℕ → α → α → ℝ} {N : ℕ} (hK : IsStochasticThrough K N) :
    ∀ n t : ℕ, t + n ≤ N → ∀ x : α, future K (fun _ => 1) n t x = 1 := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ m ih =>
    intro t htn x
    have ht : t < N := by omega
    have hNext : (t + 1) + m ≤ N := by omega
    simpa only [future_succ, ih _ hNext, mul_one] using (hK t ht x).2

theorem eventMass_compl_add {K : ℕ → α → α → ℝ} {N : ℕ}
    (hK : IsStochasticThrough K N) (P : α → Prop)
    (n t : ℕ) (htn : t + n ≤ N) (x : α) :
    eventMass K (fun y => ¬ P y) n t x + eventMass K P n t x = 1 := by
  classical
  let f (y : α) : ℝ := @ite ℝ (¬ P y) (Classical.propDecidable _) 1 0
  let g (y : α) : ℝ := @ite ℝ (P y) (Classical.propDecidable _) 1 0
  change future K f n t x + future K g n t x = 1
  rw [← future_add]
  have hsum : (fun y => f y + g y) = fun _ => 1 := by
    funext y
    by_cases h : P y <;> simp [f, g, h]
  rw [hsum, future_one hK n t htn x]

end Erdos642FiniteProbability

end Erdos642FiniteProbabilityFile

section Erdos642RandomWalkKernelFile

/- The finite nearest-neighbor walk and its transition identities. -/

namespace Erdos642RandomWalkKernel

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Uniform mass on the neighbors of the starting vertex. -/
noncomputable def step (u v : V) : ℝ :=
  if G.Adj u v then (G.degree u : ℝ)⁻¹ else 0

/-- Transition weights after a given number of steps. -/
noncomputable def walkWeight : ℕ → V → V → ℝ
  | 0, u, v => if u = v then 1 else 0
  | n + 1, u, v => ∑ x : V, step G u x * walkWeight n x v

@[simp] theorem walkWeight_zero (u v : V) :
    walkWeight G 0 u v = if u = v then 1 else 0 := rfl

theorem walkWeight_succ (n : ℕ) (u v : V) :
    walkWeight G (n + 1) u v = ∑ x : V, step G u x * walkWeight G n x v := rfl

omit [DecidableEq V] in
theorem step_nonneg (u v : V) : 0 ≤ step G u v := by
  unfold step
  split
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_rfl

omit [DecidableEq V] in
theorem sum_step (hPos : ∀ u, 0 < G.degree u) (u : V) :
    ∑ v : V, step G u v = 1 := by
  have hne : (G.degree u : ℝ) ≠ 0 := by exact_mod_cast (hPos u).ne'
  unfold step
  simp only [← Finset.sum_filter, ← G.neighborFinset_eq_filter,
    Finset.sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree, mul_inv_cancel₀ hne]

theorem walkWeight_nonneg (n : ℕ) (u v : V) : 0 ≤ walkWeight G n u v := by
  induction n generalizing u v with
  | zero =>
    rw [walkWeight_zero]
    split <;> positivity
  | succ n ih =>
    rw [walkWeight_succ]
    exact sum_nonneg fun _ _ => mul_nonneg (step_nonneg G _ _) (ih _ _)

theorem sum_walkWeight (hPos : ∀ u, 0 < G.degree u) (n : ℕ) (u : V) :
    ∑ v : V, walkWeight G n u v = 1 := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    simp only [walkWeight_succ]
    rw [sum_comm]
    simp only [← mul_sum, ih, mul_one, sum_step G hPos]

@[simp] theorem walkWeight_one (u v : V) : walkWeight G 1 u v = step G u v := by
  simp [walkWeight_succ, mul_ite]

/-- Chapman–Kolmogorov for the finite homogeneous walk. -/
theorem walkWeight_add (a b : ℕ) (u v : V) :
    walkWeight G (a + b) u v = ∑ x : V, walkWeight G a u x * walkWeight G b x v := by
  induction a generalizing u with
  | zero => simp [ite_mul]
  | succ a ih =>
    simp only [Nat.succ_add, walkWeight_succ, ih, mul_sum, sum_mul, mul_assoc]
    exact sum_comm

theorem walkWeight_succ_right (n : ℕ) (u v : V) :
    walkWeight G (n + 1) u v = ∑ x : V, walkWeight G n u x * step G x v := by
  rw [walkWeight_add]
  simp only [walkWeight_one]

omit [DecidableEq V] in
private theorem step_balance (hPos : ∀ u, 0 < G.degree u) (u v : V) :
    (G.degree u : ℝ) * step G u v = (G.degree v : ℝ) * step G v u := by
  have hu : (G.degree u : ℝ) ≠ 0 := by exact_mod_cast (hPos u).ne'
  have hv : (G.degree v : ℝ) ≠ 0 := by exact_mod_cast (hPos v).ne'
  by_cases h : G.Adj u v
  · simp [step, h, h.symm, hu, hv]
  · have hn : ¬ G.Adj v u := fun hRev => h hRev.symm
    simp [step, h, hn]

/-- Detailed balance with the degree measure at every time. -/
theorem walkWeight_balance (hPos : ∀ u, 0 < G.degree u)
    (n : ℕ) (u v : V) :
    (G.degree u : ℝ) * walkWeight G n u v =
      (G.degree v : ℝ) * walkWeight G n v u := by
  induction n generalizing u v with
  | zero =>
    by_cases h : u = v
    · subst v
      rfl
    · simp [h,Ne.symm h]
  | succ n ih =>
    rw [walkWeight_succ, walkWeight_succ_right]
    simp only [mul_sum]
    apply sum_congr rfl
    intro x _
    rw [← mul_assoc, step_balance G hPos, mul_right_comm, ih, mul_assoc]

theorem degree_stationary (hPos : ∀ u, 0 < G.degree u) (n : ℕ) (v : V) :
    (∑ u : V, (G.degree u : ℝ) * walkWeight G n u v) = (G.degree v : ℝ) := by
  simp only [walkWeight_balance G hPos n _ v, ← mul_sum, sum_walkWeight G hPos, mul_one]

/-- The reversed kernel controls the forward kernel under a degree-ratio bound. -/
theorem walkWeight_le_mul_reverse (hPos : ∀ u, 0 < G.degree u) (n : ℕ) (u v : V)
    {C : ℝ} (hDegree : (G.degree v : ℝ) ≤ C * (G.degree u : ℝ)) :
    walkWeight G n u v ≤ C * walkWeight G n v u := by
  have hu : 0 < (G.degree u : ℝ) := by exact_mod_cast hPos u
  apply (mul_le_mul_iff_right₀ hu).mp
  calc
    (G.degree u : ℝ) * walkWeight G n u v = (G.degree v : ℝ) * walkWeight G n v u :=
      walkWeight_balance G hPos n u v
    _ ≤ (C * (G.degree u : ℝ)) * walkWeight G n v u :=
      mul_le_mul_of_nonneg_right hDegree (walkWeight_nonneg G n v u)
    _ = (G.degree u : ℝ) * (C * walkWeight G n v u) := by ring

omit [DecidableEq V] in
theorem step_le_inv_minDegree {δ : ℕ} (hδ : 0 < δ) (hMin : ∀ u, δ ≤ G.degree u)
    (u v : V) :
    step G u v ≤ (δ : ℝ)⁻¹ := by
  have hδ₀ : 0 < (δ : ℝ) := by exact_mod_cast hδ
  unfold step
  split
  · exact inv_anti₀ hδ₀ (by exact_mod_cast hMin u)
  · exact inv_nonneg.mpr hδ₀.le

/-- After any positive number of steps, no single vertex has mass above
the reciprocal minimum degree. -/
theorem walkWeight_le_inv_minDegree {δ : ℕ} (hδ : 0 < δ) (hMin : ∀ u, δ ≤ G.degree u)
    {n : ℕ} (hn : 0 < n) (u v : V) :
    walkWeight G n u v ≤ (δ : ℝ)⁻¹ := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [walkWeight_succ_right]
  calc
    _ ≤ ∑ x : V, walkWeight G t u x * (δ : ℝ)⁻¹ :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
        (step_le_inv_minDegree G hδ hMin x v) (walkWeight_nonneg G t u x)
    _ = _ := by rw [← sum_mul, sum_walkWeight G (fun x => hδ.trans_le (hMin x)), one_mul]

omit [DecidableEq V] in
theorem step_pos_iff_adj (u v : V) : 0 < step G u v ↔ G.Adj u v := by
  by_cases hadj : G.Adj u v
  · have hp : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨v, hadj⟩
    have hp' : 0 < (G.degree u : ℝ) := by exact_mod_cast hp
    simp [step, hadj, hp']
  · simp [step, hadj]

/-- Positive transition weight exactly detects an admissible walk of the
prescribed length. -/
theorem walkWeight_pos_iff_exists_walk (n : ℕ) (u v : V) :
    0 < walkWeight G n u v ↔ ∃ p : G.Walk u v, p.length = n := by
  induction n generalizing u v with
  | zero =>
    rw [Walk.exists_length_eq_zero_iff, walkWeight_zero]
    by_cases h : u = v <;> simp [h]
  | succ n ih =>
    rw [walkWeight_succ, Finset.sum_pos_iff_of_nonneg (fun x _ =>
      mul_nonneg (step_nonneg G u x) (walkWeight_nonneg G n x v))]
    simp only [mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      rcases mul_pos_iff.mp hx with ⟨ha, hp⟩ | ⟨ha, hp⟩
      · obtain ⟨p, hp'⟩ := (ih x v).mp hp
        exact ⟨Walk.cons ((step_pos_iff_adj G u x).mp ha) p, by simp [hp']⟩
      · exact (not_lt_of_ge (step_nonneg G u x) ha).elim
    · rintro ⟨p, hp⟩
      cases p with
      | nil => simp at hp
      | cons ha p =>
        have hLen : p.length = n := by simpa using hp
        exact ⟨_, mul_pos ((step_pos_iff_adj G _ _).mpr ha) ((ih _ _).mpr ⟨p, hLen⟩)⟩

/-- A bipartite walk cannot arrive in the wrong color class for the elapsed parity. -/
theorem walkWeight_zero_of_wrong_parity (C : G.Coloring (Fin 2))
    (n : ℕ) (u v : V) (h : (C u).val + (C v).val + n ≡ 1 [MOD 2]) :
    walkWeight G n u v = 0 := by
  induction n generalizing u v with
  | zero =>
    have huv : u ≠ v := by
      intro he
      subst v
      change ((C u).val + (C u).val + 0) % 2 = 1 % 2 at h
      omega
    simp [huv]
  | succ n ih =>
    rw [walkWeight_succ]
    apply sum_eq_zero
    intro x _
    by_cases ha : G.Adj u x
    · have hne : C u ≠ C x := C.map_adj ha
      have hval : (C u).val ≠ (C x).val := fun he => hne (Fin.ext he)
      have hu := (C u).isLt
      have hx := (C x).isLt
      have hNext : (C x).val + (C v).val + n ≡ 1 [MOD 2] := by
        change ((C u).val + (C v).val + (n + 1)) % 2 = 1 % 2 at h
        change ((C x).val + (C v).val + n) % 2 = 1 % 2
        omega
      rw [ih x v hNext, mul_zero]
    · simp [step, ha]

/-- Running the walk for any chosen number of steps between sample times
gives a stochastic kernel for finite-payoff and seen-set calculations. -/
theorem stochasticThrough (hPos : ∀ u, 0 < G.degree u) (stride : ℕ → ℕ) (N : ℕ) :
    Erdos642FiniteProbability.IsStochasticThrough (fun t => walkWeight G (stride t)) N :=
  fun t _ u => ⟨walkWeight_nonneg G (stride t) u, sum_walkWeight G hPos (stride t) u⟩

/-- The finite-payoff operator for fixed-stride sampling evaluates the payoff
against the walk kernel at the elapsed number of graph steps. -/
theorem future_walkWeight (stride : ℕ) (f : V → ℝ) (n t : ℕ) (u : V) :
    Erdos642FiniteProbability.future (fun _ => walkWeight G stride) f n t u =
      ∑ v : V, walkWeight G (n * stride) u v * f v := by
  induction n generalizing t u with
  | zero => simp [ite_mul]
  | succ n ih =>
    rw [Erdos642FiniteProbability.future_succ, Nat.succ_mul, add_comm (n * stride)]
    simp only [ih, walkWeight_add, mul_sum, sum_mul, mul_assoc]
    exact sum_comm

end Erdos642RandomWalkKernel

end Erdos642RandomWalkKernelFile

section Erdos642BadStartsFile

/- Averaging prior-vertex exposure and controlling bad endpoints of a mixing block. -/

namespace Erdos642BadStarts

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The probability that the vertex at time t lies in A. -/
noncomputable def endpointMass (t : ℕ) (A : Finset V) (v : V) : ℝ :=
  ∑ u ∈ A, Erdos642RandomWalkKernel.walkWeight G t v u

/-- The sum of the probabilities of an A-hit at every time from 1 through k. -/
noncomputable def hitEstimate (k : ℕ) (A : Finset V) (v : V) : ℝ :=
  ∑ i ∈ range k, endpointMass G (i+1) A v

/-- Starting vertices with a large union-bound estimate for hitting A. -/
noncomputable def badStarts (k : ℕ) (A : Finset V) (β : ℝ) : Finset V := by
  classical
  exact univ.filter fun v => β ≤ hitEstimate G k A v

theorem notMem_badStarts_iff (k : ℕ) (A : Finset V) (β : ℝ) (v : V) :
    v ∉ badStarts G k A β ↔ hitEstimate G k A v < β := by
  classical
  simp [badStarts, not_le]

theorem endpointMass_nonneg (t : ℕ) (A : Finset V) (v : V) : 0 ≤ endpointMass G t A v :=
  sum_nonneg fun _ _ => Erdos642RandomWalkKernel.walkWeight_nonneg G _ _ _

theorem hitEstimate_nonneg (k : ℕ) (A : Finset V) (v : V) : 0 ≤ hitEstimate G k A v :=
  sum_nonneg fun _ _ => endpointMass_nonneg G _ _ _

theorem endpointMass_le_card_mul (t : ℕ) (A : Finset V) (v : V) {ρ : ℝ}
    (hMax : ∀ w, Erdos642RandomWalkKernel.walkWeight G t v w ≤ ρ) :
    endpointMass G t A v ≤ ρ * (A.card : ℝ) := by
  calc
    endpointMass G t A v ≤ ∑ _ ∈ A, ρ := sum_le_sum fun w _ => hMax w
    _ = _ := by simp [mul_comm]

theorem sum_endpointMass_le (hPos : ∀ v, 0 < G.degree v) {C : ℝ}
    (hreg : ∀ v u, (G.degree v : ℝ) ≤ C * (G.degree u : ℝ))
    (t : ℕ) (A : Finset V) :
    (∑ v : V, endpointMass G t A v) ≤ C * (A.card : ℝ) := by
  simp only [endpointMass]
  rw [sum_comm]
  calc
    _ ≤ ∑ u ∈ A, ∑ v : V, C * Erdos642RandomWalkKernel.walkWeight G t u v :=
      sum_le_sum fun u _ => sum_le_sum fun v _ =>
        Erdos642RandomWalkKernel.walkWeight_le_mul_reverse G hPos t v u (hreg u v)
    _ = ∑ _ ∈ A, C := by
      exact sum_congr rfl fun u _ => by
        rw [← mul_sum, Erdos642RandomWalkKernel.sum_walkWeight G hPos, mul_one]
    _ = _ := by simp [mul_comm]

theorem sum_hitEstimate_le (hPos : ∀ v, 0 < G.degree v) {C : ℝ}
    (hreg : ∀ v u, (G.degree v : ℝ) ≤ C * (G.degree u : ℝ))
    (k : ℕ) (A : Finset V) :
    (∑ v : V, hitEstimate G k A v) ≤ C * (k : ℝ) * (A.card : ℝ) := by
  simp only [hitEstimate]
  rw [sum_comm]
  calc
    _ ≤ ∑ _i ∈ range k, C * (A.card : ℝ) :=
      sum_le_sum fun i _ => sum_endpointMass_le G hPos hreg (i+1) A
    _ = _ := by simp; ring

/-- A degree-ratio bound makes the set of bad starts small, even before mixing. -/
theorem badStarts_card_mul_le (hPos : ∀ v, 0 < G.degree v) {C : ℝ}
    (hreg : ∀ v u, (G.degree v : ℝ) ≤ C * (G.degree u : ℝ))
    (k : ℕ) (A : Finset V) (β : ℝ) :
    β * ((badStarts G k A β).card : ℝ) ≤ C * (k : ℝ) * (A.card : ℝ) := by
  classical
  calc
    _ = ∑ _ ∈ badStarts G k A β, β := by simp [mul_comm]
    _ ≤ ∑ v ∈ badStarts G k A β, hitEstimate G k A v := by
      exact sum_le_sum fun v hv => (mem_filter.mp hv).2
    _ ≤ ∑ v : V, hitEstimate G k A v :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ => hitEstimate_nonneg G k A v
    _ ≤ _ := sum_hitEstimate_le G hPos hreg k A

/-- A uniform endpoint bound makes the next block land at a good start. -/
theorem endpoint_badStarts_le (hPos : ∀ v, 0 < G.degree v) {C β ρ : ℝ}
    (hreg : ∀ v u, (G.degree v : ℝ) ≤ C * (G.degree u : ℝ))
    (hβ : 0 < β) (hρ : 0 ≤ ρ)
    (k t : ℕ) (A : Finset V) (v : V)
    (hMax : ∀ w, Erdos642RandomWalkKernel.walkWeight G t v w ≤ ρ) :
    endpointMass G t (badStarts G k A β) v ≤ ρ * (C * (k : ℝ) * (A.card : ℝ) / β) := by
  refine (endpointMass_le_card_mul G t _ v hMax).trans (mul_le_mul_of_nonneg_left ?_ hρ)
  apply (le_div_iff₀ hβ).mpr
  rw [mul_comm]
  exact badStarts_card_mul_le G hPos hreg k A β

/-- DMMS's numerical bad-start bound in a form that allows integer rounding. -/
theorem dmms_endpoint_badStarts_le (hPos : ∀ v, 0 < G.degree v) {β : ℝ}
    (hreg : ∀ v u, (G.degree v : ℝ) ≤ 100 * (G.degree u : ℝ))
    (hβ : 0 < β) (k t : ℕ) (A : Finset V) (v : V)
    (hMax : ∀ w, Erdos642RandomWalkKernel.walkWeight G t v w ≤ 400 / (Fintype.card V : ℝ))
    (hSize : (k : ℝ) * (A.card : ℝ) ≤ β^2 * (Fintype.card V : ℝ) / 10^6) :
    endpointMass G t (badStarts G k A β) v ≤ β / 10 := by
  let m := (Fintype.card V : ℝ)
  have hmn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hm : 0 < m := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast hmn
  refine (endpoint_badStarts_le G hPos hreg hβ (by positivity) k t A v hMax).trans ?_
  change (400 / m) * (100 * (k : ℝ) * (A.card : ℝ) / β) ≤ β / 10
  have hSize' := mul_le_mul_of_nonneg_left hSize (show (0 : ℝ) ≤ 100 by norm_num)
  calc
    _ ≤ (400 / m) * (100 * (β^2 * m / 10^6) / β) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (by simpa only [mul_assoc, m] using hSize') hβ.le)
        (by positivity)
    _ = β / 25 := by field_simp; ring
    _ ≤ _ := by linarith

end Erdos642BadStarts

end Erdos642BadStartsFile

section Erdos642ShortAvoidanceFile

/- Finite lower bounds for avoiding a taboo set and earlier steps of a walk. -/

open Finset

namespace Erdos642ShortAvoidance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each sampled vertex is required to avoid the taboo set and all earlier
sampled vertices. The initial vertex can be included in the taboo set. -/
noncomputable def survivingMass (K : V → V → ℝ) : ℕ → Finset V → V → ℝ
  | 0, _, _ => 1
  | n + 1, A, v => ∑ u ∈ univ \ A, K v u * survivingMass K n (insert u A) u

theorem survivingMass_ge (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (hN : ∀ v, ∑ u, K v u = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (hMax : ∀ v u, K v u ≤ ρ)
    (B : ℕ) (hBudget : (B : ℝ) * ρ ≤ 1) :
    ∀ (n : ℕ) (A : Finset V) (v : V), A.card + n ≤ B →
      (1 - (B : ℝ) * ρ) ^ n ≤ survivingMass K n A v := by
  intro n
  induction n with
  | zero =>
    intro A v hB
    simp [survivingMass]
  | succ n ih =>
    intro A v hB
    have hρB : 0 ≤ 1 - (B : ℝ) * ρ := sub_nonneg.mpr hBudget
    have hBad : ∑ u ∈ A, K v u ≤ (B : ℝ) * ρ := by
      calc
        _ ≤ ∑ _u ∈ A, ρ := sum_le_sum fun _ _ => hMax _ _
        _ = (A.card : ℝ) * ρ := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show A.card ≤ B by omega)) hρ
    have hMass : 1 - (B : ℝ) * ρ ≤ ∑ u ∈ univ \ A, K v u := by
      have hSplit := Finset.sum_sdiff (s₁ := A) (s₂ := univ) (subset_univ A) (f := K v)
      rw [hN v] at hSplit
      linarith
    calc
      _ = (1 - (B : ℝ) * ρ) * (1 - (B : ℝ) * ρ) ^ n := pow_succ' _ _
      _ ≤ (∑ u ∈ univ \ A, K v u) * (1 - (B : ℝ) * ρ) ^ n :=
        mul_le_mul_of_nonneg_right hMass (pow_nonneg hρB _)
      _ ≤ _ := by
        rw [survivingMass, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro u hu
        apply mul_le_mul_of_nonneg_left _ (hK v u)
        apply ih
        rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hu).2]
        omega

theorem survivingMass_ge_one_sub (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (hN : ∀ v, ∑ u, K v u = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (hMax : ∀ v u, K v u ≤ ρ)
    {B n : ℕ} (hBudget : (B : ℝ) * ρ ≤ 1) {A : Finset V} {v : V}
    (hB : A.card + n ≤ B) :
    1 - n * ((B : ℝ) * ρ) ≤ survivingMass K n A v := by
  have hA : -2 ≤ -(B : ℝ) * ρ := by linarith
  have hBern := one_add_mul_le_pow hA n
  rw [neg_mul, ← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at hBern
  exact hBern.trans (survivingMass_ge K hK hN hρ hMax B hBudget n A v hB)

end Erdos642ShortAvoidance

end Erdos642ShortAvoidanceFile

section Erdos642BlockAvoidanceFile

/- A single block of a walk can avoid old and recent vertices and land at a good endpoint. -/

namespace Erdos642BlockAvoidance

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Self-avoiding mass with taboo set A and terminal exclusion set B. -/
noncomputable def survivingMassTo (K : V → V → ℝ) :
    ℕ → Finset V → Finset V → V → ℝ
  | 0, _, B, v => if v ∈ B then 0 else 1
  | n+1, A, B, v => ∑ u ∈ univ \ A, K v u * survivingMassTo K n (insert u A) B u

theorem survivingMass_le_one (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (hNorm : ∀ v, ∑ u, K v u = 1) (n : ℕ) (A : Finset V) (v : V) :
    Erdos642ShortAvoidance.survivingMass K n A v ≤ 1 := by
  induction n generalizing A v with
  | zero => rfl
  | succ n ih =>
    rw [Erdos642ShortAvoidance.survivingMass]
    calc
      _ ≤ ∑ u ∈ univ \ A, K v u :=
        sum_le_sum fun u _ => by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (ih (insert u A) u) (hK v u)
      _ ≤ ∑ u : V, K v u :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun u _ _ => hK v u
      _ = _ := hNorm v

variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem endpointMass_zero (A : Finset V) (v : V) :
    Erdos642BadStarts.endpointMass G 0 A v = if v ∈ A then 1 else 0 := by
  classical
  unfold Erdos642BadStarts.endpointMass
  simp only [Erdos642RandomWalkKernel.walkWeight_zero, eq_comm (a := v)]
  simp

private theorem endpointMass_succ (n : ℕ) (A : Finset V) (v : V) :
    Erdos642BadStarts.endpointMass G (n+1) A v =
      ∑ u : V, Erdos642RandomWalkKernel.step G v u * Erdos642BadStarts.endpointMass G n A u := by
  unfold Erdos642BadStarts.endpointMass
  simp only [Erdos642RandomWalkKernel.walkWeight_succ]
  rw [sum_comm]
  simp only [mul_sum]

private theorem endpointMass_one (A : Finset V) (v : V) :
    Erdos642BadStarts.endpointMass G 1 A v =
      ∑ u : V, Erdos642RandomWalkKernel.step G v u * (if u ∈ A then 1 else 0) := by
  simp only [mul_ite, mul_one, mul_zero, ← sum_filter]
  unfold Erdos642BadStarts.endpointMass
  simp only [Erdos642RandomWalkKernel.walkWeight_one, filter_mem_eq_inter, univ_inter]

private theorem hitEstimate_succ (n : ℕ) (A : Finset V) (v : V) :
    Erdos642BadStarts.hitEstimate G (n+1) A v =
      Erdos642BadStarts.endpointMass G 1 A v +
        ∑ u : V, Erdos642RandomWalkKernel.step G v u * Erdos642BadStarts.hitEstimate G n A u := by
  unfold Erdos642BadStarts.hitEstimate
  rw [sum_range_succ', add_comm]
  congr 1
  simp only [endpointMass_succ G]
  rw [sum_comm]
  simp only [mul_sum]

/-- Removing the old history from the accepted paths and excluding bad
terminal vertices costs at most the union-bound old-history estimate plus
the unconditional bad terminal mass. -/
theorem survivingMassTo_ge_sub (hPos : ∀ v, 0 < G.degree v)
    (n : ℕ) (A B S : Finset V) (v : V) :
    Erdos642ShortAvoidance.survivingMass (Erdos642RandomWalkKernel.step G) n S v -
      Erdos642BadStarts.hitEstimate G n A v - Erdos642BadStarts.endpointMass G n B v ≤
        survivingMassTo (Erdos642RandomWalkKernel.step G) n (A ∪ S) B v := by
  let K := Erdos642RandomWalkKernel.step G
  let X := Erdos642ShortAvoidance.survivingMass K
  let Y := survivingMassTo K
  let hit := Erdos642BadStarts.hitEstimate G
  let ep := Erdos642BadStarts.endpointMass G
  have hK (v u : V) : 0 ≤ K v u := Erdos642RandomWalkKernel.step_nonneg G v u
  change X n S v - hit n A v - ep n B v ≤ Y n (A ∪ S) B v
  suffices hcomp : X n S v - Y n (A ∪ S) B v ≤ hit n A v + ep n B v by linarith
  induction n generalizing S v with
  | zero =>
    have hzero : hit 0 A v = 0 := by simp [hit, Erdos642BadStarts.hitEstimate]
    change 1 - (if v ∈ B then (0 : ℝ) else 1) ≤ hit 0 A v + ep 0 B v
    rw [hzero, zero_add, show ep 0 B v = _ from endpointMass_zero G B v]
    by_cases hv : v ∈ B <;> simp [hv]
  | succ n ih =>
    have hsX : X (n+1) S v = ∑ u : V,
        if u ∉ S then K v u * X n (insert u S) u else 0 := by
      change (∑ u ∈ univ \ S, K v u * X n (insert u S) u) = _
      rw [← sum_filter]
      congr 1
      ext u
      simp
    have hsY : Y (n+1) (A ∪ S) B v = ∑ u : V,
        if u ∉ A ∪ S then K v u * Y n (insert u (A ∪ S)) B u else 0 := by
      change (∑ u ∈ univ \ (A ∪ S), K v u * Y n (insert u (A ∪ S)) B u) = _
      rw [← sum_filter]
      congr 1
      ext u
      simp
    have hcost : hit (n+1) A v + ep (n+1) B v =
        ∑ u : V, K v u * ((if u ∈ A then 1 else 0) + hit n A u + ep n B u) := by
      dsimp only [hit, ep]
      rw [hitEstimate_succ G, endpointMass_one G, endpointMass_succ G]
      simp only [K, mul_add, sum_add_distrib]
    rw [hsX, hsY, hcost, ← sum_sub_distrib]
    refine sum_le_sum fun u _ => ?_
    have hnonneg : 0 ≤ hit n A u + ep n B u :=
      add_nonneg (Erdos642BadStarts.hitEstimate_nonneg G n A u)
        (Erdos642BadStarts.endpointMass_nonneg G n B u)
    by_cases hus : u ∈ S
    · have huni : u ∈ A ∪ S := mem_union_right _ hus
      simp only [hus, huni, not_true_eq_false, if_false, sub_self]
      have hind : (0 : ℝ) ≤ (if u ∈ A then 1 else 0) := by split <;> positivity
      exact mul_nonneg (hK v u) (by linarith only [hind, hnonneg])
    · by_cases hua : u ∈ A
      · have huni : u ∈ A ∪ S := mem_union_left _ hua
        simp only [hus, hua, huni, not_true_eq_false, not_false_eq_true, if_true, if_false, sub_zero]
        apply mul_le_mul_of_nonneg_left _ (hK v u)
        have hone : X n (insert u S) u ≤ 1 := survivingMass_le_one K hK
          (Erdos642RandomWalkKernel.sum_step G hPos) n _ _
        linarith only [hone, hnonneg]
      · have hnu : u ∉ A ∪ S := (mem_union.not.mpr (not_or.mpr ⟨hua, hus⟩))
        simp only [hua, hus, hnu, not_false_eq_true, if_true, if_false, zero_add, ← mul_sub]
        have hinsert : insert u (A ∪ S) = A ∪ insert u S := by
          ext w
          simp only [mem_insert, mem_union]
          tauto
        rw [hinsert]
        exact mul_le_mul_of_nonneg_left (ih (insert u S) u) (hK v u)

/-- The successful conditional mass of one self-avoiding mixing block. The old
history A and the next terminal exclusion are fixed before the block. -/
theorem dmms_block_mass_ge (δ : ℕ) (hδ : 0 < δ) (hMin : ∀ v, δ ≤ G.degree v)
    (hreg : ∀ v u, (G.degree v : ℝ) ≤ 100 * (G.degree u : ℝ))
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {k : ℕ} (hk : 0 < k)
    (hDeg : 10 * (k : ℝ)^2 ≤ β * (δ : ℝ))
    (A S T : Finset V) (v : V) (hRecent : S.card ≤ k)
    (hGood : v ∉ Erdos642BadStarts.badStarts G k A β)
    (hMix : ∀ w, Erdos642RandomWalkKernel.walkWeight G k v w ≤ 400 / (Fintype.card V : ℝ))
    (hSize : (k : ℝ) * (T.card : ℝ) ≤ β^2 * (Fintype.card V : ℝ) / 10^6) :
    1 - 2*β ≤ survivingMassTo (Erdos642RandomWalkKernel.step G) k (A ∪ S)
      (Erdos642BadStarts.badStarts G k T β) v := by
  let K := Erdos642RandomWalkKernel.step G
  let ρ := (δ : ℝ)⁻¹
  have hPos (w : V) : 0 < G.degree w := hδ.trans_le (hMin w)
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hLocal : (k : ℝ) * (((2*k : ℕ) : ℝ) * ρ) ≤ β / 5 := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, ρ]
    rw [show (k : ℝ) * (2 * (k : ℝ) * (δ : ℝ)⁻¹) = 2 * (k : ℝ)^2 / δ by ring]
    apply (div_le_iff₀ hδR).mpr
    nlinarith only [hDeg]
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hprod : 0 ≤ (((2*k : ℕ) : ℝ) * ρ) := by positivity
  have hBudget : ((2*k : ℕ) : ℝ) * ρ ≤ 1 :=
    ((le_mul_of_one_le_left hprod hkR).trans hLocal).trans (by linarith)
  have hLocalMass := Erdos642ShortAvoidance.survivingMass_ge_one_sub K
    (Erdos642RandomWalkKernel.step_nonneg G) (Erdos642RandomWalkKernel.sum_step G hPos)
    hρ (Erdos642RandomWalkKernel.step_le_inv_minDegree G hδ hMin)
    (n := k) (A := S) (v := v) hBudget (by omega)
  have hOld := (Erdos642BadStarts.notMem_badStarts_iff G k A β v).mp hGood
  have hEnd := Erdos642BadStarts.dmms_endpoint_badStarts_le G hPos hreg hβ k k T v hMix hSize
  have hBlock := survivingMassTo_ge_sub G hPos k A (Erdos642BadStarts.badStarts G k T β) S v
  linarith only [hLocalMass, hLocal, hOld, hEnd, hBlock, hβ]

end Erdos642BlockAvoidance

end Erdos642BlockAvoidanceFile

section Erdos642RepeatedAvoidanceFile

/- Composition of self-avoiding blocks with terminal guarantees. -/

namespace Erdos642RepeatedAvoidance

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Evaluate a payoff on the final taboo set and endpoint, allowing only
transitions to previously unseen vertices. -/
noncomputable def survivePayoff (K : V → V → ℝ) (f : Finset V → V → ℝ) :
    ℕ → Finset V → V → ℝ
  | 0, A, v => f A v
  | n+1, A, v => ∑ u ∈ univ \ A, K v u * survivePayoff K f n (insert u A) u

theorem survivePayoff_one (K : V → V → ℝ) (n : ℕ) (A : Finset V) (v : V) :
    survivePayoff K (fun _ _ => 1) n A v = Erdos642ShortAvoidance.survivingMass K n A v := by
  induction n generalizing A v with
  | zero => rfl
  | succ n ih => simp only [survivePayoff, Erdos642ShortAvoidance.survivingMass, ih]

theorem survivePayoff_split (K : V → V → ℝ) (f : Finset V → V → ℝ)
    (m n : ℕ) (A : Finset V) (v : V) :
    survivePayoff K f (m+n) A v = survivePayoff K (survivePayoff K f n) m A v := by
  induction m generalizing A v with
  | zero => simp [survivePayoff]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [survivePayoff, ih]

theorem survivePayoff_nonneg (K : V → V → ℝ) (hK : ∀ u v, 0 ≤ K u v)
    (f : Finset V → V → ℝ) (hf : ∀ A v, 0 ≤ f A v) (n : ℕ) (A : Finset V) (v : V) :
    0 ≤ survivePayoff K f n A v := by
  induction n generalizing A v with
  | zero => exact hf A v
  | succ n ih => exact sum_nonneg fun u _ => mul_nonneg (hK v u) (ih (insert u A) u)

theorem survivePayoff_survivingMassTo (K : V → V → ℝ) (c : ℝ)
    (n : ℕ) (A B : Finset V) (v : V) :
    survivePayoff K (fun _ u => c * (if u ∈ B then 0 else 1)) n A v =
      c * Erdos642BlockAvoidance.survivingMassTo K n A B v := by
  induction n generalizing A v with
  | zero => rfl
  | succ n ih =>
    simp only [survivePayoff, Erdos642BlockAvoidance.survivingMassTo, ih, mul_sum]
    exact sum_congr rfl fun u _ => by ring

/-- Only extensions of A by at most n vertices can affect the n-step payoff. -/
theorem survivePayoff_mono_on_extensions (K : V → V → ℝ) (hK : ∀ u v, 0 ≤ K u v)
    {f g : Finset V → V → ℝ} (n : ℕ) (A : Finset V) (v : V)
    (hfg : ∀ B u, A ⊆ B → B.card ≤ A.card+n → f B u ≤ g B u) :
    survivePayoff K f n A v ≤ survivePayoff K g n A v := by
  induction n generalizing A v with
  | zero => exact hfg A v Subset.rfl (by omega)
  | succ n ih =>
    simp only [survivePayoff]
    refine sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (ih (insert u A) u ?_) (hK v u)
    intro B w hsub hcard
    apply hfg B w ((subset_insert u A).trans hsub)
    rw [card_insert_of_notMem (mem_sdiff.mp hu).2] at hcard
    omega

/-- Repeated successful mixing blocks lower-bound the actual self-avoiding mass. -/
theorem dmms_repeated_mass_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    (δ : ℕ) (hδ : 0 < δ) (hMin : ∀ v, δ ≤ G.degree v)
    (hreg : ∀ v u, (G.degree v : ℝ) ≤ 100 * (G.degree u : ℝ))
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1 / 2) {k : ℕ} (hk : 0 < k)
    (hDeg : 10 * (k : ℝ)^2 ≤ β * (δ : ℝ))
    (hMix : ∀ v w, Erdos642RandomWalkKernel.walkWeight G k v w ≤
      400 / (Fintype.card V : ℝ))
    (r : ℕ) (A S : Finset V) (v : V) (hRecent : S.card ≤ k)
    (hGood : v ∉ Erdos642BadStarts.badStarts G k A β)
    (hSize : (k : ℝ) * (((A∪S).card + r*k - 1 : ℕ) : ℝ) ≤
      β^2 * (Fintype.card V : ℝ) / 10^6) :
    (1-2*β)^r ≤ Erdos642ShortAvoidance.survivingMass (Erdos642RandomWalkKernel.step G)
      (r*k) (A∪S) v := by
  let K := Erdos642RandomWalkKernel.step G
  let capacity := β^2 * (Fintype.card V : ℝ) / 10^6
  have hK (u w : V) : 0 ≤ K u w := Erdos642RandomWalkKernel.step_nonneg G u w
  have hβ0 : 0 ≤ 1-2*β := by linarith
  induction r generalizing A S v with
  | zero => simp [Erdos642ShortAvoidance.survivingMass]
  | succ r ih =>
    let T := A ∪ S
    let bad := Erdos642BadStarts.badStarts G k T β
    let f := survivePayoff K (fun _ _ => 1) (r*k)
    have hSmall : (k : ℝ) * (T.card : ℝ) ≤ capacity := by
      have hcard : T.card ≤ T.card + (r+1)*k - 1 := by rw [Nat.succ_mul]; omega
      exact (mul_le_mul_of_nonneg_left
        (by exact_mod_cast hcard) (by positivity)).trans hSize
    have hblock : 1-2*β ≤ Erdos642BlockAvoidance.survivingMassTo K k T bad v :=
      Erdos642BlockAvoidance.dmms_block_mass_ge G δ hδ hMin hreg hβ (by linarith) hk hDeg
        A S T v hRecent hGood (hMix v) hSmall
    have hcont (U : Finset V) (u : V) (hTU : T ⊆ U) (hcard : U.card ≤ T.card + k) :
        (1-2*β)^r * (if u ∈ bad then 0 else 1) ≤ f U u := by
      by_cases hbad : u ∈ bad
      · simp only [if_pos hbad, mul_zero]
        exact survivePayoff_nonneg K hK _ (fun _ _ => zero_le_one) _ _ _
      · simp only [if_neg hbad, mul_one]
        let R := U \ T
        have hRT : T ∪ R = U := by
          ext x
          simp only [R, mem_union, mem_sdiff]
          exact ⟨fun h => h.elim (fun h => hTU h) And.left, fun h => by tauto⟩
        have hR : R.card ≤ k := by
          change (U \ T).card ≤ k
          rw [card_sdiff_of_subset hTU]
          omega
        have hRoom : (k : ℝ) * (((T∪R).card + r*k - 1 : ℕ) : ℝ) ≤ capacity := by
          have hh : U.card + r*k - 1 ≤ T.card + (r+1)*k - 1 := by rw [Nat.succ_mul]; omega
          rw [hRT]
          exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hh) (by positivity)).trans hSize
        have hStep := ih T R u hR hbad hRoom
        rw [hRT] at hStep
        simpa only [f, survivePayoff_one] using hStep
    have hMon := survivePayoff_mono_on_extensions K hK k T v hcont
    rw [survivePayoff_survivingMassTo] at hMon
    calc
      (1-2*β)^(r+1) = (1-2*β)^r * (1-2*β) := pow_succ _ _
      _ ≤ (1-2*β)^r * Erdos642BlockAvoidance.survivingMassTo K k T bad v :=
        mul_le_mul_of_nonneg_left hblock (pow_nonneg hβ0 _)
      _ ≤ survivePayoff K f k T v := hMon
      _ = _ := by
        dsimp only [f]
        rw [← survivePayoff_split, survivePayoff_one, Nat.succ_mul, Nat.add_comm (r*k) k]

/-- The rounded DMMS lower bound for a single complete walk. -/
theorem dmms_self_avoidance (G : SimpleGraph V) [DecidableRel G.Adj]
    (δ : ℕ) (hδ : 0 < δ) (hMin : ∀ v, δ ≤ G.degree v)
    (hreg : ∀ v u, (G.degree v : ℝ) ≤ 100 * (G.degree u : ℝ))
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1/10) {k t : ℕ} (hk : 0 < k)
    (hDeg : 10 * (k : ℝ)^2 ≤ β * (δ : ℝ))
    (hMix : ∀ v w, Erdos642RandomWalkKernel.walkWeight G k v w ≤
      400 / (Fintype.card V : ℝ))
    (hDiv : k ∣ t)
    (hSize : (k : ℝ) * (t : ℝ) ≤ β^2 * (Fintype.card V : ℝ) / 10^6)
    (v : V) :
    Real.exp (-(10*β*((t : ℝ)/k))) ≤
      Erdos642ShortAvoidance.survivingMass (Erdos642RandomWalkKernel.step G) t {v} v := by
  obtain ⟨r, rfl⟩ := hDiv
  rw [Nat.mul_comm k r] at hSize ⊢
  have hkR : (0 : ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hTime : ((r*k : ℕ) : ℝ) / (k : ℝ) = (r : ℝ) := by
    rw [Nat.cast_mul, mul_div_cancel_right₀ _ hkR.ne']
  rw [hTime]
  have hbase : Real.exp (-(10*β)) ≤ 1-2*β := by
    have h1 : 0 < 1 + 10*β := by linarith
    calc
      _ ≤ (1+10*β)⁻¹ := by
        rw [Real.exp_neg]
        exact inv_anti₀ h1 (by linarith only [Real.add_one_le_exp (10*β)])
      _ ≤ _ := (inv_le_iff_one_le_mul₀ h1).mpr (by
        have hsq := mul_le_mul_of_nonneg_right hβ1 hβ.le
        nlinarith only [hsq, hβ])
  have hExp : Real.exp (-(10*β*(r : ℝ))) = Real.exp (-(10*β))^r := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hGood : v ∉ Erdos642BadStarts.badStarts G k ∅ β := by
    rw [Erdos642BadStarts.notMem_badStarts_iff]
    simpa only [Erdos642BadStarts.hitEstimate, Erdos642BadStarts.endpointMass, sum_empty,
      sum_const_zero] using hβ
  have hRecent : ({v} : Finset V).card ≤ k := by rw [card_singleton]; omega
  have hRoom : (k : ℝ) * ((((∅ : Finset V) ∪ {v}).card + r*k - 1 : ℕ) : ℝ) ≤
      β^2 * (Fintype.card V : ℝ) / 10^6 := by
    simpa only [empty_union, card_singleton, Nat.add_comm 1, Nat.add_sub_cancel] using hSize
  rw [hExp]
  refine (pow_le_pow_left₀ (Real.exp_nonneg _) hbase _).trans ?_
  simpa only [empty_union] using dmms_repeated_mass_ge G δ hδ hMin hreg hβ
    (by linarith) hk hDeg hMix r ∅ {v} v hRecent hGood hRoom

end Erdos642RepeatedAvoidance

end Erdos642RepeatedAvoidanceFile

section Erdos642WalkTraceFile

/- A universal finite probability law on raw walks of prescribed length. -/

namespace Erdos642WalkTrace

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V]

/-- A trace records the n positions strictly after its explicitly given start. -/
noncomputable def traceWeight (K : V → V → ℝ) :
    (n : ℕ) → V → (Fin n → V) → ℝ
  | 0, _, _ => 1
  | n+1, v, p => K v (p 0) * traceWeight K n (p 0) (Fin.tail p)

/-- The endpoint of a trace, with the start as endpoint at length zero. -/
def finish : (n : ℕ) → V → (Fin n → V) → V
  | 0, v, _ => v
  | n+1, _, p => finish n (p 0) (Fin.tail p)

/-- Sum of the mass of traces satisfying a predicate. -/
noncomputable def eventMass (K : V → V → ℝ) (n : ℕ) (v : V)
    (P : (Fin n → V) → Prop) : ℝ := by
  classical
  exact ∑ p : Fin n → V, if P p then traceWeight K n v p else 0

theorem sum_trace_cons {R : Type*} [AddCommMonoid R] {n : ℕ}
    (f : (Fin (n+1) → V) → R) :
    (∑ p, f p) = ∑ u : V, ∑ p : Fin n → V, f (Fin.cons u p) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n+1) => V)
  have h := Fintype.sum_equiv e (fun up : V × (Fin n → V) => f (Fin.cons up.1 up.2)) f
    (fun _ => rfl)
  rw [← h, ← univ_product_univ, sum_product]

omit [Fintype V] in
theorem traceWeight_nonneg (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (n : ℕ) (v : V) (p : Fin n → V) : 0 ≤ traceWeight K n v p := by
  induction n generalizing v with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hK v (p 0)) (ih _ _)

theorem sum_traceWeight (K : V → V → ℝ) (hRow : ∀ v, ∑ u, K v u = 1) (n : ℕ) (v : V) :
    (∑ p : Fin n → V, traceWeight K n v p) = 1 := by
  classical
  induction n generalizing v with
  | zero => simp [traceWeight]
  | succ n ih =>
    rw [sum_trace_cons]
    simp only [traceWeight, Fin.cons_zero, Fin.tail_cons, ← mul_sum, ih, mul_one, hRow]

/-- Concatenate two consecutive pieces. The right length is placed first in
the type-level sum so the recursive construction needs no casts. -/
def appendTrace (n : ℕ) : (m : ℕ) → (Fin m → V) → (Fin n → V) → (Fin (n+m) → V)
  | 0, _, q => q
  | m+1, p, q => Fin.cons (p 0) (appendTrace n m (Fin.tail p) q)

omit [Fintype V] in
theorem traceWeight_appendTrace (K : V → V → ℝ) (m n : ℕ)
    (v : V) (p : Fin m → V) (q : Fin n → V) :
    traceWeight K (n+m) v (appendTrace n m p q) =
      traceWeight K m v p * traceWeight K n (finish m v p) q := by
  induction m generalizing v with
  | zero => simp [traceWeight, finish, appendTrace]
  | succ m ih =>
    simp only [Nat.add_succ, appendTrace, traceWeight, Fin.cons_zero, Fin.tail_cons, finish,
      mul_assoc]
    exact congrArg (fun x => K v (p 0) * x) (ih (p 0) (Fin.tail p))

theorem sum_trace_append {R : Type*} [AddCommMonoid R] (m n : ℕ)
    (f : (Fin (n+m) → V) → R) :
    (∑ p, f p) = ∑ p : Fin m → V, ∑ q : Fin n → V, f (appendTrace n m p q) := by
  classical
  induction m with
  | zero => simp [appendTrace]
  | succ m ih =>
    have h₁ : (∑ p : Fin (n+(m+1)) → V, f p) =
        ∑ u : V, ∑ s : Fin (n+m) → V, f (Fin.cons u s) := sum_trace_cons f
    rw [h₁, sum_trace_cons (f := fun p : Fin (m+1) → V =>
      ∑ q : Fin n → V, f (appendTrace n (m+1) p q))]
    apply sum_congr rfl
    intro u _
    simpa only [appendTrace, Fin.cons_zero, Fin.tail_cons] using ih (fun s => f (Fin.cons u s))

/-- Conditional splitting of any event after m steps. The starting vertex
of the second piece is determined by the first piece. -/
theorem eventMass_split (K : V → V → ℝ) (m n : ℕ) (v : V)
    (P : (Fin (n+m) → V) → Prop) :
    eventMass K (n+m) v P =
      ∑ p : Fin m → V, traceWeight K m v p *
        eventMass K n (finish m v p) (fun q => P (appendTrace n m p q)) := by
  classical
  rw [eventMass, sum_trace_append m n]
  simp only [eventMass, mul_sum]
  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
  by_cases hp : P (appendTrace n m p q)
  · simp only [if_pos hp, traceWeight_appendTrace]
  · simp only [if_neg hp, mul_zero]

theorem eventMass_nonneg (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (n : ℕ) (v : V) (P : (Fin n → V) → Prop) :
    0 ≤ eventMass K n v P := by
  classical
  apply sum_nonneg
  intro p _
  by_cases hp : P p
  · simpa only [if_pos hp] using traceWeight_nonneg K hK n v p
  · simp only [if_neg hp, le_rfl]

theorem eventMass_true (K : V → V → ℝ) (hRow : ∀ v, ∑ u, K v u = 1)
    (n : ℕ) (v : V) :
    eventMass K n v (fun _ => True) = 1 := by
  simpa only [eventMass, if_true] using sum_traceWeight K hRow n v

theorem eventMass_compl_add (K : V → V → ℝ) (hRow : ∀ v, ∑ u, K v u = 1)
    (n : ℕ) (v : V) (P : (Fin n → V) → Prop) :
    eventMass K n v (fun p => ¬ P p) + eventMass K n v P = 1 := by
  classical
  unfold eventMass
  rw [← sum_add_distrib, ← sum_traceWeight K hRow n v]
  exact sum_congr rfl fun p _ => by by_cases hp : P p <;> simp [hp]

/-- A usable subtraction form of the union bound on one trace law. -/
theorem eventMass_and_ge_sub (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (n : ℕ) (v : V) (P Q : (Fin n → V) → Prop) :
    eventMass K n v P - eventMass K n v (fun p => ¬ Q p) ≤
      eventMass K n v (fun p => P p ∧ Q p) := by
  classical
  simp only [eventMass, ← sum_sub_distrib]
  refine sum_le_sum fun p _ => ?_
  have hpw := traceWeight_nonneg K hK n v p
  by_cases hp : P p <;> by_cases hq : Q p <;> simp [hp, hq, hpw]

/-- The finite union bound on raw traces. -/
theorem eventMass_union_le {I : Type*} (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (n : ℕ) (v : V) (J : Finset I) (P : I → (Fin n → V) → Prop) :
    eventMass K n v (fun p => ∃ i ∈ J, P i p) ≤
      ∑ i ∈ J, eventMass K n v (P i) := by
  classical
  simp only [eventMass]
  rw [sum_comm]
  refine sum_le_sum fun p _ => ?_
  let W := traceWeight K n v p
  let F (i : I) := @ite ℝ (P i p) (Classical.propDecidable _) W 0
  have hF (i : I) : 0 ≤ F i := by
    dsimp only [F]
    split
    · exact traceWeight_nonneg K hK n v p
    · rfl
  change @ite ℝ (∃ i ∈ J, P i p) (Classical.propDecidable _) W 0 ≤ ∑ i ∈ J, F i
  by_cases h : ∃ i ∈ J, P i p
  · rw [if_pos h]
    obtain ⟨i, hi, hp⟩ := h
    have hval : F i = W := if_pos hp
    rw [← hval]
    exact single_le_sum (fun i _ => hF i) hi
  · rw [if_neg h]
    exact sum_nonneg fun i _ => hF i

theorem exists_trace_of_eventMass_pos (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (n : ℕ) (v : V) (P : (Fin n → V) → Prop) (hP : 0 < eventMass K n v P) :
    ∃ p, P p ∧ 0 < traceWeight K n v p := by
  classical
  change 0 < ∑ p : Fin n → V, if P p then traceWeight K n v p else 0 at hP
  rw [sum_pos_iff_of_nonneg (fun p _ => by
    split
    · exact traceWeight_nonneg K hK n v p
    · rfl)] at hP
  obtain ⟨p, _, h⟩ := hP
  by_cases hp : P p
  · exact ⟨p, hp, by simpa [hp] using h⟩
  · simp [hp] at h

omit [Fintype V] in
/-- A positive trace uses only positive one-step transitions. -/
theorem traceWeight_pos_iff (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (n : ℕ) (v : V) (p : Fin n → V) :
    0 < traceWeight K n v p ↔
      ∀ i : Fin n, 0 < K ((Fin.cons v p : Fin (n+1) → V) i.castSucc)
        ((Fin.cons v p : Fin (n+1) → V) i.succ) := by
  induction n generalizing v with
  | zero => simp [traceWeight]
  | succ n ih =>
    rw [Fin.forall_fin_succ]
    have hab :
        0 < traceWeight K (n+1) v p ↔
          0 < K v (p 0) ∧ 0 < traceWeight K n (p 0) (Fin.tail p) := by
      change 0 < K v (p 0) * traceWeight K n (p 0) (Fin.tail p) ↔ _
      rw [mul_pos_iff]
      exact ⟨fun h => h.elim id (fun h => (not_lt_of_ge (hK v (p 0)) h.1).elim), Or.inl⟩
    rw [hab, ih]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ, Fin.cons_self_tail, Fin.cons_zero,
      Fin.cons_succ, Fin.tail]

omit [Fintype V] in
/-- Concatenation indeed preserves the first piece at the original indices. -/
theorem appendTrace_left (m n : ℕ) (p : Fin m → V) (q : Fin n → V) (i : Fin m) :
    appendTrace n m p q (Fin.cast (Nat.add_comm m n) (Fin.castAdd n i)) = p i := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · have hz : Fin.cast (Nat.add_comm (m+1) n) (Fin.castAdd n (0 : Fin (m+1))) =
          (0 : Fin (n+(m+1))) := by ext; rfl
      simp only [hz, appendTrace, Fin.cons_zero]
    · have hs : Fin.cast (Nat.add_comm (m+1) n) (Fin.castAdd n j.succ) =
          (Fin.cast (Nat.add_comm m n) (Fin.castAdd n j)).succ := by ext; rfl
      rw [hs, appendTrace, Fin.cons_succ]
      exact ih (Fin.tail p) j

omit [Fintype V] in
/-- Concatenation preserves the second piece after the m initial positions. -/
theorem appendTrace_right (m n : ℕ) (p : Fin m → V) (q : Fin n → V) (i : Fin n) :
    appendTrace n m p q (Fin.cast (Nat.add_comm m n) (Fin.natAdd m i)) = q i := by
  induction m with
  | zero =>
    have he : Fin.cast (Nat.add_comm 0 n) (Fin.natAdd 0 i) = i := by ext; simp
    simp only [he, appendTrace]
  | succ m ih =>
    have hs : Fin.cast (Nat.add_comm (m+1) n) (Fin.natAdd (m+1) i) =
        (Fin.cast (Nat.add_comm m n) (Fin.natAdd m i)).succ := by
      ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      omega
    rw [hs, appendTrace, Fin.cons_succ]
    exact ih (Fin.tail p)

variable [DecidableEq V]

/-- A finite trace and the graph walk kernel give the same distribution of the endpoint. -/
theorem sum_finish_payoff_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (v : V) (f : V → ℝ) :
    (∑ p : Fin n → V, traceWeight (Erdos642RandomWalkKernel.step G) n v p *
        f (finish n v p)) =
      ∑ u : V, Erdos642RandomWalkKernel.walkWeight G n v u * f u := by
  classical
  induction n generalizing v with
  | zero =>
    simp [traceWeight, finish, ite_mul]
  | succ n ih =>
    rw [sum_trace_cons]
    simp only [traceWeight, Fin.cons_zero, Fin.tail_cons, finish, mul_assoc, ← mul_sum, ih,
      Erdos642RandomWalkKernel.walkWeight_succ]
    simp only [mul_sum, sum_mul, mul_assoc]
    exact sum_comm

/-- Every recorded vertex avoids the initial taboo set and all recorded
vertices are distinct. -/
def survives {n : ℕ} (A : Finset V) (p : Fin n → V) : Prop :=
  Function.Injective p ∧ ∀ i : Fin n, p i ∉ A

omit [Fintype V] in
theorem survives_cons {n : ℕ} (A : Finset V) (u : V) (p : Fin n → V) :
    survives A (Fin.cons u p) ↔ u ∉ A ∧ survives (insert u A) p := by
  rw [survives, survives, Fin.cons_injective_iff, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mem_insert, not_or, Set.mem_range]
  push Not
  simp only [forall_and]
  tauto

theorem eventMass_survives (K : V → V → ℝ) (n : ℕ) (A : Finset V) (v : V) :
    eventMass K n v (survives A) = Erdos642ShortAvoidance.survivingMass K n A v := by
  classical
  induction n generalizing A v with
  | zero =>
    have hzero (p : Fin 0 → V) : survives A p :=
      ⟨fun a => a.elim0, fun a => a.elim0⟩
    simp [eventMass, hzero, traceWeight, Erdos642ShortAvoidance.survivingMass]
  | succ n ih =>
    rw [eventMass, sum_trace_cons, Erdos642ShortAvoidance.survivingMass]
    have hfilter : univ \ A = univ.filter (fun u => u ∉ A) := by
      ext u
      simp
    rw [hfilter, sum_filter]
    apply sum_congr rfl
    intro u _
    by_cases hA : u ∈ A
    · simp [survives_cons, hA]
    · simp only [survives_cons, hA, not_false_eq_true, true_and, if_true]
      simp only [traceWeight, Fin.cons_zero, Fin.tail_cons]
      rw [← ih (insert u A) u, eventMass, mul_sum]
      apply sum_congr rfl
      intro p _
      by_cases hp : survives (insert u A) p <;> simp [hp]

omit [Fintype V] [DecidableEq V] in
theorem survives_singleton_iff {n : ℕ} (v : V) (p : Fin n → V) :
    survives {v} p ↔ Function.Injective (Fin.cons v p) := by
  rw [survives, Fin.cons_injective_iff, and_comm]
  simp only [mem_singleton, Set.mem_range, not_exists]

end Erdos642WalkTrace

end Erdos642WalkTraceFile

section Erdos642TraceStrideFile

/- Sampling the endpoints of equal-length blocks of a raw finite walk. -/

namespace Erdos642TraceStride

open Finset Erdos642WalkTrace
open scoped BigOperators

variable {V : Type*}

/-- The zero-based trace coordinate of the end of block i. -/
def sampleIndex (k r : ℕ) (hk : 0 < k) (i : Fin r) : Fin (r*k) :=
  ⟨(i.val+1)*k-1, by
    have h_le : (i.val+1)*k ≤ r*k := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
    have h_pos : 0 < (i.val+1)*k := Nat.mul_pos (Nat.succ_pos i.val) hk
    omega⟩

def samples (k r : ℕ) (hk : 0 < k) (p : Fin (r*k) → V) : Fin r → V :=
  p ∘ sampleIndex k r hk

def blockAppend (k r : ℕ) (p : Fin k → V) (q : Fin (r*k) → V) :
    Fin ((r+1)*k) → V :=
  appendTrace (r*k) k p q ∘ Fin.cast (Nat.succ_mul r k)

theorem traceWeight_cast (K : V → V → ℝ) {m n : ℕ} (h : m = n) (v : V) (p : Fin n → V) :
    traceWeight K m v (p ∘ Fin.cast h) = traceWeight K n v p := by
  subst n
  rfl

theorem traceWeight_blockAppend (K : V → V → ℝ) (k r : ℕ) (v : V)
    (p : Fin k → V) (q : Fin (r*k) → V) :
    traceWeight K ((r+1)*k) v (blockAppend k r p q) =
      traceWeight K k v p * traceWeight K (r*k) (finish k v p) q := by
  rw [blockAppend, traceWeight_cast, traceWeight_appendTrace]

theorem finish_eq_last (r : ℕ) (v : V) (p : Fin (r+1) → V) :
    finish (r+1) v p = p (Fin.last r) := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    change finish (r+1) (p 0) (Fin.tail p) = p (Fin.last (r+1))
    rw [ih]
    simp only [Fin.tail, Fin.succ_last]

theorem samples_blockAppend (k r : ℕ) (hk : 0 < k) (v : V)
    (p : Fin k → V) (q : Fin (r*k) → V) :
    samples k (r+1) hk (blockAppend k r p q) =
      Fin.cons (finish k v p) (samples k r hk q) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · let l : Fin k := ⟨k-1, by omega⟩
    have hidx : Fin.cast (Nat.succ_mul r k) (sampleIndex k (r+1) hk 0) =
        Fin.cast (Nat.add_comm k (r*k)) (Fin.castAdd (r*k) l) := by
      ext
      simp [sampleIndex, l]
    simp only [samples, blockAppend, Function.comp_apply, Fin.cons_zero, hidx,
      appendTrace_left]
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [finish_eq_last k']
    rfl
  · have hidx : Fin.cast (Nat.succ_mul r k) (sampleIndex k (r+1) hk j.succ) =
        Fin.cast (Nat.add_comm k (r*k)) (Fin.natAdd k (sampleIndex k r hk j)) := by
      apply Fin.ext
      simp only [sampleIndex, Fin.val_cast, Fin.val_succ, Fin.val_natAdd, ← Nat.succ_eq_add_one,
        Nat.succ_mul]
      have hpos := Nat.mul_pos (Nat.succ_pos j.val) hk
      omega
    simp only [samples, blockAppend, Function.comp_apply, Fin.cons_succ, hidx,
      appendTrace_right]

variable [Fintype V]

private theorem sum_trace_cast {R : Type*} [AddCommMonoid R] {m n : ℕ}
    (h : m = n) (f : (Fin m → V) → R) :
    (∑ p : Fin m → V, f p) = ∑ p : Fin n → V, f (p ∘ Fin.cast h) := by
  subst n
  rfl

theorem sum_blockAppend {R : Type*} [AddCommMonoid R] (k r : ℕ)
    (f : (Fin ((r+1)*k) → V) → R) :
    (∑ p, f p) = ∑ p : Fin k → V, ∑ q : Fin (r*k) → V, f (blockAppend k r p q) := by
  rw [sum_trace_cast (Nat.succ_mul r k)]
  exact sum_trace_append k (r*k) _

/-- The block endpoint marginal of the full trace law, tested against arbitrary
payoffs on the complete sampled record. -/
theorem sum_samples_payoff_eq (K L : V → V → ℝ) (k : ℕ) (hk : 0 < k)
    (hMarginal : ∀ (v : V) (f : V → ℝ),
      (∑ p : Fin k → V, traceWeight K k v p * f (finish k v p)) = ∑ u : V, L v u * f u)
    (r : ℕ) (v : V) (f : (Fin r → V) → ℝ) :
    (∑ p : Fin (r*k) → V, traceWeight K (r*k) v p * f (samples k r hk p)) =
      ∑ q : Fin r → V, traceWeight L r v q * f q := by
  classical
  induction r generalizing v with
  | zero =>
    rw [sum_trace_cast (Nat.zero_mul k)]
    simp only [traceWeight_cast, traceWeight, one_mul]
    exact sum_congr rfl fun _ _ => congrArg f (Subsingleton.elim _ _)
  | succ r ih =>
    rw [sum_blockAppend k r, sum_trace_cons]
    simp only [traceWeight_blockAppend, samples_blockAppend k r hk v, mul_assoc, ← mul_sum,
      traceWeight, Fin.cons_zero, Fin.tail_cons]
    let F (u : V) := ∑ q : Fin r → V, traceWeight L r u q * f (Fin.cons u q)
    calc
      _ = ∑ p : Fin k → V, traceWeight K k v p * F (finish k v p) := by
        apply sum_congr rfl
        intro p _
        exact congrArg (fun z => traceWeight K k v p * z)
          (ih (finish k v p) (fun q => f (Fin.cons (finish k v p) q)))
      _ = _ := hMarginal v F

/-- The exact trace-law probability of a predicate on regularly sampled endpoints. -/
theorem eventMass_samples_eq (K L : V → V → ℝ) (k : ℕ) (hk : 0 < k)
    (hMarginal : ∀ (v : V) (f : V → ℝ),
      (∑ p : Fin k → V, traceWeight K k v p * f (finish k v p)) = ∑ u : V, L v u * f u)
    (r : ℕ) (v : V) (P : (Fin r → V) → Prop) :
    eventMass K (r*k) v (fun p => P (samples k r hk p)) = eventMass L r v P := by
  classical
  simpa only [eventMass, mul_ite, mul_one, mul_zero] using
    sum_samples_payoff_eq K L k hk hMarginal r v (fun p => if P p then 1 else 0)

theorem graph_eventMass_samples_eq [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (r : ℕ) (v : V) (P : (Fin r → V) → Prop) :
    eventMass (Erdos642RandomWalkKernel.step G) (r*k) v (fun p => P (samples k r hk p)) =
      eventMass (Erdos642RandomWalkKernel.walkWeight G k) r v P :=
  eventMass_samples_eq _ _ k hk (sum_finish_payoff_eq G k) r v P

end Erdos642TraceStride

end Erdos642TraceStrideFile

section Erdos642SeenSetProbabilityFile

/- Adapting a finite kernel to count distinct sampled vertices in a target set. -/

namespace Erdos642SeenSetProbability

open Finset Erdos642FiniteProbability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Insert a sampled vertex into the record exactly when it is in the target set. -/
def remember (A S : Finset V) (v : V) : Finset V :=
  if v ∈ A then insert v S else S

/-- Lift a vertex kernel to the state consisting of a vertex and a visit record. -/
noncomputable def seenKernel (K : ℕ → V → V → ℝ) (A : Finset V)
    (t : ℕ) (x y : V × Finset V) : ℝ :=
  if y.2 = remember A x.2 y.1 then K t x.1 y.1 else 0

theorem sum_seenKernel_mul (K : ℕ → V → V → ℝ) (A : Finset V)
    (t : ℕ) (x : V × Finset V) (f : V × Finset V → ℝ) :
    (∑ y : V × Finset V, seenKernel K A t x y * f y) =
      ∑ v : V, K t x.1 v * f (v, remember A x.2 v) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  simp only [seenKernel, ite_mul, zero_mul]
  simp

theorem seenKernel_stochastic (K : ℕ → V → V → ℝ) (A : Finset V) (N : ℕ)
    (hK : IsStochasticThrough K N) : IsStochasticThrough (seenKernel K A) N := by
  intro t ht x
  constructor
  · intro y
    unfold seenKernel
    split
    · exact (hK t ht x.1).1 y.1
    · exact le_rfl
  · simpa only [mul_one] using
      (sum_seenKernel_mul K A t x (fun _ => 1)).trans (by simpa using (hK t ht x.1).2)

omit [Fintype V] in
theorem seenKernel_score_mono (K : ℕ → V → V → ℝ) (A : Finset V) (t : ℕ)
    (x y : V × Finset V) (h : 0 < seenKernel K A t x y) :
    x.2.card ≤ y.2.card := by
  have he : y.2 = remember A x.2 y.1 := by
    by_contra hn
    simp [seenKernel, hn] at h
  rw [he, remember]
  split
  · exact card_le_card (subset_insert _ _)
  · exact le_rfl

omit [Fintype V] in
theorem card_lt_card_remember_iff (A S : Finset V) (v : V) :
    S.card < (remember A S v).card ↔ v ∈ A \ S := by
  by_cases hA : v ∈ A
  · by_cases hS : v ∈ S
    · simp [remember, hA, hS, insert_eq_of_mem hS]
    · simp [remember, hA, hS, card_insert_of_notMem hS]
  · simp [remember, hA]

theorem seenKernel_success_mass (K : ℕ → V → V → ℝ) (A : Finset V) (t : ℕ)
    (x : V × Finset V) :
    (∑ y ∈ (univ : Finset (V × Finset V)).filter (fun y => x.2.card < y.2.card),
      seenKernel K A t x y) =
      ∑ v ∈ A \ x.2, K t x.1 v := by
  classical
  rw [Finset.sum_filter]
  calc
    (∑ y : V × Finset V, if x.2.card < y.2.card then seenKernel K A t x y else 0) =
        ∑ y : V × Finset V, seenKernel K A t x y * (if x.2.card < y.2.card then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      split <;> simp
    _ = ∑ v : V, K t x.1 v * (if x.2.card < (remember A x.2 v).card then 1 else 0) :=
      sum_seenKernel_mul K A t x _
    _ = _ := by
      have he : (univ : Finset V).filter (fun v => v ∈ A \ x.2) = A \ x.2 := by
        ext v
        simp only [mem_filter, mem_univ, true_and]
      rw [← he, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      have hi := card_lt_card_remember_iff A x.2 v
      by_cases h : v ∈ A \ x.2
      · simp only [if_pos h, if_pos (hi.mpr h), mul_one]
      · simp only [if_neg h, if_neg (hi.not.mpr h), mul_zero]

/-- A pointwise lower bound on the sampled transition probabilities implies a
lower-tail estimate for the number of distinct target vertices sampled. -/
theorem lowerTail_seen_le_exp_neg (K : ℕ → V → V → ℝ) (A : Finset V)
    (N : ℕ) (s p ρ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hρ : 0 ≤ ρ)
    (hK : IsStochasticThrough K N)
    (hpoint : ∀ t < N, ∀ u v : V, v ∈ A → ρ ≤ K t u v)
    (hbudget : p ≤ ρ * ((A.card : ℝ) - s))
    (hs : s ≤ (N : ℝ) * p / 4) (x : V) :
    lowerTail (seenKernel K A) (fun y => y.2.card) s N 0 (x, ∅) ≤ Real.exp (-s) := by
  apply lowerTail_le_exp_neg_of_le_quarter _ _ N s p hp0 hp1
    (seenKernel_stochastic K A N hK) (fun t _ => seenKernel_score_mono K A t) ?_ hs
  intro t ht y hSmall
  rw [seenKernel_success_mass]
  have hPart : (((A \ y.2).card : ℕ) : ℝ) + ((A ∩ y.2).card : ℝ) = A.card := by
    exact_mod_cast card_sdiff_add_card_inter A y.2
  have hInter : ((A ∩ y.2).card : ℝ) ≤ y.2.card := by exact_mod_cast card_le_card inter_subset_right
  have hMissing : (A.card : ℝ) - s ≤ ((A \ y.2).card : ℝ) := by
    change (y.2.card : ℝ) ≤ s at hSmall
    linarith only [hPart, hInter, hSmall]
  calc
    p ≤ ρ * ((A.card : ℝ) - s) := hbudget
    _ ≤ ρ * ((A \ y.2).card : ℝ) := mul_le_mul_of_nonneg_left hMissing hρ
    _ = ∑ _v ∈ A \ y.2, ρ := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun v hv => hpoint t ht y.1 v (mem_sdiff.mp hv).1)

end Erdos642SeenSetProbability

end Erdos642SeenSetProbabilityFile

section Erdos642TraceSeenFile

/- The law of recorded visits under the finite raw trace distribution. -/

namespace Erdos642TraceSeen

open Finset
open Erdos642WalkTrace Erdos642SeenSetProbability

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem image_cons {n : ℕ} (u : V) (p : Fin n → V) :
    univ.image (Fin.cons u p) = insert u (univ.image p) := by
  ext x
  simp only [mem_image, mem_univ, true_and, Fin.exists_fin_succ, Fin.cons_zero,
    Fin.cons_succ, mem_insert, eq_comm (a := u) (b := x)]

omit [Fintype V] in
private theorem record_cons {n : ℕ} (A S : Finset V) (u : V) (p : Fin n → V) :
    S ∪ (univ.image (Fin.cons u p) ∩ A) =
      remember A S u ∪ (univ.image p ∩ A) := by
  rw [image_cons]
  ext x
  by_cases h : x = u
  · subst x
    by_cases hA : u ∈ A <;> simp [remember, hA]
  · by_cases hA : u ∈ A <;> simp [remember, hA, h]

/-- A raw trace’s visited-set payoff equals the corresponding seen-kernel payoff. -/
theorem sum_seen_payoff_eq (K : V → V → ℝ) (A : Finset V) (f : V × Finset V → ℝ)
    (n t : ℕ) (v : V) (S : Finset V) :
    (∑ p : Fin n → V, traceWeight K n v p *
      f (finish n v p, S ∪ (univ.image p ∩ A))) =
      Erdos642FiniteProbability.future (seenKernel (fun _ => K) A) f n t (v,S) := by
  classical
  induction n generalizing t v S with
  | zero => simp [traceWeight, finish]
  | succ n ih =>
    rw [sum_trace_cons, Erdos642FiniteProbability.future_succ, sum_seenKernel_mul]
    simp only [traceWeight, Fin.cons_zero, Fin.tail_cons, finish, record_cons, mul_assoc,
      ← mul_sum]
    exact sum_congr rfl fun x _ =>
      congrArg (fun z => K v x * z) (ih (t+1) x (remember A S x))

/-- The seen-kernel event is exactly the event on the visited-set record of a raw trace. -/
theorem eventMass_seen_eq (K : V → V → ℝ) (A : Finset V) (P : V × Finset V → Prop)
    (n t : ℕ) (v : V) (S : Finset V) :
    Erdos642WalkTrace.eventMass K n v (fun p => P (finish n v p, S ∪ (univ.image p ∩ A))) =
      Erdos642FiniteProbability.eventMass (seenKernel (fun _ => K) A) P n t (v,S) := by
  classical
  calc
    _ = ∑ p : Fin n → V, traceWeight K n v p *
          (if P (finish n v p, S ∪ (univ.image p ∩ A)) then 1 else 0) := by
      simp only [Erdos642WalkTrace.eventMass, mul_ite, mul_one, mul_zero]
    _ = _ := by
      exact sum_seen_payoff_eq K A (fun s => if P s then 1 else 0) n t v S

/-- The seen-kernel law of sampled block endpoints equals the event on the original
unthinned graph trace. -/
theorem graph_eventMass_sample_seen_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (r t : ℕ) (v : V) (A S : Finset V) (P : V × Finset V → Prop) :
    Erdos642WalkTrace.eventMass (Erdos642RandomWalkKernel.step G) (r*k) v
      (fun p => let q := Erdos642TraceStride.samples k r hk p
                P (finish r v q, S ∪ (univ.image q ∩ A))) =
      Erdos642FiniteProbability.eventMass (seenKernel
        (fun _ => Erdos642RandomWalkKernel.walkWeight G k) A) P r t (v,S) := by
  calc
    _ = Erdos642WalkTrace.eventMass (Erdos642RandomWalkKernel.walkWeight G k) r v
          (fun q => P (finish r v q, S ∪ (univ.image q ∩ A))) :=
      Erdos642TraceStride.graph_eventMass_samples_eq G k hk r v _
    _ = _ := eventMass_seen_eq _ A P r t v S

end Erdos642TraceSeen

end Erdos642TraceSeenFile

section Erdos642TraceWindowsFile

/- Contiguous windows and conditional estimates in one finite raw trace law. -/

namespace Erdos642TraceWindows

open Finset Erdos642WalkTrace

variable {V : Type*}

def front (m n : ℕ) (p : Fin (n+m) → V) : Fin m → V :=
  p ∘ fun i => Fin.cast (Nat.add_comm m n) (Fin.castAdd n i)

def back (m n : ℕ) (p : Fin (n+m) → V) : Fin n → V :=
  p ∘ fun i => Fin.cast (Nat.add_comm m n) (Fin.natAdd m i)

theorem front_appendTrace (m n : ℕ) (p : Fin m → V) (q : Fin n → V) :
    front m n (appendTrace n m p q) = p :=
  funext (appendTrace_left m n p q)

theorem back_appendTrace (m n : ℕ) (p : Fin m → V) (q : Fin n → V) :
    back m n (appendTrace n m p q) = q :=
  funext (appendTrace_right m n p q)

/-- Skip a initial positions, read a window of b positions, and omit the c remaining positions. -/
def window (a b c : ℕ) :
    (Fin ((c+b)+a) → V) → (Fin b → V) :=
  front b c ∘ back a (c+b)

/-- Zero-based subtrace of length b beginning at coordinate a. -/
def sliceTrace (t a b : ℕ) (hab : a+b ≤ t) (p : Fin t → V) : Fin b → V :=
  fun i => p ⟨a+i.val, by omega⟩

variable [Fintype V]

theorem eventMass_le_one (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (hRow : ∀ v, ∑ u, K v u = 1) (n : ℕ) (v : V) (P : (Fin n → V) → Prop) :
    eventMass K n v P ≤ 1 := by
  have hnon := eventMass_nonneg K hK n v (fun p => ¬ P p)
  have hsum := eventMass_compl_add K hRow n v P
  linarith

/-- The law of the first m positions is independent of how much extra trace is retained. -/
theorem eventMass_front_eq (K : V → V → ℝ) (hRow : ∀ v, ∑ u, K v u = 1)
    (m n : ℕ) (v : V) (P : (Fin m → V) → Prop) :
    eventMass K (n+m) v (fun p => P (front m n p)) = eventMass K m v P := by
  classical
  rw [eventMass_split]
  simp only [front_appendTrace]
  unfold eventMass
  apply sum_congr rfl
  intro p _
  by_cases h : P p
  · simp only [if_pos h, sum_traceWeight K hRow, mul_one]
  · simp only [if_neg h, sum_const_zero, mul_zero]

/-- An estimate uniform in the current vertex holds on every suffix. -/
theorem eventMass_back_le (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (hRow : ∀ v, ∑ u, K v u = 1) (m n : ℕ) (v : V) (P : (Fin n → V) → Prop)
    {ε : ℝ} (hBound : ∀ u, eventMass K n u P ≤ ε) :
    eventMass K (n+m) v (fun p => P (back m n p)) ≤ ε := by
  rw [eventMass_split]
  simp only [back_appendTrace]
  calc
    _ ≤ ∑ p : Fin m → V, traceWeight K m v p * ε :=
      sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hBound _) (traceWeight_nonneg K hK m v p)
    _ = _ := by rw [← sum_mul, sum_traceWeight K hRow, one_mul]

/-- Shift a uniform starting-vertex bound to any contiguous subtrace. -/
theorem eventMass_window_le (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (hRow : ∀ v, ∑ u, K v u = 1) (a b c : ℕ) (v : V) (P : (Fin b → V) → Prop)
    {ε : ℝ} (hBound : ∀ u, eventMass K b u P ≤ ε) :
    eventMass K ((c+b)+a) v (fun p => P (window a b c p)) ≤ ε := by
  apply eventMass_back_le K hK hRow a (c+b) v (fun q => P (front b c q))
  intro u
  exact (eventMass_front_eq K hRow b c u P).trans_le (hBound u)

theorem eventMass_cast (K : V → V → ℝ) {t n : ℕ} (h : t = n) (v : V)
    (P : (Fin t → V) → Prop) :
    eventMass K t v P = eventMass K n v (fun p => P (p ∘ Fin.cast h)) := by
  subst n
  rfl

theorem eventMass_slice_le (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (hRow : ∀ v, ∑ u, K v u = 1) (t a b : ℕ) (hab : a+b ≤ t) (v : V)
    (P : (Fin b → V) → Prop) {ε : ℝ} (hBound : ∀ u, eventMass K b u P ≤ ε) :
    eventMass K t v (fun p => P (sliceTrace t a b hab p)) ≤ ε := by
  let c := t-(a+b)
  have ht : t = (c+b)+a := by dsimp only [c]; omega
  rw [eventMass_cast K ht]
  have he (p : Fin ((c+b)+a) → V) :
      sliceTrace t a b hab (p ∘ Fin.cast ht) = window a b c p := by
    funext i
    change p _ = p _
    congr 1
  simp only [he]
  exact eventMass_window_le K hK hRow a b c v P hBound

/-- Condition on any good prefix. Failure across the two blocks costs at most
the bad-prefix mass plus the uniform conditional continuation bound. -/
theorem eventMass_two_stage_le (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (hRow : ∀ v, ∑ u, K v u = 1) (m n : ℕ) (v : V)
    (good : (Fin m → V) → Prop) (failed : (Fin (n+m) → V) → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hBound : ∀ p : Fin m → V, 0 < traceWeight K m v p → good p →
      eventMass K n (finish m v p) (fun q => failed (appendTrace n m p q)) ≤ ε) :
    eventMass K (n+m) v failed ≤ eventMass K m v (fun p => ¬ good p) + ε := by
  classical
  rw [eventMass_split]
  calc
    _ ≤ ∑ p : Fin m → V, ((if ¬ good p then traceWeight K m v p else 0) +
        traceWeight K m v p * ε) := by
      apply sum_le_sum
      intro p _
      have hw := traceWeight_nonneg K hK m v p
      by_cases hpw : traceWeight K m v p = 0
      · simp [hpw]
      by_cases hg : good p
      · simp only [hg, not_true_eq_false, if_false, zero_add]
        exact mul_le_mul_of_nonneg_left (hBound p (lt_of_le_of_ne hw (Ne.symm hpw)) hg) hw
      · simp only [hg, not_false_eq_true, if_true]
        have h1 := eventMass_le_one K hK hRow n (finish m v p)
          (fun q => failed (appendTrace n m p q))
        calc
          _ ≤ traceWeight K m v p := by simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 hw
          _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hw hε)
    _ = _ := by
      rw [sum_add_distrib, ← sum_mul, sum_traceWeight K hRow, one_mul]
      apply congrArg (fun z : ℝ => z + ε)
      unfold eventMass
      exact sum_congr rfl fun p _ => by by_cases hg : good p <;> simp [hg]

/-- It suffices to bound continuation mass at endpoints of positive-mass prefixes. -/
theorem eventMass_back_le_on_support (K : V → V → ℝ) (hK : ∀ v u, 0 ≤ K v u)
    (hRow : ∀ v, ∑ u, K v u = 1) (m n : ℕ) (v : V) (P : (Fin n → V) → Prop)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hBound : ∀ p : Fin m → V, 0 < traceWeight K m v p →
      eventMass K n (finish m v p) P ≤ ε) :
    eventMass K (n+m) v (fun p => P (back m n p)) ≤ ε := by
  have he := eventMass_two_stage_le K hK hRow m n v (fun _ => True)
    (fun p => P (back m n p)) hε (fun p hp _ => by
      simpa only [back_appendTrace] using hBound p hp)
  simpa only [not_true_eq_false, eventMass, if_false, sum_const_zero, zero_add] using he

variable [DecidableEq V]

theorem graph_walkWeight_finish_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (v : V) (p : Fin n → V)
    (hp : 0 < traceWeight (Erdos642RandomWalkKernel.step G) n v p) :
    0 < Erdos642RandomWalkKernel.walkWeight G n v (finish n v p) := by
  classical
  let K := Erdos642RandomWalkKernel.step G
  let f (w : V) : ℝ := if w = finish n v p then 1 else 0
  have he := sum_finish_payoff_eq G n v f
  have hsum : (∑ q : Fin n → V, traceWeight K n v q * f (finish n v q)) =
      Erdos642RandomWalkKernel.walkWeight G n v (finish n v p) := by
    simpa only [K, f, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, if_true] using he
  rw [← hsum]
  apply hp.trans_le
  have hp' : f (finish n v p) = 1 := by simp [f]
  have h := single_le_sum (f := fun q => traceWeight K n v q * f (finish n v q))
    (fun q _ => mul_nonneg
      (traceWeight_nonneg K (Erdos642RandomWalkKernel.step_nonneg G) n v q)
      (by simp only [f]; split <;> positivity)) (mem_univ p)
  simpa only [hp', mul_one] using h

theorem graph_finish_parity (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring (Fin 2))
    (n : ℕ) (v : V) (p : Fin n → V)
    (hp : 0 < traceWeight (Erdos642RandomWalkKernel.step G) n v p) :
    ((C v).val + (C (finish n v p)).val + n) ≡ 0 [MOD 2] := by
  have hw := graph_walkWeight_finish_pos G n v p hp
  by_contra! he
  have hone : ((C v).val + (C (finish n v p)).val + n) ≡ 1 [MOD 2] := by
    change ((C v).val + (C (finish n v p)).val + n) % 2 ≠ 0 % 2 at he
    change ((C v).val + (C (finish n v p)).val + n) % 2 = 1 % 2
    omega
  rw [Erdos642RandomWalkKernel.walkWeight_zero_of_wrong_parity G C n v (finish n v p) hone] at hw
  exact (lt_irrefl _ hw)

theorem graph_finish_color_even (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring (Fin 2))
    (n : ℕ) (hn : Even n) (v : V) (p : Fin n → V)
    (hp : 0 < traceWeight (Erdos642RandomWalkKernel.step G) n v p) :
    C (finish n v p) = C v := by
  have hmod := Nat.even_iff.mp hn
  have h := graph_finish_parity G C n v p hp
  change ((C v).val + (C (finish n v p)).val + n) % 2 = 0 % 2 at h
  apply Fin.ext
  have hv := (C v).isLt
  have hu := (C (finish n v p)).isLt
  omega

theorem graph_finish_color_odd (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring (Fin 2))
    (n : ℕ) (hn : Odd n) (v : V) (p : Fin n → V)
    (hp : 0 < traceWeight (Erdos642RandomWalkKernel.step G) n v p) :
    C (finish n v p) ≠ C v := by
  have hmod := Nat.odd_iff.mp hn
  have h := graph_finish_parity G C n v p hp
  change ((C v).val + (C (finish n v p)).val + n) % 2 = 0 % 2 at h
  intro he
  rw [he] at h
  omega

end Erdos642TraceWindows

end Erdos642TraceWindowsFile

section Erdos642DisjointForestsFile

/- The greedy star-forest estimate for a finite bipartite edge relation. -/

namespace Erdos642StarForest

open Finset
open scoped BigOperators

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- Every row is the root of a star of `ℓ` distinct adjacent leaves. -/
def IsPacking (E : Finset (X × Y)) (A : Finset X) (B : Finset Y) (ℓ : ℕ)
    (P : Finset (X × Finset Y)) : Prop :=
  (∀ p ∈ P, p.1 ∈ A ∧ p.2 ⊆ B ∧ p.2.card = ℓ ∧ ∀ y ∈ p.2, (p.1,y) ∈ E) ∧
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1 ≠ q.1 ∧ Disjoint p.2 q.2

/-- A maximal packing leaves too few unoccupied neighbors at every unoccupied
root. Counting edges from unoccupied roots to occupied leaves gives the bound. -/
theorem exists_packing_edge_bound (E : Finset (X × Y)) (A : Finset X) (B : Finset Y)
    {d D ℓ : ℕ}
    (hLeft : ∀ x ∈ A, d ≤ (B.filter fun y => (x,y) ∈ E).card)
    (hRight : ∀ y ∈ B, (A.filter fun x => (x,y) ∈ E).card ≤ D) :
    ∃ P : Finset (X × Finset Y), IsPacking E A B ℓ P ∧ P.card ≤ A.card ∧
      (A.card - P.card) * (d + 1 - ℓ) ≤ P.card * ℓ * D := by
  classical
  let eligible := A ×ˢ B.powersetCard ℓ
  let C := eligible.powerset.filter (IsPacking E A B ℓ)
  have hC : C.Nonempty := ⟨∅,mem_filter.mpr
    ⟨mem_powerset.mpr (empty_subset _),by simp [IsPacking]⟩⟩
  obtain ⟨P,hPC,hMax⟩ := Finset.exists_max_image C Finset.card hC
  obtain ⟨hPE,hPacking⟩ := mem_filter.mp hPC
  let root := P.image Prod.fst
  let leaf := P.biUnion Prod.snd
  have hrootA : root ⊆ A := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hx
    exact (hPacking.1 r hr).1
  have hleafB : leaf ⊆ B := by
    intro y hy
    obtain ⟨r,hr,hyr⟩ := mem_biUnion.mp hy
    exact (hPacking.1 r hr).2.1 hyr
  have hRoot : root.card = P.card := by
    apply card_image_of_injOn
    intro p hp q hq heq
    by_contra hne
    exact (hPacking.2 p hp q hq hne).1 heq
  have hLeaf : leaf.card ≤ P.card * ℓ := by
    refine (card_biUnion_le (s := P) (t := Prod.snd)).trans_eq ?_
    calc
      _ = ∑ _r ∈ P, ℓ := Finset.sum_congr rfl fun p hp => (hPacking.1 p hp).2.2.1
      _ = _ := by simp
  have hUncovered (x : X) (hx : x ∈ A \ root) :
      ((B.filter fun y => (x,y) ∈ E) \ leaf).card < ℓ := by
    by_contra! h
    obtain ⟨L,hL,hLc⟩ := Finset.exists_subset_card_eq h
    have hxA := (mem_sdiff.mp hx).1
    have hxR := (mem_sdiff.mp hx).2
    have hLB : L ⊆ B := fun y hy => (mem_filter.mp (mem_sdiff.mp (hL hy)).1).1
    have hLE : ∀ y ∈ L, (x,y) ∈ E := fun y hy => (mem_filter.mp (mem_sdiff.mp (hL hy)).1).2
    have hLL : Disjoint L leaf :=
      Finset.disjoint_left.mpr fun _ hy hyl => (mem_sdiff.mp (hL hy)).2 hyl
    have hxP : (x,L) ∉ P := fun hP => hxR (mem_image_of_mem _ hP)
    let Q := insert (x,L) P
    have hQsub : Q ⊆ eligible := by
      apply insert_subset
      · exact mem_product.mpr ⟨hxA,mem_powersetCard.mpr ⟨hLB,hLc⟩⟩
      · exact mem_powerset.mp hPE
    have hd (p : X × Finset Y) (hp : p ∈ P) :
        x ≠ p.1 ∧ Disjoint L p.2 := by
      refine ⟨fun he => hxR (he.symm ▸ mem_image_of_mem _ hp),?_⟩
      exact Finset.disjoint_of_subset_right (fun y hy => mem_biUnion.mpr ⟨p,hp,hy⟩) hLL
    have hQpack : IsPacking E A B ℓ Q := by
      constructor
      · intro p hp
        rcases mem_insert.mp hp with rfl | hp
        · exact ⟨hxA,hLB,hLc,hLE⟩
        · exact hPacking.1 p hp
      · intro p hp q hq hne
        rcases mem_insert.mp hp with rfl | hp <;> rcases mem_insert.mp hq with rfl | hq
        · exact (hne rfl).elim
        · exact hd q hq
        · exact ⟨(hd p hp).1.symm,(hd p hp).2.symm⟩
        · exact hPacking.2 p hp q hq hne
    have hQ := hMax Q (mem_filter.mpr ⟨mem_powerset.mpr hQsub,hQpack⟩)
    have hcard : Q.card = P.card + 1 := card_insert_of_notMem hxP
    omega
  have hLeftUsed (x : X) (hx : x ∈ A \ root) :
      d + 1 - ℓ ≤ (leaf.filter fun y => (x,y) ∈ E).card := by
    let N := B.filter (fun y => (x,y) ∈ E)
    have hInt : N ∩ leaf = leaf.filter (fun y => (x,y) ∈ E) := by
      ext y
      simp only [N,mem_inter,mem_filter]
      have hy : y ∈ leaf → y ∈ B := fun hy => hleafB hy
      tauto
    have ht := card_sdiff_add_card_inter N leaf
    rw [hInt] at ht
    have hL := hLeft x (mem_sdiff.mp hx).1
    have hU := hUncovered x hx
    change d ≤ N.card at hL
    change (N \ leaf).card < ℓ at hU
    omega
  have hDouble : (∑ x ∈ A \ root, (leaf.filter fun y => (x,y) ∈ E).card) =
      ∑ y ∈ leaf, ((A \ root).filter fun x => (x,y) ∈ E).card := by
    simp only [card_filter]
    exact Finset.sum_comm
  refine ⟨P,hPacking,by rw [← hRoot]; exact card_le_card hrootA,?_⟩
  calc
    (A.card - P.card) * (d + 1 - ℓ) = ∑ _x ∈ A \ root, (d + 1 - ℓ) := by
      rw [Finset.sum_const_nat (fun _ _ => rfl),card_sdiff_of_subset hrootA,hRoot]
    _ ≤ ∑ x ∈ A \ root, (leaf.filter fun y => (x,y) ∈ E).card := Finset.sum_le_sum hLeftUsed
    _ = ∑ y ∈ leaf, ((A \ root).filter fun x => (x,y) ∈ E).card := hDouble
    _ ≤ ∑ _y ∈ leaf, D := by
      apply Finset.sum_le_sum
      intro y hy
      refine (card_le_card ?_).trans (hRight y (hleafB hy))
      intro x hx
      exact mem_filter.mpr ⟨(mem_sdiff.mp (mem_filter.mp hx).1).1,(mem_filter.mp hx).2⟩
    _ = leaf.card * D := by simp
    _ ≤ _ := Nat.mul_le_mul_right D hLeaf

/-- The numerical stars-per-vertex bound in the nearly regular case. -/
theorem exists_many_stars (E : Finset (X × Y)) (A : Finset X) (B : Finset Y)
    {n d D : ℕ} (hd : 1000000 ≤ d) (hA : n ≤ 1001 * A.card) (hD : D ≤ 1000 * d)
    (hLeft : ∀ x ∈ A, d ≤ (B.filter fun y => (x,y) ∈ E).card)
    (hRight : ∀ y ∈ B, (A.filter fun x => (x,y) ∈ E).card ≤ D) :
    ∃ P : Finset (X × Finset Y), IsPacking E A B (d / 1000000) P ∧
      n ≤ 100 * d * P.card := by
  let ℓ := d / 1000000
  let k := d + 1 - ℓ
  have hl : ℓ * 1000000 ≤ d := Nat.div_mul_le_self d 1000000
  have hk : d ≤ 2 * k := by dsimp only [k]; omega
  have hkpos : 0 < k := by omega
  obtain ⟨P,hP,hPA,hCount⟩ := exists_packing_edge_bound (ℓ := ℓ) E A B hLeft hRight
  change (A.card - P.card) * k ≤ P.card * ℓ * D at hCount
  have hK : 1001 * k ≤ d * k := Nat.mul_le_mul_right k (by omega)
  have hDD : 1000 * (ℓ * D) ≤ d * d := by
    calc
      _ ≤ 1000 * (ℓ * (1000 * d)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hD)
      _ = (ℓ * 1000000) * d := by ring
      _ ≤ _ := Nat.mul_le_mul_right d hl
  have hkdd : d * d ≤ 2 * (d * k) := by
    calc
      _ ≤ (2 * k) * d := Nat.mul_le_mul_right d hk
      _ = _ := by ring
  have hDD' := hDD.trans hkdd
  have hKD : 1001 * (ℓ * D) ≤ 3 * (d * k) := by omega
  have hScale : 1001 * (k + ℓ * D) ≤ 100 * d * k := by
    rw [Nat.mul_add,Nat.mul_assoc]
    omega
  have hAK : A.card * k ≤ P.card * (k + ℓ * D) := by
    calc
      _ = (A.card - P.card) * k + P.card * k := by rw [← Nat.add_mul,Nat.sub_add_cancel hPA]
      _ ≤ P.card * ℓ * D + P.card * k := Nat.add_le_add_right hCount _
      _ = _ := by ring
  refine ⟨P,hP,?_⟩
  have hnk : n * k ≤ (100 * d * P.card) * k := calc
    _ ≤ (1001 * A.card) * k := Nat.mul_le_mul_right k hA
    _ = 1001 * (A.card * k) := by ring
    _ ≤ 1001 * (P.card * (k + ℓ * D)) := Nat.mul_le_mul_left _ hAK
    _ = P.card * (1001 * (k + ℓ * D)) := by ring
    _ ≤ P.card * (100 * d * k) := Nat.mul_le_mul_left _ hScale
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hnk hkpos

end Erdos642StarForest



namespace Erdos642StarForest

open Finset

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

private def usedRoots (L : List (Finset (X × Finset Y))) : Finset X :=
  L.foldr (fun P R => P.image Prod.fst ∪ R) ∅

private theorem mem_used_roots {L : List (Finset (X × Finset Y))} {x : X} :
    x ∈ usedRoots L ↔ ∃ P ∈ L, x ∈ P.image Prod.fst := by
  induction L with
  | nil => simp [usedRoots]
  | cons P L ih =>
    change x ∈ P.image Prod.fst ∪ usedRoots L ↔ _
    simp only [mem_union,ih,List.mem_cons]
    constructor
    · rintro (hP | ⟨Q,hQL,hxQ⟩)
      · exact ⟨P,Or.inl rfl,hP⟩
      · exact ⟨Q,Or.inr hQL,hxQ⟩
    · rintro ⟨Q,rfl | hQL,hxQ⟩
      · exact Or.inl hxQ
      · exact Or.inr ⟨Q,hQL,hxQ⟩

private theorem card_used_roots_le {L : List (Finset (X × Finset Y))} {r : ℕ}
    (hL : ∀ P ∈ L, P.card = r) : (usedRoots L).card ≤ L.length * r := by
  induction L with
  | nil => simp [usedRoots]
  | cons P L ih =>
    change (P.image Prod.fst ∪ usedRoots L).card ≤ (L.length + 1) * r
    have hP : (P.image Prod.fst).card ≤ r := card_image_le.trans_eq (hL P (by simp))
    have hR := ih (fun Q hQ => hL Q (by simp [hQ]))
    rw [Nat.add_mul,one_mul,Nat.add_comm]
    exact (card_union_le _ _).trans (Nat.add_le_add hP hR)

private theorem packing_of_subset {E : Finset (X × Y)} {A A' : Finset X} {B : Finset Y}
    {ℓ : ℕ} {P Q : Finset (X × Finset Y)} (hP : IsPacking E A' B ℓ P)
    (hA : A' ⊆ A) (hQ : Q ⊆ P) : IsPacking E A B ℓ Q := by
  exact ⟨fun p hp => ⟨hA (hP.1 p (hQ hp)).1,(hP.1 p (hQ hp)).2⟩,
    fun p hp q hq hn => hP.2 p (hQ hp) q (hQ hq) hn⟩

/-- If one can find the required forest after deleting each small set of roots,
then the forests may be chosen with pairwise disjoint root sets. -/
theorem exists_root_disjoint_forests (E : Finset (X × Y)) (A : Finset X) (B : Finset Y)
    (ℓ r m : ℕ)
    (hExtend : ∀ R ⊆ A, R.card < m * r → ∃ P : Finset (X × Finset Y),
      IsPacking E (A \ R) B ℓ P ∧ r ≤ P.card) :
    ∃ L : List (Finset (X × Finset Y)), L.length = m ∧
      L.Pairwise (fun P Q => Disjoint (P.image Prod.fst) (Q.image Prod.fst)) ∧
      ∀ P ∈ L, IsPacking E A B ℓ P ∧ P.card = r := by
  classical
  by_cases hr : r = 0
  · subst r
    refine ⟨List.replicate m ∅,by simp,?_,?_⟩
    · exact List.pairwise_replicate.mpr (Or.inr (by simp))
    · intro P hP
      have he : P = ∅ := (List.mem_replicate.mp hP).2
      subst P
      simp [IsPacking]
  have hrp : 0 < r := Nat.pos_of_ne_zero hr
  have aux (j : ℕ) (hj : j ≤ m) :
      ∃ L : List (Finset (X × Finset Y)), L.length = j ∧
        L.Pairwise (fun P Q => Disjoint (P.image Prod.fst) (Q.image Prod.fst)) ∧
        ∀ P ∈ L, IsPacking E A B ℓ P ∧ P.card = r := by
    induction j with
    | zero => exact ⟨[],rfl,by simp,by simp⟩
    | succ j ih =>
      obtain ⟨L,hLen,hPair,hForest⟩ := ih (by omega)
      let R := usedRoots L
      have hR : R ⊆ A := by
        intro x hx
        obtain ⟨P,hPL,hxP⟩ := mem_used_roots.mp hx
        obtain ⟨p,hpP,hx⟩ := mem_image.mp hxP
        exact hx ▸ (hForest P hPL).1.1 p hpP |>.1
      have hRle := card_used_roots_le (fun P hP => (hForest P hP).2)
      rw [hLen] at hRle
      have hRlt : R.card < m * r := hRle.trans_lt (Nat.mul_lt_mul_of_pos_right (by omega) hrp)
      obtain ⟨P,hP,hPc⟩ := hExtend R hR hRlt
      obtain ⟨Q,hQP,hQc⟩ := Finset.exists_subset_card_eq hPc
      have hQA := packing_of_subset hP sdiff_subset hQP
      refine ⟨Q :: L,by simp [hLen],List.pairwise_cons.mpr ⟨?_,hPair⟩,?_⟩
      · intro V hVL
        apply Finset.disjoint_left.mpr
        intro x hxQ hxV
        obtain ⟨q,hqQ,hx⟩ := mem_image.mp hxQ
        have hn : q.1 ∉ R := (mem_sdiff.mp (hP.1 q (hQP hqQ)).1).2
        exact hn (hx.symm ▸ mem_used_roots.mpr ⟨V,hVL,hxV⟩)
      · intro V hV
        rcases List.mem_cons.mp hV with rfl | hv
        · exact ⟨hQA,hQc⟩
        · exact hForest V hv
  exact aux m le_rfl

end Erdos642StarForest

end Erdos642DisjointForestsFile

section Erdos642StarOccupancyFile

/- Deterministic occupancy and rounding for the forest selection in DMMS, Claim 3.6. -/

namespace Erdos642StarOccupancy

open Finset Erdos642StarForest

variable {X Y : Type*} [DecidableEq Y]

theorem card_selected_leaf_union {E : Finset (X × Y)} {A : Finset X} {B : Finset Y}
    {ell : ℕ} {P Q : Finset (X × Finset Y)} (hP : IsPacking E A B ell P) (hQ : Q ⊆ P) :
    (Q.biUnion Prod.snd).card = Q.card * ell := by
  rw [Finset.card_biUnion (fun p hp q hq hpq => (hP.2 p (hQ hp) q (hQ hq) hpq).2)]
  exact Finset.sum_const_nat (fun p hp => (hP.1 p (hQ hp)).2.2.1)

theorem card_selected_visited_leaf_union {E : Finset (X × Y)} {A : Finset X} {B : Finset Y}
    {ell : ℕ} {P Q : Finset (X × Finset Y)} (hP : IsPacking E A B ell P) (hQ : Q ⊆ P)
    (S : Finset Y) :
    (Q.biUnion Prod.snd ∩ S).card = ∑ p ∈ Q, (p.2 ∩ S).card := by
  rw [Finset.biUnion_inter]
  apply Finset.card_biUnion
  intro p hp q hq hpq
  exact Finset.disjoint_of_subset_left inter_subset_left
    (Finset.disjoint_of_subset_right inter_subset_left (hP.2 p (hQ hp) q (hQ hq) hpq).2)

/-- If fewer than half the stars meet the threshold, a rounded-up half of
the forest witnesses a small intersection with the sampled vertices. -/
theorem exists_half_small_leaf_union {E : Finset (X × Y)} {A : Finset X} {B : Finset Y}
    {ell : ℕ} {P : Finset (X × Finset Y)} (hP : IsPacking E A B ell P)
    (S : Finset Y) (R : ℝ)
    (hFew : 2 * (P.filter (fun p => R ≤ ((p.2 ∩ S).card : ℝ))).card < P.card) :
    ∃ Q ∈ P.powersetCard ((P.card + 1) / 2),
      (Q.biUnion Prod.snd).card = Q.card * ell ∧
      ((Q.biUnion Prod.snd ∩ S).card : ℝ) < (Q.card : ℝ) * R := by
  classical
  let good : X × Finset Y → Prop := fun p => R ≤ ((p.2 ∩ S).card : ℝ)
  have hSplit := Finset.card_filter_add_card_filter_not (s := P) good
  change 2 * (P.filter good).card < P.card at hFew
  have hBad : (P.card + 1) / 2 ≤ (P.filter (fun p => ¬ good p)).card := by omega
  obtain ⟨Q, hQ, hQcard⟩ := Finset.exists_subset_card_eq hBad
  have hQP : Q ⊆ P := hQ.trans (Finset.filter_subset _ _)
  refine ⟨Q, Finset.mem_powersetCard.mpr ⟨hQP, hQcard⟩,
    card_selected_leaf_union hP hQP, ?_⟩
  rw [card_selected_visited_leaf_union hP hQP]
  push_cast
  have hQpos : Q.Nonempty := Finset.card_pos.mp (by omega)
  calc
    (∑ p ∈ Q, ((p.2 ∩ S).card : ℝ)) < ∑ _p ∈ Q, R := by
      apply Finset.sum_lt_sum_of_nonempty hQpos
      intro p hp
      exact lt_of_not_ge (Finset.mem_filter.mp (hQ hp)).2
    _ = (Q.card : ℝ) * R := by simp

end Erdos642StarOccupancy

end Erdos642StarOccupancyFile

section Erdos642StarOccupancyProbabilityFile

/- The adapted finite-kernel form of DMMS, Claim 3.6. -/

namespace Erdos642StarOccupancyProbability

open Finset Erdos642FiniteProbability Erdos642SeenSetProbability Erdos642StarForest

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem remember_inter {A B : Finset V} (hAB : A ⊆ B) (S : Finset V) (v : V) :
    remember B S v ∩ A = remember A (S ∩ A) v := by
  ext w
  by_cases ha : v ∈ A
  · have hb := hAB ha
    simp only [remember, if_pos ha, if_pos hb, mem_inter, mem_insert]
    aesop
  · by_cases hb : v ∈ B
    · simp only [remember, if_neg ha, if_pos hb, mem_inter, mem_insert]
      aesop
    · simp [remember, ha, hb]

/-- Monitoring a larger set and projecting its visit record agrees with
monitoring the smaller set throughout the process. -/
theorem future_seen_inter (K : ℕ → V → V → ℝ) {A B : Finset V} (hAB : A ⊆ B)
    (f : V × Finset V → ℝ) (n : ℕ) :
    ∀ t : ℕ, ∀ x : V, ∀ S : Finset V,
      future (seenKernel K B) (fun y => f (y.1, y.2 ∩ A)) n t (x, S) =
        future (seenKernel K A) f n t (x, S ∩ A) := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro t x S
    rw [future_succ, future_succ, sum_seenKernel_mul, sum_seenKernel_mul]
    apply Finset.sum_congr rfl
    intro v _
    simp only [ih, remember_inter hAB]

theorem eventMass_seen_inter_le_exp (K : ℕ → V → V → ℝ) {A B : Finset V} (hAB : A ⊆ B)
    (N : ℕ) (s p ρ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hρ : 0 ≤ ρ)
    (hK : IsStochasticThrough K N)
    (hpoint : ∀ t < N, ∀ u v : V, v ∈ A → ρ ≤ K t u v)
    (hbudget : p ≤ ρ * ((A.card : ℝ) - s))
    (hs : s ≤ (N : ℝ) * p / 4) (x : V) :
    eventMass (seenKernel K B) (fun y => ((A ∩ y.2).card : ℝ) ≤ s) N 0 (x, ∅)
      ≤ Real.exp (-s) := by
  have he := future_seen_inter K hAB
    (fun y => if (y.2.card : ℝ) ≤ s then 1 else 0) N 0 x ∅
  have ht := lowerTail_seen_le_exp_neg K A N s p ρ hp0 hp1 hρ hK hpoint hbudget hs x
  rw [eventMass]
  simpa only [lowerTail, empty_inter, inter_comm A] using he.trans_le ht

variable {X : Type*}

/-- The lower tail for the number of good stars in one forest. Here a star is
good if at least `ell * N * ρ / 8` of its leaves were sampled, and every
sampling step assigns mass at least `ρ` to every vertex of the leaf side. -/
theorem one_forest_lower_tail (K : ℕ → V → V → ℝ) {E : Finset (X × V)}
    {A : Finset X} {B : Finset V} {ell : ℕ} {P : Finset (X × Finset V)}
    (hP : IsPacking E A B ell P)
    (N : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρB : ρ * (B.card : ℝ) ≤ 1)
    (hK : IsStochasticThrough K N)
    (hpoint : ∀ t < N, ∀ u v : V, v ∈ B → ρ ≤ K t u v)
    (hN : (N : ℝ) * ρ ≤ 4) (hScale : 4 ≤ (ell : ℝ) * ((N : ℝ) * ρ / 8)) (x : V) :
    let R := (ell : ℝ) * ((N : ℝ) * ρ / 8)
    eventMass (seenKernel K B)
      (fun y => 2 * (P.filter fun p => R ≤ ((p.2 ∩ y.2).card : ℝ)).card < P.card)
      N 0 (x, ∅) ≤ Real.exp (-((P.card : ℝ) * R / 4)) := by
  classical
  let eps := (N : ℝ) * ρ / 8
  let R := (ell : ℝ) * eps
  let J := P.powersetCard ((P.card + 1) / 2)
  let Bad (Q : Finset (X × Finset V)) (y : V × Finset V) : Prop :=
    ((Q.biUnion Prod.snd ∩ y.2).card : ℝ) ≤ (Q.card : ℝ) * R
  have hR : 4 ≤ R := hScale
  have hR0 : 0 ≤ R := by linarith
  have heps : eps ≤ 1 / 2 := by dsimp [eps]; linarith
  have hsub (Q : Finset (X × Finset V)) (hQ : Q ∈ J) :
      Q.biUnion Prod.snd ⊆ B := by
    apply Finset.biUnion_subset.mpr
    intro p hp
    exact (hP.1 p ((Finset.mem_powersetCard.mp hQ).1 hp)).2.1
  have hFew (y : V × Finset V)
      (hy : 2 * (P.filter fun p => R ≤ ((p.2 ∩ y.2).card : ℝ)).card < P.card) :
      ∃ Q ∈ J, Bad Q y := by
    obtain ⟨Q, hQ, _, hs⟩ :=
      Erdos642StarOccupancy.exists_half_small_leaf_union hP y.2 R hy
    exact ⟨Q, hQ, hs.le⟩
  have hFixed (Q : Finset (X × Finset V)) (hQ : Q ∈ J) :
      eventMass (seenKernel K B) (Bad Q) N 0 (x, ∅) ≤
        Real.exp (-((P.card : ℝ) * R / 2)) := by
    let T := Q.biUnion Prod.snd
    let u := ρ * (T.card : ℝ) / 2
    let s := (Q.card : ℝ) * R
    have hQsub := (Finset.mem_powersetCard.mp hQ).1
    have hQcard := (Finset.mem_powersetCard.mp hQ).2
    change Q.card = (P.card + 1) / 2 at hQcard
    have hCard : T.card = Q.card * ell :=
      Erdos642StarOccupancy.card_selected_leaf_union hP hQsub
    have hT : T ⊆ B := hsub Q hQ
    have hTsize : (T.card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card hT
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hu1 : u ≤ 1 := by
      have := (mul_le_mul_of_nonneg_left hTsize hρ).trans hρB
      dsimp [u]
      linarith
    have hs : s = (T.card : ℝ) * eps := by
      simp only [s, R, hCard, Nat.cast_mul]
      ring
    have hbudget : u ≤ ρ * ((T.card : ℝ) - s) := by
      have hprod := mul_le_mul_of_nonneg_left heps (Nat.cast_nonneg T.card : (0 : ℝ) ≤ T.card)
      rw [hs]
      dsimp [u]
      calc
        ρ * (T.card : ℝ) / 2 = ρ * ((T.card : ℝ) - (T.card : ℝ) * (1 / 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hprod]) hρ
    have hsmall : s ≤ (N : ℝ) * u / 4 := by
      rw [hs]
      dsimp [u, eps]
      ring_nf
      exact le_rfl
    have htail := eventMass_seen_inter_le_exp K hT N s u ρ hu0 hu1 hρ
      hK (fun t ht v w hw => hpoint t ht v w (hT hw)) hbudget hsmall x
    have hhalf : (P.card : ℝ) ≤ 2 * (Q.card : ℝ) := by
      exact_mod_cast (show P.card ≤ 2 * Q.card by omega)
    have hExp : Real.exp (-s) ≤ Real.exp (-((P.card : ℝ) * R / 2)) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hhalf hR0
      dsimp [s]
      linarith only [hh]
    exact htail.trans hExp
  have hComb : J.card ≤ 2 ^ P.card := by
    rw [← Finset.card_powerset]
    apply Finset.card_le_card
    intro Q hQ
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hQ).1
  have hExpComb : (J.card : ℝ) ≤ Real.exp (P.card : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ P.card := by exact_mod_cast hComb
      _ ≤ Real.exp 1 ^ P.card := pow_le_pow_left₀ (by norm_num)
        (by
          have h := Real.add_one_le_exp 1
          norm_num at h
          exact h) _
      _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  let T := seenKernel K B
  let Few (y : V × Finset V) : Prop :=
    2 * (P.filter fun p => R ≤ ((p.2 ∩ y.2).card : ℝ)).card < P.card
  let z : V × Finset V := (x, ∅)
  have hTK : IsStochasticThrough T N := seenKernel_stochastic K B N hK
  change eventMass T Few N 0 z ≤ _
  calc
    _ ≤ eventMass T (fun y => ∃ Q ∈ J, Bad Q y) N 0 z := by
      unfold eventMass
      apply future_mono hTK _ N 0 (by omega)
      intro y
      by_cases hy : Few y
      · rw [if_pos hy, if_pos (hFew y hy)]
      · rw [if_neg hy]
        split <;> norm_num
    _ ≤ ∑ Q ∈ J, eventMass T (Bad Q) N 0 z :=
      eventMass_union_le hTK J Bad N 0 (by omega) z
    _ ≤ ∑ _Q ∈ J, Real.exp (-((P.card : ℝ) * R / 2)) := Finset.sum_le_sum hFixed
    _ = (J.card : ℝ) * Real.exp (-((P.card : ℝ) * R / 2)) := by simp
    _ ≤ Real.exp (P.card : ℝ) * Real.exp (-((P.card : ℝ) * R / 2)) :=
      mul_le_mul_of_nonneg_right hExpComb (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      change (P.card : ℝ) + -((P.card : ℝ) * R / 2) ≤ -((P.card : ℝ) * R / 4)
      have hh := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card)
      linarith only [hh]

end Erdos642StarOccupancyProbability

end Erdos642StarOccupancyProbabilityFile

section Erdos642ManyForestsSamplingFile

/- Aggregating the first sampled block over root-disjoint star forests. -/

namespace Erdos642ManyForestsSampling

open Finset Erdos642FiniteProbability Erdos642SeenSetProbability Erdos642StarForest
open Erdos642StarOccupancyProbability

variable {V X I : Type*} [Fintype V] [DecidableEq V]

/-- The probability that some indexed forest has fewer than half good stars. -/
theorem all_forests_lower_tail (K : ℕ → V → V → ℝ) {E : Finset (X × V)}
    {A : Finset X} {B : Finset V} {ell : ℕ} (J : Finset I)
    (P : I → Finset (X × Finset V)) (hP : ∀ i ∈ J, IsPacking E A B ell (P i))
    (a : ℝ) (hCard : ∀ i ∈ J, a ≤ ((P i).card : ℝ))
    (N : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρB : ρ * (B.card : ℝ) ≤ 1)
    (hK : IsStochasticThrough K N)
    (hpoint : ∀ t < N, ∀ u v : V, v ∈ B → ρ ≤ K t u v)
    (hN : (N : ℝ) * ρ ≤ 4) (hScale : 4 ≤ (ell : ℝ) * ((N : ℝ) * ρ / 8)) (x : V) :
    let R := (ell : ℝ) * ((N : ℝ) * ρ / 8)
    eventMass (seenKernel K B)
      (fun y => ∃ i ∈ J, 2 * ((P i).filter fun p => R ≤ ((p.2 ∩ y.2).card : ℝ)).card < (P i).card)
      N 0 (x, ∅) ≤ (J.card : ℝ) * Real.exp (-(a * R / 4)) := by
  classical
  let R := (ell : ℝ) * ((N : ℝ) * ρ / 8)
  let T := seenKernel K B
  let Few (i : I) (y : V × Finset V) : Prop :=
    2 * ((P i).filter fun p => R ≤ ((p.2 ∩ y.2).card : ℝ)).card < (P i).card
  have hR : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 4).trans hScale
  have hTK : IsStochasticThrough T N := seenKernel_stochastic K B N hK
  change eventMass T (fun y => ∃ i ∈ J, Few i y) N 0 (x, ∅) ≤
    (J.card : ℝ) * Real.exp (-(a * R / 4))
  calc
    _ ≤ ∑ i ∈ J, eventMass T (Few i) N 0 (x, ∅) :=
      eventMass_union_le hTK J Few N 0 (by omega) (x, ∅)
    _ ≤ ∑ _i ∈ J, Real.exp (-(a * R / 4)) := by
      apply Finset.sum_le_sum
      intro i hi
      refine (one_forest_lower_tail K (hP i hi) N ρ hρ hρB hK hpoint hN hScale x).trans ?_
      apply Real.exp_le_exp.mpr
      change -(((P i).card : ℝ) * R / 4) ≤ -(a * R / 4)
      have hd := mul_le_mul_of_nonneg_right (hCard i hi) hR
      linarith only [hd]
    _ = _ := by simp

variable [DecidableEq X]

/-- The roots whose stars have met the leaf threshold in at least one forest. -/
noncomputable def goodRoots (J : Finset I) (P : I → Finset (X × Finset V))
    (S : Finset V) (R : ℝ) : Finset X := by
  classical
  exact J.biUnion fun i => ((P i).filter fun p => R ≤ ((p.2 ∩ S).card : ℝ)).image Prod.fst

omit [Fintype V] in
theorem mem_goodRoots {J : Finset I} {P : I → Finset (X × Finset V)}
    {S : Finset V} {R : ℝ} {x : X} :
    x ∈ goodRoots J P S R ↔
      ∃ i ∈ J, ∃ p ∈ P i, R ≤ ((p.2 ∩ S).card : ℝ) ∧ p.1 = x := by
  classical
  simp only [goodRoots, mem_biUnion, mem_image, mem_filter]
  aesop

omit [Fintype V] in
/-- All good-star counts add without collisions when the forests have disjoint roots. -/
theorem card_goodRoots {E : Finset (X × V)} {A : Finset X} {B : Finset V} {ell : ℕ}
    (J : Finset I) (P : I → Finset (X × Finset V))
    (hP : ∀ i ∈ J, IsPacking E A B ell (P i))
    (hDisj : (J : Set I).PairwiseDisjoint (fun i => (P i).image Prod.fst))
    (S : Finset V) (R : ℝ) :
    (goodRoots J P S R).card =
      ∑ i ∈ J, ((P i).filter fun p => R ≤ ((p.2 ∩ S).card : ℝ)).card := by
  classical
  let F := fun i => (P i).filter fun p => R ≤ ((p.2 ∩ S).card : ℝ)
  have hf (i : I) : (F i).image Prod.fst ⊆ (P i).image Prod.fst :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hDisj' : (J : Set I).PairwiseDisjoint (fun i => (F i).image Prod.fst) := by
    intro i hi j hj hne
    exact Finset.disjoint_of_subset_left (hf i)
      (Finset.disjoint_of_subset_right (hf j) (hDisj hi hj hne))
  change (J.biUnion fun i => (F i).image Prod.fst).card = _
  rw [Finset.card_biUnion hDisj']
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.card_image_of_injOn
  intro p hp q hq hEq
  by_contra hne
  exact ((hP i hi).2 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hne).1 hEq

end Erdos642ManyForestsSampling

end Erdos642ManyForestsSamplingFile

section Erdos642SideSamplingFile

/- Supported even-stride kernels for sampling a single bipartition class. -/

namespace Erdos642SideSampling

open Finset Erdos642FiniteProbability Erdos642SeenSetProbability
open Erdos642StarForest Erdos642ManyForestsSampling Erdos642StarOccupancyProbability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replace irrelevant rows outside a preserved set by a row at an anchor. -/
private def patch (K : ℕ → V → V → ℝ) (B : Finset V) (b : V) (t : ℕ) (u v : V) : ℝ :=
  K t (if u ∈ B then u else b) v

private theorem patch_stochastic (K : ℕ → V → V → ℝ) (B : Finset V) (b : V) (N : ℕ)
    (hK : IsStochasticThrough K N) : IsStochasticThrough (patch K B b) N := by
  intro t ht u
  exact hK t ht (if u ∈ B then u else b)

/-- On a preserved side, the patched kernel gives the same probabilities for
every function of the terminal vertex and the recorded sample. -/
private theorem future_patch (K : ℕ → V → V → ℝ) (B : Finset V) (b : V)
    (hClosed : ∀ t u v, u ∈ B → v ∉ B → K t u v = 0)
    (f : V × Finset V → ℝ) (n : ℕ) :
    ∀ t u S, u ∈ B →
      future (seenKernel (patch K B b) B) f n t (u, S) =
        future (seenKernel K B) f n t (u, S) := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro t u S hu
    rw [future_succ, future_succ, sum_seenKernel_mul, sum_seenKernel_mul]
    apply Finset.sum_congr rfl
    intro v _
    rw [patch, if_pos hu]
    by_cases hv : v ∈ B
    · rw [ih _ _ _ hv]
    · rw [hClosed _ _ _ hu hv, zero_mul, zero_mul]

variable {X I : Type*}

/-- The first-block forest bound when the kernel only mixes within one side. -/
theorem all_forests_lower_tail_on_side (K : ℕ → V → V → ℝ) {E : Finset (X × V)}
    {A : Finset X} {B : Finset V} {ell : ℕ} (J : Finset I)
    (P : I → Finset (X × Finset V)) (hP : ∀ i ∈ J, IsPacking E A B ell (P i))
    (a : ℝ) (hCard : ∀ i ∈ J, a ≤ ((P i).card : ℝ))
    (N : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρB : ρ * (B.card : ℝ) ≤ 1)
    (hK : IsStochasticThrough K N)
    (hClosed : ∀ t u v, u ∈ B → v ∉ B → K t u v = 0)
    (hpoint : ∀ t < N, ∀ u v : V, u ∈ B → v ∈ B → ρ ≤ K t u v)
    (hN : (N : ℝ) * ρ ≤ 4) (hScale : 4 ≤ (ell : ℝ) * ((N : ℝ) * ρ / 8))
    (x : V) (hx : x ∈ B) :
    let R := (ell : ℝ) * ((N : ℝ) * ρ / 8)
    eventMass (seenKernel K B)
      (fun y => ∃ i ∈ J, 2 * ((P i).filter fun p => R ≤ ((p.2 ∩ y.2).card : ℝ)).card < (P i).card)
      N 0 (x, ∅) ≤ (J.card : ℝ) * Real.exp (-(a * R / 4)) := by
  let K' := patch K B x
  have hK' := patch_stochastic K B x N hK
  have hpoint' : ∀ t < N, ∀ u v : V, v ∈ B → ρ ≤ K' t u v := by
    intro t ht u v hv
    by_cases hu : u ∈ B
    · simpa only [K', patch, if_pos hu] using hpoint t ht u v hu hv
    · simpa only [K', patch, if_neg hu] using hpoint t ht x v hx hv
  have h := all_forests_lower_tail K' J P hP a hCard N ρ hρ hρB hK' hpoint' hN hScale x
  simp only [eventMass] at h ⊢
  rwa [future_patch K B x hClosed _ N 0 x ∅ hx] at h

/-- Lower-tail estimate for any subset of a single preserved side. -/
theorem eventMass_seen_inter_le_exp_on_side (K : ℕ → V → V → ℝ) {A B : Finset V}
    (hAB : A ⊆ B) (N : ℕ) (s p ρ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hρ : 0 ≤ ρ)
    (hK : IsStochasticThrough K N)
    (hClosed : ∀ t u v, u ∈ B → v ∉ B → K t u v = 0)
    (hpoint : ∀ t < N, ∀ u v : V, u ∈ B → v ∈ A → ρ ≤ K t u v)
    (hbudget : p ≤ ρ * ((A.card : ℝ) - s))
    (hs : s ≤ (N : ℝ) * p / 4) (x : V) (hx : x ∈ B) :
    eventMass (seenKernel K B) (fun y => ((A ∩ y.2).card : ℝ) ≤ s) N 0 (x, ∅)
      ≤ Real.exp (-s) := by
  let K' := patch K B x
  have hK' := patch_stochastic K B x N hK
  have hpoint' : ∀ t < N, ∀ u v : V, v ∈ A → ρ ≤ K' t u v := by
    intro t ht u v hv
    by_cases hu : u ∈ B
    · simpa only [K', patch, if_pos hu] using hpoint t ht u v hu hv
    · simpa only [K', patch, if_neg hu] using hpoint t ht x v hx hv
  have h := eventMass_seen_inter_le_exp K' hAB N s p ρ hp0 hp1 hρ hK' hpoint' hbudget hs x
  simp only [eventMass] at h ⊢
  rwa [future_patch K B x hClosed _ N 0 x ∅ hx] at h

open SimpleGraph Erdos642RandomWalkKernel

/-- An even-stride bipartite walk cannot leave its starting color class. -/
theorem even_walk_closed (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring (Fin 2))
    (c : Fin 2) (k : ℕ) {u v : V} (hu : C u = c) (hv : C v ≠ c) :
    walkWeight G (2 * k) u v = 0 := by
  apply walkWeight_zero_of_wrong_parity G C
  change ((C u).val + (C v).val + 2 * k) % 2 = 1 % 2
  have hune : (C u).val ≠ (C v).val := fun he => hv ((Fin.ext he).symm.trans hu)
  have hu2 := (C u).isLt
  have hv2 := (C v).isLt
  omega

end Erdos642SideSampling

end Erdos642SideSamplingFile

section Erdos642DeterministicEndgameFile

/- Closing a long self-avoiding walk with enough edges in its support. -/

namespace Erdos642DeterministicEndgame

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- The edges supported on a walk, other than its own edges, are chords. -/
private theorem length_le_ncard_chords {w z : V} (c : G.Walk w z) (E : Finset (Sym2 V))
    (hAdj : ∀ e ∈ E, e ∈ G.edgeSet)
    (hSupport : ∀ e ∈ E, ∀ x ∈ e, x ∈ c.support)
    (hCount : 2 * c.length ≤ E.card) :
    c.length ≤ {e : Sym2 V | c.IsChord e}.ncard := by
  classical
  let R := E \ c.edges.toFinset
  have hR : (R : Set (Sym2 V)) ⊆ {e : Sym2 V | c.IsChord e} := by
    intro e he
    obtain ⟨hE, hC⟩ := Finset.mem_sdiff.mp (Finset.mem_coe.mp he)
    have he' : e ∉ c.edges := by simpa using hC
    induction e using Sym2.inductionOn with
    | hf a b =>
      exact Walk.isChord_sym2Mk.mpr
        ⟨hAdj _ hE, he', hSupport _ hE _ (Sym2.mem_mk_left _ _),
          hSupport _ hE _ (Sym2.mem_mk_right _ _)⟩
  have hfinite : {e : Sym2 V | c.IsChord e}.Finite := by
    refine c.support.toFinset.sym2.finite_toSet.subset ?_
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      have h := Walk.isChord_sym2Mk.mp he
      exact Finset.mk_mem_sym2_iff.mpr ⟨by simpa using h.2.2.1, by simpa using h.2.2.2⟩
  have hRCount : c.length ≤ R.card := by
    have hSplit := Finset.card_sdiff_add_card_inter E c.edges.toFinset
    have hInter : (E ∩ c.edges.toFinset).card ≤ c.length := by
      exact (Finset.card_le_card Finset.inter_subset_right).trans
        (c.edges.toFinset_card_le.trans_eq c.length_edges)
    change R.card + (E ∩ c.edges.toFinset).card = E.card at hSplit
    omega
  exact hRCount.trans (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hR hfinite)

/-- An endpoint edge closes a path of length at least two into a cycle. If the path
supports at least twice as many graph edges as the resulting cycle length, it
supplies a cycle with at least as many chords as vertices. -/
theorem close_path_with_many_edges (p : G.Walk u v) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) (hclose : G.Adj u v) (E : Finset (Sym2 V))
    (hAdj : ∀ e ∈ E, e ∈ G.edgeSet)
    (hSupport : ∀ e ∈ E, ∀ x ∈ e, x ∈ p.support)
    (hCount : 2 * (p.length + 1) ≤ E.card) :
    ¬ Erdos642.CyclesHaveMoreVerticesThanChords G := by
  let c : G.Walk v v := Walk.cons hclose.symm p
  have hCycle : c.IsCycle := (Walk.cons_isCycle_iff _ _).mpr
    ⟨hp, fun hEdge => by
      have he := hp.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hEdge)
      omega⟩
  have hlenC : c.length = p.length + 1 := p.length_cons hclose.symm
  have hChords := length_le_ncard_chords c E hAdj
    (fun e he x hx => List.mem_cons_of_mem _ (hSupport e he x hx)) (hlenC ▸ hCount)
  exact fun hG => (Nat.not_lt_of_ge hChords) (hG v c hCycle)

/-- The support between two visit times is retained by taking and dropping. This
allows the closing edge to lie outside the part of the walk that supplies the edges. -/
theorem close_subpath_with_many_edges (p : G.Walk u v) (hp : p.IsPath)
    {i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ p.length)
    (hclose : G.Adj (p.getVert i) (p.getVert j)) (E : Finset (Sym2 V))
    (hAdj : ∀ e ∈ E, e ∈ G.edgeSet)
    (hSupport : ∀ e ∈ E, ∀ x ∈ e, ∃ r : ℕ, i ≤ r ∧ r ≤ j ∧ p.getVert r = x)
    (hCount : 2 * (j - i + 1) ≤ E.card) :
    ¬ Erdos642.CyclesHaveMoreVerticesThanChords G := by
  let q := (p.drop i).take (j - i)
  have hEnd : (p.drop i).getVert (j - i) = p.getVert j := by
    rw [Walk.drop_getVert, Nat.add_sub_of_le (show i ≤ j by omega)]
  have hQ : q.IsPath := by
    exact Walk.isPath_of_isSubwalk (((p.drop i).isSubwalk_take (j - i)).trans
      (p.isSubwalk_drop i)) hp
  have hLen : q.length = j - i := by
    dsimp [q]
    rw [Walk.take_length, Walk.drop_length, inf_eq_left.mpr (Nat.sub_le_sub_right hj i)]
  have hqSupport : ∀ e ∈ E, ∀ x ∈ e, x ∈ q.support := by
    intro e he x hx
    obtain ⟨r, hir, hrj, hxr⟩ := hSupport e he x hx
    have hxq : q.getVert (r - i) = x := by
      dsimp [q]
      rw [Walk.take_getVert, inf_eq_right.mpr (Nat.sub_le_sub_right hrj i),
        Walk.drop_getVert, Nat.add_sub_of_le hir, hxr]
    exact hxq ▸ q.getVert_mem_support (r - i)
  exact close_path_with_many_edges q hQ (by omega)
    (hEnd.symm ▸ hclose) E hAdj hqSupport (by simpa only [hLen] using hCount)

/-- Edge families whose endpoints are sampled in different residue classes
are disjoint along a self-avoiding path. Their sum contributes to one cycle
whenever all the sample times lie between the endpoints of a closing edge. -/
theorem close_subpath_with_sampled_edge_families (p : G.Walk u v) (hp : p.IsPath)
    {i j a b stride : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ p.length)
    (hia : i ≤ a) (hbj : b ≤ j) (hclose : G.Adj (p.getVert i) (p.getVert j))
    (E : Fin stride → Finset (Sym2 V))
    (hAdj : ∀ r e, e ∈ E r → e ∈ G.edgeSet)
    (hSupport : ∀ r e, e ∈ E r → ∀ x ∈ e,
      ∃ t : ℕ, a ≤ t ∧ t ≤ b ∧ t % stride = r.val ∧ p.getVert t = x)
    (hCount : 2 * (j - i + 1) ≤ ∑ r, (E r).card) :
    ¬ Erdos642.CyclesHaveMoreVerticesThanChords G := by
  classical
  have hDisjoint : ((Finset.univ : Finset (Fin stride)) : Set (Fin stride)).PairwiseDisjoint E := by
    intro r _ s _ hrs
    apply Finset.disjoint_left.mpr
    intro e hEr hEs
    induction e using Sym2.inductionOn with
    | hf x y =>
      obtain ⟨t, _, htb, htr, htx⟩ := hSupport r _ hEr x (Sym2.mem_mk_left _ _)
      obtain ⟨w, _, hwb, hws, hwx⟩ := hSupport s _ hEs x (Sym2.mem_mk_left _ _)
      have htw := hp.getVert_injOn (htb.trans (hbj.trans hj)) (hwb.trans (hbj.trans hj))
        (htx.trans hwx.symm)
      exact hrs (Fin.ext (htr.symm.trans (htw ▸ hws)))
  let F := Finset.univ.biUnion E
  refine close_subpath_with_many_edges p hp hij hj hclose F ?_ ?_ ?_
  · intro e he
    obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp he
    exact hAdj r e hr
  · intro e he x hx
    obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp he
    obtain ⟨t, hat, htb, _, htx⟩ := hSupport r e hr x hx
    exact ⟨t, hia.trans hat, htb.trans hbj, htx⟩
  · simpa only [F, Finset.card_biUnion hDisjoint] using hCount

end Erdos642DeterministicEndgame

end Erdos642DeterministicEndgameFile

section Erdos642TraceEndgameFile

/- Turn a finite sequence of distinct visits into the path used in the chord argument. -/

namespace Erdos642TraceEndgame

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {t : ℕ}

/-- A sequence of graph-adjacent visits is realized by a walk with the same indices. -/
theorem exists_walk_of_visits (x : Fin (t + 1) → V)
    (hstep : ∀ i : Fin t, G.Adj (x i.castSucc) (x i.succ)) :
    ∃ u v, ∃ w : G.Walk u v, w.length = t ∧ ∀ i : Fin (t + 1), w.getVert i = x i := by
  let l := List.ofFn x
  have hlen : l.length = t + 1 := List.length_ofFn
  have hn : l ≠ [] := by
    intro he
    simp [he] at hlen
  have hc : l.IsChain G.Adj := List.isChain_ofFn.mpr (fun i hi => hstep ⟨i, by omega⟩)
  let w := Walk.ofSupport l hn hc
  have hw : w.length = t := by simp [w, hlen]
  refine ⟨_, _, w, hw, fun i => ?_⟩
  rw [w.getVert_eq_support_getElem (by simpa only [hw] using Nat.le_of_lt_succ i.isLt)]
  have he : w.support = l := Walk.support_ofSupport hn hc
  simp only [he, l, List.getElem_ofFn, Fin.eta]

/-- The trace version of the closing-edge argument keeps the same sample indices. -/
theorem close_visits_with_sampled_edges (x : Fin (t + 1) → V)
    (hstep : ∀ i : Fin t, G.Adj (x i.castSucc) (x i.succ))
    (hinj : Function.Injective x) {i j : Fin (t + 1)} {a b stride : ℕ}
    (hij : i.val + 2 ≤ j.val) (hia : i.val ≤ a) (hbj : b ≤ j.val)
    (hclose : G.Adj (x i) (x j)) (E : Fin stride → Finset (Sym2 V))
    (hAdj : ∀ r e, e ∈ E r → e ∈ G.edgeSet)
    (hSupport : ∀ r e, e ∈ E r → ∀ v ∈ e,
      ∃ k : Fin (t + 1), a ≤ k.val ∧ k.val ≤ b ∧ k.val % stride = r.val ∧ x k = v)
    (hCount : 2 * (j.val - i.val + 1) ≤ ∑ r, (E r).card) :
    ¬ Erdos642.CyclesHaveMoreVerticesThanChords G := by
  obtain ⟨u, v, w, hw, hget⟩ := exists_walk_of_visits x hstep
  have hp : w.IsPath := Walk.IsPath.getVert_injOn_iff w |>.mp (by
    intro e he f hf hef
    replace he : e ≤ t := by simpa only [Set.mem_ofPred_eq, hw] using he
    replace hf : f ≤ t := by simpa only [Set.mem_ofPred_eq, hw] using hf
    exact congrArg Fin.val (hinj ((hget ⟨e, by omega⟩).symm.trans (hef.trans (hget ⟨f, by omega⟩)))))
  refine Erdos642DeterministicEndgame.close_subpath_with_sampled_edge_families w hp
    hij (by simpa only [hw] using Nat.le_of_lt_succ j.isLt) hia hbj
    (by simpa only [hget i, hget j] using hclose) E hAdj ?_ hCount
  intro r e he y hy
  obtain ⟨k, hka, hkb, hkr, hky⟩ := hSupport r e he y hy
  exact ⟨k, hka, hkb, hkr, (hget k).trans hky⟩

/-- Closing visits in the outer quarters enclose all of the sampled middle edges. -/
theorem close_visits_in_quarters (x : Fin (t + 1) → V)
    (hstep : ∀ i : Fin t, G.Adj (x i.castSucc) (x i.succ))
    (hinj : Function.Injective x) (ht : 4 ≤ t) {i j : Fin (t + 1)} {stride : ℕ}
    (hstride : 0 < stride) (hi : i.val ≤ t / 4) (hj : 3 * (t / 4) ≤ j.val)
    (hclose : G.Adj (x i) (x j)) (E : Fin stride → Finset (Sym2 V))
    (hAdj : ∀ r e, e ∈ E r → e ∈ G.edgeSet)
    (hSupport : ∀ r e, e ∈ E r → ∀ v ∈ e,
      ∃ k : Fin (t + 1), t / 4 ≤ k.val ∧ k.val ≤ 3 * (t / 4) ∧
        k.val % stride = r.val ∧ x k = v)
    (hCount : ∀ r, 2 * ((t : ℝ) + 1) / stride ≤ ((E r).card : ℝ)) :
    ¬ Erdos642.CyclesHaveMoreVerticesThanChords G := by
  refine close_visits_with_sampled_edges x hstep hinj (i := i) (j := j)
    (a := t / 4) (b := 3 * (t / 4)) (by omega) hi hj hclose E hAdj hSupport ?_
  have hstride' : 0 < (stride : ℝ) := by exact_mod_cast hstride
  have hTotal : 2 * ((t : ℝ) + 1) ≤ ∑ r, ((E r).card : ℝ) := calc
    _ = ∑ _r : Fin stride, 2 * ((t : ℝ) + 1) / stride := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    _ ≤ _ := Finset.sum_le_sum fun r _ => hCount r
  have hNat : 2 * (t + 1) ≤ ∑ r, (E r).card := by exact_mod_cast hTotal
  have hjt : j.val ≤ t := by omega
  exact (Nat.mul_le_mul_left 2 (by omega : j.val - i.val + 1 ≤ t + 1)).trans hNat

end Erdos642TraceEndgame

end Erdos642TraceEndgameFile

section Erdos642TraceConclusionFile

/- A common trace with survival, a closing edge, and enough sampled edges. -/

namespace Erdos642TraceConclusion

open SimpleGraph Finset Erdos642WalkTrace Erdos642RandomWalkKernel

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def closesInQuarters (G : SimpleGraph V) (x : Fin (t + 1) → V) : Prop :=
  ∃ i j : Fin (t + 1), i.val ≤ t / 4 ∧ 3 * (t / 4) ≤ j.val ∧ G.Adj (x i) (x j)

def hasSampledEdges (G : SimpleGraph V) (x : Fin (t + 1) → V)
    {k : ℕ} (r : Fin k) : Prop :=
  ∃ E : Finset (Sym2 V),
    (∀ e ∈ E, e ∈ G.edgeSet) ∧
    (∀ e ∈ E, ∀ v ∈ e, ∃ i : Fin (t + 1), t / 4 ≤ i.val ∧ i.val ≤ 3 * (t / 4) ∧
      i.val % k = r.val ∧ x i = v) ∧
    2 * ((t : ℝ) + 1) / k ≤ ((E.card : ℕ) : ℝ)

/-- If each of the two kinds of closure failure has total mass below survival,
there is a path whose middle edges give a cycle with at least as many chords as vertices. -/
theorem contradict_of_trace_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {k : ℕ} (hk : 0 < k) (ht : 4 ≤ t)
    {L ε : ℝ}
    (hSurv : L ≤ Erdos642ShortAvoidance.survivingMass (step G) t {v} v)
    (hClose : eventMass (step G) t v (fun p => ¬ closesInQuarters G (Fin.cons v p)) ≤ ε)
    (hMid : ∀ r : Fin k,
      eventMass (step G) t v (fun p => ¬ hasSampledEdges G (Fin.cons v p) r) ≤ ε)
    (hChance : 0 < L - ε - (k : ℝ) * ε) :
    ¬ Erdos642.CyclesHaveMoreVerticesThanChords G := by
  classical
  let P : (Fin t → V) → Prop := survives {v}
  let Q : (Fin t → V) → Prop := fun p => closesInQuarters G (Fin.cons v p)
  let R : (Fin t → V) → Prop := fun p => ∀ r : Fin k, hasSampledEdges G (Fin.cons v p) r
  have hLower : L ≤ eventMass (step G) t v P := by
    simpa only [P, eventMass_survives] using hSurv
  have hQ : eventMass (step G) t v (fun p => ¬ Q p) ≤ ε := hClose
  have hR : eventMass (step G) t v (fun p => ¬ R p) ≤ (k : ℝ) * ε := by
    calc
      _ ≤ ∑ r : Fin k,
          eventMass (step G) t v (fun p => ¬ hasSampledEdges G (Fin.cons v p) r) := by
        simpa only [R, not_forall, Finset.mem_univ, true_and] using
          eventMass_union_le (step G) (step_nonneg G) t v (univ : Finset (Fin k))
            (fun r p => ¬ hasSampledEdges G (Fin.cons v p) r)
      _ ≤ ∑ _r : Fin k, ε := sum_le_sum fun r _ => hMid r
      _ = _ := by simp [nsmul_eq_mul]
  have hTwo := eventMass_and_ge_sub (step G) (step_nonneg G) t v P Q
  have hThree := eventMass_and_ge_sub (step G) (step_nonneg G) t v (fun p => P p ∧ Q p) R
  have hPos : 0 < eventMass (step G) t v (fun p => (P p ∧ Q p) ∧ R p) := by
    linarith only [hLower, hQ, hR, hTwo, hThree, hChance]
  obtain ⟨p, ⟨⟨hp, hq⟩, hr⟩, hWeight⟩ :=
    exists_trace_of_eventMass_pos (step G) (step_nonneg G) t v _ hPos
  obtain ⟨i, j, hi, hj, hCloseEdge⟩ := hq
  choose E hE using (show ∀ r : Fin k, hasSampledEdges G (Fin.cons v p) r from hr)
  have hAdj := (traceWeight_pos_iff (step G) (step_nonneg G) t v p).mp hWeight
  exact Erdos642TraceEndgame.close_visits_in_quarters (Fin.cons v p)
    (fun q => (step_pos_iff_adj G _ _).mp (hAdj q)) ((survives_singleton_iff v p).mp hp)
    ht hk hi hj hCloseEdge E (fun r => (hE r).1) (fun r => (hE r).2.1) (fun r => (hE r).2.2)

end Erdos642TraceConclusion

end Erdos642TraceConclusionFile

section Erdos642BankProbabilityFile

/- Raw trace forms of the two sampling estimates and their cross-edge support. -/

namespace Erdos642BankProbability

open Finset SimpleGraph
open Erdos642WalkTrace Erdos642TraceStride Erdos642TraceWindows
open Erdos642StarForest Erdos642ManyForestsSampling Erdos642RandomWalkKernel
open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- The vertices of the designated side seen at stride endpoints. -/
def bankSeen (stride N : ℕ) (hs : 0 < stride) (B : Finset V)
    (p : Fin (N*stride) → V) : Finset V :=
  univ.image (samples stride N hs p) ∩ B

/-- A family is weak on the bank if some forest has fewer than half good stars. -/
def weakForests (J : Finset I) (P : I → Finset (V × Finset V))
    (S : Finset V) (R : ℝ) : Prop :=
  ∃ i ∈ J, 2 * ((P i).filter fun p => R ≤ ((p.2 ∩ S).card : ℝ)).card < (P i).card

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The first-bank estimate transferred to the same raw trace law as the final event. -/
theorem first_bank_failure (hPos : ∀ v, 0 < G.degree v) (stride : ℕ) (hs : 0 < stride)
    {E : Finset (V × V)} {A B : Finset V} {ell : ℕ}
    (J : Finset I) (P : I → Finset (V × Finset V)) (hP : ∀ i ∈ J, IsPacking E A B ell (P i))
    (a : ℝ) (hCard : ∀ i ∈ J, a ≤ ((P i).card : ℝ))
    (N : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρB : ρ * (B.card : ℝ) ≤ 1)
    (hClosed : ∀ u v, u ∈ B → v ∉ B → walkWeight G stride u v = 0)
    (hpoint : ∀ u v, u ∈ B → v ∈ B → ρ ≤ walkWeight G stride u v)
    (hN : (N : ℝ) * ρ ≤ 4) (hScale : 4 ≤ (ell : ℝ) * ((N : ℝ) * ρ / 8))
    (x : V) (hx : x ∈ B) :
    let R := (ell : ℝ) * ((N : ℝ) * ρ / 8)
    eventMass (step G) (N*stride) x (fun p => weakForests J P (bankSeen stride N hs B p) R)
      ≤ (J.card : ℝ) * Real.exp (-(a * R / 4)) := by
  dsimp only
  let R := (ell : ℝ) * ((N : ℝ) * ρ / 8)
  let F (z : V × Finset V) := weakForests J P z.2 R
  have hEq := Erdos642TraceSeen.graph_eventMass_sample_seen_eq G stride hs N 0 x B ∅ F
  have h := Erdos642SideSampling.all_forests_lower_tail_on_side (fun _ => walkWeight G stride)
    J P hP a hCard N ρ hρ hρB (stochasticThrough G hPos _ N)
    (fun _ => hClosed) (fun _ _ => hpoint) hN hScale x hx
  have h' := hEq.trans_le h
  simp only [R, F, empty_union, weakForests] at h'
  simp only [bankSeen, weakForests]
  convert h' using 2
  funext p
  apply propext
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply Iff.of_eq
  congr 3

/-- The second-bank root-hit estimate transferred to the raw trace law. -/
theorem second_bank_failure (hPos : ∀ v, 0 < G.degree v) (stride : ℕ) (hs' : 0 < stride)
    {R B : Finset V} (hRB : R ⊆ B) (N : ℕ) (s p ρ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hρ : 0 ≤ ρ)
    (hClosed : ∀ u v, u ∈ B → v ∉ B → walkWeight G stride u v = 0)
    (hpoint : ∀ u v, u ∈ B → v ∈ R → ρ ≤ walkWeight G stride u v)
    (hbudget : p ≤ ρ * ((R.card : ℝ) - s))
    (hs : s ≤ (N : ℝ) * p / 4) (x : V) (hx : x ∈ B) :
    eventMass (step G) (N*stride) x (fun q => ((R ∩ bankSeen stride N hs' B q).card : ℝ) ≤ s)
      ≤ Real.exp (-s) := by
  let F (z : V × Finset V) := ((R ∩ z.2).card : ℝ) ≤ s
  have hEq := Erdos642TraceSeen.graph_eventMass_sample_seen_eq G stride hs' N 0 x B ∅ F
  have h := Erdos642SideSampling.eventMass_seen_inter_le_exp_on_side
    (fun _ => walkWeight G stride) hRB N s p ρ hp0 hp1 hρ (stochasticThrough G hPos _ N)
    (fun _ => hClosed) (fun _ _ => hpoint) hbudget hs x hx
  simpa only [bankSeen, F, empty_union] using hEq.trans_le h

omit [Fintype V] in
/-- Roots recovered from the first bank lie in the prescribed root side. -/
theorem goodRoots_subset {E : Finset (V × V)} {A B : Finset V} {ell : ℕ}
    (J : Finset I) (P : I → Finset (V × Finset V)) (hP : ∀ i ∈ J, IsPacking E A B ell (P i))
    (S : Finset V) (R : ℝ) :
    goodRoots J P S R ⊆ A := by
  intro u hu
  obtain ⟨i, hi, p, hp, _, rfl⟩ := mem_goodRoots.mp hu
  exact ((hP i hi).1 p hp).1

omit [Fintype V] in
theorem goodRoots_lower {E : Finset (V × V)} {A B : Finset V} {ell : ℕ}
    (J : Finset I) (P : I → Finset (V × Finset V)) (hP : ∀ i ∈ J, IsPacking E A B ell (P i))
    (hDisj : (J : Set I).PairwiseDisjoint (fun i => (P i).image Prod.fst))
    (S : Finset V) (R a : ℝ) (hCard : ∀ i ∈ J, a ≤ ((P i).card : ℝ))
    (hGood : ¬ weakForests J P S R) :
    ((J.card : ℝ) * a) / 2 ≤ (goodRoots J P S R).card := by
  rw [card_goodRoots J P hP hDisj S R, Nat.cast_sum, div_le_iff₀ (by norm_num), mul_comm]
  calc
    _ = ∑ i ∈ J, a := by simp [mul_comm]
    _ ≤ ∑ i ∈ J, 2 * ((((P i).filter fun p => R ≤ ((p.2 ∩ S).card : ℝ)).card : ℝ)) := by
      apply sum_le_sum
      intro i hi
      apply (hCard i hi).trans
      exact_mod_cast (Nat.le_of_not_gt fun hlt => hGood ⟨i,hi,hlt⟩)
    _ = _ := by rw [mul_comm _ (2 : ℝ), Finset.mul_sum]

/-- Cross-edges are stored as unoriented graph edges. -/
def crossEdges (R S : Finset V) : Finset (Sym2 V) :=
  ((R ×ˢ S).filter fun e : V × V => G.Adj e.1 e.2).image (fun e => s(e.1,e.2))

omit [Fintype V] in theorem mem_crossEdges (R S : Finset V) {e : Sym2 V} :
    e ∈ crossEdges G R S ↔ ∃ u ∈ R, ∃ v ∈ S, G.Adj u v ∧ e = s(u,v) := by
  constructor
  · intro h
    obtain ⟨⟨u,v⟩, hp, rfl⟩ := mem_image.mp h
    obtain ⟨hp, hEdge⟩ := mem_filter.mp hp
    obtain ⟨hu, hv⟩ := mem_product.mp hp
    exact ⟨u, hu, v, hv, hEdge, rfl⟩
  · rintro ⟨u, hu, v, hv, he, rfl⟩
    exact mem_image.mpr ⟨(u,v), mem_filter.mpr ⟨mem_product.mpr ⟨hu,hv⟩,he⟩,rfl⟩

omit [Fintype V] in theorem crossEdges_support (R S : Finset V) {e : Sym2 V}
    (he : e ∈ crossEdges G R S) :
    e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ R ∨ v ∈ S := by
  obtain ⟨u, hu, v, hv, hEdge, rfl⟩ := (mem_crossEdges G R S).mp he
  refine ⟨G.mem_edgeSet.mpr hEdge, ?_⟩
  intro w hw
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · exact Or.inl hu
  · exact Or.inr hv

omit [Fintype V] in theorem card_crossEdges (R S : Finset V) (hDisj : Disjoint R S) :
    (crossEdges G R S).card = ∑ u ∈ R, (S.filter fun v => G.Adj u v).card := by
  classical
  let F := (R ×ˢ S).filter (fun e : V×V => G.Adj e.1 e.2)
  have hinj : Set.InjOn (fun e : V × V => s(e.1,e.2)) (F : Set (V×V)) := by
    rintro ⟨u,v⟩ hu ⟨w,z⟩ hv he
    change s(u,v) = s(w,z) at he
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · have hu' := mem_product.mp (mem_filter.mp hu).1
      have hv' := mem_product.mp (mem_filter.mp hv).1
      exact (Finset.disjoint_left.mp hDisj hu'.1 hv'.2).elim
  change (F.image (fun e : V × V => s(e.1,e.2))).card = _
  rw [card_image_of_injOn hinj]
  calc
    F.card = ∑ e ∈ F, (1 : ℕ) := by simp
    _ = ∑ e ∈ R ×ˢ S, if G.Adj e.1 e.2 then (1 : ℕ) else 0 := by
      dsimp only [F]
      rw [sum_filter]
    _ = _ := by
      rw [sum_product]
      apply sum_congr rfl
      intro u _
      rw [← sum_filter]
      simp

omit [Fintype V] in
/-- Each recovered and resampled root contributes its threshold of distinct
edges to the first-bank vertices. -/
theorem goodRoots_crossEdges_lower {E : Finset (V × V)} {A B : Finset V} {ell : ℕ}
    (hDisj : Disjoint A B) (hE : ∀ e ∈ E, G.Adj e.1 e.2)
    (J : Finset I) (P : I → Finset (V × Finset V)) (hP : ∀ i ∈ J, IsPacking E A B ell (P i))
    (S T : Finset V) (hS : S ⊆ B) (R : ℝ) :
    (((goodRoots J P S R) ∩ T).card : ℝ) * R ≤
      ((crossEdges G ((goodRoots J P S R) ∩ T) S).card : ℝ) := by
  let Q := (goodRoots J P S R) ∩ T
  have hQ : Q ⊆ A := inter_subset_left.trans (goodRoots_subset J P hP S R)
  have hDisj' : Disjoint Q S :=
    Finset.disjoint_of_subset_left hQ (Finset.disjoint_of_subset_right hS hDisj)
  have hLeaves (u : V) (hu : u ∈ Q) : R ≤ ((S.filter fun v => G.Adj u v).card : ℝ) := by
    obtain ⟨i, hi, p, hp, hCount, rfl⟩ := mem_goodRoots.mp (mem_inter.mp hu).1
    have hRel : p.2 ∩ S ⊆ S.filter fun v => G.Adj p.1 v := by
      intro v hv
      exact mem_filter.mpr ⟨(mem_inter.mp hv).2,
        hE (p.1,v) (((hP i hi).1 p hp).2.2.2 v (mem_inter.mp hv).1)⟩
    exact hCount.trans (by exact_mod_cast card_le_card hRel)
  change (Q.card : ℝ) * R ≤ ((crossEdges G Q S).card : ℝ)
  rw [card_crossEdges G Q S hDisj', Nat.cast_sum]
  calc
    _ = ∑ _u ∈ Q, R := by simp
    _ ≤ _ := sum_le_sum hLeaves

omit [Fintype V] in
/-- Every recorded sample is realized at its exact physical time in the full visit tuple. -/
theorem bankSeen_visit_time {t a stride N : ℕ} (hs : 0 < stride) (hWindow : a+N*stride ≤ t)
    (x : V) (p : Fin t → V) (B : Finset V) {u : V}
    (hu : u ∈ bankSeen stride N hs B (sliceTrace t a (N*stride) hWindow p)) :
    ∃ j : Fin N, ∃ i : Fin (t+1),
      i.val = a + (j.val+1)*stride ∧ (Fin.cons x p : Fin (t+1) → V) i = u := by
  obtain ⟨j, -, hj⟩ := mem_image.mp (mem_inter.mp hu).1
  let raw : Fin t := ⟨a+(sampleIndex stride N hs j).val, by
    have h := (sampleIndex stride N hs j).isLt
    omega⟩
  have hz : 0 < (j.val+1)*stride := Nat.mul_pos (Nat.succ_pos _) hs
  refine ⟨j, raw.succ, ?_, ?_⟩
  · simp only [raw, Fin.val_succ, sampleIndex]
    omega
  · rw [Fin.cons_succ]
    exact hj

omit [Fintype V] in
theorem bankSeen_time_bounds {t a stride N L U : ℕ} (hs : 0 < stride)
    (hWindow : a+N*stride ≤ t) (hL : L ≤ a) (hU : a+N*stride ≤ U)
    (x : V) (p : Fin t → V) (B : Finset V) {u : V}
    (hu : u ∈ bankSeen stride N hs B (sliceTrace t a (N*stride) hWindow p)) :
    ∃ j : Fin N, ∃ i : Fin (t+1), L ≤ i.val ∧ i.val ≤ U ∧
      i.val = a + (j.val+1)*stride ∧ (Fin.cons x p : Fin (t+1) → V) i = u := by
  obtain ⟨j,i,hi,hvisit⟩ := bankSeen_visit_time hs hWindow x p B hu
  have hMul : (j.val+1)*stride ≤ N*stride :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt)
  exact ⟨j,i,by omega,by omega,hi,hvisit⟩

omit [Fintype V] in
theorem bankSeen_visit_mod {t a k N L U : ℕ} (hk : 0 < k)
    (hWindow : a+N*(2*k) ≤ t) (hL : L ≤ a) (hU : a+N*(2*k) ≤ U)
    (x : V) (p : Fin t → V) (B : Finset V) {u : V}
    (hu : u ∈ bankSeen (2*k) N (by omega) B (sliceTrace t a (N*(2*k)) hWindow p)) :
    ∃ i : Fin (t+1), L ≤ i.val ∧ i.val ≤ U ∧ i.val % k = a % k ∧
      (Fin.cons x p : Fin (t+1) → V) i = u := by
  obtain ⟨j,i,hiL,hiU,hi,hvisit⟩ := bankSeen_time_bounds (by omega) hWindow hL hU x p B hu
  refine ⟨i, hiL, hiU, ?_, hvisit⟩
  rw [hi, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]

omit [Fintype V] [DecidableRel G.Adj] in
/-- A single edge across the designated quarter banks closes the middle path. -/
theorem closes_of_banks_adj {t a b stride N : ℕ} (hs : 0 < stride)
    (ha : a+N*stride ≤ t) (hb : b+N*stride ≤ t)
    (haQ : a+N*stride ≤ t/4) (hbQ : 3*(t/4) ≤ b)
    (x : V) (p : Fin t → V) (A B : Finset V) {u v : V}
    (hu : u ∈ bankSeen stride N hs A (sliceTrace t a (N*stride) ha p))
    (hv : v ∈ bankSeen stride N hs B (sliceTrace t b (N*stride) hb p))
    (he : G.Adj u v) :
    Erdos642TraceConclusion.closesInQuarters G (Fin.cons x p) := by
  obtain ⟨_,i,_,hi,_,hui⟩ := bankSeen_time_bounds hs ha (Nat.zero_le _) haQ x p A hu
  obtain ⟨_,j,hj,_,_,hvj⟩ := bankSeen_time_bounds hs hb hbQ hb x p B hv
  exact ⟨i,j,hi,hj,by simpa only [hui,hvj] using he⟩

omit [Fintype V] in
/-- Two middle banks from one residue class certify the exact sampled-edge event. -/
theorem sampledEdges_of_banks {t a b k N : ℕ} (hk : 0 < k) (r : Fin k)
    (ha : a+N*(2*k) ≤ t) (hb : b+N*(2*k) ≤ t)
    (haL : t/4 ≤ a) (hbL : t/4 ≤ b)
    (haU : a+N*(2*k) ≤ 3*(t/4)) (hbU : b+N*(2*k) ≤ 3*(t/4))
    (haR : a % k = r.val) (hbR : b % k = r.val)
    (x : V) (p : Fin t → V) (A B R : Finset V)
    (hCount : 2 * ((t : ℝ) + 1) / (k : ℝ) ≤
      ((crossEdges G
        (R ∩ bankSeen (2*k) N (by omega) A (sliceTrace t b (N*(2*k)) hb p))
        (bankSeen (2*k) N (by omega) B (sliceTrace t a (N*(2*k)) ha p))).card : ℝ)) :
    Erdos642TraceConclusion.hasSampledEdges G (Fin.cons x p) r := by
  refine ⟨_, fun e he => (crossEdges_support G _ _ he).1, ?_, hCount⟩
  intro e he v hv
  rcases (crossEdges_support G _ _ he).2 v hv with hR | hB
  · simpa only [hbR] using bankSeen_visit_mod hk hb hbL hbU x p A (mem_inter.mp hR).2
  · simpa only [haR] using bankSeen_visit_mod hk ha haL haU x p B hB

end Erdos642BankProbability

end Erdos642BankProbabilityFile

section Erdos642BankWindowsFile

/- Conditional sampling on two separated windows of one finite walk. -/

namespace Erdos642BankWindows

open Erdos642WalkTrace Erdos642TraceWindows

variable {V : Type*} [Fintype V]

theorem eventMass_mono (K : V → V → ℝ) (hK : ∀ u v, 0 ≤ K u v) (n : ℕ) (x : V)
    {P Q : (Fin n → V) → Prop} (hPQ : ∀ q, P q → Q q) :
    eventMass K n x P ≤ eventMass K n x Q := by
  classical
  unfold eventMass
  apply Finset.sum_le_sum
  intro q _
  by_cases hp : P q
  · simp only [hp, hPQ q hp, if_true, le_refl]
  · simpa only [hp, if_false] using
      (show 0 ≤ if Q q then traceWeight K n x q else 0 from by
        split <;> [exact traceWeight_nonneg K hK n x q; exact le_refl 0])

/-- The starting state may choose the first-bank test. A good first bank lets
one condition on any positive-mass continuation to the second bank. -/
theorem two_banks_failure_le (K : V → V → ℝ) (hK : ∀ u v, 0 ≤ K u v)
    (hRow : ∀ v, ∑ u, K v u = 1) (len gap : ℕ) (x : V)
    (good : (Fin len → V) → Prop) (bad : (Fin len → V) → (Fin len → V) → Prop)
    {ε₁ ε₂ : ℝ} (hε₂ : 0 ≤ ε₂)
    (hFirst : eventMass K len x (fun p => ¬ good p) ≤ ε₁)
    (hSecond : ∀ p : Fin (gap+len) → V,
      0 < traceWeight K (gap+len) x p → good (front len gap p) →
      eventMass K len (finish (gap+len) x p) (bad (front len gap p)) ≤ ε₂) :
    eventMass K (len+(gap+len)) x
      (fun p => bad (front len gap (front (gap+len) len p)) (back (gap+len) len p)) ≤
      ε₁+ε₂ := by
  let P (p : Fin (gap+len) → V) := good (front len gap p)
  let Q (p : Fin (len+(gap+len)) → V) :=
    bad (front len gap (front (gap+len) len p)) (back (gap+len) len p)
  have hBound (p : Fin (gap+len) → V) (hp : 0 < traceWeight K (gap+len) x p)
      (hg : P p) :
      eventMass K len (finish (gap+len) x p)
        (fun q => Q (appendTrace len (gap+len) p q)) ≤ ε₂ := by
    simpa only [Q, front_appendTrace, back_appendTrace] using hSecond p hp hg
  have h := eventMass_two_stage_le K hK hRow (gap+len) len x P Q hε₂ hBound
  have h0 : eventMass K (gap+len) x (fun p => ¬ P p) ≤ ε₁ := by
    exact (eventMass_front_eq K hRow len gap x (fun p => ¬ good p)).trans_le hFirst
  exact h.trans (add_le_add h0 le_rfl)

/-- Uniform bad-event bounds for two banks transfer to arbitrary separated
windows of the full walk. -/
theorem two_windows_failure_le (K : V → V → ℝ) (hK : ∀ u v, 0 ≤ K u v)
    (hRow : ∀ v, ∑ u, K v u = 1) (t a len gap : ℕ)
    (hWindow : a+(len+(gap+len)) ≤ t) (x : V)
    (bad : (Fin len → V) → (Fin len → V) → Prop) (good : V → (Fin len → V) → Prop)
    {ε₁ ε₂ : ℝ} (hε₂ : 0 ≤ ε₂)
    (hFirst : ∀ y, eventMass K len y (fun p => ¬ good y p) ≤ ε₁)
    (hSecond : ∀ y, ∀ p : Fin (gap+len) → V,
      0 < traceWeight K (gap+len) y p → good y (front len gap p) →
      eventMass K len (finish (gap+len) y p) (bad (front len gap p)) ≤ ε₂) :
    eventMass K t x (fun p =>
      bad (sliceTrace t a len (by omega) p) (sliceTrace t (a+len+gap) len (by omega) p)) ≤
        ε₁+ε₂ := by
  let P (p : Fin (len+(gap+len)) → V) :=
    bad (front len gap (front (gap+len) len p)) (back (gap+len) len p)
  have hLocal (y : V) : eventMass K (len+(gap+len)) y P ≤ ε₁+ε₂ :=
    two_banks_failure_le K hK hRow len gap y (good y) bad hε₂ (hFirst y) (hSecond y)
  have h := eventMass_slice_le K hK hRow t a (len+(gap+len)) hWindow x P hLocal
  have hFirstSlice (p : Fin t → V) :
      front len gap (front (gap+len) len (sliceTrace t a (len+(gap+len)) hWindow p)) =
        sliceTrace t a len (by omega) p := by
    funext i
    rfl
  have hSecondSlice (p : Fin t → V) :
      back (gap+len) len (sliceTrace t a (len+(gap+len)) hWindow p) =
        sliceTrace t (a+len+gap) len (by omega) p := by
    funext i
    apply congrArg p
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_natAdd]
    omega
  simpa only [P,hFirstSlice,hSecondSlice] using h

end Erdos642BankWindows

end Erdos642BankWindowsFile

section Erdos642DegreeBudgetFile

/- Edge budgets for vertex removal and fixed minimum degree. -/

namespace Erdos642DegreeBudget

open Finset SimpleGraph Erdos642InducedCounts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Removing a set of vertices costs at most the sum of their degree bounds. -/
theorem remove_vertices_budget (A R : Finset V) (hRA : R ⊆ A) {d : ℕ}
    (hD : ∀ v ∈ R, G.degree v ≤ d) :
    (Erdos642InducedCounts.internalEdges G A).card ≤ (Erdos642InducedCounts.internalEdges G (A \ R)).card + R.card * d := by
  classical
  induction R using Finset.induction_on generalizing A with
  | empty => simp
  | @insert v R hv ih =>
    have hvA : v ∈ A := hRA (mem_insert_self _ _)
    have hR' : R ⊆ A.erase v := by
      intro x hx
      refine mem_erase.mpr ⟨?_,hRA (mem_insert_of_mem hx)⟩
      exact fun h => hv (h ▸ hx)
    have hEq : A \ insert v R = A.erase v \ R := by
      ext x
      simp only [mem_sdiff,mem_insert,not_or,mem_erase]
      tauto
    have hbound := ih (A.erase v) hR' (fun x hx => hD x (mem_insert_of_mem hx))
    have hvD := (degree_within_le G A v).trans (hD v (mem_insert_self _ _))
    rw [card_internalEdges_erase G hvA,hEq,card_insert_of_notMem hv,Nat.add_mul,one_mul]
    omega

/-- Iteratively deleting vertices of degree below `d` loses at most
`d` edges for each removed vertex. -/
theorem trim_with_budget (A : Finset V) (d : ℕ) :
    ∃ S ⊆ A, (Erdos642InducedCounts.internalEdges G A).card ≤ (Erdos642InducedCounts.internalEdges G S).card + (A.card - S.card) * d ∧
      ∀ v ∈ S, d ≤ degreeWithin G S v := by
  classical
  let C := A.powerset.filter fun S =>
    (Erdos642InducedCounts.internalEdges G A).card ≤ (Erdos642InducedCounts.internalEdges G S).card + (A.card - S.card) * d
  have hAC : A ∈ C := by simp [C]
  obtain ⟨S,hS,hMin⟩ := exists_min_image C Finset.card ⟨A,hAC⟩
  obtain ⟨hSA,hBudget⟩ := mem_filter.mp hS
  have hSA' := mem_powerset.mp hSA
  refine ⟨S,hSA',hBudget,?_⟩
  intro v hv
  by_contra! hSmall
  let T := S.erase v
  have hTc : T.card = S.card - 1 := card_erase_of_mem hv
  have hPos := card_pos.mpr (show S.Nonempty from ⟨v,hv⟩)
  have hIn := card_le_card hSA'
  have hTc' : A.card - T.card = (A.card - S.card) + 1 := by omega
  have hE : (Erdos642InducedCounts.internalEdges G S).card = (Erdos642InducedCounts.internalEdges G T).card + degreeWithin G S v :=
    card_internalEdges_erase G hv
  have hNew : (Erdos642InducedCounts.internalEdges G A).card ≤ (Erdos642InducedCounts.internalEdges G T).card + (A.card - T.card) * d := by
    rw [hTc',Nat.add_mul,one_mul]
    omega
  have hTC : T ∈ C := mem_filter.mpr
    ⟨mem_powerset.mpr ((erase_subset v S).trans hSA'),hNew⟩
  have hSm := hMin T hTC
  omega

end Erdos642DegreeBudget

end Erdos642DegreeBudgetFile

section Erdos642ForestSizesFile

/- Numerical estimates for repeated star-forest extraction. -/

namespace Erdos642ForestSizes

theorem roots_budget {n d R : ℕ} (hR : R ≤ (d / 10) * (n / (100000 * d))) :
    1000000 * R ≤ n := by
  have hd : (d / 10) * 10 ≤ d := Nat.div_mul_le_self d 10
  calc
    _ ≤ 1000000 * ((d / 10) * (n / (100000 * d))) := Nat.mul_le_mul_left _ hR
    _ = (100000 * ((d / 10) * 10)) * (n / (100000 * d)) := by ring
    _ ≤ (100000 * d) * (n / (100000 * d)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd)
    _ = (n / (100000 * d)) * (100000 * d) := Nat.mul_comm _ _
    _ ≤ n := Nat.div_mul_le_self _ _

/-- A small root deletion followed by the minimum-degree trim leaves a
slice with at least one two-hundred-fiftieth of the vertices. -/
theorem slice_size_after_trim {n d R m e₀ e₁ e₂ : ℕ}
    (hd : 0 < d) (hStart : n * d ≤ 2 * e₀) (hRoots : 1000000 * R ≤ n)
    (hRemove : e₀ ≤ e₁ + R * (100 * d)) (hTrim : e₁ ≤ e₂ + n * (d / 4))
    (hMax : 2 * e₂ ≤ m * (100 * d)) : n ≤ 250 * m := by
  have hLoss₁ : 10000 * (R * (100 * d)) ≤ n * d := by
    calc
      _ = (1000000 * R) * d := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hRoots
  have hLoss₂ : 4 * (n * (d / 4)) ≤ n * d := by
    calc
      _ = n * ((d / 4) * 4) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self d 4)
  have hMass : n * d ≤ 5 * e₂ := by omega
  have hMax' : 2 * e₂ ≤ 100 * (m * d) := by
    calc
      _ ≤ m * (100 * d) := hMax
      _ = _ := by ring
  have hSize : n * d ≤ (250 * m) * d := by
    rw [Nat.mul_assoc]
    omega
  exact Nat.le_of_mul_le_mul_right hSize hd

theorem trim_thresholds {n d m r : ℕ} (hd : 10000000 ≤ d) (hm : n ≤ 250 * m)
    (hr : m ≤ 100 * (d / 4) * r) :
    1000000 ≤ d / 4 ∧ 100 * d ≤ 1000 * (d / 4) ∧
    d / 10000000 ≤ (d / 4) / 1000000 ∧ n / (100000 * d) ≤ r := by
  refine ⟨by omega,by omega,by omega,?_⟩
  have h₁ : n ≤ (100000 * d) * r := calc
    _ ≤ 250 * (100 * (d / 4) * r) := hm.trans (Nat.mul_le_mul_left _ hr)
    _ = (25000 * (d / 4)) * r := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  exact Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using h₁)

end Erdos642ForestSizes

end Erdos642ForestSizesFile

section Erdos642GraphForestBridgeFile

/- Degree counts and resizing operations for the bipartite forest construction. -/

namespace Erdos642GraphForestBridge

open Finset SimpleGraph Erdos642InducedCounts Erdos642StarForest
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degree_sum_within (S : Finset V) :
    (∑ v ∈ S, degreeWithin G S v) = 2 * (Erdos642InducedCounts.internalEdges G S).card := by
  classical
  let H : SimpleGraph S := G.induce (S : Set V)
  have h := H.sum_degrees_eq_twice_card_edges
  rw [show H.edgeFinset.card = (Erdos642InducedCounts.internalEdges G S).card from card_induced_edges G S] at h
  rw [← Finset.sum_attach S (fun v => degreeWithin G S v)]
  rw [Finset.attach_eq_univ]
  calc
    _ = ∑ v : S, H.degree v := Finset.sum_congr rfl (fun v _ => (degree_induced G S v).symm)
    _ = _ := h

private theorem degree_within_left {A B S : Finset V}
    (hBip : G.IsBipartiteWith (A : Set V) (B : Set V)) {x : V} (hx : x ∈ A) :
    degreeWithin G S x = ((B ∩ S).filter (fun y => G.Adj x y)).card := by
  unfold degreeWithin
  congr 1
  ext y
  simp only [mem_inter,mem_filter,mem_neighborFinset]
  have h : G.Adj x y → y ∈ B := fun hy => hBip.mem_of_mem_adj hx hy
  tauto

private theorem bipartite_degree_sums {A B S : Finset V}
    (hBip : G.IsBipartiteWith (A : Set V) (B : Set V)) :
    (∑ x ∈ A ∩ S, degreeWithin G S x) = ∑ y ∈ B ∩ S, degreeWithin G S y := by
  calc
    _ = ∑ x ∈ A ∩ S, ((B ∩ S).filter (fun y => G.Adj x y)).card :=
      Finset.sum_congr rfl (fun _ hx => degree_within_left G hBip (mem_inter.mp hx).1)
    _ = ∑ y ∈ B ∩ S, ((A ∩ S).filter (fun x => G.Adj x y)).card := by
      simp only [card_filter]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [degree_within_left G hBip.symm (mem_inter.mp hy).1]
      congr 1
      ext x
      simp only [mem_filter, G.adj_comm (u := x) (v := y)]

theorem left_part_card_bound {A B S : Finset V}
    (hBip : G.IsBipartiteWith (A : Set V) (B : Set V)) (hCov : A ∪ B = univ)
    {d D : ℕ} (hd : 0 < d) (hD : D ≤ 1000 * d)
    (hMin : ∀ x ∈ S, d ≤ degreeWithin G S x)
    (hMax : ∀ x ∈ S, degreeWithin G S x ≤ D) :
    S.card ≤ 1001 * (A ∩ S).card := by
  have hBd : (B ∩ S).card * d ≤ (A ∩ S).card * D := by
    calc
      _ = ∑ _y ∈ B ∩ S, d := by rw [Finset.sum_const_nat (fun _ _ => rfl)]
      _ ≤ ∑ y ∈ B ∩ S, degreeWithin G S y := Finset.sum_le_sum (fun y hy => hMin y (mem_inter.mp hy).2)
      _ = ∑ x ∈ A ∩ S, degreeWithin G S x := (bipartite_degree_sums G hBip).symm
      _ ≤ ∑ _x ∈ A ∩ S, D := Finset.sum_le_sum (fun x hx => hMax x (mem_inter.mp hx).2)
      _ = _ := by rw [Finset.sum_const_nat (fun _ _ => rfl)]
  have hBound : (B ∩ S).card ≤ 1000 * (A ∩ S).card := by
    apply Nat.le_of_mul_le_mul_right _ hd
    calc
      _ ≤ (A ∩ S).card * D := hBd
      _ ≤ (A ∩ S).card * (1000 * d) := Nat.mul_le_mul_left _ hD
      _ = _ := by ring
  have hCover : (A ∩ S) ∪ (B ∩ S) = S := by
    rw [← Finset.union_inter_distrib_right,hCov,univ_inter]
  have hDis : Disjoint (A ∩ S) (B ∩ S) := Finset.disjoint_left.mpr
    (fun _ ha hb => Set.disjoint_left.mp hBip.disjoint (mem_inter.mp ha).1 (mem_inter.mp hb).1)
  have hCard : S.card = (A ∩ S).card + (B ∩ S).card := by
    exact (congrArg Finset.card hCover.symm).trans (card_union_of_disjoint hDis)
  omega

/-- The leaves of every star can be restricted to a smaller prescribed size. -/
theorem narrow_packing {E : Finset (V × V)} {A B : Finset V} {P : Finset (V × Finset V)}
    {ℓ ℓ' : ℕ} (hP : IsPacking E A B ℓ P) (hℓ : ℓ' ≤ ℓ) :
    ∃ Q : Finset (V × Finset V), IsPacking E A B ℓ' Q ∧ Q.card = P.card := by
  classical
  have ht (p : P) : ∃ L ⊆ p.val.2, L.card = ℓ' :=
    Finset.exists_subset_card_eq (hℓ.trans_eq (hP.1 p.val p.property).2.2.1.symm)
  choose L hL hLc using ht
  let f : P ↪ V × Finset V := ⟨fun p => (p.val.1,L p),by
    intro p q h
    apply Subtype.ext
    by_contra hn
    have hPair : ((p.val.1, L p) : V × Finset V) = (q.val.1, L q) := h
    have he : p.val.1 = q.val.1 := (Prod.mk.inj hPair).1
    exact (hP.2 p.val p.property q.val q.property hn).1 he⟩
  refine ⟨P.attach.map f,⟨?_,?_⟩,by simp⟩
  · intro x hx
    obtain ⟨p,_,rfl⟩ := mem_map.mp hx
    obtain ⟨hpA,hpB,_,hpE⟩ := hP.1 p.val p.property
    exact ⟨hpA,(hL p).trans hpB,hLc p,fun y hy => hpE y (hL p hy)⟩
  · intro x hx y hy hn
    obtain ⟨p,_,rfl⟩ := mem_map.mp hx
    obtain ⟨q,_,rfl⟩ := mem_map.mp hy
    have hpq : p.val ≠ q.val := fun h => hn (congrArg f (Subtype.ext h))
    obtain ⟨hroot,hdis⟩ := hP.2 p.val p.property q.val q.property hpq
    exact ⟨hroot,Finset.disjoint_of_subset_left (hL p) (Finset.disjoint_of_subset_right (hL q) hdis)⟩

/-- Corollary 3.2 in the fixed finite bipartition representation. -/
theorem exists_bipartite_root_disjoint_forests {A B : Finset V}
    (hBip : G.IsBipartiteWith (A : Set V) (B : Set V)) (hCov : A ∪ B = univ)
    {d : ℕ} (hd : 10000000 ≤ d) (hMin : ∀ v, d ≤ G.degree v)
    (hMax : ∀ v, G.degree v ≤ 100 * d) :
    let n := Fintype.card V
    let E := ((univ : Finset V) ×ˢ (univ : Finset V)).filter (fun p => G.Adj p.1 p.2)
    ∃ L : List (Finset (V × Finset V)), L.length = d / 10 ∧
      L.Pairwise (fun P Q => Disjoint (P.image Prod.fst) (Q.image Prod.fst)) ∧
      ∀ P ∈ L, IsPacking E A B (d / 10000000) P ∧ P.card = n / (100000 * d) := by
  classical
  let n := Fintype.card V
  let E := ((univ : Finset V) ×ˢ (univ : Finset V)).filter (fun p => G.Adj p.1 p.2)
  have hE : ∀ x y, (x,y) ∈ E ↔ G.Adj x y := by intro x y; simp [E]
  let I := Erdos642InducedCounts.internalEdges G
  have hdPos : 0 < d := by omega
  have hTrimPos : 0 < d / 4 := by omega
  have hTrimLarge : 1000000 ≤ d / 4 := by omega
  have hRatio : 100 * d ≤ 1000 * (d / 4) := by omega
  have hLeaf : d / 10000000 ≤ (d / 4) / 1000000 := by omega
  have hStart : n * d ≤ 2 * (I univ).card := by
    rw [← degree_sum_within G (univ : Finset V)]
    change n * d ≤ ∑ v : V, degreeWithin G univ v
    calc
      _ = ∑ _v : V, d := by simp [n]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => by
        simpa [degreeWithin,card_neighborFinset_eq_degree] using hMin v)
  change ∃ L : List (Finset (V × Finset V)), L.length = d / 10 ∧
    L.Pairwise (fun P Q => Disjoint (P.image Prod.fst) (Q.image Prod.fst)) ∧
    ∀ P ∈ L, IsPacking E A B (d / 10000000) P ∧ P.card = n / (100000 * d)
  apply exists_root_disjoint_forests E A B (d / 10000000) (n / (100000 * d)) (d / 10)
  intro R hRA hR
  have hRootBudget := Erdos642ForestSizes.roots_budget hR.le
  let U := (univ : Finset V) \ R
  have hRemove : (I univ).card ≤ (I U).card + R.card * (100 * d) := by
    exact Erdos642DegreeBudget.remove_vertices_budget G univ R (subset_univ _)
      (fun v _ => hMax v)
  obtain ⟨S,hSU,hTrim,hSMin⟩ := Erdos642DegreeBudget.trim_with_budget G U (d / 4)
  have hTrim' : (I U).card ≤ (I S).card + n * (d / 4) := by
    refine hTrim.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _)
    exact (Nat.sub_le U.card S.card).trans (card_le_univ U)
  have hSMax (v : V) : degreeWithin G S v ≤ 100 * d :=
    (degree_within_le G S v).trans (hMax v)
  have hSedge : 2 * (I S).card ≤ S.card * (100 * d) := by
    rw [← degree_sum_within G S]
    calc
      _ ≤ ∑ _v ∈ S, 100 * d := Finset.sum_le_sum (fun v _ => hSMax v)
      _ = _ := Finset.sum_const_nat (fun _ _ => rfl)
  have hSCard := Erdos642ForestSizes.slice_size_after_trim hdPos hStart hRootBudget hRemove hTrim' hSedge
  have hABound := left_part_card_bound G hBip hCov hTrimPos hRatio hSMin (fun v _ => hSMax v)
  have hLeft (v : V) (hv : v ∈ A ∩ S) : d / 4 ≤ ((B ∩ S).filter (fun w => (v,w) ∈ E)).card := by
    simp only [hE]
    rw [← degree_within_left G hBip (mem_inter.mp hv).1]
    exact hSMin v (mem_inter.mp hv).2
  have hRight (v : V) (hv : v ∈ B ∩ S) : ((A ∩ S).filter (fun w => (w,v) ∈ E)).card ≤ 100 * d := by
    simp only [hE]
    have hFilter : (A ∩ S).filter (fun w => G.Adj w v) = (A ∩ S).filter (fun w => G.Adj v w) := by
      ext w
      simp only [mem_filter,G.adj_comm (u := w) (v := v)]
    rw [hFilter,← degree_within_left G hBip.symm (mem_inter.mp hv).1]
    exact hSMax v
  obtain ⟨P,hP,hPC⟩ := exists_many_stars E (A ∩ S) (B ∩ S) hTrimLarge hABound hRatio hLeft hRight
  obtain ⟨Q,hQ,hQC⟩ := narrow_packing hP hLeaf
  refine ⟨Q,⟨?_,hQ.2⟩,?_⟩
  · intro p hp
    obtain ⟨hpA,hpB,hpCard,hpE⟩ := hQ.1 p hp
    have ha : p.1 ∈ A := (mem_inter.mp hpA).1
    have hu : p.1 ∈ U := hSU (mem_inter.mp hpA).2
    exact ⟨mem_sdiff.mpr ⟨ha,(mem_sdiff.mp hu).2⟩,
      fun y hy => (mem_inter.mp (hpB hy)).1,hpCard,hpE⟩
  · rw [hQC]
    exact (Erdos642ForestSizes.trim_thresholds hd hSCard hPC).2.2.2

end Erdos642GraphForestBridge

end Erdos642GraphForestBridgeFile

section Erdos642DMMSScalesFile

/- Uniform numerical scales for the walk length in DMMS, Section 3.5. -/

namespace Erdos642DMMSScales

open Filter
open scoped Topology

private theorem log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 4 * x := by
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx))
  rw [Real.log_sqrt hx₀] at hlog
  have hle : Real.log x ≤ 2 * Real.sqrt x := by linarith
  calc
    Real.log x ^ 2 ≤ (2 * Real.sqrt x) ^ 2 :=
      pow_le_pow_left₀ (Real.log_nonneg hx) hle 2
    _ = 4 * x := by rw [mul_pow, Real.sq_sqrt hx₀]; norm_num

/-- The degree ratio bounds the average above by a hundred times the minimum. -/
theorem log_pow_le_min_degree {n m : ℕ} (hm : 0 < m) (deg : Fin m → ℕ) (d : ℕ)
    (hReg : ∀ v, deg v ≤ 100 * d)
    (hAvg : Real.log n ^ 7 / 600 ≤ (∑ v, (deg v : ℝ)) / (m : ℝ)) :
    Real.log n ^ 7 / 60000 ≤ (d : ℝ) := by
  have hm₀ : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsum : (∑ v, (deg v : ℝ)) ≤ (m : ℝ) * (100 * d) := by
    calc
      _ ≤ ∑ _v : Fin m, (100 : ℝ) * d := Finset.sum_le_sum fun v _ => by exact_mod_cast hReg v
      _ = _ := by simp [mul_comm]
  have hav : (∑ v, (deg v : ℝ)) / (m : ℝ) ≤ 100 * d :=
    (div_le_iff₀ hm₀).mpr (by simpa only [mul_comm (m : ℝ)] using hsum)
  linarith only [hAvg.trans hav]

/-- Convert the edge-set average and degree-ratio assumptions into the
minimum-degree input for the numerical estimates. -/
theorem graph_min_degree_scales {n m : ℕ} (hm : 0 < m)
    (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (hReg : ∀ u v, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard)
    (hAvg : Real.log n ^ 7 / 600 ≤ 2 * (H.edgeSet.ncard : ℝ) / m) :
    Real.log n ^ 7 / 60000 ≤ (H.minDegree : ℝ) ∧ (H.minDegree : ℝ) ≤ m := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨w, hw⟩ := H.exists_minimal_degree_vertex
  have hDegree (v : Fin m) : (H.neighborSet v).ncard = H.degree v := by
    rw [Set.ncard_eq_toFinset_card']
    exact H.card_neighborFinset_eq_degree v
  have hReg' (v : Fin m) : H.degree v ≤ 100 * H.minDegree := by
    simpa only [hDegree,hw] using hReg v w
  have hSum : (∑ v, (H.degree v : ℝ)) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  have hAvg' : Real.log n ^ 7 / 600 ≤ (∑ v, (H.degree v : ℝ)) / m := by
    rw [hSum]
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hAvg
  refine ⟨log_pow_le_min_degree hm (fun v => H.degree v) H.minDegree hReg' hAvg', ?_⟩
  exact_mod_cast (show H.minDegree ≤ m by
    rw [hw]
    simpa only [Fintype.card_fin] using (H.degree_lt_card_verts w).le)

/-- A uniform bound retains the dependence of the mixing time on the subgraph size.
When the slice is small, its logarithm is bounded by eight times the logarithm of
the ambient logarithm. -/
theorem mixing_square_mul_log_square_le {L m k : ℝ}
    (hL : 1 ≤ L) (hm : 0 < m) (hk₀ : 0 ≤ k) (hlogm : Real.log m ≤ L)
    (hmin : L ^ 7 / 60000 ≤ m)
    (hk : k ≤ 10 ^ 10 * L ^ 2 * Real.log m) :
    k ^ 2 * L ^ 2 ≤ 10 ^ 28 * m := by
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hk' : k ≤ 10 ^ 10 * L ^ 3 := by
    calc
      k ≤ 10 ^ 10 * L ^ 2 * Real.log m := hk
      _ ≤ 10 ^ 10 * L ^ 2 * L := mul_le_mul_of_nonneg_left hlogm (by positivity)
      _ = 10 ^ 10 * L ^ 3 := by ring
  by_cases hbig : L ^ 8 ≤ m
  · have hs : k ^ 2 ≤ (10 ^ 10 * L ^ 3) ^ 2 := pow_le_pow_left₀ hk₀ hk' 2
    calc
      _ ≤ (10 ^ 10 * L ^ 3) ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right hs (by positivity)
      _ = 10 ^ 20 * L ^ 8 := by ring
      _ ≤ 10 ^ 20 * m := mul_le_mul_of_nonneg_left hbig (by positivity)
      _ ≤ 10 ^ 28 * m := mul_le_mul_of_nonneg_right (by norm_num) hm.le
  · have hlog : Real.log m ≤ 8 * Real.log L := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using (Real.log_le_log hm (le_of_not_ge hbig))
    have hk'' : k ≤ 10 ^ 10 * L ^ 2 * (8 * Real.log L) :=
      hk.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
    have hs := pow_le_pow_left₀ hk₀ hk'' 2
    have hr : (10 ^ 10 * L ^ 2 * (8 * Real.log L)) ^ 2 * L ^ 2 =
        (64 * 10 ^ 20 * L ^ 6) * Real.log L ^ 2 := by ring
    calc
      _ ≤ (10 ^ 10 * L ^ 2 * (8 * Real.log L)) ^ 2 * L ^ 2 :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = (64 * 10 ^ 20 * L ^ 6) * Real.log L ^ 2 := hr
      _ ≤ (64 * 10 ^ 20 * L ^ 6) * (4 * L) :=
        mul_le_mul_of_nonneg_left (log_sq_le_four_mul hL) (by positivity)
      _ = (256 * 10 ^ 20) * L ^ 7 := by ring
      _ ≤ (256 * 10 ^ 20) * (60000 * m) :=
        mul_le_mul_of_nonneg_left (by linarith only [hmin]) (by positivity)
      _ ≤ 10 ^ 28 * m := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by norm_num) hm.le

/-- Uniform dominance over the mixing-square scale for the minimum degree,
and over mixing-square times the ambient logarithm for the slice size. -/
theorem eventually_scales (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n ∧
      ∀ (m k : ℕ) (d : ℝ), 0 < m → m ≤ n → 0 < k →
        Real.log n ^ 7 / 60000 ≤ d → d ≤ m →
        (k : ℝ) ≤ 10 ^ 10 * Real.log n ^ 2 * Real.log m →
        (k : ℝ) ≤ 10 ^ 10 * Real.log n ^ 3 ∧
        D * (k : ℝ) ^ 2 ≤ d ∧
        D * (k : ℝ) ^ 2 * Real.log n ≤ m := by
  have hlogTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogTop.eventually_ge_atTop 1, hlogTop.eventually_ge_atTop (60000 * 10 ^ 20 * D),
      hlogTop.eventually_ge_atTop (10 ^ 28 * D)] with n hL hLD hLM
  refine ⟨hL, fun m k d hm hmn hk₀ hd hdm hk => ?_⟩
  let L := Real.log (n : ℝ)
  have hm₀ : 0 < (m : ℝ) := by exact_mod_cast hm
  have hk₀' : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hnLog : Real.log m ≤ L := Real.log_le_log hm₀ (by exact_mod_cast hmn)
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hk' : (k : ℝ) ≤ 10 ^ 10 * L ^ 3 := by
    calc
      _ ≤ 10 ^ 10 * L ^ 2 * Real.log m := hk
      _ ≤ 10 ^ 10 * L ^ 2 * L := mul_le_mul_of_nonneg_left hnLog (by positivity)
      _ = 10 ^ 10 * L ^ 3 := by ring
  refine ⟨hk', ?_, ?_⟩
  · calc
      D * (k : ℝ) ^ 2 ≤ D * (10 ^ 10 * L ^ 3) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk₀' hk' 2) hD
      _ = (60000 * 10 ^ 20 * D) * L ^ 6 / 60000 := by ring
      _ ≤ L * L ^ 6 / 60000 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLD (by positivity))
          (by norm_num)
      _ = L ^ 7 / 60000 := by ring
      _ ≤ d := hd
  · have hs := mixing_square_mul_log_square_le hL hm₀ hk₀' hnLog (hd.trans hdm) hk
    have h₁ : (D * (k : ℝ) ^ 2 * L) * 10 ^ 28 ≤ (k : ℝ) ^ 2 * L ^ 2 := by
      calc
        _ = (10 ^ 28 * D) * ((k : ℝ) ^ 2 * L) := by ring
        _ ≤ L * ((k : ℝ) ^ 2 * L) := mul_le_mul_of_nonneg_right hLM (by positivity)
        _ = _ := by ring
    have h₂ : (D * (k : ℝ) ^ 2 * L) * 10 ^ 28 ≤ (m : ℝ) * 10 ^ 28 := by
      simpa only [mul_comm (10 ^ 28 : ℝ)] using h₁.trans hs
    exact le_of_mul_le_mul_right h₂ (by norm_num : (0 : ℝ) < 10 ^ 28)

/-- Round down in blocks of four mixing lengths. This keeps all four quarters
integral, while losing at most a factor two in the length. -/
theorem exists_rounded_walk_length {m k : ℕ} (hk : 0 < k)
    (hLarge : 8 * (10 : ℝ) ^ 62 * (k : ℝ) ^ 2 ≤ m) :
    ∃ t : ℕ, 4 * k ∣ t ∧
      (m : ℝ) / (2 * 10 ^ 62 * k) ≤ (t : ℝ) ∧
      (t : ℝ) ≤ (m : ℝ) / (10 ^ 62 * k) ∧ t ≤ m := by
  have hk₀ : 0 < (k : ℝ) := by exact_mod_cast hk
  let x : ℝ := (m : ℝ) / (4 * 10 ^ 62 * (k : ℝ) ^ 2)
  let q : ℕ := ⌊x⌋₊
  have hx : 2 ≤ x := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * 10 ^ 62 * (k : ℝ) ^ 2)).mpr
    simpa only [← mul_assoc, show (2 : ℝ) * 4 = 8 by norm_num] using hLarge
  have hqHi : (q : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hqLo : x / 2 ≤ (q : ℝ) := by linarith only [Nat.lt_floor_add_one x, hx]
  let t := 4 * k * q
  have ht : (t : ℝ) = 4 * (k : ℝ) * (q : ℝ) := by simp [t]
  have htLo : (m : ℝ) / (2 * 10 ^ 62 * k) ≤ (t : ℝ) := by
    calc
      _ = 4 * (k : ℝ) * (x / 2) := by dsimp [x]; field_simp
      _ ≤ 4 * (k : ℝ) * (q : ℝ) := mul_le_mul_of_nonneg_left hqLo (by positivity)
      _ = _ := ht.symm
  have htHi : (t : ℝ) ≤ (m : ℝ) / (10 ^ 62 * k) := by
    calc
      _ = 4 * (k : ℝ) * (q : ℝ) := ht
      _ ≤ 4 * (k : ℝ) * x := mul_le_mul_of_nonneg_left hqHi (by positivity)
      _ = _ := by dsimp [x]; field_simp
  have hk₁ : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have htm : t ≤ m := by
    exact_mod_cast htHi.trans (div_le_self (Nat.cast_nonneg m) (by
      calc (1 : ℝ) = (1 : ℝ) * 1 := by ring
           _ ≤ 10 ^ 62 * (k : ℝ) := mul_le_mul (by norm_num) hk₁ (by norm_num)
             (by positivity)))
  exact ⟨t, ⟨q, rfl⟩, htLo, htHi, htm⟩

/-- At the eventual scale the lower bound for self-avoidance is strictly larger
than both errors combined, even with a factor-two loss in its exponent. -/
theorem exponential_tail_positive {L x k : ℝ} (hL : 1 ≤ L)
    (hLarge : 10 ^ 30 * L ≤ x) (hk : k + 1 ≤ Real.exp L) :
    0 < Real.exp (-(2 * x) / 10 ^ 27) - Real.exp (-x / 10 ^ 25) -
      k * Real.exp (-x / 10 ^ 25) := by
  have hExp : L + -x / 10 ^ 25 < -(2 * x) / 10 ^ 27 := by
    have hx : 0 ≤ x := le_trans (by positivity) hLarge
    linarith only [hLarge, hL, hx]
  have hMul : (k + 1) * Real.exp (-x / 10 ^ 25) ≤ Real.exp (L + -x / 10 ^ 25) := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
  have he := hMul.trans_lt (Real.exp_lt_exp.mpr hExp)
  rw [add_mul, one_mul] at he
  linarith only [he]

/-- The quarter segment and the two halves of every shifted middle segment
are long enough for the edge-count tail estimate. The guaranteed edge count
allows the extra vertex in a cycle that uses both extreme visit times. -/
theorem segment_and_chord_bounds {n m k t : ℕ} {d : ℝ}
    (hL : 1 ≤ Real.log n) (hm : 0 < m) (hmn : m ≤ n) (hk : 0 < k)
    (htLo : (m : ℝ) / (2 * 10 ^ 62 * k) ≤ (t : ℝ))
    (hd : 10 ^ 100 * (k : ℝ) ^ 2 ≤ d)
    (hLong : 10 ^ 30 * Real.log n ≤ (t : ℝ) / k) :
    (∀ i : ℕ, i ≤ k → (t : ℝ) / 5 ≤ ((t / 2 - i) / 2 : ℕ)) ∧
    (t : ℝ) / 5 ≤ (t / 4 : ℕ) ∧
    10 ^ 17 * (k : ℝ) * m / d ≤ (t : ℝ) / 5 ∧
    10 ^ 25 * (k : ℝ) * Real.log m ≤ (t : ℝ) / 5 ∧
    2 * ((t : ℝ) + 1) / k ≤ ((t : ℝ) / 5) ^ 2 * d / (10 ^ 32 * (k : ℝ) ^ 2 * m) := by
  have hk₀ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hm₀ : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd₀ : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hLong' := (le_div_iff₀ hk₀).mp hLong
  have h100 : 100 * k ≤ t := by
    have hc : (100 : ℝ) ≤ 10 ^ 30 * Real.log n := by linarith only [hL]
    exact_mod_cast (mul_le_mul_of_nonneg_right hc hk₀.le).trans hLong'
  have ht₁ : 1 ≤ (t : ℝ) := by exact_mod_cast (show 1 ≤ t by omega)
  have hProduct : 10 ^ 35 * (k : ℝ) * m ≤ (t : ℝ) * d := by
    have hprod := mul_le_mul htLo hd (by positivity) (Nat.cast_nonneg t)
    have hEq : (m : ℝ) / (2 * 10 ^ 62 * k) * (10 ^ 100 * (k : ℝ) ^ 2) =
        5 * 10 ^ 37 * (k : ℝ) * m := by field_simp; ring
    rw [hEq] at hprod
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num) hk₀.le) hm₀.le).trans hprod
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).mpr
    exact_mod_cast (show t ≤ ((t / 2 - i) / 2) * 5 by omega)
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).mpr
    exact_mod_cast (show t ≤ (t / 4) * 5 by omega)
  · apply (div_le_iff₀ hd₀).mpr
    have hp := div_le_div_of_nonneg_right hProduct (by norm_num : (0 : ℝ) ≤ 5)
    calc
      _ ≤ (10 ^ 35 * (k : ℝ) * m) / 5 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).mpr
        have hleft : (10 ^ 17 * (k : ℝ) * m) * 5 = (5 * 10 ^ 17) * (k : ℝ) * m := by ring
        rw [hleft]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num) hk₀.le) hm₀.le
      _ ≤ ((t : ℝ) * d) / 5 := hp
      _ = ((t : ℝ) / 5) * d := by ring
  · have hlogm : Real.log m ≤ Real.log n :=
      Real.log_le_log hm₀ (by exact_mod_cast hmn)
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).mpr
    calc
      _ ≤ (10 ^ 25 * (k : ℝ) * Real.log n) * 5 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogm (by positivity))
          (by norm_num)
      _ = (5 * 10 ^ 25) * ((Real.log n) * k) := by ring
      _ ≤ 10 ^ 30 * ((Real.log n) * k) :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (zero_le_one.trans hL) hk₀.le)
      _ = (10 ^ 30 * Real.log n) * (k : ℝ) := by ring
      _ ≤ _ := hLong'
  · apply (le_div_iff₀ (by positivity : 0 < 10 ^ 32 * (k : ℝ) ^ 2 * m)).mpr
    have hscale : (100 * 10 ^ 32) * (k : ℝ) * m ≤ (t : ℝ) * d :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hk₀.le)
        hm₀.le).trans hProduct
    calc
      _ = (2 * ((t : ℝ) + 1)) * (10 ^ 32 * k * m) := by field_simp
      _ ≤ (4 * (t : ℝ)) * (10 ^ 32 * k * m) :=
        mul_le_mul_of_nonneg_right (by linarith only [ht₁]) (by positivity)
      _ = ((t : ℝ) / 25) * ((100 * 10 ^ 32) * (k : ℝ) * m) := by ring
      _ ≤ ((t : ℝ) / 25) * ((t : ℝ) * d) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = ((t : ℝ) / 5) ^ 2 * d := by ring

/-- Uniformly for every eligible slice and mixing length, choose an integral
walk length with the degree, segment, edge-count and probability margins in
Section 3.5. -/
theorem eventually_walk_parameters :
    ∀ᶠ n : ℕ in atTop, ∀ (m k : ℕ) (d : ℝ),
      0 < m → m ≤ n → 0 < k →
      Real.log n ^ 7 / 60000 ≤ d → d ≤ m →
      (k : ℝ) ≤ 10 ^ 10 * Real.log n ^ 2 * Real.log m →
      ∃ t : ℕ, 4 * k ∣ t ∧ t ≤ m ∧
        (m : ℝ) / (2 * 10 ^ 62 * k) ≤ (t : ℝ) ∧
        (t : ℝ) ≤ (m : ℝ) / (10 ^ 62 * k) ∧
        10 ^ 100 * (k : ℝ) ^ 2 ≤ d ∧
        10 ^ 30 * Real.log n ≤ (t : ℝ) / k ∧
        (∀ i : ℕ, i ≤ k → (t : ℝ) / 5 ≤ ((t / 2 - i) / 2 : ℕ)) ∧
        (t : ℝ) / 5 ≤ (t / 4 : ℕ) ∧
        10 ^ 17 * (k : ℝ) * m / d ≤ (t : ℝ) / 5 ∧
        10 ^ 25 * (k : ℝ) * Real.log m ≤ (t : ℝ) / 5 ∧
        2 * ((t : ℝ) + 1) / k ≤
          ((t : ℝ) / 5) ^ 2 * d / (10 ^ 32 * (k : ℝ) ^ 2 * m) ∧
        0 < Real.exp (-((m : ℝ) / (10 ^ 89 * (k : ℝ) ^ 2))) -
          Real.exp (-((t : ℝ) / k) / 10 ^ 25) -
          (k : ℝ) * Real.exp (-((t : ℝ) / k) / 10 ^ 25) := by
  have hlogTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hExpTop : Tendsto (fun n : ℕ => Real.exp (Real.log n) / Real.log n ^ 3) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop 3).comp hlogTop
  filter_upwards [eventually_scales (10 ^ 100) (by positivity),
    hExpTop.eventually_ge_atTop (2 * 10 ^ 10)] with n hscale hexp
  intro m k d hm hmn hk hd hdm hkMax
  obtain ⟨hL,hbound⟩ := hscale
  obtain ⟨hkMax',hdQuad,hmQuad⟩ := hbound m k d hm hmn hk hd hdm hkMax
  have hk₀ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL₀ : 0 ≤ Real.log n := zero_le_one.trans hL
  have hk₂ : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
  have hBig : 8 * (10 : ℝ) ^ 62 * (k : ℝ) ^ 2 ≤ m := by
    calc
      _ ≤ 10 ^ 100 * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) hk₂
      _ ≤ 10 ^ 100 * (k : ℝ) ^ 2 * Real.log n := le_mul_of_one_le_right (by positivity) hL
      _ ≤ m := hmQuad
  obtain ⟨t,htDiv,htLo,htHi,htm⟩ := exists_rounded_walk_length hk hBig
  have hLong : 10 ^ 30 * Real.log n ≤ (t : ℝ) / k := by
    apply (le_div_iff₀ hk₀).mpr
    refine ((le_div_iff₀ (by positivity : 0 < 2 * 10 ^ 62 * (k : ℝ))).mpr ?_).trans htLo
    calc
      _ = (2 * 10 ^ 92) * (k : ℝ) ^ 2 * Real.log n := by ring
      _ ≤ 10 ^ 100 * (k : ℝ) ^ 2 * Real.log n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hk₂) hL₀
      _ ≤ m := hmQuad
  obtain ⟨hHalves,hQuarter,hLen₁,hLen₂,hChord⟩ :=
    segment_and_chord_bounds hL hm hmn hk htLo hdQuad hLong
  have hExp' : 2 * 10 ^ 10 * Real.log n ^ 3 ≤ Real.exp (Real.log n) :=
    (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hL) 3)).mp hexp
  have hBase : 1 ≤ 10 ^ 10 * Real.log n ^ 3 := by
    have hcube : 1 ≤ Real.log n ^ 3 := one_le_pow₀ hL
    exact one_le_mul_of_one_le_of_one_le (by norm_num) hcube
  have hKExp : (k : ℝ) + 1 ≤ Real.exp (Real.log n) := by
    have h := add_le_add hkMax' hBase
    linarith only [h,hExp']
  have hChance := exponential_tail_positive hL hLong hKExp
  have hSelf :
      -(2 * ((t : ℝ) / k)) / 10 ^ 27 ≤ -((m : ℝ) / (10 ^ 89 * (k : ℝ) ^ 2)) := by
    have hmBound := (div_le_iff₀ (by positivity : 0 < 2 * 10 ^ 62 * (k : ℝ))).mp htLo
    have hr : (m : ℝ) / (10 ^ 89 * (k : ℝ) ^ 2) ≤ (2 * ((t : ℝ) / k)) / 10 ^ 27 := by
      apply (div_le_iff₀ (by positivity : 0 < 10 ^ 89 * (k : ℝ) ^ 2)).mpr
      calc
        _ ≤ (t : ℝ) * (2 * 10 ^ 62 * (k : ℝ)) := hmBound
        _ = ((2 * ((t : ℝ) / k)) / 10 ^ 27) * (10 ^ 89 * (k : ℝ) ^ 2) := by
          field_simp
    linarith only [hr]
  have hSelf' := Real.exp_le_exp.mpr hSelf
  refine ⟨t,htDiv,htm,htLo,htHi,hdQuad,hLong,hHalves,hQuarter,hLen₁,hLen₂,hChord,?_⟩
  linarith only [hChance,hSelf']

/-- Choose equal halves of the middle window with the same sampling residue.
The two blocks occupy at most the available window, and rounding to a multiple
of the odd stride still leaves each block of length at least one fifth of the walk. -/
theorem exists_aligned_middle_halves {n t k stride i : ℕ}
    (hL : 1 ≤ Real.log n) (hk : 0 < k) (hi : i ≤ k)
    (hStride : 0 < stride) (hStrideUpper : stride ≤ k + 1)
    (hLong : 10 ^ 30 * Real.log n ≤ (t : ℝ) / k) :
    ∃ s : ℕ, stride ∣ s ∧ 2 * s ≤ t / 2 - i ∧ (t : ℝ) / 5 ≤ (s : ℝ) := by
  have hk₀ : 0 < (k : ℝ) := by exact_mod_cast hk
  have h100 : 100 * k ≤ t := by
    have hc : (100 : ℝ) ≤ 10 ^ 30 * Real.log n := by linarith only [hL]
    exact_mod_cast (mul_le_mul_of_nonneg_right hc hk₀.le).trans ((le_div_iff₀ hk₀).mp hLong)
  let w := t / 2 - i
  let q := w / (2 * stride)
  let s := stride * q
  have hr := Nat.mod_lt w (by omega : 0 < 2 * stride)
  have hw : w = 2 * s + w % (2 * stride) := by
    simpa only [s, q, ← mul_assoc] using (Nat.div_add_mod w (2 * stride)).symm
  refine ⟨s, ⟨q,rfl⟩, by omega, ?_⟩
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).mpr
  exact_mod_cast (show t ≤ s * 5 by dsimp only [w] at hw hr; omega)

end Erdos642DMMSScales

end Erdos642DMMSScalesFile

section Erdos642PriorEdgesFile

-- Problem: Erdős Problem 642 — upper bound n pow three halves
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/642.lean:68 (declaration Erdos642.erdos_642.variants.upper_bound_n_pow_three_halves)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

namespace OMA642

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- `f` restricted to `[0, m]` is a path of `G` inside `S`. -/
def IsP (S : Finset V) (m : ℕ) (f : ℕ → V) : Prop :=
  (∀ k ≤ m, f k ∈ S) ∧ (∀ k < m, G.Adj (f k) (f (k + 1))) ∧
    (∀ a ≤ m, ∀ b ≤ m, f a = f b → a = b)

/-- the walk going down along `g` from index `k` to index `0` -/
def walkDown (g : ℕ → V) :
    (k : ℕ) → (∀ j < k, G.Adj (g (j + 1)) (g j)) → G.Walk (g k) (g 0)
  | 0, _ => SimpleGraph.Walk.nil
  | k + 1, h => SimpleGraph.Walk.cons (h k (by omega)) (walkDown g k (fun j hj => h j (by omega)))

variable {G}

lemma walkDown_length (g : ℕ → V) :
    ∀ k (h : ∀ j < k, G.Adj (g (j + 1)) (g j)), (walkDown G g k h).length = k := by
  intro k
  induction k with
  | zero => intro h; rfl
  | succ k ih => intro h; simp [walkDown, ih]

lemma mem_support_walkDown (g : ℕ → V) :
    ∀ k (h : ∀ j < k, G.Adj (g (j + 1)) (g j)) (v : V),
      v ∈ (walkDown G g k h).support ↔ ∃ j ≤ k, g j = v := by
  intro k
  induction k with
  | zero => intro h v; simp [walkDown, eq_comm]
  | succ k ih =>
    intro h v
    simp only [walkDown, SimpleGraph.Walk.support_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨k + 1, le_rfl, rfl⟩
      · exact ⟨j, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.lt_or_ge j (k + 1) with h1 | h1
      · exact Or.inr ⟨j, by omega, rfl⟩
      · left; rw [show j = k + 1 by omega]

lemma mem_edges_walkDown (g : ℕ → V) :
    ∀ k (h : ∀ j < k, G.Adj (g (j + 1)) (g j)) (e : Sym2 V),
      e ∈ (walkDown G g k h).edges → ∃ j < k, e = s(g (j + 1), g j) := by
  intro k
  induction k with
  | zero => intro h e he; simp [walkDown] at he
  | succ k ih =>
    intro h e he
    simp only [walkDown, SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨k, by omega, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ih _ e he
      exact ⟨j, by omega, rfl⟩

lemma walkDown_isPath (g : ℕ → V) :
    ∀ k (h : ∀ j < k, G.Adj (g (j + 1)) (g j)),
      (∀ a ≤ k, ∀ b ≤ k, g a = g b → a = b) → (walkDown G g k h).IsPath := by
  intro k
  induction k with
  | zero => intro h _; exact SimpleGraph.Walk.IsPath.nil
  | succ k ih =>
    intro h hinj
    simp only [walkDown]
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨ih _ (fun a ha b hb hab => hinj a (by omega) b (by omega) hab), ?_⟩
    rw [mem_support_walkDown]
    rintro ⟨j, hj, hjk⟩
    have := hinj j (by omega) (k + 1) le_rfl hjk
    omega


lemma ext_lemma {S : Finset V} {M : ℕ} {f : ℕ → V} (hf : IsP G S M f)
    (hmax : ∀ g, ¬ IsP G S (M + 1) g) :
    ∀ w ∈ S, G.Adj (f 0) w → ∃ k ≤ M, f k = w := by
  intro w hw hadj
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2, h3⟩ := hf
  apply hmax (fun k => if k = 0 then w else f (k - 1))
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    dsimp only
    split_ifs
    · exact hw
    · exact h1 _ (by omega)
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa using hadj.symm
    · simp only [show k ≠ 0 by omega, show k + 1 ≠ 0 by omega, if_false]
      have := h2 (k - 1) (by omega)
      rwa [show k - 1 + 1 = k + 1 - 1 by omega] at this
  · intro a ha b hb hab
    by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0
    · omega
    · simp only [ha0, hb0, if_true, if_false] at hab
      exact absurd hab.symm (hc _ (by omega))
    · simp only [ha0, hb0, if_true, if_false] at hab
      exact absurd hab (hc _ (by omega))
    · simp only [ha0, hb0, if_false] at hab
      have := h3 _ (by omega) _ (by omega) hab
      omega

/-- rotation of a path at a neighbour `f i` of the endpoint `f 0` -/
def rot (f : ℕ → V) (i : ℕ) : ℕ → V := fun k => if k < i then f (i - 1 - k) else f k

lemma rot_isP {S : Finset V} {M : ℕ} {f : ℕ → V} (hf : IsP G S M f) {i : ℕ} (hi1 : 1 ≤ i)
    (hiM : i ≤ M) (hadj : G.Adj (f 0) (f i)) : IsP G S M (rot f i) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    unfold rot; split_ifs
    · exact h1 _ (by omega)
    · exact h1 _ hk
  · intro k hk
    unfold rot
    by_cases hk1 : k + 1 < i
    · rw [if_pos (by omega), if_pos hk1]
      have := h2 (i - 1 - (k + 1)) (by omega)
      rw [show i - 1 - (k + 1) + 1 = i - 1 - k by omega] at this
      exact this.symm
    · by_cases hk2 : k + 1 = i
      · rw [if_pos (by omega), if_neg (by omega), show i - 1 - k = 0 by omega, hk2]
        exact hadj
      · rw [if_neg (by omega), if_neg (by omega)]
        exact h2 k hk
  · intro a ha b hb hab
    unfold rot at hab
    split_ifs at hab with p q q
    · have := h3 _ (by omega) _ (by omega) hab; omega
    · have := h3 _ (by omega) _ (by omega) hab; omega
    · have := h3 _ (by omega) _ (by omega) hab; omega
    · exact h3 _ ha _ hb hab

lemma rot_image {f : ℕ → V} {i M : ℕ} (hiM : i ≤ M) :
    ∀ k ≤ M, ∃ k' ≤ M, rot f i k = f k' := by
  intro k hk
  unfold rot
  split_ifs
  · exact ⟨i - 1 - k, by omega, rfl⟩
  · exact ⟨k, hk, rfl⟩


lemma rot_zero {f : ℕ → V} {i : ℕ} (hi : 1 ≤ i) : rot f i 0 = f (i - 1) := by
  simp [rot, show 0 < i by omega]

lemma rot_ge {f : ℕ → V} {i k : ℕ} (hk : i ≤ k) : rot f i k = f k := by
  simp [rot, show ¬ k < i by omega]

lemma rot_surj {f : ℕ → V} {i J : ℕ} (hiJ : i ≤ J) :
    ∀ t ≤ J, ∃ j ≤ J, rot f i j = f t := by
  intro t ht
  by_cases h : t < i
  · refine ⟨i - 1 - t, by omega, ?_⟩
    simp [rot, show i - 1 - t < i by omega, show i - 1 - (i - 1 - t) = t by omega]
  · exact ⟨t, ht, rot_ge (by omega)⟩

theorem core [Fintype V] [DecidableRel G.Adj] (S : Finset V) (δ : ℕ) (hδ2 : 2 ≤ δ)
    (hne : S.Nonempty) (hdeg : ∀ v ∈ S, δ ≤ #(S.filter (G.Adj v))) :
    ∃ u, ∃ c : G.Walk u u, c.IsCycle ∧
      δ * δ ≤ 2 * ({e | c.IsChord e}.ncard + c.length) := by
  classical
  -- a longest path in S
  obtain ⟨v0, hv0⟩ := hne
  have hex0 : ∃ f, IsP G S 0 f :=
    ⟨fun _ => v0, fun _ _ => hv0, fun k hk => absurd hk (by omega), fun a ha b hb _ => by omega⟩
  have hbound : ∀ m f, IsP G S m f → m + 1 ≤ #S := by
    intro m f hf
    have := Finset.card_le_card_of_injOn f (s := range (m + 1)) (t := S)
      (fun k hk => hf.1 k (by simp at hk; omega))
      (fun a ha b hb hab => hf.2.2 a (by simp at ha; omega) b (by simp at hb; omega) hab)
    simpa using this
  set M := Nat.findGreatest (fun m => ∃ f, IsP G S m f) #S with hMdef
  have hMspec := Nat.findGreatest_spec (P := fun m => ∃ f, IsP G S m f) (m := 0) (n := #S)
    (Nat.zero_le _) hex0
  rw [← hMdef] at hMspec
  obtain ⟨f, hf⟩ := hMspec
  have hmax : ∀ g, ¬ IsP G S (M + 1) g := by
    intro g hg
    have h1 := hbound _ _ hg
    have h2 : M + 1 ≤ M := Nat.le_findGreatest (by omega) ⟨g, hg⟩
    omega
  obtain ⟨hfS, hfadj, hfinj⟩ := hf
  -- neighbours of endpoints of rotated paths lie on the path
  have hnbr : ∀ i, 1 ≤ i → i ≤ M → G.Adj (f 0) (f i) →
      ∀ w ∈ S, G.Adj (f (i - 1)) w → ∃ k ≤ M, f k = w := by
    intro i hi1 hiM hadj w hw hw'
    have hr := rot_isP ⟨hfS, hfadj, hfinj⟩ hi1 hiM hadj
    obtain ⟨k', hk', hk'w⟩ := ext_lemma hr hmax w hw (by rw [rot_zero hi1]; exact hw')
    obtain ⟨k'', hk'', he⟩ := rot_image (f := f) hiM k' hk'
    exact ⟨k'', hk'', he ▸ hk'w⟩
  have hnbr0 : ∀ w ∈ S, G.Adj (f 0) w → ∃ k ≤ M, f k = w :=
    ext_lemma ⟨hfS, hfadj, hfinj⟩ hmax
  -- the index set of neighbours of f 0
  set E := (range (M + 1)).filter (fun i => 1 ≤ i ∧ G.Adj (f 0) (f i)) with hEdef
  have hE_card : δ ≤ #E := by
    refine (hdeg _ (hfS 0 (by omega))).trans ?_
    calc #(S.filter (G.Adj (f 0))) ≤ #(E.image f) := by
          refine Finset.card_le_card (fun w hw => ?_)
          rw [Finset.mem_filter] at hw
          obtain ⟨k, hk, rfl⟩ := hnbr0 w hw.1 hw.2
          have hk0 : k ≠ 0 := by rintro rfl; exact G.irrefl hw.2
          exact Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
            by omega, hw.2⟩, rfl⟩
      _ ≤ #E := Finset.card_image_le
  have hEmem : ∀ i ∈ E, 1 ≤ i ∧ i ≤ M ∧ G.Adj (f 0) (f i) := by
    intro i hi
    simp only [hEdef, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.2.1, by omega, hi.2.2⟩
  have hM1 : 1 ≤ M := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < #E)
    have := hEmem i hi; omega
  -- the farthest neighbour index J
  set Pairs := (E ×ˢ range (M + 1)).filter (fun p => G.Adj (f (p.1 - 1)) (f p.2)) with hPdef
  have hPmem : ∀ i ∈ E, (i, i) ∈ Pairs := by
    intro i hi
    obtain ⟨h1, h2, _⟩ := hEmem i hi
    simp only [hPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨hi, by omega⟩, ?_⟩
    have := hfadj (i - 1) (by omega)
    rwa [show i - 1 + 1 = i by omega] at this
  have hPne : Pairs.Nonempty := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < #E)
    exact ⟨_, hPmem i hi⟩
  obtain ⟨⟨i0, J⟩, hp, hmaxJ⟩ := Finset.exists_max_image Pairs (fun p => p.2) hPne
  simp only [hPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
  obtain ⟨⟨hi0E, hJM⟩, hadjJ⟩ := hp
  obtain ⟨hi01, hi0M, hi0adj⟩ := hEmem i0 hi0E
  have hJall : ∀ i ∈ E, ∀ k ≤ M, G.Adj (f (i - 1)) (f k) → k ≤ J := by
    intro i hi k hk hadj
    have : (i, k) ∈ Pairs := by
      simp only [hPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hi, by omega⟩, hadj⟩
    exact hmaxJ _ this
  have hi0J : i0 ≤ J := hmaxJ _ (hPmem i0 hi0E)
  have h1E : 1 ∈ E := by
    simp only [hEdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, le_rfl, by simpa using hfadj 0 (by omega)⟩
  have hJ2 : 2 ≤ J := by
    by_contra hJ
    have hsub : E ⊆ {1} := by
      intro i hi
      have := hJall 1 h1E i (hEmem i hi).2.1 (by simpa using (hEmem i hi).2.2)
      have := (hEmem i hi).1
      simp; omega
    have := Finset.card_le_card hsub
    simp at this
    omega
  -- the rotated path and the cycle
  set g := rot f i0 with hgdef
  obtain ⟨hgS, hgadj, hginj⟩ := rot_isP ⟨hfS, hfadj, hfinj⟩ hi01 hi0M hi0adj
  have hg0 : g 0 = f (i0 - 1) := rot_zero hi01
  have hgJ : g J = f J := rot_ge hi0J
  have hadjc : G.Adj (g 0) (g J) := by rw [hg0, hgJ]; exact hadjJ
  set W := walkDown G g J (fun j hj => (hgadj j (by omega)).symm) with hWdef
  have hWpath : W.IsPath :=
    walkDown_isPath g J _ (fun a ha b hb hab => hginj a (by omega) b (by omega) hab)
  have hnotin : s(g 0, g J) ∉ W.edges := by
    intro hmem
    obtain ⟨j, hj, hje⟩ := mem_edges_walkDown g J _ _ hmem
    rw [Sym2.eq_iff] at hje
    rcases hje with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hginj 0 (by omega) (j + 1) (by omega) h1; omega
    · have := hginj 0 (by omega) j (by omega) h1
      have := hginj J (by omega) (j + 1) (by omega) h2
      omega
  set c : G.Walk (g 0) (g 0) := SimpleGraph.Walk.cons hadjc W with hcdef
  have hcyc : c.IsCycle := (SimpleGraph.Walk.cons_isCycle_iff W hadjc).2 ⟨hWpath, hnotin⟩
  have hclen : c.length = J + 1 := by
    simp [hcdef, hWdef, walkDown_length]
  have hcsupp : ∀ t ≤ J, f t ∈ c.support := by
    intro t ht
    obtain ⟨j, hj, hjt⟩ := rot_surj (f := f) hi0J t ht
    simp only [hcdef, SimpleGraph.Walk.support_cons, List.mem_cons]
    right
    rw [hWdef, mem_support_walkDown]
    exact ⟨j, hj, hjt⟩
  refine ⟨g 0, c, hcyc, ?_⟩
  -- double counting
  set D := E.sigma (fun i => S.filter (G.Adj (f (i - 1)))) with hDdef
  set φ : (Σ _ : ℕ, V) → Sym2 V := fun p => s(f (p.1 - 1), p.2) with hφdef
  have hD : δ * δ ≤ #D := by
    rw [hDdef, Finset.card_sigma]
    calc δ * δ ≤ #E * δ := Nat.mul_le_mul_right _ hE_card
      _ = ∑ _i ∈ E, δ := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hdeg _ (hfS _ (by have := hEmem i hi; omega)))
  have hfib : #D ≤ 2 * #(D.image φ) := by
    refine Finset.card_le_mul_card_image (f := φ) D 2 (fun e he => ?_)
    obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.1 he
    refine (Finset.card_le_card_of_injOn (fun p => p.2) (t := {f (p0.1 - 1), p0.2})
      ?_ ?_).trans (Finset.card_le_two)
    · intro p hp
      rw [Finset.coe_filter] at hp
      obtain ⟨-, hpe⟩ := hp
      simp only [hφdef] at hpe
      have : p.2 ∈ s(f (p0.1 - 1), p0.2) := by rw [← hpe]; exact Sym2.mem_mk_right _ _
      rw [Sym2.mem_iff] at this
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact this
    · intro p hp q hq hpq
      rw [Finset.coe_filter] at hp hq
      obtain ⟨hpD, hpe⟩ := hp
      obtain ⟨hqD, hqe⟩ := hq
      simp only at hpq
      have hpq' : s(f (p.1 - 1), p.2) = s(f (q.1 - 1), q.2) := by
        simp only [hφdef] at hpe hqe; rw [hpe, hqe]
      rw [hpq, Sym2.congr_left] at hpq'
      rw [hDdef, Finset.mem_sigma] at hpD hqD
      have h1 := hEmem _ hpD.1
      have h2 := hEmem _ hqD.1
      have := hfinj _ (by omega) _ (by omega) hpq'
      have hp1 : p.1 = q.1 := by omega
      exact Sigma.ext hp1 (heq_of_eq hpq)
  -- the image is made of chords or cycle edges
  set Ch := (D.image φ).filter (fun e => e ∉ c.edges) with hChdef
  have hCh : #(D.image φ) ≤ #Ch + c.length := by
    have : D.image φ ⊆ Ch ∪ c.edges.toFinset := by
      intro e he
      by_cases h : e ∈ c.edges
      · exact Finset.mem_union_right _ (List.mem_toFinset.2 h)
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, h⟩)
    refine (Finset.card_le_card this).trans ((Finset.card_union_le _ _).trans ?_)
    have := List.toFinset_card_le c.edges
    rw [SimpleGraph.Walk.length_edges] at this
    omega
  have hChsub : (Ch : Set (Sym2 V)) ⊆ {e | c.IsChord e} := by
    intro e he
    rw [hChdef, Finset.coe_filter] at he
    obtain ⟨he, hnot⟩ := he
    obtain ⟨⟨i, w⟩, hpD, rfl⟩ := Finset.mem_image.1 he
    simp only [hDdef, Finset.mem_sigma, Finset.mem_filter] at hpD
    obtain ⟨hiE, hwS, hadj⟩ := hpD
    obtain ⟨hi1, hiM, hi0⟩ := hEmem i hiE
    obtain ⟨k, hkM, rfl⟩ := hnbr i hi1 hiM hi0 w hwS hadj
    have hkJ := hJall i hiE k hkM hadj
    have hiJ : i ≤ J := hmaxJ _ (hPmem i hiE)
    show c.IsChord s(f (i - 1), f k)
    rw [SimpleGraph.Walk.isChord_sym2Mk]
    exact ⟨hadj, hnot, hcsupp _ (by omega), hcsupp _ hkJ⟩
  have hncard : #Ch ≤ {e | c.IsChord e}.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hChsub (Set.toFinite _)
  omega


theorem edges_le [Fintype V] (G : SimpleGraph V)
    (hG : ∀ (v : V) (c : G.Walk v v), c.IsCycle → {e : Sym2 V | c.IsChord e}.ncard < c.length) :
    G.edgeSet.ncard ≤ 2 * (Nat.sqrt (Fintype.card V) + 1) * Fintype.card V := by
  classical
  set δ := 2 * (Nat.sqrt (Fintype.card V) + 1) with hδ
  set n := Fintype.card V with hn
  by_contra hcon
  push Not at hcon
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset] at hcon
  -- edges inside a set
  let eS : Finset V → ℕ := fun S => #(G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S))
  let obj : Finset V → ℤ := fun S => (eS S : ℤ) - δ * #S
  obtain ⟨S, -, hSmax⟩ := Finset.exists_max_image (univ : Finset V).powerset obj
    ⟨univ, Finset.mem_powerset.2 subset_rfl⟩
  have huniv : obj univ ≥ 1 := by
    have : eS univ = #G.edgeFinset := by
      simp only [eS]; congr 1; ext e; simp
    simp only [obj, this, Finset.card_univ, ← hn]
    push_cast; linarith [(by exact_mod_cast hcon : (δ * n : ℤ) < #G.edgeFinset)]
  have hS1 : obj S ≥ 1 := le_trans huniv (hSmax univ (Finset.mem_powerset.2 subset_rfl))
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have : eS ∅ = 0 := by
      simp only [eS, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hall
      induction e using Sym2.ind with
      | _ a b => exact absurd (hall a (Sym2.mem_mk_left a b)) (by simp)
    simp [obj, this] at hS1
  have hdeg : ∀ v ∈ S, δ ≤ #(S.filter (G.Adj v)) := by
    intro v hv
    by_contra hlt
    push Not at hlt
    have hsplit : eS S ≤ eS (S.erase v) + #(S.filter (G.Adj v)) := by
      have hsub : G.edgeFinset.filter (fun e => ∀ u ∈ e, u ∈ S) ⊆
          G.edgeFinset.filter (fun e => ∀ u ∈ e, u ∈ S.erase v) ∪
            (S.filter (G.Adj v)).image (fun w => s(v, w)) := by
        intro e he
        rw [Finset.mem_filter] at he
        obtain ⟨heE, hall⟩ := he
        by_cases hve : v ∈ e
        · apply Finset.mem_union_right
          obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hve
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heE
          exact Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hall w (Sym2.mem_mk_right v w), heE⟩,
            rfl⟩
        · apply Finset.mem_union_left
          refine Finset.mem_filter.2 ⟨heE, fun u hu => Finset.mem_erase.2 ⟨?_, hall u hu⟩⟩
          rintro rfl; exact hve hu
      exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left Finset.card_image_le _))
    have hmax := hSmax (S.erase v) (Finset.mem_powerset.2 (Finset.subset_univ _))
    simp only [obj] at hmax
    rw [Finset.card_erase_of_mem hv] at hmax
    have hS0 : 1 ≤ #S := Finset.card_pos.2 hSne
    push_cast [hS0] at hmax
    have : (eS S : ℤ) ≤ eS (S.erase v) + #(S.filter (G.Adj v)) := by exact_mod_cast hsplit
    have : (#(S.filter (G.Adj v)) : ℤ) < δ := by exact_mod_cast hlt
    linarith
  have hδ2 : 2 ≤ δ := by omega
  obtain ⟨u, c, hc, hineq⟩ := core (G := G) S δ hδ2 hSne hdeg
  have hlt := hG u c hc
  have hlen : c.length ≤ n := by
    have h1 := hc.support_nodup.length_le_card
    rw [List.length_tail, SimpleGraph.Walk.length_support] at h1
    simpa using h1
  have hsq : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have : δ * δ = 4 * ((Nat.sqrt n + 1) * (Nat.sqrt n + 1)) := by rw [hδ]; ring
  nlinarith

end OMA642

end Erdos642PriorEdgesFile

section Erdos642ForestRoundingFile

/- The exact finitary forest and rounding bounds used in DMMS, Section 3.3. -/

namespace Erdos642ForestRounding

open Finset Filter SimpleGraph Erdos642StarForest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite bipartite graph admits a partition covering all its vertices. -/
theorem exists_finset_bipartition (G : SimpleGraph V) (hG : G.IsBipartite) :
    ∃ A B : Finset V, G.IsBipartiteWith (A : Set V) (B : Set V) ∧ A ∪ B = univ := by
  classical
  obtain ⟨c, hc⟩ := hG
  let A : Finset V := univ.filter fun v => c v = 0
  let B : Finset V := univ.filter fun v => c v = 1
  have hc01 (v : V) : c v = 0 ∨ c v = 1 := by
    have hv := (c v).isLt
    rcases Nat.eq_zero_or_pos (c v).val with h | h
    · left; apply Fin.ext; simpa using h
    · right; apply Fin.ext; simp only [Fin.val_one]; omega
  have hA (v : V) : v ∈ A ↔ c v = 0 := by simp [A]
  have hB (v : V) : v ∈ B ↔ c v = 1 := by simp [B]
  refine ⟨A, B, ⟨?_, ?_⟩, ?_⟩
  · rw [Set.disjoint_left]
    intro v hvA hvB
    have h := (hA v).mp hvA
    have h' := (hB v).mp hvB
    exact (by decide : (0 : Fin 2) ≠ 1) (h.symm.trans h')
  · intro v w hvw
    change (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A)
    rw [hA, hB, hA, hB]
    have hne := hc hvw
    rcases hc01 v with hv | hv <;> rcases hc01 w with hw | hw
    · exact (hne (hv.trans hw.symm)).elim
    · exact Or.inl ⟨hv, hw⟩
    · exact Or.inr ⟨hv, hw⟩
    · exact (hne (hv.trans hw.symm)).elim
  · ext v
    simp only [mem_union, hA, hB, mem_univ, iff_true]
    exact hc01 v

/-- The integer quotient in a forest parameter loses at most a factor two. -/
theorem half_div_le_nat_div {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    (a : ℝ) / (2 * (b : ℝ)) ≤ ((a / b : ℕ) : ℝ) := by
  have hq : 1 ≤ a / b := (Nat.le_div_iff_mul_le hb).mpr (by simpa using hba)
  have hq' : a / b + 1 ≤ 2 * (a / b) := by omega
  have ha : a ≤ 2 * (a / b) * b := by
    apply le_trans (Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hb).mp (Nat.lt_succ_self (a / b))))
    exact Nat.mul_le_mul_right b hq'
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (b : ℝ))).mpr
  calc
    (a : ℝ) ≤ 2 * ((a / b : ℕ) : ℝ) * (b : ℝ) := by exact_mod_cast ha
    _ = _ := by ring

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Index the root-disjoint forests and expose each packing in the graph API. -/
theorem exists_indexed_star_forests {A B : Finset V}
    (hBip : G.IsBipartiteWith (A : Set V) (B : Set V)) (hCov : A ∪ B = univ)
    {d : ℕ} (hd : 10000000 ≤ d) (hMin : ∀ v, d ≤ G.degree v)
    (hMax : ∀ v, G.degree v ≤ 100 * d) :
    ∃ F : Fin (d / 10) → Finset (V × Finset V),
      Pairwise (fun i j => Disjoint ((F i).image Prod.fst) ((F j).image Prod.fst)) ∧
      ∀ i, (F i).card = Fintype.card V / (100000 * d) ∧
        (∀ p ∈ F i, p.1 ∈ A ∧ p.2 ⊆ B ∧ p.2.card = d / 10000000 ∧
          ∀ y ∈ p.2, G.Adj p.1 y) ∧
        ∀ p ∈ F i, ∀ q ∈ F i, p ≠ q → p.1 ≠ q.1 ∧ Disjoint p.2 q.2 := by
  obtain ⟨L, hL, hp, hpack⟩ :=
    Erdos642GraphForestBridge.exists_bipartite_root_disjoint_forests G hBip hCov hd hMin hMax
  let F : Fin (d / 10) → Finset (V × Finset V) := fun i => L.get (Fin.cast hL.symm i)
  refine ⟨F, ?_, ?_⟩
  · intro i j hij
    have hget := List.pairwise_iff_get.mp hp
    rcases lt_or_gt_of_ne hij with h | h
    · exact hget (Fin.cast hL.symm i) (Fin.cast hL.symm j) h
    · exact (hget (Fin.cast hL.symm j) (Fin.cast hL.symm i) h).symm
  · intro i
    have ⟨hPi, hcard⟩ := hpack (F i) (List.get_mem _ _)
    refine ⟨hcard, ?_, hPi.2⟩
    intro p hp
    obtain ⟨hpA, hpB, hpCard, hpAdj⟩ := hPi.1 p hp
    refine ⟨hpA, hpB, hpCard, fun y hy => ?_⟩
    simpa using hpAdj y hy

/-- The extremal edge bound gives a sublinear minimum-degree bound
on the graphs in the contradictory case of H2. -/
theorem minDegree_le_four_sqrt_add_one [Nonempty V]
    (hG : Erdos642.CyclesHaveMoreVerticesThanChords G) :
    G.minDegree ≤ 4 * (Nat.sqrt (Fintype.card V) + 1) := by
  have hE := OMA642.edges_le G hG
  have hsum : Fintype.card V * G.minDegree ≤ 2 * G.edgeSet.ncard := by
    rw [← G.coe_edgeFinset, Set.ncard_coe_finset, ← G.sum_degrees_eq_twice_card_edges]
    calc
      _ = ∑ _v : V, G.minDegree := by simp
      _ ≤ _ := Finset.sum_le_sum fun v _ => G.minDegree_le_degree v
  have hcpos : 0 < Fintype.card V := Fintype.card_pos
  apply Nat.le_of_mul_le_mul_left _ hcpos
  calc
    _ ≤ 2 * G.edgeSet.ncard := hsum
    _ ≤ 2 * (2 * (Nat.sqrt (Fintype.card V) + 1) * Fintype.card V) :=
      Nat.mul_le_mul_left _ hE
    _ = _ := by ring

/-- Once the slice is large, the stars-per-forest quotient is positive and
has the required real lower bound. -/
theorem forest_denominator_le [Nonempty V]
    (hG : Erdos642.CyclesHaveMoreVerticesThanChords G)
    (hsize : 1600000 ^ 2 ≤ Fintype.card V) :
    200000 * G.minDegree ≤ Fintype.card V := by
  let s := Nat.sqrt (Fintype.card V)
  have hs : 1600000 ≤ s := Nat.le_sqrt'.mpr hsize
  calc
    _ ≤ 200000 * (4 * (s + 1)) :=
      Nat.mul_le_mul_left _ (minDegree_le_four_sqrt_add_one G hG)
    _ ≤ 1600000 * s := by omega
    _ ≤ s * s := Nat.mul_le_mul_right _ hs
    _ ≤ _ := Nat.sqrt_le _

/-- The minimum degree in H2 eventually clears any fixed threshold, uniformly
over the eligible slices. -/
theorem eventually_minDegree_ge (D : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → ∀ (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
      (∀ u v, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) →
      Real.log n ^ 7 / 600 ≤ 2 * (H.edgeSet.ncard : ℝ) / m →
      D ≤ H.minDegree ∧ D ≤ m := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1, hlog.eventually_ge_atTop (60000 * (D : ℝ))]
    with n hlog1 hlogD
  intro m hm H _ hReg hAvg
  obtain ⟨hd, hm'⟩ := Erdos642DMMSScales.graph_min_degree_scales hm H hReg hAvg
  have hL7 : Real.log n ≤ Real.log n ^ 7 := le_self_pow₀ hlog1 (by norm_num)
  have hD : (D : ℝ) ≤ (H.minDegree : ℝ) := by linarith only [hlogD, hL7, hd]
  exact ⟨by exact_mod_cast hD, by exact_mod_cast hD.trans hm'⟩

/-- Exact floors with real lower bounds, uniformly in every H2 counterexample. -/
theorem eventually_rounded_star_forests :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → ∀ (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
      H.IsBipartite →
      (∀ u v, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) →
      Real.log n ^ 7 / 600 ≤ 2 * (H.edgeSet.ncard : ℝ) / m →
      Erdos642.CyclesHaveMoreVerticesThanChords H →
      let d := H.minDegree
      (d : ℝ) / 20 ≤ ((d / 10 : ℕ) : ℝ) ∧
      (m : ℝ) / (200000 * (d : ℝ)) ≤ ((m / (100000 * d) : ℕ) : ℝ) ∧
      (d : ℝ) / 20000000 ≤ ((d / 10000000 : ℕ) : ℝ) ∧
      ∃ A B : Finset (Fin m), H.IsBipartiteWith (A : Set (Fin m)) (B : Set (Fin m)) ∧
        A ∪ B = univ ∧
        ∃ F : Fin (d / 10) → Finset (Fin m × Finset (Fin m)),
          Pairwise (fun i j => Disjoint ((F i).image Prod.fst) ((F j).image Prod.fst)) ∧
          ∀ i, (F i).card = m / (100000 * d) ∧
            (∀ p ∈ F i, p.1 ∈ A ∧ p.2 ⊆ B ∧ p.2.card = d / 10000000 ∧
              ∀ y ∈ p.2, H.Adj p.1 y) ∧
            ∀ p ∈ F i, ∀ q ∈ F i, p ≠ q → p.1 ≠ q.1 ∧ Disjoint p.2 q.2 := by
  filter_upwards [eventually_minDegree_ge (1600000 ^ 2)] with n hlarge
  intro m hm H _ hBip hReg hAvg hNo
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let d := H.minDegree
  have ⟨hdLarge, hmLarge⟩ := hlarge m hm H hReg hAvg
  have hdLarge' : 10000000 ≤ d := by change 1600000 ^ 2 ≤ d at hdLarge; omega
  have hd : 0 < d := by omega
  have hmD : 200000 * d ≤ m := by
    simpa only [Fintype.card_fin] using forest_denominator_le H hNo (by simpa using hmLarge)
  have hmD' : 100000 * d ≤ m := by omega
  have hnbr (v : Fin m) : (H.neighborSet v).ncard = H.degree v := by
    rw [Set.ncard_eq_toFinset_card']
    exact H.card_neighborFinset_eq_degree v
  obtain ⟨v, hv⟩ := H.exists_minimal_degree_vertex
  have hMax (w : Fin m) : H.degree w ≤ 100 * d := by simpa only [hnbr, ← hv, d] using hReg w v
  obtain ⟨A, B, hb, hCov⟩ := exists_finset_bipartition H hBip
  refine ⟨?_, ?_, ?_, A, B, hb, hCov, ?_⟩
  · have h := half_div_le_nat_div (a := d) (b := 10) (by decide) (by omega)
    norm_num [d] at h ⊢
    exact h
  · have h := half_div_le_nat_div (a := m) (b := 100000 * d) (by positivity) hmD'
    norm_num [d, Nat.cast_mul, ← mul_assoc] at h ⊢
    exact h
  · have h := half_div_le_nat_div (a := d) (b := 10000000) (by decide) hdLarge'
    norm_num [d] at h ⊢
    exact h
  · simpa only [Fintype.card_fin] using
      exists_indexed_star_forests H hb hCov hdLarge' H.minDegree_le_degree hMax

end Erdos642ForestRounding

end Erdos642ForestRoundingFile

section Erdos642FiniteCoareaFile

/- Finite coarea for the variational mixing bound in Erdős Problem 642. -/

namespace Erdos642FiniteCoarea

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Oriented boundary of a finite set in a weighted graph or kernel. -/
def cut (w : V → V → ℝ) (S : Finset V) : ℝ := ∑ x ∈ S, ∑ y ∈ Sᶜ, w x y

/-- Nonnegative oriented variation evaluated on all ordered pairs. -/
noncomputable def variation (w : V → V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ x : V, ∑ y : V, w x y * max (f x - f y) 0

private theorem sum_ite_cut (w : V → V → ℝ) (S : Finset V) (a : ℝ) :
    (∑ x : V, ∑ y : V, w x y * (if x ∈ S ∧ y ∉ S then a else 0)) = a * cut w S := by
  classical
  calc
    _ = ∑ x : V, if x ∈ S then ∑ y : V, if y ∉ S then w x y * a else 0 else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases hx : x ∈ S <;> simp [hx, mul_ite]
    _ = ∑ x ∈ S, ∑ y ∈ Sᶜ, w x y * a := by
      rw [← sum_filter]
      simp_rw [← sum_filter]
      have hc : (univ.filter fun y => y ∉ S) = Sᶜ := by ext y; simp
      rw [hc]
      simp
    _ = _ := by
      simp only [cut, mul_comm a, sum_mul]

private theorem variation_sub_min (w : V → V → ℝ) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) {a : ℝ}
    (ha : 0 ≤ a) (hmin : ∀ x, 0 < f x → a ≤ f x) :
    variation w f =
      variation w (fun x => max (f x - a) 0) +
        a * cut w (univ.filter fun x => 0 < f x) := by
  classical
  let S := univ.filter fun x => 0 < f x
  let g (x : V) := max (f x - a) 0
  have hterm (x y : V) : max (f x - f y) 0 =
      max (g x - g y) 0 + if x ∈ S ∧ y ∉ S then a else 0 := by
    have hS {z : V} : z ∈ S ↔ 0 < f z := by simp [S]
    have hg_pos {z : V} (hz : z ∈ S) : g z = f z - a :=
      max_eq_left (sub_nonneg.mpr (hmin z (hS.mp hz)))
    have hf_zero {z : V} (hz : z ∉ S) : f z = 0 :=
      le_antisymm (le_of_not_gt (hS.not.mp hz)) (hf z)
    have hg_zero {z : V} (hz : z ∉ S) : g z = 0 := by
      simpa only [g, hf_zero hz, zero_sub] using max_eq_right (neg_nonpos.mpr ha)
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simp only [hg_pos hx, hg_pos hy, hx, hy, not_true_eq_false, and_false, if_false,
        add_zero]
      congr 1
      ring
    · rw [hg_pos hx, hg_zero hy, hf_zero hy, sub_zero, sub_zero,
        max_eq_left (hf x), max_eq_left (sub_nonneg.mpr (hmin x (hS.mp hx)))]
      simp [hx, hy]
    · rw [hg_zero hx, hg_pos hy, hf_zero hx, zero_sub, zero_sub,
        max_eq_right (neg_nonpos.mpr (hf y)),
        max_eq_right (neg_nonpos.mpr (sub_nonneg.mpr (hmin y (hS.mp hy))))]
      simp [hx]
    · simp [hg_zero hx, hg_zero hy, hf_zero hx, hf_zero hy, hx]
  change variation w f = variation w g + a * cut w S
  simp only [variation, hterm, mul_add, sum_add_distrib, sum_ite_cut]

/-- Layer-cake inequality when each subset of the positive support satisfies
a common cut lower bound. This proof removes the smallest positive value at
each step, avoiding integration or a real-valued ordering enumeration. -/
theorem weighted_sum_le_variation (w : V → V → ℝ) (d : V → ℝ)
    (A : Finset V) (h : ℝ)
    (hcut : ∀ T : Finset V, T ⊆ A → h * (∑ x ∈ T, d x) ≤ cut w T)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hA : ∀ x, 0 < f x → x ∈ A) :
    h * (∑ x : V, d x * f x) ≤ variation w f := by
  classical
  let support (g : V → ℝ) := univ.filter (fun x => 0 < g x)
  have hsupport (g : V → ℝ) (x : V) : x ∈ support g ↔ 0 < g x := by simp [support]
  generalize hn : (support f).card = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases he : (support f).Nonempty
    · obtain ⟨x, hx, hx_min⟩ := Finset.exists_min_image (support f) f he
      let a := f x
      let g (y : V) := max (f y - a) 0
      have ha : 0 < a := (hsupport f x).mp hx
      have hg (y : V) : 0 ≤ g y := le_max_right _ _
      have hmin (y : V) (hy : 0 < f y) : a ≤ f y := hx_min y ((hsupport f y).mpr hy)
      have hg_subset : support g ⊆ support f := by
        intro y hy
        have hyp := (hsupport g y).mp hy
        simp only [g, lt_max_iff, lt_self_iff_false, or_false] at hyp
        exact (hsupport f y).mpr (by linarith)
      have hgn : (support g).card < n := by
        rw [← hn]
        apply card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hg_subset, fun heq => ?_⟩
        have hnot : x ∉ support g := by simp [support, g, a]
        exact hnot (heq ▸ hx)
      have hgA (y : V) (hy : 0 < g y) : y ∈ A :=
        hA y ((hsupport f y).mp (hg_subset ((hsupport g y).mpr hy)))
      have hbelow := ih (support g).card hgn g hg hgA rfl
      have hS := hcut (support f) (fun y hy => hA y ((hsupport f y).mp hy))
      have hsplit (y : V) : f y = g y + if y ∈ support f then a else 0 := by
        by_cases hy : y ∈ support f
        · simp [g, hy, max_eq_left (sub_nonneg.mpr (hmin y ((hsupport f y).mp hy)))]
        · have hzero : f y = 0 := le_antisymm (le_of_not_gt ((hsupport f y).not.mp hy)) (hf y)
          simp [g, hy, hzero, ha.le]
      have hsum : (∑ y : V, d y * f y) =
          (∑ y : V, d y * g y) + a * (∑ y ∈ support f, d y) := by
        simp_rw [hsplit, mul_add, mul_ite, mul_zero, sum_add_distrib]
        rw [← sum_filter]
        simp [← sum_mul, mul_comm]
      rw [hsum, mul_add, variation_sub_min w f hf ha.le hmin]
      exact add_le_add hbelow (by
        rw [← mul_assoc, mul_comm h a, mul_assoc]
        exact mul_le_mul_of_nonneg_left hS ha.le)
    · have hzero : f = fun _ => 0 := by
        funext y
        apply le_antisymm _ (hf y)
        by_contra! hy
        exact he ⟨y, (hsupport f y).mpr hy⟩
      simp [hzero, variation]

/-- Ordered-pair Dirichlet energy, twice the unoriented graph convention. -/
def energy (w : V → V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ x : V, ∑ y : V, w x y * (f x - f y)^2

/-- The finite one-sided Cheeger estimate on a nonnegative function whose
positive support satisfies a common cut lower bound. -/
theorem support_poincare (w : V → V → ℝ) (d : V → ℝ)
    (hw : ∀ x y, 0 ≤ w x y) (hsym : ∀ x y, w x y = w y x)
    (hd : ∀ x, (∑ y : V, w x y) = d x)
    (A : Finset V) {h : ℝ} (hh : 0 ≤ h)
    (hcut : ∀ T : Finset V, T ⊆ A → h * (∑ x ∈ T, d x) ≤ cut w T)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (hA : ∀ x, 0 < f x → x ∈ A) :
    h^2 * (∑ x : V, d x * (f x)^2) ≤ 4 * energy w f := by
  classical
  let D := ∑ x : V, d x * (f x)^2
  have hdpos (x : V) : 0 ≤ d x := by rw [← hd]; exact sum_nonneg fun _ _ => hw _ _
  have hD : 0 ≤ D := sum_nonneg fun x _ => mul_nonneg (hdpos x) (sq_nonneg _)
  have hE : 0 ≤ energy w f := sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    mul_nonneg (hw _ _) (sq_nonneg _)
  by_cases hzero : D = 0
  · change h^2 * D ≤ _
    rw [hzero, mul_zero]
    positivity
  have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hzero)
  let g (p : V × V) := Real.sqrt (w p.1 p.2) * max (f p.1 - f p.2) 0
  let j (p : V × V) := Real.sqrt (w p.1 p.2) * (f p.1 + f p.2)
  have hprod (x y : V) :
      g (x,y) * j (x,y) = w x y * max ((f x)^2 - (f y)^2) 0 := by
    have hfactor : max ((f x)^2 - (f y)^2) 0 =
        max (f x - f y) 0 * (f x + f y) := by
      by_cases hxy : f y ≤ f x
      · rw [max_eq_left (sub_nonneg.mpr (pow_le_pow_left₀ (hf y) hxy 2)),
          max_eq_left (sub_nonneg.mpr hxy)]
        ring
      · have hyx := le_of_not_ge hxy
        rw [max_eq_right (sub_nonpos.mpr (pow_le_pow_left₀ (hf x) hyx 2)),
          max_eq_right (sub_nonpos.mpr hyx), zero_mul]
    rw [hfactor]
    calc
      _ = (Real.sqrt (w x y))^2 * (max (f x - f y) 0 * (f x + f y)) := by
        dsimp only [g, j]
        ring
      _ = _ := by rw [Real.sq_sqrt (hw x y)]
  have hg (x y : V) : (g (x,y))^2 ≤ w x y * (f x - f y)^2 := by
    have hs : (max (f x - f y) 0)^2 ≤ (f x - f y)^2 := by
      by_cases hxy : 0 ≤ f x - f y
      · simp [max_eq_left hxy]
      · simpa only [max_eq_right (le_of_not_ge hxy), zero_pow (by decide : (2 : ℕ) ≠ 0)]
          using sq_nonneg (f x - f y)
    simp only [g, mul_pow, Real.sq_sqrt (hw x y)]
    exact mul_le_mul_of_nonneg_left hs (hw x y)
  have hj (x y : V) : (j (x,y))^2 ≤ w x y * (2 * (f x)^2 + 2 * (f y)^2) := by
    simp only [j, mul_pow, Real.sq_sqrt (hw x y)]
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (f x - f y)]) (hw x y)
  have hsum (a : V × V → ℝ) :
      (∑ p : V × V, a p) = ∑ x : V, ∑ y : V, a (x,y) := by
    rw [← univ_product_univ, sum_product]
  have hV : (∑ p : V × V, g p * j p) = variation w (fun x => (f x)^2) := by
    rw [hsum]
    simp only [variation, hprod]
  have hG : (∑ p : V × V, (g p)^2) ≤ energy w f := by
    rw [hsum]
    exact sum_le_sum fun x _ => sum_le_sum fun y _ => hg x y
  have hJ : (∑ p : V × V, (j p)^2) ≤ 4 * D := by
    rw [hsum]
    calc
      _ ≤ ∑ x : V, ∑ y : V, w x y * (2 * (f x)^2 + 2 * (f y)^2) :=
        sum_le_sum fun x _ => sum_le_sum fun y _ => hj x y
      _ = _ := by
        simp only [mul_add, sum_add_distrib]
        have left : (∑ x : V, ∑ y : V, w x y * (2 * (f x)^2)) = 2 * D := by
          simp_rw [← sum_mul, hd]
          unfold D
          rw [mul_sum]
          exact sum_congr rfl fun x _ => by ring
        have right : (∑ x : V, ∑ y : V, w x y * (2 * (f y)^2)) = 2 * D := by
          rw [sum_comm]
          refine Eq.trans (sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_) left
          rw [hsym y x]
        rw [left, right]
        ring
  have hC := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (V × V)) g j
  rw [hV] at hC
  have hco := weighted_sum_le_variation w d A h hcut (fun x => (f x)^2)
    (fun x => sq_nonneg _) (fun x hx => hA x (lt_of_le_of_ne (hf x) (by
      intro hz
      simp [← hz] at hx)))
  change h * D ≤ _ at hco
  have hCV : (h*D)^2 ≤ (variation w (fun x => (f x)^2))^2 :=
    pow_le_pow_left₀ (mul_nonneg hh hD) hco 2
  have hAll : (h*D)^2 ≤ energy w f * (4*D) :=
    (hCV.trans hC).trans (mul_le_mul hG hJ
      (sum_nonneg fun _ _ => sq_nonneg _) hE)
  change h^2 * D ≤ 4 * energy w f
  apply (mul_le_mul_iff_right₀ hDpos).mp
  calc
    D * (h^2 * D) = (h*D)^2 := by ring
    _ ≤ energy w f * (4*D) := hAll
    _ = D * (4 * energy w f) := by ring

omit [DecidableEq V] in
/-- A finite weighted median leaves at most half of the total weight strictly on either side. -/
theorem exists_weighted_median [Nonempty V] (d f : V → ℝ) (hd : ∀ x, 0 ≤ d x) :
    ∃ m : ℝ, 2 * (∑ x with f x < m, d x) ≤ ∑ x : V, d x ∧
      2 * (∑ x with m < f x, d x) ≤ ∑ x : V, d x := by
  classical
  let D := ∑ x : V, d x
  let Q (m : ℝ) := (univ : Finset V).filter (fun x => f x ≤ m)
  let U := ((univ : Finset V).image f).filter (fun m => D ≤ 2 * (∑ x ∈ Q m, d x))
  have hD : 0 ≤ D := sum_nonneg fun x _ => hd x
  have hU : U.Nonempty := by
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (univ : Finset V) f univ_nonempty
    have hpQ : Q (f p) = univ := by
      ext x
      simp [Q, hmax x (mem_univ _)]
    exact ⟨f p, mem_filter.mpr ⟨mem_image.mpr ⟨p, hp, rfl⟩, by rw [hpQ]; linarith⟩⟩
  obtain ⟨m, hm, hm_min⟩ := Finset.exists_min_image U id hU
  have hbelow := (mem_filter.mp hm).2
  refine ⟨m, ?_, ?_⟩
  · let R := (univ : Finset V).filter (fun x => f x < m)
    change 2 * (∑ x ∈ R, d x) ≤ D
    by_cases hR : R.Nonempty
    · obtain ⟨q, hq, hRq⟩ := Finset.exists_max_image R f hR
      have hqm : f q < m := (mem_filter.mp hq).2
      have hqQ : Q (f q) = R := by
        ext x
        simp only [Q, R, mem_filter_univ]
        exact ⟨fun h => h.trans_lt hqm, fun h => hRq x (mem_filter.mpr ⟨mem_univ _, h⟩)⟩
      by_contra! hgt
      have hqU : f q ∈ U :=
        mem_filter.mpr ⟨mem_image.mpr ⟨q, mem_univ _, rfl⟩, by rw [hqQ]; exact hgt.le⟩
      exact (not_lt_of_ge (hm_min _ hqU)) hqm
    · simp only [not_nonempty_iff_eq_empty.mp hR, sum_empty, mul_zero]
      exact hD
  · have hsum : (∑ x ∈ Q m, d x) + (∑ x with m < f x, d x) = D := by
      simpa only [Q, not_le] using
        (sum_filter_add_sum_filter_not (univ : Finset V) (fun x => f x ≤ m) d)
    change 2 * (∑ x with m < f x, d x) ≤ D
    linarith

/-- Conductance controls weighted variance on a finite symmetric kernel.
This form uses only real sums, so it can be applied to graph Laplacians or
to reversible Markov kernels without a spectral definition. -/
theorem conductance_imp_poincare [Nonempty V] (w : V → V → ℝ) (d : V → ℝ)
    (hw : ∀ x y, 0 ≤ w x y) (hsym : ∀ x y, w x y = w y x)
    (hd : ∀ x, (∑ y : V, w x y) = d x) {h : ℝ} (hh : 0 ≤ h)
    (hcut : ∀ S : Finset V, h * min (∑ x ∈ S, d x) (∑ x ∈ Sᶜ, d x) ≤ cut w S)
    (f : V → ℝ) (hmean : ∑ x : V, d x * f x = 0) :
    h^2 * (∑ x : V, d x * (f x)^2) ≤ 4 * energy w f := by
  classical
  have hdpos (x : V) : 0 ≤ d x := by rw [← hd]; exact sum_nonneg fun _ _ => hw _ _
  obtain ⟨m, hmedLower, hmedUpper⟩ := exists_weighted_median d f hdpos
  let P := (univ : Finset V).filter fun x => m < f x
  let Q := (univ : Finset V).filter fun x => f x < m
  let p (x : V) := max (f x - m) 0
  let q (x : V) := max (m - f x) 0
  have hsmall (A : Finset V) (hA : 2 * (∑ x ∈ A, d x) ≤ ∑ x : V, d x)
      (T : Finset V) (hTA : T ⊆ A) : h * (∑ x ∈ T, d x) ≤ cut w T := by
    have hle := sum_le_sum_of_subset_of_nonneg hTA (fun x _ _ => hdpos x)
    have hsplit := sum_add_sum_compl T d
    have hmin : (∑ x ∈ T, d x) ≤ ∑ x ∈ Tᶜ, d x := by linarith
    simpa only [min_eq_left hmin] using hcut T
  have hpA (x : V) (hx : 0 < p x) : x ∈ P := by
    simpa only [p, P, lt_max_iff, lt_self_iff_false, or_false, sub_pos, mem_filter_univ] using hx
  have hqA (x : V) (hx : 0 < q x) : x ∈ Q := by
    simpa only [q, Q, lt_max_iff, lt_self_iff_false, or_false, sub_pos, mem_filter_univ] using hx
  have hp := support_poincare w d hw hsym hd P hh (hsmall P hmedUpper) p
    (fun _ => le_max_right _ _) hpA
  have hq := support_poincare w d hw hsym hd Q hh (hsmall Q hmedLower) q
    (fun _ => le_max_right _ _) hqA
  have hparts (x : V) :
      p x - q x = f x - m ∧ (p x)^2 + (q x)^2 = (f x - m)^2 := by
    by_cases hx : m ≤ f x
    · simp only [p, q, max_eq_left (sub_nonneg.mpr hx), max_eq_right (sub_nonpos.mpr hx),
        sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, and_self]
    · have hx' := le_of_not_ge hx
      simp only [p, q, max_eq_left (sub_nonneg.mpr hx'), max_eq_right (sub_nonpos.mpr hx'),
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
      constructor <;> ring
  have hmass : (∑ x : V, d x * (f x)^2) ≤
      (∑ x : V, d x * (p x)^2) + ∑ x : V, d x * (q x)^2 := by
    rw [← sum_add_distrib]
    simp only [← mul_add, fun x => (hparts x).2]
    have hrewrite : (∑ x : V, d x * (f x - m)^2) =
        (∑ x : V, d x * (f x)^2) - (2*m) * (∑ x : V, d x * f x) +
          m^2 * (∑ x : V, d x) := by
      simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [hrewrite, hmean, mul_zero, sub_zero]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sum_nonneg fun x _ => hdpos x))
  have hterm (x y : V) : (p x - p y)^2 + (q x - q y)^2 ≤ (f x - f y)^2 := by
    have hprod : (p x - p y) * (q x - q y) ≤ 0 := by
      rcases le_total (f x) (f y) with hxy | hyx
      · exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (max_le_max (sub_le_sub_right hxy _) le_rfl))
          (sub_nonneg.mpr (max_le_max (sub_le_sub_left hxy _) le_rfl))
      · exact mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr (max_le_max (sub_le_sub_right hyx _) le_rfl))
          (sub_nonpos.mpr (max_le_max (sub_le_sub_left hyx _) le_rfl))
    have heq : f x - f y = (p x - p y) - (q x - q y) := by
      linarith only [(hparts x).1, (hparts y).1]
    rw [heq]
    nlinarith only [hprod]
  have henergy : energy w p + energy w q ≤ energy w f := by
    simp only [energy, ← sum_add_distrib, ← mul_add]
    exact sum_le_sum fun x _ => sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hterm x y) (hw x y)
  calc
    _ ≤ h^2 * ((∑ x : V, d x * (p x)^2) + ∑ x : V, d x * (q x)^2) :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg h)
    _ ≤ 4 * (energy w p + energy w q) := by linarith only [hp, hq]
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy (by norm_num)

end Erdos642FiniteCoarea

end Erdos642FiniteCoareaFile

section Erdos642BipartiteContractionFile

/- Variational contraction of a reversible bipartite finite Markov kernel. -/

namespace Erdos642BipartiteContraction

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V]

def scalar (d f g : V → ℝ) : ℝ := ∑ x : V, d x * f x * g x

def squareMass (d f : V → ℝ) : ℝ := ∑ x : V, d x * (f x)^2

def applyKernel (K : V → V → ℝ) (f : V → ℝ) (x : V) : ℝ :=
  ∑ y : V, K x y * f y

def centered (d sign f : V → ℝ) : Prop :=
  (∑ x : V, d x * f x) = 0 ∧ (∑ x : V, d x * (sign x * f x)) = 0

theorem applyKernel_add (K : V → V → ℝ) (f g : V → ℝ) (x : V) :
    applyKernel K (fun y => f y + g y) x = applyKernel K f x + applyKernel K g x := by
  simp only [applyKernel, mul_add, sum_add_distrib]

theorem applyKernel_sub (K : V → V → ℝ) (f g : V → ℝ) (x : V) :
    applyKernel K (fun y => f y - g y) x = applyKernel K f x - applyKernel K g x := by
  simp only [applyKernel, mul_sub, sum_sub_distrib]

theorem scalar_symm (d f g : V → ℝ) : scalar d f g = scalar d g f := by
  apply sum_congr rfl
  intro x _
  ring

theorem scalar_self (d f : V → ℝ) : scalar d f f = squareMass d f := by
  apply sum_congr rfl
  intro x _
  ring

theorem scalar_applyKernel_symm (d : V → ℝ) (K : V → V → ℝ)
    (hrev : ∀ x y, d x * K x y = d y * K y x) (f g : V → ℝ) :
    scalar d f (applyKernel K g) = scalar d (applyKernel K f) g := by
  simp only [scalar, applyKernel, mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  calc
    d y * f y * (K y x * g x) = (d y * K y x) * (f y * g x) := by ring
    _ = (d x * K x y) * (f y * g x) := by rw [hrev y x]
    _ = d x * (K x y * f y) * g x := by ring

theorem weighted_sum_applyKernel (d : V → ℝ) (K : V → V → ℝ)
    (hrev : ∀ x y, d x * K x y = d y * K y x) (hrow : ∀ x, ∑ y : V, K x y = 1)
    (f : V → ℝ) : (∑ x : V, d x * applyKernel K f x) = ∑ x : V, d x * f x := by
  simp only [applyKernel, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  calc
    _ = ∑ y : V, (d x * f x) * K x y := by
      apply sum_congr rfl
      intro y _
      calc
        d y * (K y x * f x) = (d y * K y x) * f x := by ring
        _ = (d x * f x) * K x y := by rw [hrev y x]; ring
    _ = _ := by rw [← mul_sum, hrow, mul_one]

theorem applyKernel_signed (K : V → V → ℝ) (sign f : V → ℝ)
    (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x) (x : V) :
    applyKernel K (fun y => sign y * f y) x = -sign x * applyKernel K f x := by
  simp only [applyKernel, mul_sum]
  apply sum_congr rfl
  intro y _
  by_cases he : K x y = 0
  · simp [he]
  · rw [hflip x y he]
    ring

theorem centered_applyKernel (d : V → ℝ) (K : V → V → ℝ) (sign f : V → ℝ)
    (hrev : ∀ x y, d x * K x y = d y * K y x) (hrow : ∀ x, ∑ y : V, K x y = 1)
    (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x)
    (hf : centered d sign f) : centered d sign (applyKernel K f) := by
  refine ⟨(weighted_sum_applyKernel d K hrev hrow f).trans hf.1, ?_⟩
  have he := weighted_sum_applyKernel d K hrev hrow (fun y => sign y * f y)
  simp only [applyKernel_signed K sign f hflip, neg_mul, mul_neg, sum_neg_distrib] at he
  linarith only [he, hf.2]

theorem energy_as_quadratic (d : V → ℝ) (K : V → V → ℝ)
    (hrev : ∀ x y, d x * K x y = d y * K y x) (hrow : ∀ x, ∑ y : V, K x y = 1) (f : V → ℝ) :
    Erdos642FiniteCoarea.energy (fun x y => d x * K x y) f =
      2 * squareMass d f - 2 * scalar d f (applyKernel K f) := by
  unfold Erdos642FiniteCoarea.energy
  have hterm (x y : V) : (d x * K x y) * (f x - f y)^2 =
      (d x * K x y) * (f x)^2 + (d x * K x y) * (f y)^2 -
        2 * (d x * f x * (K x y * f y)) := by ring
  have hleft : (∑ x : V, ∑ y : V, (d x * K x y) * (f x)^2) = squareMass d f := by
    unfold squareMass
    apply sum_congr rfl
    intro x _
    calc
      _ = ∑ y : V, (d x * (f x)^2) * K x y := by
        exact sum_congr rfl fun y _ => by ring
      _ = _ := by rw [← mul_sum, hrow, mul_one]
  have hright : (∑ x : V, ∑ y : V, (d x * K x y) * (f y)^2) = squareMass d f := by
    rw [sum_comm]
    refine Eq.trans (sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_) hleft
    rw [hrev y x]
  simp only [hterm, sum_sub_distrib, sum_add_distrib, hleft, hright, ← mul_sum]
  change squareMass d f + squareMass d f - 2 * scalar d f (applyKernel K f) =
    2 * squareMass d f - 2 * scalar d f (applyKernel K f)
  ring

theorem signed_squareMass (d sign f : V → ℝ) (hsign : ∀ x, (sign x)^2 = 1) :
    squareMass d (fun x => sign x * f x) = squareMass d f := by
  unfold squareMass
  simp only [mul_pow, hsign, one_mul]

theorem signed_scalar_applyKernel (d : V → ℝ) (K : V → V → ℝ) (sign f : V → ℝ)
    (hsign : ∀ x, (sign x)^2 = 1) (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x) :
    scalar d (fun x => sign x * f x) (applyKernel K (fun x => sign x * f x)) =
      -scalar d f (applyKernel K f) := by
  simp only [scalar, applyKernel_signed K sign f hflip, ← sum_neg_distrib]
  apply sum_congr rfl
  intro x _
  calc
    _ = -((sign x)^2 * (d x * f x * applyKernel K f x)) := by ring
    _ = _ := by rw [hsign, one_mul]

variable [DecidableEq V] [Nonempty V]

/-- The quadratic form of a bipartite kernel on vectors whose mean is zero
on each side is bounded in both signs by its conductance. -/
theorem rayleigh_abs_le (d : V → ℝ) (K : V → V → ℝ) (sign : V → ℝ)
    (hd : ∀ x, 0 ≤ d x) (hK : ∀ x y, 0 ≤ K x y)
    (hrev : ∀ x y, d x * K x y = d y * K y x) (hrow : ∀ x, ∑ y : V, K x y = 1)
    (hsign : ∀ x, (sign x)^2 = 1) (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x)
    {h : ℝ} (hh : 0 ≤ h)
    (hcut : ∀ S : Finset V, h * min (∑ x ∈ S, d x) (∑ x ∈ Sᶜ, d x) ≤
      Erdos642FiniteCoarea.cut (fun x y => d x * K x y) S)
    (f : V → ℝ) (hf : centered d sign f) :
    |scalar d f (applyKernel K f)| ≤ (1 - h^2/8) * squareMass d f := by
  have one_sided (g : V → ℝ) (hg : ∑ x : V, d x * g x = 0) :
      scalar d g (applyKernel K g) ≤ (1 - h^2/8) * squareMass d g := by
    have he := Erdos642FiniteCoarea.conductance_imp_poincare (fun x y => d x * K x y) d
      (fun x y => mul_nonneg (hd x) (hK x y)) hrev
      (fun x => by rw [← mul_sum, hrow, mul_one]) hh hcut g hg
    change h^2 * squareMass d g ≤ _ at he
    rw [energy_as_quadratic d K hrev hrow] at he
    linarith only [he]
  refine abs_le.mpr ⟨?_, one_sided f hf.1⟩
  have hneg := one_sided (fun x => sign x * f x) hf.2
  rw [signed_squareMass d sign f hsign, signed_scalar_applyKernel d K sign f hsign hflip] at hneg
  linarith only [hneg]

omit [DecidableEq V] [Nonempty V] in
/-- Polarization yields squared-norm contraction using only finite real sums. -/
theorem squared_norm_contraction (d : V → ℝ) (K : V → V → ℝ) (sign : V → ℝ)
    (hd : ∀ x, 0 ≤ d x) (hrev : ∀ x y, d x * K x y = d y * K y x)
    (hrow : ∀ x, ∑ y : V, K x y = 1)
    (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x)
    {a : ℝ} (ha : a ≤ 1)
    (hbound : ∀ f, centered d sign f →
      |scalar d f (applyKernel K f)| ≤ a * squareMass d f)
    (f : V → ℝ) (hf : centered d sign f) :
    squareMass d (applyKernel K f) ≤ a * squareMass d f := by
  let g := applyKernel K f
  have hg : centered d sign g := centered_applyKernel d K sign f hrev hrow hflip hf
  have hadd : centered d sign (fun x => f x + g x) := by
    constructor <;> simp only [mul_add, sum_add_distrib, hf.1, hf.2, hg.1, hg.2, zero_add]
  have hsub : centered d sign (fun x => f x - g x) := by
    constructor <;> simp only [mul_sub, sum_sub_distrib, hf.1, hf.2, hg.1, hg.2, sub_zero]
  have hsym : scalar d f (applyKernel K g) = squareMass d g := by
    rw [scalar_applyKernel_symm d K hrev, scalar_self]
  have hquad :
      scalar d (fun x => f x + g x) (applyKernel K (fun x => f x + g x)) -
        scalar d (fun x => f x - g x) (applyKernel K (fun x => f x - g x)) =
      4 * squareMass d g := by
    simp only [applyKernel_add, applyKernel_sub, scalar, ← sum_sub_distrib]
    calc
      _ = 2 * (scalar d f (applyKernel K g) + scalar d g g) := by
        simp only [scalar, mul_add, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun x _ => by dsimp only [g]; ring
      _ = _ := by rw [hsym, scalar_self]; ring
  have hmass : squareMass d (fun x => f x + g x) + squareMass d (fun x => f x - g x) =
      2 * (squareMass d f + squareMass d g) := by
    simp only [squareMass, mul_add, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by ring
  have hup := (abs_le.mp (hbound _ hadd)).2
  have hlo := (abs_le.mp (hbound _ hsub)).1
  have hboth : 4 * squareMass d g ≤ 2 * (a * (squareMass d f + squareMass d g)) := by
    rw [← hquad, ← mul_left_comm, ← hmass, mul_add]
    linarith only [hup, hlo]
  have hp : 0 ≤ squareMass d g := sum_nonneg fun x _ => mul_nonneg (hd x) (sq_nonneg _)
  have hscale := mul_le_mul_of_nonneg_right ha hp
  linarith only [hboth, hscale]

omit [DecidableEq V] [Nonempty V] in
/-- The k-step action on a payoff function, with the start vertex as argument. -/
def evolve (K : V → V → ℝ) (f : V → ℝ) : ℕ → V → ℝ
  | 0 => f
  | n + 1 => applyKernel K (evolve K f n)

omit [DecidableEq V] [Nonempty V] in
theorem evolve_sub (K : V → V → ℝ) (f g : V → ℝ) (k : ℕ) :
    evolve K (fun x => f x - g x) k = fun x => evolve K f k x - evolve K g k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    simp only [evolve, ih, applyKernel_sub]

omit [DecidableEq V] [Nonempty V] in
theorem evolve_centered (d : V → ℝ) (K : V → V → ℝ) (sign : V → ℝ)
    (hrev : ∀ x y, d x * K x y = d y * K y x) (hrow : ∀ x, ∑ y : V, K x y = 1)
    (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x)
    (f : V → ℝ) (hf : centered d sign f) (k : ℕ) :
    centered d sign (evolve K f k) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact centered_applyKernel d K sign _ hrev hrow hflip ih

omit [DecidableEq V] [Nonempty V] in
/-- Squared norm after k steps on the simultaneous mean-zero subspace. -/
theorem evolve_squareMass_le (d : V → ℝ) (K : V → V → ℝ) (sign : V → ℝ)
    (hd : ∀ x, 0 ≤ d x) (hrev : ∀ x y, d x * K x y = d y * K y x)
    (hrow : ∀ x, ∑ y : V, K x y = 1)
    (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hbound : ∀ f, centered d sign f →
      |scalar d f (applyKernel K f)| ≤ a * squareMass d f)
    (f : V → ℝ) (hf : centered d sign f) (k : ℕ) :
    squareMass d (evolve K f k) ≤ a^k * squareMass d f := by
  induction k with
  | zero => simp [evolve]
  | succ k ih =>
    have hcen := evolve_centered d K sign hrev hrow hflip f hf k
    calc
      _ ≤ a * squareMass d (evolve K f k) :=
        squared_norm_contraction d K sign hd hrev hrow hflip ha1 hbound _ hcen
      _ ≤ a * (a^k * squareMass d f) := mul_le_mul_of_nonneg_left ih ha
      _ = _ := by rw [pow_succ]; ring

omit [DecidableEq V] [Nonempty V] in
theorem applyKernel_sign (K : V → V → ℝ) (sign : V → ℝ)
    (hrow : ∀ x, ∑ y : V, K x y = 1)
    (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x) (x : V) :
    applyKernel K sign x = -sign x := by
  have hOne : applyKernel K (fun _ => 1) x = 1 := by simpa only [applyKernel, mul_one] using hrow x
  simpa only [mul_one, hOne] using applyKernel_signed K sign (fun _ => 1) hflip x

omit [DecidableEq V] [Nonempty V] in
theorem weighted_sign_zero (d : V → ℝ) (K : V → V → ℝ) (sign : V → ℝ)
    (hrev : ∀ x y, d x * K x y = d y * K y x)
    (hrow : ∀ x, ∑ y : V, K x y = 1)
    (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x) :
    (∑ x : V, d x * sign x) = 0 := by
  have he := weighted_sum_applyKernel d K hrev hrow sign
  simp only [applyKernel_sign K sign hrow hflip, mul_neg, sum_neg_distrib] at he
  linarith

omit [DecidableEq V] [Nonempty V] in
theorem evolve_affine_sign (K : V → V → ℝ) (sign : V → ℝ)
    (hrow : ∀ x, ∑ y : V, K x y = 1)
    (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x) (c s : ℝ) (k : ℕ) (u : V) :
    evolve K (fun x => c * (1 + sign x * s)) k u =
      c * (1 + (-1 : ℝ)^k * sign u * s) := by
  induction k generalizing u with
  | zero => simp [evolve]
  | succ k ih =>
    simp only [evolve, applyKernel, ih]
    have hterm (x : V) :
        K u x * (c * (1 + (-1 : ℝ)^k * sign x * s)) =
          c * K u x + c * ((-1 : ℝ)^k * s) * (K u x * sign x) := by ring
    simp only [hterm, sum_add_distrib, ← mul_sum, hrow u, mul_one]
    have hsign : (∑ x : V, K u x * sign x) = -sign u := applyKernel_sign K sign hrow hflip u
    rw [hsign, pow_succ]
    ring

omit [Nonempty V] in
/-- Pointwise mixing around the degree-weighted parity correction. -/
theorem evolve_point_error (d : V → ℝ) (K : V → V → ℝ) (sign : V → ℝ)
    (hd : ∀ x, 0 < d x)
    (hrev : ∀ x y, d x * K x y = d y * K y x) (hrow : ∀ x, ∑ y : V, K x y = 1)
    (hsign : ∀ x, (sign x)^2 = 1)
    (hflip : ∀ x y, K x y ≠ 0 → sign y = -sign x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hbound : ∀ f, centered d sign f →
      |scalar d f (applyKernel K f)| ≤ a * squareMass d f)
    (k : ℕ) (u v : V) :
    |evolve K (fun x => if x = v then 1 else 0) k u -
      (d v / ∑ x : V, d x) * (1 + (-1 : ℝ)^k * sign u * sign v)| ≤
        Real.sqrt (a^k * d v / d u) := by
  classical
  let D := ∑ x : V, d x
  let c := d v / D
  let p (x : V) : ℝ := if x = v then 1 else 0
  let b (x : V) := c * (1 + sign x * sign v)
  let f (x : V) := p x - b x
  have hD : 0 < D :=
    (hd v).trans_le (single_le_sum (f := d) (fun x _ => (hd x).le) (mem_univ v))
  have hc : c * D = d v := div_mul_cancel₀ _ hD.ne'
  have hsd := weighted_sign_zero d K sign hrev hrow hflip
  have hpsum : (∑ x : V, d x * p x) = d v := by simp [p, mul_ite]
  have hpSign : (∑ x : V, d x * (sign x * p x)) = d v * sign v := by simp [p, mul_ite]
  have hbTerm (x : V) : d x * b x = c * d x + (c * sign v) * (d x * sign x) := by
    dsimp only [b]
    ring
  have hbsum : (∑ x : V, d x * b x) = d v := by
    simp only [hbTerm, sum_add_distrib, ← mul_sum, hsd, mul_zero, add_zero]
    exact hc
  have hbSignTerm (x : V) : d x * (sign x * b x) =
      c * (d x * sign x) + (c * sign v) * d x := by
    dsimp only [b]
    linear_combination (c * sign v * d x) * hsign x
  have hbSign : (∑ x : V, d x * (sign x * b x)) = d v * sign v := by
    simp only [hbSignTerm, sum_add_distrib, ← mul_sum, hsd, mul_zero, zero_add]
    calc
      c * sign v * D = (c * D) * sign v := by ring
      _ = _ := by rw [hc]
  have hf : centered d sign f := by
    constructor <;> simp only [f, mul_sub, sum_sub_distrib, hpsum, hpSign, hbsum, hbSign, sub_self]
  have horthTerm (x : V) : d x * f x * b x =
      c * (d x * f x) + (c * sign v) * (d x * (sign x * f x)) := by
    dsimp only [b]
    ring
  have horth : scalar d f b = 0 := by
    simp only [scalar, horthTerm, sum_add_distrib, ← mul_sum, hf.1, hf.2, mul_zero, add_zero]
  have hpEq (x : V) : p x = f x + b x := by
    dsimp only [f]
    ring
  have hMassSplit : squareMass d p =
      squareMass d f + 2 * scalar d f b + squareMass d b := by
    simp only [squareMass, scalar, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    rw [hpEq x]
    ring
  have hpMass : squareMass d p = d v := by simp [squareMass, p, ite_pow, mul_ite]
  have hMass : squareMass d f ≤ d v := by
    have hnonneg : 0 ≤ squareMass d b := sum_nonneg fun x _ => mul_nonneg (hd x).le (sq_nonneg _)
    linarith only [hMassSplit, horth, hpMass, hnonneg]
  have he := evolve_squareMass_le d K sign (fun x => (hd x).le) hrev hrow hflip ha ha1
    hbound f hf k
  have hu : d u * (evolve K f k u)^2 ≤ squareMass d (evolve K f k) :=
    single_le_sum (fun x _ => mul_nonneg (hd x).le (sq_nonneg _)) (mem_univ u)
  have hsq : (evolve K f k u)^2 ≤ a^k * d v / d u :=
    (le_div_iff₀ (hd u)).mpr (by
      rw [mul_comm]
      exact hu.trans (he.trans (mul_le_mul_of_nonneg_left hMass (pow_nonneg ha _))))
  have habs := Real.le_sqrt_of_sq_le
    (show |evolve K f k u|^2 ≤ a^k * d v / d u by simpa only [sq_abs] using hsq)
  change |evolve K (fun x => p x - b x) k u| ≤ _ at habs
  simp only [evolve_sub, b, evolve_affine_sign K sign hrow hflip] at habs
  exact habs

end Erdos642BipartiteContraction

end Erdos642BipartiteContractionFile

section Erdos642ExpansionConductanceFile

/- Finite cut conductance for the expanding graphs in Erdős 642. -/

namespace Erdos642ExpansionConductance

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A neighborhood count regarded as a weight. -/
def adjWeight (u v : V) : ℝ := if G.Adj u v then 1 else 0

/-- The unnormalized degree measure of a vertex set. -/
def degreeVolume (S : Finset V) : ℝ := ∑ v ∈ S, (G.degree v : ℝ)

/-- Every crossing edge is counted once, oriented from the set to its complement. -/
def cutCapacity (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, adjWeight G u v

omit [Fintype V] [DecidableEq V] in
theorem adjWeight_nonneg (u v : V) : 0 ≤ adjWeight G u v := by
  unfold adjWeight
  split <;> positivity

omit [Fintype V] [DecidableEq V] in
theorem adjWeight_symm (u v : V) : adjWeight G u v = adjWeight G v u := by
  simp only [adjWeight, adj_comm (G := G) (u := u) (v := v)]

omit [DecidableEq V] in
theorem sum_adjWeight (u : V) : ∑ v : V, adjWeight G u v = (G.degree u : ℝ) := by
  unfold adjWeight
  simp only [← Finset.sum_filter, ← G.neighborFinset_eq_filter,
    Finset.sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree, mul_one]

theorem cutCapacity_compl (S : Finset V) : cutCapacity G Sᶜ = cutCapacity G S := by
  unfold cutCapacity
  rw [compl_compl, sum_comm]
  simp only [adjWeight_symm G]

theorem cutCapacity_eq_ncard (S : Finset V) :
    cutCapacity G S =
      ({e ∈ G.edgeSet | ∃ u v : V, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}.ncard : ℝ) := by
  classical
  let pairs := (S ×ˢ Sᶜ).filter (fun uv : V × V => G.Adj uv.1 uv.2)
  let m (uv : V × V) : Sym2 V := s(uv.1, uv.2)
  have hpairs : cutCapacity G S = (pairs.card : ℝ) := by
    rw [show (pairs.card : ℝ) = ∑ x ∈ pairs, (1 : ℝ) by simp]
    dsimp only [pairs, cutCapacity, adjWeight]
    rw [sum_filter, sum_product]
  have hinj : Set.InjOn m (pairs : Set (V × V)) := by
    rintro ⟨u, v⟩ huv ⟨x, y⟩ hxy heq
    change s(u, v) = s(x, y) at heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · have ha := mem_product.mp (mem_filter.mp huv).1
      have hb := mem_product.mp (mem_filter.mp hxy).1
      exact ((mem_compl.mp hb.2) ha.1).elim
  rw [hpairs, ← card_image_of_injOn hinj, Set.ncard_eq_toFinset_card]
  congr 2
  ext e
  simp only [mem_image, Set.Finite.mem_toFinset, Set.mem_sep_iff]
  constructor
  · rintro ⟨⟨u, v⟩, huv, rfl⟩
    have hp := mem_product.mp (mem_filter.mp huv).1
    exact ⟨(G.mem_edgeSet).mpr (mem_filter.mp huv).2,
      u, v, hp.1, mem_compl.mp hp.2, rfl⟩
  · rintro ⟨he, u, v, hu, hv, rfl⟩
    exact ⟨(u, v), mem_filter.mpr ⟨mem_product.mpr ⟨hu, mem_compl.mpr hv⟩,
      (G.mem_edgeSet).mp he⟩, rfl⟩

/-- Cardinal expansion and a uniform degree upper bound imply volume conductance. -/
theorem min_volume_conductance {a D : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    (hmax : ∀ x, (G.degree x : ℝ) ≤ D)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V → a * S.card ≤ cutCapacity G S)
    (S : Finset V) :
    (a / D) * min (degreeVolume G S) (degreeVolume G Sᶜ) ≤ cutCapacity G S := by
  have hvol (T : Finset V) : degreeVolume G T ≤ D * T.card := by
    calc
      degreeVolume G T ≤ ∑ _ ∈ T, D := sum_le_sum fun v _ => hmax v
      _ = _ := by simp [mul_comm]
  have hcoef : 0 ≤ a / D := div_nonneg ha hD.le
  have hcancel (T : Finset V) : (a / D) * (D * T.card) = a * T.card := by
    field_simp
  by_cases hs : 2 * S.card ≤ Fintype.card V
  · exact (mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (hvol S)) hcoef).trans
      ((hcancel S).le.trans (hexp S hs))
  · have hsc : 2 * Sᶜ.card ≤ Fintype.card V := by
      rw [card_compl]
      omega
    rw [← cutCapacity_compl G S]
    exact (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (hvol Sᶜ)) hcoef).trans
      ((hcancel Sᶜ).le.trans (hexp Sᶜ hsc))

/-- The exact conductance form of the average-degree expansion in DMMS. -/
theorem conductance_of_average_degree_expansion [Nonempty V]
    {lam K av : ℝ} (hlam : 0 ≤ lam) (hK : 0 < K) (hav : 0 < av)
    (hMean : av = (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ))
    (hreg : ∀ x y, (G.degree x : ℝ) ≤ K * (G.degree y : ℝ))
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      lam * av * S.card ≤
        ({e ∈ G.edgeSet | ∃ u v : V, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}.ncard : ℝ))
    (S : Finset V) :
    (lam / K) * min (degreeVolume G S) (degreeVolume G Sᶜ) ≤ cutCapacity G S := by
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hmax (x : V) : (G.degree x : ℝ) ≤ K * av := by
    calc
      (G.degree x : ℝ) = (∑ _ : V, (G.degree x : ℝ)) / Fintype.card V := by
        simp [hV.ne']
      _ ≤ (∑ y : V, K * (G.degree y : ℝ)) / Fintype.card V :=
        div_le_div_of_nonneg_right (sum_le_sum fun y _ => hreg x y) hV.le
      _ = K * av := by rw [← mul_sum, hMean, mul_div_assoc]
  have hratio : (lam * av) / (K * av) = lam / K := by
    field_simp
  rw [← hratio]
  apply min_volume_conductance G (mul_nonneg hlam hav.le) (mul_pos hK hav) hmax _ S
  intro T hT
  rw [cutCapacity_eq_ncard]
  exact hexp T hT

end Erdos642ExpansionConductance

end Erdos642ExpansionConductanceFile

section Erdos642WalkMixingFile

/- Quantitative mixing of the finite graph walk, including its parity correction. -/

namespace Erdos642WalkMixing

open Finset SimpleGraph
open scoped BigOperators

/-- A conservative integral mixing scale leaves room for rounding. -/
theorem sqrt_error_at_scale {L M r : ℝ} (hL : 1 ≤ L) (hM : 100 ≤ M)
    (hr : 0 ≤ r) (hr100 : r ≤ 100) {t : ℕ}
    (ht : 10^9 * L^2 * Real.log M ≤ (t : ℝ)) :
    Real.sqrt ((1 - (1 / (1000*L))^2/8)^t * r) ≤ 1 / M^2 := by
  let z := (1 / (1000*L))^2 / 8
  have hL₀ : 0 < L := by linarith
  have hM₀ : 0 < M := by linarith
  have hlog : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hz : z = 1 / (8000000 * L^2) := by
    dsimp only [z]
    field_simp
    ring
  have hden : (0 : ℝ) < 8000000 * L^2 := by positivity
  have hz1 : z ≤ 1 := by
    rw [hz]
    apply (div_le_one hden).mpr
    nlinarith only [hL, sq_nonneg (L - 1)]
  have hzt : 8 * Real.log M ≤ z * (t : ℝ) := by
    rw [hz, one_div_mul_eq_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _ = 64000000 * L^2 * Real.log M := by ring
      _ ≤ 10^9 * L^2 * Real.log M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg L)) hlog
      _ ≤ _ := ht
  have hpow : (1-z)^t ≤ Real.exp (-(8*Real.log M)) := by
    calc
      _ ≤ Real.exp (-z)^t := pow_le_pow_left₀ (sub_nonneg.mpr hz1) (by
        simpa only [neg_add_eq_sub] using Real.add_one_le_exp (-z)) _
      _ = Real.exp (-(z*(t:ℝ))) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg hzt)
  have hexp : Real.exp (-(8*Real.log M)) = 1 / M^8 := by
    rw [Real.exp_neg, show (8 : ℝ) * Real.log M = (8 : ℕ) * Real.log M from rfl,
      Real.exp_nat_mul, Real.exp_log hM₀, one_div]
  change Real.sqrt ((1-z)^t * r) ≤ 1 / M^2
  apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc
    _ ≤ Real.exp (-(8*Real.log M)) * 100 :=
      mul_le_mul hpow hr100 hr (Real.exp_nonneg _)
    _ = 100 / M^8 := by rw [hexp]; ring
    _ ≤ (1 / M^2)^2 := by
      rw [div_pow, one_pow, ← pow_mul]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      norm_num only [Nat.reduceMul, one_mul]
      have hM4 : 100 ≤ M^4 := hM.trans
        (by simpa only [pow_one] using (pow_le_pow_right₀ (show 1 ≤ M by linarith)
          (by decide : (1 : ℕ) ≤ 4)))
      calc
        _ ≤ M^4 * M^4 := mul_le_mul_of_nonneg_right hM4 (by positivity)
        _ = _ := by ring

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem evolve_point_eq_walkWeight (t : ℕ) (u v : V) :
    Erdos642BipartiteContraction.evolve (Erdos642RandomWalkKernel.step G)
      (fun x => if x = v then 1 else 0) t u =
      Erdos642RandomWalkKernel.walkWeight G t u v := by
  induction t generalizing u with
  | zero => rfl
  | succ t ih =>
    simp only [Erdos642BipartiteContraction.evolve,
      Erdos642BipartiteContraction.applyKernel, Erdos642RandomWalkKernel.walkWeight_succ, ih]

lemma sign_of_fin_two (i : Fin 2) : (((-1 : ℝ)^i.val)^2) = 1 := by
  fin_cases i <;> norm_num

lemma sign_flip_of_fin_two {i j : Fin 2} (h : i ≠ j) :
    (-1 : ℝ)^j.val = -((-1 : ℝ)^i.val) := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- Pointwise walk mixing on the parity-compatible side of a bipartite graph. -/
theorem parity_walk_error [Nonempty V] (C : G.Coloring (Fin 2)) (hPos : ∀ u, 0 < G.degree u)
    {h : ℝ} (hh : 0 ≤ h) (hupper : h^2 ≤ 8)
    (hcut : ∀ S : Finset V, h * min
        (Erdos642ExpansionConductance.degreeVolume G S)
        (Erdos642ExpansionConductance.degreeVolume G Sᶜ) ≤
      Erdos642ExpansionConductance.cutCapacity G S)
    (t : ℕ) (u v : V) (hparity : ((C u).val + (C v).val + t) ≡ 0 [MOD 2]) :
    |Erdos642RandomWalkKernel.walkWeight G t u v -
        (2 * (G.degree v : ℝ) / ∑ x : V, (G.degree x : ℝ))| ≤
      Real.sqrt ((1 - h^2/8)^t * (G.degree v : ℝ) / (G.degree u : ℝ)) := by
  let d (x : V) := (G.degree x : ℝ)
  let K := Erdos642RandomWalkKernel.step G
  let sign (x : V) := (-1 : ℝ)^(C x).val
  have hd (x : V) : 0 < d x := by
    change (0 : ℝ) < (G.degree x : ℝ)
    exact_mod_cast hPos x
  have hK (x y : V) : 0 ≤ K x y := Erdos642RandomWalkKernel.step_nonneg G x y
  have hrev (x y : V) : d x * K x y = d y * K y x := by
    simpa only [d, K, Erdos642RandomWalkKernel.walkWeight_one] using
      Erdos642RandomWalkKernel.walkWeight_balance G hPos 1 x y
  have hrow (x : V) : ∑ y : V, K x y = 1 := Erdos642RandomWalkKernel.sum_step G hPos x
  have hsign (x : V) : (sign x)^2 = 1 := sign_of_fin_two (C x)
  have hflip (x y : V) (hxy : K x y ≠ 0) : sign y = -sign x := by
    apply sign_flip_of_fin_two
    apply C.map_adj
    exact (Erdos642RandomWalkKernel.step_pos_iff_adj G x y).mp
      (lt_of_le_of_ne (hK x y) (Ne.symm hxy))
  have hw (x y : V) : d x * K x y = Erdos642ExpansionConductance.adjWeight G x y := by
    by_cases ha : G.Adj x y <;>
      simp [d, K, Erdos642RandomWalkKernel.step, Erdos642ExpansionConductance.adjWeight, ha, (hd x).ne']
  have hcut' (S : Finset V) : h * min (∑ x ∈ S, d x) (∑ x ∈ Sᶜ, d x) ≤
      Erdos642FiniteCoarea.cut (fun x y => d x * K x y) S := by
    simpa only [Erdos642FiniteCoarea.cut, hw, Erdos642ExpansionConductance.cutCapacity,
      Erdos642ExpansionConductance.degreeVolume] using hcut S
  have hbound := Erdos642BipartiteContraction.rayleigh_abs_le d K sign
    (fun x => (hd x).le) hK hrev hrow hsign hflip hh hcut'
  have hErr := Erdos642BipartiteContraction.evolve_point_error d K sign hd hrev hrow hsign hflip
    (a := 1 - h^2/8) (by linarith only [hupper]) (by linarith only [sq_nonneg h]) hbound t u v
  rw [evolve_point_eq_walkWeight G] at hErr
  have heven : Even (t + (C u).val + (C v).val) := by
    rw [Nat.even_iff]
    change ((C u).val + (C v).val + t) % 2 = 0 % 2 at hparity
    simpa only [Nat.add_comm t ((C u).val + (C v).val), Nat.add_assoc] using hparity
  have hparity' : (-1 : ℝ)^t * sign u * sign v = 1 := by
    dsimp only [sign]
    rw [← pow_add, ← pow_add, heven.neg_one_pow]
  rw [hparity'] at hErr
  rw [show (d v / ∑ x : V, d x) * (1+1) = 2*d v / ∑ x : V, d x by ring] at hErr
  exact hErr

/-- The endpoint estimates used in the forest and self-avoidance arguments. -/
private theorem uniform_walk_bounds_with_slack [Nonempty V] (C : G.Coloring (Fin 2))
    (hPos : ∀ u, 0 < G.degree u)
    (hreg : ∀ u v, (G.degree u : ℝ) ≤ 100 * (G.degree v : ℝ))
    (hsize : 100 ≤ Fintype.card V) {L av : ℝ} (hL : 1 ≤ L)
    (hMean : av = (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ))
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      (1 / (10*L)) * av * S.card ≤
        ({e ∈ G.edgeSet | ∃ u v : V, u ∈ S ∧ v ∉ S ∧ e = s(u,v)}.ncard : ℝ)) :
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ 2 * 10^9 * L^2 * Real.log (Fintype.card V : ℝ) ∧
      ∀ t : ℕ, k ≤ t → ∀ u v : V,
        Erdos642RandomWalkKernel.walkWeight G t u v ≤ 400 / (Fintype.card V : ℝ) ∧
        (((C u).val + (C v).val + t) ≡ 0 [MOD 2] →
          1 / (100 * (Fintype.card V : ℝ)) ≤ Erdos642RandomWalkKernel.walkWeight G t u v) := by
  classical
  let M := (Fintype.card V : ℝ)
  let d (v : V) := (G.degree v : ℝ)
  let D := ∑ x : V, d x
  let h := 1 / (1000*L)
  have hM : 100 ≤ M := by
    change (100 : ℝ) ≤ (Fintype.card V : ℝ)
    exact_mod_cast hsize
  have hM₀ : 0 < M := by linarith
  have hL₀ : 0 < L := by linarith
  have hd (v : V) : 0 < d v := by
    change (0 : ℝ) < (G.degree v : ℝ)
    exact_mod_cast hPos v
  have hD : 0 < D := by
    inhabit V
    exact (hd default).trans_le (single_le_sum (f := d) (fun x _ => (hd x).le)
      (mem_univ default))
  have hav : 0 < av := by rw [hMean]; exact div_pos hD hM₀
  have hcut (S : Finset V) :
      h * min (Erdos642ExpansionConductance.degreeVolume G S)
          (Erdos642ExpansionConductance.degreeVolume G Sᶜ) ≤
        Erdos642ExpansionConductance.cutCapacity G S := by
    have he := Erdos642ExpansionConductance.conductance_of_average_degree_expansion G
      (lam := 1/(10*L)) (K := 100) (by positivity) (by norm_num) hav hMean hreg hexp S
    rw [show (1 / (10 * L))/100 = h by dsimp only [h]; ring] at he
    exact he
  have hh₀ : 0 < h := by dsimp only [h]; positivity
  have hh1 : h ≤ 1 := by dsimp only [h]; exact (div_le_one (by positivity)).2 (by linarith)
  have hh8 : h^2 ≤ 8 := by nlinarith [mul_nonneg hh₀.le (sub_nonneg.mpr hh1)]
  have hLog : 1 ≤ Real.log M := by
    apply (Real.le_log_iff_exp_le hM₀).2
    linarith only [Real.exp_one_lt_d9, hM]
  let p := 10^9 * L^2 * Real.log M
  let k := ⌈p⌉₊
  have hp : 1 ≤ p := by
    have hl : 1 ≤ L^2 := by nlinarith only [hL, sq_nonneg (L - 1)]
    dsimp only [p]
    have hcoeff : (1:ℝ) ≤ 10^9 * L^2 := by nlinarith only [hl]
    simpa only [mul_one] using mul_le_mul hcoeff hLog (by norm_num) (by positivity)
  have hkreal : p ≤ (k:ℝ) := Nat.le_ceil p
  have hk : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) := (by linarith : (0:ℝ) < p).trans_le hkreal
    exact_mod_cast this
  refine ⟨k, hk, ?_, ?_⟩
  · have hceil : (k : ℝ) < p + 1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ p)
    change (k : ℝ) ≤ 2 * 10^9 * L^2 * Real.log M
    have hratio : 2 * 10^9 * L^2 * Real.log M = 2*p := by dsimp only [p]; ring
    rw [hratio]
    linarith
  intro t ht u v
  have ht' : p ≤ (t : ℝ) := hkreal.trans (by exact_mod_cast ht)
  by_cases hp' : ((C u).val + (C v).val + t) ≡ 0 [MOD 2]
  · have hratio : d v / d u ≤ 100 := (div_le_iff₀ (hd u)).2 (hreg v u)
    have he := (parity_walk_error G C hPos hh₀.le hh8 hcut t u v hp').trans (by
      simpa only [h, d, div_eq_mul_inv, mul_assoc] using
        sqrt_error_at_scale hL hM (div_nonneg (hd v).le (hd u).le) hratio ht')
    change |Erdos642RandomWalkKernel.walkWeight G t u v - 2*d v/D| ≤ 1/M^2 at he
    have hlo : D ≤ M * (100 * d v) := by
      calc
        D ≤ ∑ _ : V, 100 * d v := sum_le_sum fun u _ => hreg u v
        _ = _ := by simp [M]
    have hhi : M * d v ≤ 100 * D := by
      calc
        M * d v = ∑ _ : V, d v := by simp [M]
        _ ≤ ∑ x : V, 100 * d x := sum_le_sum fun x _ => hreg v x
        _ = _ := by rw [← mul_sum]
    have hloBase : 2/(100*M) ≤ 2*d v/D :=
      (div_le_div_iff₀ (by positivity) hD).2 (by nlinarith only [hlo])
    have hhiBase : 2*d v/D ≤ 200/M :=
      (div_le_div_iff₀ hD hM₀).2 (by nlinarith only [hhi])
    have hsmall : 1/M^2 ≤ 1/(100*M) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [mul_le_mul_of_nonneg_right hM hM₀.le]
    have hlarge : 1/(100*M) ≤ 200/M := by
      apply (div_le_div_iff₀ (by positivity) hM₀).2
      linarith
    have hl' : 2/(100*M) = 2*(1/(100*M)) := by ring
    have hh' : 400/M = 2*(200/M) := by ring
    obtain ⟨hleft, hright⟩ := abs_le.mp he
    change Erdos642RandomWalkKernel.walkWeight G t u v ≤ 400/M ∧
      (_ → 1/(100*M) ≤ Erdos642RandomWalkKernel.walkWeight G t u v)
    rw [hh']
    refine ⟨by linarith only [hright, hhiBase, hsmall, hlarge], fun _ => ?_⟩
    linarith only [hleft, hsmall, hl', hloBase]
  · have hwrong : ((C u).val + (C v).val + t) ≡ 1 [MOD 2] := by
      change ((C u).val + (C v).val + t) % 2 ≠ 0 % 2 at hp'
      change ((C u).val + (C v).val + t) % 2 = 1 % 2
      omega
    rw [Erdos642RandomWalkKernel.walkWeight_zero_of_wrong_parity G C t u v hwrong]
    exact ⟨by positivity, fun q => (hp' q).elim⟩

/-- An odd common stride ensures each residue sequence alternates bipartition sides. -/
theorem uniform_walk_bounds_odd [Nonempty V] (C : G.Coloring (Fin 2)) (hPos : ∀ u, 0 < G.degree u)
    (hreg : ∀ u v, (G.degree u : ℝ) ≤ 100 * (G.degree v : ℝ))
    (hsize : 100 ≤ Fintype.card V) {L av : ℝ} (hL : 1 ≤ L)
    (hMean : av = (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ))
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      (1 / (10*L)) * av * S.card ≤
        ({e ∈ G.edgeSet | ∃ u v : V, u ∈ S ∧ v ∉ S ∧ e = s(u,v)}.ncard : ℝ)) :
    ∃ k : ℕ, 0 < k ∧ Odd k ∧ (k : ℝ) ≤ 10^10 * L^2 * Real.log (Fintype.card V : ℝ) ∧
      ∀ t : ℕ, k ≤ t → ∀ u v : V,
        Erdos642RandomWalkKernel.walkWeight G t u v ≤ 400 / (Fintype.card V : ℝ) ∧
        (((C u).val + (C v).val + t) ≡ 0 [MOD 2] →
          1 / (100 * (Fintype.card V : ℝ)) ≤ Erdos642RandomWalkKernel.walkWeight G t u v) := by
  obtain ⟨j, hj, hjBound, hjMix⟩ :=
    uniform_walk_bounds_with_slack G C hPos hreg hsize hL hMean hexp
  refine ⟨2*j+1, by omega, ⟨j, rfl⟩, ?_, fun t ht => hjMix t (by omega)⟩
  let M := (Fintype.card V : ℝ)
  have hM : (100 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hsize
  have hLog : 1 ≤ Real.log M := by
    apply (Real.le_log_iff_exp_le (by dsimp [M]; linarith)).2
    dsimp only [M]
    linarith only [Real.exp_one_lt_d9, hM]
  have hUnit : 1 ≤ 10^9 * L^2 * Real.log M := by
    have hLp : 1 ≤ L^2 := by nlinarith only [hL, sq_nonneg (L-1)]
    have hc : (1 : ℝ) ≤ 10^9 * L^2 := by nlinarith only [hLp]
    simpa only [mul_one] using mul_le_mul hc hLog (by norm_num) (by positivity)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  change 2 * (j : ℝ) + 1 ≤ 10^10 * L^2 * Real.log M
  change (j : ℝ) ≤ 2 * 10^9 * L^2 * Real.log M at hjBound
  nlinarith only [hjBound, hUnit]

theorem uniform_walk_bounds [Nonempty V] (C : G.Coloring (Fin 2)) (hPos : ∀ u, 0 < G.degree u)
    (hreg : ∀ u v, (G.degree u : ℝ) ≤ 100 * (G.degree v : ℝ))
    (hsize : 100 ≤ Fintype.card V) {L av : ℝ} (hL : 1 ≤ L)
    (hMean : av = (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ))
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      (1 / (10*L)) * av * S.card ≤
        ({e ∈ G.edgeSet | ∃ u v : V, u ∈ S ∧ v ∉ S ∧ e = s(u,v)}.ncard : ℝ)) :
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ 10^10 * L^2 * Real.log (Fintype.card V : ℝ) ∧
      ∀ t : ℕ, k ≤ t → ∀ u v : V,
        Erdos642RandomWalkKernel.walkWeight G t u v ≤ 400 / (Fintype.card V : ℝ) ∧
        (((C u).val + (C v).val + t) ≡ 0 [MOD 2] →
          1 / (100 * (Fintype.card V : ℝ)) ≤ Erdos642RandomWalkKernel.walkWeight G t u v) := by
  obtain ⟨k, hk, _, hBound, hMix⟩ :=
    uniform_walk_bounds_odd G C hPos hreg hsize hL hMean hexp
  exact ⟨k, hk, hBound, hMix⟩

end Erdos642WalkMixing

end Erdos642WalkMixingFile

section Erdos642ColoredForestsFile

/- Star packings in either orientation of the same colored graph. -/

namespace Erdos642ColoredForests

open Finset SimpleGraph Filter Erdos642StarForest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The vertices of either color in a fixed two-coloring. -/
def colorClass (C : G.Coloring (Fin 2)) (c : Fin 2) : Finset V :=
  univ.filter fun v => C v = c

omit [DecidableEq V] in
@[simp] theorem mem_colorClass (C : G.Coloring (Fin 2)) (c : Fin 2) (v : V) :
    v ∈ colorClass C c ↔ C v = c := by simp [colorClass]

/-- The two colors form a bipartition in either order. -/
theorem class_bipartition (C : G.Coloring (Fin 2)) (c : Fin 2) :
    G.IsBipartiteWith (colorClass C c : Set V) (colorClass C (1 - c) : Set V) ∧
    colorClass C c ∪ colorClass C (1 - c) = univ := by
  have hOther (i : Fin 2) : i ≠ c ↔ i = 1 - c := by
    fin_cases i <;> fin_cases c <;> decide
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Set.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_coe, mem_colorClass, ← hOther] at hv hv'
    exact hv' hv
  · intro u v huv
    have huv' : C u ≠ C v := C.valid huv
    simp only [Finset.mem_coe, mem_colorClass, ← hOther]
    by_cases h : C u = c
    · exact Or.inl ⟨h, fun hv => huv' (h.trans hv.symm)⟩
    · exact Or.inr ⟨h, by
        by_contra hh
        exact huv' ((hOther _).mp h |>.trans ((hOther _).mp hh).symm)⟩
  · ext v
    simpa only [Finset.mem_union, mem_colorClass, ← hOther, Finset.mem_univ, iff_true] using
      (em (C v = c))

/-- Orient the DMMS star forests so that their roots have the prescribed color. -/
theorem exists_color_packings (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : G.Coloring (Fin 2)) (c : Fin 2) {d : ℕ} (hd : 10000000 ≤ d)
    (hMin : ∀ v, d ≤ G.degree v) (hMax : ∀ v, G.degree v ≤ 100 * d) :
    ∃ P : Fin (d / 10) → Finset (V × Finset V),
      Pairwise (fun i j => Disjoint ((P i).image Prod.fst) ((P j).image Prod.fst)) ∧
      ∀ i, (P i).card = Fintype.card V / (100000 * d) ∧
        IsPacking ((univ ×ˢ univ).filter (fun p : V × V => G.Adj p.1 p.2))
          (colorClass C c) (colorClass C (1 - c)) (d / 10000000) (P i) := by
  obtain ⟨hbip, hcover⟩ := class_bipartition C c
  obtain ⟨P, hpair, hP⟩ := Erdos642ForestRounding.exists_indexed_star_forests G hbip hcover hd hMin hMax
  refine ⟨P, hpair, fun i => ⟨(hP i).1, ?_, (hP i).2.2⟩⟩
  intro p hp
  obtain ⟨hroot, hleaf, hcard, hadj⟩ := (hP i).2.1 p hp
  exact ⟨hroot, hleaf, hcard, fun y hy => by simpa using hadj y hy⟩

end Erdos642ColoredForests

end Erdos642ColoredForestsFile

section Erdos642BankEventsFile

/- The two aligned banks of the same colored random walk. -/

namespace Erdos642BankEvents

open Finset SimpleGraph
open Erdos642WalkTrace Erdos642TraceWindows Erdos642RandomWalkKernel
open Erdos642BankProbability Erdos642BankWindows Erdos642ColoredForests
open Erdos642StarForest Erdos642ManyForestsSampling

variable {V I : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def bankEdges (C : G.Coloring (Fin 2)) (J : Finset I)
    (P : Fin 2 → I → Finset (V × Finset V)) (R : ℝ)
    (stride N : ℕ) (hs : 0 < stride) (c : Fin 2) (p q : Fin (N*stride) → V) :
    Finset (Sym2 V) :=
  let S := bankSeen stride N hs (colorClass C c) p
  let T := bankSeen stride N hs (colorClass C (1-c)) q
  crossEdges G (goodRoots J (P c) S R ∩ T) S

omit [Fintype V] [DecidableEq V] in
theorem other_color {G : SimpleGraph V} (C : G.Coloring (Fin 2)) {u v : V}
    (h : C u ≠ C v) : C u = 1-C v := by
  revert h
  generalize C u = a
  generalize C v = b
  fin_cases a <;> fin_cases b <;> decide

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem disjoint_colorClasses (C : G.Coloring (Fin 2)) (c : Fin 2) :
    Disjoint (colorClass C (1-c)) (colorClass C c) := by
  rw [Finset.disjoint_left]
  intro v hv hw
  simp only [mem_colorClass] at hv hw
  have hne : c ≠ 1-c := by fin_cases c <;> decide
  exact hne (hw.symm.trans hv)

/-- The first bank chooses its forest orientation from its starting color.
An odd gap then places the second bank on the opposite color, where it samples
the recovered roots. The resulting edge event is independent of either start. -/
theorem two_windows_edges_failure_le (C : G.Coloring (Fin 2))
    (hPos : ∀ v, 0 < G.degree v)
    {E : Finset (V × V)} {ell : ℕ} (J : Finset I)
    (P : Fin 2 → I → Finset (V × Finset V))
    (hP : ∀ c, ∀ i ∈ J, IsPacking E (colorClass C (1-c)) (colorClass C c) ell (P c i))
    (hRoots : ∀ c, (J : Set I).PairwiseDisjoint (fun i => (P c i).image Prod.fst))
    (hEdge : ∀ e ∈ E, G.Adj e.1 e.2)
    (aStar : ℝ) (hStars : ∀ c, ∀ i ∈ J, aStar ≤ ((P c i).card : ℝ))
    (t a gap k N : ℕ) (hk : 0 < k) (hGap : Odd gap)
    (hWindow : a+(N*(2*k)+(gap+N*(2*k))) ≤ t)
    (x : V) (ρ prob s threshold : ℝ)
    (hρ : 0 ≤ ρ) (hρB : ∀ c, ρ * ((colorClass C c).card : ℝ) ≤ 1)
    (hpoint : ∀ c, ∀ u v, u ∈ colorClass C c → v ∈ colorClass C c →
      ρ ≤ walkWeight G (2*k) u v)
    (hN : (N : ℝ) * ρ ≤ 4)
    (hScale : 4 ≤ (ell : ℝ) * ((N : ℝ) * ρ / 8))
    (hprob0 : 0 ≤ prob) (hprob1 : prob ≤ 1)
    (hbudget : ∀ Q : ℝ, (J.card : ℝ)*aStar/2 ≤ Q → prob ≤ ρ*(Q-s))
    (hs : s ≤ (N : ℝ)*prob/4)
    (hThreshold : threshold ≤ s * ((ell : ℝ) * ((N : ℝ) * ρ / 8))) :
    let R := (ell : ℝ) * ((N : ℝ) * ρ / 8)
    eventMass (step G) t x (fun p => ¬ ∃ c : Fin 2,
      threshold ≤ ((bankEdges G C J P R (2*k) N (by omega) c
        (sliceTrace t a (N*(2*k)) (by omega) p)
        (sliceTrace t (a+N*(2*k)+gap) (N*(2*k)) (by omega) p)).card : ℝ)) ≤
      (J.card : ℝ) * Real.exp (-(aStar*R/4)) + Real.exp (-s) := by
  dsimp only
  let len := N*(2*k)
  let R := (ell : ℝ) * ((N : ℝ) * ρ / 8)
  let ε₁ := (J.card : ℝ) * Real.exp (-(aStar*R/4))
  let ε₂ := Real.exp (-s)
  let good (y : V) (p : Fin len → V) :=
    ¬ weakForests J (P (C y)) (bankSeen (2*k) N (by omega) (colorClass C (C y)) p) R
  let bad (p q : Fin len → V) :=
    ¬ ∃ c : Fin 2, threshold ≤ ((bankEdges G C J P R (2*k) N (by omega) c p q).card : ℝ)
  have hClosed (c : Fin 2) (u v : V) (hu : u ∈ colorClass C c)
      (hv : v ∉ colorClass C c) : walkWeight G (2*k) u v = 0 :=
    Erdos642SideSampling.even_walk_closed G C c k ((mem_colorClass C c u).mp hu)
      (fun he => hv ((mem_colorClass C c v).mpr he))
  have hFirst (y : V) : eventMass (step G) len y (fun p => ¬ good y p) ≤ ε₁ := by
    have hy : y ∈ colorClass C (C y) := (mem_colorClass C (C y) y).mpr rfl
    simpa only [len, ε₁, R, good, not_not] using
      first_bank_failure G hPos (2*k) (by omega) J (P (C y)) (hP (C y))
        aStar (hStars (C y)) N ρ hρ (hρB _) (hClosed _) (hpoint _) hN hScale y hy
  have hSecond (y : V) (p : Fin (gap+len) → V)
      (hp : 0 < traceWeight (step G) (gap+len) y p) (hg : good y (front len gap p)) :
      eventMass (step G) len (finish (gap+len) y p) (bad (front len gap p)) ≤ ε₂ := by
    let c := C y
    let A := colorClass C (1-c)
    let B := colorClass C c
    let S := bankSeen (2*k) N (by omega) B (front len gap p)
    let Q := goodRoots J (P c) S R
    have hLen : Even len := by
      refine ⟨N*k, ?_⟩
      dsimp only [len]
      ring
    have hOpp : finish (gap+len) y p ∈ A := by
      apply (mem_colorClass C _ _).mpr
      apply other_color C
      exact graph_finish_color_odd G C (gap+len) (hGap.add_even hLen) y p hp
    have hQ : Q ⊆ A := goodRoots_subset J (P c) (hP c) S R
    have hS : S ⊆ B := inter_subset_right
    have hLarge : (J.card : ℝ)*aStar/2 ≤ (Q.card : ℝ) :=
      goodRoots_lower J (P c) (hP c) (hRoots c) S R aStar (hStars c) hg
    have hTail := second_bank_failure G hPos (2*k) (by omega) hQ N s prob ρ hprob0 hprob1 hρ
      (hClosed _) (fun u v hu hv => hpoint _ u v hu (hQ hv)) (hbudget _ hLarge) hs
      (finish (gap+len) y p) hOpp
    apply le_trans ?_ hTail
    apply eventMass_mono (step G) (step_nonneg G)
    intro q hBad
    let T := bankSeen (2*k) N (by omega) A q
    change ((Q ∩ T).card : ℝ) ≤ s
    by_contra! hHits
    have hR0 : 0 ≤ R := le_trans (by norm_num) hScale
    have hCross := goodRoots_crossEdges_lower G (disjoint_colorClasses G C c) hEdge J (P c)
      (hP c) S T hS R
    exact hBad ⟨c, hThreshold.trans ((mul_le_mul_of_nonneg_right hHits.le hR0).trans hCross)⟩
  exact two_windows_failure_le (step G) (step_nonneg G) (sum_step G hPos)
    t a len gap hWindow x bad good (Real.exp_pos (-s)).le hFirst hSecond

/-- A large bank edge set in the selected residue has the required support
and cardinality on the middle half of the full walk. -/
theorem middle_event_of_bank_edges (C : G.Coloring (Fin 2)) (J : Finset I)
    (P : Fin 2 → I → Finset (V × Finset V)) (R : ℝ)
    {t a b k N : ℕ} (hk : 0 < k) (r : Fin k)
    (ha : a+N*(2*k) ≤ t) (hb : b+N*(2*k) ≤ t)
    (haL : t/4 ≤ a) (hbL : t/4 ≤ b)
    (haU : a+N*(2*k) ≤ 3*(t/4)) (hbU : b+N*(2*k) ≤ 3*(t/4))
    (haR : a % k = r.val) (hbR : b % k = r.val)
    (x : V) (p : Fin t → V) (c : Fin 2)
    (hCount : 2 * ((t : ℝ) + 1) / (k : ℝ) ≤
      ((bankEdges G C J P R (2*k) N (by omega) c (sliceTrace t a (N*(2*k)) ha p)
        (sliceTrace t b (N*(2*k)) hb p)).card : ℝ)) :
    Erdos642TraceConclusion.hasSampledEdges G (Fin.cons x p) r := by
  exact sampledEdges_of_banks G hk r ha hb haL hbL haU hbU haR hbR x p _ _ _ hCount

/-- Any bank edge between the first and last quarters provides a closing edge. -/
theorem quarter_event_of_bank_edges (C : G.Coloring (Fin 2)) (J : Finset I)
    (P : Fin 2 → I → Finset (V × Finset V)) (R : ℝ)
    {t a b k N : ℕ} (hk : 0 < k)
    (ha : a+N*(2*k) ≤ t) (hb : b+N*(2*k) ≤ t)
    (haQ : a+N*(2*k) ≤ t/4) (hbQ : 3*(t/4) ≤ b)
    (x : V) (p : Fin t → V) (c : Fin 2)
    (hCount : (1 : ℝ) ≤
      ((bankEdges G C J P R (2*k) N (by omega) c (sliceTrace t a (N*(2*k)) ha p)
        (sliceTrace t b (N*(2*k)) hb p)).card : ℝ)) :
    Erdos642TraceConclusion.closesInQuarters G (Fin.cons x p) := by
  let S := bankSeen (2*k) N (by omega) (colorClass C c) (sliceTrace t a (N*(2*k)) ha p)
  let T := bankSeen (2*k) N (by omega) (colorClass C (1-c)) (sliceTrace t b (N*(2*k)) hb p)
  let Q := goodRoots J (P c) S R ∩ T
  have hc : 0 < (crossEdges G Q S).card := by
    change (1 : ℝ) ≤ ((crossEdges G Q S).card : ℝ) at hCount
    exact_mod_cast (zero_lt_one.trans_le hCount)
  obtain ⟨e, he⟩ := card_pos.mp hc
  obtain ⟨v, hv, u, hu, hEdge, _⟩ := (mem_crossEdges G Q S).mp he
  exact closes_of_banks_adj G (by omega) ha hb haQ hbQ x p _ _ hu (mem_inter.mp hv).2 hEdge.symm

end Erdos642BankEvents

end Erdos642BankEventsFile

section Erdos642BankAlignmentFile

/- Rounding the two sampling banks while preserving one common stride. -/

namespace Erdos642BankAlignment

/-- Equally long even-stride banks fit inside a shifted middle window, with
room for one odd-stride gap and at most the indicated loss from rounding. -/
theorem aligned_middle_banks {t k i : ℕ} (hk : 0 < k)
    (hi : i ≤ k) (hLarge : 100*k ≤ t) :
    ∃ N : ℕ, 0 < N ∧
      2 * (2*k*N) + k ≤ t/2-i ∧
      t ≤ 5 * (2*k*N) := by
  let w := t/2-i
  let n := (w-k)/(4*k)
  let s := 2*k*n
  let r := (w-k)%(4*k)
  have hkw : k ≤ w := by dsimp [w]; omega
  have hr : r < 4*k := Nat.mod_lt _ (by omega)
  have hDiv0 : w-k = 4*k*n+r := (Nat.div_add_mod (w-k) (4*k)).symm
  have hMul : 4*k*n = 2*s := by dsimp only [s]; ring
  have hDiv : w = 2*s+r+k := by rw [hMul] at hDiv0; omega
  have hSize : t ≤ 5*s := by dsimp only [w] at hDiv; omega
  have hn : 0 < n := Nat.pos_of_ne_zero (fun hz => by
    simp only [s, hz, mul_zero] at hSize
    omega)
  exact ⟨n, hn, by omega, hSize⟩

/-- An even-stride bank fitting inside a quarter still has room to shift
its start by one whole stride when its sampling side needs to change. -/
theorem aligned_extreme_bank {t k : ℕ} (hk : 0 < k) (hLarge : 100*k ≤ t) :
    ∃ N : ℕ, 0 < N ∧
      (2*k*N) + k ≤ t/4 ∧
      t ≤ 5 * (2*k*N) := by
  let w := t/4
  let n := (w-k)/(2*k)
  let s := 2*k*n
  let r := (w-k)%(2*k)
  have hkw : k ≤ w := by dsimp [w]; omega
  have hr : r < 2*k := Nat.mod_lt _ (by omega)
  have hDiv0 : w-k = s+r := (Nat.div_add_mod (w-k) (2*k)).symm
  have hDiv : w = s+r+k := by omega
  have hSize : t ≤ 5*s := by dsimp only [w] at hDiv; omega
  have hn : 0 < n := Nat.pos_of_ne_zero (fun hz => by
    simp only [s, hz, mul_zero] at hSize
    omega)
  exact ⟨n, hn, by omega, hSize⟩

end Erdos642BankAlignment

end Erdos642BankAlignmentFile

section Erdos642BankOffsetsFile

/- Explicit compatible-residue and opposite-color bank offsets. -/

namespace Erdos642BankOffsets

open Erdos642BankAlignment

/-- The two middle banks lie in the requested residue, including for lengths
whose quotients by two and four round differently. -/
theorem middle_bank_offsets {t k : ℕ} (hk : 0 < k) (r : Fin k)
    (hLarge : 100*k ≤ t) :
    ∃ a N : ℕ, 0 < N ∧ t ≤ 5 * (2*k*N) ∧ t/4 ≤ a ∧ a % k = r.val ∧
      (a+N*(2*k)+k) % k = r.val ∧
      a+(N*(2*k)+(k+N*(2*k))) ≤ 3*(t/4) := by
  let q := t/4
  let z := r.val+k-q%k
  let i := z%k
  let a := q+i
  have hi : i < k := Nat.mod_lt z hk
  have hq : q%k < k := Nat.mod_lt q hk
  have hz : q%k+z = r.val+k := by dsimp only [z]; omega
  have haR : a%k = r.val := by
    dsimp only [a, i]
    rw [Nat.add_mod q (z%k) k, Nat.mod_mod]
    calc
      (q%k+z%k)%k = (q+z)%k := (Nat.add_mod q z k).symm
      _ = (q%k+z)%k := by rw [Nat.add_mod q z k, Nat.add_mod (q%k) z k, Nat.mod_mod]
      _ = r.val := by rw [hz, Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
  obtain ⟨N, hN, hFit, hLong⟩ := aligned_middle_banks hk (show i+1 ≤ k by omega) hLarge
  have hSwap : N*(2*k) = 2*k*N := Nat.mul_comm _ _
  refine ⟨a,N,hN,hLong,by dsimp [a,q]; omega,haR,?_,?_⟩
  · rw [Nat.add_mod_right, ← Nat.mul_assoc, Nat.add_mul_mod_self_right, haR]
  · dsimp only [a,q]
    rw [hSwap]
    omega

/-- The two extreme banks lie in the first and last quarters and have
an odd connecting gap, so they use opposite sides of a bipartite graph. -/
theorem extreme_bank_offsets {t k : ℕ} (hk : 0 < k) (hkOdd : Odd k) (hLarge : 100*k ≤ t) :
    ∃ N gap : ℕ, 0 < N ∧ t ≤ 5 * (2*k*N) ∧ Odd gap ∧ N*(2*k) ≤ t/4 ∧
      3*(t/4) ≤ N*(2*k)+gap ∧ N*(2*k)+(gap+N*(2*k)) ≤ t := by
  obtain ⟨N, hN, hFit, hLong⟩ := aligned_extreme_bank hk hLarge
  let q := t/4
  let len := N*(2*k)
  let b := 3*q + if Odd (3*q) then 0 else k
  let gap := b-len
  have hlen : len+k ≤ q := by simpa only [len, q, Nat.mul_comm N (2*k)] using hFit
  have hbL : 3*q ≤ b := Nat.le_add_right _ _
  have hbU : b ≤ 3*q+k := by dsimp only [b]; split <;> omega
  have hb : len+gap = b := by dsimp only [gap]; omega
  have hbOdd : Odd b := by
    dsimp only [b]
    split_ifs with h
    · simpa using h
    · exact (Nat.not_odd_iff_even.mp h).add_odd hkOdd
  have hlenEven : Even len := by
    refine ⟨N*k, ?_⟩
    dsimp only [len]
    ring
  have hGapOdd : Odd gap := by
    rw [Nat.odd_iff] at hbOdd ⊢
    rw [Nat.even_iff] at hlenEven
    omega
  refine ⟨N,gap,hN,hLong,hGapOdd,by omega,by omega,?_⟩
  dsimp only [q] at hlen hbU
  change len+(gap+len) ≤ t
  omega

end Erdos642BankOffsets

end Erdos642BankOffsetsFile

section Erdos642BankBoundsFile

/- Quantitative constants for the two even-stride sample banks. -/

namespace Erdos642BankBounds

/-- Convert the interval and rounded-bank guarantees into the arithmetic used by sampling. -/
theorem bank_length_bounds {m d k t N : ℝ} (hm : 0 < m) (hd : 0 < d) (hk : 1 ≤ k)
    (htm : t ≤ m) (hN0 : 0 ≤ N) (hFit : 2 * k * N ≤ t) (hLong : t ≤ 5 * (2 * k * N))
    (hScale : 10 ^ 17 * k * m / d ≤ t / 5) :
    t / (10 * k) ≤ N ∧ N ≤ m ∧ 10 ^ 15 * m ≤ d * N := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  refine ⟨(div_le_iff₀ (by positivity)).mpr (by linarith only [hLong]), ?_, ?_⟩
  · calc
      N = 1 * N := (one_mul _).symm
      _ ≤ (2 * k) * N := mul_le_mul_of_nonneg_right (by linarith only [hk]) hN0
      _ ≤ t := hFit
      _ ≤ m := htm
  · apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * k)).mp
    calc
      (2 * k) * (10 ^ 15 * m) ≤ 10 ^ 17 * k * m := by
        nlinarith only [mul_nonneg hk0.le hm.le]
      _ ≤ (t / 5) * d := (div_le_iff₀ hd).mp hScale
      _ ≤ (2 * k * N) * d := mul_le_mul_of_nonneg_right (by linarith only [hLong]) hd.le
      _ = (2 * k) * (d * N) := by ring

/-- With rounding losses included, enough good stars are seen in the first bank
and enough of their roots can be found in the second bank. -/
theorem bank_constants {m d k t N J a ell : ℝ} (hm : 0 < m) (hd : 0 < d) (hk : 0 < k)
    (ht : 0 ≤ t) (hN : t / (10 * k) ≤ N) (hNm : N ≤ m) (hScale : 10 ^ 15 * m ≤ d * N)
    (hJ : d / 20 ≤ J) (ha : m / (200000 * d) ≤ a) (hell : d / 20000000 ≤ ell) :
    let ρ := 1 / (100 * m)
    let R := ell * (N * ρ / 8)
    let p := 1 / 2000000000
    let s := N / 8000000000
    N * ρ ≤ 4 ∧ 4 ≤ R ∧ N / 10 ^ 17 ≤ a * R / 4 ∧
      (∀ Q : ℝ, J * a / 2 ≤ Q → p ≤ ρ * (Q - s)) ∧ s ≤ N * p / 4 ∧
      (t / 5) ^ 2 * d / (10 ^ 32 * k ^ 2 * m) ≤ s * R := by
  dsimp only
  let ρ : ℝ := 1 / (100 * m)
  let R : ℝ := ell * (N * ρ / 8)
  let p : ℝ := 1 / 2000000000
  let s : ℝ := N / 8000000000
  change N * ρ ≤ 4 ∧ 4 ≤ R ∧ N / 10 ^ 17 ≤ a * R / 4 ∧
      (∀ Q : ℝ, J * a / 2 ≤ Q → p ≤ ρ * (Q - s)) ∧ s ≤ N * p / 4 ∧
      (t / 5) ^ 2 * d / (10 ^ 32 * k ^ 2 * m) ≤ s * R
  have hN0 : 0 ≤ N := (by positivity : 0 ≤ t / (10 * k)).trans hN
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have ha0 : 0 ≤ a := (by positivity : 0 ≤ m / (200000 * d)).trans ha
  have hRlo : d * N / (20000000000 * m) ≤ R := calc
    _ ≤ (d / 20000000) * (N * ρ / 8) := by
      dsimp only [ρ]
      field_simp
      linarith only [hN0]
    _ ≤ _ := mul_le_mul_of_nonneg_right hell (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      N * ρ ≤ m * ρ := mul_le_mul_of_nonneg_right hNm hρ.le
      _ ≤ 4 := by dsimp [ρ]; field_simp; linarith
  · refine le_trans ?_ hRlo
    apply (le_div_iff₀ (by positivity : 0 < 20000000000 * m)).mpr
    norm_num at hScale ⊢
    linarith only [hm, hScale]
  · calc
      N / 10 ^ 17 ≤ (m / (200000 * d)) * (d * N / (20000000000 * m)) / 4 := by
        field_simp
        linarith only [hN0]
      _ ≤ (a * R) / 4 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul ha hRlo (by positivity) ha0) (by norm_num)
  · intro Q hQ
    have hRoots : m / 8000000 ≤ Q := calc
      _ = (d / 20) * (m / (200000 * d)) / 2 := by field_simp; norm_num
      _ ≤ J * a / 2 := div_le_div_of_nonneg_right
        (mul_le_mul hJ ha (by positivity) ((by positivity : 0 ≤ d / 20).trans hJ)) (by norm_num)
      _ ≤ Q := hQ
    have hs : s ≤ m / 8000000000 := div_le_div_of_nonneg_right hNm (by norm_num)
    calc
      p ≤ ρ * (m / 8000000 - m / 8000000000) := by
        dsimp only [p, ρ]
        field_simp
        linarith only [hm]
      _ ≤ ρ * (Q - s) := mul_le_mul_of_nonneg_left (sub_le_sub hRoots hs) hρ.le
  · dsimp only [s, p]
    ring_nf
    rfl
  · have hLowSq : (t / (10 * k)) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (by positivity) hN 2
    calc
      _ ≤ (t / (10 * k)) ^ 2 * (d / (160000000000000000000 * m)) := by
        field_simp
        nlinarith only [mul_nonneg (sq_nonneg t) hd.le]
      _ ≤ N ^ 2 * (d / (160000000000000000000 * m)) := mul_le_mul_of_nonneg_right hLowSq (by positivity)
      _ = s * (d * N / (20000000000 * m)) := by dsimp [s]; ring
      _ ≤ s * R := mul_le_mul_of_nonneg_left hRlo (by dsimp [s]; positivity)

/-- Both failure tails together fit the bound needed for the outer and middle windows. -/
theorem bank_failure_bound {m U N J : ℝ} (hm : 0 < m) (hlog : 1 ≤ Real.log m)
    (hU : 10 ^ 30 * Real.log m ≤ U) (hN : U / 10 ≤ N) (hJ : J ≤ m) :
    J * Real.exp (-(N / 10 ^ 17)) + Real.exp (-(N / 8000000000)) ≤
      Real.exp (-(U / 10 ^ 25)) := by
  have hUbig : (10 : ℝ) ^ 30 ≤ U := (le_mul_of_one_le_right (by positivity) hlog).trans hU
  have hfirst : Real.log m - N / 10 ^ 17 ≤ -(U / 10 ^ 25) - 1 := by
    norm_num at hU hUbig ⊢
    linarith only [hU, hUbig, hN]
  have hsecond : -(N / 8000000000) ≤ -(U / 10 ^ 25) - 1 := by
    norm_num at hUbig ⊢
    linarith only [hUbig, hN]
  have hhalf : Real.exp (-(1 : ℝ)) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact inv_anti₀ (by norm_num) h
  have hf : m * Real.exp (-(N / 10 ^ 17)) ≤ Real.exp (-(U / 10 ^ 25)) * (1 / 2) := by
    calc
      _ = Real.exp (Real.log m - N / 10 ^ 17) := by rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hm]
      _ ≤ Real.exp (-(U / 10 ^ 25) - 1) := Real.exp_le_exp.mpr hfirst
      _ ≤ _ := by rw [sub_eq_add_neg, Real.exp_add]; gcongr
  have hs : Real.exp (-(N / 8000000000)) ≤ Real.exp (-(U / 10 ^ 25)) * (1 / 2) := by
    calc
      _ ≤ Real.exp (-(U / 10 ^ 25) - 1) := Real.exp_le_exp.mpr hsecond
      _ ≤ _ := by rw [sub_eq_add_neg, Real.exp_add]; gcongr
  have hJF := mul_le_mul_of_nonneg_right hJ (Real.exp_pos (-(N/10^17))).le
  linarith only [hJF, hf, hs]

end Erdos642BankBounds

end Erdos642BankBoundsFile

section Erdos642TraceParametersFile

/- Extract the concrete walk and forest parameters from the hypotheses of the second reduction step. -/

namespace Erdos642TraceParameters

open Filter SimpleGraph Finset Erdos642RandomWalkKernel Erdos642ColoredForests

structure SamplingParameters {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (C : H.Coloring (Fin 2)) (k t : ℕ) : Prop where
  degreePositive : ∀ u, 0 < H.degree u
  minDegreeLarge : 10000000 ≤ H.minDegree
  degreeUpper : ∀ u, H.degree u ≤ 100 * H.minDegree
  stridePositive : 0 < k
  strideOdd : Odd k
  quarters : 4 ∣ t
  walkLong : 100 * k ≤ t
  walkFits : t ≤ m
  logLarge : 1 ≤ Real.log m
  exponentScale : 10 ^ 30 * Real.log m ≤ (t : ℝ) / k
  occupancyScale : 10 ^ 17 * (k : ℝ) * m / (H.minDegree : ℝ) ≤ (t : ℝ) / 5
  chordScale : 2 * ((t : ℝ) + 1) / k ≤
    ((t : ℝ) / 5) ^ 2 * (H.minDegree : ℝ) / (10 ^ 32 * (k : ℝ) ^ 2 * m)
  forestsCount : (H.minDegree : ℝ) / 20 ≤ ((H.minDegree / 10 : ℕ) : ℝ)
  starsCount : (m : ℝ) / (200000 * (H.minDegree : ℝ)) ≤
    ((m / (100000 * H.minDegree) : ℕ) : ℝ)
  leavesCount : (H.minDegree : ℝ) / 20000000 ≤ ((H.minDegree / 10000000 : ℕ) : ℝ)
  parityMixing : ∀ s, k ≤ s → ∀ u v : Fin m,
    ((C u).val + (C v).val + s) ≡ 0 [MOD 2] →
      1 / (100 * (m : ℝ)) ≤ walkWeight H s u v
  survive : ∀ v : Fin m,
    Real.exp (-((m : ℝ) / (10 ^ 89 * (k : ℝ) ^ 2))) ≤
      Erdos642ShortAvoidance.survivingMass (step H) t {v} v
  chance : 0 < Real.exp (-((m : ℝ) / (10 ^ 89 * (k : ℝ) ^ 2))) -
    Real.exp (-((t : ℝ) / k) / 10 ^ 25) - (k : ℝ) * Real.exp (-((t : ℝ) / k) / 10 ^ 25)

/-- Even sampling stride has the lower bound on each single color class. -/
theorem SamplingParameters.same_color_mix {m k t : ℕ} {H : SimpleGraph (Fin m)}
    [DecidableRel H.Adj] {C : H.Coloring (Fin 2)} (h : SamplingParameters H C k t)
    {u v : Fin m} (hSame : C u = C v) :
    1 / (100 * (m : ℝ)) ≤ walkWeight H (2 * k) u v := by
  apply h.parityMixing (2 * k) (by omega)
  change ((C u).val + (C v).val + 2 * k) % 2 = 0 % 2
  rw [hSame]
  omega

private theorem degree_average {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    2 * (H.edgeSet.ncard : ℝ) / m = (∑ v, (H.degree v : ℝ)) / m := by
  congr 1
  have hsum : (∑ v, (H.degree v : ℝ)) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  rw [hsum, ← Set.ncard_coe_finset, H.coe_edgeFinset]

/-- The walk parameters are available uniformly for every alleged counterexample. -/
theorem eventually_parameters :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ n →
      ∀ H : SimpleGraph (Fin m), ∀ [DecidableRel H.Adj],
      H.IsBipartite →
      (∀ u v, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) →
      Real.log n ^ 7 / 600 ≤ 2 * (H.edgeSet.ncard : ℝ) / m →
      (∀ S : Finset (Fin m), 2 * S.card ≤ m →
        (1 / (10 * Real.log n)) * (2 * (H.edgeSet.ncard : ℝ) / m) * S.card ≤
          ({e ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}.ncard : ℝ)) →
      Erdos642.CyclesHaveMoreVerticesThanChords H →
      ∃ (C : H.Coloring (Fin 2)) (k t : ℕ), SamplingParameters H C k t := by
  have hLogTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hLogTop.eventually_ge_atTop 1,
    Erdos642ForestRounding.eventually_minDegree_ge 10000000,
    Erdos642ForestRounding.eventually_rounded_star_forests,
    Erdos642DMMSScales.eventually_walk_parameters] with n hLog hLarge hForests hWalk
  intro m hm hmn H _ hBip hReg hAvg hExp hNo
  let v : Fin m := ⟨0, hm⟩
  let : Nonempty (Fin m) := ⟨v⟩
  let d := H.minDegree
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨hdLarge, hmLarge⟩ := hLarge m hm H hReg hAvg
  have hd : 0 < d := by change 10000000 ≤ d at hdLarge; omega
  have hnbr (u : Fin m) : (H.neighborSet u).ncard = H.degree u := by
    rw [Set.ncard_eq_toFinset_card']
    exact H.card_neighborFinset_eq_degree u
  have hReg' (u w : Fin m) : (H.degree u : ℝ) ≤ 100 * (H.degree w : ℝ) := by
    exact_mod_cast (show H.degree u ≤ 100 * H.degree w by simpa only [hnbr] using hReg u w)
  obtain ⟨w, hw⟩ := H.exists_minimal_degree_vertex
  have hDegreeMax (u : Fin m) : H.degree u ≤ 100 * d := by
    simpa only [hnbr, ← hw, d] using hReg u w
  have hPos (u : Fin m) : 0 < H.degree u := hd.trans_le (H.minDegree_le_degree u)
  obtain ⟨C⟩ := hBip
  have hm100 : 100 ≤ Fintype.card (Fin m) := by simpa only [Fintype.card_fin] using (show 100 ≤ m by omega)
  have hExp' : ∀ S : Finset (Fin m), 2 * S.card ≤ Fintype.card (Fin m) →
      (1 / (10 * Real.log n)) * (2 * (H.edgeSet.ncard : ℝ) / m) * S.card ≤
        ({e ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ e = s(u,v)}.ncard : ℝ) := by
    simpa only [Fintype.card_fin] using hExp
  have hav : 2 * (H.edgeSet.ncard : ℝ) / m =
      (∑ v, (H.degree v : ℝ)) / (Fintype.card (Fin m) : ℝ) := by
    simpa only [Fintype.card_fin] using degree_average H
  obtain ⟨k, hk, hkOdd, hkMax, hMix⟩ :=
    Erdos642WalkMixing.uniform_walk_bounds_odd H C hPos hReg' hm100 hLog hav hExp'
  simp only [Fintype.card_fin] at hkMax hMix
  obtain ⟨hdAvg, hdm⟩ := Erdos642DMMSScales.graph_min_degree_scales hm H hReg hAvg
  obtain ⟨t, htDiv, htFits, _, htUpper, hdQuad, htLong, _, _, hScale, _, hChord, hChance⟩ :=
    hWalk m k d hm hmn hk hdAvg hdm hkMax
  obtain ⟨hForest, hStars, hLeaves, _⟩ := hForests m hm H ⟨C⟩ hReg hAvg hNo
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hLogm : 1 ≤ Real.log m := (Real.le_log_iff_exp_le hmR).2 (by
    have hm9 : (9 : ℝ) ≤ m := by exact_mod_cast (show 9 ≤ m by omega)
    linarith only [Real.exp_one_lt_d9, hm9])
  have hLogmn : Real.log m ≤ Real.log n := Real.log_le_log hmR (by exact_mod_cast hmn)
  have hTReal : 100 * (k : ℝ) ≤ t := by
    apply (le_div_iff₀ hkR).mp ?_
    exact (by linarith only [hLog] : (100 : ℝ) ≤ 10 ^ 30 * Real.log n).trans htLong
  have htLongNat : 100 * k ≤ t := by exact_mod_cast hTReal
  let β : ℝ := 1 / 10 ^ 28
  have hD : 10 * (k : ℝ) ^ 2 ≤ β * (d : ℝ) := by
    dsimp only [β]
    have hk2 : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
    nlinarith only [hdQuad, hk2]
  have hSize : (k : ℝ) * (t : ℝ) ≤ β ^ 2 * (m : ℝ) / 10^6 := by
    apply (le_div_iff₀ (by positivity : 0 < (10 : ℝ)^62 * k)).mp at htUpper
    dsimp only [β]
    nlinarith only [htUpper]
  have hLowerExp : -((m : ℝ) / (10 ^ 89 * (k : ℝ) ^ 2)) ≤ -(10 * β * ((t : ℝ) / k)) := by
    have hMul := mul_le_mul_of_nonneg_left htUpper (show 0 ≤ 10 * β / (k : ℝ) by dsimp only [β]; positivity)
    have hl : (10 * β / (k : ℝ)) * (t : ℝ) = 10 * β * ((t : ℝ) / k) := by ring
    have hr : (10 * β / (k : ℝ)) * ((m : ℝ) / (10 ^ 62 * k)) =
        (m : ℝ) / (10 ^ 89 * (k : ℝ) ^ 2) := by
      dsimp only [β]
      field_simp
    rw [hl, hr] at hMul
    linarith only [hMul]
  have h4 : 4 ∣ t := (Nat.dvd_mul_right 4 k).trans htDiv
  have hkd : k ∣ t := (Nat.dvd_mul_left k 4).trans htDiv
  refine ⟨C, k, t, hPos, hdLarge, hDegreeMax, hk, hkOdd, h4, htLongNat, htFits, hLogm,
    (mul_le_mul_of_nonneg_left hLogmn (by positivity)).trans htLong, hScale, hChord,
    hForest, hStars, hLeaves, (fun s hs u w hp => (hMix s hs u w).2 hp), ?_, hChance⟩
  intro u
  apply (Real.exp_le_exp.mpr hLowerExp).trans
  refine Erdos642RepeatedAvoidance.dmms_self_avoidance H d hd H.minDegree_le_degree hReg'
    (show 0 < β by dsimp only [β]; positivity) (show β ≤ 1/10 by norm_num [β])
    hk hD (fun v w => ?_) hkd ?_ u
  · simpa only [Fintype.card_fin] using (hMix k le_rfl v w).1
  · simpa only [Fintype.card_fin] using hSize

end Erdos642TraceParameters

end Erdos642TraceParametersFile

section Erdos642BankCompletionFile

/- Complete the random-walk contradiction from its verified numerical parameters. -/

namespace Erdos642BankCompletion

open Finset SimpleGraph Filter
open Erdos642WalkTrace Erdos642TraceWindows Erdos642TraceConclusion
open Erdos642RandomWalkKernel Erdos642StarForest Erdos642ColoredForests
open Erdos642BankEvents Erdos642BankOffsets Erdos642BankBounds Erdos642BankWindows
open Erdos642TraceParameters

theorem contradict_of_parameters {m k t : ℕ} (hm : 0 < m) (H : SimpleGraph (Fin m))
    [DecidableRel H.Adj] (C : H.Coloring (Fin 2)) (h : SamplingParameters H C k t) :
    ¬ Erdos642.CyclesHaveMoreVerticesThanChords H := by
  classical
  let x : Fin m := ⟨0,hm⟩
  let d := H.minDegree
  let J : Finset (Fin (d/10)) := univ
  let E := (univ ×ˢ univ).filter (fun p : Fin m × Fin m => H.Adj p.1 p.2)
  let ell := d/10000000
  let aStar : ℝ := (m/(100000*d) : ℕ)
  let ρ : ℝ := 1/(100*(m:ℝ))
  let prob : ℝ := 1/2000000000
  let s (N : ℕ) : ℝ := (N : ℝ)/8000000000
  let R (N : ℕ) : ℝ := (ell : ℝ)*((N : ℝ)*ρ/8)
  let threshold : ℝ := 2*((t : ℝ)+1)/(k : ℝ)
  let ε : ℝ := Real.exp (-(((t : ℝ)/k)/10^25))
  have hk := h.stridePositive
  have h40 := h.walkLong
  have ht4 : 4 ≤ t := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkR1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hd0 : 0 < d := lt_of_lt_of_le (by decide : 0 < 10000000) h.minDegreeLarge
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd0
  have hdM : d ≤ m :=
    (H.minDegree_le_degree x).trans (by simpa only [Fintype.card_fin] using (H.degree_lt_card_verts x).le)
  have hflip (c : Fin 2) : 1-(1-c)=c := by fin_cases c <;> decide
  have hExist (c : Fin 2) := exists_color_packings H C (1-c) h.minDegreeLarge
    H.minDegree_le_degree h.degreeUpper
  choose P hPDisj hPData using hExist
  have hP (c : Fin 2) (i : Fin (d/10)) (_ : i ∈ J) :
      IsPacking E (colorClass C (1-c)) (colorClass C c) ell (P c i) := by
    simpa only [E, ell, d, hflip] using (hPData c i).2
  have hRoots (c : Fin 2) : (J : Set (Fin (d/10))).PairwiseDisjoint
      (fun i => (P c i).image Prod.fst) :=
    fun _ _ _ _ hij => hPDisj c hij
  have hEdge (p : Fin m × Fin m) (hp : p ∈ E) : H.Adj p.1 p.2 :=
    (mem_filter.mp hp).2
  have hStars (c : Fin 2) (i : Fin (d/10)) (_ : i ∈ J) : aStar ≤ ((P c i).card : ℝ) := by
    simp only [(hPData c i).1, Fintype.card_fin, aStar, d, le_refl]
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  have hρB (c : Fin 2) : ρ * ((colorClass C c).card : ℝ) ≤ 1 := by
    have hc : (colorClass C c).card ≤ m := by
      simpa only [Fintype.card_fin] using card_le_univ (colorClass C c)
    calc
      _ ≤ ρ * (m : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hc) hρ
      _ ≤ _ := by dsimp only [ρ]; field_simp; linarith only [hmR]
  have hpoint (c : Fin 2) (u v : Fin m) (hu : u ∈ colorClass C c) (hv : v ∈ colorClass C c) :
      ρ ≤ walkWeight H (2*k) u v :=
    h.same_color_mix (((mem_colorClass C c u).mp hu).trans ((mem_colorClass C c v).mp hv).symm)
  have hJlower : (d : ℝ)/20 ≤ (J.card : ℝ) := by simpa only [J,card_univ,Fintype.card_fin] using h.forestsCount
  have hJupper : (J.card : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (show J.card ≤ m by
      simpa only [J,card_univ,Fintype.card_fin] using (Nat.div_le_self d 10).trans hdM)
  have hThreshold1 : (1 : ℝ) ≤ threshold := by
    apply (le_div_iff₀ hkR).mpr
    have htk : (100 : ℝ)*(k : ℝ) ≤ (t : ℝ) := by exact_mod_cast h.walkLong
    linarith only [htk,hkR]
  have hBank (a gap N : ℕ) (hGap : Odd gap) (hLong : t ≤ 5*(2*k*N))
      (hFit : a+(N*(2*k)+(gap+N*(2*k))) ≤ t) {goal : ℝ} (hGoal : goal ≤ threshold) :
      eventMass (step H) t x (fun p => ¬ ∃ c : Fin 2, goal ≤
        ((bankEdges H C J P (R N) (2*k) N (by omega) c
          (sliceTrace t a (N*(2*k)) (by omega) p)
          (sliceTrace t (a+N*(2*k)+gap) (N*(2*k)) (by omega) p)).card : ℝ)) ≤ ε := by
    have hFitNat : 2*k*N ≤ t := by rw [Nat.mul_comm (2*k) N]; omega
    obtain ⟨hN, hNm, hScale⟩ := bank_length_bounds hmR hdR hkR1 (by exact_mod_cast h.walkFits)
      (by positivity : 0 ≤ (N : ℝ)) (by exact_mod_cast hFitNat)
      (by exact_mod_cast hLong) h.occupancyScale
    obtain ⟨hNρ, hR, hExp, hBudget, hProb, hNR⟩ :=
      bank_constants hmR hdR hkR (Nat.cast_nonneg t) hN hNm hScale hJlower h.starsCount h.leavesCount
    have hCount : goal ≤ s N * R N := hGoal.trans (h.chordScale.trans hNR)
    have hraw := two_windows_edges_failure_le H C h.degreePositive J P hP hRoots hEdge
      aStar hStars t a gap k N hk hGap hFit x ρ prob (s N) goal hρ hρB hpoint hNρ hR
      (by norm_num [prob]) (by norm_num [prob]) hBudget hProb hCount
    refine hraw.trans ?_
    have hExp' := (Real.exp_le_exp.mpr (neg_le_neg hExp))
    have hJExp := mul_le_mul_of_nonneg_left hExp' (by positivity : 0 ≤ (J.card : ℝ))
    have hTail := bank_failure_bound hmR h.logLarge h.exponentScale
      (show ((t : ℝ)/k)/10 ≤ (N : ℝ) from by simpa only [div_div,mul_comm (k:ℝ) (10:ℝ)] using hN)
      hJupper
    exact (add_le_add hJExp le_rfl).trans hTail
  have hClose : eventMass (step H) t x (fun p => ¬ closesInQuarters H (Fin.cons x p)) ≤ ε := by
    obtain ⟨N,gap,_,hLong,hGap,hFirst,hLast,hFit⟩ := extreme_bank_offsets hk h.strideOdd h.walkLong
    have hFit' : 0+(N*(2*k)+(gap+N*(2*k))) ≤ t := by omega
    refine (eventMass_mono (step H) (step_nonneg H) t x ?_).trans
      (hBank 0 gap N hGap hLong hFit' hThreshold1)
    rintro p hp ⟨c,hc⟩
    exact hp (quarter_event_of_bank_edges H C J P (R N) hk
      (ha := by omega) (hb := by omega) (by omega) (by omega) x p c hc)
  have hMid (r : Fin k) :
      eventMass (step H) t x (fun p => ¬ hasSampledEdges H (Fin.cons x p) r) ≤ ε := by
    obtain ⟨a,N,_,hLong,haL,haR,hbR,hFit⟩ := middle_bank_offsets hk r h.walkLong
    have hFit' : a+(N*(2*k)+(k+N*(2*k))) ≤ t := by omega
    refine (eventMass_mono (step H) (step_nonneg H) t x ?_).trans
      (hBank a k N h.strideOdd hLong hFit' (le_refl threshold))
    rintro p hp ⟨c,hc⟩
    exact hp (middle_event_of_bank_edges H C J P (R N) hk r
      (ha := by omega) (hb := by omega) haL (by omega) (by omega) (by omega) haR hbR x p c hc)
  apply contradict_of_trace_bounds H x hk ht4 (h.survive x) hClose hMid
  simpa only [ε, neg_div] using h.chance

/-- The exact second leaf of the Erdős 642 reduction. -/
theorem eventually_no_counterexample :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ n → ∀ H : SimpleGraph (Fin m),
      H.IsBipartite →
      (∀ u v : Fin m, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) →
      Real.log n ^ 7 / 600 ≤ 2 * (H.edgeSet.ncard : ℝ) / m →
      (∀ S : Finset (Fin m), 2 * S.card ≤ m →
        (1 / (10 * Real.log n)) * (2 * (H.edgeSet.ncard : ℝ) / m) * S.card ≤
          ({e ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}.ncard : ℝ)) →
      ¬ Erdos642.CyclesHaveMoreVerticesThanChords H := by
  classical
  filter_upwards [eventually_parameters] with n h
  intro m hm hmn H hBip hReg hAvg hExp hCounter
  obtain ⟨C,k,t,hParams⟩ := h m hm hmn H hBip hReg hAvg hExp hCounter
  exact contradict_of_parameters hm H C hParams hCounter

end Erdos642BankCompletion

end Erdos642BankCompletionFile

theorem OMA.solution : type_of% @Erdos642.erdos_642.variants.upper_bound_n_log_pow_eight :=
  OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1.main
    Erdos642ExpansionH1.proved_h1 Erdos642BankCompletion.eventually_no_counterexample
