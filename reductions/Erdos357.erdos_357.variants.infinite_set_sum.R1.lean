import FormalConjectures.ErdosProblems.«357»

/-!
Merging successive terms in Erdős 357. The cut points need only be strictly
increasing, so the same theorem applies when block lengths change between epochs.
Any initial segment before the first cut point is discarded. Empty index intervals
are included as required by the pinned definition of HasDistinctSums.
-/

namespace Erdos357ReductionLemmas

variable {α : Type*} [AddCommMonoid α]

private theorem join_intervals (f : ℕ → α) {l m r : ℕ} (hlm : l ≤ m) (hmr : m ≤ r) :
    (∑ i ∈ Finset.Ico l m, f i) + (∑ i ∈ Finset.Ico m r, f i) =
      ∑ i ∈ Finset.Ico l r, f i := by
  have hdis : Disjoint (Finset.Ico l m) (Finset.Ico m r) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Nat.not_lt_of_ge (Finset.mem_Ico.mp hj).1) (Finset.mem_Ico.mp hi).2
  have hunion : Finset.Ico l m ∪ Finset.Ico m r = Finset.Ico l r := by
    ext i
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  rw [← Finset.sum_union hdis, hunion]

theorem sum_blocks (a : ℕ → α) {cut : ℕ → ℕ} (hc : StrictMono cut)
    {l r : ℕ} (hlr : l ≤ r) :
    (∑ j ∈ Finset.Ico l r, (fun j : ℕ => ∑ i ∈ Finset.Ico (cut j) (cut (j+1)), a i) j) =
      ∑ i ∈ Finset.Ico (cut l) (cut r), a i := by
  induction r, hlr using Nat.le_induction with
  | base => simp
  | succ r hlr ih =>
    have hsingle : Finset.Ico r (r + 1) = {r} := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    calc
      _ = (∑ j ∈ Finset.Ico l r, (fun j : ℕ => ∑ i ∈ Finset.Ico (cut j) (cut (j+1)), a i) j) +
          (∑ j ∈ Finset.Ico r (r + 1), (fun j : ℕ => ∑ i ∈ Finset.Ico (cut j) (cut (j+1)), a i) j) :=
        (join_intervals _ hlr (Nat.le_succ r)).symm
      _ = (∑ i ∈ Finset.Ico (cut l) (cut r), a i) +
          (∑ i ∈ Finset.Ico (cut r) (cut (r + 1)), a i) := by
        simp only [ih, hsingle, Finset.sum_singleton]
      _ = _ := join_intervals _ (hc.monotone hlr) (hc.monotone (Nat.le_succ r))

private theorem connected_interval (l r : ℕ) :
    ((Finset.Ico l r : Finset ℕ) : Set ℕ).OrdConnected := by
  constructor
  intro x hx z hz y hy
  change x ∈ Finset.Ico l r at hx
  change z ∈ Finset.Ico l r at hz
  change y ∈ Finset.Ico l r
  exact Finset.mem_Ico.mpr
    ⟨le_trans (Finset.mem_Ico.mp hx).1 hy.1, lt_of_le_of_lt hy.2 (Finset.mem_Ico.mp hz).2⟩

private theorem interval_of_connected (J : Finset ℕ) (hJ : (J : Set ℕ).OrdConnected) :
    ∃ l r : ℕ, l ≤ r ∧ J = Finset.Ico l r := by
  by_cases hne : J.Nonempty
  · let l := J.min' hne
    let m := J.max' hne
    have hl : l ∈ J := J.min'_mem hne
    have hm : m ∈ J := J.max'_mem hne
    have hlm : l ≤ m := J.min'_le m hm
    refine ⟨l, m + 1, by omega, ?_⟩
    ext i
    constructor
    · intro hi
      exact Finset.mem_Ico.mpr ⟨J.min'_le i hi, Nat.lt_succ_of_le (J.le_max' i hi)⟩
    · intro hi
      obtain ⟨hli, him⟩ := Finset.mem_Ico.mp hi
      rcases hJ with ⟨hconv⟩
      exact hconv hl hm ⟨hli, by omega⟩
  · exact ⟨0, 0, le_rfl, by simp [Finset.not_nonempty_iff_eq_empty.mp hne]⟩

theorem hasDistinctSums_blockSum {a : ℕ → α} (ha : Erdos357.HasDistinctSums a)
    {cut : ℕ → ℕ} (hc : StrictMono cut) : Erdos357.HasDistinctSums ((fun j : ℕ => ∑ i ∈ Finset.Ico (cut j) (cut (j+1)), a i)) := by
  intro J hJ K hK heq
  obtain ⟨l, r, hlr, rfl⟩ := interval_of_connected J hJ
  obtain ⟨s, t, hst, rfl⟩ := interval_of_connected K hK
  have hsum : (∑ i ∈ Finset.Ico (cut l) (cut r), a i) =
      ∑ i ∈ Finset.Ico (cut s) (cut t), a i :=
    (sum_blocks a hc hlr).symm.trans (heq.trans (sum_blocks a hc hst))
  have hsets : Finset.Ico (cut l) (cut r) = Finset.Ico (cut s) (cut t) :=
    ha (connected_interval _ _) (connected_interval _ _) hsum
  ext i
  have hi : cut i ∈ Finset.Ico (cut l) (cut r) ↔ cut i ∈ Finset.Ico (cut s) (cut t) := by
    rw [hsets]
  simpa only [Finset.mem_Ico, hc.le_iff_le, hc.lt_iff_lt] using hi

end Erdos357ReductionLemmas


namespace OMA.R_Erdos357_erdos_357_variants_infinite_set_sum_R1

/-
Source: https://www.erdosproblems.com/357
Credit: @dwilfand-sys

A divergent positive decreasing reciprocal series stays divergent after any
fixed grouping of a tail. Successive finite groups of sizes 1, 2, ... can
therefore give a divergent coarsening with gaps growing to infinity. H1
isolates this real-analysis lemma, independent of distinct interval sums.
H2 is the remaining open conjecture restricted to sequences whose successive gaps tend to infinity.
-/

private theorem positive_terms {A : ℕ → ℕ} (h : Erdos357.HasDistinctSums A) (i : ℕ) :
    0 < A i := by
  by_contra! hzero
  have hz : A i = 0 := by omega
  have hempty : (((∅ : Finset ℕ) : Set ℕ)).OrdConnected := by
    constructor
    intro x hx
    change x ∈ (∅ : Finset ℕ) at hx
    simp at hx
  have hsingle : ((({i} : Finset ℕ) : Set ℕ)).OrdConnected := by
    constructor
    intro x hx z hz y hy
    have hx' : x = i := Finset.mem_singleton.mp hx
    have hz' : z = i := Finset.mem_singleton.mp hz
    apply Finset.mem_singleton.mpr
    obtain ⟨hxy, hyz⟩ := hy
    omega
  have hclash : (∅ : Finset ℕ) = {i} := h hempty hsingle (by simp [hz])
  have hi : i ∈ (∅ : Finset ℕ) := by rw [hclash]; simp
  simp at hi

def H1 : Prop := ∀ A : ℕ → ℕ, StrictMono A → (∀ j, 0 < A j) →
  ¬ Summable (fun j => (1 : ℝ) / A j) →
  ∃ cut : ℕ → ℕ,
    let B := fun j : ℕ => ∑ i ∈ Finset.Ico (cut j) (cut (j+1)), A i
    StrictMono cut ∧ StrictMono B ∧
      (∀ d : ℕ, ∃ n : ℕ, ∀ j ≥ n, d ≤ B (j+1) - B j) ∧
      ¬ Summable (fun j => (1 : ℝ) / B j)

def H2 : Prop := ∀ B : ℕ → ℕ, StrictMono B → Erdos357.HasDistinctSums B →
  (∀ d : ℕ, ∃ n : ℕ, ∀ j ≥ n, d ≤ B (j+1) - B j) →
  Summable (fun j => (1 : ℝ) / B j)

theorem main : H1 → H2 → type_of% @Erdos357.erdos_357.variants.infinite_set_sum := by
  intro h1 h2 A hmono hdist
  by_contra hdiv
  obtain ⟨cut, hcut, hb, hgaps, hnot⟩ := h1 A hmono (positive_terms hdist) hdiv
  exact hnot (h2 _ hb (Erdos357ReductionLemmas.hasDistinctSums_blockSum hdist hcut) hgaps)

end OMA.R_Erdos357_erdos_357_variants_infinite_set_sum_R1
