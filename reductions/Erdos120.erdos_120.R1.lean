import FormalConjectures.ErdosProblems.«120»
import Mathlib

/-!
Reduction Erdos120.erdos_120.R1 of Erdős Problem 120 (Erdős similarity problem).
Credit: @sntntHb

Sketch. Every infinite set reduces to a strictly decreasing positive null sequence
(the standard reduction stated on erdosproblems.com/120; @bmountain also formalized it
locally in site notes 26631 and 28298 without submitting it; this file is written independently):
* the property is monotone (a superset of a good set is good) and invariant under
  nonconstant affine maps;
* an unbounded set is good with E = [0,1] (an affine copy of an unbounded set is unbounded);
* a bounded infinite set contains a strictly monotone sequence (exists_increasing_or_nonincreasing_subseq),
  which converges to its sup or inf; after x ↦ ±(x − L) it becomes a strictly decreasing
  positive null sequence.
The null sequences are then split by the consecutive ratio a(n+1)/a(n):
* H1: ratio → 1, the known theorem of Falconer (1984), also Eigen (1985); not in Mathlib;
* H2: ratio does not tend to 1. Open in general (geometric sequences such as 2^(-n) were
  reported settled in 2026, but arbitrary fast-decaying sequences remain open).
No computer search was used.
-/

open Filter Topology MeasureTheory Erdos120

namespace OMA.R_Erdos120_erdos_120_R1

/-- Falconer 1984: slowly decaying null sequences are not universal. -/
def H1 : Prop :=
  ∀ a : ℕ → ℝ, StrictAnti a → (∀ n, 0 < a n) → Tendsto a atTop (𝓝 0) →
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1) → Erdos120For (Set.range a)

/-- The open core: null sequences whose consecutive ratio does not tend to 1. -/
def H2 : Prop :=
  ∀ a : ℕ → ℝ, StrictAnti a → (∀ n, 0 < a n) → Tendsto a atTop (𝓝 0) →
    ¬ Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1) → Erdos120For (Set.range a)

lemma good_mono {A B : Set ℝ} (h : B ⊆ A) (hB : Erdos120For B) : Erdos120For A := by
  obtain ⟨E, hE, hv, hno⟩ := hB
  exact ⟨E, hE, hv, fun a b ha hsub => hno a b ha ((Set.image_mono h).trans hsub)⟩

lemma good_affine {A : Set ℝ} (c d : ℝ) (hc : c ≠ 0) (hA : Erdos120For A) :
    Erdos120For ((fun x => c * x + d) '' A) := by
  obtain ⟨E, hE, hv, hno⟩ := hA
  refine ⟨E, hE, hv, fun a b ha hsub => ?_⟩
  apply hno (a * c) (a * d + b) (mul_ne_zero ha hc)
  have : (fun x => (a * c) * x + (a * d + b)) '' A =
      (fun x => a * x + b) '' ((fun x => c * x + d) '' A) := by
    rw [Set.image_image]; congr 1; funext x; ring
  rw [this]; exact hsub

lemma good_unbounded {A : Set ℝ} (hA : ¬ Bornology.IsBounded A) : Erdos120For A := by
  refine ⟨Set.Icc 0 1, measurableSet_Icc, by simp [Real.volume_Icc], fun a b ha hsub => hA ?_⟩
  have hK : IsCompact ((fun y => (y - b) / a) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image (by fun_prop)
  refine hK.isBounded.subset ?_
  intro x hx
  refine ⟨a * x + b, hsub ⟨x, hx, rfl⟩, ?_⟩
  field_simp
  ring

lemma good_null (h1 : H1) (h2 : H2) (a : ℕ → ℝ) (ha : StrictAnti a) (hpos : ∀ n, 0 < a n)
    (hlim : Tendsto a atTop (𝓝 0)) : Erdos120For (Set.range a) := by
  by_cases hr : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1)
  · exact h1 a ha hpos hlim hr
  · exact h2 a ha hpos hlim hr

theorem main : H1 → H2 → type_of% @Erdos120.erdos_120 := by
  intro h1 h2 A hA
  by_cases hb : Bornology.IsBounded A
  swap
  · exact good_unbounded hb
  set f : ℕ → ℝ := fun n => (hA.natEmbedding A n : ℝ) with hf
  have finj : Function.Injective f := by
    intro m n hmn
    exact (hA.natEmbedding A).injective (Subtype.ext hmn)
  have fA : ∀ n, f n ∈ A := fun n => (hA.natEmbedding A n).2
  obtain ⟨g, hg⟩ := exists_increasing_or_nonincreasing_subseq (· < ·) f
  set v : ℕ → ℝ := fun n => f (g n) with hv
  have vA : Set.range v ⊆ A := by rintro _ ⟨n, rfl⟩; exact fA _
  have hbdA : BddAbove (Set.range v) := hb.bddAbove.mono vA
  have hbdB : BddBelow (Set.range v) := hb.bddBelow.mono vA
  rcases hg with hinc | hdec
  · -- strictly increasing subsequence
    have hvm : StrictMono v := fun m n hmn => hinc m n hmn
    set L := ⨆ i, v i with hL
    have hT : Tendsto v atTop (𝓝 L) := tendsto_atTop_ciSup hvm.monotone hbdA
    set w : ℕ → ℝ := fun n => L - v n with hw
    have wpos : ∀ n, 0 < w n := fun n => by
      have := le_ciSup hbdA (n + 1)
      have := hvm (Nat.lt_succ_self n)
      simp only [hw]; linarith
    have wanti : StrictAnti w := fun m n hmn => by
      have := hvm hmn
      simp only [hw]; linarith
    have wlim : Tendsto w atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := L)).sub hT
      simpa using this
    have hgood := good_affine (-1) L (by norm_num) (good_null h1 h2 w wanti wpos wlim)
    have hset : (fun x => -1 * x + L) '' Set.range w = Set.range v := by
      rw [← Set.range_comp]; congr 1; funext n; simp only [Function.comp, hw]; ring
    rw [hset] at hgood
    exact good_mono vA hgood
  · -- strictly decreasing subsequence
    have hva : StrictAnti v := by
      intro m n hmn
      have h := hdec m n hmn
      have hne : v n ≠ v m := by
        intro he
        exact (ne_of_lt hmn).symm (g.injective (finj he))
      exact lt_of_le_of_ne (not_lt.mp h) hne
    set L := ⨅ i, v i with hL
    have hT : Tendsto v atTop (𝓝 L) := tendsto_atTop_ciInf hva.antitone hbdB
    set w : ℕ → ℝ := fun n => v n - L with hw
    have wpos : ∀ n, 0 < w n := fun n => by
      have := ciInf_le hbdB (n + 1)
      have := hva (Nat.lt_succ_self n)
      simp only [hw]; linarith
    have wanti : StrictAnti w := fun m n hmn => by
      have := hva hmn
      simp only [hw]; linarith
    have wlim : Tendsto w atTop (𝓝 0) := by
      have := hT.sub (tendsto_const_nhds (x := L))
      simpa using this
    have hgood := good_affine 1 L (by norm_num) (good_null h1 h2 w wanti wpos wlim)
    have hset : (fun x => 1 * x + L) '' Set.range w = Set.range v := by
      rw [← Set.range_comp]; congr 1; funext n; simp only [Function.comp, hw]; ring
    rw [hset] at hgood
    exact good_mono vA hgood

end OMA.R_Erdos120_erdos_120_R1
