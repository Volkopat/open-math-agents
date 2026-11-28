import FormalConjectures.ErdosProblems.«120»
import Mathlib

-- Reduction Erdos120.erdos_120.R2 of Erdős Problem 120
-- Credit: @volskew90
-- H1 is the 2026 Jiang--Xi adjacent-ratios-bounded-below case.
-- H2 is the remaining superlacunary case.

open Filter Topology MeasureTheory Erdos120

namespace OMA.R_Erdos120_erdos_120_R2

def H1 : Prop :=
  ∀ a : ℕ → ℝ, StrictAnti a → (∀ n, 0 < a n) → Tendsto a atTop (𝓝 0) →
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ a (n + 1) / a n) →
      Erdos120For (Set.range a)

def H2 : Prop :=
  ∀ a : ℕ → ℝ, StrictAnti a → (∀ n, 0 < a n) → Tendsto a atTop (𝓝 0) →
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 0) → Erdos120For (Set.range a)

lemma good_mono {A B : Set ℝ} (h : B ⊆ A) (hB : Erdos120For B) : Erdos120For A := by
  obtain ⟨E, hE, hv, hno⟩ := hB
  exact ⟨E, hE, hv, fun a b ha hsub => hno a b ha ((Set.image_mono h).trans hsub)⟩

lemma good_affine {A : Set ℝ} (c d : ℝ) (hc : c ≠ 0) (hA : Erdos120For A) :
    Erdos120For ((fun x => c * x + d) '' A) := by
  obtain ⟨E, hE, hv, hno⟩ := hA
  refine ⟨E, hE, hv, fun a b ha hsub => ?_⟩
  apply hno (a * c) (a * d + b) (mul_ne_zero ha hc)
  have himage : (fun x => (a * c) * x + (a * d + b)) '' A =
      (fun x => a * x + b) '' ((fun x => c * x + d) '' A) := by
    rw [Set.image_image]
    congr 1
    funext x
    ring
  rw [himage]
  exact hsub

lemma good_unbounded {A : Set ℝ} (hA : ¬ Bornology.IsBounded A) : Erdos120For A := by
  refine ⟨Set.Icc 0 1, measurableSet_Icc, by simp [Real.volume_Icc], fun a b ha hsub => hA ?_⟩
  have hK : IsCompact ((fun y => (y - b) / a) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image (by fun_prop)
  refine hK.isBounded.subset ?_
  intro x hx
  refine ⟨a * x + b, hsub ⟨x, hx, rfl⟩, ?_⟩
  field_simp
  ring

lemma good_of_no_eventual_lower_ratio (hsuper : H2) (a : ℕ → ℝ) (ha : StrictAnti a)
    (hpos : ∀ n, 0 < a n) (hlim : Tendsto a atTop (𝓝 0))
    (hbelow : ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ a (n + 1) / a n) :
    Erdos120For (Set.range a) := by
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, a (n + 1) / a n < ε := by
    intro ε hε N
    by_contra h
    push_neg at h
    exact hbelow ⟨ε, hε, eventually_atTop.2 ⟨N, h⟩⟩
  choose f hf using fun (k N : ℕ) => hsmall ((1 / 2 : ℝ) ^ k) (by positivity) N
  let n : ℕ → ℕ := fun k => Nat.rec (f 0 0) (fun j prev => f (j + 1) (prev + 1)) k
  have hn_succ (k : ℕ) : n (k + 1) = f (k + 1) (n k + 1) := rfl
  have hnstep (k : ℕ) : n k + 1 ≤ n (k + 1) := by
    rw [hn_succ]
    exact (hf (k + 1) (n k + 1)).1
  have hnmono : StrictMono n :=
    strictMono_nat_of_lt_succ fun k => Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hnstep k)
  have hnratio (k : ℕ) : a (n k + 1) / a (n k) < (1 / 2 : ℝ) ^ k := by
    cases k with
    | zero => exact (hf 0 0).2
    | succ k =>
      rw [hn_succ]
      exact (hf (k + 1) (n k + 1)).2
  let b : ℕ → ℝ := fun k => a (n k)
  have hbanti : StrictAnti b := fun i j hij => ha (hnmono hij)
  have hbpos : ∀ k, 0 < b k := fun k => hpos (n k)
  have hblim : Tendsto b atTop (𝓝 0) := hlim.comp hnmono.tendsto_atTop
  have hbratio (k : ℕ) : b (k + 1) / b k < (1 / 2 : ℝ) ^ k := by
    have hnum : b (k + 1) ≤ a (n k + 1) := ha.antitone (hnstep k)
    have hden : 0 < b k := hbpos k
    exact lt_of_le_of_lt ((div_le_div_iff_of_pos_right hden).2 hnum) (hnratio k)
  have hbrlim : Tendsto (fun k => b (k + 1) / b k) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => div_nonneg (hbpos (k + 1)).le (hbpos k).le)
      (fun k => (hbratio k).le)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply good_mono (A := Set.range a) (B := Set.range b)
  · rintro x ⟨k, rfl⟩
    exact ⟨n k, rfl⟩
  · exact hsuper b hbanti hbpos hblim hbrlim

lemma good_null (hlow : H1) (hsuper : H2) (a : ℕ → ℝ) (ha : StrictAnti a)
    (hpos : ∀ n, 0 < a n) (hlim : Tendsto a atTop (𝓝 0)) : Erdos120For (Set.range a) := by
  by_cases hbelow : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ a (n + 1) / a n
  · exact hlow a ha hpos hlim hbelow
  · exact good_of_no_eventual_lower_ratio hsuper a ha hpos hlim hbelow

theorem main : H1 → H2 → type_of% @Erdos120.erdos_120 := by
  intro hlow hsuper A hA
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
  · have hvm : StrictMono v := fun m n hmn => hinc m n hmn
    set L := ⨆ i, v i with hL
    have hT : Tendsto v atTop (𝓝 L) := tendsto_atTop_ciSup hvm.monotone hbdA
    set w : ℕ → ℝ := fun n => L - v n with hw
    have wpos : ∀ n, 0 < w n := fun n => by
      have hle := le_ciSup hbdA (n + 1)
      have hlt := hvm (Nat.lt_succ_self n)
      simp only [hw]
      linarith
    have wanti : StrictAnti w := fun m n hmn => by
      have hlt := hvm hmn
      simp only [hw]
      linarith
    have wlim : Tendsto w atTop (𝓝 0) := by
      have h := (tendsto_const_nhds (x := L)).sub hT
      simpa using h
    have hgood := good_affine (-1) L (by norm_num) (good_null hlow hsuper w wanti wpos wlim)
    have hset : (fun x => -1 * x + L) '' Set.range w = Set.range v := by
      rw [← Set.range_comp]
      congr 1
      funext n
      simp only [Function.comp, hw]
      ring
    rw [hset] at hgood
    exact good_mono vA hgood
  · have hva : StrictAnti v := by
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
      have hle := ciInf_le hbdB (n + 1)
      have hlt := hva (Nat.lt_succ_self n)
      simp only [hw]
      linarith
    have wanti : StrictAnti w := fun m n hmn => by
      have hlt := hva hmn
      simp only [hw]
      linarith
    have wlim : Tendsto w atTop (𝓝 0) := by
      have h := hT.sub (tendsto_const_nhds (x := L))
      simpa using h
    have hgood := good_affine 1 L (by norm_num) (good_null hlow hsuper w wanti wpos wlim)
    have hset : (fun x => 1 * x + L) '' Set.range w = Set.range v := by
      rw [← Set.range_comp]
      congr 1
      funext n
      simp only [Function.comp, hw]
      ring
    rw [hset] at hgood
    exact good_mono vA hgood

end OMA.R_Erdos120_erdos_120_R2
