import OMAStatements.S_mo_221428

/-!
Retains @connoranderson’s complete proof #25207, signed head
 9f9e35f86cefa220dfb3a0c9a505331d244ed35e, also linked by statement #19497.
Standard positive-product, measurable-intersection, order-cancellation and addition-injectivity APIs
replace the corresponding manual helper arguments. The cyclic ballot bound and
normalized-logarithm squeeze are unchanged.
Source: Vladimir, https://mathoverflow.net/questions/221428 (CC BY-SA 3.0).
Serguei Popov’s cyclic-rotation argument is credited below.
-/

namespace OMA.S_mo_221428

open Finset

/-- Rotate a walk with negative total immediately after the last maximizing
    prefix. Every nonempty prefix of this rotation has strictly negative sum.
    This cyclic-shift argument is due to Serguei Popov in the MO discussion. -/
theorem cyclic_ballot (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hend : (∑ j ∈ range (n + 1), v (Fin.ofNat (n + 1) j)) < 0) :
    ∃ r : Fin (n + 1), ∀ k : ℕ, 0 < k → k ≤ n + 1 →
      (∑ j ∈ range k, v (Fin.ofNat (n + 1) j + r)) < 0 := by
  classical
  let x (j : ℕ) := v (Fin.ofNat (n + 1) j)
  let S (k : ℕ) := ∑ j ∈ range k, x j
  have htotal : S (n + 1) < 0 := hend
  have period (j : ℕ) : x (n + 1 + j) = x j := by
    apply congrArg v
    apply Fin.ext
    simp [Fin.ofNat]
  have sadd (k : ℕ) : S (n + 1 + k) = S (n + 1) + S k := by
    unfold S
    rw [sum_range_add]
    simp only [period]
  obtain ⟨m, hm, hmax⟩ := (range (n + 1)).exists_max_image S (by simp)
  let M := (range (n + 1)).filter (fun a ↦ S a = S m)
  have hm' : m ∈ M := mem_filter.mpr ⟨hm, rfl⟩
  obtain ⟨r, hr, hlast⟩ := M.exists_max_image id ⟨m, hm'⟩
  obtain ⟨hrn, he⟩ := mem_filter.mp hr
  have hrlt := mem_range.mp hrn
  refine ⟨⟨r, hrlt⟩, ?_⟩
  intro k hk hkn
  have hdrop : S (r + k) < S r := by
    by_cases h : r + k < n + 1
    · have hle := hmax (r + k) (mem_range.mpr h)
      rw [he]
      refine lt_of_le_of_ne hle ?_
      intro heq
      have hindex := hlast (r + k) (mem_filter.mpr ⟨mem_range.mpr h, heq⟩)
      change r + k ≤ r at hindex
      omega
    · let a := r + k - (n + 1)
      have ha : a < n + 1 := by dsimp [a]; omega
      have hsplit : r + k = n + 1 + a := by dsimp [a]; omega
      have hle := hmax a (mem_range.mpr ha)
      rw [hsplit, sadd, he]
      linarith
  have hshift (j : ℕ) : x (r + j) = v (Fin.ofNat (n + 1) j + ⟨r, hrlt⟩) := by
    apply congrArg v
    apply Fin.ext
    simp [Fin.ofNat, Fin.add_def, Nat.add_comm r]
  change (∑ j ∈ range (r + k), x j) < (∑ j ∈ range r, x j) at hdrop
  rw [sum_range_add] at hdrop
  simpa only [← hshift, add_lt_iff_neg_left] using hdrop

end OMA.S_mo_221428

namespace OMA.S_mo_221428

open Filter Asymptotics
open scoped Topology

theorem same_rate (p q : ℕ → ℝ) (γ : ℝ) (hp : rate p γ)
    (hb : ∀ n : ℕ, 0<n → q n ≤ p n ∧ p n ≤ n*q n) : rate q γ := by
  have hpos : ∀ᶠ n in atTop, 0<q n := by
    filter_upwards [hp.1,eventually_gt_atTop 0] with n hn hn'
    exact pos_of_mul_pos_right (hn.trans_le (hb n hn').2) (Nat.cast_nonneg n)
  refine ⟨hpos,?_⟩
  have hsmall : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlow : Tendsto (fun n : ℕ => Real.log (p n)/(n:ℝ)-Real.log (n:ℝ)/(n:ℝ))
      atTop (𝓝 (-γ)) := by simpa using hp.2.sub hsmall
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hp.2
  · filter_upwards [hp.1,hpos,eventually_gt_atTop 0] with n hn hq hn'
    have hnr : (0:ℝ)<n := by exact_mod_cast hn'
    have hlog := Real.log_le_log hn (hb n hn').2
    rw [Real.log_mul hnr.ne' hq.ne'] at hlog
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hnr.le
  · filter_upwards [hpos,eventually_gt_atTop 0] with n hq hn
    exact div_le_div_of_nonneg_right (Real.log_le_log hq (hb n hn).1) (Nat.cast_nonneg n)

end OMA.S_mo_221428

namespace OMA.S_mo_221428

open MeasureTheory ProbabilityTheory Finset

private def good (n : ℕ) (ν : ℝ) (v : Fin (n+1) → ℝ) : Prop :=
  ∀ k : Fin (n+1), (∑ j ∈ range (k.val+1), (v (Fin.ofNat (n+1) j)-ν)) < 0

private theorem measurable_good (n : ℕ) (ν : ℝ) : MeasurableSet {v | good n ν v} := by
  unfold good
  measurability

private theorem ordinary_sum {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) (ν : ℝ) (n k : ℕ)
    (hk : k ≤ n+1) :
    (∑ j ∈ range k, (X (Fin.ofNat (n+1) j).val ω-ν)) = ∑ j ∈ range k, (X j ω-ν) := by
  apply sum_congr rfl
  intro j hj
  have h : j<n+1 := (mem_range.mp hj).trans_le hk
  simp [Fin.ofNat,Nat.mod_eq_of_lt h]

/-- The strict path probability lies between the endpoint probability and that probability
divided by the number of cyclic shifts. -/
theorem ballot_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (law : Measure ℝ) [IsProbabilityMeasure law] (ν : ℝ)
    (hi : iIndepFun X P) (hl : ∀ j, HasLaw (X j) law P) (n : ℕ) (hn : 0<n) :
    P.real (staysBelow X ν n) ≤ P.real (below X ν n) ∧
      P.real (below X ν n) ≤ n * P.real (staysBelow X ν n) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  constructor
  · refine measureReal_mono ?_ (measure_ne_top P _)
    intro ω hω
    exact hω _ (by omega) le_rfl
  let draw (r : Fin (n+1)) (ω : Ω) (j : Fin (n+1)) := X (j+r).val ω
  let A (r : Fin (n+1)) : Set Ω := {ω | good n ν (draw r ω)}
  have hA : ∀ r, P.real (A r) = (Measure.pi (fun _ : Fin (n+1) => law)).real {v | good n ν v} := by
    intro r
    have hvec : HasLaw (draw r) (Measure.pi (fun _ : Fin (n+1) => law)) P :=
      (hi.precomp (Fin.val_injective.comp (add_left_injective r))).hasLaw_pi (fun j => hl (j+r).val)
    exact hvec.measureReal_eq (measurable_good n ν)
  have h0 : A 0 = staysBelow X ν (n+1) := by
    ext ω
    change (∀ k : Fin (n+1), _) ↔ ∀ k : ℕ, 0<k → k≤n+1 → _
    simp only [draw,add_zero]
    constructor
    · intro hg k hk hkn
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      change (∑ j ∈ range (m+1), (X j ω-ν)) < 0
      simpa only [ordinary_sum X ω ν n (m+1) hkn] using hg ⟨m,by omega⟩
    · intro hg k
      rw [ordinary_sum X ω ν n (k.val+1) (by omega)]
      exact hg _ (by omega) (by omega)
  have hsub : below X ν (n+1) ⊆ ⋃ r, A r := by
    intro ω hω
    have hsum : (∑ j ∈ range (n+1), (X (Fin.ofNat (n+1) j).val ω-ν)) < 0 := by
      rw [ordinary_sum X ω ν n (n+1) le_rfl]
      exact hω
    obtain ⟨r,hr⟩ := cyclic_ballot n (fun j => X j.val ω - ν) hsum
    apply Set.mem_iUnion.mpr
    exact ⟨r,fun k => hr (k.val+1) (by omega) (by omega)⟩
  calc
    _ ≤ P.real (⋃ r, A r) := measureReal_mono hsub
    _ ≤ ∑ r, P.real (A r) := measureReal_iUnion_fintype_le (μ := P) A
    _ = _ := by
      simp_rw [fun r => (hA r).trans (hA 0).symm, h0]
      simp

end OMA.S_mo_221428

open OMA.S_mo_221428 in
theorem OMA.solution : type_of% @OMA.S_mo_221428.main := by
  intro Ω m P hP X law hl ν γ hi hX hInt hmean hγ hrate
  exact same_rate _ _ γ hrate (ballot_bounds P X law ν hi hX)
