import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R4 of step Erdos142.erdos_142.variants.lower.R1.H2
-- Credit: @Pixelstorm44

/-!
A logarithmic moment of the reciprocal sum suffices for a square-logarithmic
density saving. Pack extremizers at scales 4^j into separated intervals.
Writing d_j for their normalized sizes, the moment controls the series of
j*d_j. Since d_j decreases, its tail on [m,2m) dominates m^2*d_(2m).
Rounding an arbitrary length up to a power of sixteen then gives the claim.

The packing statement, positive-step conversion, extremizers, subadditivity,
and the disjoint-block encoding are adapted from reduction R2 of the parent
Erdős 142 lower bound. The packing statement is identical to the solved lower.R2.H2.
The weighted moment is an additional hypothesis. It does not follow from
summability of the unweighted reciprocal series alone.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R4

open Erdos142 Filter Real
open scoped Topology

/-- On separated geometric blocks, divergence of the first logarithmic
moment of reciprocal mass forces every fixed progression length at least four. -/
def H1 : Prop :=
  ∀ A : Set ℕ, (∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →
    ¬ Summable (A.indicator (fun n : ℕ ↦ (Nat.log 4 n : ℝ) / n)) →
    ∀ k : ℕ, 4 ≤ k → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- Packing each progression-free block preserves the absence of a progression. -/
def H2 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (B : ℕ → Finset ℕ), (∀ j, B j ⊆ Finset.Icc 1 (4 ^ j)) →
    (∀ j, ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ B j) →
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, ∃ j b, b ∈ B j ∧ a + i * d = 4 * 4 ^ j + b

theorem card_le_maxCard {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : (S : Set ℕ).IsAPOfLengthFree k) :
    S.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
  unfold Set.IsAPOfLengthFree.maxCard
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro _ ⟨U, hU, _, rfl⟩
    exact (Finset.card_mono hU).trans_eq (Nat.card_Icc 1 N)
  · exact ⟨S, hS, hfree, rfl⟩

theorem maxCard_monotone (k : ℕ) : Monotone (Set.IsAPOfLengthFree.maxCard k) := by
  intro M N hMN
  apply csSup_le'
  rintro _ ⟨S, hS, hfree, rfl⟩
  exact card_le_maxCard (hS.trans (Finset.Icc_subset_Icc_right hMN)) hfree

theorem isAPOfLength_translate {t : Set ℕ} {k : ℕ} (ht : t.IsAPOfLength k) (M : ℕ) :
    ((fun x : ℕ ↦ M + x) '' t).IsAPOfLength k := by
  obtain ⟨a, d, hc, ht⟩ := ht
  refine ⟨M + a, d, ?_, ?_⟩
  · have hi : Function.Injective (fun x : ℕ ↦ M + x) := fun _ _ h ↦ Nat.add_left_cancel h
    simpa only [ENat.card_coe_set_eq, hi.encard_image] using hc
  · rw [ht]
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, by simp [Nat.add_assoc]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨a + i • d, ⟨i, hi, rfl⟩, by simp [Nat.add_assoc]⟩

theorem maxCard_add_le (k M N : ℕ) :
    Set.IsAPOfLengthFree.maxCard k (M + N) ≤
      Set.IsAPOfLengthFree.maxCard k M + Set.IsAPOfLengthFree.maxCard k N := by
  classical
  apply csSup_le'
  rintro _ ⟨S, hS, hfree, rfl⟩
  let L := S.filter fun x ↦ x ≤ M
  let R := S.filter fun x ↦ ¬ x ≤ M
  let T := R.image fun x ↦ x - M
  have hL : L.card ≤ Set.IsAPOfLengthFree.maxCard k M := by
    apply card_le_maxCard
    · intro x hx
      obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hS hxS)).1, hxM⟩
    · intro t ht h
      apply hfree t _ h
      exact ht.trans (fun _ hx ↦ (Finset.mem_filter.mp hx).1)
  have hT : T.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
    apply card_le_maxCard
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hyS, hyM⟩ := Finset.mem_filter.mp hy
      have hyMN := (Finset.mem_Icc.mp (hS hyS)).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro t ht h
      apply hfree ((fun x : ℕ ↦ M + x) '' t) _ (isAPOfLength_translate h M)
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (ht hx)
      obtain ⟨hyS, hyM⟩ := Finset.mem_filter.mp hy
      change M + (y - M) ∈ S
      rwa [Nat.add_sub_of_le (by omega : M ≤ y)]
  have hRT : T.card = R.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy h
    have hxM := (Finset.mem_filter.mp hx).2
    have hyM := (Finset.mem_filter.mp hy).2
    change x - M = y - M at h
    omega
  have hLR : L.card + R.card = S.card := Finset.card_filter_add_card_filter_not _
  omega

theorem maxCard_double_le (k N : ℕ) :
    Set.IsAPOfLengthFree.maxCard k (2 * N) ≤ 2 * Set.IsAPOfLengthFree.maxCard k N := by
  simpa only [two_mul] using maxCard_add_le k N N

theorem dyadic_density_antitone (k : ℕ) :
    Antitone (fun j : ℕ ↦ (Set.IsAPOfLengthFree.maxCard k (2 ^ j) : ℝ) / (2 : ℝ) ^ j) := by
  apply antitone_nat_of_succ_le
  intro j
  have hnat := maxCard_double_le k (2 ^ j)
  have h : (Set.IsAPOfLengthFree.maxCard k (2 * 2 ^ j) : ℝ) ≤
      2 * (Set.IsAPOfLengthFree.maxCard k (2 ^ j) : ℝ) := by exact_mod_cast hnat
  simp only [pow_succ']
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (2 : ℝ) ^ j)]

theorem summable_weighted_density
    (B : ℕ → Finset ℕ) (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j))
    (A : Set ℕ) (hA : ∀ j b, b ∈ B j → 4 * 4 ^ j + b ∈ A)
    (hsum : Summable (A.indicator (fun n : ℕ ↦ (Nat.log 4 n : ℝ) / n))) :
    Summable (fun j : ℕ ↦ (j : ℝ) * (((B j).card : ℝ) / (4 : ℝ) ^ j)) := by
  classical
  let encode (p : (j : ℕ) × ↥(B j)) : ℕ := 4 * 4 ^ p.1 + p.2.1
  have ordered {i j : ℕ} (hij : i < j) (a : B i) (b : B j) :
      encode ⟨i, a⟩ < encode ⟨j, b⟩ := by
    have ha := (Finset.mem_Icc.mp (hB i a.property)).2
    have hp : (4 : ℕ) ^ (i + 1) ≤ 4 ^ j := Nat.pow_le_pow_right (by decide) hij
    rw [pow_succ] at hp
    have hpos : 0 < (4 : ℕ) ^ i := by positivity
    dsimp [encode]
    omega
  have hinj : Function.Injective encode := by
    rintro ⟨i, a⟩ ⟨j, b⟩ heq
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact ((ordered hij a b).ne heq).elim
    · have hval : a.val = b.val := by simpa [encode] using heq
      rw [Subtype.ext hval]
    · exact ((ordered hji b a).ne heq.symm).elim
  have hscale : Summable (fun p : (j : ℕ) × ↥(B j) ↦ (p.1 : ℝ) * ((4 : ℝ)^p.1)⁻¹) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _
      ((hsum.comp_injective hinj).mul_left 5)
    rintro ⟨j, b⟩
    change (j : ℝ) * ((4 : ℝ)^j)⁻¹ ≤ 5 * A.indicator _ (encode ⟨j, b⟩)
    rw [Set.indicator_of_mem (hA j b b.property)]
    have hb := (Finset.mem_Icc.mp (hB j b.property)).2
    have hupper : (encode ⟨j, b⟩ : ℝ) ≤ 5 * (4 : ℝ)^j := by
      exact_mod_cast (show encode ⟨j, b⟩ ≤ 5 * 4 ^ j by dsimp [encode]; omega)
    have hencode : 0 < (encode ⟨j, b⟩ : ℝ) := by
      exact_mod_cast (show 0 < encode ⟨j, b⟩ by dsimp [encode]; positivity)
    have hfrac : 1 / (4 : ℝ)^j ≤ 5 / (encode ⟨j, b⟩ : ℝ) :=
      (div_le_div_iff₀ (by positivity) hencode).mpr (by simpa using hupper)
    have hj : j ≤ Nat.log 4 (encode ⟨j,b⟩) := by
      apply Nat.le_log_of_pow_le (by decide)
      dsimp [encode]
      omega
    have hjR : (j : ℝ) ≤ Nat.log 4 (encode ⟨j,b⟩) := by exact_mod_cast hj
    calc
      _ ≤ (j : ℝ) * (5 / (encode ⟨j,b⟩ : ℝ)) := by
        simpa only [one_div] using mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg j)
      _ ≤ (Nat.log 4 (encode ⟨j,b⟩) : ℝ) * (5 / (encode ⟨j,b⟩ : ℝ)) := by gcongr
      _ = _ := by ring
  have hfiber := hscale.sigma
  have hf (j : ℕ) : (∑' b : B j, (j : ℝ) * ((4 : ℝ)^j)⁻¹) =
      (j : ℝ) * (((B j).card : ℝ) / (4 : ℝ)^j) := by
    simp [tsum_fintype, div_eq_mul_inv, mul_left_comm]
  simpa only [hf] using hfiber

/-- The mass on [m,2m) dominates m squared times the density at 2m. -/
lemma square_tail {d : ℕ → ℝ} (hn : ∀ j, 0 ≤ d j) (ha : Antitone d)
    (hs : Summable (fun j : ℕ ↦ (j : ℝ) * d j)) :
    Tendsto (fun m : ℕ ↦ (m : ℝ)^2 * d (2*m)) atTop (𝓝 0) := by
  have hdouble : Tendsto (fun m : ℕ ↦ 2*m) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b, fun n h ↦ by omega⟩
  have ht := (hs.tendsto_sum_tsum_nat.comp hdouble).sub hs.tendsto_sum_tsum_nat
  have ht' : Tendsto (fun m : ℕ ↦ ∑ i ∈ Finset.Ico m (2*m), (i : ℝ)*d i) atTop (𝓝 0) := by
    have htail (m : ℕ) := Finset.sum_Ico_eq_sub (fun i : ℕ ↦ (i : ℝ)*d i)
      (show m ≤ 2*m by omega)
    simpa only [htail, Function.comp_apply, Pi.sub_apply, sub_self] using ht
  apply squeeze_zero (fun m ↦ mul_nonneg (sq_nonneg _) (hn _)) _ ht'
  intro m
  calc
    _ = ∑ _i ∈ Finset.Ico m (2*m), (m : ℝ)*d (2*m) := by
      simp [show 2*m-m=m by omega, pow_two, mul_assoc]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hi
      exact mul_le_mul (by exact_mod_cast hl) (ha hu.le) (hn _) (Nat.cast_nonneg i)

/-- Interpolate the square-log estimate from powers of sixteen. -/
lemma interpolate (f : ℕ → ℕ) (hm : Monotone f)
    (ht : Tendsto (fun m : ℕ ↦ (m : ℝ)^2 * ((f (16^m) : ℝ) / (16:ℝ)^m))
      atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ (N : ℝ) / log (N : ℝ)^2 := by
  have hl : 0 < log 16 := log_pos (by norm_num)
  have hc : 0 < 1 / (16 * (log 16)^2) := by positivity
  obtain ⟨J,hJ⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hc))
  filter_upwards [eventually_ge_atTop (16^J), eventually_gt_atTop (1 : ℕ)] with N hlarge hN
  let m := Nat.log 16 N + 1
  have hJm : J ≤ m := (Nat.le_log_of_pow_le (by decide) hlarge).trans (Nat.le_succ _)
  have hscale := (hJ m hJm).le
  change (m : ℝ)^2 * ((f (16^m) : ℝ) / (16:ℝ)^m) ≤ 1 / (16 * (log 16)^2) at hscale
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNlog : 0 < log N := log_pos (by exact_mod_cast hN)
  have hup : N ≤ 16^m := (Nat.lt_pow_succ_log_self (by decide : 1 < 16) N).le
  have hupR : (N : ℝ) ≤ (16 : ℝ)^m := by exact_mod_cast hup
  have hceil : (16 : ℝ)^m ≤ 16 * N := by
    have hfloor := Nat.pow_log_le_self 16 (by omega : N ≠ 0)
    dsimp [m]
    rw [pow_succ, mul_comm]
    gcongr
    exact_mod_cast hfloor
  have hf : (f N : ℝ) ≤ (f (16^m) : ℝ) := by exact_mod_cast hm hup
  have hlog : log N ≤ (m : ℝ) * log 16 := by
    simpa only [log_pow] using log_le_log hNpos hupR
  rw [← mul_div_assoc] at hscale
  have hprod := (div_le_div_iff₀ (by positivity) (by positivity)).mp hscale
  apply (le_div_iff₀ (sq_pos_of_pos hNlog)).mpr
  calc
    _ ≤ (f (16^m) : ℝ) * ((m : ℝ) * log 16)^2 := by gcongr
    _ ≤ _ := by nlinarith only [hprod, hceil]

lemma no_positive_step {A : Set ℕ} {k : ℕ} (hk : 1 < k) (hfree : A.IsAPOfLengthFree k) :
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  rintro ⟨a, d, hd, hmem⟩
  let T := (Finset.range k).image fun i => a + i * d
  have hcard : T.card = k := by
    have hinj : Function.Injective (fun i : ℕ => a + i * d) := by
      intro x y h
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
    simp [T, Finset.card_image_of_injective _ hinj]
  have hsub : (T : Set ℕ) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i (Finset.mem_range.mp hi)
  have hap' : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, by simp [hcard], ?_⟩
    ext x
    simp [T]
  have hle := hfree (T : Set ℕ) hsub hap'
  exact (not_le_of_gt hk) (by exact_mod_cast hle)

/-- The natural-number supremum defining the extremal cardinality is attained. -/
lemma extremizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      S.card = r k N := by
  let c : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hnon : c.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro t ht hprogression
    have ht' : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    have hpos : 0 < (k : ℕ∞) := by exact_mod_cast (show 0 < k by omega)
    exact (Set.not_isAPOfLength_empty hpos (ht' ▸ hprogression)).elim
  have hbound : BddAbove c := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hs, _, rfl⟩
    exact (Finset.card_mono hs).trans_eq (Nat.card_Icc 1 N)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hnon hbound
  exact ⟨S, hS, hfree, hcard⟩

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1.H2 := by
  intro hrec hpack k hk
  have hthree : 3 ≤ k := by omega
  choose B hB hfree hcard using fun j : ℕ ↦ extremizer (by omega : 1 < k) (4 ^ j)
  let A : Set ℕ := {x | ∃ j b, b ∈ B j ∧ x = 4 * 4 ^ j + b}
  have hsupport (x : ℕ) (hx : x ∈ A) : ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j := by
    obtain ⟨j, b, hb, rfl⟩ := hx
    have h := Finset.mem_Icc.mp (hB j hb)
    exact ⟨j, by omega, by omega⟩
  have hnoAP := hpack k hthree B hB (fun j ↦ no_positive_step (by omega : 1 < k) (hfree j))
  have hsum : Summable (A.indicator (fun n : ℕ ↦ (Nat.log 4 n : ℝ) / n)) := by
    by_contra h
    exact hnoAP (hrec A hsupport h k hk)
  have hden : Summable (fun j : ℕ ↦ (j : ℝ) * ((r k (4 ^ j) : ℝ) / (4 : ℝ)^j)) := by
    simpa only [hcard] using summable_weighted_density
      B hB A (fun j b hb ↦ ⟨j, b, hb, rfl⟩) hsum
  have hmono : Antitone (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ)^j) := by
    intro i j hij
    have hd := dyadic_density_antitone k (show 2 * i ≤ 2 * j by omega)
    simpa only [pow_mul, Nat.reducePow, show (2 : ℝ)^2 = 4 by norm_num] using hd
  have ht := square_tail (d := fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ)^j)
    (fun _ ↦ by positivity) hmono hden
  refine ⟨1, by norm_num, ?_⟩
  rw [show (1 : ℝ) + 1 = 2 by norm_num]
  simp only [rpow_two]
  apply interpolate _ (maxCard_monotone k)
  simpa only [pow_mul, Nat.reducePow, show (4 : ℝ)^2 = 16 by norm_num] using ht

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R4
