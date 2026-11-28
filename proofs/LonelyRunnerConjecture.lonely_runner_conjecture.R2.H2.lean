import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_R2
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.GCDMonoid.Finset

/-!
Proof of Step `LonelyRunnerConjecture.lonely_runner_conjecture.R2.H2`:
Malikiosis-Santos-Schymura (2025) zonotopal subset-GCD sum finite-checking
reduction for the Lonely Runner Conjecture, proved directly in integer,
modular, and `UnitAddCircle` coordinates.
Credit: @paynebrowning
-/

noncomputable section

/- ### Module 0: Elementary Binomial & UnitAddCircle Helpers -/

private lemma two_mul_choose_two (n : ℕ) : 2 * Nat.choose (n + 1) 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, mul_add, ih]
    ring

private lemma unitAddCircle_dist_neg (x : ℝ) :
    dist ((-x : ℝ) : UnitAddCircle) 0 = dist (x : UnitAddCircle) 0 := by
  rw [dist_zero_right, dist_zero_right, QuotientAddGroup.mk_neg, norm_neg]

private lemma unitAddCircle_dist_abs (x : ℝ) :
    dist ((|x| : ℝ) : UnitAddCircle) 0 = dist (x : UnitAddCircle) 0 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, unitAddCircle_dist_neg]

private lemma unitAddCircle_dist_eq_abs_of_lt_half {x : ℝ} (hx : |x| < 1 / 2) :
    dist (x : UnitAddCircle) 0 = |x| := by
  rw [dist_zero_right, UnitAddCircle.norm_eq]
  have hround_zero : round x = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(round x : ℝ)| := by
      have hint : (1 : ℤ) ≤ |round x| := Int.one_le_abs hne
      exact_mod_cast hint
    have h2 : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    have h3 : |(round x : ℝ)| ≤ |x - (round x : ℝ)| + |x| := by
      calc
        |(round x : ℝ)| = |((round x : ℝ) - x) + x| := by ring_nf
        _ ≤ |(round x : ℝ) - x| + |x| := abs_add_le _ _
        _ = |x - (round x : ℝ)| + |x| := by rw [abs_sub_comm]
    linarith
  rw [hround_zero, Int.cast_zero, sub_zero]

private lemma unitAddCircle_int_cast_eq_zero (z : ℤ) :
    (((z : ℝ) : UnitAddCircle)) = 0 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
  exact ⟨z, by simp⟩

/- ### Module 1: Bézout Combination & ZMod Hyperplane Cardinality -/

private lemma mss_gcd_eq_nat_gcd (a b : ℕ) : GCDMonoid.gcd a b = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (GCDMonoid.gcd_dvd_left a b) (GCDMonoid.gcd_dvd_right a b)
  · exact GCDMonoid.dvd_gcd (Nat.gcd_dvd_left a b) (GCDMonoid.gcd_dvd_right a b)

private lemma finset_gcd_bezout {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℕ) :
    ∃ c : ι → ℤ, ((s.gcd w : ℕ) : ℤ) = ∑ i ∈ s, c i * (w i : ℤ) := by
  induction s using Finset.cons_induction with
  | empty =>
    exact ⟨fun _ => 0, by simp⟩
  | cons a s has ih =>
    obtain ⟨c, hc⟩ := ih
    rw [Finset.gcd_cons, mss_gcd_eq_nat_gcd]
    let A := Nat.gcdA (w a) (s.gcd w)
    let B := Nat.gcdB (w a) (s.gcd w)
    refine ⟨fun i => if i = a then A else B * c i, ?_⟩
    rw [Finset.sum_cons]
    dsimp only
    rw [if_pos rfl]
    have hsum : ∑ x ∈ s, (if x = a then A else B * c x) * (w x : ℤ) =
        B * ∑ x ∈ s, c x * (w x : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hne : x ≠ a := fun h => has (h ▸ hx)
      rw [if_neg hne, mul_assoc]
    rw [hsum, ← hc]
    have hbez := Nat.gcd_eq_gcd_ab (w a) (s.gcd w)
    linarith

private def bezoutLinear {k ℓ : ℕ} (c : Fin k → ℤ) (y : Fin k → ZMod ℓ) : ZMod ℓ :=
  ∑ i : Fin k, (c i : ZMod ℓ) * y i

private lemma bezoutLinear_eval_w {k ℓ : ℕ} (w : Fin k → ℕ) (c : Fin k → ℤ)
    (hc : ∑ i : Fin k, c i * (w i : ℤ) = 1) :
    bezoutLinear (ℓ := ℓ) c (fun i => (w i : ZMod ℓ)) = 1 := by
  have h := congr_arg (Int.cast : ℤ → ZMod ℓ) hc
  simpa [bezoutLinear, Int.cast_sum, Int.cast_mul, Int.cast_natCast] using h

private lemma bezoutLinear_add_smul {k ℓ : ℕ} (w : Fin k → ℕ) (c : Fin k → ℤ)
    (hc : ∑ i : Fin k, c i * (w i : ℤ) = 1) (y : Fin k → ZMod ℓ) (t : ZMod ℓ) :
    bezoutLinear c (fun i => y i + t * (w i : ZMod ℓ)) = bezoutLinear c y + t := by
  unfold bezoutLinear
  have h1 : ∑ i : Fin k, (c i : ZMod ℓ) * (y i + t * (w i : ZMod ℓ)) =
      (∑ i : Fin k, (c i : ZMod ℓ) * y i) +
      t * (∑ i : Fin k, (c i : ZMod ℓ) * (w i : ZMod ℓ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1]
  have hw := bezoutLinear_eval_w (ℓ := ℓ) w c hc
  unfold bezoutLinear at hw
  rw [hw, mul_one]

private lemma bezoutLinear_sub_smul {k ℓ : ℕ} (w : Fin k → ℕ) (c : Fin k → ℤ)
    (hc : ∑ i : Fin k, c i * (w i : ℤ) = 1) (y : Fin k → ZMod ℓ) (t : ZMod ℓ) :
    bezoutLinear c (fun i => y i - t * (w i : ZMod ℓ)) = bezoutLinear c y - t := by
  have h := bezoutLinear_add_smul (ℓ := ℓ) w c hc y (-t)
  simpa [sub_eq_add_neg, neg_mul] using h

private def kerBezoutEquiv {k ℓ : ℕ} (w : Fin k → ℕ) (c : Fin k → ℤ)
    (hc : ∑ i : Fin k, c i * (w i : ℤ) = 1) :
    { u : Fin k → ZMod ℓ // bezoutLinear c u = 0 } × ZMod ℓ ≃ (Fin k → ZMod ℓ) where
  toFun p i := p.1.1 i + p.2 * (w i : ZMod ℓ)
  invFun y := (⟨fun i => y i - bezoutLinear c y * (w i : ZMod ℓ), by
    rw [bezoutLinear_sub_smul w c hc, sub_self]⟩, bezoutLinear c y)
  left_inv := by
    rintro ⟨⟨u, hu⟩, t⟩
    have hL : bezoutLinear c (fun i => u i + t * (w i : ZMod ℓ)) = t := by
      rw [bezoutLinear_add_smul w c hc, hu, zero_add]
    ext i
    · dsimp
      rw [hL]
      ring
    · dsimp
      exact hL
  right_inv := by
    intro y
    ext i
    dsimp
    ring

private lemma card_kerBezout_eq {k ℓ : ℕ} [NeZero ℓ] (hk : 1 ≤ k) (w : Fin k → ℕ)
    (c : Fin k → ℤ) (hc : ∑ i : Fin k, c i * (w i : ℤ) = 1) :
    Fintype.card { u : Fin k → ZMod ℓ // bezoutLinear c u = 0 } = ℓ ^ (k - 1) := by
  have hcard := Fintype.card_congr (kerBezoutEquiv (ℓ := ℓ) w c hc)
  rw [Fintype.card_prod, ZMod.card, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
  have hk_eq : ℓ ^ k = ℓ ^ (k - 1) * ℓ := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  rw [hk_eq] at hcard
  exact Nat.mul_right_cancel (NeZero.pos ℓ) hcard

/- ### Module 2: Direct Floor Coset Injection -/

private abbrev NonemptyPowerset (k : ℕ) : Finset (Finset (Fin k)) :=
  (Finset.univ : Finset (Fin k)).powerset.erase ∅

private abbrev Idx (k : ℕ) (w : Fin k → ℕ) : Type :=
  Σ S : { S : Finset (Fin k) // S ∈ NonemptyPowerset k }, Fin (S.1.gcd w)

private lemma card_idx_eq (k : ℕ) (w : Fin k → ℕ) :
    Fintype.card (Idx k w) = ∑ S ∈ NonemptyPowerset k, S.gcd w := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach (NonemptyPowerset k) (fun S => S.gcd w)

private lemma subset_nonempty_of_mem {k : ℕ} {S : Finset (Fin k)} (hS : S ∈ NonemptyPowerset k) :
    S.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1

private lemma subset_gcd_pos {k : ℕ} {w : Fin k → ℕ} (hw : ∀ i, 0 < w i)
    {S : Finset (Fin k)} (hS : S ∈ NonemptyPowerset k) : 0 < S.gcd w := by
  obtain ⟨i₀, hi₀⟩ := subset_nonempty_of_mem hS
  have hdvd : S.gcd w ∣ w i₀ := Finset.gcd_dvd hi₀
  rcases Nat.eq_zero_or_pos (S.gcd w) with h0 | hpos
  · rw [h0, zero_dvd_iff] at hdvd
    exact absurd hdvd (Nat.ne_of_gt (hw i₀))
  · exact hpos

private def alphaVal {k : ℕ} {w : Fin k → ℕ} (x : Idx k w) : ℝ :=
  (x.2.val : ℝ) / ((x.1.1.gcd w : ℕ) : ℝ)

private lemma alphaVal_nonneg {k : ℕ} {w : Fin k → ℕ} (x : Idx k w) : 0 ≤ alphaVal x := by
  unfold alphaVal
  positivity

private lemma alphaVal_lt_one {k : ℕ} {w : Fin k → ℕ} (hw : ∀ i, 0 < w i) (x : Idx k w) :
    alphaVal x < 1 := by
  unfold alphaVal
  have hg : (0 : ℝ) < ((x.1.1.gcd w : ℕ) : ℝ) := Nat.cast_pos.mpr (subset_gcd_pos hw x.1.2)
  rw [div_lt_one hg]
  exact Nat.cast_lt.mpr x.2.isLt

private def zVec {k : ℕ} {w : Fin k → ℕ} (x : Idx k w) (i : Fin k) : ℤ :=
  let g : ℕ := x.1.1.gcd w
  let q_div : ℕ := w i / g
  if i ∈ x.1.1 then - ((x.2.val : ℤ) * (q_div : ℤ))
  else ⌊(1 : ℝ) - alphaVal x * (w i : ℝ)⌋

private lemma zVec_eq_zero_of_mem {k : ℕ} {w : Fin k → ℕ} (hw : ∀ i, 0 < w i)
    (x : Idx k w) {i : Fin k} (hi : i ∈ x.1.1) :
    (zVec x i : ℝ) + alphaVal x * (w i : ℝ) = 0 := by
  let g : ℕ := x.1.1.gcd w
  let q_div : ℕ := w i / g
  have hz : zVec x i = - ((x.2.val : ℤ) * (q_div : ℤ)) := by
    simp [zVec, hi, g, q_div]
  have hdvd : g ∣ w i := Finset.gcd_dvd hi
  have hmul : q_div * g = w i := Nat.div_mul_cancel hdvd
  have hg_pos : (0 : ℝ) < (g : ℝ) := Nat.cast_pos.mpr (subset_gcd_pos hw x.1.2)
  have hmul_real : (q_div : ℝ) * (g : ℝ) = (w i : ℝ) := by exact_mod_cast hmul
  have ha : alphaVal x = (x.2.val : ℝ) / (g : ℝ) := rfl
  rw [hz, ha, ← hmul_real]
  push_cast
  field_simp [ne_of_gt hg_pos]
  ring

private lemma zVec_mem_Ioc_of_not_mem {k : ℕ} {w : Fin k → ℕ}
    (x : Idx k w) {i : Fin k} (hi : i ∉ x.1.1) :
    0 < (zVec x i : ℝ) + alphaVal x * (w i : ℝ) ∧
      (zVec x i : ℝ) + alphaVal x * (w i : ℝ) ≤ 1 := by
  unfold zVec
  simp only [hi, ↓reduceIte]
  have h1 := Int.sub_one_lt_floor ((1 : ℝ) - alphaVal x * (w i : ℝ))
  have h2 := Int.floor_le ((1 : ℝ) - alphaVal x * (w i : ℝ))
  constructor <;> linarith

private lemma zVec_mem_Icc {k : ℕ} {w : Fin k → ℕ} (hw : ∀ i, 0 < w i)
    (x : Idx k w) (i : Fin k) :
    0 ≤ (zVec x i : ℝ) + alphaVal x * (w i : ℝ) ∧
      (zVec x i : ℝ) + alphaVal x * (w i : ℝ) ≤ 1 := by
  by_cases hi : i ∈ x.1.1
  · rw [zVec_eq_zero_of_mem hw x hi]
    exact ⟨le_rfl, zero_le_one⟩
  · obtain ⟨hpos, hle⟩ := zVec_mem_Ioc_of_not_mem x hi
    exact ⟨le_of_lt hpos, hle⟩

private lemma zVec_eq_zero_iff {k : ℕ} {w : Fin k → ℕ} (hw : ∀ i, 0 < w i)
    (x : Idx k w) (i : Fin k) :
    (zVec x i : ℝ) + alphaVal x * (w i : ℝ) = 0 ↔ i ∈ x.1.1 := by
  constructor
  · intro h0
    by_contra hi
    have hpos := (zVec_mem_Ioc_of_not_mem x hi).1
    linarith
  · exact zVec_eq_zero_of_mem hw x

private lemma zVec_mod_injective {k : ℕ} {w : Fin k → ℕ} (hw : ∀ i, 0 < w i)
    {x₁ x₂ : Idx k w} {m : ℤ}
    (hmod : ∀ i : Fin k, zVec x₁ i - zVec x₂ i = m * (w i : ℤ)) :
    x₁ = x₂ := by
  obtain ⟨i₁, hi₁⟩ := subset_nonempty_of_mem x₁.1.2
  obtain ⟨i₂, hi₂⟩ := subset_nonempty_of_mem x₂.1.2
  have hm_le : (m : ℝ) ≤ alphaVal x₂ - alphaVal x₁ := by
    have hz1 := zVec_eq_zero_of_mem hw x₁ hi₁
    have hz2 := (zVec_mem_Icc hw x₂ i₁).1
    have hdiff : (zVec x₁ i₁ : ℝ) - (zVec x₂ i₁ : ℝ) = (m : ℝ) * (w i₁ : ℝ) := by
      exact_mod_cast hmod i₁
    have hw1 : (0 : ℝ) < (w i₁ : ℝ) := Nat.cast_pos.mpr (hw i₁)
    have hprod : 0 ≤ (alphaVal x₂ - alphaVal x₁ - (m : ℝ)) * (w i₁ : ℝ) := by linarith
    have hnonneg : 0 ≤ alphaVal x₂ - alphaVal x₁ - (m : ℝ) :=
      nonneg_of_mul_nonneg_left hprod hw1
    linarith
  have hm_ge : alphaVal x₂ - alphaVal x₁ ≤ (m : ℝ) := by
    have hz2 := zVec_eq_zero_of_mem hw x₂ hi₂
    have hz1 := (zVec_mem_Icc hw x₁ i₂).1
    have hdiff : (zVec x₁ i₂ : ℝ) - (zVec x₂ i₂ : ℝ) = (m : ℝ) * (w i₂ : ℝ) := by
      exact_mod_cast hmod i₂
    have hw2 : (0 : ℝ) < (w i₂ : ℝ) := Nat.cast_pos.mpr (hw i₂)
    have hprod : 0 ≤ ((m : ℝ) - (alphaVal x₂ - alphaVal x₁)) * (w i₂ : ℝ) := by linarith
    have hnonneg : 0 ≤ (m : ℝ) - (alphaVal x₂ - alphaVal x₁) :=
      nonneg_of_mul_nonneg_left hprod hw2
    linarith
  have hm_eq : (m : ℝ) = alphaVal x₂ - alphaVal x₁ := le_antisymm hm_le hm_ge
  have ha1_0 := alphaVal_nonneg x₁
  have ha1_1 := alphaVal_lt_one hw x₁
  have ha2_0 := alphaVal_nonneg x₂
  have ha2_1 := alphaVal_lt_one hw x₂
  have hm_gt : ((-1 : ℤ) : ℝ) < (m : ℝ) := by push_cast; linarith
  have hm_lt : (m : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
  have hm_gt_int : (-1 : ℤ) < m := Int.cast_lt.mp hm_gt
  have hm_lt_int : m < 1 := Int.cast_lt.mp hm_lt
  have hm0 : m = 0 := by omega
  have halpha : alphaVal x₁ = alphaVal x₂ := by
    rw [hm0, Int.cast_zero] at hm_eq
    linarith
  have hz_eq : ∀ i : Fin k, zVec x₁ i = zVec x₂ i := by
    intro i
    have h := hmod i
    rw [hm0, zero_mul, sub_eq_zero] at h
    exact h
  have hS_eq : x₁.1 = x₂.1 := by
    apply Subtype.ext
    ext i
    rw [← zVec_eq_zero_iff hw x₁ i, ← zVec_eq_zero_iff hw x₂ i, hz_eq i, halpha]
  rcases x₁ with ⟨S₁, r₁⟩
  rcases x₂ with ⟨S₂, r₂⟩
  dsimp at hS_eq
  subst hS_eq
  congr 1
  apply Fin.ext
  unfold alphaVal at halpha
  dsimp at halpha
  have hg_pos : (0 : ℝ) < ((S₁.1.gcd w : ℕ) : ℝ) := Nat.cast_pos.mpr (subset_gcd_pos hw S₁.2)
  have hr_real : (r₁.val : ℝ) = (r₂.val : ℝ) := (div_left_inj' (ne_of_gt hg_pos)).mp halpha
  exact_mod_cast hr_real

/- ### Module 3: Pigeonhole Short Non-Proportional Vector -/

private lemma exists_short_nonproportional_vec {k : ℕ} (hk : 3 ≤ k) {w : Fin k → ℕ}
    (hw : ∀ i, 0 < w i) (hgcd : Finset.univ.gcd w = 1)
    (hsum : (Nat.choose (k + 1) 2) ^ (k - 1) < ∑ S ∈ NonemptyPowerset k, S.gcd w) :
    ∃ (q : Fin k → ℤ) (β : ℝ),
      (¬ ∃ γ : ℝ, ∀ i : Fin k, (q i : ℝ) = γ * (w i : ℝ)) ∧
      (∀ i : Fin k, |(q i : ℝ) + β * (w i : ℝ)| ≤ 2 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  obtain ⟨c, hc0⟩ := finset_gcd_bezout (Finset.univ : Finset (Fin k)) w
  rw [hgcd] at hc0
  have hc : ∑ i : Fin k, c i * (w i : ℤ) = 1 := hc0.symm
  let ℓ : ℕ := Nat.choose (k + 1) 2
  have hℓ_two : 2 * ℓ = k * (k + 1) := two_mul_choose_two k
  have hk_mul_pos : 0 < k * (k + 1) := Nat.mul_pos (by omega) (by omega)
  have hℓ_pos : 0 < ℓ := by omega
  have : NeZero ℓ := ⟨Nat.ne_of_gt hℓ_pos⟩
  let proj : Idx k w → { u : Fin k → ZMod ℓ // bezoutLinear c u = 0 } :=
    fun x => ((kerBezoutEquiv (ℓ := ℓ) w c hc).symm (fun i => (zVec x i : ZMod ℓ))).1
  have hcard_lt :
      Fintype.card { u : Fin k → ZMod ℓ // bezoutLinear c u = 0 } < Fintype.card (Idx k w) := by
    rw [card_kerBezout_eq (by omega) w c hc, card_idx_eq]
    exact hsum
  obtain ⟨x₁, x₂, hne, hproj⟩ := Fintype.exists_ne_map_eq_of_card_lt proj hcard_lt
  let y₁ : Fin k → ZMod ℓ := fun i => (zVec x₁ i : ZMod ℓ)
  let y₂ : Fin k → ZMod ℓ := fun i => (zVec x₂ i : ZMod ℓ)
  let t_mod : ZMod ℓ := bezoutLinear c y₁ - bezoutLinear c y₂
  let m : ℤ := (t_mod.val : ℤ)
  have hdvd : ∀ i : Fin k, (ℓ : ℤ) ∣ (zVec x₁ i - zVec x₂ i - m * (w i : ℤ)) := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h_eq_i := congr_fun (congr_arg Subtype.val hproj) i
    dsimp [proj, kerBezoutEquiv] at h_eq_i
    have ht_cast : (m : ZMod ℓ) = t_mod := by
      dsimp [m]
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    push_cast
    rw [ht_cast]
    dsimp [t_mod, y₁, y₂]
    linear_combination h_eq_i
  let q : Fin k → ℤ := fun i => Classical.choose (hdvd i)
  have hq_spec : ∀ i : Fin k, zVec x₁ i - zVec x₂ i - m * (w i : ℤ) = (ℓ : ℤ) * q i :=
    fun i => Classical.choose_spec (hdvd i)
  have hnot_prop : ¬ ∃ γ : ℝ, ∀ i : Fin k, (q i : ℝ) = γ * (w i : ℝ) := by
    rintro ⟨γ, hγ⟩
    have hreal : ∀ i : Fin k,
        (zVec x₁ i : ℝ) - (zVec x₂ i : ℝ) = ((m : ℝ) + (ℓ : ℝ) * γ) * (w i : ℝ) := by
      intro i
      have hi : (zVec x₁ i : ℝ) - (zVec x₂ i : ℝ) - (m : ℝ) * (w i : ℝ) =
          (ℓ : ℝ) * (q i : ℝ) := by exact_mod_cast hq_spec i
      rw [hγ i] at hi
      linarith
    let m' : ℤ := ∑ i : Fin k, c i * (zVec x₁ i - zVec x₂ i)
    have hm'_real : (m' : ℝ) = (m : ℝ) + (ℓ : ℝ) * γ := by
      dsimp [m']
      push_cast
      have hsum_eq : ∑ i : Fin k, (c i : ℝ) * ((zVec x₁ i : ℝ) - (zVec x₂ i : ℝ)) =
          ((m : ℝ) + (ℓ : ℝ) * γ) * ∑ i : Fin k, (c i : ℝ) * (w i : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hreal i]
        ring
      have hc_real : ∑ i : Fin k, (c i : ℝ) * (w i : ℝ) = 1 := by exact_mod_cast hc
      rw [hsum_eq, hc_real, mul_one]
    have hmod_m' : ∀ i : Fin k, zVec x₁ i - zVec x₂ i = m' * (w i : ℤ) := by
      intro i
      have hi := hreal i
      rw [← hm'_real] at hi
      exact_mod_cast hi
    exact hne (zVec_mod_injective hw hmod_m')
  let β : ℝ := (alphaVal x₁ - alphaVal x₂ + (m : ℝ)) / (ℓ : ℝ)
  refine ⟨q, β, hnot_prop, ?_⟩
  intro i
  have hℓ_real_pos : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ_pos
  have hℓ_real_eq : (ℓ : ℝ) = ((k : ℝ) * ((k : ℝ) + 1)) / 2 := by
    have h2 : (2 : ℝ) * (ℓ : ℝ) = (k : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hℓ_two
    linarith
  have hlin : (ℓ : ℝ) * ((q i : ℝ) + β * (w i : ℝ)) =
      ((zVec x₁ i : ℝ) + alphaVal x₁ * (w i : ℝ)) -
      ((zVec x₂ i : ℝ) + alphaVal x₂ * (w i : ℝ)) := by
    have hi : (zVec x₁ i : ℝ) - (zVec x₂ i : ℝ) - (m : ℝ) * (w i : ℝ) =
        (ℓ : ℝ) * (q i : ℝ) := by exact_mod_cast hq_spec i
    dsimp [β]
    field_simp [ne_of_gt hℓ_real_pos]
    linarith
  obtain ⟨hz1_0, hz1_1⟩ := zVec_mem_Icc hw x₁ i
  obtain ⟨hz2_0, hz2_1⟩ := zVec_mem_Icc hw x₂ i
  have habs_mul : |(ℓ : ℝ) * ((q i : ℝ) + β * (w i : ℝ))| ≤ 1 := by
    rw [hlin, abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hℓ_real_pos] at habs_mul
  have hk_pos : (0 : ℝ) < (k : ℝ) * ((k : ℝ) + 1) := by positivity
  rw [hℓ_real_eq] at habs_mul
  rw [le_div_iff₀ hk_pos]
  linarith

/- ### Module 4: 2×2 Ratio Extremum & Merged Smaller-Runner Instance -/

private lemma exists_merged_speeds {k : ℕ} (hk : 3 ≤ k) {w : Fin k → ℕ}
    (hw : ∀ i, 0 < w i) (hmono : StrictMono w) {q : Fin k → ℤ}
    (hnot_prop : ¬ ∃ γ : ℝ, ∀ i : Fin k, (q i : ℝ) = γ * (w i : ℝ)) :
    ∃ (Δw Δq : ℤ) (m : ℕ) (u : Fin m → ℕ),
      1 ≤ m ∧ m < k ∧ (∀ j : Fin m, 0 < u j) ∧ StrictMono u ∧
      ∀ i : Fin k, ∃ j : Fin m, |q i * Δw - (w i : ℤ) * Δq| = (u j : ℤ) := by
  have huniv_ne : (Finset.univ : Finset (Fin k)).Nonempty := by
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let ratio : Fin k → ℝ := fun i => (q i : ℝ) / (w i : ℝ)
  obtain ⟨i_min, _, hmin⟩ := Finset.exists_min_image Finset.univ ratio huniv_ne
  obtain ⟨i_max, _, hmax⟩ := Finset.exists_max_image Finset.univ ratio huniv_ne
  have hlt_ratio : ratio i_min < ratio i_max := by
    rcases lt_or_eq_of_le (hmin i_max (Finset.mem_univ _)) with hlt | heq
    · exact hlt
    · exfalso
      apply hnot_prop
      refine ⟨ratio i_min, fun i => ?_⟩
      have hi_ge := hmin i (Finset.mem_univ _)
      have hi_le := hmax i (Finset.mem_univ _)
      have hi_eq : ratio i = ratio i_min := by linarith
      dsimp [ratio] at hi_eq
      have hwi : (0 : ℝ) < (w i : ℝ) := Nat.cast_pos.mpr (hw i)
      exact (div_eq_iff (ne_of_gt hwi)).mp hi_eq
  have hne_idx : i_min ≠ i_max := fun h => by rw [h] at hlt_ratio; exact lt_irrefl _ hlt_ratio
  let a : Fin k := if i_min < i_max then i_min else i_max
  let b : Fin k := if i_min < i_max then i_max else i_min
  have hab_lt : a < b := by
    dsimp [a, b]
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (le_of_not_gt h) hne_idx.symm
  have hab_ne : a ≠ b := ne_of_lt hab_lt
  have hwa_lt_wb : w a < w b := hmono hab_lt
  let Δw : ℤ := (w b : ℤ) - (w a : ℤ)
  let Δq : ℤ := q b - q a
  have hΔw_pos : (0 : ℝ) < (Δw : ℝ) := by
    dsimp [Δw]
    push_cast
    exact sub_pos.mpr (Nat.cast_lt.mpr hwa_lt_wb)
  have hdet_ne : ∀ i : Fin k, q i * Δw - (w i : ℤ) * Δq ≠ 0 := by
    intro i
    have hwi_pos : (0 : ℝ) < (w i : ℝ) := Nat.cast_pos.mpr (hw i)
    have hwa_pos : (0 : ℝ) < (w a : ℝ) := Nat.cast_pos.mpr (hw a)
    have hwb_pos : (0 : ℝ) < (w b : ℝ) := Nat.cast_pos.mpr (hw b)
    have hreal_ne : (q i : ℝ) * (Δw : ℝ) - (w i : ℝ) * (Δq : ℝ) ≠ 0 := by
      by_cases hcond : i_min < i_max
      · have ha_eq : a = i_min := if_pos hcond
        have hb_eq : b = i_max := if_pos hcond
        have hi_le : ratio i ≤ ratio b := by rw [hb_eq]; exact hmax i (Finset.mem_univ _)
        have ha_lt_b : ratio a < ratio b := by rw [ha_eq, hb_eq]; exact hlt_ratio
        dsimp [ratio] at hi_le ha_lt_b
        rw [div_lt_div_iff₀ hwa_pos hwb_pos] at ha_lt_b
        rw [div_le_div_iff₀ hwi_pos hwb_pos] at hi_le
        have h1 : (q i : ℝ) * (w b : ℝ) ≤ (q b : ℝ) * (w i : ℝ) := hi_le
        have h2 : (q a : ℝ) * (w b : ℝ) < (q b : ℝ) * (w a : ℝ) := ha_lt_b
        have hΔw_eq : (Δw : ℝ) = (w b : ℝ) - (w a : ℝ) := by dsimp [Δw]; push_cast; rfl
        have hΔq_eq : (Δq : ℝ) = (q b : ℝ) - (q a : ℝ) := by dsimp [Δq]; push_cast; rfl
        rw [hΔw_eq, hΔq_eq]
        have hprod : ((q i : ℝ) * ((w b : ℝ) - (w a : ℝ)) -
            (w i : ℝ) * ((q b : ℝ) - (q a : ℝ))) * (w b : ℝ) < 0 := by
          calc
            ((q i : ℝ) * ((w b : ℝ) - (w a : ℝ)) -
                (w i : ℝ) * ((q b : ℝ) - (q a : ℝ))) * (w b : ℝ)
              = ((q i : ℝ) * (w b : ℝ) - (q b : ℝ) * (w i : ℝ)) * ((w b : ℝ) - (w a : ℝ)) +
                (w i : ℝ) * ((q a : ℝ) * (w b : ℝ) - (q b : ℝ) * (w a : ℝ)) := by ring
            _ < 0 := by
              have hterm1 : ((q i : ℝ) * (w b : ℝ) - (q b : ℝ) * (w i : ℝ)) *
                  ((w b : ℝ) - (w a : ℝ)) ≤ 0 :=
                mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
              have hterm2 : (w i : ℝ) * ((q a : ℝ) * (w b : ℝ) - (q b : ℝ) * (w a : ℝ)) < 0 :=
                mul_neg_of_pos_of_neg hwi_pos (by linarith)
              linarith
        intro hzero
        rw [hzero, zero_mul] at hprod
        exact lt_irrefl 0 hprod
      · have ha_eq : a = i_max := if_neg hcond
        have hb_eq : b = i_min := if_neg hcond
        have hi_ge : ratio b ≤ ratio i := by rw [hb_eq]; exact hmin i (Finset.mem_univ _)
        have hb_lt_a : ratio b < ratio a := by rw [ha_eq, hb_eq]; exact hlt_ratio
        dsimp [ratio] at hi_ge hb_lt_a
        rw [div_lt_div_iff₀ hwb_pos hwa_pos] at hb_lt_a
        rw [div_le_div_iff₀ hwb_pos hwi_pos] at hi_ge
        have h1 : (q b : ℝ) * (w i : ℝ) ≤ (q i : ℝ) * (w b : ℝ) := hi_ge
        have h2 : (q b : ℝ) * (w a : ℝ) < (q a : ℝ) * (w b : ℝ) := hb_lt_a
        have hΔw_eq : (Δw : ℝ) = (w b : ℝ) - (w a : ℝ) := by dsimp [Δw]; push_cast; rfl
        have hΔq_eq : (Δq : ℝ) = (q b : ℝ) - (q a : ℝ) := by dsimp [Δq]; push_cast; rfl
        rw [hΔw_eq, hΔq_eq]
        have hprod : 0 < ((q i : ℝ) * ((w b : ℝ) - (w a : ℝ)) -
            (w i : ℝ) * ((q b : ℝ) - (q a : ℝ))) * (w b : ℝ) := by
          calc
            0 < ((q i : ℝ) * (w b : ℝ) - (q b : ℝ) * (w i : ℝ)) * ((w b : ℝ) - (w a : ℝ)) +
                (w i : ℝ) * ((q a : ℝ) * (w b : ℝ) - (q b : ℝ) * (w a : ℝ)) := by
              have hterm1 : 0 ≤ ((q i : ℝ) * (w b : ℝ) - (q b : ℝ) * (w i : ℝ)) *
                  ((w b : ℝ) - (w a : ℝ)) :=
                mul_nonneg (by linarith) (by linarith)
              have hterm2 : 0 < (w i : ℝ) * ((q a : ℝ) * (w b : ℝ) - (q b : ℝ) * (w a : ℝ)) :=
                mul_pos hwi_pos (by linarith)
              linarith
            _ = ((q i : ℝ) * ((w b : ℝ) - (w a : ℝ)) -
                (w i : ℝ) * ((q b : ℝ) - (q a : ℝ))) * (w b : ℝ) := by ring
        intro hzero
        rw [hzero, zero_mul] at hprod
        exact lt_irrefl 0 hprod
    intro hzero
    apply hreal_ne
    exact_mod_cast hzero
  have hdet_ab : q a * Δw - (w a : ℤ) * Δq = q b * Δw - (w b : ℤ) * Δq := by
    dsimp [Δw, Δq]
    ring
  let D : Fin k → ℕ := fun i => (q i * Δw - (w i : ℤ) * Δq).natAbs
  let U : Finset ℕ := (Finset.univ.erase b).image D
  have ha_mem_erase : a ∈ Finset.univ.erase b :=
    Finset.mem_erase.mpr ⟨hab_ne, Finset.mem_univ a⟩
  have hU_nonempty : U.Nonempty := ⟨D a, Finset.mem_image_of_mem D ha_mem_erase⟩
  let m : ℕ := U.card
  have hm_ge : 1 ≤ m := Finset.card_pos.mpr hU_nonempty
  have hm_lt : m < k := by
    calc
      m ≤ (Finset.univ.erase b).card := Finset.card_image_le
      _ = k - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_fin]
      _ < k := by omega
  let emb := U.orderEmbOfFin rfl
  let u : Fin m → ℕ := fun j => emb j
  have hu_mono : StrictMono u := emb.strictMono
  have hu_pos : ∀ j : Fin m, 0 < u j := by
    intro j
    have hj_mem : u j ∈ U := Finset.orderEmbOfFin_mem U rfl j
    obtain ⟨i, _, hi_eq⟩ := Finset.mem_image.mp hj_mem
    rw [← hi_eq]
    exact Int.natAbs_pos.mpr (hdet_ne i)
  refine ⟨Δw, Δq, m, u, hm_ge, hm_lt, hu_pos, hu_mono, ?_⟩
  intro i
  have hDi_mem : D i ∈ U := by
    by_cases hib : i = b
    · subst hib
      have hDa_eq : D b = D a := by
        dsimp [D]
        rw [hdet_ab]
      rw [hDa_eq]
      exact Finset.mem_image_of_mem D ha_mem_erase
    · exact Finset.mem_image_of_mem D (Finset.mem_erase.mpr ⟨hib, Finset.mem_univ i⟩)
  have hDi_range : D i ∈ Set.range emb := by
    rw [Finset.range_orderEmbOfFin]
    exact hDi_mem
  obtain ⟨j, hj⟩ := hDi_range
  refine ⟨j, ?_⟩
  have hcast : ((D i : ℕ) : ℤ) = |q i * Δw - (w i : ℤ) * Δq| := Int.natCast_natAbs _
  rw [← hcast, ← hj]

/- ### Module 5: Inductive Lift in UnitAddCircle & Main Theorem -/

private theorem mss_gcd_sum_reduction (k : ℕ) (hk : 3 ≤ k) (w : Fin k → ℕ)
    (hw : ∀ i : Fin k, 0 < w i) (hmono : StrictMono w) (hgcd : Finset.univ.gcd w = 1)
    (hsum : (Nat.choose (k + 1) 2) ^ (k - 1) <
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd w)
    (h_smaller : ∀ (m : ℕ), 1 ≤ m → m < k → ∀ (u : Fin m → ℕ),
      (∀ i : Fin m, 0 < u i) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  obtain ⟨q, β, hnot_prop, hshort⟩ := exists_short_nonproportional_vec hk hw hgcd hsum
  obtain ⟨Δw, Δq, m, u, hm_ge, hm_lt, hu_pos, hu_mono, hu_cover⟩ :=
    exists_merged_speeds hk hw hmono hnot_prop
  obtain ⟨τ, hτ_nonneg, hτ⟩ := h_smaller m hm_ge hm_lt u hu_pos hu_mono
  let s : ℝ := τ * (Δw : ℝ)
  let t₀ : ℝ := -τ * (Δq : ℝ)
  let sqReal : Fin k → ℝ := fun i => s * (q i : ℝ) + t₀ * (w i : ℝ)
  have hdist_sq : ∀ i : Fin k,
      dist ((sqReal i : ℝ) : UnitAddCircle) 0 ≥ 1 / (k : ℝ) := by
    intro i
    obtain ⟨j, hj⟩ := hu_cover i
    have hj_real : |(q i : ℝ) * (Δw : ℝ) - (w i : ℝ) * (Δq : ℝ)| = (u j : ℝ) := by
      exact_mod_cast hj
    have hexpr : sqReal i = τ * ((q i : ℝ) * (Δw : ℝ) - (w i : ℝ) * (Δq : ℝ)) := by
      dsimp [sqReal, s, t₀]
      ring
    have habs_tau : |τ * ((q i : ℝ) * (Δw : ℝ) - (w i : ℝ) * (Δq : ℝ))| = τ * (u j : ℝ) := by
      rw [abs_mul, abs_of_nonneg hτ_nonneg, hj_real]
    rw [hexpr, ← unitAddCircle_dist_abs, habs_tau]
    have hm_le_k : ((m + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hm_lt
    have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    calc
      dist ((τ * (u j : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := hτ j
      _ ≥ 1 / (k : ℝ) := one_div_le_one_div_of_le hm_pos hm_le_k
  let z_s : ℤ := ⌊s + 1 / 2⌋
  let θ : ℝ := (z_s : ℝ) - s
  have hθ_abs : |θ| ≤ 1 / 2 := by
    dsimp [θ, z_s]
    rw [abs_le]
    have h1 := Int.sub_one_lt_floor (s + 1 / 2)
    have h2 := Int.floor_le (s + 1 / 2)
    constructor <;> linarith
  let t₁ : ℝ := t₀ + θ * β
  let t : ℝ := |t₁|
  refine ⟨t, abs_nonneg t₁, ?_⟩
  intro i
  have ht_abs : dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 =
      dist ((t₁ * (w i : ℝ) : ℝ) : UnitAddCircle) 0 := by
    dsimp [t]
    have hw_abs : |(w i : ℝ)| = (w i : ℝ) := abs_of_pos (Nat.cast_pos.mpr (hw i))
    have hmul : |t₁| * (w i : ℝ) = |t₁ * (w i : ℝ)| := by
      rw [abs_mul, hw_abs]
    rw [hmul, unitAddCircle_dist_abs]
  rw [ht_abs]
  let yReal : ℝ := t₁ * (w i : ℝ)
  let errReal : ℝ := -θ * ((q i : ℝ) + β * (w i : ℝ))
  let X : UnitAddCircle := (sqReal i : UnitAddCircle)
  let Y : UnitAddCircle := (yReal : UnitAddCircle)
  have hdiff_eq : X - Y = (errReal : UnitAddCircle) := by
    change (sqReal i : UnitAddCircle) - (yReal : UnitAddCircle) = (errReal : UnitAddCircle)
    rw [← QuotientAddGroup.mk_sub]
    have hring : sqReal i - yReal = (((z_s * q i : ℤ) : ℝ)) + errReal := by
      dsimp [sqReal, yReal, errReal, t₁, θ]
      push_cast
      ring
    rw [hring, QuotientAddGroup.mk_add, unitAddCircle_int_cast_eq_zero, zero_add]
  have herr_le : |errReal| ≤ 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
    dsimp [errReal]
    calc
      |-θ * ((q i : ℝ) + β * (w i : ℝ))| = |θ| * |(q i : ℝ) + β * (w i : ℝ)| := by
        rw [abs_mul, abs_neg]
      _ ≤ (1 / 2) * (2 / ((k : ℝ) * ((k : ℝ) + 1))) :=
        mul_le_mul hθ_abs (hshort i) (abs_nonneg _) (by norm_num)
      _ = 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by ring
  have herr_lt_half : |errReal| < 1 / 2 := by
    have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk_prod : (12 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := by nlinarith
    have hfrac_lt : 1 / ((k : ℝ) * ((k : ℝ) + 1)) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    exact lt_of_le_of_lt herr_le hfrac_lt
  have hdist_XY : dist X Y ≤ 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
    rw [dist_eq_norm, hdiff_eq, ← dist_zero_right, unitAddCircle_dist_eq_abs_of_lt_half herr_lt_half]
    exact herr_le
  have htri : dist X 0 ≤ dist X Y + dist Y 0 := dist_triangle X Y 0
  have hX0 : 1 / (k : ℝ) ≤ dist X 0 := hdist_sq i
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hfrac : 1 / (k : ℝ) - 1 / ((k : ℝ) * ((k : ℝ) + 1)) = 1 / (((k + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos]
    ring
  linarith

end

theorem OMA.solution : OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R2.H2 := by
  intro k hk w hw hmono hgcd _ _ _ hsum h_smaller _
  exact mss_gcd_sum_reduction k (by omega) w hw hmono hgcd hsum h_smaller
