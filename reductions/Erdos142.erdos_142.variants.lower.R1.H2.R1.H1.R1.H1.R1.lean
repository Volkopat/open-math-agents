import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R1 of step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1
-- Credit: @yhay81

/-!
# Gowers U^3 reduction for the k=4 super-polylogarithmic bound

We reduce the k=4 super-polylogarithmic bound (`r 4 N ≤ N * exp(-c * (log log N)^A)` for `A > 1`)
to two statements in `ZMod p` via Bertrand's postulate (`2N < p ≤ 4N`):
- `H1`: every sufficiently dense subset of `ZMod p` whose balanced function has large Gowers `U^3`
  norm contains a nontrivial 4-term arithmetic progression;
- `H2`: the Gowers `U^3` generalized von Neumann inequality on `ZMod p`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1

/-- Every sufficiently dense subset of ZMod p with large Gowers U^3 norm contains a
    nontrivial 4-term arithmetic progression in ZMod p. -/
def H1 : Prop :=
  ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ p : ℕ in Filter.atTop, ∀ [Fact p.Prime],
    ∀ S : Finset (ZMod p),
      let α : ℝ := (S.card : ℝ) / (p : ℝ)
      let f : ZMod p → ℝ := fun x => (if x ∈ S then (1 : ℝ) else 0) - α
      (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) < (S.card : ℝ) →
      (p : ℝ) ^ 4 * (α ^ 4 / 8) ^ 8 ≤
        ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
          f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
          f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃) →
      ∃ x d : ZMod p, d ≠ 0 ∧ x ∈ S ∧ x + d ∈ S ∧ x + 2 * d ∈ S ∧ x + 3 * d ∈ S

/-- Gowers U^3 generalized von Neumann inequality on ZMod p: the 4-AP linear form of
    bounded real functions is controlled by the Gowers U^3 cube sum. -/
def H2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∀ (c₀ c₁ c₂ c₃ : ZMod p),
      c₀ ≠ c₁ → c₀ ≠ c₂ → c₀ ≠ c₃ → c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ →
    ∀ (f₀ f₁ f₂ f₃ : ZMod p → ℝ),
      (∀ x, |f₀ x| ≤ 1) → (∀ x, |f₁ x| ≤ 1) → (∀ x, |f₂ x| ≤ 1) →
      (∑ x : ZMod p, ∑ d : ZMod p,
        f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)) ^ 8 ≤
      (p : ℝ) ^ 12 * ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        f₃ x * f₃ (x + h₁) * f₃ (x + h₂) * f₃ (x + h₁ + h₂) *
        f₃ (x + h₃) * f₃ (x + h₁ + h₃) * f₃ (x + h₂ + h₃) * f₃ (x + h₁ + h₂ + h₃)

lemma not_isAPOfLengthFree_four {S₀ : Set ℕ} {a step : ℕ} (hstep : 0 < step)
    (h0 : a ∈ S₀) (h1 : a + step ∈ S₀) (h2 : a + 2 * step ∈ S₀) (h3 : a + 3 * step ∈ S₀) :
    ¬ S₀.IsAPOfLengthFree 4 := by
  intro hfree
  let T : Finset ℕ := (Finset.range 4).image (fun i => a + i * step)
  have hsub : (T : Set ℕ) ⊆ S₀ := by
    intro y hy
    simp only [T, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    interval_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  have hinj : Function.Injective (fun i : ℕ => a + i * step) := by
    intro i j hij
    have hmul : i * step = j * step := Nat.add_left_cancel hij
    exact Nat.eq_of_mul_eq_mul_right hstep hmul
  have hcard : ENat.card (T : Set ℕ) = 4 := by
    have hTc : T.card = 4 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard, hTc]
    rfl
  have heq : (T : Set ℕ) = {a + n • step | (n : ℕ) (_ : n < (4 : ℕ∞))} := by
    ext y
    simp only [T, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
      Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by exact_mod_cast hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by exact_mod_cast hi, rfl⟩
  have h4le1 : (4 : ℕ∞) ≤ 1 := hfree (T : Set ℕ) hsub ⟨a, step, hcard, heq⟩
  exact absurd h4le1 (by decide)

lemma exists_extremal_4ap_free (N : ℕ) :
    ∃ S₀ : Finset ℕ, S₀ ⊆ Finset.Icc 1 N ∧ (S₀ : Set ℕ).IsAPOfLengthFree 4 ∧
      S₀.card = Erdos142.r 4 N := by
  let M : Set ℕ :=
    {Finset.card S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree 4)}
  have hne : M.Nonempty := by
    refine ⟨0, ∅, Finset.empty_subset _, ?_, Finset.card_empty⟩
    intro t ht hAP
    have hte : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    subst hte
    exact (Set.not_isAPOfLength_empty (by decide : (0 : ℕ∞) < 4) hAP).elim
  have hbdd : BddAbove M := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, -, rfl⟩
    exact (Finset.card_le_card hS).trans_eq (by simp [Nat.card_Icc])
  have hmem : sSup M ∈ M := Nat.sSup_mem hne hbdd
  obtain ⟨S₀, hsub, hfree, hcard⟩ := hmem
  exact ⟨S₀, hsub, hfree, hcard⟩

lemma natCast_eq_of_lt {p a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv

lemma embed_4ap_free {N p : ℕ} [Fact p.Prime] (hp : 2 * N < p) {S₀ : Finset ℕ}
    (hsub : S₀ ⊆ Finset.Icc 1 N) (hfree : (S₀ : Set ℕ).IsAPOfLengthFree 4) :
    (S₀.image (Nat.cast : ℕ → ZMod p)).card = S₀.card ∧
    ¬ ∃ x d : ZMod p, d ≠ 0 ∧
      x ∈ S₀.image (Nat.cast : ℕ → ZMod p) ∧
      x + d ∈ S₀.image (Nat.cast : ℕ → ZMod p) ∧
      x + 2 * d ∈ S₀.image (Nat.cast : ℕ → ZMod p) ∧
      x + 3 * d ∈ S₀.image (Nat.cast : ℕ → ZMod p) := by
  have hleN : ∀ a ∈ S₀, a ≤ N := fun a ha => (Finset.mem_Icc.mp (hsub ha)).2
  constructor
  · apply Finset.card_image_of_injOn
    intro a ha b hb hab
    exact natCast_eq_of_lt (by have := hleN a ha; omega) (by have := hleN b hb; omega) hab
  · rintro ⟨x, d, hd, h0, h1, h2, h3⟩
    obtain ⟨a₀, ha₀, hx0⟩ := Finset.mem_image.mp h0
    obtain ⟨a₁, ha₁, hx1⟩ := Finset.mem_image.mp h1
    obtain ⟨a₂, ha₂, hx2⟩ := Finset.mem_image.mp h2
    obtain ⟨a₃, ha₃, hx3⟩ := Finset.mem_image.mp h3
    have hN0 : a₀ ≤ N := hleN a₀ ha₀
    have hN1 : a₁ ≤ N := hleN a₁ ha₁
    have hN2 : a₂ ≤ N := hleN a₂ ha₂
    have hN3 : a₃ ≤ N := hleN a₃ ha₃
    have hmid1 : a₀ + a₂ = 2 * a₁ := by
      apply natCast_eq_of_lt (p := p) (by omega) (by omega)
      push_cast
      rw [hx0, hx1, hx2]
      ring
    have hmid2 : a₁ + a₃ = 2 * a₂ := by
      apply natCast_eq_of_lt (p := p) (by omega) (by omega)
      push_cast
      rw [hx1, hx2, hx3]
      ring
    have hne01 : a₀ ≠ a₁ := by
      intro h
      apply hd
      have hcast : (a₀ : ZMod p) = (a₁ : ZMod p) := congrArg Nat.cast h
      rw [hx0, hx1] at hcast
      exact (add_left_cancel (hcast.symm.trans (add_zero x).symm))
    rcases lt_or_gt_of_ne hne01 with hlt | hgt
    · set step : ℕ := a₁ - a₀
      have hstep : 0 < step := by omega
      have he1 : a₀ + step = a₁ := by omega
      have he2 : a₀ + 2 * step = a₂ := by omega
      have he3 : a₀ + 3 * step = a₃ := by omega
      exact not_isAPOfLengthFree_four hstep ha₀
        (by rw [he1]; exact ha₁) (by rw [he2]; exact ha₂) (by rw [he3]; exact ha₃) hfree
    · set step : ℕ := a₀ - a₁
      have hstep : 0 < step := by omega
      have he1 : a₃ + step = a₂ := by omega
      have he2 : a₃ + 2 * step = a₁ := by omega
      have he3 : a₃ + 3 * step = a₀ := by omega
      exact not_isAPOfLengthFree_four hstep ha₃
        (by rw [he1]; exact ha₂) (by rw [he2]; exact ha₁) (by rw [he3]; exact ha₀) hfree

lemma pow_eight_eq_abs_pow_eight (t : ℝ) : t ^ 8 = |t| ^ 8 := by
  calc t ^ 8 = (t ^ 2) ^ 4 := by ring
    _ = (|t| ^ 2) ^ 4 := by rw [sq_abs]
    _ = |t| ^ 8 := by ring

lemma pow_eight_add_four_le {a b c d M : ℝ}
    (ha : a ^ 8 ≤ M) (hb : b ^ 8 ≤ M) (hc : c ^ 8 ≤ M) (hd : d ^ 8 ≤ M) :
    (a + b + c + d) ^ 8 ≤ 4 ^ 8 * M := by
  set m : ℝ := max (max |a| |b|) (max |c| |d|) with hm_def
  have hma : |a| ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have hmb : |b| ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have hmc : |c| ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hmd : |d| ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  have habs : |a + b + c + d| ≤ 4 * m := by
    have h1 := abs_add_le (a + b + c) d
    have h2 := abs_add_le (a + b) c
    have h3 := abs_add_le a b
    linarith
  have hm8 : m ^ 8 ≤ M := by
    rcases max_choice (max |a| |b|) (max |c| |d|) with hL | hR
    · rcases max_choice |a| |b| with ha' | hb'
      · rw [hm_def, hL, ha', ← pow_eight_eq_abs_pow_eight]; exact ha
      · rw [hm_def, hL, hb', ← pow_eight_eq_abs_pow_eight]; exact hb
    · rcases max_choice |c| |d| with hc' | hd'
      · rw [hm_def, hR, hc', ← pow_eight_eq_abs_pow_eight]; exact hc
      · rw [hm_def, hR, hd', ← pow_eight_eq_abs_pow_eight]; exact hd
  calc (a + b + c + d) ^ 8
      = |a + b + c + d| ^ 8 := pow_eight_eq_abs_pow_eight _
    _ ≤ (4 * m) ^ 8 := pow_le_pow_left₀ (abs_nonneg _) habs 8
    _ = 4 ^ 8 * m ^ 8 := by ring
    _ ≤ 4 ^ 8 * M := mul_le_mul_of_nonneg_left hm8 (by positivity)

lemma zmod_natCast_ne (p a b : ℕ) (ha : a < p) (hb : b < p) (hne : a ≠ b) :
    (a : ZMod p) ≠ (b : ZMod p) :=
  fun h => hne (natCast_eq_of_lt ha hb h)

lemma gowers_u3_lower_bound (h2 : H2) {p : ℕ} [Fact p.Prime] (hp4 : 4 < p)
    (S : Finset (ZMod p))
    (hno : ¬ ∃ x d : ZMod p, d ≠ 0 ∧ x ∈ S ∧ x + d ∈ S ∧ x + 2 * d ∈ S ∧ x + 3 * d ∈ S)
    (hα2 : 2 ≤ (p : ℝ) * ((S.card : ℝ) / (p : ℝ)) ^ 3) :
    let α : ℝ := (S.card : ℝ) / (p : ℝ)
    let f : ZMod p → ℝ := fun x => (if x ∈ S then (1 : ℝ) else 0) - α
    (p : ℝ) ^ 4 * (α ^ 4 / 8) ^ 8 ≤
      ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
        f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃) := by
  intro α f
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hS_le_p : (S.card : ℝ) ≤ (p : ℝ) := by
    have hcard : S.card ≤ p := (Finset.card_le_univ S).trans_eq (ZMod.card p)
    exact_mod_cast hcard
  have hα_nonneg : 0 ≤ α := by positivity
  have hα_le_one : α ≤ 1 := (div_le_one hp_pos).mpr hS_le_p
  let g : ZMod p → ℝ := fun x => if x ∈ S then (1 : ℝ) else 0
  have hg_bdd : ∀ x : ZMod p, |g x| ≤ 1 := by
    intro x; by_cases hx : x ∈ S <;> simp [g, hx]
  have hα_bdd : ∀ _ : ZMod p, |α| ≤ 1 := by
    intro _; rw [abs_of_nonneg hα_nonneg]; exact hα_le_one
  have hsum_g :
      ∑ x : ZMod p, ∑ d : ZMod p, g x * g (x + d) * g (x + 2 * d) * g (x + 3 * d) =
        (p : ℝ) * α := by
    have hinner : ∀ x : ZMod p,
        ∑ d : ZMod p, g x * g (x + d) * g (x + 2 * d) * g (x + 3 * d) = g x := by
      intro x
      rw [Finset.sum_eq_single (0 : ZMod p)]
      · by_cases hx : x ∈ S <;> simp [g, hx]
      · intro d _ hd
        by_cases h0 : x ∈ S
        · by_cases h1 : x + d ∈ S
          · by_cases h2' : x + 2 * d ∈ S
            · by_cases h3 : x + 3 * d ∈ S
              · exact (hno ⟨x, d, hd, h0, h1, h2', h3⟩).elim
              · simp [g, h3]
            · simp [g, h2']
          · simp [g, h1]
        · simp [g, h0]
      · intro h0; exact (h0 (Finset.mem_univ 0)).elim
    simp_rw [hinner]
    have hsg : ∑ x : ZMod p, g x = (S.card : ℝ) := by
      simp [g]
    rw [hsg]
    dsimp only [α]
    field_simp
  have hsum_α : ∑ _x : ZMod p, ∑ _d : ZMod p, (α * α * α * α) = (p : ℝ) ^ 2 * α ^ 4 := by
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    ring
  let T₀ : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
    g (x + 1 * d) * g (x + 2 * d) * g (x + 3 * d) * f (x + 0 * d)
  let T₁ : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
    α * g (x + 2 * d) * g (x + 3 * d) * f (x + 1 * d)
  let T₂ : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
    α * α * g (x + 3 * d) * f (x + 2 * d)
  let T₃ : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
    α * α * α * f (x + 3 * d)
  have htele : (p : ℝ) * α - (p : ℝ) ^ 2 * α ^ 4 = T₀ + T₁ + T₂ + T₃ := by
    rw [← hsum_g, ← hsum_α]
    simp only [T₀, T₁, T₂, T₃, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [f, g, zero_mul, add_zero, one_mul]
    ring
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  have h02 : (0 : ZMod p) ≠ 2 := by
    simpa using zmod_natCast_ne p 0 2 (by omega) (by omega) (by decide)
  have h03 : (0 : ZMod p) ≠ 3 := by
    simpa using zmod_natCast_ne p 0 3 (by omega) (by omega) (by decide)
  have h12 : (1 : ZMod p) ≠ 2 := by
    simpa using zmod_natCast_ne p 1 2 (by omega) (by omega) (by decide)
  have h13 : (1 : ZMod p) ≠ 3 := by
    simpa using zmod_natCast_ne p 1 3 (by omega) (by omega) (by decide)
  have h23 : (2 : ZMod p) ≠ 3 := by
    simpa using zmod_natCast_ne p 2 3 (by omega) (by omega) (by decide)
  set U : ℝ :=
    ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
      f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
      f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃)
  have hT0 : T₀ ^ 8 ≤ (p : ℝ) ^ 12 * U :=
    h2 p 1 2 3 0 h12 h13 h01.symm h23 h02.symm h03.symm g g g f hg_bdd hg_bdd hg_bdd
  have hT1 : T₁ ^ 8 ≤ (p : ℝ) ^ 12 * U :=
    h2 p 0 2 3 1 h02 h03 h01 h23 h12.symm h13.symm (fun _ => α) g g f hα_bdd hg_bdd hg_bdd
  have hT2 : T₂ ^ 8 ≤ (p : ℝ) ^ 12 * U :=
    h2 p 0 1 3 2 h01 h03 h02 h13 h12 h23.symm (fun _ => α) (fun _ => α) g f hα_bdd hα_bdd hg_bdd
  have hT3 : T₃ ^ 8 ≤ (p : ℝ) ^ 12 * U :=
    h2 p 0 1 2 3 h01 h02 h03 h12 h13 h23 (fun _ => α) (fun _ => α) (fun _ => α) f
      hα_bdd hα_bdd hα_bdd
  have hsum8 : ((p : ℝ) ^ 2 * α ^ 4 - (p : ℝ) * α) ^ 8 ≤ 4 ^ 8 * ((p : ℝ) ^ 12 * U) := by
    have hneg : ((p : ℝ) ^ 2 * α ^ 4 - (p : ℝ) * α) ^ 8 = (T₀ + T₁ + T₂ + T₃) ^ 8 := by
      rw [← htele]; ring
    rw [hneg]
    exact pow_eight_add_four_le hT0 hT1 hT2 hT3
  have hhalf : (p : ℝ) ^ 2 * α ^ 4 / 2 ≤ (p : ℝ) ^ 2 * α ^ 4 - (p : ℝ) * α := by
    have hpa : 0 ≤ (p : ℝ) * α / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hα2 hpa
    have hlhs : 2 * ((p : ℝ) * α / 2) = (p : ℝ) * α := by ring
    have hrhs : (p : ℝ) * α ^ 3 * ((p : ℝ) * α / 2) = (p : ℝ) ^ 2 * α ^ 4 / 2 := by ring
    linarith
  have hlow : ((p : ℝ) ^ 2 * α ^ 4 / 2) ^ 8 ≤ 4 ^ 8 * ((p : ℝ) ^ 12 * U) :=
    (pow_le_pow_left₀ (by positivity) hhalf 8).trans hsum8
  have hfac :
      ((p : ℝ) ^ 2 * α ^ 4 / 2) ^ 8 =
        (4 ^ 8 * (p : ℝ) ^ 12) * ((p : ℝ) ^ 4 * (α ^ 4 / 8) ^ 8) := by ring
  have hfacR : 4 ^ 8 * ((p : ℝ) ^ 12 * U) = (4 ^ 8 * (p : ℝ) ^ 12) * U := by ring
  rw [hfac, hfacR] at hlow
  exact le_of_mul_le_mul_left hlow (by positivity)

lemma log_rpow_dom (A c : ℝ) (hA : 1 < A) (hc : 0 < c) :
    ∃ U₀ : ℝ, ∀ u : ℝ, U₀ ≤ u → (3 * c / 2) * (Real.log u) ^ A + Real.log 128 ≤ u := by
  have hA0 : 0 < A := by linarith
  have h2A : 0 < 2 * A := by linarith
  set δ : ℝ := 1 / (2 * A) with hδ_def
  have hδ : 0 < δ := by positivity
  set K : ℝ := (3 * c / 2) * (2 * A) ^ A with hK_def
  have hK : 0 < K := by positivity
  set M : ℝ := K + 129 with hM_def
  have hM1 : 1 ≤ M := by linarith
  refine ⟨M ^ 2, fun u hu => ?_⟩
  have hu1 : 1 ≤ u := le_trans (by nlinarith) hu
  have hu0 : 0 < u := by linarith
  set s : ℝ := u ^ (1 / 2 : ℝ) with hs_def
  have hs0 : 0 ≤ s := Real.rpow_nonneg hu0.le _
  have hss : s * s = u := by
    rw [hs_def, ← Real.rpow_add hu0]
    norm_num
  have hMs : M ≤ s := by nlinarith
  have hs1 : 1 ≤ s := le_trans hM1 hMs
  have hlogu_nonneg : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hlogu_le : Real.log u ≤ (2 * A) * u ^ δ := by
    have h1 : Real.log (u ^ δ) ≤ u ^ δ - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu0 δ)
    rw [Real.log_rpow hu0 δ] at h1
    have h2 : δ * Real.log u ≤ u ^ δ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 h2A.le
    have h4 : (2 * A) * (δ * Real.log u) = Real.log u := by
      rw [hδ_def]; field_simp
    linarith
  have hpow : (Real.log u) ^ A ≤ (2 * A) ^ A * s := by
    calc (Real.log u) ^ A
        ≤ ((2 * A) * u ^ δ) ^ A := Real.rpow_le_rpow hlogu_nonneg hlogu_le hA0.le
      _ = (2 * A) ^ A * (u ^ δ) ^ A := Real.mul_rpow h2A.le (Real.rpow_nonneg hu0.le δ)
      _ = (2 * A) ^ A * u ^ (δ * A) := by rw [← Real.rpow_mul hu0.le]
      _ = (2 * A) ^ A * s := by
            have hδA : δ * A = 1 / 2 := by rw [hδ_def]; field_simp
            rw [hδA, hs_def]
  have hlog128 : Real.log 128 ≤ 128 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 128)
    linarith
  have hterm : (3 * c / 2) * (Real.log u) ^ A ≤ K * s := by
    have := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 3 * c / 2 by positivity)
    rw [hK_def]
    linarith
  have h128s : 128 ≤ 128 * s := by nlinarith
  have hKMs : (K + 128) * s ≤ M * s := by
    rw [hM_def]; nlinarith
  have hMss : M * s ≤ s * s := by nlinarith
  linarith

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1.H1 := by
  intro h1 h2
  obtain ⟨A, c, hA, hc, hP⟩ := h1
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp hP
  obtain ⟨U₀, hU₀⟩ := log_rpow_dom A c hA hc
  refine ⟨A, c / 2, hA, by positivity, ?_⟩
  have hlogN : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogN :
      Filter.Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hlogN
  filter_upwards [Filter.eventually_ge_atTop (max P₀ 3),
    hlogN.eventually_ge_atTop (max 1 U₀),
    hloglogN.eventually_ge_atTop (max 1 (2 * Real.log 4 / c))] with N hN hlog hll
  have hNP₀ : P₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlog_ge1 : 1 ≤ Real.log (N : ℝ) := le_trans (le_max_left _ _) hlog
  have hlog_geU : U₀ ≤ Real.log (N : ℝ) := le_trans (le_max_right _ _) hlog
  have hll_ge1 : 1 ≤ Real.log (Real.log (N : ℝ)) := le_trans (le_max_left _ _) hll
  have hll_ge4 : 2 * Real.log 4 / c ≤ Real.log (Real.log (N : ℝ)) :=
    le_trans (le_max_right _ _) hll
  by_contra hlt
  push Not at hlt
  obtain ⟨p, hp_prime, h2Np, hp4N⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp4 : 4 < p := by omega
  have hpP₀ : P₀ ≤ p := by omega
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp_le4N : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast (by omega : p ≤ 4 * N)
  have hN_lt_p : (N : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : N < p)
  obtain ⟨S₀, hS₀_sub, hS₀_free, hS₀_card⟩ := exists_extremal_4ap_free N
  let S : Finset (ZMod p) := S₀.image (Nat.cast : ℕ → ZMod p)
  obtain ⟨hScard_eq, hSno4⟩ := embed_4ap_free h2Np hS₀_sub hS₀_free
  have hScard : (N : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) < (S.card : ℝ) := by
    have : (S.card : ℝ) = (Erdos142.r 4 N : ℝ) := by exact_mod_cast (hScard_eq.trans hS₀_card)
    rw [this]
    exact hlt
  have hll_le : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (p : ℝ)) := by
    have hlog_pos : 0 < Real.log (N : ℝ) := by linarith
    have hlog_le : Real.log (N : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log hN_pos hN_lt_p.le
    exact Real.log_le_log hlog_pos hlog_le
  have hllA_le : Real.log (Real.log (N : ℝ)) ^ A ≤ Real.log (Real.log (p : ℝ)) ^ A :=
    Real.rpow_le_rpow (by linarith) hll_le (by linarith)
  have hdens_p : (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) < (S.card : ℝ) := by
    have h4_le_exp :
        (4 : ℝ) ≤ Real.exp ((c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
      have hpow_ge : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (N : ℝ)) ^ A := by
        have := Real.rpow_le_rpow_of_exponent_le hll_ge1 hA.le
        rwa [Real.rpow_one] at this
      have hlog4 : Real.log 4 ≤ (c / 2) * Real.log (Real.log (N : ℝ)) ^ A := by
        have hmul := mul_le_mul_of_nonneg_left (hll_ge4.trans hpow_ge) (show (0 : ℝ) ≤ c / 2 by positivity)
        have hsimp : (c / 2) * (2 * Real.log 4 / c) = Real.log 4 := by field_simp
        linarith
      calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp ((c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := Real.exp_le_exp.mpr hlog4
    have hexp_mono :
        Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) ≤
          Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h4exp :
        4 * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) ≤
          Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
      have hmul := mul_le_mul_of_nonneg_right h4_le_exp
        (Real.exp_pos (-c * Real.log (Real.log (N : ℝ)) ^ A)).le
      rw [← Real.exp_add] at hmul
      have hadd :
          (c / 2) * Real.log (Real.log (N : ℝ)) ^ A +
            -c * Real.log (Real.log (N : ℝ)) ^ A =
          -(c / 2) * Real.log (Real.log (N : ℝ)) ^ A := by ring
      rwa [hadd] at hmul
    calc (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A)
        ≤ (4 * (N : ℝ)) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) :=
          mul_le_mul hp_le4N hexp_mono (Real.exp_pos _).le (by positivity)
      _ = (N : ℝ) * (4 * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A)) := by ring
      _ ≤ (N : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) :=
          mul_le_mul_of_nonneg_left h4exp hN_pos.le
      _ < (S.card : ℝ) := hScard
  have hα2 : 2 ≤ (p : ℝ) * ((S.card : ℝ) / (p : ℝ)) ^ 3 := by
    set E : ℝ := Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) with hE_def
    have hE_pos : 0 < E := Real.exp_pos _
    have hα_gt : (1 / 4 : ℝ) * E < (S.card : ℝ) / (p : ℝ) := by
      rw [lt_div_iff₀ hp_pos]
      have hmul : (1 / 4 : ℝ) * E * (p : ℝ) ≤ (1 / 4 : ℝ) * E * (4 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hp_le4N (by positivity)
      have heq : (1 / 4 : ℝ) * E * (4 * (N : ℝ)) = (N : ℝ) * E := by ring
      linarith
    have hE3 : E ^ 3 = Real.exp (-(3 * c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
      rw [hE_def, pow_succ, pow_succ, pow_one, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    have hα3 : (1 / 64 : ℝ) * E ^ 3 ≤ ((S.card : ℝ) / (p : ℝ)) ^ 3 := by
      have hpow := pow_le_pow_left₀ (by positivity) hα_gt.le 3
      have hlhs : ((1 / 4 : ℝ) * E) ^ 3 = (1 / 64 : ℝ) * E ^ 3 := by ring
      linarith
    have h128 : 128 ≤ (N : ℝ) * E ^ 3 := by
      have hdom := hU₀ (Real.log (N : ℝ)) hlog_geU
      have hexp := Real.exp_le_exp.mpr hdom
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 128), Real.exp_log hN_pos] at hexp
      have hmul := mul_le_mul_of_nonneg_right hexp
        (Real.exp_pos (-(3 * c / 2) * Real.log (Real.log (N : ℝ)) ^ A)).le
      have hcancel :
          Real.exp ((3 * c / 2) * Real.log (Real.log (N : ℝ)) ^ A) * 128 *
            Real.exp (-(3 * c / 2) * Real.log (Real.log (N : ℝ)) ^ A) = 128 := by
        rw [mul_comm _ (128 : ℝ), mul_assoc, ← Real.exp_add]
        simp
      rw [hcancel, ← hE3] at hmul
      exact hmul
    calc (2 : ℝ) = (1 / 64 : ℝ) * 128 := by norm_num
      _ ≤ (1 / 64 : ℝ) * ((N : ℝ) * E ^ 3) := by linarith
      _ = (N : ℝ) * ((1 / 64 : ℝ) * E ^ 3) := by ring
      _ ≤ (p : ℝ) * ((S.card : ℝ) / (p : ℝ)) ^ 3 :=
          mul_le_mul hN_lt_p.le hα3 (by positivity) hp_pos.le
  have hU3 := gowers_u3_lower_bound h2 hp4 S hSno4 hα2
  exact hSno4 (hP₀ p hpP₀ S hdens_p hU3)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1
