import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R2 of step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1
-- Credit: @Goidelg

/-!
# Derivative-spectrum Fourier reduction for the k = 4 super-polylogarithmic bound

We reduce the k = 4 super-polylogarithmic bound
(`∃ A c, 1 < A ∧ 0 < c ∧ ∀ᶠ N, r 4 N ≤ N * exp (-c * (log log N)^A)`)
beyond the Gowers U^3 generalized von Neumann stage: inside this reduction we
prove from scratch
1. the Bertrand prime cyclic embedding (`2N < p ≤ 4N`) with no-wrap 4-AP lifting,
2. the Gowers U^3 generalized von Neumann inequality on `ZMod p`, and
3. the 4-AP telescoping lower bound on the U^3 cube sum of `1_S - α`.

This isolates two clean, independent remaining hypotheses:
- `H1`: Derivative-spectrum Fourier extraction on `ZMod p` (controlling the U^3
  cube sum by the dominant Fourier frequency `ξ h` of each multiplicative
  derivative `x ↦ f x * f (x + h)`).
- `H2`: Super-polylogarithmic 4-AP existence in `ZMod p` from large
  derivative-spectrum Fourier correlation.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2

open Finset BigOperators Filter Real Erdos142

/-- Derivative-spectrum Fourier extraction on `ZMod p`: for any 1-bounded real function `f`,
the Gowers `U^3` cube sum is bounded by `p` times the sum over shifts `h` of the squared
dominant Fourier coefficient of the multiplicative derivative `x ↦ f x * f (x + h)`. -/
def H1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : ZMod p → ℝ), (∀ x, |f x| ≤ 1) →
    ∃ ξ : ZMod p → ZMod p,
      ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
        f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃) ≤
      (p : ℝ) * ∑ h : ZMod p,
        ‖∑ x : ZMod p, ((f x * f (x + h) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (((x * ξ h).val : ℕ) : ℂ) / (p : ℂ))‖ ^ 2

/-- Super-polylogarithmic 4-AP existence from large derivative-spectrum Fourier correlation
on `ZMod p`. -/
def H2 : Prop :=
  ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ p : ℕ in Filter.atTop, ∀ [Fact p.Prime],
    ∀ S : Finset (ZMod p),
      let α : ℝ := (S.card : ℝ) / (p : ℝ)
      let f : ZMod p → ℝ := fun x => (if x ∈ S then (1 : ℝ) else 0) - α
      (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) < (S.card : ℝ) →
      (∃ ξ : ZMod p → ZMod p,
        (p : ℝ) ^ 3 * (α ^ 4 / 8) ^ 8 ≤
          ∑ h : ZMod p,
            ‖∑ x : ZMod p, ((f x * f (x + h) : ℝ) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * (((x * ξ h).val : ℕ) : ℂ) / (p : ℂ))‖ ^ 2) →
      ∃ x d : ZMod p, d ≠ 0 ∧ x ∈ S ∧ x + d ∈ S ∧ x + 2 * d ∈ S ∧ x + 3 * d ∈ S

lemma exists_extremal_ap_free (k N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧ S.card = r k N := by
  let E : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hne : E.Nonempty := by
    refine ⟨0, ∅, Finset.empty_subset _, ?_, rfl⟩
    intro t ht htap
    have hte : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    subst hte
    obtain ⟨_, _, hcard, _⟩ := htap
    simp at hcard
    rw [← hcard]
    exact bot_le
  have hbdd : BddAbove E := by
    refine ⟨N, ?_⟩
    rintro m ⟨S, hS, -, rfl⟩
    simpa using Finset.card_le_card hS
  have hmem : sSup E ∈ E := Nat.sSup_mem hne hbdd
  rcases hmem with ⟨S, hS, hfree, hcard⟩
  exact ⟨S, hS, hfree, hcard⟩

lemma lift_midpoint {p N a b c : ℕ} (hp : 2 * N < p)
    (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N)
    (h : (a : ZMod p) + (c : ZMod p) = (b : ZMod p) + (b : ZMod p)) : a + c = b + b := by
  have h' : ((a + c : ℕ) : ZMod p) = ((b + b : ℕ) : ZMod p) := by
    simpa only [Nat.cast_add] using h
  have hm := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h'
  rwa [Nat.mod_eq_of_lt (show a + c < p by omega),
    Nat.mod_eq_of_lt (show b + b < p by omega)] at hm

lemma no_wrap_four_ap {p N : ℕ} [NeZero p] (hp : 2 * N < p)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N) (hfree : (S : Set ℕ).IsAPOfLengthFree 4) :
    ∀ x d : ZMod p, d ≠ 0 →
      ¬ (x ∈ S.image (fun n : ℕ => (n : ZMod p)) ∧
         x + d ∈ S.image (fun n : ℕ => (n : ZMod p)) ∧
         x + 2 * d ∈ S.image (fun n : ℕ => (n : ZMod p)) ∧
         x + 3 * d ∈ S.image (fun n : ℕ => (n : ZMod p))) := by
  intro x d hd ⟨h0, h1, h2, h3⟩
  rcases Finset.mem_image.mp h0 with ⟨a, haS, haEq⟩
  rcases Finset.mem_image.mp h1 with ⟨b, hbS, hbEq⟩
  rcases Finset.mem_image.mp h2 with ⟨c, hcS, hcEq⟩
  rcases Finset.mem_image.mp h3 with ⟨e, heS, heEq⟩
  have haN : a ≤ N := (Finset.mem_Icc.mp (hS haS)).2
  have hbN : b ≤ N := (Finset.mem_Icc.mp (hS hbS)).2
  have hcN : c ≤ N := (Finset.mem_Icc.mp (hS hcS)).2
  have heN : e ≤ N := (Finset.mem_Icc.mp (hS heS)).2
  have hm1 : a + c = b + b := by
    apply lift_midpoint hp haN hbN hcN
    rw [haEq, hbEq, hcEq]
    ring
  have hm2 : b + e = c + c := by
    apply lift_midpoint hp hbN hcN heN
    rw [hbEq, hcEq, heEq]
    ring
  have hab : a ≠ b := by
    intro heq
    rw [heq] at haEq
    have : x = x + d := haEq.symm.trans hbEq
    exact hd (by linear_combination -this)
  have hnat_ap : ∃ u s : ℕ, 0 < s ∧ u ∈ S ∧ u + s ∈ S ∧ u + 2 * s ∈ S ∧ u + 3 * s ∈ S := by
    by_cases hlt : a < b
    · refine ⟨a, b - a, by omega, haS, ?_, ?_, ?_⟩
      · rwa [show a + (b - a) = b by omega]
      · rwa [show a + 2 * (b - a) = c by omega]
      · rwa [show a + 3 * (b - a) = e by omega]
    · refine ⟨e, a - b, by omega, heS, ?_, ?_, ?_⟩
      · rwa [show e + (a - b) = c by omega]
      · rwa [show e + 2 * (a - b) = b by omega]
      · rwa [show e + 3 * (a - b) = a by omega]
  obtain ⟨u, s, hs, hu0, hu1, hu2, hu3⟩ := hnat_ap
  let T : Finset ℕ := (Finset.range 4).image (fun i => u + i * s)
  have hTsub : (T : Set ℕ) ⊆ (S : Set ℕ) := by
    intro y hy
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hy) with ⟨i, hi, rfl⟩
    have hi4 : i < 4 := Finset.mem_range.mp hi
    interval_cases i
    · simpa using hu0
    · simpa using hu1
    · simpa using hu2
    · simpa using hu3
  have hinj : Function.Injective (fun i : ℕ => u + i * s) := fun i j hij =>
    Nat.eq_of_mul_eq_mul_right hs (Nat.add_left_cancel hij)
  have hTcard : ENat.card (T : Set ℕ) = 4 := by
    rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _ hinj, Finset.card_range]
    rfl
  have hTeq : (T : Set ℕ) = {u + n • s | (n : ℕ) (_ : n < (4 : ℕ∞))} := by
    ext y
    simp only [T, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
      Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, by exact_mod_cast hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, by exact_mod_cast hi, rfl⟩
  have h4le1 : (4 : ℕ∞) ≤ 1 := hfree (T : Set ℕ) hTsub ⟨u, s, hTcard, hTeq⟩
  exact absurd h4le1 (by decide)

lemma cs_bounded {ι : Type} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, |a i| ≤ 1) :
    (∑ i : ι, a i * b i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (b i) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) a b
  have ha2 : ∑ i : ι, (a i) ^ 2 ≤ (Fintype.card ι : ℝ) := by
    calc
      ∑ i : ι, (a i) ^ 2 ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h1 : |a i| ^ 2 ≤ 1 ^ 2 := sq_le_sq' (by linarith [abs_nonneg (a i), ha i]) (ha i)
        simpa [sq_abs] using h1
      _ = (Fintype.card ι : ℝ) := by simp
  have hb2 : 0 ≤ ∑ i : ι, (b i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact le_trans hcs (mul_le_mul_of_nonneg_right ha2 hb2)

lemma gowers_u3_von_neumann
    (p : ℕ) [Fact p.Prime]
    (c₀ c₁ c₂ c₃ : ZMod p)
    (h03 : c₀ ≠ c₃) (h13 : c₁ ≠ c₃) (h23 : c₂ ≠ c₃)
    (f₀ f₁ f₂ f₃ : ZMod p → ℝ)
    (hf₀ : ∀ x, |f₀ x| ≤ 1) (hf₁ : ∀ x, |f₁ x| ≤ 1) (hf₂ : ∀ x, |f₂ x| ≤ 1) :
    (∑ x : ZMod p, ∑ d : ZMod p,
      f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)) ^ 8 ≤
    (p : ℝ) ^ 12 * ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
      f₃ x * f₃ (x + h₁) * f₃ (x + h₂) * f₃ (x + h₁ + h₂) *
      f₃ (x + h₃) * f₃ (x + h₁ + h₃) * f₃ (x + h₂ + h₃) * f₃ (x + h₁ + h₂ + h₃) := by
  have hp_card : (Fintype.card (ZMod p) : ℝ) = (p : ℝ) := by simp [ZMod.card]
  set a₁ : ZMod p := c₁ - c₀
  set a₂ : ZMod p := c₂ - c₀
  set a₃ : ZMod p := c₃ - c₀
  set b₂ : ZMod p := c₂ - c₁
  set b₃ : ZMod p := c₃ - c₁
  set r : ZMod p := c₃ - c₂
  have ha₃_ne : a₃ ≠ 0 := sub_ne_zero.mpr h03.symm
  have hb₃_ne : b₃ ≠ 0 := sub_ne_zero.mpr h13.symm
  have hr_ne : r ≠ 0 := sub_ne_zero.mpr h23.symm
  set S : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
      f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)
  have hS0 : S = ∑ u : ZMod p, f₀ u *
      (∑ d : ZMod p, f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d)) := by
    dsimp only [S]
    rw [Finset.sum_comm]
    have hshift : ∀ d : ZMod p,
        ∑ x : ZMod p, f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d) =
        ∑ u : ZMod p, f₀ u * (f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d)) := by
      intro d
      refine Fintype.sum_equiv (Equiv.addRight (c₀ * d)) _ _ (fun x => ?_)
      change f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d) =
        f₀ (x + c₀ * d) * (f₁ (x + c₀ * d + a₁ * d) * f₂ (x + c₀ * d + a₂ * d) * f₃ (x + c₀ * d + a₃ * d))
      have h1 : x + c₁ * d = x + c₀ * d + a₁ * d := by dsimp only [a₁]; ring
      have h2 : x + c₂ * d = x + c₀ * d + a₂ * d := by dsimp only [a₂]; ring
      have h3 : x + c₃ * d = x + c₀ * d + a₃ * d := by dsimp only [a₃]; ring
      rw [h1, h2, h3]
      ring
    simp_rw [hshift]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  let g₁ : ZMod p → ZMod p → ℝ := fun k₁ y => f₁ y * f₁ (y + a₁ * k₁)
  let g₂ : ZMod p → ZMod p → ℝ := fun k₁ y => f₂ y * f₂ (y + a₂ * k₁)
  let g₃ : ZMod p → ZMod p → ℝ := fun k₁ y => f₃ y * f₃ (y + a₃ * k₁)
  have hg₁_bd : ∀ k₁ y, |g₁ k₁ y| ≤ 1 := fun k₁ y => by
    dsimp only [g₁]; rw [abs_mul]
    nlinarith [hf₁ y, hf₁ (y + a₁ * k₁), abs_nonneg (f₁ y), abs_nonneg (f₁ (y + a₁ * k₁))]
  have hg₂_bd : ∀ k₁ y, |g₂ k₁ y| ≤ 1 := fun k₁ y => by
    dsimp only [g₂]; rw [abs_mul]
    nlinarith [hf₂ y, hf₂ (y + a₂ * k₁), abs_nonneg (f₂ y), abs_nonneg (f₂ (y + a₂ * k₁))]
  set T₁ : ℝ := ∑ k₁ : ZMod p, ∑ v : ZMod p,
      g₁ k₁ v * (∑ d : ZMod p, g₂ k₁ (v + b₂ * d) * g₃ k₁ (v + b₃ * d))
  have hstep1 : S ^ 2 ≤ (p : ℝ) * T₁ := by
    have hcs := cs_bounded f₀
      (fun u => ∑ d : ZMod p, f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d)) hf₀
    rw [← hS0, hp_card] at hcs
    have hT1_eq : ∑ u : ZMod p,
        (∑ d : ZMod p, f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d)) ^ 2 = T₁ := by
      have hexp : ∀ u : ZMod p,
          (∑ d : ZMod p, f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d)) ^ 2 =
          ∑ k₁ : ZMod p, ∑ d : ZMod p,
            g₁ k₁ (u + a₁ * d) * g₂ k₁ (u + a₂ * d) * g₃ k₁ (u + a₃ * d) := by
        intro u
        rw [sq, Finset.sum_mul_sum]
        have hre : ∀ d : ZMod p,
            ∑ d' : ZMod p,
              (f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d)) *
              (f₁ (u + a₁ * d') * f₂ (u + a₂ * d') * f₃ (u + a₃ * d')) =
            ∑ k₁ : ZMod p, g₁ k₁ (u + a₁ * d) * g₂ k₁ (u + a₂ * d) * g₃ k₁ (u + a₃ * d) := by
          intro d
          refine Fintype.sum_equiv (Equiv.subRight d) _ _ (fun d' => ?_)
          change (f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d)) *
              (f₁ (u + a₁ * d') * f₂ (u + a₂ * d') * f₃ (u + a₃ * d')) =
            g₁ (d' - d) (u + a₁ * d) * g₂ (d' - d) (u + a₂ * d) * g₃ (d' - d) (u + a₃ * d)
          dsimp only [g₁, g₂, g₃]
          have e1 : u + a₁ * d + a₁ * (d' - d) = u + a₁ * d' := by ring
          have e2 : u + a₂ * d + a₂ * (d' - d) = u + a₂ * d' := by ring
          have e3 : u + a₃ * d + a₃ * (d' - d) = u + a₃ * d' := by ring
          rw [e1, e2, e3]; ring
        simp_rw [hre]
        rw [Finset.sum_comm]
      simp_rw [hexp]
      rw [Finset.sum_comm]
      dsimp only [T₁]
      apply Finset.sum_congr rfl
      intro k₁ _
      rw [Finset.sum_comm]
      have hsh : ∀ d : ZMod p,
          ∑ u : ZMod p, g₁ k₁ (u + a₁ * d) * g₂ k₁ (u + a₂ * d) * g₃ k₁ (u + a₃ * d) =
          ∑ v : ZMod p, g₁ k₁ v * (g₂ k₁ (v + b₂ * d) * g₃ k₁ (v + b₃ * d)) := by
        intro d
        refine Fintype.sum_equiv (Equiv.addRight (a₁ * d)) _ _ (fun u => ?_)
        change g₁ k₁ (u + a₁ * d) * g₂ k₁ (u + a₂ * d) * g₃ k₁ (u + a₃ * d) =
          g₁ k₁ (u + a₁ * d) * (g₂ k₁ (u + a₁ * d + b₂ * d) * g₃ k₁ (u + a₁ * d + b₃ * d))
        have e2 : u + a₂ * d = u + a₁ * d + b₂ * d := by dsimp only [a₁, a₂, b₂]; ring
        have e3 : u + a₃ * d = u + a₁ * d + b₃ * d := by dsimp only [a₁, a₃, b₃]; ring
        rw [e2, e3]; ring
      simp_rw [hsh]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    rw [hT1_eq] at hcs
    exact hcs
  let H₂ : ZMod p → ZMod p → ZMod p → ℝ := fun k₁ k₂ y => g₂ k₁ y * g₂ k₁ (y + b₂ * k₂)
  let H₃ : ZMod p → ZMod p → ZMod p → ℝ := fun k₁ k₂ y => g₃ k₁ y * g₃ k₁ (y + b₃ * k₂)
  have hH₂_bd : ∀ k₁ k₂ y, |H₂ k₁ k₂ y| ≤ 1 := fun k₁ k₂ y => by
    dsimp only [H₂]; rw [abs_mul]
    nlinarith [hg₂_bd k₁ y, hg₂_bd k₁ (y + b₂ * k₂), abs_nonneg (g₂ k₁ y), abs_nonneg (g₂ k₁ (y + b₂ * k₂))]
  set T₂ : ℝ := ∑ k₁ : ZMod p, ∑ k₂ : ZMod p, ∑ w : ZMod p,
      H₂ k₁ k₂ w * (∑ d : ZMod p, H₃ k₁ k₂ (w + r * d))
  have hstep2 : T₁ ^ 2 ≤ (p : ℝ) ^ 2 * T₂ := by
    have hcs := cs_bounded (ι := ZMod p × ZMod p)
      (fun kv => g₁ kv.1 kv.2)
      (fun kv => ∑ d : ZMod p, g₂ kv.1 (kv.2 + b₂ * d) * g₃ kv.1 (kv.2 + b₃ * d))
      (fun kv => hg₁_bd kv.1 kv.2)
    have hT1_pair : ∑ kv : ZMod p × ZMod p,
        g₁ kv.1 kv.2 * (∑ d : ZMod p, g₂ kv.1 (kv.2 + b₂ * d) * g₃ kv.1 (kv.2 + b₃ * d)) = T₁ := by
      rw [Fintype.sum_prod_type]
    have hcard2 : (Fintype.card (ZMod p × ZMod p) : ℝ) = (p : ℝ) ^ 2 := by
      simp [ZMod.card, sq]
    rw [hT1_pair, hcard2, Fintype.sum_prod_type] at hcs
    have hT2_eq : ∑ k₁ : ZMod p, ∑ v : ZMod p,
        (∑ d : ZMod p, g₂ k₁ (v + b₂ * d) * g₃ k₁ (v + b₃ * d)) ^ 2 = T₂ := by
      dsimp only [T₂]
      apply Finset.sum_congr rfl
      intro k₁ _
      have hexp : ∀ v : ZMod p,
          (∑ d : ZMod p, g₂ k₁ (v + b₂ * d) * g₃ k₁ (v + b₃ * d)) ^ 2 =
          ∑ k₂ : ZMod p, ∑ d : ZMod p, H₂ k₁ k₂ (v + b₂ * d) * H₃ k₁ k₂ (v + b₃ * d) := by
        intro v
        rw [sq, Finset.sum_mul_sum]
        have hre : ∀ d : ZMod p,
            ∑ d' : ZMod p,
              (g₂ k₁ (v + b₂ * d) * g₃ k₁ (v + b₃ * d)) *
              (g₂ k₁ (v + b₂ * d') * g₃ k₁ (v + b₃ * d')) =
            ∑ k₂ : ZMod p, H₂ k₁ k₂ (v + b₂ * d) * H₃ k₁ k₂ (v + b₃ * d) := by
          intro d
          refine Fintype.sum_equiv (Equiv.subRight d) _ _ (fun d' => ?_)
          change (g₂ k₁ (v + b₂ * d) * g₃ k₁ (v + b₃ * d)) *
              (g₂ k₁ (v + b₂ * d') * g₃ k₁ (v + b₃ * d')) =
            H₂ k₁ (d' - d) (v + b₂ * d) * H₃ k₁ (d' - d) (v + b₃ * d)
          dsimp only [H₂, H₃]
          have e2 : v + b₂ * d + b₂ * (d' - d) = v + b₂ * d' := by ring
          have e3 : v + b₃ * d + b₃ * (d' - d) = v + b₃ * d' := by ring
          rw [e2, e3]; ring
        simp_rw [hre]
        rw [Finset.sum_comm]
      simp_rw [hexp]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k₂ _
      rw [Finset.sum_comm]
      have hsh : ∀ d : ZMod p,
          ∑ v : ZMod p, H₂ k₁ k₂ (v + b₂ * d) * H₃ k₁ k₂ (v + b₃ * d) =
          ∑ w : ZMod p, H₂ k₁ k₂ w * H₃ k₁ k₂ (w + r * d) := by
        intro d
        refine Fintype.sum_equiv (Equiv.addRight (b₂ * d)) _ _ (fun v => ?_)
        change H₂ k₁ k₂ (v + b₂ * d) * H₃ k₁ k₂ (v + b₃ * d) =
          H₂ k₁ k₂ (v + b₂ * d) * H₃ k₁ k₂ (v + b₂ * d + r * d)
        have e3 : v + b₃ * d = v + b₂ * d + r * d := by dsimp only [b₂, b₃, r]; ring
        rw [e3]
      simp_rw [hsh]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    rw [hT2_eq] at hcs
    exact hcs
  set Cube : ℝ := ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
      f₃ x * f₃ (x + h₁) * f₃ (x + h₂) * f₃ (x + h₁ + h₂) *
      f₃ (x + h₃) * f₃ (x + h₁ + h₃) * f₃ (x + h₂ + h₃) * f₃ (x + h₁ + h₂ + h₃)
  have hstep3 : T₂ ^ 2 ≤ (p : ℝ) ^ 4 * Cube := by
    have hcs := cs_bounded (ι := ZMod p × ZMod p × ZMod p)
      (fun t => H₂ t.1 t.2.1 t.2.2)
      (fun t => ∑ d : ZMod p, H₃ t.1 t.2.1 (t.2.2 + r * d))
      (fun t => hH₂_bd t.1 t.2.1 t.2.2)
    have hT2_trip : ∑ t : ZMod p × ZMod p × ZMod p,
        H₂ t.1 t.2.1 t.2.2 * (∑ d : ZMod p, H₃ t.1 t.2.1 (t.2.2 + r * d)) = T₂ := by
      simp only [Fintype.sum_prod_type]
      rfl
    have hcard3 : (Fintype.card (ZMod p × ZMod p × ZMod p) : ℝ) = (p : ℝ) ^ 3 := by
      simp [ZMod.card]
      ring
    rw [hT2_trip, hcard3] at hcs
    have hcube_eq : ∑ t : ZMod p × ZMod p × ZMod p,
        (∑ d : ZMod p, H₃ t.1 t.2.1 (t.2.2 + r * d)) ^ 2 = (p : ℝ) * Cube := by
      simp only [Fintype.sum_prod_type]
      have hinner : ∀ k₁ k₂ : ZMod p,
          ∑ w : ZMod p, (∑ d : ZMod p, H₃ k₁ k₂ (w + r * d)) ^ 2 =
          (p : ℝ) * ∑ k₃ : ZMod p, ∑ x : ZMod p, H₃ k₁ k₂ x * H₃ k₁ k₂ (x + r * k₃) := by
        intro k₁ k₂
        have hexp : ∀ w : ZMod p,
            (∑ d : ZMod p, H₃ k₁ k₂ (w + r * d)) ^ 2 =
            ∑ d : ZMod p, ∑ k₃ : ZMod p, H₃ k₁ k₂ (w + r * d) * H₃ k₁ k₂ (w + r * d + r * k₃) := by
          intro w
          rw [sq, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          refine Fintype.sum_equiv (Equiv.subRight d) _ _ (fun d' => ?_)
          change H₃ k₁ k₂ (w + r * d) * H₃ k₁ k₂ (w + r * d') =
            H₃ k₁ k₂ (w + r * d) * H₃ k₁ k₂ (w + r * d + r * (d' - d))
          have e : w + r * d + r * (d' - d) = w + r * d' := by ring
          rw [e]
        simp_rw [hexp]
        rw [Finset.sum_comm]
        have hconst : ∀ d : ZMod p,
            ∑ w : ZMod p, ∑ k₃ : ZMod p, H₃ k₁ k₂ (w + r * d) * H₃ k₁ k₂ (w + r * d + r * k₃) =
            ∑ k₃ : ZMod p, ∑ x : ZMod p, H₃ k₁ k₂ x * H₃ k₁ k₂ (x + r * k₃) := by
          intro d
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k₃ _
          exact Fintype.sum_equiv (Equiv.addRight (r * d)) _ _ (fun _ => rfl)
        simp_rw [hconst]
        simp [ZMod.card]
      simp_rw [hinner, ← Finset.mul_sum]
      congr 1
      let e₁ := Equiv.mulLeft₀ a₃ ha₃_ne
      let e₂ := Equiv.mulLeft₀ b₃ hb₃_ne
      let e₃ := Equiv.mulLeft₀ r hr_ne
      have hre1 : ∑ k₁ : ZMod p, ∑ k₂ : ZMod p, ∑ k₃ : ZMod p, ∑ x : ZMod p,
            H₃ k₁ k₂ x * H₃ k₁ k₂ (x + r * k₃) =
          ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ x : ZMod p,
            f₃ x * f₃ (x + h₁) * f₃ (x + h₂) * f₃ (x + h₁ + h₂) *
            f₃ (x + h₃) * f₃ (x + h₁ + h₃) * f₃ (x + h₂ + h₃) * f₃ (x + h₁ + h₂ + h₃) := by
        refine Fintype.sum_equiv e₁ _ _ (fun k₁ => ?_)
        refine Fintype.sum_equiv e₂ _ _ (fun k₂ => ?_)
        refine Fintype.sum_equiv e₃ _ _ (fun k₃ => ?_)
        apply Finset.sum_congr rfl
        intro x _
        simp only [e₁, e₂, e₃, Equiv.mulLeft₀_apply, H₃, g₃]
        have s1 : x + b₃ * k₂ + a₃ * k₁ = x + a₃ * k₁ + b₃ * k₂ := by ring
        have s2 : x + r * k₃ + a₃ * k₁ = x + a₃ * k₁ + r * k₃ := by ring
        have s3 : x + r * k₃ + b₃ * k₂ = x + b₃ * k₂ + r * k₃ := by ring
        have s4 : x + b₃ * k₂ + r * k₃ + a₃ * k₁ = x + a₃ * k₁ + b₃ * k₂ + r * k₃ := by ring
        rw [s1, s2, s3, s4]
        ring
      rw [hre1]
      dsimp only [Cube]
      calc
        ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ x : ZMod p,
            f₃ x * f₃ (x + h₁) * f₃ (x + h₂) * f₃ (x + h₁ + h₂) *
            f₃ (x + h₃) * f₃ (x + h₁ + h₃) * f₃ (x + h₂ + h₃) * f₃ (x + h₁ + h₂ + h₃)
          = ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ x : ZMod p, ∑ h₃ : ZMod p,
            f₃ x * f₃ (x + h₁) * f₃ (x + h₂) * f₃ (x + h₁ + h₂) *
            f₃ (x + h₃) * f₃ (x + h₁ + h₃) * f₃ (x + h₂ + h₃) * f₃ (x + h₁ + h₂ + h₃) := by
              apply Finset.sum_congr rfl; intro h₁ _
              apply Finset.sum_congr rfl; intro h₂ _
              exact Finset.sum_comm
        _ = ∑ h₁ : ZMod p, ∑ x : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
            f₃ x * f₃ (x + h₁) * f₃ (x + h₂) * f₃ (x + h₁ + h₂) *
            f₃ (x + h₃) * f₃ (x + h₁ + h₃) * f₃ (x + h₂ + h₃) * f₃ (x + h₁ + h₂ + h₃) := by
              apply Finset.sum_congr rfl; intro h₁ _
              exact Finset.sum_comm
        _ = Cube := Finset.sum_comm
    rw [hcube_eq] at hcs
    calc
      T₂ ^ 2 ≤ (p : ℝ) ^ 3 * ((p : ℝ) * Cube) := hcs
      _ = (p : ℝ) ^ 4 * Cube := by ring
  have hS4 : S ^ 4 ≤ (p : ℝ) ^ 4 * T₂ := by
    have h1 : (S ^ 2) ^ 2 ≤ ((p : ℝ) * T₁) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg S) hstep1 2
    calc
      S ^ 4 = (S ^ 2) ^ 2 := by ring
      _ ≤ ((p : ℝ) * T₁) ^ 2 := h1
      _ = (p : ℝ) ^ 2 * T₁ ^ 2 := by ring
      _ ≤ (p : ℝ) ^ 2 * ((p : ℝ) ^ 2 * T₂) := mul_le_mul_of_nonneg_left hstep2 (sq_nonneg _)
      _ = (p : ℝ) ^ 4 * T₂ := by ring
  have hS8 : S ^ 8 ≤ (p : ℝ) ^ 12 * Cube := by
    have h1 : (S ^ 4) ^ 2 ≤ ((p : ℝ) ^ 4 * T₂) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hS4 2
    calc
      S ^ 8 = (S ^ 4) ^ 2 := by ring
      _ ≤ ((p : ℝ) ^ 4 * T₂) ^ 2 := h1
      _ = (p : ℝ) ^ 8 * T₂ ^ 2 := by ring
      _ ≤ (p : ℝ) ^ 8 * ((p : ℝ) ^ 4 * Cube) := mul_le_mul_of_nonneg_left hstep3 (by positivity)
      _ = (p : ℝ) ^ 12 * Cube := by ring
  exact hS8

lemma zmod_0123_distinct {p : ℕ} (hp : 3 < p) :
    (0 : ZMod p) ≠ 1 ∧ (0 : ZMod p) ≠ 2 ∧ (0 : ZMod p) ≠ 3 ∧
    (1 : ZMod p) ≠ 2 ∧ (1 : ZMod p) ≠ 3 ∧ (2 : ZMod p) ≠ 3 := by
  have ne_cast : ∀ a b : ℕ, a < p → b < p → a ≠ b → (a : ZMod p) ≠ (b : ZMod p) := by
    intro a b ha hb hab h
    have hm := (ZMod.natCast_eq_natCast_iff' a b p).mp h
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hm
    exact hab hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using ne_cast 0 1 (by omega) (by omega) (by omega)
  · simpa using ne_cast 0 2 (by omega) (by omega) (by omega)
  · simpa using ne_cast 0 3 (by omega) (by omega) (by omega)
  · simpa using ne_cast 1 2 (by omega) (by omega) (by omega)
  · simpa using ne_cast 1 3 (by omega) (by omega) (by omega)
  · simpa using ne_cast 2 3 (by omega) (by omega) (by omega)

lemma four_ap_free_u3_lower
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (S : Finset (ZMod p))
    (hfree : ∀ x d : ZMod p, d ≠ 0 → ¬ (x ∈ S ∧ x + d ∈ S ∧ x + 2 * d ∈ S ∧ x + 3 * d ∈ S))
    (hdens : (2 : ℝ) ≤ ((S.card : ℝ) / (p : ℝ)) ^ 4 * (p : ℝ)) :
    let α : ℝ := (S.card : ℝ) / (p : ℝ)
    let f : ZMod p → ℝ := fun x => (if x ∈ S then (1 : ℝ) else 0) - α
    (p : ℝ) ^ 4 * (α ^ 4 / 8) ^ 8 ≤
      ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
        f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃) := by
  intro α f
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hα_nonneg : 0 ≤ α := by dsimp only [α]; positivity
  have hα_le1 : α ≤ 1 := by
    dsimp only [α]
    rw [div_le_one hp_pos]
    have hle : S.card ≤ Fintype.card (ZMod p) := Finset.card_le_univ S
    rw [ZMod.card] at hle
    exact_mod_cast hle
  let ind : ZMod p → ℝ := fun x => if x ∈ S then 1 else 0
  let cα : ZMod p → ℝ := fun _ => α
  have hind_bd : ∀ x, |ind x| ≤ 1 := fun x => by
    dsimp only [ind]; split_ifs <;> norm_num
  have hcα_bd : ∀ x, |cα x| ≤ 1 := fun x => by
    dsimp only [cα]; rw [abs_of_nonneg hα_nonneg]; exact hα_le1
  have hf_eq : ∀ x, ind x = cα x + f x := fun x => by
    dsimp only [ind, cα, f]; ring
  -- Count of 4-APs in S equals S.card
  have hcount : ∑ x : ZMod p, ∑ d : ZMod p,
      ind x * ind (x + d) * ind (x + 2 * d) * ind (x + 3 * d) = (S.card : ℝ) := by
    have hfiber : ∀ x : ZMod p,
        ∑ d : ZMod p, ind x * ind (x + d) * ind (x + 2 * d) * ind (x + 3 * d) = ind x := by
      intro x
      rw [Finset.sum_eq_single (0 : ZMod p)]
      · dsimp only [ind]; simp only [add_zero, mul_zero]; split_ifs <;> norm_num
      · intro d _ hd0
        have hnot := hfree x d hd0
        dsimp only [ind]
        by_cases hx0 : x ∈ S
        · by_cases hx1 : x + d ∈ S
          · by_cases hx2 : x + 2 * d ∈ S
            · have hx3 : x + 3 * d ∉ S := fun h3 => hnot ⟨hx0, hx1, hx2, h3⟩
              simp [hx0, hx1, hx2, hx3]
            · simp [hx0, hx1, hx2]
          · simp [hx0, hx1]
        · simp [hx0]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hfiber]
    dsimp only [ind]
    simp
  have hconst_count : ∑ x : ZMod p, ∑ d : ZMod p,
      cα x * cα (x + d) * cα (x + 2 * d) * cα (x + 3 * d) = α ^ 4 * (p : ℝ) ^ 2 := by
    dsimp only [cα]
    simp [ZMod.card]
    ring
  -- Telescope 1_S = α + f
  set T₁ : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
      ind (x + 1 * d) * ind (x + 2 * d) * ind (x + 3 * d) * f (x + 0 * d)
  set T₂ : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
      cα (x + 0 * d) * ind (x + 2 * d) * ind (x + 3 * d) * f (x + 1 * d)
  set T₃ : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
      cα (x + 0 * d) * cα (x + 1 * d) * ind (x + 3 * d) * f (x + 2 * d)
  set T₄ : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
      cα (x + 0 * d) * cα (x + 1 * d) * cα (x + 2 * d) * f (x + 3 * d)
  have htele : α ^ 4 * (p : ℝ) ^ 2 - (S.card : ℝ) = -(T₁ + T₂ + T₃ + T₄) := by
    rw [← hcount, ← hconst_count]
    dsimp only [T₁, T₂, T₃, T₄]
    have hpt : ∀ x d : ZMod p,
        cα x * cα (x + d) * cα (x + 2 * d) * cα (x + 3 * d) -
          ind x * ind (x + d) * ind (x + 2 * d) * ind (x + 3 * d) =
        -(ind (x + 1 * d) * ind (x + 2 * d) * ind (x + 3 * d) * f (x + 0 * d) +
          cα (x + 0 * d) * ind (x + 2 * d) * ind (x + 3 * d) * f (x + 1 * d) +
          cα (x + 0 * d) * cα (x + 1 * d) * ind (x + 3 * d) * f (x + 2 * d) +
          cα (x + 0 * d) * cα (x + 1 * d) * cα (x + 2 * d) * f (x + 3 * d)) := by
      intro x d
      simp only [zero_mul, add_zero, one_mul]
      rw [hf_eq x, hf_eq (x + d), hf_eq (x + 2 * d), hf_eq (x + 3 * d)]
      ring
    simp_rw [← Finset.sum_sub_distrib, hpt, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hScard_eq : (S.card : ℝ) = α * (p : ℝ) := by
    dsimp only [α]
    rw [div_mul_cancel₀ _ (ne_of_gt hp_pos)]
  have hdiff_ge : α ^ 4 * (p : ℝ) ^ 2 / 2 ≤ |T₁| + |T₂| + |T₃| + |T₄| := by
    have h1 : α * (p : ℝ) ≤ α ^ 4 * (p : ℝ) ^ 2 / 2 := by
      have h2 : (2 : ℝ) * (p : ℝ) ≤ α ^ 4 * (p : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hdens (le_of_lt hp_pos)
        linarith
      have h3 : α * (p : ℝ) ≤ (p : ℝ) := by nlinarith
      linarith
    have h2 : -(T₁ + T₂ + T₃ + T₄) ≤ |T₁| + |T₂| + |T₃| + |T₄| := by
      linarith [neg_le_abs T₁, neg_le_abs T₂, neg_le_abs T₃, neg_le_abs T₄]
    linarith
  set M : ℝ := max (max |T₁| |T₂|) (max |T₃| |T₄|)
  have hM_ge : (p : ℝ) ^ 2 * (α ^ 4 / 8) ≤ M := by
    have h1 : |T₁| ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
    have h2 : |T₂| ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
    have h3 : |T₃| ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
    have h4 : |T₄| ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := zmod_0123_distinct hp3
  set Cube : ℝ := ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
      f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
      f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃)
  have hT1_le : T₁ ^ 8 ≤ (p : ℝ) ^ 12 * Cube :=
    gowers_u3_von_neumann p 1 2 3 0 h01.symm h02.symm h03.symm ind ind ind f hind_bd hind_bd hind_bd
  have hT2_le : T₂ ^ 8 ≤ (p : ℝ) ^ 12 * Cube :=
    gowers_u3_von_neumann p 0 2 3 1 h01 h12.symm h13.symm cα ind ind f hcα_bd hind_bd hind_bd
  have hT3_le : T₃ ^ 8 ≤ (p : ℝ) ^ 12 * Cube :=
    gowers_u3_von_neumann p 0 1 3 2 h02 h12 h23.symm cα cα ind f hcα_bd hcα_bd hind_bd
  have hT4_le : T₄ ^ 8 ≤ (p : ℝ) ^ 12 * Cube :=
    gowers_u3_von_neumann p 0 1 2 3 h03 h13 h23 cα cα cα f hcα_bd hcα_bd hcα_bd
  have hM8_le : M ^ 8 ≤ (p : ℝ) ^ 12 * Cube := by
    have hpow : ∀ x : ℝ, |x| ^ 8 = x ^ 8 := fun x => by
      have : Even (8 : ℕ) := by decide
      exact this.pow_abs x
    have hcases : M = |T₁| ∨ M = |T₂| ∨ M = |T₃| ∨ M = |T₄| := by
      dsimp only [M]
      rcases max_choice (max |T₁| |T₂|) (max |T₃| |T₄|) with h | h <;> rw [h]
      · rcases max_choice |T₁| |T₂| with h' | h' <;> simp [h']
      · rcases max_choice |T₃| |T₄| with h' | h' <;> simp [h']
    rcases hcases with h | h | h | h <;> rw [h, hpow]
    · exact hT1_le
    · exact hT2_le
    · exact hT3_le
    · exact hT4_le
  have hpow_ge : ((p : ℝ) ^ 2 * (α ^ 4 / 8)) ^ 8 ≤ M ^ 8 :=
    pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (div_nonneg (pow_nonneg hα_nonneg 4) (by norm_num))) hM_ge 8
  have hcomb : (p : ℝ) ^ 12 * ((p : ℝ) ^ 4 * (α ^ 4 / 8) ^ 8) ≤ (p : ℝ) ^ 12 * Cube := by
    have heq : ((p : ℝ) ^ 2 * (α ^ 4 / 8)) ^ 8 = (p : ℝ) ^ 12 * ((p : ℝ) ^ 4 * (α ^ 4 / 8) ^ 8) := by
      ring
    linarith
  exact le_of_mul_le_mul_left hcomb (by positivity : (0 : ℝ) < (p : ℝ) ^ 12)

private lemma log_rpow_le_linear {A c : ℝ} (hA : 1 < A) (hc : 0 < c) :
    ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x → 2 * c * (Real.log x) ^ A ≤ x / 2 := by
  have hA0 : 0 < A := by linarith
  set B : ℝ := 4 * c * (2 * A) ^ A
  have hB_pos : 0 < B := by positivity
  refine ⟨max 2 (B ^ 2), le_max_left _ _, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hxB2 : B ^ 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h1 : Real.log x ≤ 2 * A * x ^ (1 / (2 * A)) := by
    have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 (1 / (2 * A)))
    rw [Real.log_rpow hx0] at hlog
    have h2A : 0 < 2 * A := by linarith
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt h2A)
    have hlhs : 2 * A * (1 / (2 * A) * Real.log x) = Real.log x := by field_simp
    linarith
  have hpow : (Real.log x) ^ A ≤ (2 * A) ^ A * x ^ ((1 : ℝ) / 2) := by
    have h2 := Real.rpow_le_rpow hlog_nonneg h1 (le_of_lt hA0)
    rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg (le_of_lt hx0) _),
      ← Real.rpow_mul (le_of_lt hx0)] at h2
    have hexp : 1 / (2 * A) * A = (1 : ℝ) / 2 := by field_simp
    rwa [hexp] at h2
  have hB_le : B ≤ x ^ ((1 : ℝ) / 2) := by
    have hsq := Real.rpow_le_rpow (sq_nonneg B) hxB2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hBsq : (B ^ 2) ^ ((1 : ℝ) / 2) = B := by
      rw [← Real.rpow_natCast B 2, ← Real.rpow_mul (le_of_lt hB_pos)]
      norm_num
    rwa [hBsq] at hsq
  have hprod : B * x ^ ((1 : ℝ) / 2) ≤ x := by
    have hmul := mul_le_mul_of_nonneg_right hB_le (Real.rpow_nonneg (le_of_lt hx0) ((1 : ℝ) / 2))
    have hxx : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    linarith
  have hcomb : 2 * c * (Real.log x) ^ A ≤ (B / 2) * x ^ ((1 : ℝ) / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hpow (by linarith : (0 : ℝ) ≤ 2 * c)
    have heq : 2 * c * ((2 * A) ^ A * x ^ ((1 : ℝ) / 2)) = (B / 2) * x ^ ((1 : ℝ) / 2) := by
      dsimp only [B]; ring
    linarith
  linarith

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1.H1 := by
  intro hspec hmain
  obtain ⟨A, c, hA, hc, hp_ev⟩ := hmain
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp hp_ev
  obtain ⟨X₀, hX₀2, hX₀⟩ := log_rpow_le_linear hA hc
  set T₀ : ℝ := max (max 1 (8 / c)) (Real.log (max X₀ 1000))
  set N₀ : ℕ := max (max 10 P₀) (Nat.ceil (Real.exp (Real.exp T₀)) + 1)
  refine ⟨A, c / 2, hA, by linarith, Filter.eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩⟩
  have hN10 : 10 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNP0 : P₀ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN_exp : Real.exp (Real.exp T₀) ≤ (N : ℝ) := by
    have h1 : Real.exp (Real.exp T₀) ≤ (Nat.ceil (Real.exp (Real.exp T₀)) : ℝ) := Nat.le_ceil _
    have h2 : Nat.ceil (Real.exp (Real.exp T₀)) + 1 ≤ N := le_trans (le_max_right _ _) hN
    have h3 : ((Nat.ceil (Real.exp (Real.exp T₀)) : ℝ)) ≤ (N : ℝ) := by exact_mod_cast (by omega : Nat.ceil (Real.exp (Real.exp T₀)) ≤ N)
    linarith
  have hlogN_ge : Real.exp T₀ ≤ Real.log (N : ℝ) := by
    have h1 := Real.log_le_log (Real.exp_pos _) hN_exp
    rwa [Real.log_exp] at h1
  have hloglogN_ge : T₀ ≤ Real.log (Real.log (N : ℝ)) := by
    have h1 := Real.log_le_log (Real.exp_pos _) hlogN_ge
    rwa [Real.log_exp] at h1
  have hlogN_ge_X0 : X₀ ≤ Real.log (N : ℝ) := by
    have h1 : Real.log (max X₀ 1000) ≤ T₀ := le_max_right _ _
    have h2 : max X₀ 1000 ≤ Real.exp T₀ := by
      have := Real.exp_le_exp.mpr h1
      rwa [Real.exp_log (by linarith [le_max_left X₀ 1000] : (0 : ℝ) < max X₀ 1000)] at this
    exact le_trans (le_max_left X₀ 1000) (le_trans h2 hlogN_ge)
  have hlogN_ge_1000 : (1000 : ℝ) ≤ Real.log (N : ℝ) := by
    have h1 : Real.log (max X₀ 1000) ≤ T₀ := le_max_right _ _
    have h2 : max X₀ 1000 ≤ Real.exp T₀ := by
      have := Real.exp_le_exp.mpr h1
      rwa [Real.exp_log (by linarith [le_max_left X₀ 1000] : (0 : ℝ) < max X₀ 1000)] at this
    exact le_trans (le_max_right X₀ 1000) (le_trans h2 hlogN_ge)
  by_contra hgt
  push Not at hgt
  -- Embed an extremal 4-AP-free set into ZMod p with 2N < p ≤ 4N
  obtain ⟨p, hp_prime, hp_lo, hp_hi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have hp_hi4 : p ≤ 4 * N := by omega
  have hp_ge_P0 : P₀ ≤ p := by omega
  have hp3 : 3 < p := by omega
  let : Fact p.Prime := ⟨hp_prime⟩
  obtain ⟨S₀, hS₀_sub, hS₀_free, hS₀_card⟩ := exists_extremal_ap_free 4 N
  let S : Finset (ZMod p) := S₀.image (fun x : ℕ => (x : ZMod p))
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod p)) (S₀ : Set ℕ) := by
    intro x hx y hy heq
    have hxN : x ≤ N := (Finset.mem_Icc.mp (hS₀_sub hx)).2
    have hyN : y ≤ N := (Finset.mem_Icc.mp (hS₀_sub hy)).2
    have hm := (ZMod.natCast_eq_natCast_iff' x y p).mp heq
    rwa [Nat.mod_eq_of_lt (by omega : x < p), Nat.mod_eq_of_lt (by omega : y < p)] at hm
  have hScard : S.card = r 4 N := by
    rw [← hS₀_card, Finset.card_image_of_injOn hinj]
  have hSfree : ∀ x d : ZMod p, d ≠ 0 → ¬ (x ∈ S ∧ x + d ∈ S ∧ x + 2 * d ∈ S ∧ x + 3 * d ∈ S) :=
    no_wrap_four_ap hp_lo hS₀_sub hS₀_free
  -- Density comparison in ZMod p
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
  have hll_ge1 : 1 ≤ Real.log (Real.log (N : ℝ)) :=
    le_trans (le_trans (le_max_left 1 (8 / c)) (le_max_left _ _)) hloglogN_ge
  have hll_ge8c : 8 / c ≤ Real.log (Real.log (N : ℝ)) :=
    le_trans (le_trans (le_max_right 1 (8 / c)) (le_max_left _ _)) hloglogN_ge
  have hll_le_p : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (p : ℝ)) := by
    have hNp : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show N ≤ p by omega)
    exact Real.log_le_log (by linarith) (Real.log_le_log hN_pos hNp)
  have hllA_le : Real.log (Real.log (N : ℝ)) ^ A ≤ Real.log (Real.log (p : ℝ)) ^ A :=
    Real.rpow_le_rpow (by linarith) hll_le_p (by linarith)
  have h4_le_exp : (4 : ℝ) ≤ Real.exp ((c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
    have hpow_ge : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (N : ℝ)) ^ A := by
      have := Real.rpow_le_rpow_of_exponent_le hll_ge1 (le_of_lt hA)
      rwa [Real.rpow_one] at this
    have harg : (4 : ℝ) ≤ (c / 2) * Real.log (Real.log (N : ℝ)) ^ A := by
      have h1 : (4 : ℝ) ≤ (c / 2) * (8 / c) := by field_simp; norm_num
      have h2 : (c / 2) * (8 / c) ≤ (c / 2) * Real.log (Real.log (N : ℝ)) ^ A :=
        mul_le_mul_of_nonneg_left (le_trans hll_ge8c hpow_ge) (by linarith)
      linarith
    have := Real.add_one_le_exp ((c / 2) * Real.log (Real.log (N : ℝ)) ^ A)
    linarith
  have hS_dense : (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) < (S.card : ℝ) := by
    rw [hScard]
    have hp4N : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hp_hi4
    have hexp_mono : Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) ≤
        Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hsplit : (4 : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) ≤
        Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
      have hmul := mul_le_mul_of_nonneg_right h4_le_exp (Real.exp_pos (-c * Real.log (Real.log (N : ℝ)) ^ A)).le
      rw [← Real.exp_add] at hmul
      have harg : (c / 2) * Real.log (Real.log (N : ℝ)) ^ A +
          -c * Real.log (Real.log (N : ℝ)) ^ A =
          -(c / 2) * Real.log (Real.log (N : ℝ)) ^ A := by ring
      rwa [harg] at hmul
    calc
      (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A)
          ≤ (4 * (N : ℝ)) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) :=
            mul_le_mul hp4N hexp_mono (Real.exp_pos _).le (by positivity)
      _ = (N : ℝ) * (4 * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A)) := by ring
      _ ≤ (N : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) :=
            mul_le_mul_of_nonneg_left hsplit (le_of_lt hN_pos)
      _ < (r 4 N : ℝ) := hgt
  -- Verify α^4 * p ≥ 2
  have hα_ge : (1 / 4 : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) ≤
      (S.card : ℝ) / (p : ℝ) := by
    rw [hScard, le_div_iff₀ hp_pos]
    have hp4N : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hp_hi4
    have h1 : (1 / 4 : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) * (p : ℝ) ≤
        (N : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
      have hmul := mul_le_mul_of_nonneg_left hp4N
        (show 0 ≤ (1 / 4 : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) by positivity)
      linarith
    linarith
  have hdens2 : (2 : ℝ) ≤ ((S.card : ℝ) / (p : ℝ)) ^ 4 * (p : ℝ) := by
    have hpow4 : ((1 / 4 : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A)) ^ 4 ≤
        ((S.card : ℝ) / (p : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hα_ge 4
    have h2N : 2 * (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 2 * N ≤ p by omega)
    have hprod : (1 / 128 : ℝ) * (N : ℝ) * Real.exp (-2 * c * Real.log (Real.log (N : ℝ)) ^ A) ≤
        ((S.card : ℝ) / (p : ℝ)) ^ 4 * (p : ℝ) := by
      have heq : ((1 / 4 : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A)) ^ 4 * (2 * (N : ℝ)) =
          (1 / 128 : ℝ) * (N : ℝ) * Real.exp (-2 * c * Real.log (Real.log (N : ℝ)) ^ A) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        push_cast
        ring_nf
      have hmul := mul_le_mul hpow4 h2N (by positivity) (by positivity)
      linarith
    have hlin := hX₀ (Real.log (N : ℝ)) hlogN_ge_X0
    have hexp_big : (256 : ℝ) ≤ (N : ℝ) * Real.exp (-2 * c * Real.log (Real.log (N : ℝ)) ^ A) := by
      have harg : (500 : ℝ) ≤ Real.log (N : ℝ) + -2 * c * Real.log (Real.log (N : ℝ)) ^ A := by
        linarith
      have hadd := Real.add_one_le_exp (Real.log (N : ℝ) + -2 * c * Real.log (Real.log (N : ℝ)) ^ A)
      calc
        (256 : ℝ) ≤ Real.exp (Real.log (N : ℝ) + -2 * c * Real.log (Real.log (N : ℝ)) ^ A) := by
          linarith
        _ = (N : ℝ) * Real.exp (-2 * c * Real.log (Real.log (N : ℝ)) ^ A) := by
          rw [Real.exp_add, Real.exp_log hN_pos]
    linarith
  -- Apply U^3 lower bound + H1 + H2
  have hu3 := four_ap_free_u3_lower hp3 S hSfree hdens2
  dsimp only at hu3
  set α : ℝ := (S.card : ℝ) / (p : ℝ)
  set f : ZMod p → ℝ := fun x => (if x ∈ S then (1 : ℝ) else 0) - α
  have hu3' : (p : ℝ) ^ 4 * (α ^ 4 / 8) ^ 8 ≤
      ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
        f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃) := hu3
  have hf_bd : ∀ x, |f x| ≤ 1 := by
    intro x
    have hα0 : 0 ≤ α := by dsimp only [α]; positivity
    have hα1 : α ≤ 1 := by
      dsimp only [α]
      rw [div_le_one hp_pos]
      have hle : S.card ≤ Fintype.card (ZMod p) := Finset.card_le_univ S
      rw [ZMod.card] at hle
      exact_mod_cast hle
    dsimp only [f]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  obtain ⟨ξ, hξ⟩ := hspec p f hf_bd
  have hspec_lb : (p : ℝ) ^ 3 * (α ^ 4 / 8) ^ 8 ≤
      ∑ h : ZMod p,
        ‖∑ x : ZMod p, ((f x * f (x + h) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (((x * ξ h).val : ℕ) : ℂ) / (p : ℂ))‖ ^ 2 := by
    have hcomb : (p : ℝ) * ((p : ℝ) ^ 3 * (α ^ 4 / 8) ^ 8) ≤
        (p : ℝ) * ∑ h : ZMod p,
          ‖∑ x : ZMod p, ((f x * f (x + h) : ℝ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (((x * ξ h).val : ℕ) : ℂ) / (p : ℂ))‖ ^ 2 := by
      have heq : (p : ℝ) * ((p : ℝ) ^ 3 * (α ^ 4 / 8) ^ 8) = (p : ℝ) ^ 4 * (α ^ 4 / 8) ^ 8 := by ring
      linarith
    exact le_of_mul_le_mul_left hcomb hp_pos
  obtain ⟨x, d, hd0, h0, h1, h2, h3⟩ := hP₀ p hp_ge_P0 S hS_dense ⟨ξ, hspec_lb⟩
  exact hSfree x d hd0 ⟨h0, h1, h2, h3⟩

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2
