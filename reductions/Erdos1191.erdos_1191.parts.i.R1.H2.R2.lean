import OMAReductions.R_Erdos1191_erdos_1191_parts_i_R1

/-!
# Reduction `Erdos1191.erdos_1191.parts.i.R1.H2.R2` — Sound asymptotic regular/spiky split

Replaces the broken reduction `Erdos1191.erdos_1191.parts.i.R1.H2.R1` (whose `H1` restricted
the scale `R` to the bounded interval `[R₀, 2 * R₀]` for arbitrary `L`, making it false via
singleton Sidon sets such as `S = {2 ^ 33}` at `R₀ = 16, L = 2 ^ 32`, as independently
documented by `@KeystoneScience`, `@KevinBigham`, `@ehsanmok`, and `@rickmanelius`).

This reduction raises any base scale `R₀ ≥ 16` into the clean asymptotic regime
`R₁ = max R₀ (max 86 (4 * L))`, keeps `R` ranging over the full unbounded interval
`Set.Icc R₁ (K - L)`, and splits `Erdos1191.erdos_1191.parts.i.R1.H2` cleanly into two
sound, complementary regimes:

* `H1` (regular dyadic regime): Sidon sets `S ⊆ [1, 2 ^ K]` whose dyadic profile
  `|S ∩ [1, 2 ^ R]| ^ 2 * R / 2 ^ R` stays at most `C` across `[R₁, K - L]`.
* `H2` (spiky dyadic regime): Sidon sets `S ⊆ [1, 2 ^ K]` whose dyadic profile exceeds `C`
  at some scale in `[R₁, K₀ - L]`, asking for a light window at some scale in `[R₁, K - L]`.

Inside this file we also prove:
1. `old_R1_H1_refuted`: formal refutation of the bounded-scale `[R₀, 2 * R₀]` statement.
2. `sidon_prefix_truncation`: truncating `S ⊆ [1, 2 ^ K]` to `S.filter (· ≤ 2 ^ K₀)` preserves
   `IsSidon` and every prefix/window count up to `R ≤ K₀ - L`.
3. `singleton_passes_H1`: sanity theorem verifying every singleton Sidon set `{a}` satisfies
   the repaired `H1` at `K = 2 * R₁ + 2 * L + 2`.
-/

-- Credit: @sanchan (acknowledging @KeystoneScience, @KevinBigham, @ehsanmok, @rickmanelius for diagnosing the R1.H2.R1.H1 counterexample)

namespace OMA.R_Erdos1191_erdos_1191_parts_i_R1_H2_R2

open Finset

/-- Regular dyadic regime (`R₁ ≥ max 86 (4 * L)`): Sidon sets whose dyadic profile stays
uniformly bounded by `C` across `[R₁, K - L]` admit a good scale `R ∈ [R₁, K - L]` with a
light `L`-window. -/
def H1 : Prop :=
  ∀ L C R₁ : ℕ, 1 ≤ L → 512 ≤ C → max 86 (4 * L) ≤ R₁ →
    ∃ K : ℕ, 2 * R₁ + L ≤ K ∧
      ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (↑S : Set ℕ) →
        (∀ R ∈ Set.Icc R₁ (K - L), (S.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ C * 2 ^ R) →
        ∃ R ∈ Set.Icc R₁ (K - L),
          (S.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ 512 * 2 ^ R ∧
          2 ^ L * (S.filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ (R + L))).card ^ 2 * (R + L) ≤
            2 ^ (R + L)

/-- Spiky dyadic regime (`R₁ ≥ max 86 (4 * L)`): for a suitable threshold `C = C(L) ≥ 512`,
any Sidon set whose dyadic profile exceeds `C` somewhere on `[R₁, K₀ - L]` admits, below a
later horizon `K ≥ K₀`, a good scale `R ∈ [R₁, K - L]` with a light `L`-window. -/
def H2 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∃ C : ℕ, 512 ≤ C ∧
    ∀ R₁ K₀ : ℕ, max 86 (4 * L) ≤ R₁ → 2 * R₁ + L ≤ K₀ →
      ∃ K : ℕ, K₀ ≤ K ∧
        ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (↑S : Set ℕ) →
          (∃ R ∈ Set.Icc R₁ (K₀ - L), C * 2 ^ R < (S.filter (· ≤ 2 ^ R)).card ^ 2 * R) →
          ∃ R ∈ Set.Icc R₁ (K - L),
            (S.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ 512 * 2 ^ R ∧
            2 ^ L * (S.filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ (R + L))).card ^ 2 * (R + L) ≤
              2 ^ (R + L)

/-- Refutation of the bounded-scale variant (`R ∈ [R₀, 2 * R₀]` for arbitrary `L`) from
`R1.H2.R1.H1`: at `R₀ = 16`, `L = 2 ^ 32`, the Sidon singleton `S = {2 ^ 33}` violates
the window inequality for every `R ∈ [16, 32]`. -/
theorem old_R1_H1_refuted :
    ¬ (∀ L R₀ : ℕ, 16 ≤ R₀ → R₀ ≤ 85 → 1 ≤ L →
        ∃ K : ℕ, 2 * R₀ + L ≤ K ∧
          ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (↑S : Set ℕ) →
            ∃ R ∈ Set.Icc R₀ (2 * R₀),
              2 ^ L * (S.filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ (R + L))).card ^ 2 * (R + L) ≤
                2 ^ (R + L)) := by
  intro hbad
  set L0 : ℕ := 2 ^ 32 with hL0
  have hL0_ge : 1 ≤ L0 := by rw [hL0]; norm_num
  have hL0_33 : 33 ≤ 2 * 16 + L0 := by rw [hL0]; norm_num
  obtain ⟨K, hK, hS⟩ := hbad L0 16 (by norm_num) (by norm_num) hL0_ge
  let S : Finset ℕ := {2 ^ 33}
  have hS_sub : (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) := by
    intro x hx
    have hx' : x = 2 ^ 33 := by simpa [S] using hx
    subst hx'
    exact ⟨by norm_num, Nat.pow_le_pow_right (by norm_num) (by omega)⟩
  have hS_sid : IsSidon (↑S : Set ℕ) := by
    intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ _
    have h1 : i₁ = 2 ^ 33 := by simpa [S] using hi₁
    have h2 : j₁ = 2 ^ 33 := by simpa [S] using hj₁
    have h3 : i₂ = 2 ^ 33 := by simpa [S] using hi₂
    have h4 : j₂ = 2 ^ 33 := by simpa [S] using hj₂
    exact Or.inl ⟨h1.trans h2.symm, h3.trans h4.symm⟩
  obtain ⟨R, ⟨hRlo, hRhi⟩, hineq⟩ := hS S hS_sub hS_sid
  have hlt : 2 ^ R < 2 ^ 33 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hle : 2 ^ 33 ≤ 2 ^ (R + L0) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfilt : S.filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ (R + L0)) = S := by
    ext a
    simp only [S, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro rfl; exact ⟨rfl, hlt, hle⟩
  rw [hfilt] at hineq
  have hcard : S.card = 1 := Finset.card_singleton _
  rw [hcard, one_pow, mul_one, pow_add] at hineq
  have h2Lpos : 0 < 2 ^ L0 := Nat.two_pow_pos L0
  have hcancel : R + L0 ≤ 2 ^ R := by
    have : 2 ^ L0 * (R + L0) ≤ 2 ^ L0 * 2 ^ R := by
      simpa [mul_comm] using hineq
    exact Nat.le_of_mul_le_mul_left this h2Lpos
  have h2Rle : 2 ^ R ≤ L0 := by
    rw [hL0]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Truncating a Sidon set `S` to `S.filter (· ≤ 2 ^ K₀)` preserves `IsSidon` and preserves
all prefix and `L`-window counts for scales `R ≤ K₀ - L`. -/
theorem sidon_prefix_truncation {S : Finset ℕ} (hSid : IsSidon (↑S : Set ℕ)) {K₀ L R : ℕ}
    (hLK₀ : L ≤ K₀) (hR : R ≤ K₀ - L) :
    IsSidon (↑(S.filter (· ≤ 2 ^ K₀)) : Set ℕ) ∧
    (S.filter (· ≤ 2 ^ K₀)).filter (· ≤ 2 ^ R) = S.filter (· ≤ 2 ^ R) ∧
    (S.filter (· ≤ 2 ^ K₀)).filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ (R + L)) =
      S.filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ (R + L)) := by
  have hRK : R ≤ K₀ := by omega
  have hRLK : R + L ≤ K₀ := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    exact hSid i₁ (Finset.filter_subset _ _ hi₁) j₁ (Finset.filter_subset _ _ hj₁)
      i₂ (Finset.filter_subset _ _ hi₂) j₂ (Finset.filter_subset _ _ hj₂) hsum
  · ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, _⟩, hle⟩; exact ⟨ha, hle⟩
    · rintro ⟨ha, hle⟩
      exact ⟨⟨ha, hle.trans (Nat.pow_le_pow_right (by norm_num) hRK)⟩, hle⟩
  · ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, _⟩, h1, h2⟩; exact ⟨ha, h1, h2⟩
    · rintro ⟨ha, h1, h2⟩
      exact ⟨⟨ha, h2.trans (Nat.pow_le_pow_right (by norm_num) hRLK)⟩, h1, h2⟩

/-- Sanity check: every singleton Sidon set `{a}` satisfies the conclusion of `H1` at
`K = 2 * R₁ + 2 * L + 2`, showing our repaired reduction is immune to the `R1.H2.R1` bug. -/
theorem singleton_passes_H1 {L R₁ a : ℕ} :
    let K := 2 * R₁ + 2 * L + 2
    ∃ R ∈ Set.Icc R₁ (K - L),
      (({a} : Finset ℕ).filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ 512 * 2 ^ R ∧
      2 ^ L * (({a} : Finset ℕ).filter (fun x => 2 ^ R < x ∧ x ≤ 2 ^ (R + L))).card ^ 2 * (R + L) ≤
        2 ^ (R + L) := by
  intro K
  have hgood : ∀ R : ℕ, (({a} : Finset ℕ).filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ 512 * 2 ^ R := by
    intro R
    have hc : (({a} : Finset ℕ).filter (· ≤ 2 ^ R)).card ≤ 1 := by
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hc2 : (({a} : Finset ℕ).filter (· ≤ 2 ^ R)).card ^ 2 ≤ 1 := by nlinarith
    have hlt : R < 2 ^ R := Nat.lt_two_pow_self
    nlinarith
  by_cases ha : 2 ^ R₁ < a ∧ a ≤ 2 ^ (R₁ + L)
  · refine ⟨R₁ + L, ⟨by omega, by dsimp only [K]; omega⟩, hgood (R₁ + L), ?_⟩
    have hemp : ({a} : Finset ℕ).filter (fun x => 2 ^ (R₁ + L) < x ∧ x ≤ 2 ^ (R₁ + L + L)) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl h1 _
      omega
    rw [hemp]
    simp
  · refine ⟨R₁, ⟨le_rfl, by dsimp only [K]; omega⟩, hgood R₁, ?_⟩
    have hemp : ({a} : Finset ℕ).filter (fun x => 2 ^ R₁ < x ∧ x ≤ 2 ^ (R₁ + L)) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl h1 h2
      exact ha ⟨h1, h2⟩
    rw [hemp]
    simp

theorem main : H1 → H2 → OMA.R_Erdos1191_erdos_1191_parts_i_R1.H2 := by
  intro h1 h2 L R₀ hR₀ hL
  set R₁ : ℕ := max R₀ (max 86 (4 * L))
  have hR₀_le : R₀ ≤ R₁ := le_max_left _ _
  have hR₁_ge : max 86 (4 * L) ≤ R₁ := le_max_right _ _
  obtain ⟨C, hC512, h2C⟩ := h2 L hL
  obtain ⟨K₀, hK₀_ge, h1K₀⟩ := h1 L C R₁ hL hC512 hR₁_ge
  obtain ⟨K, hK_ge, h2K⟩ := h2C R₁ K₀ hR₁_ge hK₀_ge
  refine ⟨K, by omega, ?_⟩
  intro S hS_sub hS_sid _
  by_cases hreg : ∀ R ∈ Set.Icc R₁ (K₀ - L), (S.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ C * 2 ^ R
  · let S₀ : Finset ℕ := S.filter (· ≤ 2 ^ K₀)
    have hS₀_sub : (↑S₀ : Set ℕ) ⊆ Set.Icc 1 (2 ^ K₀) := by
      intro x hx
      obtain ⟨hxS, hxle⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      exact ⟨(hS_sub (Finset.mem_coe.mpr hxS)).1, hxle⟩
    have hS₀_sid : IsSidon (↑S₀ : Set ℕ) :=
      (sidon_prefix_truncation hS_sid (K₀ := K₀) (L := 0) (R := 0) (by omega) (by omega)).1
    have hS₀_reg : ∀ R ∈ Set.Icc R₁ (K₀ - L),
        (S₀.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ C * 2 ^ R := by
      intro R hR
      have heq := (sidon_prefix_truncation hS_sid (K₀ := K₀) (L := L) (by omega) hR.2).2.1
      rw [show S₀ = S.filter (· ≤ 2 ^ K₀) from rfl, heq]
      exact hreg R hR
    obtain ⟨R, hR, hgood, hlight⟩ := h1K₀ S₀ hS₀_sub hS₀_sid hS₀_reg
    have htr := sidon_prefix_truncation hS_sid (K₀ := K₀) (L := L) (by omega) hR.2
    rw [show S₀ = S.filter (· ≤ 2 ^ K₀) from rfl, htr.2.1] at hgood
    rw [show S₀ = S.filter (· ≤ 2 ^ K₀) from rfl, htr.2.2] at hlight
    exact ⟨R, ⟨hR₀_le.trans hR.1, hR.2.trans (Nat.sub_le_sub_right hK_ge L)⟩, hgood, hlight⟩
  · push Not at hreg
    obtain ⟨R, hR, hgood, hlight⟩ := h2K S hS_sub hS_sid hreg
    exact ⟨R, ⟨hR₀_le.trans hR.1, hR.2⟩, hgood, hlight⟩

end OMA.R_Erdos1191_erdos_1191_parts_i_R1_H2_R2
