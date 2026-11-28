import OMAReductions.R_Erdos387_erdos_387_variants_guy_R1
import Mathlib

/-! Decomposition of the mixed-divisor exception bound (`H3` of
`Erdos387.erdos_387.variants.guy.R1`) into the four structural divisor regimes of
Bui-Naprienko-Pratt-Zaharescu (arXiv:2605.21221, Section 6, Propositions 6.2-6.6):
- `H1`: some factor `f i` satisfies `x^(51/100) ≤ f i` (elementary divisor-switching, Prop. 6.2);
- `H2`: all `f i < x^(51/100)` and some `f i ≥ x^(35/100)` (Weil Kloosterman bound + Type I/II, Prop. 6.3);
- `H3`: all `f i < x^(35/100)` and some `f i` admits a convenient factorization `r * s` with
  `r, s ≥ x^(1/(100*k))` (bilinear short Kloosterman sums, Prop. 6.4);
- `H4`: all `f i < x^(35/100)` with no convenient factorization (close primes + q-van der Corput,
  Propositions 6.5 and 6.6). -/

namespace OMA.R_Erdos387_erdos_387_variants_guy_R1_H3_R1
open Finset Filter Real
open scoped Classical

/-- Regime 1 (Proposition 6.2, elementary divisor-switching): at least one factor `f i`
satisfies `x^(51/100) ≤ f i`. -/
def H1 : Prop := ∀ᶠ k : ℕ in atTop, ∀ γ : ℕ, ∀ g : ℕ → ℕ, ((∀ i < k, 2 ≤ g i) ∧
    (∏ i ∈ range k, g i) = k.factorial ∧
    ∀ n : ℕ, k < n → n ≡ γ [MOD (∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1))] →
      (∀ i < k, g i ∣ n - i) ∧ ∀ p : ℕ, p.Prime → p ≤ 2 * k → ¬ p ∣ n.choose k) →
  ∀ᶠ x : ℕ in atTop,
    let S := (Ioc x (2 * x)).filter (fun n =>
      n ≡ γ [MOD (∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1))] ∧
      ∀ p : ℕ, p.Prime → p ∣ n.choose k → (x : ℝ) ^ ((3 : ℝ) ^ k)⁻¹ ≤ p)
    40 * (S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
      (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
      n < 2 * (∏ i ∈ range k, f i) ∧ (∏ i ∈ range k, f i) ≤ n ∧
      (∃ i < k, (x : ℝ) ^ (51 / 100 : ℝ) ≤ (f i : ℝ)))).card ≤ 9 * S.card

/-- Regime 2 (Proposition 6.3, Weil bound for Kloosterman sums + Type I/II): all factors satisfy
`f i < x^(51/100)` and at least one satisfies `x^(35/100) ≤ f i`. -/
def H2 : Prop := ∀ᶠ k : ℕ in atTop, ∀ γ : ℕ, ∀ g : ℕ → ℕ, ((∀ i < k, 2 ≤ g i) ∧
    (∏ i ∈ range k, g i) = k.factorial ∧
    ∀ n : ℕ, k < n → n ≡ γ [MOD (∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1))] →
      (∀ i < k, g i ∣ n - i) ∧ ∀ p : ℕ, p.Prime → p ≤ 2 * k → ¬ p ∣ n.choose k) →
  ∀ᶠ x : ℕ in atTop,
    let S := (Ioc x (2 * x)).filter (fun n =>
      n ≡ γ [MOD (∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1))] ∧
      ∀ p : ℕ, p.Prime → p ∣ n.choose k → (x : ℝ) ^ ((3 : ℝ) ^ k)⁻¹ ≤ p)
    40 * (S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
      (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
      n < 2 * (∏ i ∈ range k, f i) ∧ (∏ i ∈ range k, f i) ≤ n ∧
      (∀ i < k, (f i : ℝ) < (x : ℝ) ^ (51 / 100 : ℝ)) ∧
      (∃ i < k, (x : ℝ) ^ (35 / 100 : ℝ) ≤ (f i : ℝ)))).card ≤ 9 * S.card

/-- Regime 3 (Proposition 6.4, bilinear forms in short incomplete Kloosterman sums): all factors
satisfy `f i < x^(35/100)` and some `f i` admits a convenient factorization `f i = r * s`
with `r, s ≥ x^(1/(100*k))`. -/
def H3 : Prop := ∀ᶠ k : ℕ in atTop, ∀ γ : ℕ, ∀ g : ℕ → ℕ, ((∀ i < k, 2 ≤ g i) ∧
    (∏ i ∈ range k, g i) = k.factorial ∧
    ∀ n : ℕ, k < n → n ≡ γ [MOD (∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1))] →
      (∀ i < k, g i ∣ n - i) ∧ ∀ p : ℕ, p.Prime → p ≤ 2 * k → ¬ p ∣ n.choose k) →
  ∀ᶠ x : ℕ in atTop,
    let S := (Ioc x (2 * x)).filter (fun n =>
      n ≡ γ [MOD (∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1))] ∧
      ∀ p : ℕ, p.Prime → p ∣ n.choose k → (x : ℝ) ^ ((3 : ℝ) ^ k)⁻¹ ≤ p)
    40 * (S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
      (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
      n < 2 * (∏ i ∈ range k, f i) ∧ (∏ i ∈ range k, f i) ≤ n ∧
      (∀ i < k, (f i : ℝ) < (x : ℝ) ^ (35 / 100 : ℝ)) ∧
      (∃ i < k, ∃ r s : ℕ, f i = r * s ∧
        (x : ℝ) ^ ((100 * (k : ℝ))⁻¹) ≤ (r : ℝ) ∧
        (x : ℝ) ^ ((100 * (k : ℝ))⁻¹) ≤ (s : ℝ)))).card ≤ 9 * S.card

/-- Regime 4 (Propositions 6.5 and 6.6, close primes and q-van der Corput method): all factors
satisfy `f i < x^(35/100)` and none admits a convenient factorization `r * s` with
`r, s ≥ x^(1/(100*k))`. -/
def H4 : Prop := ∀ᶠ k : ℕ in atTop, ∀ γ : ℕ, ∀ g : ℕ → ℕ, ((∀ i < k, 2 ≤ g i) ∧
    (∏ i ∈ range k, g i) = k.factorial ∧
    ∀ n : ℕ, k < n → n ≡ γ [MOD (∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1))] →
      (∀ i < k, g i ∣ n - i) ∧ ∀ p : ℕ, p.Prime → p ≤ 2 * k → ¬ p ∣ n.choose k) →
  ∀ᶠ x : ℕ in atTop,
    let S := (Ioc x (2 * x)).filter (fun n =>
      n ≡ γ [MOD (∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1))] ∧
      ∀ p : ℕ, p.Prime → p ∣ n.choose k → (x : ℝ) ^ ((3 : ℝ) ^ k)⁻¹ ≤ p)
    40 * (S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
      (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
      n < 2 * (∏ i ∈ range k, f i) ∧ (∏ i ∈ range k, f i) ≤ n ∧
      (∀ i < k, (f i : ℝ) < (x : ℝ) ^ (35 / 100 : ℝ)) ∧
      (∀ i < k, ∀ r s : ℕ, f i = r * s →
        (r : ℝ) < (x : ℝ) ^ ((100 * (k : ℝ))⁻¹) ∨
        (s : ℝ) < (x : ℝ) ^ ((100 * (k : ℝ))⁻¹)))).card ≤ 9 * S.card

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos387_erdos_387_variants_guy_R1.H3 := by
  intro h1 h2 h3 h4
  rw [OMA.R_Erdos387_erdos_387_variants_guy_R1.H3]
  filter_upwards [h1, h2, h3, h4] with k hk1 hk2 hk3 hk4
  intro γ g hcov
  filter_upwards [hk1 γ g hcov, hk2 γ g hcov, hk3 γ g hcov, hk4 γ g hcov] with x hx1 hx2 hx3 hx4
  intro S
  set E := S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
    (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
    n < 2 * (∏ i ∈ range k, f i) ∧ (∏ i ∈ range k, f i) ≤ n)
  set E1 := S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
    (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
    n < 2 * (∏ i ∈ range k, f i) ∧ (∏ i ∈ range k, f i) ≤ n ∧
    (∃ i < k, (x : ℝ) ^ (51 / 100 : ℝ) ≤ (f i : ℝ)))
  set E2 := S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
    (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
    n < 2 * (∏ i ∈ range k, f i) ∧ (∏ i ∈ range k, f i) ≤ n ∧
    (∀ i < k, (f i : ℝ) < (x : ℝ) ^ (51 / 100 : ℝ)) ∧
    (∃ i < k, (x : ℝ) ^ (35 / 100 : ℝ) ≤ (f i : ℝ)))
  set E3 := S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
    (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
    n < 2 * (∏ i ∈ range k, f i) ∧ (∏ i ∈ range k, f i) ≤ n ∧
    (∀ i < k, (f i : ℝ) < (x : ℝ) ^ (35 / 100 : ℝ)) ∧
    (∃ i < k, ∃ r s : ℕ, f i = r * s ∧
      (x : ℝ) ^ ((100 * (k : ℝ))⁻¹) ≤ (r : ℝ) ∧
      (x : ℝ) ^ ((100 * (k : ℝ))⁻¹) ≤ (s : ℝ)))
  set E4 := S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i < k, f i ∣ (n - i) / g i) ∧
    (∃ i < k, ∃ j < k, i ≠ j ∧ 1 < f i ∧ 1 < f j) ∧
    n < 2 * (∏ i ∈ range k, f i) ∧ (∏ i ∈ range k, f i) ≤ n ∧
    (∀ i < k, (f i : ℝ) < (x : ℝ) ^ (35 / 100 : ℝ)) ∧
    (∀ i < k, ∀ r s : ℕ, f i = r * s →
      (r : ℝ) < (x : ℝ) ^ ((100 * (k : ℝ))⁻¹) ∨
      (s : ℝ) < (x : ℝ) ^ ((100 * (k : ℝ))⁻¹)))
  have hsub : E ⊆ ((E1 ∪ E2) ∪ E3) ∪ E4 := by
    intro n hn
    obtain ⟨hnS, f, hfdvd, hftwo, hfhi, hflo⟩ := Finset.mem_filter.mp hn
    by_cases hc1 : ∃ i < k, (x : ℝ) ^ (51 / 100 : ℝ) ≤ (f i : ℝ)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hnS, f, hfdvd, hftwo, hfhi, hflo, hc1⟩)))
    · push Not at hc1
      by_cases hc2 : ∃ i < k, (x : ℝ) ^ (35 / 100 : ℝ) ≤ (f i : ℝ)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hnS, f, hfdvd, hftwo, hfhi, hflo, hc1, hc2⟩)))
      · push Not at hc2
        by_cases hc3 : ∃ i < k, ∃ r s : ℕ, f i = r * s ∧
            (x : ℝ) ^ ((100 * (k : ℝ))⁻¹) ≤ (r : ℝ) ∧
            (x : ℝ) ^ ((100 * (k : ℝ))⁻¹) ≤ (s : ℝ)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hnS, f, hfdvd, hftwo, hfhi, hflo, hc2, hc3⟩))
        · push Not at hc3
          refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnS, f, hfdvd, hftwo, hfhi, hflo, hc2, ?_⟩)
          intro i hi r s hrs
          by_contra hnot
          push Not at hnot
          exact lt_irrefl _ (lt_of_le_of_lt hnot.2 (hc3 i hi r s hrs hnot.1))
  have hcard : E.card ≤ E1.card + E2.card + E3.card + E4.card := by
    calc E.card ≤ (((E1 ∪ E2) ∪ E3) ∪ E4).card := Finset.card_le_card hsub
      _ ≤ ((E1 ∪ E2) ∪ E3).card + E4.card := Finset.card_union_le _ _
      _ ≤ (E1 ∪ E2).card + E3.card + E4.card := by linarith [Finset.card_union_le (E1 ∪ E2) E3]
      _ ≤ E1.card + E2.card + E3.card + E4.card := by linarith [Finset.card_union_le E1 E2]
  have h1' : 40 * E1.card ≤ 9 * S.card := hx1
  have h2' : 40 * E2.card ≤ 9 * S.card := hx2
  have h3' : 40 * E3.card ≤ 9 * S.card := hx3
  have h4' : 40 * E4.card ≤ 9 * S.card := hx4
  omega

end OMA.R_Erdos387_erdos_387_variants_guy_R1_H3_R1
