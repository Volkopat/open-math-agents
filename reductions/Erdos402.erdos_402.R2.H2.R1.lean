import OMAReductions.R_Erdos402_erdos_402_R2

/-! The medium-range method in Section 3 of Balasubramanian and
Soundararajan, On a conjecture of R. L. Graham, Acta Arithmetica 75 (1996).
The single square-gap inequality at the endpoint is equivalent to all
double-gap inequalities required by the prime-pair criterion. The
criterion itself is isolated from the finite prime-pair coverage and
the explicit analytic tail. -/

namespace OMA.R_Erdos402_erdos_402_R2_H2_R1

open Finset

/-- The endpoint of the interval is the strongest double-gap constraint. -/
theorem double_gap_iff_endpoint {N p : ℕ} (hpN : N < p) (hp₂ : p < 2 * N) :
    (∀ α ∈ Icc ((p + 1) / 2) N,
      (N - α)^2 < α ∧ p - α ≤ N ∧ (N - (p - α))^2 < p - α) ↔
    (2 * N - p)^2 < p - N := by
  constructor
  · intro hall
    have hN : N ∈ Icc ((p + 1) / 2) N := mem_Icc.mpr ⟨by omega, le_rfl⟩
    have eq : N - (p - N) = 2 * N - p := by omega
    simpa only [eq] using (hall N hN).2.2
  · intro gap α ha
    obtain ⟨alo, ahi⟩ := mem_Icc.mp ha
    have a₁ : p - N ≤ α := by omega
    have a₂ : p - N ≤ p - α := Nat.sub_le_sub_left ahi p
    have b₁ : N - α ≤ 2 * N - p := by omega
    have b₂ : N - (p - α) ≤ 2 * N - p := by omega
    refine ⟨?_, by omega, ?_⟩
    · exact (Nat.pow_le_pow_left b₁ 2).trans_lt (gap.trans_le a₁)
    · exact (Nat.pow_le_pow_left b₂ 2).trans_lt (gap.trans_le a₂)

/-- The medium-range prime pair, stated as a single strict square-gap test. -/
def H1 : Prop :=
  ∀ N : ℕ, 7001 ≤ N → N ≤ 2220000000000 → ¬N.Prime →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N < p ∧ p < 2 * N ∧
      3 * N ≤ 2 * p ∧ 3 < p - N ∧ q ∈ Icc (p - N) N ∧
      (2 * N - p)^2 < p - N

/-- The combinatorial prime-interval and double-gap criterion. -/
def H2 : Prop :=
  ∀ A : Finset ℕ, 0 ∉ A → A.gcd id = 1 → 10 ≤ A.card →
    ∀ p q : ℕ, p.Prime → A.card < p → p < 2 * A.card →
      3 * A.card ≤ 2 * p → 3 < p - A.card →
      (2 * A.card - p)^2 ≤ 4 * A.card →
      q.Prime → q ∈ Icc (p - A.card) A.card →
      (∀ α ∈ Icc ((p + 1) / 2) A.card,
        (A.card - α)^2 < α ∧ p - α ≤ A.card ∧
        (A.card - (p - α))^2 < p - α) →
      ∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a

/-- The explicit analytic tail for the normalized smooth core. -/
def H3 : Prop :=
  ∀ A : Finset ℕ, 0 ∉ A → A.gcd id = 1 →
    2220000000000 < A.card → ¬A.card.Prime →
    (¬ ∀ a ∈ A, Squarefree a) →
    (∀ a ∈ A, a ∣ (Finset.Ico 1 A.card).lcm id) →
    (∀ a ∈ A, ∀ p : ℕ, p.Prime → p ∣ a → 2 * p < A.card) →
    ∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a

theorem main : H1 → H2 → H3 → OMA.R_Erdos402_erdos_402_R2.H2 := by
  intro medium criterion tail A h₀ hg hcard hcomp hnotSq hlcm hsmall
  by_cases hfin : A.card ≤ 2220000000000
  · obtain ⟨p, q, hp, hq, hpN, hp₂, hthree, hqmin, hqI, hgap⟩ :=
      medium A.card hcard hfin hcomp
    have hwindow : (2 * A.card - p)^2 ≤ 4 * A.card :=
      hgap.le.trans (by omega)
    exact criterion A h₀ hg (by omega) p q hp hpN hp₂ hthree hqmin hwindow hq hqI
      ((double_gap_iff_endpoint hpN hp₂).mpr hgap)
  · exact tail A h₀ hg (by omega) hcomp hnotSq hlcm hsmall

end OMA.R_Erdos402_erdos_402_R2_H2_R1
