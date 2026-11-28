import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1.R1 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1
-- Credit: @mijuny
-- Builds on the finite log-log descent formulation of @NicholasWierenga (lower.R1.H2.R1),
-- extending the descent conclusion from an eventual polylogarithmic bound to the full
-- uniform quasipolynomial bound for all N >= 3 with exponent 1 + eta = 1 / beta > 1.

/-!
# Uniform quasipolynomial density bound from subquadratic affine density increment

We reduce the uniform quasipolynomial bound (`N ≥ 3`, exponent `1 + η > 1`) of step
`lower.R2.H1.R1.H2.R1.H1` to the exact two hypotheses of reduction `lower.R1.H2.R1`:

* `H1`: sparse finite sets without `k`-term progressions admit an affine density increment
  preserving the subquadratic budget `C * p ^ β + R ≤ log (log N)` with `0 < β < 1`.
* `H2`: qualitative Szemerédi terminal step at fixed positive density (`p ≤ T`), already
  proved in `proofs/Erdos142.erdos_142.variants.lower.R1.H2.R1.H2.lean`.

From `H1` and `H2`, finite descent rules out `C * p ^ β + R ≤ log (log N)`. For
`log (log N)` above `max 1 (max (2 * R) (4 * C * 2 ^ β))`, inverting `C * p ^ β > log (log N) / 2`
yields `p > c * (log (log N)) ^ (1 + η)` with `1 + η = 1 / β > 1`, and bounded scales
`3 ≤ N` below that cutoff are absorbed into the leading constant `C'`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R1

open Filter Real
open scoped Topology

/-- Sparse finite sets admit an affine density increment preserving the log-log budget. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∃ (β C T R₀ : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (N : ℕ) (S : Finset ℕ),
        2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
          (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
        T < p → C * p ^ β + R ≤ Real.log (Real.log (N : ℝ)) →
          ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
            (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
            let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
            let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
            0 < U.card ∧ p' + 1 ≤ p ∧ C * p' ^ β + R ≤ Real.log (Real.log (M : ℝ))

/-- Fixed positive density forces a progression once the interval is long enough. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ T : ℝ, ∃ Q : ℝ, ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
    max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) ≤ T →
      Real.log (Real.log (N : ℝ)) < Q

lemma eliminate_descent {X : Type} (p : X → ℝ) (P : X → Prop)
    (hp : ∀ x, 0 ≤ p x)
    (decrease : ∀ x, P x → ∃ y, P y ∧ p y + 1 ≤ p x) :
    ∀ x, ¬ P x := by
  suffices H : ∀ n : ℕ, ∀ x, P x → ⌊p x⌋₊ = n → False from
    fun x hx ↦ H _ x hx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hx he
    obtain ⟨y, hy, hdrop⟩ := decrease x hx
    have hlt : ⌊p y⌋₊ < ⌊p x⌋₊ := (Nat.floor_lt (hp y)).mpr (by
      linarith [Nat.lt_floor_add_one (p x)])
    exact ih _ (by simpa only [he] using hlt) y hy rfl

lemma progression_preimage_free {k a q M : ℕ} {S : Finset ℕ}
    (hk : 4 ≤ k) (hq : 0 < q)
    (hfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k, b + i * d ∈ S) :
    ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k,
      b + i * d ∈ (Finset.Icc 1 M).filter (fun j ↦ a + (j - 1) * q ∈ S) := by
  rintro ⟨b, d, hd, hAP⟩
  have hbase : b ∈ Finset.Icc 1 M := by
    simpa only [zero_mul, add_zero] using (Finset.mem_filter.mp (hAP 0 (by omega))).1
  have hb : 1 ≤ b := (Finset.mem_Icc.mp hbase).1
  refine hfree ⟨a + (b - 1) * q, d * q, Nat.mul_pos hd hq, fun i hi ↦ ?_⟩
  have hmem := (Finset.mem_filter.mp (hAP i hi)).2
  have he : b + i * d - 1 = b - 1 + i * d := by omega
  rw [he] at hmem
  simpa only [add_mul, Nat.add_assoc, Nat.mul_assoc] using hmem

lemma no_budget (hdesc : H1) (hterm : H2) {k : ℕ} (hk : 4 ≤ k) :
    ∃ (β C R : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        ¬ C * (max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))) ^ β + R ≤
          Real.log (Real.log (N : ℝ)) := by
  obtain ⟨β, C, T, R₀, hβ, hβ1, hC, hstep⟩ := hdesc k hk
  obtain ⟨Q, hstop⟩ := hterm k hk T
  let R := max R₀ Q
  refine ⟨β, C, R, hβ, hβ1, hC, ?_⟩
  let X := ℕ × Finset ℕ
  let p (x : X) := max 2 (Real.log (2 * (x.1 : ℝ) / (x.2.card : ℝ)))
  let admissible (x : X) :=
    2 ≤ x.1 ∧ x.2 ⊆ Finset.Icc 1 x.1 ∧ 0 < x.2.card ∧
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ x.2) ∧
      C * (p x) ^ β + R ≤ Real.log (Real.log (x.1 : ℝ))
  have hp (x : X) : 0 ≤ p x := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  have decrease (x : X) (hx : admissible x) :
      ∃ y, admissible y ∧ p y + 1 ≤ p x := by
    obtain ⟨hN, hS, hcard, hfree, hbudget⟩ := hx
    have hlarge : T < p x := by
      by_contra! hsmall
      have hlt := hstop x.1 x.2 hN hS hcard hfree hsmall
      have hnonneg := mul_nonneg hC.le (Real.rpow_nonneg (hp x) β)
      have hQR : Q ≤ R := le_max_right _ _
      linarith
    obtain ⟨a, q, M, hq, hM, _, hcard', hdrop, hbudget'⟩ :=
      hstep R (le_max_left _ _) x.1 x.2 hN hS hcard hfree hlarge hbudget
    let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ x.2)
    refine ⟨(M, U), ⟨hM, Finset.filter_subset _ _, hcard', ?_, hbudget'⟩, hdrop⟩
    exact progression_preimage_free hk hq hfree
  intro N S hN hS hcard hfree hbudget
  exact eliminate_descent p admissible hp decrease (N, S) ⟨hN, hS, hcard, hfree, hbudget⟩

lemma log_log_pos_of_ge_three {N : ℕ} (hN : 3 ≤ N) :
    0 < Real.log (Real.log (N : ℝ)) := by
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexpN : Real.exp 1 < (N : ℝ) := lt_of_lt_of_le he h3
  have hlog1 : 1 < Real.log (N : ℝ) := by
    have := Real.log_lt_log (Real.exp_pos 1) hexpN
    rwa [Real.log_exp] at this
  exact Real.log_pos hlog1

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H1 := by
  intro hdesc hterm k hk
  obtain ⟨β, C, R, hβ, hβ1, hC, hno⟩ := no_budget hdesc hterm hk
  let η : ℝ := (1 - β) / β
  have hη : 0 < η := div_pos (sub_pos.mpr hβ1) hβ
  have h1η_pos : 0 < 1 + η := by linarith
  have hmul : β * (1 + η) = 1 := by
    dsimp [η]
    field_simp [hβ.ne']
    ring
  let c : ℝ := (1 / (2 * C)) ^ (1 + η)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) (1 + η)
  let L₀ : ℝ := max 1 (max (2 * R) (4 * C * (2 : ℝ) ^ β))
  have hL₀1 : 1 ≤ L₀ := le_max_left _ _
  have hL₀R : 2 * R ≤ L₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hL₀2 : 4 * C * (2 : ℝ) ^ β ≤ L₀ := (le_max_right _ _).trans (le_max_right _ _)
  let C' : ℝ := max 2 (Real.exp (c * L₀ ^ (1 + η)))
  have hC'2 : 2 ≤ C' := le_max_left _ _
  have hC'exp : Real.exp (c * L₀ ^ (1 + η)) ≤ C' := le_max_right _ _
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num) hC'2
  refine ⟨C', c, η, hC'pos, hc, hη, ?_⟩
  intro N S hN3 hS hfree
  by_cases hScard : S.card = 0
  · rw [hScard, Nat.cast_zero]
    positivity
  have hSpos : 0 < S.card := Nat.pos_of_ne_zero hScard
  have hSposR : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSpos
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let L : ℝ := Real.log (Real.log (N : ℝ))
  have hLpos : 0 < L := log_log_pos_of_ge_three hN3
  by_cases hsmall : L ≤ L₀
  · have hpow : L ^ (1 + η) ≤ L₀ ^ (1 + η) :=
      Real.rpow_le_rpow hLpos.le hsmall h1η_pos.le
    have hcmul : c * L ^ (1 + η) ≤ c * L₀ ^ (1 + η) :=
      mul_le_mul_of_nonneg_left hpow hc.le
    have hexp : Real.exp (-(c * L₀ ^ (1 + η))) ≤ Real.exp (-c * L ^ (1 + η)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hone : 1 ≤ C' * Real.exp (-c * L ^ (1 + η)) := by
      calc (1 : ℝ)
          = Real.exp (c * L₀ ^ (1 + η)) * Real.exp (-(c * L₀ ^ (1 + η))) := by
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        _ ≤ C' * Real.exp (-c * L ^ (1 + η)) :=
              mul_le_mul hC'exp hexp (Real.exp_pos _).le hC'pos.le
    have hcardN : (S.card : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast ((Finset.card_mono hS).trans_eq (Nat.card_Icc 1 N))
    calc (S.card : ℝ)
        ≤ (N : ℝ) * 1 := by linarith
      _ ≤ (N : ℝ) * (C' * Real.exp (-c * L ^ (1 + η))) :=
            mul_le_mul_of_nonneg_left hone hNposR.le
      _ = C' * (N : ℝ) * Real.exp (-c * L ^ (1 + η)) := by ring
  · have hsmall' : L₀ < L := lt_of_not_ge hsmall
    let q : ℝ := Real.log (2 * (N : ℝ) / (S.card : ℝ))
    let p : ℝ := max 2 q
    have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
    have hfail := hno N S (by omega) hS hSpos hfree
    have hgt : L < C * p ^ β + R := not_le.mp hfail
    have hhalf : L / 2 < C * p ^ β := by linarith
    have hdiv : L / (2 * C) < p ^ β := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have hp_gt2 : 2 < q := by
      by_contra! hq2
      have hp_eq2 : p = 2 := max_eq_left hq2
      rw [hp_eq2] at hhalf
      linarith
    have hp_eq : p = q := max_eq_right hp_gt2.le
    have hrpow : (L / (2 * C)) ^ (1 + η) < (p ^ β) ^ (1 + η) :=
      Real.rpow_lt_rpow (by positivity) hdiv h1η_pos
    have hlhs : (L / (2 * C)) ^ (1 + η) = c * L ^ (1 + η) := by
      have hrewrite : L / (2 * C) = (1 / (2 * C)) * L := by ring
      rw [hrewrite, Real.mul_rpow (by positivity) hLpos.le]
    have hrhs : (p ^ β) ^ (1 + η) = q := by
      rw [← Real.rpow_mul hp_pos.le, hmul, Real.rpow_one, hp_eq]
    rw [hlhs, hrhs] at hrpow
    have hratio_pos : 0 < 2 * (N : ℝ) / (S.card : ℝ) := by positivity
    have hexp_lt : Real.exp (c * L ^ (1 + η)) < 2 * (N : ℝ) / (S.card : ℝ) := by
      have h := Real.exp_lt_exp.mpr hrpow
      rwa [Real.exp_log hratio_pos] at h
    have hmul_lt : (S.card : ℝ) * Real.exp (c * L ^ (1 + η)) < 2 * (N : ℝ) := by
      linarith [(lt_div_iff₀ hSposR).mp hexp_lt]
    calc (S.card : ℝ)
        = ((S.card : ℝ) * Real.exp (c * L ^ (1 + η))) * Real.exp (-c * L ^ (1 + η)) := by
            rw [mul_assoc, ← Real.exp_add]
            have hcancel : c * L ^ (1 + η) + -c * L ^ (1 + η) = 0 := by ring
            rw [hcancel, Real.exp_zero, mul_one]
      _ ≤ (2 * (N : ℝ)) * Real.exp (-c * L ^ (1 + η)) :=
            mul_le_mul_of_nonneg_right hmul_lt.le (Real.exp_pos _).le
      _ ≤ (C' * (N : ℝ)) * Real.exp (-c * L ^ (1 + η)) := by
            gcongr
      _ = C' * (N : ℝ) * Real.exp (-c * L ^ (1 + η)) := by ring

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R1
