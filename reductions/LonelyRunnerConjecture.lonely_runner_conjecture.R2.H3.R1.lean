import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_R2
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.GCDMonoid.Finset

/-!
Reduction `LonelyRunnerConjecture.lonely_runner_conjecture.R2.H3.R1` of the open high-runner
frontier `R2.H3` (`k ≥ 10` moving integer runners, i.e., `n ≥ 11` total runners).

Unconditionally proved in-file for all `k ≥ 10` (without assuming smaller-runner induction):
1. Full small-divisor sieve (`∀ j ∈ [2, k + 1], ∃ i, j ∣ w i`).
2. First-harmonic multi-prime `p`-adic valuation concentration (`c = 1` Barajas-Serra lifting)
   across every odd prime `3 ≤ p ≤ k + 1`: at least one sub-maximal `p`-adic valuation layer has
   strictly more than `(p - 1) / 2` speeds.
3. Prime-denominator middle-band exclusion theorem: whenever `k + 1` is prime (`k ≥ 10` even),
   tuples having `k / 2` or `k / 2 + 1` multiples of `k + 1` are solved unconditionally, splitting
   the prime-denominator frontier across the excluded middle band into sparse `(k + 1)`-divisibility
   (`≤ k / 2 - 1` multiples, `H1`) and higher-power `(k + 1)^2` super-concentration (`≥ k / 2 + 2`
   multiples with `≥ k / 2 + 1` colliding at a positive valuation below the maximum, `H2`).
4. Second-harmonic `p`-adic valuation concentration (`c = 2` non-unit-seed lifting) across every
   prime `k + 1 < p ≤ 2 * k + 1` dividing at least one speed: either the top `p`-adic layer has
   more than `(p - 3) / 2` speeds or a sub-maximal `p`-adic layer has more than `(p - 1) / 4` speeds.

Remaining regimes:
- `H1`: Prime-denominator frontier (`Nat.Prime (k + 1)`) with sparse `(k + 1)`-divisibility
  (`≤ k / 2 - 1` multiples of `k + 1`) and full first/second-harmonic `p`-adic concentration.
- `H2`: Prime-denominator frontier (`Nat.Prime (k + 1)`) with higher `(k + 1)^2` super-concentration
  (`≥ k / 2 + 2` multiples of `k + 1`, `≥ k / 2 + 1` at a single positive valuation layer).
- `H3`: Composite-denominator frontier (`¬ Nat.Prime (k + 1)`) with full small-divisor and
  first/second-harmonic multi-prime `p`-adic concentration.

Credit: @paynebrowning
-/

namespace OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R2_H3_R1

-- Regime 1: Prime-denominator frontier (k + 1 prime) with sparse (k + 1)-divisibility
-- (at most k / 2 - 1 multiples of k + 1, after excluding the middle band {k / 2, k / 2 + 1}).
def H1 : Prop :=
  ∀ (k : ℕ), 10 ≤ k → Nat.Prime (k + 1) → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin k, (Finset.univ.erase i₀).gcd w = 1) →
    (∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → ∃ i : Fin k, j ∣ w i) →
    (Finset.univ.filter (fun i : Fin k => (k + 1) ∣ w i)).card ≤ k / 2 - 1 →
    (∀ p : ℕ, Nat.Prime p → 3 ≤ p → p ≤ k + 1 →
      ∃ j : ℕ, (∃ i_hi : Fin k, p ^ (j + 1) ∣ w i_hi) ∧
        (p - 1) / 2 < (Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i))).card) →
    (∀ p : ℕ, Nat.Prime p → k + 1 < p → p ≤ 2 * k + 1 → (∃ i : Fin k, p ∣ w i) →
      (∃ m : ℕ, 1 ≤ m ∧ (∀ i : Fin k, ¬ (p ^ (m + 1) ∣ w i)) ∧
        (p - 3) / 2 < (Finset.univ.filter (fun i : Fin k => p ^ m ∣ w i)).card) ∨
      (∃ j : ℕ, (∃ i_hi : Fin k, p ^ (j + 1) ∣ w i_hi) ∧
        (p - 1) / 4 < (Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i))).card)) →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
    (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd w) ≤
      (Nat.choose (k + 1) 2) ^ (k - 1) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

-- Regime 2: Prime-denominator frontier (k + 1 prime) with higher-power (k + 1)^2 super-concentration
-- (at least k / 2 + 2 multiples of k + 1 and >= k / 2 + 1 speeds at a single positive valuation layer).
def H2 : Prop :=
  ∀ (k : ℕ), 10 ≤ k → Nat.Prime (k + 1) → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin k, (Finset.univ.erase i₀).gcd w = 1) →
    (∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → ∃ i : Fin k, j ∣ w i) →
    k / 2 + 2 ≤ (Finset.univ.filter (fun i : Fin k => (k + 1) ∣ w i)).card →
    (∃ j : ℕ, 1 ≤ j ∧ (∃ i_hi : Fin k, (k + 1) ^ (j + 1) ∣ w i_hi) ∧
      k / 2 + 1 ≤
        (Finset.univ.filter (fun i : Fin k => (k + 1) ^ j ∣ w i ∧ ¬ ((k + 1) ^ (j + 1) ∣ w i))).card) →
    (∀ p : ℕ, Nat.Prime p → 3 ≤ p → p ≤ k + 1 →
      ∃ j : ℕ, (∃ i_hi : Fin k, p ^ (j + 1) ∣ w i_hi) ∧
        (p - 1) / 2 < (Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i))).card) →
    (∀ p : ℕ, Nat.Prime p → k + 1 < p → p ≤ 2 * k + 1 → (∃ i : Fin k, p ∣ w i) →
      (∃ m : ℕ, 1 ≤ m ∧ (∀ i : Fin k, ¬ (p ^ (m + 1) ∣ w i)) ∧
        (p - 3) / 2 < (Finset.univ.filter (fun i : Fin k => p ^ m ∣ w i)).card) ∨
      (∃ j : ℕ, (∃ i_hi : Fin k, p ^ (j + 1) ∣ w i_hi) ∧
        (p - 1) / 4 < (Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i))).card)) →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
    (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd w) ≤
      (Nat.choose (k + 1) 2) ^ (k - 1) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

-- Regime 3: Composite-denominator frontier (k + 1 composite) equipped with small-divisor and
-- first/second-harmonic multi-prime p-adic concentration invariants.
def H3 : Prop :=
  ∀ (k : ℕ), 10 ≤ k → ¬ Nat.Prime (k + 1) → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin k, (Finset.univ.erase i₀).gcd w = 1) →
    (∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → ∃ i : Fin k, j ∣ w i) →
    (∀ p : ℕ, Nat.Prime p → 3 ≤ p → p ≤ k + 1 →
      ∃ j : ℕ, (∃ i_hi : Fin k, p ^ (j + 1) ∣ w i_hi) ∧
        (p - 1) / 2 < (Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i))).card) →
    (∀ p : ℕ, Nat.Prime p → k + 1 < p → p ≤ 2 * k + 1 → (∃ i : Fin k, p ∣ w i) →
      (∃ m : ℕ, 1 ≤ m ∧ (∀ i : Fin k, ¬ (p ^ (m + 1) ∣ w i)) ∧
        (p - 3) / 2 < (Finset.univ.filter (fun i : Fin k => p ^ m ∣ w i)).card) ∨
      (∃ j : ℕ, (∃ i_hi : Fin k, p ^ (j + 1) ∣ w i_hi) ∧
        (p - 1) / 4 < (Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i))).card)) →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
    (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd w) ≤
      (Nat.choose (k + 1) 2) ^ (k - 1) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

section ReductionProofs

noncomputable section

/- ### Module 1: UnitAddCircle Distance & Small-Divisor Sieve -/

private lemma unitAddCircle_dist_ge_of_Icc (x δ : ℝ) (k : ℤ)
    (h1 : (k : ℝ) + δ ≤ x) (h2 : x ≤ (k : ℝ) + 1 - δ) :
    dist (x : UnitAddCircle) 0 ≥ δ := by
  rw [ge_iff_le, dist_zero_right, UnitAddCircle.norm_eq]
  set m : ℤ := round x
  rcases le_or_gt m k with hmk | hkm
  · have hmk' : (m : ℝ) ≤ (k : ℝ) := Int.cast_le.mpr hmk
    have hle : δ ≤ x - (m : ℝ) := by linarith
    exact hle.trans (le_abs_self _)
  · have hkm1 : k + 1 ≤ m := Int.add_one_le_iff.mpr hkm
    have hkm' : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hkm1
    have hle : δ ≤ -(x - (m : ℝ)) := by linarith
    exact hle.trans (neg_le_abs _)

private lemma unitAddCircle_dist_ge_of_mod_Icc {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (lam w : ℕ) (hlo : N ≤ p * ((lam * w) % N)) (hhi : p * ((lam * w) % N) ≤ (p - 1) * N) :
    dist (((((lam : ℝ) / (N : ℝ)) * (w : ℝ) : ℝ)) : UnitAddCircle) 0 ≥ 1 / (p : ℝ) := by
  let q_nat : ℕ := (lam * w) / N
  let r_nat : ℕ := (lam * w) % N
  have hdiv : N * q_nat + r_nat = lam * w := Nat.div_add_mod (lam * w) N
  have hdiv_real : (N : ℝ) * (q_nat : ℝ) + (r_nat : ℝ) = (lam : ℝ) * (w : ℝ) := by
    exact_mod_cast hdiv
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hx_eq : ((lam : ℝ) / (N : ℝ)) * (w : ℝ) = ((q_nat : ℤ) : ℝ) + (r_nat : ℝ) / (N : ℝ) := by
    push_cast
    field_simp [ne_of_gt hN_pos]
    linarith
  have hlo_real : (N : ℝ) ≤ (p : ℝ) * (r_nat : ℝ) := by exact_mod_cast hlo
  have hhi_real : (p : ℝ) * (r_nat : ℝ) ≤ ((p - 1 : ℕ) : ℝ) * (N : ℝ) := by exact_mod_cast hhi
  have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hp1] at hhi_real
  refine unitAddCircle_dist_ge_of_Icc _ (1 / (p : ℝ)) (q_nat : ℤ) ?_ ?_
  · rw [hx_eq]
    have h1 : 1 / (p : ℝ) ≤ (r_nat : ℝ) / (N : ℝ) := by
      rw [div_le_div_iff₀ hp_pos hN_pos]; linarith
    linarith
  · rw [hx_eq]
    have h2 : (r_nat : ℝ) / (N : ℝ) ≤ 1 - 1 / (p : ℝ) := by
      have hsub : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by field_simp [ne_of_gt hp_pos]
      rw [hsub, div_le_div_iff₀ hN_pos hp_pos]; linarith
    linarith

private lemma lrc_small_divisor_sieve {k j : ℕ} (hj2 : 2 ≤ j) (hjk : j ≤ k + 1)
    (w : Fin k → ℕ) (hnot_dvd : ∀ i : Fin k, ¬ (j ∣ w i)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  refine ⟨1 / (j : ℝ), by positivity, fun i => ?_⟩
  have hmod_ne : (1 * w i) % j ≠ 0 := by
    rw [one_mul]; intro h0; exact hnot_dvd i (Nat.dvd_of_mod_eq_zero h0)
  have hmod_ge : 1 ≤ (1 * w i) % j := Nat.one_le_iff_ne_zero.mpr hmod_ne
  have hmod_lt : (1 * w i) % j < j := Nat.mod_lt _ (by omega)
  have hmod_le : (1 * w i) % j ≤ j - 1 := by omega
  have hdist_j : dist ((((1 : ℝ) / (j : ℝ)) * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / (j : ℝ) := by
    simpa [Nat.cast_one] using
      unitAddCircle_dist_ge_of_mod_Icc (N := j) (p := j) (by omega) hj2 1 (w i)
        (by nlinarith) (by nlinarith)
  have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
  have hjk_real : (j : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hjk
  exact le_trans (one_div_le_one_div_of_le hj_pos hjk_real) hdist_j

/- ### Module 2: Valuation Characterization & First-Harmonic (`c = 1`) `p`-adic Lifting -/

private lemma exists_pow_mul_not_dvd {p : ℕ} (hp : 2 ≤ p) :
    ∀ n : ℕ, 0 < n → ∃ e u : ℕ, 0 < u ∧ ¬ (p ∣ u) ∧ n = p ^ e * u := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hdvd : p ∣ n
    · obtain ⟨m, hm⟩ := hdvd
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hm; omega
        · exact hpos
      have hm_lt : m < n := by nlinarith
      obtain ⟨e, u, hu_pos, hnot, hmu⟩ := ih m hm_lt hm_pos
      refine ⟨e + 1, u, hu_pos, hnot, ?_⟩
      rw [hm, hmu, pow_succ]; ring
    · exact ⟨0, n, hn, hdvd, by simp⟩

private lemma pow_dvd_pow_mul_iff {p e u j : ℕ} (hp : Nat.Prime p) (hu : ¬ (p ∣ u)) :
    p ^ j ∣ p ^ e * u ↔ j ≤ e := by
  constructor
  · intro hdvd
    by_contra hlt
    have hsplit : j = e + (j - e) := by omega
    rw [hsplit, pow_add] at hdvd
    have hdvd_u : p ^ (j - e) ∣ u :=
      (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos e)).mp (by simpa [mul_assoc] using hdvd)
    have hp_dvd_pow : p ∣ p ^ (j - e) := dvd_pow_self p (by omega)
    exact hu (dvd_trans hp_dvd_pow hdvd_u)
  · intro hle
    exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow p hle) u

private lemma exact_pow_dvd_iff_eq {p e u j : ℕ} (hp : Nat.Prime p) (hu : ¬ (p ∣ u)) :
    (p ^ j ∣ p ^ e * u ∧ ¬ (p ^ (j + 1) ∣ p ^ e * u)) ↔ e = j := by
  rw [pow_dvd_pow_mul_iff hp hu, pow_dvd_pow_mul_iff hp hu]
  omega

private lemma div_pow_mod_pow_succ {p m : ℕ} (hp : 2 ≤ p) (a s : ℕ) (hs : s < p ^ m) :
    ((a * p ^ m + s) % p ^ (m + 1)) / p ^ m = a % p := by
  have hpm_pos : 0 < p ^ m := pow_pos (by omega) m
  have ha_eq : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
  have hlt : (a % p) * p ^ m + s < p ^ (m + 1) := by
    have hap : a % p ≤ p - 1 := by have := Nat.mod_lt a (by omega : 0 < p); omega
    calc
      (a % p) * p ^ m + s ≤ (p - 1) * p ^ m + s :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hap) s
      _ < (p - 1) * p ^ m + p ^ m := Nat.add_lt_add_left hs _
      _ = p ^ (m + 1) := by
        rw [pow_succ']
        cases p with
        | zero => omega
        | succ p' => simp [Nat.succ_mul]
  have hrew : a * p ^ m + s = ((a % p) * p ^ m + s) + p ^ (m + 1) * (a / p) := by
    conv_lhs => rw [ha_eq]
    rw [pow_succ']; ring
  rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpm_pos, Nat.div_eq_of_lt hs, zero_add]

private lemma add_mul_mod_inj {p : ℕ} (hp : Nat.Prime p) {q₀ b : ℕ} (hb : ¬ (p ∣ b)) :
    Function.Injective (fun x : Fin p => (q₀ + x.val * b) % p) := by
  intro x₁ x₂ heq
  by_contra hne
  have hval_ne : x₁.val ≠ x₂.val := fun hv => hne (Fin.ext hv)
  have hcop : Nat.Coprime p b := hp.coprime_iff_not_dvd.mpr hb
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · have hle : q₀ + x₁.val * b ≤ q₀ + x₂.val * b :=
      Nat.add_le_add_left (Nat.mul_le_mul_right b hlt.le) q₀
    have hdvd1 : p ∣ (q₀ + x₂.val * b) - (q₀ + x₁.val * b) :=
      (Nat.modEq_iff_dvd' hle).mp heq
    have hsub : (q₀ + x₂.val * b) - (q₀ + x₁.val * b) = (x₂.val - x₁.val) * b := by
      rw [Nat.add_sub_add_left, ← Nat.sub_mul]
    rw [hsub] at hdvd1
    have := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_right hdvd1)
    omega
  · have hle : q₀ + x₂.val * b ≤ q₀ + x₁.val * b :=
      Nat.add_le_add_left (Nat.mul_le_mul_right b hgt.le) q₀
    have hdvd1 : p ∣ (q₀ + x₁.val * b) - (q₀ + x₂.val * b) :=
      (Nat.modEq_iff_dvd' hle).mp heq.symm
    have hsub : (q₀ + x₁.val * b) - (q₀ + x₂.val * b) = (x₁.val - x₂.val) * b := by
      rw [Nat.add_sub_add_left, ← Nat.sub_mul]
    rw [hsub] at hdvd1
    have := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_right hdvd1)
    omega

private lemma card_filter_eq_le_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) {f : α → β} (hf : Function.Injective f) (y : β) :
    (s.filter (fun x => f x = y)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  exact hf (ha.2.trans hb.2.symm)

private theorem prime_filtering_step {k p m : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hm : 1 ≤ m)
    (e u : Fin k → ℕ) (hu_not : ∀ i, ¬ (p ∣ u i))
    (hlevel : ∀ j < m, (Finset.univ.filter (fun i : Fin k => e i = j)).card ≤ (p - 1) / 2) :
    ∀ t ≤ m, ∃ lam : ℕ, ¬ (p ∣ lam) ∧
      ∀ i : Fin k, m - t ≤ e i → e i < m →
        1 ≤ ((lam * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m ∧
        ((lam * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m ≤ p - 2 := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨1, ?_, fun i hge hlt => by omega⟩
    intro hdvd; have := Nat.le_of_dvd zero_lt_one hdvd; omega
  | succ t ih =>
    intro ht_le
    obtain ⟨lam₀, hlam₀, hprev⟩ := ih (by omega)
    let j : ℕ := m - (t + 1)
    have hj_lt : j < m := by omega
    let Sj : Finset (Fin k) := Finset.univ.filter (fun i => e i = j)
    let f_digit : Fin k → Fin p → ℕ :=
      fun i x => (((lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m
    have hdigit_formula : ∀ i ∈ Sj, ∀ x : Fin p,
        f_digit i x = ((((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m) +
          x.val * (lam₀ * u i)) % p := by
      intro i hi x
      have hei : e i = j := (Finset.mem_filter.mp hi).2
      dsimp [f_digit]; rw [hei]
      let q₀ : ℕ := ((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m
      let s₀ : ℕ := ((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) % p ^ m
      have hs₀_lt : s₀ < p ^ m := Nat.mod_lt _ (pow_pos (by omega) m)
      have hrem_decomp : (lam₀ * (p ^ j * u i)) % p ^ (m + 1) = q₀ * p ^ m + s₀ := by
        dsimp only [q₀, s₀]; rw [mul_comm _ (p ^ m), Nat.div_add_mod]
      have hpow_add : p ^ (m - j) * p ^ j = p ^ m := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt hj_lt)]
      have hexpand : (lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ j * u i) =
          lam₀ * (p ^ j * u i) + (x.val * (lam₀ * u i)) * p ^ m := by
        calc
          (lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ j * u i)
            = lam₀ * (p ^ j * u i) + (x.val * (lam₀ * u i)) * (p ^ (m - j) * p ^ j) := by ring
          _ = lam₀ * (p ^ j * u i) + (x.val * (lam₀ * u i)) * p ^ m := by rw [hpow_add]
      have hmod_N : ((lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ j * u i)) % p ^ (m + 1) =
          ((q₀ + x.val * (lam₀ * u i)) * p ^ m + s₀) % p ^ (m + 1) := by
        rw [hexpand]
        conv_lhs => rw [← Nat.div_add_mod (lam₀ * (p ^ j * u i)) (p ^ (m + 1)), hrem_decomp]
        have hring : p ^ (m + 1) * (lam₀ * (p ^ j * u i) / p ^ (m + 1)) + (q₀ * p ^ m + s₀) +
            x.val * (lam₀ * u i) * p ^ m =
            ((q₀ + x.val * (lam₀ * u i)) * p ^ m + s₀) +
            p ^ (m + 1) * (lam₀ * (p ^ j * u i) / p ^ (m + 1)) := by ring
        rw [hring, Nat.add_mul_mod_self_left]
      rw [hmod_N]
      exact div_pow_mod_pow_succ (by omega) (q₀ + x.val * (lam₀ * u i)) s₀ hs₀_lt
    let badFor : Fin k → Finset (Fin p) :=
      fun i => Finset.univ.filter (fun x : Fin p => f_digit i x = 0 ∨ f_digit i x = p - 1)
    have hbad_card : ∀ i ∈ Sj, (badFor i).card ≤ 2 := by
      intro i hi
      have hb_not : ¬ (p ∣ lam₀ * u i) := fun hdvd =>
        (hp.dvd_mul.mp hdvd).elim hlam₀ (hu_not i)
      let g : Fin p → ℕ :=
        fun x => ((((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m) + x.val * (lam₀ * u i)) % p
      have hg_inj : Function.Injective g := add_mul_mod_inj hp hb_not
      have hsub : badFor i ⊆
          (Finset.univ.filter (fun x => g x = 0)) ∪ (Finset.univ.filter (fun x => g x = p - 1)) := by
        intro x hx; rw [Finset.mem_filter] at hx; rw [hdigit_formula i hi x] at hx
        rcases hx.2 with h0 | hp1
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h0⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hp1⟩)
      calc
        (badFor i).card ≤ ((Finset.univ.filter (fun x => g x = 0)) ∪
            (Finset.univ.filter (fun x => g x = p - 1))).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun x => g x = 0)).card +
            (Finset.univ.filter (fun x => g x = p - 1)).card := Finset.card_union_le _ _
        _ ≤ 1 + 1 := Nat.add_le_add (card_filter_eq_le_one _ hg_inj 0)
            (card_filter_eq_le_one _ hg_inj (p - 1))
        _ = 2 := rfl
    let allBad : Finset (Fin p) := Sj.biUnion badFor
    have hallBad_lt : allBad.card < p := by
      calc
        allBad.card ≤ ∑ i ∈ Sj, (badFor i).card := Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ Sj, 2 := Finset.sum_le_sum hbad_card
        _ = 2 * Sj.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * ((p - 1) / 2) := Nat.mul_le_mul_left 2 (hlevel j hj_lt)
        _ ≤ p - 1 := Nat.mul_div_le (p - 1) 2
        _ < p := by omega
    have hexists_good : (Finset.univ \ allBad).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro hemp
      have hcard := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)
      rw [Finset.card_fin] at hcard; omega
    obtain ⟨x₀, hx₀⟩ := hexists_good
    have hx₀_not_bad : x₀ ∉ allBad := (Finset.mem_sdiff.mp hx₀).2
    let lam : ℕ := lam₀ * (1 + x₀.val * p ^ (m - j))
    have hlam_not : ¬ (p ∣ lam) := by
      intro hdvd
      rcases hp.dvd_mul.mp hdvd with h1 | h2
      · exact hlam₀ h1
      · have hdvd_pow : p ∣ x₀.val * p ^ (m - j) :=
          dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) x₀.val
        have := Nat.le_of_dvd zero_lt_one ((Nat.dvd_add_left hdvd_pow).mp h2)
        omega
    refine ⟨lam, hlam_not, fun i hge hlt => ?_⟩
    rcases eq_or_lt_of_le hge with hei_eq | hei_gt
    · have hi_mem : i ∈ Sj := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hei_eq.symm⟩
      have hx_not_i : x₀ ∉ badFor i := fun h => hx₀_not_bad (Finset.mem_biUnion.mpr ⟨i, hi_mem, h⟩)
      have hnot_or : ¬ (f_digit i x₀ = 0 ∨ f_digit i x₀ = p - 1) :=
        fun hor => hx_not_i (Finset.mem_filter.mpr ⟨Finset.mem_univ x₀, hor⟩)
      have hlt_p : f_digit i x₀ < p := by
        dsimp [f_digit]
        have hlt_N := Nat.mod_lt ((lam₀ * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i))
          (pow_pos (by omega : 0 < p) (m + 1))
        rw [pow_succ] at hlt_N; exact Nat.div_lt_of_lt_mul hlt_N
      change 1 ≤ f_digit i x₀ ∧ f_digit i x₀ ≤ p - 2; omega
    · have hmod_same : (lam * (p ^ (e i) * u i)) % p ^ (m + 1) =
          (lam₀ * (p ^ (e i) * u i)) % p ^ (m + 1) := by
        dsimp [lam]
        have he_split : m - j + e i = (m + 1) + (e i - (j + 1)) := by omega
        have hexp : (lam₀ * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i) =
            lam₀ * (p ^ (e i) * u i) +
            p ^ (m + 1) * (lam₀ * x₀.val * u i * p ^ (e i - (j + 1))) := by
          calc
            (lam₀ * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i)
              = lam₀ * (p ^ (e i) * u i) +
                (lam₀ * x₀.val * u i) * (p ^ (m - j) * p ^ (e i)) := by ring
            _ = lam₀ * (p ^ (e i) * u i) +
                (lam₀ * x₀.val * u i) * p ^ ((m + 1) + (e i - (j + 1))) := by
                  rw [← pow_add, he_split]
            _ = lam₀ * (p ^ (e i) * u i) +
                p ^ (m + 1) * (lam₀ * x₀.val * u i * p ^ (e i - (j + 1))) := by
                  rw [pow_add]; ring
        rw [hexp, Nat.add_mul_mod_self_left]
      rw [hmod_same]; exact hprev i (by omega) hlt

private theorem prime_filtering_finish {k p m : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (w e u : Fin k → ℕ) (hu_not : ∀ i, ¬ (p ∣ u i))
    (hw_decomp : ∀ i, w i = p ^ (e i) * u i) (he_le : ∀ i, e i ≤ m)
    (lam : ℕ) (hlam_not : ¬ (p ∣ lam))
    (hdigits : ∀ i : Fin k, e i < m →
      1 ≤ ((lam * w i) % p ^ (m + 1)) / p ^ m ∧
      ((lam * w i) % p ^ (m + 1)) / p ^ m ≤ p - 2) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / (p : ℝ) := by
  let N : ℕ := p ^ (m + 1)
  have hN_pos : 0 < N := pow_pos (by omega) (m + 1)
  refine ⟨(lam : ℝ) / (N : ℝ), by positivity, fun i => ?_⟩
  rcases lt_or_eq_of_le (he_le i) with hlt | heq
  · obtain ⟨hq_lo, hq_hi⟩ := hdigits i hlt
    let q_i : ℕ := ((lam * w i) % N) / p ^ m
    let s_i : ℕ := ((lam * w i) % N) % p ^ m
    have hq_lo' : 1 ≤ q_i := hq_lo
    have hq_hi' : q_i ≤ p - 2 := hq_hi
    have hs_lt : s_i < p ^ m := Nat.mod_lt _ (pow_pos (by omega) m)
    have hrem_eq : (lam * w i) % N = p ^ m * q_i + s_i :=
      (Nat.div_add_mod ((lam * w i) % N) (p ^ m)).symm
    have hN_eq : N = p * p ^ m := pow_succ' p m
    have hlo : N ≤ p * ((lam * w i) % N) := by
      rw [hrem_eq, hN_eq]
      have : p ^ m ≤ p ^ m * q_i := Nat.le_mul_of_pos_right _ (by omega)
      nlinarith
    have hhi : p * ((lam * w i) % N) ≤ (p - 1) * N := by
      rw [hrem_eq, hN_eq]
      have hmul : p ^ m * q_i ≤ p ^ m * (p - 2) := Nat.mul_le_mul_left _ hq_hi'
      have hpm_pos : 0 < p ^ m := pow_pos (by omega) m
      have hsub : p - 1 = (p - 2) + 1 := by omega
      have h2 : p ^ m * (p - 2) + (p ^ m - 1) < p ^ m * (p - 1) := by
        rw [hsub, Nat.mul_add, Nat.mul_one]; omega
      have h3 : p ^ m * q_i + s_i ≤ p ^ m * (p - 1) := by omega
      nlinarith
    exact unitAddCircle_dist_ge_of_mod_Icc hN_pos (by omega) lam (w i) hlo hhi
  · have hwi : w i = p ^ m * u i := by rw [hw_decomp i, heq]
    have hprod_not : ¬ (p ∣ lam * u i) := fun hdvd =>
      (hp.dvd_mul.mp hdvd).elim hlam_not (hu_not i)
    let r_u : ℕ := (lam * u i) % p
    have hru_ge : 1 ≤ r_u :=
      Nat.one_le_iff_ne_zero.mpr (fun h0 => hprod_not (Nat.dvd_of_mod_eq_zero h0))
    have hru_lt : r_u < p := Nat.mod_lt _ (by omega)
    have hru_le : r_u ≤ p - 1 := by omega
    have hmod_eq : (lam * w i) % N = r_u * p ^ m := by
      dsimp [N]; rw [hwi]
      have hdiv := (Nat.div_add_mod (lam * u i) p).symm
      have hrew : lam * (p ^ m * u i) = r_u * p ^ m + p ^ (m + 1) * ((lam * u i) / p) := by
        calc lam * (p ^ m * u i) = (lam * u i) * p ^ m := by ring
          _ = (p * ((lam * u i) / p) + r_u) * p ^ m := by rw [← hdiv]
          _ = r_u * p ^ m + p ^ (m + 1) * ((lam * u i) / p) := by rw [pow_succ']; ring
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
      rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_right hru_lt (pow_pos (by omega) m)
    have hN_eq : N = p * p ^ m := pow_succ' p m
    exact unitAddCircle_dist_ge_of_mod_Icc hN_pos (by omega) lam (w i)
      (by rw [hmod_eq, hN_eq]; nlinarith [pow_pos (by omega : 0 < p) m])
      (by rw [hmod_eq, hN_eq]; nlinarith [pow_pos (by omega : 0 < p) m])

private theorem first_harmonic_padic_sieve {k p : ℕ} (hk : 1 ≤ k) (hp : Nat.Prime p)
    (hp3 : 3 ≤ p) (hpk : p ≤ k + 1) (w : Fin k → ℕ) (hw : ∀ i, 0 < w i)
    (hdvd_p : ∃ i : Fin k, p ∣ w i)
    (h_no_conc : ¬ ∃ j : ℕ, (∃ i_hi : Fin k, p ^ (j + 1) ∣ w i_hi) ∧
      (p - 1) / 2 < (Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i))).card) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  have hex := fun i => exists_pow_mul_not_dvd hp.two_le (w i) (hw i)
  let e : Fin k → ℕ := fun i => Classical.choose (hex i)
  let u : Fin k → ℕ := fun i => Classical.choose (Classical.choose_spec (hex i))
  have hu_spec : ∀ i, 0 < u i ∧ ¬ (p ∣ u i) ∧ w i = p ^ (e i) * u i :=
    fun i => Classical.choose_spec (Classical.choose_spec (hex i))
  have hu_not : ∀ i, ¬ (p ∣ u i) := fun i => (hu_spec i).2.1
  have hw_decomp : ∀ i, w i = p ^ (e i) * u i := fun i => (hu_spec i).2.2
  let m : ℕ := Finset.univ.sup e
  have he_le : ∀ i, e i ≤ m := fun i => Finset.le_sup (Finset.mem_univ i)
  have hm_ge : 1 ≤ m := by
    obtain ⟨i₀, hi₀⟩ := hdvd_p
    have he_pos : 1 ≤ e i₀ := by
      rcases Nat.eq_zero_or_pos (e i₀) with h0 | hpos
      · exfalso; rw [hw_decomp i₀, h0, pow_zero, one_mul] at hi₀; exact hu_not i₀ hi₀
      · exact hpos
    exact le_trans he_pos (he_le i₀)
  obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ e ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have he_max : e i_max = m :=
    le_antisymm (he_le i_max) (Finset.sup_le fun i _ => hi_max i (Finset.mem_univ i))
  have hlevel : ∀ j < m, (Finset.univ.filter (fun i : Fin k => e i = j)).card ≤ (p - 1) / 2 := by
    intro j hj_lt
    have hi_hi : p ^ (j + 1) ∣ w i_max := by
      rw [hw_decomp i_max, pow_dvd_pow_mul_iff hp (hu_not i_max)]; omega
    have hfilt_eq : Finset.univ.filter (fun i : Fin k => e i = j) =
        Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hw_decomp i, exact_pow_dvd_iff_eq hp (hu_not i)]
    rw [hfilt_eq]
    by_contra hgt
    exact h_no_conc ⟨j, ⟨i_max, hi_hi⟩, Nat.lt_of_not_le hgt⟩
  obtain ⟨lam, hlam_not, hstep⟩ := prime_filtering_step hp hp3 hm_ge e u hu_not hlevel m le_rfl
  obtain ⟨t, ht0, ht⟩ := prime_filtering_finish hp hp3 w e u hu_not hw_decomp he_le lam hlam_not
    (fun i hlt => by rw [hw_decomp i]; exact hstep i (by omega) hlt)
  refine ⟨t, ht0, fun i => ?_⟩
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hpk_r : (p : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hpk
  exact le_trans (one_div_le_one_div_of_le hp_pos hpk_r) (ht i)

/- ### Module 3: Second-Harmonic (`c = 2`) Non-Unit-Seed `p`-adic Lifting -/

private theorem second_harmonic_filtering_step {k p m lam₀ : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hm : 1 ≤ m) (hlam₀_not : ¬ (p ∣ lam₀))
    (e u : Fin k → ℕ) (hu_not : ∀ i, ¬ (p ∣ u i))
    (hlevel : ∀ j < m, (Finset.univ.filter (fun i : Fin k => e i = j)).card ≤ (p - 1) / 4) :
    ∀ t ≤ m, ∃ lam : ℕ, ¬ (p ∣ lam) ∧ lam % p = lam₀ % p ∧
      ∀ i : Fin k, m - t ≤ e i → e i < m →
        2 ≤ ((lam * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m ∧
        ((lam * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m ≤ p - 3 := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨lam₀, hlam₀_not, rfl, fun i hge hlt => by omega⟩
  | succ t ih =>
    intro ht_le
    obtain ⟨lam_prev, hlam_prev, hmod_prev, hprev⟩ := ih (by omega)
    let j : ℕ := m - (t + 1)
    have hj_lt : j < m := by omega
    let Sj : Finset (Fin k) := Finset.univ.filter (fun i => e i = j)
    let f_digit : Fin k → Fin p → ℕ :=
      fun i x => (((lam_prev * (1 + x.val * p ^ (m - j))) * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m
    have hdigit_formula : ∀ i ∈ Sj, ∀ x : Fin p,
        f_digit i x = ((((lam_prev * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m) +
          x.val * (lam_prev * u i)) % p := by
      intro i hi x
      have hei : e i = j := (Finset.mem_filter.mp hi).2
      dsimp [f_digit]; rw [hei]
      let q₀ : ℕ := ((lam_prev * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m
      let s₀ : ℕ := ((lam_prev * (p ^ j * u i)) % p ^ (m + 1)) % p ^ m
      have hs₀_lt : s₀ < p ^ m := Nat.mod_lt _ (pow_pos (by omega) m)
      have hrem_decomp : (lam_prev * (p ^ j * u i)) % p ^ (m + 1) = q₀ * p ^ m + s₀ := by
        dsimp only [q₀, s₀]; rw [mul_comm _ (p ^ m), Nat.div_add_mod]
      have hpow_add : p ^ (m - j) * p ^ j = p ^ m := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt hj_lt)]
      have hexpand : (lam_prev * (1 + x.val * p ^ (m - j))) * (p ^ j * u i) =
          lam_prev * (p ^ j * u i) + (x.val * (lam_prev * u i)) * p ^ m := by
        calc
          (lam_prev * (1 + x.val * p ^ (m - j))) * (p ^ j * u i)
            = lam_prev * (p ^ j * u i) + (x.val * (lam_prev * u i)) * (p ^ (m - j) * p ^ j) := by ring
          _ = lam_prev * (p ^ j * u i) + (x.val * (lam_prev * u i)) * p ^ m := by rw [hpow_add]
      have hmod_N : ((lam_prev * (1 + x.val * p ^ (m - j))) * (p ^ j * u i)) % p ^ (m + 1) =
          ((q₀ + x.val * (lam_prev * u i)) * p ^ m + s₀) % p ^ (m + 1) := by
        rw [hexpand]
        conv_lhs => rw [← Nat.div_add_mod (lam_prev * (p ^ j * u i)) (p ^ (m + 1)), hrem_decomp]
        have hring : p ^ (m + 1) * (lam_prev * (p ^ j * u i) / p ^ (m + 1)) + (q₀ * p ^ m + s₀) +
            x.val * (lam_prev * u i) * p ^ m =
            ((q₀ + x.val * (lam_prev * u i)) * p ^ m + s₀) +
            p ^ (m + 1) * (lam_prev * (p ^ j * u i) / p ^ (m + 1)) := by ring
        rw [hring, Nat.add_mul_mod_self_left]
      rw [hmod_N]
      exact div_pow_mod_pow_succ (by omega) (q₀ + x.val * (lam_prev * u i)) s₀ hs₀_lt
    let badFor : Fin k → Finset (Fin p) :=
      fun i => Finset.univ.filter (fun x : Fin p =>
        f_digit i x = 0 ∨ f_digit i x = 1 ∨ f_digit i x = p - 2 ∨ f_digit i x = p - 1)
    have hbad_card : ∀ i ∈ Sj, (badFor i).card ≤ 4 := by
      intro i hi
      have hb_not : ¬ (p ∣ lam_prev * u i) := fun hdvd =>
        (hp.dvd_mul.mp hdvd).elim hlam_prev (hu_not i)
      let g : Fin p → ℕ :=
        fun x => ((((lam_prev * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m) + x.val * (lam_prev * u i)) % p
      have hg_inj : Function.Injective g := add_mul_mod_inj hp hb_not
      let F0 := Finset.univ.filter (fun x : Fin p => g x = 0)
      let F1 := Finset.univ.filter (fun x : Fin p => g x = 1)
      let F2 := Finset.univ.filter (fun x : Fin p => g x = p - 2)
      let F3 := Finset.univ.filter (fun x : Fin p => g x = p - 1)
      have hsub : badFor i ⊆ (F0 ∪ F1) ∪ (F2 ∪ F3) := by
        intro x hx; rw [Finset.mem_filter] at hx; rw [hdigit_formula i hi x] at hx
        rcases hx.2 with h0 | h1 | h2 | h3
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h0⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h1⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h2⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h3⟩))
      calc
        (badFor i).card ≤ ((F0 ∪ F1) ∪ (F2 ∪ F3)).card := Finset.card_le_card hsub
        _ ≤ (F0 ∪ F1).card + (F2 ∪ F3).card := Finset.card_union_le _ _
        _ ≤ (F0.card + F1.card) + (F2.card + F3.card) :=
            Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)
        _ ≤ (1 + 1) + (1 + 1) := Nat.add_le_add
            (Nat.add_le_add (card_filter_eq_le_one _ hg_inj 0) (card_filter_eq_le_one _ hg_inj 1))
            (Nat.add_le_add (card_filter_eq_le_one _ hg_inj (p - 2)) (card_filter_eq_le_one _ hg_inj (p - 1)))
        _ = 4 := rfl
    let allBad : Finset (Fin p) := Sj.biUnion badFor
    have hallBad_lt : allBad.card < p := by
      calc
        allBad.card ≤ ∑ i ∈ Sj, (badFor i).card := Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ Sj, 4 := Finset.sum_le_sum hbad_card
        _ = 4 * Sj.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 4 * ((p - 1) / 4) := Nat.mul_le_mul_left 4 (hlevel j hj_lt)
        _ ≤ p - 1 := Nat.mul_div_le (p - 1) 4
        _ < p := by omega
    have hexists_good : (Finset.univ \ allBad).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro hemp
      have hcard := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)
      rw [Finset.card_fin] at hcard; omega
    obtain ⟨x₀, hx₀⟩ := hexists_good
    have hx₀_not_bad : x₀ ∉ allBad := (Finset.mem_sdiff.mp hx₀).2
    let lam : ℕ := lam_prev * (1 + x₀.val * p ^ (m - j))
    have hlam_mod : lam % p = lam₀ % p := by
      dsimp [lam]
      have hpow_split : p ^ (m - j) = p * p ^ (m - j - 1) := by
        conv_lhs => rw [show m - j = (m - j - 1) + 1 by omega, pow_succ']
      have hexp_p : lam_prev * (1 + x₀.val * p ^ (m - j)) =
          lam_prev + p * (lam_prev * x₀.val * p ^ (m - j - 1)) := by
        rw [hpow_split]; ring
      rw [hexp_p, Nat.add_mul_mod_self_left, hmod_prev]
    have hlam_not : ¬ (p ∣ lam) := by
      intro hdvd
      have h0 : lam % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rw [hlam_mod] at h0
      exact hlam₀_not (Nat.dvd_of_mod_eq_zero h0)
    refine ⟨lam, hlam_not, hlam_mod, fun i hge hlt => ?_⟩
    rcases eq_or_lt_of_le hge with hei_eq | hei_gt
    · have hi_mem : i ∈ Sj := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hei_eq.symm⟩
      have hx_not_i : x₀ ∉ badFor i := fun h => hx₀_not_bad (Finset.mem_biUnion.mpr ⟨i, hi_mem, h⟩)
      have hnot_or : ¬ (f_digit i x₀ = 0 ∨ f_digit i x₀ = 1 ∨ f_digit i x₀ = p - 2 ∨ f_digit i x₀ = p - 1) :=
        fun hor => hx_not_i (Finset.mem_filter.mpr ⟨Finset.mem_univ x₀, hor⟩)
      have hlt_p : f_digit i x₀ < p := by
        dsimp [f_digit]
        have hlt_N := Nat.mod_lt ((lam_prev * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i))
          (pow_pos (by omega : 0 < p) (m + 1))
        rw [pow_succ] at hlt_N; exact Nat.div_lt_of_lt_mul hlt_N
      change 2 ≤ f_digit i x₀ ∧ f_digit i x₀ ≤ p - 3; omega
    · have hmod_same : (lam * (p ^ (e i) * u i)) % p ^ (m + 1) =
          (lam_prev * (p ^ (e i) * u i)) % p ^ (m + 1) := by
        dsimp [lam]
        have he_split : m - j + e i = (m + 1) + (e i - (j + 1)) := by omega
        have hexp : (lam_prev * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i) =
            lam_prev * (p ^ (e i) * u i) +
            p ^ (m + 1) * (lam_prev * x₀.val * u i * p ^ (e i - (j + 1))) := by
          calc
            (lam_prev * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i)
              = lam_prev * (p ^ (e i) * u i) +
                (lam_prev * x₀.val * u i) * (p ^ (m - j) * p ^ (e i)) := by ring
            _ = lam_prev * (p ^ (e i) * u i) +
                (lam_prev * x₀.val * u i) * p ^ ((m + 1) + (e i - (j + 1))) := by
                  rw [← pow_add, he_split]
            _ = lam_prev * (p ^ (e i) * u i) +
                p ^ (m + 1) * (lam_prev * x₀.val * u i * p ^ (e i - (j + 1))) := by
                  rw [pow_add]; ring
        rw [hexp, Nat.add_mul_mod_self_left]
      rw [hmod_same]; exact hprev i (by omega) hlt

private theorem second_harmonic_padic_sieve {k p : ℕ} (hk : 10 ≤ k) (hp : Nat.Prime p)
    (hpk_gt : k + 1 < p) (hp_ub : p ≤ 2 * k + 1) (w : Fin k → ℕ) (hw : ∀ i, 0 < w i)
    (hdvd_p : ∃ i : Fin k, p ∣ w i)
    (h_no_conc : ¬ ((∃ m : ℕ, 1 ≤ m ∧ (∀ i : Fin k, ¬ (p ^ (m + 1) ∣ w i)) ∧
        (p - 3) / 2 < (Finset.univ.filter (fun i : Fin k => p ^ m ∣ w i)).card) ∨
      (∃ j : ℕ, (∃ i_hi : Fin k, p ^ (j + 1) ∣ w i_hi) ∧
        (p - 1) / 4 < (Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i))).card))) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  have hp5 : 5 ≤ p := by omega
  have hex := fun i => exists_pow_mul_not_dvd hp.two_le (w i) (hw i)
  let e : Fin k → ℕ := fun i => Classical.choose (hex i)
  let u : Fin k → ℕ := fun i => Classical.choose (Classical.choose_spec (hex i))
  have hu_spec : ∀ i, 0 < u i ∧ ¬ (p ∣ u i) ∧ w i = p ^ (e i) * u i :=
    fun i => Classical.choose_spec (Classical.choose_spec (hex i))
  have hu_not : ∀ i, ¬ (p ∣ u i) := fun i => (hu_spec i).2.1
  have hw_decomp : ∀ i, w i = p ^ (e i) * u i := fun i => (hu_spec i).2.2
  let m : ℕ := Finset.univ.sup e
  have he_le : ∀ i, e i ≤ m := fun i => Finset.le_sup (Finset.mem_univ i)
  have hm_ge : 1 ≤ m := by
    obtain ⟨i₀, hi₀⟩ := hdvd_p
    have he_pos : 1 ≤ e i₀ := by
      rcases Nat.eq_zero_or_pos (e i₀) with h0 | hpos
      · exfalso; rw [hw_decomp i₀, h0, pow_zero, one_mul] at hi₀; exact hu_not i₀ hi₀
      · exact hpos
    exact le_trans he_pos (he_le i₀)
  obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ e ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have he_max : e i_max = m :=
    le_antisymm (he_le i_max) (Finset.sup_le fun i _ => hi_max i (Finset.mem_univ i))
  have hm_top_not : ∀ i : Fin k, ¬ (p ^ (m + 1) ∣ w i) := by
    intro i hdvd
    rw [hw_decomp i, pow_dvd_pow_mul_iff hp (hu_not i)] at hdvd
    have := he_le i; omega
  let Sm : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => e i = m)
  have hSm_eq : Sm = Finset.univ.filter (fun i : Fin k => p ^ m ∣ w i) := by
    ext i; simp only [Sm, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hw_decomp i, pow_dvd_pow_mul_iff hp (hu_not i)]
    have := he_le i; omega
  have hSm_card : Sm.card ≤ (p - 3) / 2 := by
    rw [hSm_eq]; by_contra hgt
    exact h_no_conc (Or.inl ⟨m, hm_ge, hm_top_not, Nat.lt_of_not_le hgt⟩)
  have hlevel : ∀ j < m, (Finset.univ.filter (fun i : Fin k => e i = j)).card ≤ (p - 1) / 4 := by
    intro j hj_lt
    have hi_hi : p ^ (j + 1) ∣ w i_max := by
      rw [hw_decomp i_max, pow_dvd_pow_mul_iff hp (hu_not i_max)]; omega
    have hfilt_eq : Finset.univ.filter (fun i : Fin k => e i = j) =
        Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hw_decomp i, exact_pow_dvd_iff_eq hp (hu_not i)]
    rw [hfilt_eq]; by_contra hgt
    exact h_no_conc (Or.inr ⟨j, ⟨i_max, hi_hi⟩, Nat.lt_of_not_le hgt⟩)
  -- Step 1: Choose non-zero seed `lam₀ ∈ {1, ..., p - 1}` keeping every `i ∈ Sm` in `[2, p - 2]` mod `p`.
  let zeroFin : Fin p := ⟨0, by omega⟩
  let unitsFin : Finset (Fin p) := Finset.univ.erase zeroFin
  have hunits_card : unitsFin.card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ zeroFin), Finset.card_fin]
  let badTop : Fin k → Finset (Fin p) :=
    fun i => unitsFin.filter (fun x => (x.val * u i) % p = 1 ∨ (x.val * u i) % p = p - 1)
  have hbadTop_card : ∀ i ∈ Sm, (badTop i).card ≤ 2 := by
    intro i _
    let g : Fin p → ℕ := fun x => (0 + x.val * u i) % p
    have hg_inj : Function.Injective g := add_mul_mod_inj hp (hu_not i)
    have hsub : badTop i ⊆
        (Finset.univ.filter (fun x => g x = 1)) ∪ (Finset.univ.filter (fun x => g x = p - 1)) := by
      intro x hx; rw [Finset.mem_filter] at hx
      have hgx : g x = (x.val * u i) % p := by dsimp [g]; rw [zero_add]
      rcases hx.2 with h1 | hp1
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hgx.trans h1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hgx.trans hp1⟩)
    calc
      (badTop i).card ≤ ((Finset.univ.filter (fun x => g x = 1)) ∪
          (Finset.univ.filter (fun x => g x = p - 1))).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter (fun x => g x = 1)).card +
          (Finset.univ.filter (fun x => g x = p - 1)).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add (card_filter_eq_le_one _ hg_inj 1)
          (card_filter_eq_le_one _ hg_inj (p - 1))
      _ = 2 := rfl
  let allBadTop : Finset (Fin p) := Sm.biUnion badTop
  have hallBadTop_lt : allBadTop.card < unitsFin.card := by
    rw [hunits_card]
    calc
      allBadTop.card ≤ ∑ i ∈ Sm, (badTop i).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ Sm, 2 := Finset.sum_le_sum hbadTop_card
      _ = 2 * Sm.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * ((p - 3) / 2) := Nat.mul_le_mul_left 2 hSm_card
      _ ≤ p - 3 := Nat.mul_div_le (p - 3) 2
      _ < p - 1 := by omega
  have hex_top : (unitsFin \ allBadTop).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hemp
    have hcard := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)
    omega
  obtain ⟨x_top, hx_top⟩ := hex_top
  have hx_in_units : x_top ∈ unitsFin := (Finset.mem_sdiff.mp hx_top).1
  have hx_not_badTop : x_top ∉ allBadTop := (Finset.mem_sdiff.mp hx_top).2
  have hx_pos : 1 ≤ x_top.val := by
    have hne : x_top ≠ zeroFin := (Finset.mem_erase.mp hx_in_units).1
    have hv_ne : x_top.val ≠ 0 := fun hv => hne (Fin.ext hv)
    omega
  let lam₀ : ℕ := x_top.val
  have hlam₀_not : ¬ (p ∣ lam₀) := by
    intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; have := x_top.isLt; omega
  obtain ⟨lam, hlam_not, hlam_mod, hstep⟩ :=
    second_harmonic_filtering_step hp hp5 hm_ge hlam₀_not e u hu_not hlevel m le_rfl
  let N : ℕ := p ^ (m + 1)
  have hN_pos : 0 < N := pow_pos (by omega) (m + 1)
  have hN_eq : N = p * p ^ m := pow_succ' p m
  have hpm_pos : 0 < p ^ m := pow_pos (by omega) m
  refine ⟨(lam : ℝ) / (N : ℝ), by positivity, fun i => ?_⟩
  rcases lt_or_eq_of_le (he_le i) with hlt | heq
  · obtain ⟨hq_lo, hq_hi⟩ := hstep i (by omega) hlt
    rw [← hw_decomp i] at hq_lo hq_hi
    let q_i : ℕ := ((lam * w i) % N) / p ^ m
    let s_i : ℕ := ((lam * w i) % N) % p ^ m
    have hs_lt : s_i < p ^ m := Nat.mod_lt _ hpm_pos
    have hrem_eq : (lam * w i) % N = p ^ m * q_i + s_i :=
      (Nat.div_add_mod ((lam * w i) % N) (p ^ m)).symm
    have hlo : N ≤ (k + 1) * ((lam * w i) % N) := by
      rw [hrem_eq, hN_eq]
      have hmul : 2 * p ^ m ≤ p ^ m * q_i := by
        rw [mul_comm 2]; exact Nat.mul_le_mul_left _ hq_lo
      nlinarith
    have hhi : (k + 1) * ((lam * w i) % N) ≤ (k + 1 - 1) * N := by
      rw [Nat.add_sub_cancel, hrem_eq, hN_eq]
      have hmul : p ^ m * q_i ≤ p ^ m * (p - 3) := Nat.mul_le_mul_left _ hq_hi
      have hsub : p - 2 = (p - 3) + 1 := by omega
      have hlt_p2 : p ^ m * (p - 3) + s_i < p ^ m * (p - 2) := by
        rw [hsub, Nat.mul_add, Nat.mul_one]; omega
      have hle_p2 : p ^ m * q_i + s_i ≤ p ^ m * (p - 2) := by omega
      have hkp : (k + 1) * (p - 2) ≤ k * p := by
        have hp_ge2 : 2 ≤ p := by omega
        zify [hp_ge2] at hp_ub ⊢; nlinarith
      calc
        (k + 1) * (p ^ m * q_i + s_i) ≤ (k + 1) * (p ^ m * (p - 2)) :=
          Nat.mul_le_mul_left _ hle_p2
        _ = ((k + 1) * (p - 2)) * p ^ m := by ring
        _ ≤ (k * p) * p ^ m := Nat.mul_le_mul_right _ hkp
        _ = k * (p * p ^ m) := by ring
    exact unitAddCircle_dist_ge_of_mod_Icc hN_pos (by omega) lam (w i) hlo hhi
  · have hi_Sm : i ∈ Sm := Finset.mem_filter.mpr ⟨Finset.mem_univ i, heq⟩
    have hx_not_i : x_top ∉ badTop i := fun h => hx_not_badTop (Finset.mem_biUnion.mpr ⟨i, hi_Sm, h⟩)
    have htop_mod_eq : (lam * u i) % p = (lam₀ * u i) % p := by
      rw [Nat.mul_mod, hlam_mod, ← Nat.mul_mod]
    have hprod_not : ¬ (p ∣ lam * u i) := fun hdvd =>
      (hp.dvd_mul.mp hdvd).elim hlam_not (hu_not i)
    let r_u : ℕ := (lam * u i) % p
    have hru_ne0 : r_u ≠ 0 := fun h0 => hprod_not (Nat.dvd_of_mod_eq_zero h0)
    have hru_not_1_p1 : ¬ (r_u = 1 ∨ r_u = p - 1) := by
      intro hor; rw [show r_u = (lam * u i) % p from rfl, htop_mod_eq] at hor
      exact hx_not_i (Finset.mem_filter.mpr ⟨hx_in_units, hor⟩)
    have hru_lt : r_u < p := Nat.mod_lt _ (by omega)
    have hru_le : r_u ≤ p - 1 := by omega
    have hru_lo : 2 ≤ r_u := by omega
    have hru_hi : r_u ≤ p - 2 := by omega
    have hwi : w i = p ^ m * u i := by rw [hw_decomp i, heq]
    have hmod_eq : (lam * w i) % N = r_u * p ^ m := by
      dsimp [N]; rw [hwi]
      have hdiv := (Nat.div_add_mod (lam * u i) p).symm
      have hrew : lam * (p ^ m * u i) = r_u * p ^ m + p ^ (m + 1) * ((lam * u i) / p) := by
        calc lam * (p ^ m * u i) = (lam * u i) * p ^ m := by ring
          _ = (p * ((lam * u i) / p) + r_u) * p ^ m := by rw [← hdiv]
          _ = r_u * p ^ m + p ^ (m + 1) * ((lam * u i) / p) := by rw [pow_succ']; ring
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
      rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_right hru_lt hpm_pos
    have hlo : N ≤ (k + 1) * ((lam * w i) % N) := by
      rw [hmod_eq, hN_eq]
      have hmul : 2 * p ^ m ≤ r_u * p ^ m := Nat.mul_le_mul_right _ hru_lo
      nlinarith
    have hhi : (k + 1) * ((lam * w i) % N) ≤ (k + 1 - 1) * N := by
      rw [Nat.add_sub_cancel, hmod_eq, hN_eq]
      have hkp : (k + 1) * (p - 2) ≤ k * p := by
        have hp_ge2 : 2 ≤ p := by omega
        zify [hp_ge2] at hp_ub ⊢; nlinarith
      calc
        (k + 1) * (r_u * p ^ m) ≤ (k + 1) * ((p - 2) * p ^ m) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hru_hi)
        _ = ((k + 1) * (p - 2)) * p ^ m := by ring
        _ ≤ (k * p) * p ^ m := Nat.mul_le_mul_right _ hkp
        _ = k * (p * p ^ m) := by ring
    exact unitAddCircle_dist_ge_of_mod_Icc hN_pos (by omega) lam (w i) hlo hhi

end

end ReductionProofs

theorem main : H1 → H2 → H3 → OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R2.H3 := by
  intro h1 h2 h3 k hk10 w hw_pos hw_mono hw_gcd hw_sub hdvd_k1 hlac hsum_le
  by_cases h_sdiv : ∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → ∃ i : Fin k, j ∣ w i
  · by_cases h_c1 : ∀ p : ℕ, Nat.Prime p → 3 ≤ p → p ≤ k + 1 →
        ∃ j : ℕ, (∃ i_hi : Fin k, p ^ (j + 1) ∣ w i_hi) ∧
          (p - 1) / 2 < (Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i))).card
    · by_cases h_c2 : ∀ p : ℕ, Nat.Prime p → k + 1 < p → p ≤ 2 * k + 1 → (∃ i : Fin k, p ∣ w i) →
          (∃ m : ℕ, 1 ≤ m ∧ (∀ i : Fin k, ¬ (p ^ (m + 1) ∣ w i)) ∧
            (p - 3) / 2 < (Finset.univ.filter (fun i : Fin k => p ^ m ∣ w i)).card) ∨
          (∃ j : ℕ, (∃ i_hi : Fin k, p ^ (j + 1) ∣ w i_hi) ∧
            (p - 1) / 4 < (Finset.univ.filter (fun i : Fin k => p ^ j ∣ w i ∧ ¬ (p ^ (j + 1) ∣ w i))).card)
      · by_cases hp_k1 : Nat.Prime (k + 1)
        · -- Prime-denominator middle-band exclusion!
          have hk_even : 2 * (k / 2) = k := by
            have hnot2 : ¬ (2 ∣ k + 1) := by
              intro hd2
              rcases hp_k1.eq_one_or_self_of_dvd 2 hd2 with h | h <;> omega
            omega
          obtain ⟨j, ⟨i_hi, hi_hi⟩, hj_gt⟩ := h_c1 (k + 1) hp_k1 (by omega) le_rfl
          have hhalf : (k + 1 - 1) / 2 = k / 2 := by omega
          rw [hhalf] at hj_gt
          let Mset : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => (k + 1) ∣ w i)
          rcases Nat.eq_zero_or_pos j with rfl | hj_pos
          · -- j = 0: sparse (k + 1)-divisibility (Mset.card ≤ k / 2 - 1) -> H1!
            have hfilt0 : Finset.univ.filter (fun i : Fin k =>
                (k + 1) ^ 0 ∣ w i ∧ ¬ ((k + 1) ^ (0 + 1) ∣ w i)) = Finset.univ \ Mset := by
              ext i
              simp only [Mset, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
                pow_zero, one_dvd, zero_add, pow_one]
            rw [hfilt0] at hj_gt
            have hsdiff_card : (Finset.univ \ Mset).card + Mset.card = k := by
              have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Mset)
              rwa [Finset.card_fin] at h
            have hM_le : Mset.card ≤ k / 2 - 1 := by omega
            exact h1 k hk10 hp_k1 w hw_pos hw_mono hw_gcd hw_sub h_sdiv hM_le h_c1 h_c2 hlac hsum_le
          · -- j ≥ 1: super-concentrated higher (k + 1)^2-divisibility (Mset.card ≥ k / 2 + 2) -> H2!
            let Lj : Finset (Fin k) := Finset.univ.filter (fun i : Fin k =>
              (k + 1) ^ j ∣ w i ∧ ¬ ((k + 1) ^ (j + 1) ∣ w i))
            have hi_not_Lj : i_hi ∉ Lj := by
              intro hmem; exact (Finset.mem_filter.mp hmem).2.2 hi_hi
            have hins_sub : insert i_hi Lj ⊆ Mset := by
              intro i hi_in
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ i, ?_⟩
              rcases Finset.mem_insert.mp hi_in with rfl | hi_Lj
              · exact dvd_trans (dvd_pow_self (k + 1) (by omega)) hi_hi
              · exact dvd_trans (dvd_pow_self (k + 1) (by omega)) (Finset.mem_filter.mp hi_Lj).2.1
            have hcard_ins : (insert i_hi Lj).card = Lj.card + 1 :=
              Finset.card_insert_of_notMem hi_not_Lj
            have hcard_le_M : Lj.card + 1 ≤ Mset.card := by
              rw [← hcard_ins]; exact Finset.card_le_card hins_sub
            have hLj_ge : k / 2 + 1 ≤ Lj.card := by dsimp [Lj]; omega
            have hM_ge : k / 2 + 2 ≤ Mset.card := by omega
            exact h2 k hk10 hp_k1 w hw_pos hw_mono hw_gcd hw_sub h_sdiv hM_ge
              ⟨j, hj_pos, ⟨i_hi, hi_hi⟩, hLj_ge⟩ h_c1 h_c2 hlac hsum_le
        · exact h3 k hk10 hp_k1 w hw_pos hw_mono hw_gcd hw_sub h_sdiv h_c1 h_c2 hlac hsum_le
      · simp only [not_forall] at h_c2
        obtain ⟨p, hp, hpk_gt, hp_ub, hdvd_p, hno⟩ := h_c2
        exact second_harmonic_padic_sieve hk10 hp hpk_gt hp_ub w hw_pos hdvd_p hno
    · simp only [not_forall] at h_c1
      obtain ⟨p, hp, hp3, hpk, hno⟩ := h_c1
      exact first_harmonic_padic_sieve (by omega) hp hp3 hpk w hw_pos (h_sdiv p hp.two_le hpk) hno
  · simp only [not_forall, not_exists] at h_sdiv
    obtain ⟨j, hj2, hjk, hndvd⟩ := h_sdiv
    exact lrc_small_divisor_sieve hj2 hjk w hndvd

end OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R2_H3_R1
