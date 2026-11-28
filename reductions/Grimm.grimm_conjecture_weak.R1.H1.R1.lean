import OMAReductions.R_Grimm_grimm_conjecture_weak_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Reduction of `Grimm.grimm_conjecture_weak.R1.H1` to 3-logarithm Diophantine separation

`OMA.R_Grimm_grimm_conjecture_weak_R1.H1` asks to prove that for every run of `k ≥ 8`
consecutive composites `n, ..., n + k - 1` with `k < n ≤ lcm(1..k-1)`, some
`(n + j) ∣ lcm(1..k-1)`, and `k ^ 2 ≤ (Nat.log 2 n) ^ 5`, at most `π(k)` of the elements
`n + j` are `k`-smooth (`∈ Nat.smoothNumbers (k + 1)`).

We prove unconditionally in Lean 4:
1. **Small `k` (`8 ≤ k ≤ 11`):** Every run of `k ≥ 8` composites satisfies `55 ≤ n`, and
   every interval `[n, n + k)` with `55 ≤ n ≤ lcm(1..k-1)` containing a divisor of
   `lcm(1..k-1) ∣ 2520` has at most `π(k)` elements that are `k`-smooth.
   For `12 ≤ k ≤ 14`, a verified divisor enumeration checks the smooth counts against
   divisibility in a suitable power of `lcm(1..k)`, or finds a prime in the window.
2. **Chebyshev + binary-log threshold (`k ≥ 2 ^ 38`):** Using `Chebyshev.pi_ge` (where
   `Real.log 2` cancels identically via `m = Nat.log 2 k`), `k ^ 2 ≤ (Nat.log 2 n) ^ 5`
   implies `k ^ 12 < n` and `(k - 1)! ^ 4 < n ^ (π(k) / 4)`.
3. **Prime-power maximizer deletion and product averaging (`k ≥ 2 ^ 38`):**
   If more than `π(k)` elements of `[n, n + k)` are `k`-smooth, assign each active prime
   `p ≤ k` to an index `j_p` maximizing `v_p(n + j)` and factor `n + j = A_j * B_j` where
   `A_j` collects the prime powers assigned to `j`. Then:
   - `∏_{j ∈ S} B_j ∣ (k - 1)!`,
   - partitioning `S = T₀ ⊔ T₁ ⊔ T₂` by `|Q_j| ∈ {0, 1, ≥ 2}` gives `|T₀| > |T₂|` and
     `n ^ |T₀| ≤ (k - 1)! < n ^ (π(k) / 4)`, forcing `|T₁| - 1 ≥ π(k) / 2`,
   - choosing the two smallest cofactors `B₁ ≤ B₂` in `T₁` produces two distinct
     prime-power-dominated integers `p₁ ^ e₁ * B₁ ≠ p₂ ^ e₂ * B₂` in `[n, n + k)` with
     distinct primes `p₁ ≠ p₂ ≤ k`, `¬ pᵢ ∣ Bᵢ`, `Bᵢ ^ (π(k) / 2) ≤ (k - 1)!`, and
     `(B₁ * B₂) ^ 4 < n` (hence `k ^ 3 * B₁ * B₂ < √n`, ABC quality `> 2`).

This splits `OMA.R_Grimm_grimm_conjecture_weak_R1.H1` cleanly into:
- `H1`: pure 3-logarithm Baker / ABC Diophantine separation for `k ≥ 2 ^ 38` (no mention
  of Grimm's conjecture, composites, smooth numbers, or `lcm`), and
- `H2`: the explicit finite range `15 ≤ k < 2 ^ 38`.
-/

namespace OMA.R_Grimm_grimm_conjecture_weak_R1_H1_R1

/-- Asymptotic Baker / 3-logarithm / ABC Diophantine separation (`k ≥ 2 ^ 38`):
there are no two distinct prime-power-dominated integers `p₁ ^ e₁ * B₁ ≠ p₂ ^ e₂ * B₂`
in `[n, n + k)` with `k ^ 12 < n`, `k ^ 2 ≤ (Nat.log 2 n) ^ 5`, distinct primes
`p₁ ≠ p₂ ≤ k`, positive exponents `e₁, e₂ ≥ 1`, and cofactors `B₁, B₂ ≥ 1` coprime to
`p₁, p₂` satisfying `B₁ ^ (Nat.primeCounting k / 2) ≤ (k - 1)!`,
`B₂ ^ (Nat.primeCounting k / 2) ≤ (k - 1)!`, and `(B₁ * B₂) ^ 4 < n`. -/
def H1 : Prop :=
  ∀ n k : ℕ, 2 ^ 38 ≤ k → k ^ 12 < n → k ^ 2 ≤ (Nat.log 2 n) ^ 5 →
    ¬ ∃ p₁ p₂ e₁ e₂ B₁ B₂ : ℕ,
      p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧ p₁ ≤ k ∧ p₂ ≤ k ∧
      1 ≤ e₁ ∧ 1 ≤ e₂ ∧ 1 ≤ B₁ ∧ 1 ≤ B₂ ∧ ¬ p₁ ∣ B₁ ∧ ¬ p₂ ∣ B₂ ∧
      B₁ ^ (Nat.primeCounting k / 2) ≤ Nat.factorial (k - 1) ∧
      B₂ ^ (Nat.primeCounting k / 2) ≤ Nat.factorial (k - 1) ∧
      (B₁ * B₂) ^ 4 < n ∧
      n ≤ p₁ ^ e₁ * B₁ ∧ p₁ ^ e₁ * B₁ < n + k ∧
      n ≤ p₂ ^ e₂ * B₂ ∧ p₂ ^ e₂ * B₂ < n + k ∧
      p₁ ^ e₁ * B₁ ≠ p₂ ^ e₂ * B₂

/-- Bounded-`k` regime (`15 ≤ k < 2 ^ 38`): smooth-number count bound for runs of `k`
consecutive composites in the finite range `15 ≤ k < 2 ^ 38`. -/
def H2 : Prop :=
  ∀ n k : ℕ, 15 ≤ k → k < 2 ^ 38 → k < n → n ≤ (Finset.Ico 1 k).lcm id →
    (∃ j : Fin k, (n + j) ∣ (Finset.Ico 1 k).lcm id) →
    k ^ 2 ≤ (Nat.log 2 n) ^ 5 →
    (∀ i : Fin k, (n + i).Composite) →
    (Finset.univ.filter (fun j : Fin k => (n + j) ∈ Nat.smoothNumbers (k + 1))).card ≤
      Nat.primeCounting k

lemma twenty_mul_succ_le_two_pow (m : ℕ) (hm : 8 ≤ m) : 20 * (m + 1) ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

lemma pow_five_lt_two_pow_two_mul (m : ℕ) (hm : 38 ≤ m) :
    (20 * (m + 1) ^ 2) ^ 5 < 2 ^ (2 * m) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h10 : 10 * (m + 2) ≤ 11 * (m + 1) := by omega
    have hpow : (10 * (m + 2)) ^ 10 ≤ (11 * (m + 1)) ^ 10 := Nat.pow_le_pow_left h10 10
    rw [mul_pow, mul_pow] at hpow
    have h11 : 11 ^ 10 ≤ 4 * 10 ^ 10 := by norm_num
    have hstep1 : 10 ^ 10 * (m + 2) ^ 10 ≤ 10 ^ 10 * (4 * (m + 1) ^ 10) := by
      calc 10 ^ 10 * (m + 2) ^ 10
          ≤ 11 ^ 10 * (m + 1) ^ 10 := hpow
        _ ≤ (4 * 10 ^ 10) * (m + 1) ^ 10 := Nat.mul_le_mul_right _ h11
        _ = 10 ^ 10 * (4 * (m + 1) ^ 10) := by ring
    have hstep : (m + 2) ^ 10 ≤ 4 * (m + 1) ^ 10 :=
      Nat.le_of_mul_le_mul_left hstep1 (by norm_num)
    have hmul : (20 * (m + 2) ^ 2) ^ 5 ≤ 4 * (20 * (m + 1) ^ 2) ^ 5 := by
      have hL : (20 * (m + 2) ^ 2) ^ 5 = 20 ^ 5 * (m + 2) ^ 10 := by ring
      have hR : 4 * (20 * (m + 1) ^ 2) ^ 5 = 20 ^ 5 * (4 * (m + 1) ^ 10) := by ring
      rw [hL, hR]
      exact Nat.mul_le_mul_left _ hstep
    have h2 : 2 ^ (2 * (m + 1)) = 4 * 2 ^ (2 * m) := by
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
      ring
    rw [h2]
    exact lt_of_le_of_lt hmul (Nat.mul_lt_mul_of_pos_left ih (by norm_num))

lemma primeCounting_ge_div (k : ℕ) (hk : 2 ^ 38 ≤ k) :
    k ≤ 5 * (Nat.log 2 k + 1) * (Nat.primeCounting k / 4) := by
  set m := Nat.log 2 k
  have hm38 : 38 ≤ m := Nat.le_log_of_pow_le (by norm_num) hk
  have h2m_le : 2 ^ m ≤ k := Nat.pow_log_le_self 2 (by omega)
  have hk_lt : k < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have h20 : 20 * (m + 1) ≤ k := (twenty_mul_succ_le_two_pow m (by omega)).trans h2m_le
  have hpiR : ((k : ℝ) * Real.log 2 - Real.log ((k : ℝ) + 1)) / Real.log (k : ℝ) ≤
      (Nat.primeCounting k : ℝ) := Chebyshev.pi_ge k
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk1_le : ((k : ℝ) + 1) ≤ (2 : ℝ) ^ (m + 1) := by
    have : k + 1 ≤ 2 ^ (m + 1) := hk_lt
    exact_mod_cast this
  have hk_le : (k : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by linarith
  have hlog_k1 : Real.log ((k : ℝ) + 1) ≤ ((m + 1 : ℕ) : ℝ) * Real.log 2 := by
    calc Real.log ((k : ℝ) + 1)
        ≤ Real.log ((2 : ℝ) ^ (m + 1)) := Real.log_le_log (by positivity) hk1_le
      _ = ((m + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (m + 1)
  have hlog_k : Real.log (k : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * Real.log 2 := by
    calc Real.log (k : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (m + 1)) := Real.log_le_log (by positivity) hk_le
      _ = ((m + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (m + 1)
  have hmulR : (k : ℝ) * Real.log 2 - Real.log ((k : ℝ) + 1) ≤
      (Nat.primeCounting k : ℝ) * Real.log (k : ℝ) := (div_le_iff₀ hlogk_pos).mp hpiR
  have hstepR : ((k : ℝ) - ((m + 1 : ℕ) : ℝ)) * Real.log 2 ≤
      ((Nat.primeCounting k : ℝ) * ((m + 1 : ℕ) : ℝ)) * Real.log 2 := by
    calc ((k : ℝ) - ((m + 1 : ℕ) : ℝ)) * Real.log 2
        = (k : ℝ) * Real.log 2 - ((m + 1 : ℕ) : ℝ) * Real.log 2 := by ring
      _ ≤ (k : ℝ) * Real.log 2 - Real.log ((k : ℝ) + 1) := by linarith
      _ ≤ (Nat.primeCounting k : ℝ) * Real.log (k : ℝ) := hmulR
      _ ≤ (Nat.primeCounting k : ℝ) * (((m + 1 : ℕ) : ℝ) * Real.log 2) :=
          mul_le_mul_of_nonneg_left hlog_k (Nat.cast_nonneg _)
      _ = ((Nat.primeCounting k : ℝ) * ((m + 1 : ℕ) : ℝ)) * Real.log 2 := by ring
  have hcancel : (k : ℝ) - ((m + 1 : ℕ) : ℝ) ≤ (Nat.primeCounting k : ℝ) * ((m + 1 : ℕ) : ℝ) :=
    le_of_mul_le_mul_right hstepR hlog2_pos
  have hnat : k ≤ (m + 1) * Nat.primeCounting k + (m + 1) := by
    have : (k : ℝ) ≤ (((m + 1) * Nat.primeCounting k + (m + 1) : ℕ) : ℝ) := by
      push_cast at hcancel ⊢
      linarith
    exact_mod_cast this
  have hdiv : Nat.primeCounting k ≤ 4 * (Nat.primeCounting k / 4) + 3 := by omega
  have h5 : 5 * k ≤ 5 * ((m + 1) * (4 * (Nat.primeCounting k / 4) + 3) + (m + 1)) := by
    calc 5 * k ≤ 5 * ((m + 1) * Nat.primeCounting k + (m + 1)) := Nat.mul_le_mul_left 5 hnat
      _ ≤ 5 * ((m + 1) * (4 * (Nat.primeCounting k / 4) + 3) + (m + 1)) :=
          Nat.mul_le_mul_left 5 (Nat.add_le_add_right (Nat.mul_le_mul_left (m + 1) hdiv) _)
  have hexp : 5 * ((m + 1) * (4 * (Nat.primeCounting k / 4) + 3) + (m + 1)) =
      4 * (5 * (m + 1) * (Nat.primeCounting k / 4)) + 20 * (m + 1) := by ring
  rw [hexp] at h5
  omega

lemma factorial_pow_four_lt_of_ge (n k : ℕ) (hk : 2 ^ 38 ≤ k)
    (hgap : k ^ 2 ≤ (Nat.log 2 n) ^ 5) :
    k ^ 12 < n ∧ (Nat.factorial (k - 1)) ^ 4 < n ^ (Nat.primeCounting k / 4) := by
  set m := Nat.log 2 k
  set L := Nat.log 2 n
  have hm38 : 38 ≤ m := Nat.le_log_of_pow_le (by norm_num) hk
  have h2m_le : 2 ^ m ≤ k := Nat.pow_log_le_self 2 (by omega)
  have hk_lt : k < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have h2_2m_le : 2 ^ (2 * m) ≤ L ^ 5 := by
    calc 2 ^ (2 * m) = (2 ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
      _ ≤ k ^ 2 := Nat.pow_le_pow_left h2m_le 2
      _ ≤ L ^ 5 := hgap
  have hL5 : (20 * (m + 1) ^ 2) ^ 5 < L ^ 5 :=
    lt_of_lt_of_le (pow_five_lt_two_pow_two_mul m hm38) h2_2m_le
  have h20L : 20 * (m + 1) ^ 2 < L := by
    by_contra hle
    push Not at hle
    exact Nat.not_lt_of_ge (Nat.pow_le_pow_left hle 5) hL5
  have hn_ne : n ≠ 0 := by
    intro h0
    have : L = 0 := by simp [L, h0]
    omega
  have h2L_le : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn_ne
  constructor
  · have h12 : 12 * (m + 1) ≤ L := by nlinarith
    calc k ^ 12 < (2 ^ (m + 1)) ^ 12 := Nat.pow_lt_pow_left hk_lt (by norm_num)
      _ = 2 ^ (12 * (m + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) h12
      _ ≤ n := h2L_le
  · have hpi := primeCounting_ge_div k hk
    have hfact_le : Nat.factorial (k - 1) ≤ k ^ k := by
      calc Nat.factorial (k - 1) ≤ Nat.factorial k := Nat.factorial_le (by omega)
        _ ≤ k ^ k := Nat.factorial_le_pow k
    have hexp_le : 4 * (m + 1) * k ≤ L * (Nat.primeCounting k / 4) := by
      calc 4 * (m + 1) * k
          ≤ 4 * (m + 1) * (5 * (m + 1) * (Nat.primeCounting k / 4)) :=
            Nat.mul_le_mul_left _ hpi
        _ = (20 * (m + 1) ^ 2) * (Nat.primeCounting k / 4) := by ring
        _ ≤ L * (Nat.primeCounting k / 4) := Nat.mul_le_mul_right _ h20L.le
    calc (Nat.factorial (k - 1)) ^ 4
        ≤ (k ^ k) ^ 4 := Nat.pow_le_pow_left hfact_le 4
      _ = k ^ (4 * k) := by rw [← pow_mul, mul_comm]
      _ < (2 ^ (m + 1)) ^ (4 * k) := Nat.pow_lt_pow_left hk_lt (by omega)
      _ = 2 ^ (4 * (m + 1) * k) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ (L * (Nat.primeCounting k / 4)) := Nat.pow_le_pow_right (by norm_num) hexp_le
      _ = (2 ^ L) ^ (Nat.primeCounting k / 4) := by rw [pow_mul]
      _ ≤ n ^ (Nat.primeCounting k / 4) := Nat.pow_le_pow_left h2L_le _

lemma prod_Icc_eq_factorial (m : ℕ) : ∏ x ∈ Finset.Icc 1 m, x = m.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1), ih, Nat.factorial_succ, mul_comm]

lemma primeCounting_ge_four (k : ℕ) (hk : 8 ≤ k) : 4 ≤ Nat.primeCounting k := by
  have h8 : 4 ≤ Nat.primeCounting 8 := by decide
  exact h8.trans (Nat.monotone_primeCounting hk)

lemma factorization_prod_prime_pow (T : Finset ℕ) (e : ℕ → ℕ)
    (hT : ∀ q ∈ T, q.Prime) (p : ℕ) :
    (∏ q ∈ T, q ^ e q).factorization p = if p ∈ T then e p else 0 := by
  have hne : ∀ q ∈ T, q ^ e q ≠ 0 := fun q hq => pow_ne_zero _ (hT q hq).ne_zero
  rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
  have hterm : ∀ q ∈ T, (q ^ e q).factorization p = if p = q then e q else 0 := by
    intro q hq
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, (hT q hq).factorization,
      Finsupp.single_apply]
    by_cases h : p = q
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl hterm]
  simp

lemma exists_prime_power_pair_of_many_smooth (n k : ℕ) (hk8 : 8 ≤ k) (hkn : k < n)
    (hfact_lt : (Nat.factorial (k - 1)) ^ 4 < n ^ (Nat.primeCounting k / 4))
    (hS : Nat.primeCounting k <
      (Finset.univ.filter (fun j : Fin k => (n + j) ∈ Nat.smoothNumbers (k + 1))).card) :
    ∃ p₁ p₂ e₁ e₂ B₁ B₂ : ℕ,
      p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧ p₁ ≤ k ∧ p₂ ≤ k ∧
      1 ≤ e₁ ∧ 1 ≤ e₂ ∧ 1 ≤ B₁ ∧ 1 ≤ B₂ ∧ ¬ p₁ ∣ B₁ ∧ ¬ p₂ ∣ B₂ ∧
      B₁ ^ (Nat.primeCounting k / 2) ≤ Nat.factorial (k - 1) ∧
      B₂ ^ (Nat.primeCounting k / 2) ≤ Nat.factorial (k - 1) ∧
      (B₁ * B₂) ^ 4 < n ∧
      n ≤ p₁ ^ e₁ * B₁ ∧ p₁ ^ e₁ * B₁ < n + k ∧
      n ≤ p₂ ^ e₂ * B₂ ∧ p₂ ^ e₂ * B₂ < n + k ∧
      p₁ ^ e₁ * B₁ ≠ p₂ ^ e₂ * B₂ := by
  classical
  set S : Finset (Fin k) :=
    Finset.univ.filter (fun j : Fin k => (n + j) ∈ Nat.smoothNumbers (k + 1))
  have hpi4 : 4 ≤ Nat.primeCounting k := primeCounting_ge_four k hk8
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  set P : Finset ℕ := k.primesLE
  have hP_card : P.card = Nat.primeCounting k := Nat.primesLE_card_eq_primeCounting k
  set P_S : Finset ℕ := P.filter (fun p => ∃ j ∈ S, p ∣ (n + j))
  have hPS_sub : P_S ⊆ P := Finset.filter_subset _ _
  have hPS_prime : ∀ p ∈ P_S, p.Prime := fun p hp => Nat.prime_of_mem_primesLE (hPS_sub hp)
  have hPS_le : ∀ p ∈ P_S, p ≤ k := fun p hp => Nat.le_of_mem_primesLE (hPS_sub hp)
  have hPS_card : P_S.card ≤ Nat.primeCounting k := (Finset.card_le_card hPS_sub).trans hP_card.le
  have hex_max : ∀ p : ℕ, ∃ j₀ ∈ S, ∀ j ∈ S, (n + j).factorization p ≤ (n + j₀).factorization p :=
    fun p => Finset.exists_max_image S (fun j : Fin k => (n + j).factorization p) hS_ne
  choose jmax hjmax_mem hjmax_ge using hex_max
  let Q : Fin k → Finset ℕ := fun j => P_S.filter (fun p => jmax p = j)
  let A : Fin k → ℕ := fun j => ∏ p ∈ Q j, p ^ ((n + j).factorization p)
  let B : Fin k → ℕ := fun j => ∏ p ∈ P_S \ Q j, p ^ ((n + j).factorization p)
  have hQ_sub : ∀ j : Fin k, Q j ⊆ P_S := fun j => Finset.filter_subset _ _
  have hB_pos : ∀ j : Fin k, 0 < B j := fun j =>
    Finset.prod_pos fun p hp => pow_pos (hPS_prime p (Finset.sdiff_subset hp)).pos _
  have hAB : ∀ j ∈ S, A j * B j = n + j := by
    intro j hj
    dsimp only [A, B]
    rw [mul_comm, Finset.prod_sdiff (hQ_sub j)]
    have hsm : (n + j : ℕ) ∈ Nat.smoothNumbers (k + 1) := (Finset.mem_filter.mp hj).2
    have hne : (n + j : ℕ) ≠ 0 := by omega
    have hpf_sub : (n + j : ℕ).primeFactors ⊆ P_S := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd := Nat.dvd_of_mem_primeFactors hp
      have hp_lt : p < k + 1 := Nat.mem_smoothNumbers'.mp hsm p hp_prime hp_dvd
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega, hp_prime⟩, j, hj, hp_dvd⟩
    have hprod_eq : ∏ p ∈ P_S, p ^ ((n + j).factorization p) =
        ∏ p ∈ (n + j).primeFactors, p ^ ((n + j).factorization p) := by
      refine (Finset.prod_subset hpf_sub fun p _ hp_not => ?_).symm
      have h0 : (n + j).factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hp_not
      simp [h0]
    rw [hprod_eq, ← Nat.prod_factorization_eq_prod_primeFactors,
      Nat.prod_factorization_pow_eq_self hne]
  have hB_fact : ∀ j : Fin k, ∀ p : ℕ,
      (B j).factorization p = if p ∈ P_S \ Q j then (n + j).factorization p else 0 := by
    intro j p
    exact factorization_prod_prime_pow (P_S \ Q j) (fun q => (n + j).factorization q)
      (fun q hq => hPS_prime q (Finset.sdiff_subset hq)) p
  have hprod_B_dvd : ∏ j ∈ S, B j ∣ Nat.factorial (k - 1) := by
    have hprod_ne : ∏ j ∈ S, B j ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => (hB_pos j).ne'
    have hfact_ne : Nat.factorial (k - 1) ≠ 0 := Nat.factorial_ne_zero _
    rw [← Nat.factorization_le_iff_dvd hprod_ne hfact_ne]
    intro p
    rw [Nat.factorization_prod (fun j _ => (hB_pos j).ne'), Finsupp.finsetSum_apply]
    by_cases hpPS : p ∈ P_S
    · have hp_prime : p.Prime := hPS_prime p hpPS
      set j₀ := jmax p
      have hj₀_mem : j₀ ∈ S := hjmax_mem p
      have hterm_j₀ : (B j₀).factorization p = 0 := by
        rw [hB_fact]
        have : p ∉ P_S \ Q j₀ := by simp [Q, j₀]
        simp [this]
      rw [← Finset.add_sum_erase S (fun j => (B j).factorization p) hj₀_mem, hterm_j₀, zero_add]
      have hterm_ne : ∀ j ∈ S.erase j₀, (B j).factorization p = (n + j).factorization p := by
        intro j hj
        rw [hB_fact]
        have hne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
        have hmem : p ∈ P_S \ Q j := by
          rw [Finset.mem_sdiff]
          exact ⟨hpPS, fun h => hne (Finset.mem_filter.mp h).2.symm⟩
        simp [hmem]
      rw [Finset.sum_congr rfl hterm_ne]
      set S_lt := (S.erase j₀).filter (fun j : Fin k => j.1 < j₀.1)
      set S_gt := (S.erase j₀).filter (fun j : Fin k => j₀.1 < j.1)
      have hunion : S.erase j₀ = S_lt ∪ S_gt := by
        ext j
        simp only [S_lt, S_gt, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
        constructor
        · intro hj
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hj.1) with hlt | hgt
          · exact Or.inl ⟨hj, hlt⟩
          · exact Or.inr ⟨hj, hgt⟩
        · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
      have hdisj : Disjoint S_lt S_gt := by
        rw [Finset.disjoint_left]
        intro j h1 h2
        have h1' := (Finset.mem_filter.mp h1).2
        have h2' := (Finset.mem_filter.mp h2).2
        omega
      rw [hunion, Finset.sum_union hdisj]
      have hlt_le : ∑ j ∈ S_lt, (n + j).factorization p ≤ (j₀.1.factorial).factorization p := by
        have hpt : ∀ j ∈ S_lt, (n + j).factorization p ≤ (j₀.1 - j.1).factorization p := by
          intro j hj
          have hjS : j ∈ S := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).2
          have hlt : j.1 < j₀.1 := (Finset.mem_filter.mp hj).2
          set e := (n + j).factorization p
          have hd1 : p ^ e ∣ n + j.1 := Nat.ordProj_dvd (n + j.1) p
          have hd2 : p ^ e ∣ n + j₀.1 :=
            (Nat.pow_dvd_pow p (hjmax_ge p j hjS)).trans (Nat.ordProj_dvd (n + j₀.1) p)
          have hsub : p ^ e ∣ j₀.1 - j.1 := by
            have heq : (n + j₀.1) - (n + j.1) = j₀.1 - j.1 := by omega
            rw [← heq]
            exact Nat.dvd_sub hd2 hd1
          exact (hp_prime.pow_dvd_iff_le_factorization (by omega)).mp hsub
        have h1 := Finset.sum_le_sum hpt
        have hinj : Set.InjOn (fun j : Fin k => j₀.1 - j.1) S_lt := by
          intro a ha b hb hab
          dsimp only at hab
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          ext; omega
        have himg_sub : S_lt.image (fun j : Fin k => j₀.1 - j.1) ⊆ Finset.Icc 1 j₀.1 := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
          have hj' := (Finset.mem_filter.mp hj).2
          rw [Finset.mem_Icc]; omega
        calc ∑ j ∈ S_lt, (n + j).factorization p
            ≤ ∑ j ∈ S_lt, (j₀.1 - j.1).factorization p := h1
          _ = ∑ x ∈ S_lt.image (fun j : Fin k => j₀.1 - j.1), x.factorization p :=
              (Finset.sum_image (f := fun x : ℕ => x.factorization p) hinj).symm
          _ ≤ ∑ x ∈ Finset.Icc 1 j₀.1, x.factorization p :=
              Finset.sum_le_sum_of_subset himg_sub
          _ = (∏ x ∈ Finset.Icc 1 j₀.1, x).factorization p := by
              rw [Nat.factorization_prod (fun x hx => by rw [Finset.mem_Icc] at hx; omega),
                Finsupp.finsetSum_apply]
          _ = (j₀.1.factorial).factorization p := by rw [prod_Icc_eq_factorial]
      have hgt_le : ∑ j ∈ S_gt, (n + j).factorization p ≤
          ((k - 1 - j₀.1).factorial).factorization p := by
        have hpt : ∀ j ∈ S_gt, (n + j).factorization p ≤ (j.1 - j₀.1).factorization p := by
          intro j hj
          have hjS : j ∈ S := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).2
          have hgt : j₀.1 < j.1 := (Finset.mem_filter.mp hj).2
          set e := (n + j).factorization p
          have hd1 : p ^ e ∣ n + j.1 := Nat.ordProj_dvd (n + j.1) p
          have hd2 : p ^ e ∣ n + j₀.1 :=
            (Nat.pow_dvd_pow p (hjmax_ge p j hjS)).trans (Nat.ordProj_dvd (n + j₀.1) p)
          have hsub : p ^ e ∣ j.1 - j₀.1 := by
            have heq : (n + j.1) - (n + j₀.1) = j.1 - j₀.1 := by omega
            rw [← heq]
            exact Nat.dvd_sub hd1 hd2
          exact (hp_prime.pow_dvd_iff_le_factorization (by omega)).mp hsub
        have h1 := Finset.sum_le_sum hpt
        have hinj : Set.InjOn (fun j : Fin k => j.1 - j₀.1) S_gt := by
          intro a ha b hb hab
          dsimp only at hab
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          ext; omega
        have himg_sub : S_gt.image (fun j : Fin k => j.1 - j₀.1) ⊆ Finset.Icc 1 (k - 1 - j₀.1) := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
          have hj' := (Finset.mem_filter.mp hj).2
          have hjk := j.2
          rw [Finset.mem_Icc]; omega
        calc ∑ j ∈ S_gt, (n + j).factorization p
            ≤ ∑ j ∈ S_gt, (j.1 - j₀.1).factorization p := h1
          _ = ∑ x ∈ S_gt.image (fun j : Fin k => j.1 - j₀.1), x.factorization p :=
              (Finset.sum_image (f := fun x : ℕ => x.factorization p) hinj).symm
          _ ≤ ∑ x ∈ Finset.Icc 1 (k - 1 - j₀.1), x.factorization p :=
              Finset.sum_le_sum_of_subset himg_sub
          _ = (∏ x ∈ Finset.Icc 1 (k - 1 - j₀.1), x).factorization p := by
              rw [Nat.factorization_prod (fun x hx => by rw [Finset.mem_Icc] at hx; omega),
                Finsupp.finsetSum_apply]
          _ = ((k - 1 - j₀.1).factorial).factorization p := by rw [prod_Icc_eq_factorial]
      have hdvd_choose : j₀.1.factorial * (k - 1 - j₀.1).factorial ∣ (k - 1).factorial := by
        have hc := Nat.choose_mul_factorial_mul_factorial (show j₀.1 ≤ k - 1 by omega)
        refine ⟨Nat.choose (k - 1) j₀.1, ?_⟩
        linarith
      have hsum_le : (j₀.1.factorial).factorization p + ((k - 1 - j₀.1).factorial).factorization p ≤
          ((k - 1).factorial).factorization p := by
        rw [← Finsupp.add_apply,
          ← Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
        exact (Nat.factorization_le_iff_dvd
          (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) hfact_ne).mpr
          hdvd_choose p
      exact (Nat.add_le_add hlt_le hgt_le).trans hsum_le
    · have hzero : ∀ j ∈ S, (B j).factorization p = 0 := by
        intro j _
        rw [hB_fact]
        have : p ∉ P_S \ Q j := fun h => hpPS (Finset.mem_sdiff.mp h).1
        simp [this]
      rw [Finset.sum_eq_zero hzero]
      exact Nat.zero_le _
  have hprod_B_le : ∏ j ∈ S, B j ≤ Nat.factorial (k - 1) :=
    Nat.le_of_dvd (Nat.factorial_pos _) hprod_B_dvd
  set T₀ := S.filter (fun j => (Q j).card = 0)
  set T₁ := S.filter (fun j => (Q j).card = 1)
  set T₂ := S.filter (fun j => 2 ≤ (Q j).card)
  have hcard_S : T₀.card + T₁.card + T₂.card = S.card := by
    have hdisj01 : Disjoint T₀ T₁ := by
      rw [Finset.disjoint_left]; intro j h0 h1
      have := (Finset.mem_filter.mp h0).2; have := (Finset.mem_filter.mp h1).2; omega
    have hdisj012 : Disjoint (T₀ ∪ T₁) T₂ := by
      rw [Finset.disjoint_left]; intro j h01 h2
      have h2' := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h01 with h0 | h1
      · have := (Finset.mem_filter.mp h0).2; omega
      · have := (Finset.mem_filter.mp h1).2; omega
    have hunion : T₀ ∪ T₁ ∪ T₂ = S := by
      ext j
      simp only [T₀, T₁, T₂, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro hj
        rcases lt_or_ge (Q j).card 2 with hlt | hge
        · rcases (show (Q j).card = 0 ∨ (Q j).card = 1 by omega) with h0 | h1
          · exact Or.inl (Or.inl ⟨hj, h0⟩)
          · exact Or.inl (Or.inr ⟨hj, h1⟩)
        · exact Or.inr ⟨hj, hge⟩
    rw [← Finset.card_union_of_disjoint hdisj01, ← Finset.card_union_of_disjoint hdisj012, hunion]
  have hsum_Q : ∑ j ∈ S, (Q j).card = P_S.card := by
    have hbiU : S.biUnion Q = P_S := by
      ext p
      simp only [Finset.mem_biUnion, Q, Finset.mem_filter]
      constructor
      · rintro ⟨j, _, hp, _⟩; exact hp
      · intro hp; exact ⟨jmax p, hjmax_mem p, hp, rfl⟩
    have hdisjQ : (S : Set (Fin k)).PairwiseDisjoint Q := by
      intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hpa hpb
      have ha := (Finset.mem_filter.mp hpa).2
      have hb := (Finset.mem_filter.mp hpb).2
      exact hab (ha.symm.trans hb)
    rw [← hbiU, Finset.card_biUnion hdisjQ]
  have hT1_T2_le : T₁.card + 2 * T₂.card ≤ Nat.primeCounting k := by
    have hdisj12 : Disjoint T₁ T₂ := by
      rw [Finset.disjoint_left]; intro j h1 h2
      have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
    have hsub12 : T₁ ∪ T₂ ⊆ S := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have h1 : T₁.card = ∑ j ∈ T₁, (Q j).card := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl fun j hj => ((Finset.mem_filter.mp hj).2).symm
    have h2 : 2 * T₂.card ≤ ∑ j ∈ T₂, (Q j).card := by
      calc 2 * T₂.card = ∑ _ ∈ T₂, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ j ∈ T₂, (Q j).card := Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2
    calc T₁.card + 2 * T₂.card
        ≤ ∑ j ∈ T₁, (Q j).card + ∑ j ∈ T₂, (Q j).card := Nat.add_le_add h1.le h2
      _ = ∑ j ∈ T₁ ∪ T₂, (Q j).card := (Finset.sum_union hdisj12).symm
      _ ≤ ∑ j ∈ S, (Q j).card := Finset.sum_le_sum_of_subset hsub12
      _ = P_S.card := hsum_Q
      _ ≤ Nat.primeCounting k := hPS_card
  have hT0_pow : n ^ T₀.card ≤ Nat.factorial (k - 1) := by
    have hle_B : ∀ j ∈ T₀, n ≤ B j := by
      intro j hj
      have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
      have hQ0 : Q j = ∅ := Finset.card_eq_zero.mp (Finset.mem_filter.mp hj).2
      have hA1 : A j = 1 := by simp [A, hQ0]
      have hBj : B j = n + j := by
        have := hAB j hjS
        rw [hA1, one_mul] at this
        exact this
      omega
    have hprod_sub : ∏ j ∈ T₀, B j ≤ ∏ j ∈ S, B j :=
      Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) fun j _ _ => hB_pos j
    calc n ^ T₀.card = ∏ _ ∈ T₀, n := by rw [Finset.prod_const]
      _ ≤ ∏ j ∈ T₀, B j := Finset.prod_le_prod' hle_B
      _ ≤ ∏ j ∈ S, B j := hprod_sub
      _ ≤ Nat.factorial (k - 1) := hprod_B_le
  have hT0_lt : T₀.card < Nat.primeCounting k / 4 := by
    have hpow_lt : n ^ T₀.card < n ^ (Nat.primeCounting k / 4) := by
      have h1 : Nat.factorial (k - 1) ≤ (Nat.factorial (k - 1)) ^ 4 :=
        le_self_pow₀ (Nat.factorial_pos _) (by norm_num)
      exact lt_of_le_of_lt (hT0_pow.trans h1) hfact_lt
    exact (Nat.pow_lt_pow_iff_right (show 1 < n by omega)).mp hpow_lt
  have hT1_ge : Nat.primeCounting k / 2 + 1 ≤ T₁.card := by omega
  have hT1_ne : T₁.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j₁, hj₁_T1, hj₁_min⟩ := Finset.exists_min_image T₁ B hT1_ne
  have hT1e_card : Nat.primeCounting k / 2 ≤ (T₁.erase j₁).card := by
    rw [Finset.card_erase_of_mem hj₁_T1]
    omega
  have hT1e_ne : (T₁.erase j₁).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j₂, hj₂_T1e, hj₂_min⟩ := Finset.exists_min_image (T₁.erase j₁) B hT1e_ne
  have hj₂_ne : j₂ ≠ j₁ := (Finset.mem_erase.mp hj₂_T1e).1
  have hj₂_T1 : j₂ ∈ T₁ := (Finset.mem_erase.mp hj₂_T1e).2
  have hB1_le_B2 : B j₁ ≤ B j₂ := hj₁_min j₂ hj₂_T1
  have hB2_pow : (B j₂) ^ (Nat.primeCounting k / 2) ≤ Nat.factorial (k - 1) := by
    have hsub_S : T₁.erase j₁ ⊆ S :=
      (Finset.erase_subset j₁ T₁).trans (Finset.filter_subset _ _)
    have hprod_sub : ∏ j ∈ T₁.erase j₁, B j ≤ ∏ j ∈ S, B j :=
      Finset.prod_le_prod_of_subset_of_one_le' hsub_S fun j _ _ => hB_pos j
    calc (B j₂) ^ (Nat.primeCounting k / 2)
        ≤ (B j₂) ^ (T₁.erase j₁).card := Nat.pow_le_pow_right (hB_pos j₂) hT1e_card
      _ = ∏ _ ∈ T₁.erase j₁, B j₂ := by rw [Finset.prod_const]
      _ ≤ ∏ j ∈ T₁.erase j₁, B j := Finset.prod_le_prod' hj₂_min
      _ ≤ ∏ j ∈ S, B j := hprod_sub
      _ ≤ Nat.factorial (k - 1) := hprod_B_le
  have hB1_pow : (B j₁) ^ (Nat.primeCounting k / 2) ≤ Nat.factorial (k - 1) :=
    (Nat.pow_le_pow_left hB1_le_B2 _).trans hB2_pow
  have hB12_lt : (B j₁ * B j₂) ^ 4 < n := by
    set q := Nat.primeCounting k / 4
    have hq_pos : 0 < q := by omega
    have h2q_le : 2 * q ≤ Nat.primeCounting k / 2 := by omega
    have hB1_2q : (B j₁) ^ (2 * q) ≤ Nat.factorial (k - 1) :=
      (Nat.pow_le_pow_right (hB_pos j₁) h2q_le).trans hB1_pow
    have hB2_2q : (B j₂) ^ (2 * q) ≤ Nat.factorial (k - 1) :=
      (Nat.pow_le_pow_right (hB_pos j₂) h2q_le).trans hB2_pow
    have hpowq : ((B j₁ * B j₂) ^ 4) ^ q < n ^ q := by
      calc ((B j₁ * B j₂) ^ 4) ^ q
          = ((B j₁) ^ (2 * q) * (B j₂) ^ (2 * q)) ^ 2 := by ring
        _ ≤ (Nat.factorial (k - 1) * Nat.factorial (k - 1)) ^ 2 :=
            Nat.pow_le_pow_left (Nat.mul_le_mul hB1_2q hB2_2q) 2
        _ = (Nat.factorial (k - 1)) ^ 4 := by ring
        _ < n ^ q := hfact_lt
    by_contra hle
    push Not at hle
    exact Nat.not_lt_of_ge (Nat.pow_le_pow_left hle q) hpowq
  obtain ⟨p₁, hp₁_eq⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hj₁_T1).2
  obtain ⟨p₂, hp₂_eq⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hj₂_T1).2
  have hp₁_memQ : p₁ ∈ Q j₁ := by rw [hp₁_eq]; exact Finset.mem_singleton_self p₁
  have hp₂_memQ : p₂ ∈ Q j₂ := by rw [hp₂_eq]; exact Finset.mem_singleton_self p₂
  have hp₁_PS : p₁ ∈ P_S := hQ_sub j₁ hp₁_memQ
  have hp₂_PS : p₂ ∈ P_S := hQ_sub j₂ hp₂_memQ
  have hp₁_prime : p₁.Prime := hPS_prime p₁ hp₁_PS
  have hp₂_prime : p₂.Prime := hPS_prime p₂ hp₂_PS
  have hp₁_le : p₁ ≤ k := hPS_le p₁ hp₁_PS
  have hp₂_le : p₂ ≤ k := hPS_le p₂ hp₂_PS
  have hp₁_jmax : jmax p₁ = j₁ := (Finset.mem_filter.mp hp₁_memQ).2
  have hp₂_jmax : jmax p₂ = j₂ := (Finset.mem_filter.mp hp₂_memQ).2
  have hp_ne : p₁ ≠ p₂ := by
    intro h
    exact hj₂_ne (hp₂_jmax.symm.trans (h ▸ hp₁_jmax))
  have he₁_pos : 1 ≤ (n + j₁).factorization p₁ := by
    obtain ⟨j, hjS, hdvd⟩ := (Finset.mem_filter.mp hp₁_PS).2
    have hpos : 1 ≤ (n + j).factorization p₁ :=
      Nat.one_le_iff_ne_zero.mpr (hp₁_prime.factorization_pos_of_dvd (by omega) hdvd).ne'
    exact hpos.trans (hp₁_jmax ▸ hjmax_ge p₁ j hjS)
  have he₂_pos : 1 ≤ (n + j₂).factorization p₂ := by
    obtain ⟨j, hjS, hdvd⟩ := (Finset.mem_filter.mp hp₂_PS).2
    have hpos : 1 ≤ (n + j).factorization p₂ :=
      Nat.one_le_iff_ne_zero.mpr (hp₂_prime.factorization_pos_of_dvd (by omega) hdvd).ne'
    exact hpos.trans (hp₂_jmax ▸ hjmax_ge p₂ j hjS)
  have hA₁ : A j₁ = p₁ ^ ((n + j₁).factorization p₁) := by simp [A, hp₁_eq]
  have hA₂ : A j₂ = p₂ ^ ((n + j₂).factorization p₂) := by simp [A, hp₂_eq]
  have hmul₁ : p₁ ^ ((n + j₁).factorization p₁) * B j₁ = n + j₁ := by
    rw [← hA₁]
    exact hAB j₁ (Finset.mem_filter.mp hj₁_T1).1
  have hmul₂ : p₂ ^ ((n + j₂).factorization p₂) * B j₂ = n + j₂ := by
    rw [← hA₂]
    exact hAB j₂ (Finset.mem_filter.mp hj₂_T1).1
  have hndvd₁ : ¬ p₁ ∣ B j₁ := by
    intro hd
    have hpos := hp₁_prime.factorization_pos_of_dvd (hB_pos j₁).ne' hd
    have h0 : (B j₁).factorization p₁ = 0 := by
      rw [hB_fact]
      have : p₁ ∉ P_S \ Q j₁ := fun h => (Finset.mem_sdiff.mp h).2 hp₁_memQ
      simp [this]
    omega
  have hndvd₂ : ¬ p₂ ∣ B j₂ := by
    intro hd
    have hpos := hp₂_prime.factorization_pos_of_dvd (hB_pos j₂).ne' hd
    have h0 : (B j₂).factorization p₂ = 0 := by
      rw [hB_fact]
      have : p₂ ∉ P_S \ Q j₂ := fun h => (Finset.mem_sdiff.mp h).2 hp₂_memQ
      simp [this]
    omega
  refine ⟨p₁, p₂, (n + j₁).factorization p₁, (n + j₂).factorization p₂, B j₁, B j₂,
    hp₁_prime, hp₂_prime, hp_ne, hp₁_le, hp₂_le, he₁_pos, he₂_pos, hB_pos j₁, hB_pos j₂,
    hndvd₁, hndvd₂, hB1_pow, hB2_pow, hB12_lt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmul₁]; omega
  · rw [hmul₁]; have := j₁.2; omega
  · rw [hmul₂]; omega
  · rw [hmul₂]; have := j₂.2; omega
  · rw [hmul₁, hmul₂]
    intro heq
    exact hj₂_ne (Fin.ext (by omega)).symm

lemma fifty_five_le_of_composite_eight (n k : ℕ) (hk : 8 ≤ k) (hn : 9 ≤ n)
    (hcomp : ∀ i : Fin k, (n + i).Composite) : 55 ≤ n := by
  by_contra hlt
  have hhit : ∀ p : ℕ, p.Prime → n ≤ p → p < n + 8 → False := by
    intro p hp hle hltp
    have hi : p - n < k := by omega
    have hc := (hcomp ⟨p - n, hi⟩).2
    rw [show n + (p - n) = p by omega] at hc
    exact hc hp
  by_cases h1 : n ≤ 11
  · exact hhit 11 (by norm_num) h1 (by omega)
  · by_cases h2 : n ≤ 17
    · exact hhit 17 (by norm_num) h2 (by omega)
    · by_cases h3 : n ≤ 23
      · exact hhit 23 (by norm_num) h3 (by omega)
      · by_cases h4 : n ≤ 29
        · exact hhit 29 (by norm_num) h4 (by omega)
        · by_cases h5 : n ≤ 31
          · exact hhit 31 (by norm_num) h5 (by omega)
          · by_cases h6 : n ≤ 37
            · exact hhit 37 (by norm_num) h6 (by omega)
            · by_cases h7 : n ≤ 43
              · exact hhit 43 (by norm_num) h7 (by omega)
              · by_cases h8 : n ≤ 47
                · exact hhit 47 (by norm_num) h8 (by omega)
                · by_cases h9 : n ≤ 53
                  · exact hhit 53 (by norm_num) h9 (by omega)
                  · exact hhit 59 (by norm_num) (by omega) (by omega)

lemma dvd_2520_form (d : ℕ) (hd : d ∣ 2520) :
    ∃ a : Fin 4, ∃ b : Fin 3, ∃ c : Fin 2, ∃ e : Fin 2,
      d = 2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 := by
  have hd_ne : d ≠ 0 := ne_zero_of_dvd_ne_zero (by decide) hd
  have h2520 : (2520 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 := by norm_num
  have hf_le := (Nat.factorization_le_iff_dvd hd_ne (by decide : (2520 : ℕ) ≠ 0)).mpr hd
  have h2520_f : ∀ p : ℕ, (2520 : ℕ).factorization p =
      if p = 2 then 3 else if p = 3 then 2 else if p = 5 then 1 else if p = 7 then 1 else 0 := by
    intro p
    rw [h2520,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.Prime.factorization (by norm_num : Nat.Prime 2),
      Nat.Prime.factorization (by norm_num : Nat.Prime 3),
      Nat.Prime.factorization (by norm_num : Nat.Prime 5),
      Nat.Prime.factorization (by norm_num : Nat.Prime 7),
      Finsupp.single_apply]
    split_ifs <;> omega
  have ha : d.factorization 2 < 4 := by have := hf_le 2; rw [h2520_f] at this; simp at this; omega
  have hb : d.factorization 3 < 3 := by have := hf_le 3; rw [h2520_f] at this; simp at this; omega
  have hc : d.factorization 5 < 2 := by have := hf_le 5; rw [h2520_f] at this; simp at this; omega
  have he : d.factorization 7 < 2 := by have := hf_le 7; rw [h2520_f] at this; simp at this; omega
  refine ⟨⟨d.factorization 2, ha⟩, ⟨d.factorization 3, hb⟩, ⟨d.factorization 5, hc⟩,
    ⟨d.factorization 7, he⟩, ?_⟩
  have hsub : d.primeFactors ⊆ {2, 3, 5, 7} := by
    intro p hp
    have hpos : 0 < d.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Nat.support_factorization d ▸ hp))
    have hle := hf_le p
    rw [h2520_f] at hle
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hnot
    push Not at hnot
    simp [hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2] at hle
    omega
  have hprod : d = ∏ p ∈ ({2, 3, 5, 7} : Finset ℕ), p ^ (d.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hd_ne,
      Nat.prod_factorization_eq_prod_primeFactors]
    refine Finset.prod_subset hsub fun p _ hp_not => ?_
    have h0 : d.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact hp_not
    simp [h0]
  dsimp only
  conv_lhs => rw [hprod]
  simp [mul_assoc]

lemma smooth_le_2531_dvd_M7 (m : ℕ) (hm : m ∈ Nat.smoothNumbers 11) (hle : m ≤ 2531) :
    m ∣ 2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 := by
  have hm_ne : m ≠ 0 := hm.1
  have hM_ne : (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 : ℕ) ≠ 0 := by norm_num
  rw [← Nat.factorization_le_iff_dvd hm_ne hM_ne]
  intro p
  by_cases hpd : p ∣ m
  · by_cases hp : p.Prime
    · have hlt : p < 11 := Nat.mem_smoothNumbers'.mp hm p hp hpd
      have hpow_le : p ^ (m.factorization p) ≤ 2531 :=
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hm_ne) (Nat.ordProj_dvd m p)).trans hle
      have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
        interval_cases p <;> first | exact absurd hp (by decide) | simp
      rcases hp_cases with rfl | rfl | rfl | rfl
      · have h1 : m.factorization 2 ≤ 11 := by
          by_contra hgt; push Not at hgt
          have : 2 ^ 12 ≤ 2 ^ (m.factorization 2) := Nat.pow_le_pow_right (by norm_num) hgt
          omega
        have h2 : 11 ≤ (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 : ℕ).factorization 2 :=
          (hp.pow_dvd_iff_le_factorization hM_ne).mp ⟨3 ^ 7 * 5 ^ 4 * 7 ^ 4, by ring⟩
        omega
      · have h1 : m.factorization 3 ≤ 7 := by
          by_contra hgt; push Not at hgt
          have : 3 ^ 8 ≤ 3 ^ (m.factorization 3) := Nat.pow_le_pow_right (by norm_num) hgt
          omega
        have h2 : 7 ≤ (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 : ℕ).factorization 3 :=
          (hp.pow_dvd_iff_le_factorization hM_ne).mp ⟨2 ^ 11 * 5 ^ 4 * 7 ^ 4, by ring⟩
        omega
      · have h1 : m.factorization 5 ≤ 4 := by
          by_contra hgt; push Not at hgt
          have : 5 ^ 5 ≤ 5 ^ (m.factorization 5) := Nat.pow_le_pow_right (by norm_num) hgt
          omega
        have h2 : 4 ≤ (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 : ℕ).factorization 5 :=
          (hp.pow_dvd_iff_le_factorization hM_ne).mp ⟨2 ^ 11 * 3 ^ 7 * 7 ^ 4, by ring⟩
        omega
      · have h1 : m.factorization 7 ≤ 4 := by
          by_contra hgt; push Not at hgt
          have : 7 ^ 5 ≤ 7 ^ (m.factorization 7) := Nat.pow_le_pow_right (by norm_num) hgt
          omega
        have h2 : 4 ≤ (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 : ℕ).factorization 7 :=
          (hp.pow_dvd_iff_le_factorization hM_ne).mp ⟨2 ^ 11 * 3 ^ 7 * 5 ^ 4, by ring⟩
        omega
    · rw [Nat.factorization_eq_zero_of_not_prime m hp]; exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_dvd hpd]; exact Nat.zero_le _

lemma smooth_le_2531_dvd_M11 (m : ℕ) (hm : m ∈ Nat.smoothNumbers 12) (hle : m ≤ 2531) :
    m ∣ 2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3 := by
  have hm_ne : m ≠ 0 := hm.1
  have hM_ne : (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3 : ℕ) ≠ 0 := by norm_num
  rw [← Nat.factorization_le_iff_dvd hm_ne hM_ne]
  intro p
  by_cases hpd : p ∣ m
  · by_cases hp : p.Prime
    · have hlt : p < 12 := Nat.mem_smoothNumbers'.mp hm p hp hpd
      have hpow_le : p ^ (m.factorization p) ≤ 2531 :=
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hm_ne) (Nat.ordProj_dvd m p)).trans hle
      have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
        interval_cases p <;> first | exact absurd hp (by decide) | simp
      rcases hp_cases with rfl | rfl | rfl | rfl | rfl
      · have h1 : m.factorization 2 ≤ 11 := by
          by_contra hgt; push Not at hgt
          have : 2 ^ 12 ≤ 2 ^ (m.factorization 2) := Nat.pow_le_pow_right (by norm_num) hgt
          omega
        have h2 : 11 ≤ (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3 : ℕ).factorization 2 :=
          (hp.pow_dvd_iff_le_factorization hM_ne).mp ⟨3 ^ 7 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3, by ring⟩
        omega
      · have h1 : m.factorization 3 ≤ 7 := by
          by_contra hgt; push Not at hgt
          have : 3 ^ 8 ≤ 3 ^ (m.factorization 3) := Nat.pow_le_pow_right (by norm_num) hgt
          omega
        have h2 : 7 ≤ (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3 : ℕ).factorization 3 :=
          (hp.pow_dvd_iff_le_factorization hM_ne).mp ⟨2 ^ 11 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3, by ring⟩
        omega
      · have h1 : m.factorization 5 ≤ 4 := by
          by_contra hgt; push Not at hgt
          have : 5 ^ 5 ≤ 5 ^ (m.factorization 5) := Nat.pow_le_pow_right (by norm_num) hgt
          omega
        have h2 : 4 ≤ (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3 : ℕ).factorization 5 :=
          (hp.pow_dvd_iff_le_factorization hM_ne).mp ⟨2 ^ 11 * 3 ^ 7 * 7 ^ 4 * 11 ^ 3, by ring⟩
        omega
      · have h1 : m.factorization 7 ≤ 4 := by
          by_contra hgt; push Not at hgt
          have : 7 ^ 5 ≤ 7 ^ (m.factorization 7) := Nat.pow_le_pow_right (by norm_num) hgt
          omega
        have h2 : 4 ≤ (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3 : ℕ).factorization 7 :=
          (hp.pow_dvd_iff_le_factorization hM_ne).mp ⟨2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 11 ^ 3, by ring⟩
        omega
      · have h1 : m.factorization 11 ≤ 3 := by
          by_contra hgt; push Not at hgt
          have : 11 ^ 4 ≤ 11 ^ (m.factorization 11) := Nat.pow_le_pow_right (by norm_num) hgt
          omega
        have h2 : 3 ≤ (2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3 : ℕ).factorization 11 :=
          (hp.pow_dvd_iff_le_factorization hM_ne).mp ⟨2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4, by ring⟩
        omega
    · rw [Nat.factorization_eq_zero_of_not_prime m hp]; exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_dvd hpd]; exact Nat.zero_le _

lemma small_k_8_to_11 (n k : ℕ) (hk8 : 8 ≤ k) (hk11 : k ≤ 11) (hkn : k < n)
    (hle : n ≤ (Finset.Ico 1 k).lcm id)
    (hdvd : ∃ j : Fin k, (n + j) ∣ (Finset.Ico 1 k).lcm id)
    (hcomp : ∀ i : Fin k, (n + i).Composite) :
    (Finset.univ.filter (fun j : Fin k => (n + j) ∈ Nat.smoothNumbers (k + 1))).card ≤
      Nat.primeCounting k := by
  have hn55 : 55 ≤ n := fifty_five_le_of_composite_eight n k hk8 (by omega) hcomp
  have hcases : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hL : (Finset.Ico 1 8).lcm id = 420 := by decide
    have hpc : Nat.primeCounting 8 = 4 := by decide
    rw [hL] at hle hdvd; rw [hpc]
    obtain ⟨j, hj⟩ := hdvd
    obtain ⟨a, b, c, e, hd_eq⟩ := dvd_2520_form (n + j) (hj.trans (by decide : 420 ∣ 2520))
    have hsub : Finset.univ.filter (fun i : Fin 8 => (n + i) ∈ Nat.smoothNumbers 9) ⊆
        Finset.univ.filter (fun i : Fin 8 => 2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 % (n + i) = 0) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ _, Nat.mod_eq_zero_of_dvd ?_⟩
      have hsm11 : n + i ∈ Nat.smoothNumbers 11 :=
        (Nat.smoothNumbers_eq_factoredNumbers 9 ▸ hi.2 |> fun h =>
          Nat.smoothNumbers_eq_factoredNumbers 11 ▸
            Nat.factoredNumbers_mono (Finset.range_mono (by omega : 9 ≤ 11)) h)
      exact smooth_le_2531_dvd_M7 (n + i) hsm11 (by have := i.2; omega)
    have hchk : ∀ a : Fin 4, ∀ b : Fin 3, ∀ c : Fin 2, ∀ e : Fin 2, ∀ j : Fin 8,
        55 ≤ 2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 →
        (Finset.univ.filter (fun i : Fin 8 =>
          2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 % (2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 + i.1) = 0)).card ≤ 4 := by
      decide
    have hn_eq : 2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 = n := by omega
    have hres := hchk a b c e j (hn_eq ▸ hn55)
    rw [hn_eq] at hres
    exact (Finset.card_le_card hsub).trans hres
  · have hL : (Finset.Ico 1 9).lcm id = 840 := by decide
    have hpc : Nat.primeCounting 9 = 4 := by decide
    rw [hL] at hle hdvd; rw [hpc]
    obtain ⟨j, hj⟩ := hdvd
    obtain ⟨a, b, c, e, hd_eq⟩ := dvd_2520_form (n + j) (hj.trans (by decide : 840 ∣ 2520))
    have hsub : Finset.univ.filter (fun i : Fin 9 => (n + i) ∈ Nat.smoothNumbers 10) ⊆
        Finset.univ.filter (fun i : Fin 9 => 2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 % (n + i) = 0) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ _, Nat.mod_eq_zero_of_dvd ?_⟩
      have hsm11 : n + i ∈ Nat.smoothNumbers 11 :=
        (Nat.smoothNumbers_eq_factoredNumbers 10 ▸ hi.2 |> fun h =>
          Nat.smoothNumbers_eq_factoredNumbers 11 ▸
            Nat.factoredNumbers_mono (Finset.range_mono (by omega : 10 ≤ 11)) h)
      exact smooth_le_2531_dvd_M7 (n + i) hsm11 (by have := i.2; omega)
    have hchk : ∀ a : Fin 4, ∀ b : Fin 3, ∀ c : Fin 2, ∀ e : Fin 2, ∀ j : Fin 9,
        55 ≤ 2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 →
        (Finset.univ.filter (fun i : Fin 9 =>
          2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 % (2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 + i.1) = 0)).card ≤ 4 := by
      decide
    have hn_eq : 2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 = n := by omega
    have hres := hchk a b c e j (hn_eq ▸ hn55)
    rw [hn_eq] at hres
    exact (Finset.card_le_card hsub).trans hres
  · have hL : (Finset.Ico 1 10).lcm id = 2520 := by decide
    have hpc : Nat.primeCounting 10 = 4 := by decide
    rw [hL] at hle hdvd; rw [hpc]
    obtain ⟨j, hj⟩ := hdvd
    obtain ⟨a, b, c, e, hd_eq⟩ := dvd_2520_form (n + j) hj
    have hsub : Finset.univ.filter (fun i : Fin 10 => (n + i) ∈ Nat.smoothNumbers 11) ⊆
        Finset.univ.filter (fun i : Fin 10 => 2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 % (n + i) = 0) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, Nat.mod_eq_zero_of_dvd
        (smooth_le_2531_dvd_M7 (n + i) hi.2 (by have := i.2; omega))⟩
    have hchk : ∀ a : Fin 4, ∀ b : Fin 3, ∀ c : Fin 2, ∀ e : Fin 2, ∀ j : Fin 10,
        55 ≤ 2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 →
        (Finset.univ.filter (fun i : Fin 10 =>
          2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 % (2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 + i.1) = 0)).card ≤ 4 := by
      decide
    have hn_eq : 2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 = n := by omega
    have hres := hchk a b c e j (hn_eq ▸ hn55)
    rw [hn_eq] at hres
    exact (Finset.card_le_card hsub).trans hres
  · have hL : (Finset.Ico 1 11).lcm id = 2520 := by decide
    have hpc : Nat.primeCounting 11 = 5 := by decide
    rw [hL] at hle hdvd; rw [hpc]
    obtain ⟨j, hj⟩ := hdvd
    obtain ⟨a, b, c, e, hd_eq⟩ := dvd_2520_form (n + j) hj
    have hsub : Finset.univ.filter (fun i : Fin 11 => (n + i) ∈ Nat.smoothNumbers 12) ⊆
        Finset.univ.filter (fun i : Fin 11 => 2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3 % (n + i) = 0) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, Nat.mod_eq_zero_of_dvd
        (smooth_le_2531_dvd_M11 (n + i) hi.2 (by have := i.2; omega))⟩
    have hchk : ∀ a : Fin 4, ∀ b : Fin 3, ∀ c : Fin 2, ∀ e : Fin 2, ∀ j : Fin 11,
        55 ≤ 2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 →
        (Finset.univ.filter (fun i : Fin 11 =>
          2 ^ 11 * 3 ^ 7 * 5 ^ 4 * 7 ^ 4 * 11 ^ 3 % (2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 + i.1) = 0)).card ≤ 5 := by
      decide
    have hn_eq : 2 ^ a.1 * 3 ^ b.1 * 5 ^ c.1 * 7 ^ e.1 - j.1 = n := by omega
    have hres := hchk a b c e j (hn_eq ▸ hn55)
    rw [hn_eq] at hres
    exact (Finset.card_le_card hsub).trans hres

/-- A divisor of a product of prime powers occurs in the list of products obtained by
lowering the exponents. -/
private theorem mem_divisor_products (pe : List (ℕ × ℕ)) (d : ℕ)
    (hp : ∀ x ∈ pe, x.1.Prime)
    (hd : d ∣ (pe.map fun x => x.1 ^ x.2).prod) :
    d ∈ pe.foldr (fun x ds =>
      (List.range (x.2 + 1)).flatMap fun e => ds.map (fun a => x.1 ^ e * a)) [1] := by
  induction pe generalizing d with
  | nil => simpa using hd
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons] at hd
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow (hp x (by simp))).mp ha
    refine List.mem_flatMap.mpr ⟨e, List.mem_range.mpr (by omega), ?_⟩
    exact List.mem_map.mpr ⟨b, ih b (by
      intro y hy
      exact hp y (List.mem_cons_of_mem x hy)) hb, rfl⟩

/-- Taking a sufficiently high power of the lcm accounts for every small-prime exponent
that can occur in a smooth number below the given bound. -/
private theorem smooth_dvd_lcm_pow (m k bound : ℕ) (hm : m ∈ Nat.smoothNumbers (k + 1))
    (hb : m ≤ bound) :
    m ∣ ((Finset.Ico 1 (k + 1)).lcm id) ^ Nat.log 2 bound := by
  let L := (Finset.Ico 1 (k + 1)).lcm id
  have hL : L ≠ 0 := by
    simp [L, Finset.lcm_eq_zero_iff]
  rw [← Nat.factorization_le_iff_dvd hm.1 (pow_ne_zero _ hL)]
  intro p
  rw [Nat.factorization_pow]
  change m.factorization p ≤ Nat.log 2 bound * L.factorization p
  by_cases hp0 : m.factorization p = 0
  · simp [hp0]
  have hpp : p.Prime := by
    by_contra h
    exact hp0 (Nat.factorization_eq_zero_of_not_prime m h)
  have hpk : p < k + 1 := Nat.mem_smoothNumbers'.mp hm p hpp
    (Nat.dvd_of_factorization_pos hp0)
  have hpL : p ∣ L := Finset.dvd_lcm (f := id) (Finset.mem_Ico.mpr ⟨hpp.one_le, hpk⟩)
  have hpLf : 1 ≤ L.factorization p := (hpp.pow_dvd_iff_le_factorization hL).mp (by
    simpa using hpL)
  have hp_pow : 2 ^ m.factorization p ≤ bound :=
    (Nat.pow_le_pow_left hpp.two_le _).trans
      ((Nat.le_of_dvd (Nat.pos_of_ne_zero hm.1) (Nat.ordProj_dvd m p)).trans hb)
  have hexp := Nat.le_log_of_pow_le (by decide : 1 < 2) hp_pow
  exact hexp.trans (by simpa using Nat.mul_le_mul_left (Nat.log 2 bound) hpLf)

private theorem smooth_count_le_range_count (n k start width M : ℕ)
    (hstart : start ≤ n) (hwidth : n + k ≤ start + width)
    (hdiv : ∀ i : Fin k, n + i ∈ Nat.smoothNumbers (k + 1) → n + i ∣ M) :
    (Finset.univ.filter (fun i : Fin k => n + i ∈ Nat.smoothNumbers (k + 1))).card ≤
      (List.range width).countP (fun i => M % (start + i) == 0) := by
  let pred := fun i => M % (start + i) == 0
  change _ ≤ (List.range width).countP pred
  have hr : (List.range width).toFinset = Finset.range width := by
    ext i
    simp
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter pred), List.toFinset_filter, hr]
  apply Finset.card_le_card_of_injOn (fun i : Fin k => n + i.1 - start)
  · intro i hi
    have his := (Finset.mem_filter.mp hi).2
    have hik := i.2
    have heq : start + (n + i.1 - start) = n + i.1 := by omega
    simp [pred, heq, Nat.mod_eq_zero_of_dvd (hdiv i his), show n + i.1 - start < width by omega]
  · intro i _ j _ hij
    change n + i.1 - start = n + j.1 - start at hij
    exact Fin.ext (by omega)

private theorem small_k_of_certificate (n k : ℕ) (hkn : k < n)
    (hle : n ≤ (Finset.Ico 1 k).lcm id)
    (hdvd : ∃ j : Fin k, (n + j) ∣ (Finset.Ico 1 k).lcm id)
    (hcomp : ∀ i : Fin k, (n + i).Composite)
    (M C : ℕ)
    (hM : M = ((Finset.Ico 1 (k + 1)).lcm id) ^ Nat.log 2 ((Finset.Ico 1 k).lcm id + k))
    (hC : C = Nat.primeCounting k)
    (hcheck :
      let pe := ((List.range k).filter fun p => decide (Nat.Prime p)).map
        fun p => (p, Nat.log p (k - 1))
      let ds := pe.foldr (fun x ds =>
        (List.range (x.2 + 1)).flatMap fun e => ds.map (fun a => x.1 ^ e * a)) [1]
      (pe.map fun x => x.1 ^ x.2).prod = (Finset.Ico 1 k).lcm id ∧
      ds.all (fun d =>
        let start := d - (k - 1)
        if (List.range (2 * k - 1)).countP (fun i => M % (start + i) == 0) ≤ C then true
        else (List.range k).all (fun j =>
          let x := d - j
          if k < x then
            decide ((List.range k).countP (fun i => M % (x + i) == 0) ≤ C) ||
              (List.range k).any (fun i => decide (Nat.Prime (x + i)))
          else true)) = true) :
    (Finset.univ.filter (fun i : Fin k => n + i ∈ Nat.smoothNumbers (k + 1))).card ≤
      Nat.primeCounting k := by
  let pe := ((List.range k).filter fun p => decide (Nat.Prime p)).map
    fun p => (p, Nat.log p (k - 1))
  let ds := pe.foldr (fun x ds =>
    (List.range (x.2 + 1)).flatMap fun e => ds.map (fun a => x.1 ^ e * a)) [1]
  let count := fun start width =>
    (List.range width).countP (fun i => M % (start + i) == 0)
  let covered := fun d =>
    if count (d - (k - 1)) (2 * k - 1) ≤ C then true
    else (List.range k).all (fun j =>
      let x := d - j
      if k < x then decide (count x k ≤ C) ||
        (List.range k).any (fun i => decide (Nat.Prime (x + i))) else true)
  change (pe.map fun x => x.1 ^ x.2).prod = (Finset.Ico 1 k).lcm id ∧
    ds.all covered = true at hcheck
  obtain ⟨j, hj⟩ := hdvd
  have hmem : n + j.1 ∈ ds := mem_divisor_products pe _ (by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    simpa using (List.mem_filter.mp hp).2) (by
      rw [hcheck.1]
      exact hj)
  have hcovered := List.all_eq_true.mp hcheck.2 _ hmem
  have hdiv : ∀ i : Fin k, n + i ∈ Nat.smoothNumbers (k + 1) → n + i ∣ M := by
    intro i hi
    rw [hM]
    exact smooth_dvd_lcm_pow (n + i) k _ hi (by have := i.2; omega)
  rw [← hC]
  have hjlt := j.2
  let start := n + j.1 - (k - 1)
  -- Every window containing the chosen divisor lies in this wider interval.
  by_cases hwide : count start (2 * k - 1) ≤ C
  · exact (smooth_count_le_range_count n k start (2 * k - 1) M (by dsimp [start]; omega)
      (by dsimp [start]; omega) hdiv).trans hwide
  have hall : (List.range k).all (fun j' =>
      let x := n + j.1 - j'
      if k < x then decide (count x k ≤ C) ||
        (List.range k).any (fun i => decide (Nat.Prime (x + i))) else true) = true := by
    simpa only [covered, show ¬ count (n + j.1 - (k - 1)) (2 * k - 1) ≤ C from hwide,
      if_false] using hcovered
  have h := List.all_eq_true.mp hall _ (List.mem_range.mpr hjlt)
  simp only [show n + j.1 - j.1 = n by omega, hkn, if_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with hcount | hprime
  · exact (smooth_count_le_range_count n k n k M le_rfl le_rfl hdiv).trans hcount
  · obtain ⟨i, hi, hpi⟩ := List.any_eq_true.mp hprime
    exact False.elim ((hcomp ⟨i, List.mem_range.mp hi⟩).2 (of_decide_eq_true hpi))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem small_k_12_to_14 (n k : ℕ) (hkLow : 12 ≤ k) (hkLimit : k ≤ 14) (hkn : k < n)
    (hle : n ≤ (Finset.Ico 1 k).lcm id)
    (hdvd : ∃ j : Fin k, (n + j) ∣ (Finset.Ico 1 k).lcm id)
    (hcomp : ∀ i : Fin k, (n + i).Composite) :
    (Finset.univ.filter (fun i : Fin k => n + i ∈ Nat.smoothNumbers (k + 1))).card ≤
      Nat.primeCounting k := by
  interval_cases k
  · refine small_k_of_certificate n 12 hkn hle hdvd hcomp
      158163098028668242656275643717608526012244977254400000000000000 5 (by decide +kernel) (by decide +kernel) ?_
    decide +kernel
  · refine small_k_of_certificate n 13 hkn hle hdvd hcomp
      622747647267120106291638778363249757614914342822913475243252121600000000000000 6 (by decide +kernel) (by decide +kernel) ?_
    decide +kernel
  · refine small_k_of_certificate n 14 hkn hle hdvd hcomp
      10501671000078875486953174308167535041101376011514170586047820502924464542822957056000000000000000000 6 (by decide +kernel) (by decide +kernel) ?_
    decide +kernel

theorem main : H1 → H2 → OMA.R_Grimm_grimm_conjecture_weak_R1.H1 := by
  intro h1 h2 n k hk8 hkn hle hdvd hgap hcomp
  by_cases hk12 : k < 12
  · exact small_k_8_to_11 n k hk8 (by omega) hkn hle hdvd hcomp
  · by_cases hk38 : k < 2 ^ 38
    · by_cases hk14 : k ≤ 14
      · exact small_k_12_to_14 n k (by omega) hk14 hkn hle hdvd hcomp
      · exact h2 n k (by omega) hk38 hkn hle hdvd hgap hcomp
    · push Not at hk38
      obtain ⟨hk12_lt, hfact_lt⟩ := factorial_pow_four_lt_of_ge n k hk38 hgap
      by_contra! hS
      have hpair := exists_prime_power_pair_of_many_smooth n k hk8 hkn hfact_lt hS
      exact h1 n k hk38 hk12_lt hgap hpair

end OMA.R_Grimm_grimm_conjecture_weak_R1_H1_R1
